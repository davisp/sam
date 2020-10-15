% Licensed under the Apache License, Version 2.0 (the "License"); you may not
% use this file except in compliance with the License. You may obtain a copy of
% the License at
%
%   http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
% WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
% License for the specific language governing permissions and limitations under
% the License.

-module(sam_server).
-behavior(gen_server).

-export([
    start_link/0,

    handle_notification/1,
    handle_request/1
]).

-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).

-include("sam.hrl").

-define(PROCS, sam_server_processes).

-record(st, {
    methods
}).


start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

handle_notification(Body) ->
    gen_server:cast(?MODULE, {notification, Body}).

handle_request(Body) ->
    gen_server:cast(?MODULE, {request, Body}).

init(_) ->
    ets:new(?PROCS, [set, named_table]),
    Types = sam_lsp_schema:client_initiated(),
    Methods = lists:foldl(fun(TypeName, Acc) ->
        Type = sam_lsp_schema:TypeName(),
        case maps:get(method, Type, undefined) of
            undefined ->
                Acc;
            Method ->
                maps:put(Method, TypeName, Acc)
        end
    end, #{}, Types),
    {ok, #st{methods = Methods}}.


terminate(_, _) ->
    ok.


handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.


handle_cast({notification, Body}, #st{methods = Methods} = St) ->
    Method = maps:get(<<"method">>, Body, undefined),
    case maps:get(Method, Methods) of
        undefined ->
            lager:warning("Unknown notification: ~p", [Body]),
            {noreply, St};
        TypeName ->
            case sam_lsp_schema:response_type(TypeName) of
                undefined ->
                    sam_provider:notify(TypeName, Body),
                    {noreply, St};
                _ResponseType ->
                    lager:error("Invalid request: ~p", [Body]),
                    % JSONRPC requires a response for every request
                    % but we haven't got one for this request so all
                    % we can do is die to express our dissatisfaction.
                    sam:exit(1)
            end
    end;
handle_cast({request, Body}, #st{methods = Methods} = St) ->
    Method = maps:get(<<"method">>, Body, undefined),
    case maps:get(Method, Methods, undefined) of
        undefined ->
            lager:warning("Unknown method: ~p", [Body]),
            sam_client:error(Body, ?JSONRPC_METHOD_NOT_FOUND, unknown_method);
        ReqTypeName ->
            case sam_lsp_schema:response_type(ReqTypeName) of
                undefined ->
                    lager:error("Invalid request type: ~s", [ReqTypeName]),
                    sam_client:error(Body, ?JSONRPC_INVALID_REQUEST, invalid_request_type);
                RespTypeName ->
                    ReqId = maps:get(<<"id">>, Body),
                    {ok, Pid} = sam_provider:request(ReqTypeName, RespTypeName, Body),
                    Ref = erlang:monitor(process, Pid),
                    ets:insert(?PROCS, {Ref, Pid, ReqId})
            end
    end,
    {noreply, St};
handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.


handle_info({'DOWN', Ref, process, Pid, Reason}, St) ->
    case ets:lookup(?PROCS, Ref) of
        [{Ref, Pid, _ReqId}] when Reason == normal ->
            % Process has left this world peacefully
            ets:delete(?PROCS, Ref);
        [{Ref, Pid, ReqId}] ->
            ets:delete(?PROCS, Ref),
            lager:error("Error handling request ~p: ~p", [Pid, Reason]),
            sam_client:error(ReqId, ?JSONRPC_INTERNAL_ERROR, process_died);
        [] ->
            % Unknown process exit?
            lager:error("Unknown process ~p died: ~p", [Pid, Reason])
    end,
    {noreply, St};            
handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.
