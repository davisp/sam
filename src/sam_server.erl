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
    handle/1,
    respond/1
]).


-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).


-define(PROCS, sam_server_processes).

-record(st, {
    request_id = 0
}).


start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).


handle(Body) ->
    gen_server:cast(?MODULE, {handle, Body}).


send(_) ->
    ok.

respond(_) ->
    ok.


init(_) ->
    ets:new(?PROCS, [set, named_table]),
    {ok, #st{}}.


terminate(_, _) ->
    ok.


handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.


handle_cast({handle, Body}, St) ->
    try
        Msg = sam_msg:from_json(Body),
        case Msg of
            #{type := request} -> handle_request(Msg);
            #{type := response} -> handle_response(Msg);
            #{type := cancel} -> cancel_request(Msg);
            #{type := progress} -> handle_progress(Msg)
        end,
        {noreply, St}
    catch T:R:S ->
        lager:error("Error handling ~p :: ~p ~p ~p", [Body, T, R, S]),
        {stop, {bad_msg, Body}, St}
    end;
handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.


handle_info({'DOWN', Ref, process, Pid, Reason}, St) ->
    case ets:lookup(?PROCS, Ref) of
        [] when Reason == normal ->
            % Process has left this world peacefully
            ok;
        [] ->
            % Unknown process exit?
            lager:error("Unknown process ~p died: ~p", [Pid, Reason]);
        [{Ref, Pid, ReqId}] ->
            ets:delete(?PROCS, Ref),
            lager:error("Error handling request ~p: ~p", [Pid, Reason]);
            Msg = sam_msg:error(ReqId, ?JSONRPC_INTERNAL_ERROR, process_died),
            sam_stdio:send(Msg)
    end,
    {noreply, St};            
handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.

handle_request(#{req_id := ReqId} = Request) ->
    {ok, Pid} = sam_handler:start(Request),
    Ref = erlang:monitor(process, Pid),
    ets:insert(?PROCS, {Ref, Pid, ReqId}).

handle_response(#{req_id := ReqId} = Response) ->
    erlang:error(not_implemented).

handle_cancel(#{}) ->
    % not implemented
    ok.

handle_progress(#{}) ->
    erlang:error(not_implemented).
