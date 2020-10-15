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

-module(sam_client).
-behavior(gen_server).

-export([
    start_link/0,

    send/2,
    reply/2,
    error/3,

    handle_response/1
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

-define(REQUESTS, sam_client_requests).
-define(PROCS, sam_client_processes).

-record(st, {
    io_dev,
    req_id = 0
}).


start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

send(TypeName, Msg) ->
    case sam_lsp_schema:response_type(TypeName) of
        undefined ->
            sam_lsp_validator:validate(sam_lsp_schema:TypeName(), Msg),
            gen_server:cast(?MODULE, {send, Msg});
        RespType ->
            case lists:member(TypeName, sam_lsp_schema:server_initiated()) of
                true ->
                    ok;
                false ->
                    erlang:error({invalid_server_initiated_message, TypeName})
            end,
            ReqId = gen_server:call(?MODULE, next_req_id),
            ReqMsg = maps:put(<<"id">>, ReqId, Msg),
            {ok, Resp} = gen_server:call(?MODULE, {request, ReqId, ReqMsg}),
            sam_lsp_validator:validate(sam_lsp_schema:RespType(), Resp),
            Resp
    end.

reply(TypeName, Msg) ->
    Type = sam_lsp_schema:TypeName(),
    sam_lsp_validator:validate(Type, Msg),
    gen_server:cast(?MODULE, {send, Msg}).

error(#{} = Body, Code, Error) ->
    error(maps:get(<<"id">>, Body), Code, Error);
error(ReqId, Code, Error) ->
    Msg = #{
        jsonrpc => <<"2.0">>,
        id => ReqId,
        error => #{
            code => Code,
            message => Error
        }
    },
    gen_server:cast(?MODULE, {send, Msg}).

handle_response(Body) ->
    gen_server:cast(?MODULE, {response, Body}).

init(_) ->
    {ok, IoDevice} = application:get_env(sam, stdio),
    ets:new(?REQUESTS, [set, named_table]),
    ets:new(?PROCS, [set, named_table]),
    {ok, #st{
        io_dev = IoDevice,
        req_id = 0
    }}.

terminate(_, _) ->
    ok.


handle_call(next_req_id, _From, St) ->
    #st{req_id = ReqId} = St,
    {reply, ReqId, St#st{req_id = ReqId + 1}};
handle_call({request, ReqId, ReqMsg}, {Client, _} = From, St) ->
    #st{
        io_dev = IoDevice
    } = St,
    Ref = erlang:monitor(process, Client),
    ets:insert(?REQUESTS, {ReqId, Ref, From}),
    ets:insert(?PROCS, {Ref, ReqId}),
    do_send(IoDevice, ReqMsg),
    {noreply, St};
handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast({send, Body}, St) ->
    #st{io_dev = IoDevice} = St,
    do_send(IoDevice, Body),
    {noreply, St};
handle_cast({response, Body}, St) ->
    ReqId = maps:get(<<"id">>, Body),
    case ets:lookup(?REQUESTS, ReqId) of
        [{ReqId, Ref, From}] ->
            gen_server:reply(From, {ok, Body}),
            ets:delete(?REQUESTS, ReqId),
            ets:delete(?PROCS, Ref),
            erlang:demonitor(Ref, [flush]);
        [] ->
            lager:warning("Response for dead process: ~p", [Body])
    end,
    {noreply, St};
handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.


handle_info({'DOWN', Ref, process, Pid, Reason}, St) ->
    case ets:lookup(?PROCS, Ref) of
        [{Ref, ReqId}] ->
            % Client died before receiving a response
            ets:delete(?REQUESTS, ReqId),
            ets:delete(?PROCS, Ref);
        [] ->
            lager:warning("Unknown process ~p died: ~p", [Pid, Reason])
    end,
    {noreply, St};            
handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.


do_send(IoDevice, #{} = Msg) ->
    %lager:debug("STDOUT: ~p", [Msg]),
    Body = jsx:encode(Msg),
    CL = size(Body),
    IoData = io_lib:format("Content-Length: ~b\r\n\r\n~s", [CL, Body]),
    do_send(IoDevice, iolist_to_binary(IoData));
do_send(IoDevice, Data) when is_binary(Data) ->
    io:put_chars(IoDevice, Data).
