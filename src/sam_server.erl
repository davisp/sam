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
    handle_request/1,
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


-record(st, {
    request_id = 0
}).


start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).


handle_request(Request) ->
    gen_server:cast(?MODULE, {handle_request, Request}).


init(_) ->
    ets:new(?MODULE, [set, named_table]),
    {ok, #st{}}.


terminate(_, _) ->
    ok.


handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.


handle_cast({handle_request, JSONRequest}, St) ->
    case sam_msg:from_json(JSONRequest) of
        {ok, Msg} ->
            start_handler(Msg);
        {error, Error} ->
            respond(sam_msg:error(Error))
    end,
    {noreply, St};
handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.


handle_info({'DOWN', Ref, process, Pid, Reason}, St) ->
    case ets:lookup(?MODULE, Ref) of
        [] when Reason == normal ->
            % Process responded and left this world peacefully
            ok;
        [] ->
            % Bad process exit after responding?
            lager:warn("Request handler died abnormally: ~p", [Reason]);        
        [{Ref, Pid, _ReqId}] ->
            
    end,
    {noreply, St};            
handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.


code_change(_OldVsn, St, _Extra) ->
    {ok, St}.


start_handler(Msg) ->
    ReqId = maps:get(req_id, Msg, undefined),
    {ok, Pid} = sam_handler:start(Request),
    Ref = erlang:monitor(process, Pid),
    ets:insert(?MODULE, {Ref, Pid, ReqId}).
