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

-module(sam_sup).

-behavior(supervisor).

-export([
    start_link/0
]).

-export([
    init/1
]).

start_link() ->
    supervisor:start_link({local, ?MODULE}, ?MODULE, []).

init([]) ->
    replace_group_leader(),
    Flags = #{
        strategy => rest_for_one,
        intensity => 5,
        period => 60
    },
    Children = [
        #{id => sam_client, start => {sam_client, start_link, []}},
        #{id => sam_server, start => {sam_server, start_link, []}},
        #{id => sam_file_server, start => {sam_file_server, start_link, []}},
        #{id => sam_db_indexer, start => {sam_db_indexer, start_link, []}},
        #{id => sam_db, start => {sam_db, start_link, []}},
        #{id => sam_db_scanner, start => {sam_db_scanner, start_link, []}},
        #{id => sam_diagnostics, start => {sam_diagnostics, start_link, []}},
        #{id => sam_stdio, start => {sam_stdio, start_link, []}}
    ],
    {ok, {Flags, Children}}.


% Good idea stolen from Erlang_LS to disable all
% messages to stdio to avoid corrupting the JSON-RPC
% protocol.
replace_group_leader() ->
    application:set_env(sam, stdio, erlang:group_leader()),
    Pid = erlang:spawn(fun lager_redirect/0),
    erlang:group_leader(Pid, self()).
    

lager_redirect() ->
    receive
        Message ->
            lager:info("group_leader message: ~p", [Message]),
            case Message of
                {io_request, From, ReplyAs, getopts} ->
                    From ! {io_reply, ReplyAs, []};
                {io_request, From, ReplyAs, _} ->
                    From ! {io_reply, ReplyAs, ok};
                _ ->
                    ok
            end,
            lager_redirect()
    end.

