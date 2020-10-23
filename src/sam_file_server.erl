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

-module(sam_file_server).
-behavior(gen_server).

-export([
    start_link/0,

    opened/2,
    changed/2,
    closed/1,
    lookup/1
]).

-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).

-define(DOCS, sam_file_server_table).

start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

opened(Uri, Text) ->
    ets:insert(?DOCS, {Uri, Text}).

changed(Uri, Text) ->
    ets:insert(?DOCS, {Uri, Text}).

closed(Uri) ->
    ets:delete(?DOCS, Uri).

lookup(Uri) ->
    case ets:lookup(?DOCS, Uri) of
        [{Uri, Text}] -> {ok, Text};
        [] -> not_found
    end.

init(_) ->
    ets:new(?DOCS, [
        set,
        named_table,
        public,
        {write_concurrency, true},
        {read_concurrency, true}
    ]),
    {ok, nil}.

terminate(_, _) ->
    ok.

handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.

handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.
