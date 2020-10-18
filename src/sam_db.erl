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

-module(sam_db).
-behaviour(gen_server).

-export([
    start_link/1,

    add_document/1,

    lookup_pois/2
]).

-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).

start_link(_RootUri) ->
    ok.

add_document(_Doc) ->
    ok.

lookup_pois(_Uri, _Poi) ->
    ok.

init(_) ->
    {ok, nil}.

terminate(_Reason, _St) ->
    ok.

handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.

handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.
