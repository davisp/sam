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

-module(sam_provider_request_unknown).

-export([
    handle/1
]).

-include("sam.hrl").

handle(#{} = Msg) ->
    lager:info("Unknown request: ~p", [Msg]),
    Reason = io_lib:format("unknown_request_method : ~s", [maps:get(<<"method">>, Msg)]),
    sam_client:error(Msg, ?JSONRPC_UNKNOWN_ERROR_CODE, iolist_to_binary(Reason)),
    exit(self(), kill).
