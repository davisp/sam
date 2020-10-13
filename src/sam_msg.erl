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

-module(sam_msg).


-export([
    from_json/1,

    error/1
]).


from_json(#{} = Request) ->
    case maps:get(<<"jsonrpc">>, Request, null) of
        <<"2.0">> -> ok;
        Else -> {error, {?JSON_RPC_INVALID_REQUEST, bad_jsonrpc_version, Else}}
    end,
    ReqId = maps:get(<<"id">>, Request, undefined) of
        undefined ->


error({Code, Reason}) ->
    #{
        code: Code,
        message: Reason
    }.

