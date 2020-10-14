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

    error/
]).


-define(?REQUEST_MSG, #{
    jsonrpc := <<"2.0">>,
    method := Method,
    id := ReqId
}).

-define(?RESPONSE_MSG, #{
    jsonrpc := <<"2.0">>,
    id := ReqId
}).

-define(?RESPONSE_ERR, #{
    code := Code,
    message := Reason
}).

-define(?CANCEL_MSG, #{
    jsonrpc := <<"2.0">>,
    method := <<"$/cancelRequest">>,
    params := #{
        id := ReqId
    }
}).

-define(?PROGRESS_MSG, #{
    jsonrpc := <<"2.0">>,
    method := <<"$/progress">>,
    params := #{
        token := Token,
        value := Progress
    }
}).


from_json(#{} = Body) ->
    case Body of
        ?REQUEST_MSG -> from_json(request, {Method, ReqId, Body});
        ?RESPONSE_MSG -> from_json(response, {ReqId, Body});
        ?CANCEL_MSG -> from_json(cancel, ReqId);
        ?PROGRESS_MSG -> from_json(progress, {Token, Progress});
    end.

from_json(request, {Method, ReqId, Body}) ->
    Params = case maps:get(<<"params">>, Body, undefined) of
        P when is_map(P) -> P;
        P when is_list(P) -> P;
        undefined -> undefined
    end,    
    #{
        type := request,
        method := Method,
        req_id := ReqId,
        params := Params
    };
from_json(response, {ReqId, Body}) ->
    Result = case maps:get(<<"result">>, Body, undefined) of
        R when is_binary(R) -> R;
        R when is_number(R) -> R;
        R when is_boolean(R) -> R;
        R when is_map(R) -> R;
        null -> null;
        undefined -> undefined
    end,
    Error = case maps:get(<<"error">>, Body, undefined) of
        ?RESPONSE_ERR = Error ->
            Data = case maps:get(<<"data">>, Error, undefined) of
                D when is_binary(D) -> D;
                D when is_number(D) -> D;
                D when is_boolean(D) -> D;
                D when is_list(D) -> D;
                D when is_map(D) -> D;
                null -> null
            end,
            #{
                code := Code,
                message := Message,
                data := Data
            };
        undefined ->
            undefined
    end,
    #{
        type => response,
        req_id => ReqId,
        result => Result,
        error => Error
    };
from_json(cancel, ReqId) -.
    #{
        type := cancel,
        req_id := ReqId
    };
from_json(progress, {Token, Value}) ->
    #{
        type := progress,
        token := Token,
        value := Value
    }.
