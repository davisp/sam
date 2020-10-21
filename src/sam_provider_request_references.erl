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

-module(sam_provider_request_references).

-export([
    handle/1
]).

% #{
%    <<"id">> => 4,
%    <<"jsonrpc">> => <<"2.0">>,
%    <<"method">> => <<"textDocument/references">>,
%    <<"params">> => #{
%        <<"context">> => #{
%            <<"includeDeclaration">> => true
%        },
%        <<"position">> => #{
%            <<"character">> => 13,
%            <<"line">> => 195
%        },
%        <<"textDocument">> => #{
%            <<"uri">> => <<"file:///Volumes/Macintosh%20HD/Users/davisp/github/davisp/sam/src/sam_db.erl">>
%        }
%    }
%}

-include("sam.hrl").

handle(#{<<"params">> := Params} = Msg) ->
    #{
        <<"position">> := #{
            <<"line">> := Line,
            <<"character">> := Char
        },
        <<"textDocument">> := #{
            <<"uri">> := RawUri
        }
    } = Params,
    Uri = sam_uri:normalize(RawUri),
    Resp = case sam_db:get_doc(Uri) of
        {ok, #{pois := POIs}} ->
            POIsAt = lists:filter(fun(POI) -> sam_poi:overlaps(POI, Line, Char) end, POIs),
            Calls = lists:filter(fun(POI) ->
                case POI of
                    #{type := remote_call} -> true;
                    #{type := local_call} -> true;
                    _ -> false
                end
            end, POIsAt),
            case Calls of
                [#{type := remote_call, data := MFA} | _] ->
                    return_refs(MFA);
                [#{type := local_call, data := {Fun, Arity}} | _] ->
                    case get_mod(POIs) of
                        not_found -> null;
                        ModName -> return_refs({ModName, Fun, Arity})
                    end;
                _ ->
                    null
            end;
        _Else ->
            null
    end,
    sam_provider:response(Msg, Resp).

return_refs(MFA) ->
    case sam_db:get_refs(MFA) of
        {ok, Refs} ->
            lists:foldl(fun({Uri, Ranges}, Acc0) ->
                lists:foldl(fun(Range, Acc1) ->
                    [#{uri => Uri, range => Range} | Acc1]
                end, Acc0, Ranges)
            end, [], Refs);
        not_found ->
            null
    end.

get_mod(not_found) ->
    not_found;
get_mod(POIs) ->
    case lists:filter(fun(#{type := module}) -> true; (_) -> false end, POIs) of
        [#{type := module, data := ModName} | _] ->
            ModName;
        _ ->
            not_found
    end.
