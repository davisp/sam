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
        #{pois := POIs} ->
            CallQuery = #{
                type => [remote_call, local_call],
                range => fun(Range) -> sam_poi:overlaps(Range, Line, Char) end
            },
            case sam_poi:search(CallQuery, [data], {Line, Char}, POIs) of
                [#{data := {M, F, A}} | _] ->
                    lager:info("Got remote call", []),
                    return_refs({M, F, A});
                [#{data := {F, A}} | _] ->
                    case sam_poi:search(#{type => module}, [data], POIs) of
                        #{data := M} ->
                            lager:info("Got local call", []),
                            return_refs({M, F, A});
                        _ ->
                            null
                    end;
                _ ->
                    lager:info("No call", []),
                    null
            end;
        not_found ->
            null
    end,
    sam_provider:response(Msg, Resp).

return_refs(MFA) ->
    case sam_db:get_refs(MFA) of
        not_found ->
            lager:info("No refs for: ~p", [MFA]),
            null;
        Refs ->
            lists:foldl(fun({Uri, Ranges}, Acc0) ->
                lists:foldl(fun(Range, Acc1) ->
                    [#{uri => Uri, range => Range} | Acc1]
                end, Acc0, Ranges)
            end, [], Refs)
    end.
