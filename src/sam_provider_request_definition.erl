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

-module(sam_provider_request_definition).

-export([
    handle/1
]).

% #{
%    <<"id">> => 1,
%    <<"jsonrpc">> => <<"2.0">>,
%    <<"method">> => <<"textDocument/definition">>,
%    <<"params">> => #{
%        <<"position">> => #{<<"character">> => 4,<<"line">> => 25},
%        <<"textDocument">> => #{<<"uri">> => <<"file:///Volumes/Macintosh%20HD/Users/davisp/github/davisp/sam/src/sam_sup.erl">>}
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
                    case sam_db:get_doc_for_mod(M) of
                        #{uri := RemoteUri, pois := RemotePOIs} ->
                            FunQuery = #{
                                type => function,
                                data => fun(Data) -> Data == {F, A} end
                            },
                            case sam_poi:search(FunQuery, [range], RemotePOIs) of
                                [#{range := Range} | _] ->
                                    #{uri => RemoteUri, range => Range};
                                _ ->
                                    null
                            end;
                        not_found ->
                            null
                    end;
                [#{data := {F, A}} | _] ->
                    FunQuery = #{
                        type => function,
                        data => fun(Data) -> Data == {F, A} end
                    },
                    case sam_poi:search(FunQuery, [range], POIs) of
                        [#{range := Range} | _] ->
                            #{uri => Uri, range => Range};
                        _ ->
                            null
                    end;
                _ ->
                    null
            end;
        not_found ->
            null
    end,
    sam_provider:response(Msg, Resp).