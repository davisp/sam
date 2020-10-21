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
                [#{type := remote_call, data := {Mod, Fun, Arity}} | _] ->
                    case sam_db:uri_for_mod(Mod) of
                        {ok, RemoteUri} ->
                            lookup_location(RemoteUri, Fun, Arity);
                        _ ->
                            null
                    end;
                [#{type := local_call, data := {Fun, Arity}} | _] ->
                    lookup_location(Uri, POIs, Fun, Arity);
                _ ->
                    null
            end;
        _Else ->
            null
    end,
    sam_provider:response(Msg, Resp).

lookup_location(Uri, Fun, Arity) ->
    case sam_db:get_doc(Uri) of
        {ok, #{pois := POIs}} ->
            lookup_location(Uri, POIs, Fun, Arity);
        _ ->
            null
    end.

lookup_location(Uri, POIs, Fun, Arity) ->
    Functions = lists:filter(fun(POI) ->
        case POI of
            #{type := function, data := {Fun, Arity}} -> true;
            _ -> false
        end
    end, POIs),
    case Functions of
        [#{range := Range} | _] ->
            #{uri => Uri, range => Range};
        _ ->
            null
    end.
