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

-module(sam_provider_request_hover).

-export([
    handle/1
]).

%#{
%    <<"id">> => 1,
%    <<"jsonrpc">> => <<"2.0">>,
%    <<"method">> => ,
%    <<"params">> => #{
%        <<"position">> => #{
%            <<"character">> => 13,
%            <<"line">> => 53
%        },
%        <<"textDocument">> => #{
%            <<"uri">> => <<"file:///Volumes/Macintosh%20HD/Users/davisp/github/davisp/sam/src/sam_file_server.erl">>
%        }
%    }
%}

-define(PATTERN, <<"(?<a>[a-z][a-zA-Z0-9@_]*):(?<b>[a-z][a-zA-Z0-9@_]*)\\($">>).

handle(#{<<"params">> := Params} = Msg) ->
    #{
        <<"position">> := #{
            <<"character">> := Char,
            <<"line">> := Line
        },
        <<"textDocument">> := #{
            <<"uri">> := RawUri
        }
    } = Params,
    Uri = sam_uri:normalize(RawUri),
    Resp = case sam_file_server:lookup(Uri) of
        {ok, Text} ->
            find_item(Uri, Text, Line, Char);
        not_found ->
            null
    end,
    sam_provider:response(Msg, Resp).

find_item(Uri, Text, Line, Char) ->
    POIs = sam_parser:parse(Uri, Text),
    Query = #{
        type => [remote_call, local_call],
        range => fun(Range) -> sam_poi:overlaps(Range, Line, Char) end
    },
    case sam_poi:search(Query, [data, range], {Line, Char}, POIs) of
        [#{data := {M, F, A}, range := Range} | _] ->
            describe(M, F, A, Range);
        [#{data := {F, A}, range := Range} | _] ->
            case sam_poi:search(#{type => module}, [data], POIs) of
                [#{data := Module} | _] ->
                    describe(Module, F, A, Range);
                _ ->
                    null
            end;
        _ ->
            null
    end.

describe(M, F, A, Range) ->
    case sam_documentation:describe(M, F, A) of
        Desc when is_binary(Desc) ->
            #{
                contents => #{
                    kind => <<"plaintext">>,
                    value => Desc
                },
                range => Range
            };
        not_found ->
            null
    end.
