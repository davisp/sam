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

-module(sam_provider_request_formatting).

-export([
    handle/1
]).

%#{
%    <<"id">> => 1,
%    <<"jsonrpc">> => <<"2.0">>,
%    <<"method">> => ,
%    <<"params">> => #{
%        <<"textDocument">> => #{
%            <<"uri">> => <<"file:///Volumes/Macintosh%20HD/Users/davisp/github/davisp/sam/src/sam_file_server.erl">>
%        },
%        <<"options">> => #{
%            ...
%        }
%    }
%}

handle(#{<<"params">> := Params} = Msg) ->
    #{
        <<"textDocument">> := #{
            <<"uri">> := RawUri
        }
    } = Params,
    Uri = sam_uri:normalize(RawUri),
    Resp = case sam_file_server:lookup(Uri) of
        {ok, Text} ->
            format_text(Uri, Text);
        not_found ->
            null
    end,
    sam_provider:response(Msg, Resp).

format_text(_Uri, Text) ->
    TextAsString = binary_to_list(Text),
    case erlfmt:format_string(TextAsString, []) of
        {ok, Formatted, _} ->
            OriginalLines = binary:split(Text, <<"\n">>, [global]),
            LastLine = length(OriginalLines) - 1,
            LastChar = size(lists:last(OriginalLines)),
            [#{
                range => #{
                    start => #{line => 0, character => 0},
                    'end' => #{line => LastLine, character => LastChar}
                },
                newText => iolist_to_binary(Formatted)
            }];
        _ ->
            null
    end.
