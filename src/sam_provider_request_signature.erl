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

-module(sam_provider_request_signature).

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
            find_signatures(Uri, Text, Line, Char);
        not_found ->
            null
    end,
    sam_provider:response(Msg, Resp).

find_signatures(_Uri, Text, Line, Char) ->
    case find_mod_fun(Text, Line, Char) of
        {ModName, FunName} ->
            get_exports(ModName, FunName);
        not_found ->
            null
    end.

find_mod_fun(Bin, LineNum, Char) ->
    Lines = binary:split(Bin, <<"\n">>, [global]),
    Line = case LineNum + 1 > length(Lines) of
        true -> <<>>;
        false -> lists:nth(LineNum + 1, Lines)
    end,
    BeforeChar = case Char < size(Line) of
        true -> binary:part(Line, 0, Char);
        false -> Line
    end,
    case re:run(BeforeChar, ?PATTERN, [{capture, all_names, binary}]) of
        {match, [ModBin, FunBin]} ->
            M = list_to_atom(binary_to_list(ModBin)),
            F = list_to_atom(binary_to_list(FunBin)),
            {M, F};
        _ ->
            not_found
    end.

get_exports(ModName, FunName) ->
    case sam_db:get_doc_for_mod(ModName) of
        #{pois := POIs} ->
            ExportedFuns = sam_poi:search(#{type => exported_fun}, [data], POIs),
            case ExportedFuns of
                [_ | _] ->
                    Infos = lists:flatmap(fun(#{data := {F, A}}) ->
                        case F == FunName of
                            true ->
                                case sam_documentation:describe(ModName, F, A) of
                                    Desc when is_binary(Desc) ->
                                        [#{label => Desc}];
                                    not_found ->
                                        []
                                end;
                            false ->
                                []
                        end
                    end, lists:sort(ExportedFuns)),
                    case Infos of
                        [] -> null;
                        _ -> #{signatures => Infos}
                    end;
                _ ->
                    null
            end;
        not_found ->
            null
    end.
