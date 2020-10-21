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

-module(sam_provider_request_symbols).

-export([
    handle/1
]).

% #{
%    <<"id">> => 4,
%    <<"jsonrpc">> => <<"2.0">>,
%    <<"method">> => <<"textDocument/documentSymbols">>,
%    <<"params">> => #{
%        <<"textDocument">> => #{
%            <<"uri">> => <<"file:///Volumes/Macintosh%20HD/Users/davisp/github/davisp/sam/src/sam_db.erl">>
%        }
%    }
%}

-include("sam.hrl").

handle(#{<<"params">> := Params} = Msg) ->
    #{
        <<"textDocument">> := #{
            <<"uri">> := RawUri
        }
    } = Params,
    Uri = sam_uri:normalize(RawUri),
    POIs = case sam_db:get_doc(Uri) of
        {ok, #{pois := Ps}} -> Ps;
        _ -> []
    end,

    SortedPOIs = lists:sort(fun(A, B) ->
        ATup = sam_poi:range_to_tuple(maps:get(range, A)),
        BTup = sam_poi:range_to_tuple(maps:get(range, B)),
        ATup =< BTup
    end, POIs),

    Symbols = lists:map(fun(POI) ->
        #{
            type := Type,
            data := Data,
            range := Range
        } = POI,
        Name = iolist_to_binary(io_lib:format("~w", [Data])),
        Kind = case Type of
            module -> ?LSP_SYMBOL_KIND_MODULE;
            export -> ?LSP_SYMBOL_KIND_INTERFACE;
            exported_fun -> ?LSP_SYMBOL_KIND_FUNCTION;
            import -> ?LSP_SYMBOL_KIND_PACKAGE;
            imported_fun -> ?LSP_SYMBOL_KIND_FUNCTION;
            include -> ?LSP_SYMBOL_KIND_FILE;
            include_lib -> ?LSP_SYMBOL_KIND_FILE;
            record -> ?LSP_SYMBOL_KIND_STRUCT;
            type -> ?LSP_SYMBOL_KIND_TYPE_PARAMETER;
            export_type -> ?LSP_SYMBOL_KIND_TYPE_PARAMETER;
            exported_type -> ?LSP_SYMBOL_KIND_TYPE_PARAMETER;
            spec -> ?LSP_SYMBOL_KIND_INTERFACE;
            callback -> ?LSP_SYMBOL_KIND_INTERFACE;
            attribute -> ?LSP_SYMBOL_KIND_PROPERTY;
            function -> ?LSP_SYMBOL_KIND_FUNCTION;
            remote_call -> ?LSP_SYMBOL_KIND_OPERATOR;
            local_call -> ?LSP_SYMBOL_KIND_OPERATOR;
            remote_fun -> ?LSP_SYMBOL_KIND_FUNCTION;
            local_fun -> ?LSP_SYMBOL_KIND_FUNCTION;
            record_index -> ?LSP_SYMBOL_KIND_CONSTANT;
            record_field -> ?LSP_SYMBOL_KIND_FIELD;
            record_access -> ?LSP_SYMBOL_KIND_OBJECT;
            macro -> ?LSP_SYMBOL_KIND_CONSTANT;
            _ -> ?LSP_SYMBOL_KIND_NULL
        end,
        #{
            name => Name,
            kind => Kind,
            location => #{
                uri => Uri,
                range => Range
            }
        }
    end, SortedPOIs),

    Resp = case Symbols of
        [] -> null;
        _ -> Symbols
    end,
    sam_provider:response(Msg, Resp).