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

-module(sam_documentation).

-export([
    describe/3
]).

-spec describe(atom(), atom(), integer()) -> binary().
describe(M, F, A) ->
    try
        {Uri, POIs} = load_pois(M),
        Desc = load_raw(Uri, F, A, POIs),
        case erlfmt:format_string(binary_to_list(Desc), []) of
            {ok, Formatted, _} ->
                iolist_to_binary(string:trim(Formatted));
            _ ->
                not_found
        end
    catch
        throw:done ->
            not_found;
        T:R:S ->
            lager:error("Failed to render documentation: ~p :: ~p", [{T, R}, S]),
            not_found
    end.

load_pois(Module) ->
    case sam_db:get_doc_for_mod(Module) of
        #{uri := Uri, pois := POIs} ->
            {Uri, POIs};
        not_found ->
            throw(done)
    end.

load_raw(Uri, Fun, Arity, POIs) ->
    SpecQuery = #{
        type => spec,
        data => fun(Data) -> Data == {Fun, Arity} end
    },
    FunQuery = #{
        type => function,
        data => fun(Data) -> Data == {Fun, Arity} end
    },
    case sam_poi:search(SpecQuery, [range], POIs) of
        [#{range := Range} | _] ->
            extract(Uri, Range);
        _ ->
            case sam_poi:search(FunQuery, [range], POIs) of
                [#{range := Range} | _] ->
                    Raw = extract(Uri, Range),
                    case re:run(Raw, <<"(?<A>.*?)(when|->)">>, [{capture, all_names, binary}]) of
                        {match, [Head]} ->
                            Head;
                        nomatch ->
                            throw(done)
                    end;
                _ ->
                    throw(done)
            end
    end.

extract(Uri, Range) ->
    #{
        start := #{line := SLine, character := SChar},
        'end' := #{line := ELine, character := EChar}
    } = Range,
    case file:read_file(sam_uri:to_path(Uri)) of
        {ok, Data} ->
            FileLines = binary:split(Data, <<"\n">>, [global]),
            SpecLines = lists:sublist(FileLines, SLine + 1, ELine - SLine + 1),
            EOffset = size(lists:last(SpecLines)) - EChar,
            AllLines = iolist_to_binary(SpecLines),
            SpecSize = size(AllLines) - EOffset,
            <<_:SChar/binary, Spec:SpecSize/binary, _/binary>> = AllLines,
            Spec;
        _ ->
            throw(done)
    end.
    