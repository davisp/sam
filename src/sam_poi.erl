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

-module(sam_poi).

-export([
    search/3,
    match/2,
    extract/2,
    overlaps/3,
    range_to_tuple/1
]).


search(Pattern, Fields, POIs) ->
    lists:flatmap(fun(POI) ->
        case match(Pattern, POI) of
            true -> [extract(Fields, POI)];
            false -> []
        end
    end, POIs).

match(Pattern, POI) when is_map(Pattern), is_map(POI) ->
    lists:all(fun({K, V}) ->
        match({K, V}, POI)
    end, maps:to_list(Pattern));
match({Field, Matcher}, POI) when is_atom(Field), is_atom(Matcher), is_map(POI) ->
    try
        maps:get(Field, POI) == Matcher
    catch _:_ ->
        false
    end;
match({Field, Matchers}, POI) when is_atom(Field), is_list(Matchers), is_map(POI) ->
    lists:any(fun(M) ->
        match({Field, M}, POI)
    end, Matchers);
match({Field, Matcher}, POI) when is_atom(Field), is_function(Matcher), is_map(POI) ->
    try
        Matcher(maps:get(Field, POI))
    catch _:_ ->
        false
    end.

extract(Field, POI) when is_atom(Field), is_map(POI) ->
    maps:get(Field, POI);
extract(Fields, POI) when is_list(Fields), is_map(POI) ->
    lists:foldl(fun(Field, Acc) ->
        maps:put(Field, maps:get(Field, POI), Acc)
    end, #{}, Fields).

overlaps(POI, Line, Char) ->
    #{range := #{
        start := #{line := SLine, character := SChar},
        'end' := #{line := ELine, character := EChar}
    }} = POI,
    AfterStart = SLine =< Line andalso SChar =< Char,
    BeforeEnd = ELine >= Line andalso EChar >= Char,
    AfterStart andalso BeforeEnd.

range_to_tuple(#{start := Start, 'end' := End}) ->
    #{
        line := StartLine,
        character := StartChar
    } = Start,
    #{
        line := EndLine,
        character := EndChar
    } = End,
    {StartLine, StartChar, EndLine, EndChar}.
