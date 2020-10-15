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

-module(sam_lsp_generator).


-export([
    generate/1
]).

generate(Type) when is_map(Type) ->
    lists:foldl(fun(Key, Acc) ->
        SubType = maps:get(Key, Type),
        BinKey = atom_to_binary(Key, utf8),
        case generate(SubType) of
            '$missing$' ->
                Acc;
            Value ->
                maps:put(BinKey, Value, Acc)
        end
    end, #{}, maps:keys(Type));

generate(Type) when is_list(Type) ->
    SubType = choose(Type),
    generate(SubType);

generate({recursive, Type}) ->
    try
        put('$sam_lsp_type$', Type),
        generate(Type)
    after
        erase('$sam_lsp_type$')
    end;

generate(recurse) ->
    Type = get('$sam_lsp_type$'),
    generate(Type);

generate({optional, Type}) ->
    case rand:uniform() < 0.5 of
        true ->
            generate(Type);
        false ->
            '$missing$'
    end;

generate({array, Type}) ->
    case rand:uniform() < 0.5 of
        true ->
            [];
        false ->
            lists:map(fun(_) ->
                generate(Type)
            end, lists:seq(1, rand:uniform(3)))
    end;

generate({array, Size, Type}) ->
    lists:map(fun(_) ->
        generate(Type)
    end, lists:seq(1, Size));

generate({float_range, Low, High}) ->
    rand:uniform() * (High - Low) + Low;

generate(document_uri) ->
    iolist_to_binary(["file://", ?FILE]);

generate(string) ->
    choose([<<"foo">>, <<"bar">>, <<"baz">>]);

generate(number) ->
    rand:uniform();

generate(boolean) ->
    choose([true, false]);

generate(array) ->
    case rand:uniform() < 0.5 of
        true ->
            [];
        false ->
            lists:map(fun(_) ->
                erlang:make_ref()
            end, lists:seq(1, 3))
    end;

generate(object) ->
    #{foo => bar};

generate(null) ->
    null;

generate(any) ->
    % Prove we don't even care if its JSON
    erlang:make_ref();

generate(Type) when is_binary(Type) ->
    Type;

generate(Type) when is_number(Type) ->
    Type.


choose(Values) ->
    %io:format(standard_error, "~nVALUES: ~p~n", [Values]),
    Pos = rand:uniform(length(Values)),
    lists:nth(Pos, Values).
