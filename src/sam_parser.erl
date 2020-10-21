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

-module(sam_parser).

-export([
    parse/2
]).

parse(Uri, Source) ->
    case sam_pp:run(Source) of
        {ok, FormsAndTokens} ->
            lists:flatten(lists:map(fun({Form, Tokens}) ->
                try
                    process(Form, Tokens)
                catch T:R:S ->
                    Fmt = "Failed to process form in: ~s :: ~p~n~p~n~p",
                    lager:warning(Fmt, [Uri, {T, R}, Form, S]),
                    []
                end
            end, FormsAndTokens));
        error ->
            lager:warning("Failed to parse: ~s", [Uri])
    end.

process({attribute, Anno, module, {ModName, _Args}}, Tokens) ->
    process({attribute, Anno, module, ModName}, Tokens);
process({attribute, _, module, ModName}, Tokens) when is_atom(ModName) ->
    #{
        type => module,
        data => ModName,
        range => tokens_to_range(Tokens)
    };
process({attribute, _, behavior, Behavior}, Tokens) ->
    #{
        type => behavior,
        data => Behavior,
        range => tokens_to_range(Tokens)
    };
process({attribute, Anno, behaviour, Behavior}, Tokens) ->
    process({attribute, Anno, behavior, Behavior}, Tokens);
process({attribute, _, export, FArityList}, Tokens) ->
    Export = #{
        type => export,
        data => [{F, A} || {_Anno, F, A} <- FArityList],
        range => tokens_to_range(Tokens)
    },
    ExportFuns = lists:map(fun({Anno, F, A}) ->
        #{
            type => exported_fun,
            data => {F, A},
            range => anno_to_range(Anno, 0, atom_len(F))
        }
    end, FArityList),
    [Export | ExportFuns];
process({attribute, _, import, {ModName, FArityList}}, Tokens) ->
    Import = #{
        type => import,
        data => [{ModName, F, A} || {_Anno, F, A} <- FArityList],
        range => tokens_to_range(Tokens)
    },
    ImportedFuns = lists:map(fun({Anno, F, A}) ->
        #{
            type => imported_fun,
            data => {ModName, F, A},
            range => anno_to_range(Anno, 0, atom_len(F))
        }
    end, FArityList),
    [Import | ImportedFuns];
process({attribute, _, include, Path}, Tokens) ->
    #{
        type => include,
        data => Path,
        range => tokens_to_range(Tokens)
    };
process({attribute, _, include_lib, Path}, Tokens) ->
    #{
        type => include_lib,
        data => Path,
        range => tokens_to_range(Tokens)
    };
process({attribute, _, record, {RecName, Fields}}, Tokens) ->
    {FieldNames, FieldPOIs} = lists:unzip(lists:map(fun(Field) ->
        case Field of
            {record_field, _, {atom, Anno, FN}} ->
                % Simple field name
                {FN, #{
                    type => record_field,
                    data => {RecName, FN},
                    range => anno_to_range(Anno, 0, atom_len(FN))
                }};
            {record_field, _, {atom, Anno, FN}, _} ->
                % Field name with default value
                {FN, #{
                    type => record_field,
                    data => {RecName, FN},
                    range => anno_to_range(Anno, 0, atom_len(FN))
                }};
            {typed_record_field, {record_field, _, {atom, Anno, FN}}, _} ->
                % Field name with type
                {FN, #{
                    type => record_field,
                    data => {RecName, FN},
                    range => anno_to_range(Anno, 0, atom_len(FN))
                }};
            {typed_record_field, {record_field, _, {atom, Anno, FN}, _}, _} ->
                % Field name with type and default value
                {FN, #{
                    type => record_field,
                    data => {RecName, FN},
                    range => anno_to_range(Anno, 0, atom_len(FN))
                }}
        end
    end, Fields)),
    Record = #{
        type => record,
        data => {RecName, FieldNames},
        range => tokens_to_range(Tokens)
    },
    [Record | FieldPOIs];
process({attribute, _, type, {TypeName, _Type, _Args}}, Tokens) ->
    #{
        type => type,
        data => {TypeName, public},
        range => tokens_to_range(Tokens)
    };
process({attribute, Anno, export_type, FArityList}, Tokens) ->
    Export = #{
        type => export_type,
        data => [{T, A} || {_, T, A} <- FArityList],
        range => tokens_to_range(Tokens)
    },
    Types = lists:map(fun({Type, Arity}) ->
        #{
            type => exported_type,
            data => {Type, Arity},
            % I'm not motivated to tweak export_type parsing
            % just now so we just anchor these to the attribute
            % seeing as they'll mostly be for features rather than
            % highlighting.
            range => anno_to_range(Anno, 0, atom_len(export_type))
        }
    end, FArityList),
    [Export | Types];
process({attribute, _, opaque, {TypeName, _Type, _Args}}, Tokens) ->
    #{
        type => type,
        data => {TypeName, private},
        range => tokens_to_range(Tokens)
    };
process({attribute, _, spec, {SpecFun, _}}, Tokens) ->
    #{
        type => spec,
        data => SpecFun,
        range => tokens_to_range(Tokens)
    };
process({attribute, _, callback, {CBFun, _}}, Tokens) ->
    #{
        type => callback,
        data => CBFun,
        range => tokens_to_range(Tokens)
    };
process({attribute, _, file, {_Name, _Line}}, _Tokens) ->
    % This a compiler directive to report different
    % line/column values for errors. This is for things like
    % .yrl files that generate .erl output so the errors
    % respect the location in .yrl. I don't think I need
    % to support this here.
    [];
process({attribute, _, AttrName, _Expr}, Tokens) ->
    % Catch-all for unknown attributes
    #{
        type => attribute,
        data => AttrName,
        range => tokens_to_range(Tokens)
    };
process({function, _, Name, Arity, _Clauses} = Tree, Tokens) ->
    Function = #{
        type => function,
        data => {Name, Arity},
        range => tokens_to_range(Tokens)
    },
    [Function] ++ process_tree(Tree);
process(Form, _Tokens) ->
    io:format(standard_error, "Unknown form: ~p~n", [Form]).


% TODO: call, fun, record_access, record_expr, variable, atom, macro
process_tree({call, CloseParen, {remote, _, ModExpr, FunExpr}, Args}) ->
    Mod = case ModExpr of
        {atom, _, M} -> [M];
        {macro, _, 'MODULE'} -> ['?MODULE'];
        _ -> []
    end,
    Fun = case FunExpr of
        {atom, _, F} -> [F];
        _ -> []
    end,
    CallPOI = case Mod /= [] andalso Fun /= [] of
        true ->
            [#{
                type => remote_call,
                data => {hd(Mod), hd(Fun), length(Args)},
                range => annos_to_range(element(2, ModExpr), CloseParen)
            }];
        false ->
            []
    end,
    CallPOI ++ lists:map(fun process_tree/1, [ModExpr, FunExpr | Args]);
process_tree({call, CloseParen, {atom, Start, Fun}, Args}) ->
    {Type, FunDef} = case sam_erl_internal:bif(Fun, length(Args)) of
        true -> {remote_call, {erlang, Fun, length(Args)}};
        false -> {local_call, {Fun, length(Args)}}
    end,
    CallPOI = [#{
        type => Type,
        data => FunDef,
        range => annos_to_range(Start, CloseParen)
    }],
    CallPOI ++ lists:map(fun process_tree/1, Args);
process_tree({'fun', Anno, {function, M, F, A}}) ->
    MFAType = {element(1, M), element(1, F), element(1, A)},
    POI = case MFAType of
        {atom, atom, integer} ->
            [#{
                type => 'remote_fun',
                data => {element(3, M), element(3, F), element(3, A)},
                range => anno_ex_to_range(Anno)
            }];
        _ ->
            []
    end,
    POI ++ lists:map(fun process_tree/1, [M, F, A]);
process_tree({'fun', Anno, {function, F, A}}) ->
    POI = #{
        type => 'fun',
        data => {F, A},
        range => anno_ex_to_range(Anno)
    },
    [POI] ++ lists:map(fun process_tree/1, [F, A]);
process_tree({record_index, Anno, RecName, Field}) ->
    % The grammar garuantees that Field is an atom node
    {atom, EndAnno, FieldName} = Field,
    #{
        type => record_index,
        data => {RecName, FieldName},
        range => annos_to_range(Anno, move_anno(EndAnno, 0, atom_len(FieldName)))
    };
process_tree({record_field, Anno, Var, RecName, Field}) ->
    % The grammar garuantees that Field is an atom node
    {atom, EndAnno, FieldName} = Field,
    POI = #{
        type => record_field,
        data => {RecName, FieldName},
        range => annos_to_range(Anno, move_anno(EndAnno, 0, atom_len(FieldName)))
    },
    [POI, process_tree(Var)];
process_tree({record, Anno, RecName, Fields}) ->
    Range = case lists:keyfind(record_close, 1, Fields) of
        {record_close, EndAnno} ->
            annos_to_range(Anno, EndAnno);
        false ->
            anno_to_range(Anno, 0, 1 + atom_len(RecName))
    end,
    POI = #{
        type => record_access,
        data => RecName,
        range => Range
    },
    [POI] ++ lists:map(fun process_tree/1, Fields);
process_tree({record, Anno, Var, RecName, Fields}) ->
    Range = case lists:keyfind(record_close, 1, Fields) of
        {record_close, EndAnno} ->
            annos_to_range(Anno, EndAnno);
        false ->
            anno_to_range(Anno, 0, 1 + atom_len(RecName))
    end,
    POI = #{
        type => record_access,
        data => RecName,
        range => Range
    },
    [POI, process_tree(Var)] ++ lists:map(fun process_tree/1, Fields);
%process_tree({var, Anno, Var}) ->
%    #{
%        type => var,
%        data => Var,
%        range => anno_to_range(Anno, 0, atom_len(Var))
%    };
process_tree({macro, Anno, Macro}) ->
    #{
        type => macro,
        data => Macro,
        range => anno_to_range(Anno, 0, atom_len(Macro))
    };
process_tree(Node) when is_tuple(Node), size(Node) > 2 ->
    [_NodeType, _Anno | Elems] = tuple_to_list(Node),
    lists:map(fun
        (Val) when is_list(Val) ->
            lists:map(fun process_tree/1, Val);
        (Val) ->
            process_tree(Val)
    end, Elems);
process_tree(_Else) ->
    [].

tokens_to_range(Tokens) ->
    Start = element(2, hd(Tokens)),
    End = case find_dot(Tokens) of
        {dot, Anno} ->
            % Include the `.` in highlights
            {ELine, ECol} = lc(Anno),
            {dot, [{line, ELine}, {column, ECol + 1}]};
        Else ->
            Else
    end,
    annos_to_range(Start, End).

annos_to_range(Start, End) ->
    {SLine, SCol} = lc(Start),
    {ELine, ECol} = lc(End),
    #{
        start => #{
            line => SLine - 1,
            character => SCol - 1
        },
        'end' => #{
            line => ELine - 1,
            character => ECol - 1
        }
    }.

anno_to_range(Anno, LineDiff, ColDiff) ->
    {Line, Col} = lc(Anno),
    #{
        start => #{
            line => Line - 1,
            character => Col - 1
        },
        'end' => #{
            line => Line - 1 + LineDiff,
            character => Col - 1 + ColDiff
        }
    }.

anno_ex_to_range(Anno) ->
    case lists:keyfind('end', 1, Anno) of
        {'end', Node} ->
            annos_to_range(Anno, element(2, Node));
        false ->
            annos_to_range(Anno, Anno)
    end.

find_dot([Last]) ->
    element(2, Last);
find_dot([{dot, Anno} | _]) ->
    Anno;
find_dot([_ | Rest]) ->
    find_dot(Rest).

atom_len(Atom) when is_atom(Atom) ->
    size(atom_to_binary(Atom, utf8)).

move_anno(Anno, LineDiff, ColDiff) ->
    {Line, Col} = lc(Anno),
    [{line, Line + LineDiff}, {column, Col + ColDiff}].

lc(Anno) ->
    {line, L} = lists:keyfind(line, 1, Anno),
    {column, C} = lists:keyfind(column, 1, Anno),
    {L, C}.
