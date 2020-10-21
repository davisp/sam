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

% Based on emilio_pp.erl
% https://github.com/cloudant-labs/emilio

-module(sam_pp).


-export([
    run/1
]).


-define(SCAN_OPTS, [text, return]).


run(Source) when is_binary(Source) ->
    run(binary_to_list(Source));

run(Source) when is_list(Source) ->
    case sam_erl_scan:string(Source, {1, 1}, ?SCAN_OPTS) of
        {ok, AllTokens, _} ->
            Reverted = revert_annos(AllTokens),
            MacroedTokens = macroize(Reverted),
            ReDefinedTokens = process_define_args(MacroedTokens),
            CodeTokens = split_code(ReDefinedTokens),
            {ok, parse_forms(CodeTokens, [])};
        {error, _, _} ->
            error
    end.


revert_annos([]) ->
    [];
revert_annos([Token | Rest]) ->
    Anno = element(2, Token),
    {value, {location, {Line, Col}}, RestAnno} =
            lists:keytake(location, 1, Anno),
    Ref = erlang:make_ref(),
    NewAnno = RestAnno ++ [{line, Line}, {column, Col}, {ref, Ref}],
    [setelement(2, Token, NewAnno)] ++ revert_annos(Rest).


macroize([]) ->
    [];
macroize([{'?', Anno} = MacroToken | Rest]) ->
    case extend_macro(Rest) of
        {MacroTokens, RestTokens} ->
            TextList = lists:foldl(fun(Token, Acc) ->
                case Token of
                    {'?', _} -> ["?" | Acc];
                    {atom, _, Name} -> [atom_to_list(Name) | Acc];
                    {var, _, Name} -> [atom_to_list(Name) | Acc]
                end
            end, ["?"], MacroTokens),
            Text = lists:flatten(lists:reverse(TextList)),
            NewToken = {macro, Anno, list_to_atom(Text)},
            RestMacroized = macroize(RestTokens),
            [NewToken] ++ replace_macro_args(RestMacroized);
        not_a_macro ->
            [MacroToken] ++ macroize(Rest)
    end;
macroize([Token | Rest]) ->
    [Token] ++ macroize(Rest).

extend_macro([{'?', _} = MacroToken | Rest]) ->
    case extend_macro(Rest) of
        {RestMacro, RestTokens} ->
            {[MacroToken | RestMacro], RestTokens};
        not_a_macro ->
            not_a_macro
    end;
extend_macro([{white_space, _, _} | Rest]) ->
    extend_macro(Rest);
extend_macro([{atom, _, _} = MacroToken | Rest]) ->
    {[MacroToken], Rest};
extend_macro([{var, _, _} = MacroToken | Rest]) ->
    {[MacroToken], Rest};
extend_macro(_) ->
    not_a_macro.

% The logic for replace_macro_args is based on skip_macro_args
% in epp_dodger.erl
%
% The logic here is that for every argument in a call
% to a macro we try to parse the expression. If it parses
% then we leave it alone. If it doesn't parse then we
% replace the argument with a stringified version.

replace_macro_args([{'(', _} = Token | Rest]) ->
    [Token] ++ replace_macro_args(Rest, [')'], []);
replace_macro_args([{white_space, _, _} = Token | Rest]) ->
    [Token] ++ replace_macro_args(Rest);
replace_macro_args(Tokens) ->
    Tokens.

replace_macro_args([{'(', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, [')' | CloseStack], [Token | Arg]);
replace_macro_args([{'{', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['}' | CloseStack], [Token | Arg]);
replace_macro_args([{'[', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, [']' | CloseStack], [Token | Arg]);
replace_macro_args([{'<<', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['>>' | CloseStack], [Token | Arg]);
replace_macro_args([{'begin', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['end' | CloseStack], [Token | Arg]);
replace_macro_args([{'if', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['end' | CloseStack], [Token | Arg]);
replace_macro_args([{'case', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['end' | CloseStack], [Token | Arg]);
replace_macro_args([{'receive', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['end' | CloseStack], [Token | Arg]);
replace_macro_args([{'try', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['end' | CloseStack], [Token | Arg]);
replace_macro_args([{'cond', _} = Token | Rest], CloseStack, Arg) ->
    replace_macro_args(Rest, ['end' | CloseStack], [Token | Arg]);
replace_macro_args([{',', Loc} = Token | Rest], [Close], Arg) ->
    % Note that the logic here is that we hit a comma
    % at the top level between '(' and ')' which indicates
    % that we've finished accumulating an argument.
    macro_argify(Arg, Loc) ++ [Token] ++ replace_macro_args(Rest, [Close], []);
replace_macro_args([{Close, Loc} = Token | Rest], [Close], Arg) ->
    % Need to check the last argument in case this was
    % a call with no arguments
    Replacement = case length(lists:filter(fun is_code/1, Arg)) of
        0 ->
            lists:reverse(Arg);
        _ ->
            macro_argify(Arg, Loc)
    end,
    Replacement ++ [Token] ++ Rest;
replace_macro_args([{Close, _} = Token | Rest], [Close | CloseStack], Arg) ->
    % Matched a closing element
    replace_macro_args(Rest, CloseStack, [Token | Arg]);
replace_macro_args([Token | Rest], CloseStack, Arg) ->
    % Anything else just goes into the current argument
    replace_macro_args(Rest, CloseStack, [Token | Arg]);
replace_macro_args([], _CloseStack, [{dot, _} = Dot | RestArg]) ->
    % We'll end up here if we had a macro definition that had
    % unlanced openings for complex expressions. If it looks
    % like we're in a define then we'll just go ahead and
    % stringify the arg after removing the trailing right
    % paren.
    {Arg, Close} = unwind_close_paren(RestArg),
    stringify_tokens(lists:reverse(Arg)) ++ Close ++ [Dot];
replace_macro_args([], _CloseStack, _Arg) ->
    erlang:error({error, macro_args}).

macro_argify(Arg, Loc) ->
    Code = lists:filter(fun is_code/1, Arg),
    Expr = lists:reverse(Code, [{dot, Loc}]),
    try
        {ok, _} = sam_erl_parse:parse_exprs(Expr),
        lists:reverse(Arg)
    catch _:_ ->
        stringify_tokens(lists:reverse(Arg))
    end.

process_define_args([]) ->
    [];
process_define_args([{'-', _} = Token | Rest]) ->
    [Token] ++ process_define_args(find_define(Rest));
process_define_args([Token | Rest]) ->
    [Token] ++ process_define_args(Rest).

find_define([]) ->
    [];
find_define([{atom, _, define} = Token | Rest]) ->
    {DefineTokens, Tail} = find_dot(Rest),
    [Token] ++ replace_macro_args(DefineTokens) ++ Tail;
find_define([{white_space, _, _} = Token | Rest]) ->
    [Token] ++ find_define(Rest);
find_define(Tokens) ->
    Tokens.

find_dot([]) ->
    erlang:error({error, unterminated_define});
find_dot([{dot, _} = Dot | Rest]) ->
    {[Dot], Rest};
find_dot([Token | Rest]) ->
    {Define, Tail} = find_dot(Rest),
    {[Token | Define], Tail}.

unwind_close_paren([{')', _} = Close | Rest]) ->
    {Rest, [Close]};
unwind_close_paren([{white_space, _, _} = WS | Rest]) ->
    {Tail, Close} = unwind_close_paren(Rest),
    {Tail, [WS | Close]};
unwind_close_paren(_) ->
    erlang:error({error, unterminated_define}).

split_code([]) ->
    [];
split_code([Token | Rest]) ->
    CodeTokens = split_code(Rest),
    case is_code(Token) of
        true -> [Token | CodeTokens];
        false -> CodeTokens
    end.

parse_forms([], Acc) ->
    lists:reverse(Acc);
parse_forms([{eof, _}], Acc) ->
    lists:reverse(Acc);
parse_forms(Tokens, Acc) ->
    case take_form(Tokens) of
        {no_form, _} ->
            lists:reverse(Acc);
        {FormTokens, RestTokens} ->
            case sam_erl_parse:parse_form(FormTokens) of
                {ok, AbstractForm} ->
                    parse_forms(RestTokens, [{AbstractForm, FormTokens} | Acc]);
                {error, _} ->
                    parse_forms(RestTokens, Acc)
            end
    end.

take_form(Tokens) ->
    IsNotDot = fun(Token) -> element(1, Token) /= dot end,
    case lists:splitwith(IsNotDot, Tokens) of
        {Form, [Dot | Rest]} ->
            {Form ++ [Dot], Rest};
        {_, []} ->
            Start = element(2, hd(Tokens)),
            End = element(2, lists:last(Tokens)),
            {no_form, {discard, Start, End}}
    end.

stringify_tokens([]) ->
    [];
stringify_tokens(Tokens) ->
    % Convert arg tokens to a string
    TextList = lists:foldl(fun
        ({N, _}, Acc) -> [atom_to_list(N) | Acc];
        ({_, _, V}, Acc) -> [io_lib:format("~p", [V]) | Acc]
    end, [], Tokens),
    Text = lists:flatten(lists:reverse(TextList)),
    [{string, element(2, hd(Tokens)), Text}].

is_code({white_space, _, _}) -> false;
is_code({comment, _, _}) -> false;
is_code(_) -> true.
