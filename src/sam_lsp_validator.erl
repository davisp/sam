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

-module(sam_lsp_validator).


-export([
    validate/2
]).

validate(Type, Data) when is_map(Type), is_map(Data) ->
    lists:foreach(fun(Key) ->
        SubType = maps:get(Key, Type),
        Value = case maps:is_key(Key, Data) of
            true ->
                maps:get(Key, Data);
            false ->
                BinKey = atom_to_binary(Key, utf8),
                maps:get(BinKey, Data, '$missing$')
        end,
        try
            validate(SubType, Value)
        catch
            error:{type_mismatch, _, _} = Reason->
                erlang:error({match_failed, [Key], Reason});
            error:{match_failed, Path, Reason} ->
                erlang:error({match_failed, [Key | Path], Reason})
        end
    end, maps:keys(Type));

validate(Type, Data) when is_list(Type) ->
    try
        lists:foreach(fun(SubType) ->
            try
                validate(SubType, Data),
                throw(matched)
            catch
                error:{type_mismatch, _, _} ->
                    ok;
                error:{match_failed, _, _} ->
                    ok
            end
        end, Type),
        % None of the possible types matched
        erlang:error({type_mismatch, Type, Data})
    catch throw:matched ->
        ok
    end;

validate({recursive, Type}, Data) ->
    try
        put('$sam_lsp_type$', Type),
        validate(Type, Data)
    after
        erase('$sam_lsp_type$')
    end;

validate(recurse, Data) ->
    Type = get('$sam_lsp_type$'),
    validate(Type, Data);

validate({optional, _Type}, '$missing$') ->
    ok;

validate({optional, Type}, Data) ->
    validate(Type, Data);

validate({array, Type}, Data) when is_list(Data) ->
    lists:foreach(fun(Item) ->
        validate(Type, Item)
    end, Data);

validate({array, Size, Type}, Data) when is_list(Data), length(Data) == Size ->
    validate({array, Type}, Data);

validate({float_range, Low, High}, Data) when is_number(Data), Data >= Low, Data =< High ->
    ok;

validate(document_uri, Data) when is_binary(Data) ->
    case uri_string:normalize(Data, [return_map]) of
        #{} ->
            ok;
        {error, _, _} ->
            erlang:error({type_mismatch, document_uri, Data})
    end;

validate(string, Data) when is_binary(Data) ->
    ok;

validate(number, Data) when is_number(Data) ->
    ok;

validate(boolean, Data) when is_boolean(Data) ->
    ok;

validate(array, Data) when is_list(Data) ->
    ok;

validate(object, Data) when is_map(Data) ->
    ok;

validate(null, null) ->
    ok;

validate(any, _Data) ->
    ok;

validate(Type, Data) when is_binary(Type), Data == Type ->
    ok;

validate(Type, Data) when is_number(Type), Data == Type ->
    ok;

validate(Type, Data) ->
    erlang:error({type_mismatch, Type, Data}).
