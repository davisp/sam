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

-module(sam_lsp_schema_test).

-include_lib("eunit/include/eunit.hrl").

cancel_notification_test() ->
    Data = #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"method">> => <<"$/cancelRequest">>,
        <<"params">> => #{
            <<"id">> => 1
        }
    },
    check(cancel_notification, Data).

selection_range_response_test() ->
    Data = #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"id">> => 1,
        <<"result">> => [
            #{
                <<"range">> => #{
                    <<"start">> => #{<<"line">> => 1, <<"character">> => 1},
                    <<"end">> => #{<<"line">> => 5, <<"character">> => 5}
                },
                <<"parent">> => #{
                    <<"range">> => #{
                        <<"start">> => #{<<"line">> => 2, <<"character">> => 2},
                        <<"end">> => #{<<"line">> => 4, <<"character">> => 4}
                    },
                    <<"parent">> => #{
                        <<"range">> => #{
                            <<"start">> => #{<<"line">> => 3, <<"character">> => 1},
                            <<"end">> => #{<<"line">> => 3, <<"character">> => 3}
                        }
                    }
                }
            }
        ]
    },
    check(selection_range_response, Data).

nested_error_test() ->
    Data = #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"method">> => <<"$/cancelRequest">>,
        <<"params">> => #{
            <<"id">> => foo
        }
    },
    ?assertError(
        {match_failed, [params, id], {type_mismatch, [number, string], foo}},
        check(cancel_notification, Data)
    ).

document_uri_error_test() ->
    Data = <<"foo\\bar">>,
    ?assertError(
        {type_mismatch, document_uri, Data},
        sam_lsp_validator:validate(document_uri, Data)
    ).

generator_test_() ->
    Exports = sam_lsp_schema:module_info(exports),
    lists:flatmap(
        fun
            ({module_info, _Arity}) ->
                [];
            ({client_initiated, _Arity}) ->
                [];
            ({server_initiated, _Arity}) ->
                [];
            ({message_type, _Arity}) ->
                [];
            ({response_type, _Arity}) ->
                [];
            ({Fun, 0}) ->
                Test = fun() ->
                    Type = sam_lsp_schema:Fun(),
                    lists:foreach(
                        fun(_) ->
                            Value = sam_lsp_generator:generate(Type),
                            try
                                sam_lsp_validator:validate(Type, Value),
                                MessageType = sam_lsp_schema:message_type(Value),
                                ?assert(is_atom(MessageType))
                            catch
                                T:R:S ->
                                    ?debugFmt("ERROR: ~p~n", [Value]),
                                    erlang:raise(T, R, S)
                            end
                        end,
                        lists:seq(1, 10)
                    )
                end,
                [{atom_to_list(Fun), Test}]
        end,
        lists:sort(Exports)
    ).

check_request_response_types_test() ->
    ClientInitiated = sam_lsp_schema:client_initiated(),
    ServerInitiated = sam_lsp_schema:server_initiated(),
    lists:foreach(fun(Type) ->
        TypeString = atom_to_list(Type),
        ReqResp = case lists:suffix("_request", TypeString) of
            true ->
                ReqBase = lists:sublist(TypeString, length(TypeString) - 8),
                Response = list_to_atom(ReqBase ++ "_response"),
                [{Type, Response}];
            false ->
                []
        end,
        RespReq = case lists:suffix("_response", TypeString) of
            true ->
                RespBase = lists:sublist(TypeString, length(TypeString) - 9),
                Request = list_to_atom(RespBase ++ "_request"),
                [{Request, Type}];
            false ->
                []
        end,
        Notification = case lists:suffix("_notification", TypeString) of
            true ->
                [{Type, undefined}];
            false ->
                []
        end,
        [{Req, Resp}] = ReqResp ++ RespReq ++ Notification,
        ?assertEqual(Resp, sam_lsp_schema:response_type(Req))
    end, ClientInitiated ++ ServerInitiated).

check(TypeName, Data) ->
    Type = sam_lsp_schema:TypeName(),
    sam_lsp_validator:validate(Type, Data).
