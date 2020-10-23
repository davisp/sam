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

-module(sam_provider).

-export([
    notify/2,
    request/3,

    response/2
]).

-export([
    do_notify/2,
    do_request/3
]).

-include("sam.hrl").

-callback run(any()) -> any().

notify(NotifyType, Msg) ->
    {ok, proc_lib:spawn(?MODULE, do_notify, [NotifyType, Msg])}.

request(ReqType, RespTypeName, Msg) ->
    {ok, proc_lib:spawn(?MODULE, do_request, [ReqType, RespTypeName, Msg])}.

response(Msg, Result) ->
    #{
        <<"jsonrpc">> => <<"2.0">>,
        <<"id">> => maps:get(<<"id">>, Msg),
        <<"result">> => Result
    }.

do_notify(TypeName, Msg) ->
    try
        sam_lsp_validator:validate(sam_lsp_schema:TypeName(), Msg)
    catch T1:R1 ->
        lager:error("Invalid notification: ~p ~p", [{T1, R1}, Msg]),
        exit(normal)
    end,
    try
        Provider = notification_provider(maps:get(<<"method">>, Msg)),
        Provider:handle(Msg)
    catch T2:R2:S2 ->
        lager:error("Error handling notification: ~p ~p", [{T2, R2}, S2])
    end.
    

do_request(ReqTypeName, RespTypeName, Msg) ->
    try
        sam_lsp_validator:validate(sam_lsp_schema:ReqTypeName(), Msg)
    catch T1:R1 ->
        lager:error("Invalid request: ~p - ~p", [{T1, R1}, Msg]),
        sam_client:error(Msg, ?JSONRPC_INVALID_REQUEST, schema_validation_failed),
        exit(normal)
    end,
    Resp = try
        Provider = request_provider(maps:get(<<"method">>, Msg)),
        Provider:handle(Msg)
    catch T2:R2:S2 ->
        lager:error("Error handling message: ~p ~p", [{T2, R2}, S2]),
        sam_client:error(Msg, ?JSONRPC_INTERNAL_ERROR, unknown_error),
        exit(normal)
    end,
    try
        sam_client:reply(RespTypeName, Resp)
    catch error:{match_failed, _, _}=R3:S3 ->
        lager:error("Invalid response: ~p :: ~p ~p", [Resp, R3, S3]),
        sam_client:error(Msg, ?JSONRPC_INTERNAL_ERROR, invalid_response)
    end.

notification_provider(<<"exit">>) ->
    sam_provider_notify_exit;
notification_provider(<<"initialized">>) ->
    sam_provider_notify_initialized;
notification_provider(<<"textDocument/didChange">>) ->
    sam_provider_notify_did_change;
notification_provider(<<"textDocument/didClose">>) ->
    sam_provider_notify_did_close;
notification_provider(<<"textDocument/didOpen">>) ->
    sam_provider_notify_did_open;
notification_provider(<<"textDocument/didSave">>) ->
    sam_provider_notify_did_save;
notification_provider(_) ->
    sam_provider_notify_unknown.

request_provider(<<"initialize">>) ->
    sam_provider_request_initialize;
request_provider(<<"shutdown">>) ->
    sam_provider_request_shutdown;
request_provider(<<"textDocument/definition">>) ->
    sam_provider_request_definition;
request_provider(<<"textDocument/hover">>) ->
    sam_provider_request_hover;
request_provider(<<"textDocument/references">>) ->
    sam_provider_request_references;
request_provider(<<"textDocument/signatureHelp">>) ->
    sam_provider_request_signature;
request_provider(<<"textDocument/documentSymbols">>) ->
    sam_provider_request_symbols;
request_provider(_) ->
    sam_provider_request_unknown.
