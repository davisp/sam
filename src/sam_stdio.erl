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

-module(sam_stdio).

-export([
    start_link/0
]).

-export([
    init/0,
    loop/2
]).


-define(CONTENT_LENGTH, <<"content-length">>).


start_link() ->
    proc_lib:start_link(?MODULE, init, []).

init() ->
    {ok, IoDevice} = application:get_env(sam, stdio),
    ok = io:setopts(IoDevice, [binary]),
    proc_lib:init_ack({ok, self()}),
    ?MODULE:loop(IoDevice, []).

loop(IoDevice, BinHeaders) ->
    case io:get_line(IoDevice, "") of
        <<"\n">> ->
            Headers = parse_headers(BinHeaders),
            Length = content_length(Headers),
            Body = read_body(IoDevice, Length),
            dispatch(Body),
            ?MODULE:loop(IoDevice, []);
        eof ->
            sam:exit(0);
        Line ->
            ?MODULE:loop(IoDevice, [Line | BinHeaders])
    end.

parse_headers(Lines) ->
    [parse_header(Line) || Line <- Lines].

parse_header(Line) ->
    [Name, Value] = binary:split(Line, <<":">>),
    {string:trim(string:lowercase(Name)), string:trim(Value)}.

content_length(Headers) ->
    {?CONTENT_LENGTH, Length} = lists:keyfind(?CONTENT_LENGTH, 1, Headers),
    binary_to_integer(Length).

read_body(IoDevice, Length) ->
    {ok, Body} = file:read(IoDevice, Length),
    jsx:decode(Body, [return_maps]).

dispatch(Body) ->
    %lager:debug("STDIN: ~p", [Body]),
    case sam_lsp_schema:message_type(Body) of
        notification -> sam_server:handle_notification(Body);
        request -> sam_server:handle_request(Body);
        response -> sam_client:handle_response(Body)
    end.

