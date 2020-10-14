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
    start_link/0,
    send/1
]).

-export([
    init/0,
    loop/2
]).


-define(CONTENT_LENGTH, <<"content-length">>).


start_link() ->
    proc_lib:start_link(?MODULE, init, []).

send(#{type := _} = Msg) ->
    Body = sam_msg:to_json(Msg),
    CL = size(Body),
    send(io_lib:format("Content-Length: ~b\r\n\r\n~s", [CL, Body]));
send(Data) when is_binary(Data); is_list(Data) ->
    {ok, IoDevice} = application:get_env(sam, stdio),
    io:format(IoDevice, "~s", Data).

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
            sam_server:handle(Body),
            ?MODULE:loop(IoDevice, []);
        eof ->
            sam:exit();
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
