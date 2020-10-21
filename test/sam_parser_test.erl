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

-module(sam_parser_test).


-include_lib("eunit/include/eunit.hrl").
-include("sam_test.hrl").

sam_parser_test_() ->
    {
        setup,
        fun setup_all/0,
        fun teardown_all/1,
        {
            foreach,
            fun setup/0,
            fun teardown/1,
            [
                ?TDEF_FE(can_parse)
            ]
        }
    }.

setup_all() ->
    ok.

teardown_all(_) ->
    ok.

setup() ->
    ok.

teardown(_) ->
    ok.

can_parse(_) ->
    {ok, Data} = file:read_file("src/sam_parser.erl"),
    Result = sam_parser:parse(Data),
    io:format(standard_error, "RESULT: ~p~n", [Result]),
    ok.