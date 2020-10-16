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

-module(sam_db_btree_test).

-include_lib("eunit/include/eunit.hrl").
-include("sam_test.hrl").

-define(NUM_ROWS, 1000).
-define(TIMEOUT, 60). % seconds


sam_db_btree_test_() ->
    {
        setup,
        fun setup_all/0,
        fun teardown_all/1,
        {
            foreach,
            fun setup/0,
            fun teardown/1,
            [
                ?TDEF_FE(empty_btree_is_empty),
                ?TDEF_FE(no_rows_in_empty_btree),
                ?TDEF_FE(can_add_row_to_btree),
                ?TDEF_FE(can_lookup_row_in_btree),
                ?TDEF_FE(can_add_multiple_rows),
                ?TDEF_FE(can_add_multiple_rows_progressively)
            ]
        }
    }.


setup_all() ->
    ok.

teardown_all(_) ->
    ok.

setup() ->
    FileNameStr = io_lib:format("test_btree.~b", [rand:uniform(16#10000000)]),
    FileNameBin = iolist_to_binary(FileNameStr),
    {ok, Pid} = sam_db_file:open(FileNameBin),
    {Pid, FileNameBin}.

teardown({Pid, FileName}) ->
    sam_db_file:close(Pid),
    file:delete(FileName).

empty_btree_is_empty({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    ?assertEqual(0, sam_db_btree:num_rows(Bt)),
    ?assertEqual(0, sam_db_btree:size(Bt)).

no_rows_in_empty_btree({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    Result = sam_db_btree:fold(Bt, FoldFun, [], #{}),
    ?assertEqual([], Result).

can_add_row_to_btree({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    {ok, NewBt} = sam_db_btree:update(Bt, [{a, b}], []),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    Result = sam_db_btree:fold(NewBt, FoldFun, [], #{}),
    ?assertEqual([{a, b}], Result).

can_lookup_row_in_btree({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    {ok, NewBt} = sam_db_btree:update(Bt, [{a, b}], []),
    Result = sam_db_btree:lookup(NewBt, [a]),
    ?assertEqual([{a, b}], Result).

can_add_multiple_rows({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    KVs = [{I, rand:uniform()} || I <- lists:seq(1, ?NUM_ROWS)],
    {ok, NewBt} = sam_db_btree:update(Bt, KVs, []),
    ?assertEqual(?NUM_ROWS, sam_db_btree:num_rows(NewBt)),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    Result = sam_db_btree:fold(NewBt, FoldFun, [], #{}),
    ?assertEqual(?NUM_ROWS, length(Result)),
    ?assert(sam_db_btree:size(NewBt) > 0),
    ?assertEqual(lists:sort(Result), lists:reverse(Result)).

can_add_multiple_rows_progressively({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    KVs = [{I, rand:uniform()} || I <- lists:seq(1, ?NUM_ROWS)],
    NewBt = lists:foldl(fun(KV, Acc) ->
        {ok, NewAcc} = sam_db_btree:update(Acc, [KV], []),
        NewAcc
    end, Bt, KVs),
    ?assertEqual(?NUM_ROWS, sam_db_btree:num_rows(NewBt)),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    Result = sam_db_btree:fold(NewBt, FoldFun, [], #{}),
    ?assertEqual(?NUM_ROWS, length(Result)),
    ?assert(sam_db_btree:size(NewBt) > 0),
    ?assertEqual(lists:sort(Result), lists:reverse(Result)).
