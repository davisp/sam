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
                ?TDEF_FE(can_add_multiple_rows_progressively),
                ?TDEF_FE(can_add_multiple_rows_progressively_in_reverse),
                ?TDEF_FE(can_add_multiple_rows_randomly),
                ?TDEF_FE(can_remove_row),
                ?TDEF_FE(can_remove_all_rows),
                ?TDEF_FE(can_lookup_rows),
                ?TDEF_FE(cant_lookup_rows_in_empty_tree),
                ?TDEF_FE(start_keys_work)
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

can_add_multiple_rows_progressively_in_reverse({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    KVs = [{I, rand:uniform()} || I <- lists:seq(1, ?NUM_ROWS)],
    NewBt = lists:foldl(fun(KV, Acc) ->
        {ok, NewAcc} = sam_db_btree:update(Acc, [KV], []),
        NewAcc
    end, Bt, lists:reverse(KVs)),
    ?assertEqual(?NUM_ROWS, sam_db_btree:num_rows(NewBt)),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    Result = sam_db_btree:fold(NewBt, FoldFun, [], #{}),
    ?assertEqual(?NUM_ROWS, length(Result)),
    ?assert(sam_db_btree:size(NewBt) > 0),
    ?assertEqual(lists:sort(Result), lists:reverse(Result)).

can_add_multiple_rows_randomly({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    KVs = [{I, rand:uniform()} || I <- lists:seq(1, ?NUM_ROWS)],
    NewBt = lists:foldl(fun(KV, Acc) ->
        {ok, NewAcc} = sam_db_btree:update(Acc, [KV], []),
        NewAcc
    end, Bt, shuffle(KVs)),
    ?assertEqual(?NUM_ROWS, sam_db_btree:num_rows(NewBt)),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    Result = sam_db_btree:fold(NewBt, FoldFun, [], #{}),
    ?assertEqual(?NUM_ROWS, length(Result)),
    ?assert(sam_db_btree:size(NewBt) > 0),
    ?assertEqual(lists:sort(Result), lists:reverse(Result)).

can_remove_row({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,

    {ok, NewBt1} = sam_db_btree:update(Bt, [{a, b}], []),
    Result1 = sam_db_btree:fold(NewBt1, FoldFun, [], #{}),
    ?assertEqual([{a, b}], Result1),

    {ok, NewBt2} = sam_db_btree:update(Bt, [], [a]),
    Result2 = sam_db_btree:fold(NewBt2, FoldFun, [], #{}),
    ?assertEqual([], Result2).

can_remove_all_rows({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    KVs = [{I, rand:uniform()} || I <- lists:seq(1, ?NUM_ROWS)],

    {ok, NewBt1} = sam_db_btree:update(Bt, KVs, []),
    Result1 = sam_db_btree:fold(NewBt1, FoldFun, [], #{}),
    ?assertEqual(lists:sort(Result1), lists:reverse(Result1)),

    {ok, NewBt2} = sam_db_btree:update(Bt, [], element(1, lists:unzip(KVs))),
    Result2 = sam_db_btree:fold(NewBt2, FoldFun, [], #{}),
    ?assertEqual([], Result2).

can_lookup_rows({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    KVs = [{I, rand:uniform()} || I <- lists:seq(1, ?NUM_ROWS)],
    NewBt = lists:foldl(fun(KV, Acc) ->
        {ok, NewAcc} = sam_db_btree:update(Acc, [KV], []),
        NewAcc
    end, Bt, shuffle(KVs)),
    ?assertEqual(?NUM_ROWS, sam_db_btree:num_rows(NewBt)),

    lists:foreach(fun({K, V}) ->
        ?assertEqual([{K, V}], sam_db_btree:lookup(NewBt, [K]))
    end, shuffle(KVs)),

    {_, Chunks} = lists:foldl(fun(_, {From, To}) ->
        {Chunk, Rest} = lists:split(length(KVs) div 4, From),
        {Rest, [Chunk | To]}
    end, {shuffle(KVs), []}, lists:seq(1, 4)),

    lists:foreach(fun(Chunk) ->
        Keys = [K || {K, _} <- Chunk],
        Result = sam_db_btree:lookup(NewBt, Keys),
        ?assertEqual(lists:sort(Chunk), Result)
    end, Chunks).

cant_lookup_rows_in_empty_tree({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    lists:foreach(fun(K) ->
        ?assertEqual([{K, not_found}], sam_db_btree:lookup(Bt, [K]))
    end, lists:seq(1, ?NUM_ROWS)).

start_keys_work({Pid, _}) ->
    {ok, Bt} = sam_db_btree:open(Pid),
    FoldFun = fun(K, V, Acc) -> [{K, V} | Acc] end,
    KVs = [{I, rand:uniform()} || I <- lists:seq(1, ?NUM_ROWS)],
    NewBt = lists:foldl(fun(KV, Acc) ->
        {ok, NewAcc} = sam_db_btree:update(Acc, [KV], []),
        NewAcc
    end, Bt, shuffle(KVs)),
    ?assertEqual(?NUM_ROWS, sam_db_btree:num_rows(NewBt)),

    lists:foreach(fun({K, V}) ->
        Result = sam_db_btree:fold(NewBt, FoldFun, [], #{start_key => K}),
        Reversed = lists:reverse(Result),
        ?assertEqual(lists:sort(Result), Reversed),
        ?assertEqual({K, V}, hd(Reversed))
    end, shuffle(KVs)).

shuffle(Items) ->
    Tagged = [{rand:uniform(), I} || I <- Items],
    [I || {_, I} <- lists:sort(Tagged)].
