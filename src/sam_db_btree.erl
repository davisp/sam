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

% Based on a reduced version of couch_btree from Apache CouchDB

-module(sam_db_btree).


-export([
    open/1,
    open/2,
    get_state/1,

    num_rows/1,
    size/1,

    lookup/2,
    fold/4,
    update/3
]).

-record(btree, {
    fd,
    root
}).

-define(CHUNK_SIZE, 16#2000). % 8KiB
-define(FILL_RATIO, 0.5).

open(Fd) ->
    {ok, #btree{fd = Fd}}.

open(Fd, Root) ->
    {ok, #btree{fd = Fd, root = Root}}.

get_state(#btree{} = Bt) ->
    Bt#btree.root.

num_rows(#btree{root = undefined}) ->
    0;
num_rows(#btree{root = {_Loc, Count, _Size}}) ->
    Count.

size(#btree{root = undefined}) ->
    0;
size(#btree{root = {_Loc, _Count, Size}}) ->
    Size.

lookup(#btree{root = Root} = Bt, Keys) ->
    Sorted = lists:usort(Keys),
    lookup(Bt, Root, Sorted).

fold(#btree{root = undefined}, _Fun, Acc, _Options) ->
    Acc;
fold(#btree{} = Bt, Fun, Acc, Options) ->
    case Options of
        #{start_key := StartKey} ->
            seek(Bt, Bt#btree.root, StartKey, Fun, Acc);
        _ ->
            stream(Bt, Bt#btree.root, Fun, Acc)
    end.

update(#btree{root = Root} = Bt, ToAddKVs, ToRemKeys) ->
    Insert = [{insert, Key, Val} || {Key, Val} <- ToAddKVs],
    Remove = [{remove, Key, undefined} || Key <- ToRemKeys],
    Sorted = lists:sort(fun cmp_actions/2, Insert ++ Remove),

    {ok, KPs} = update_node(Bt, Root, Sorted),
    {ok, NewRoot} = complete_root(Bt, KPs),
    {ok, Bt#btree{root = NewRoot}}.

lookup(_Bt, undefined, Keys) ->
    [{Key, not_found} || Key <- Keys];
lookup(Bt, {Loc, _Count, _Size}, Keys) ->
    {NodeType, Children} = get_node(Bt, Loc),
    case NodeType of
        kp_node -> lookup_kp(Bt, Children, Keys);
        kv_node -> lookup_kv(Bt, Children, Keys)
    end.

lookup_kp(_Bt, [], Keys) ->
    [{Key, not_found} || Key <- Keys];
lookup_kp(Bt, [{Key, Node} | Rest], Keys) ->
    {KeysInNode, RestKeys} = lists:splitwith(fun(K) -> K =< Key end, Keys),
    case KeysInNode of
        [] ->
            lookup_kp(Bt, Rest, RestKeys);
        _ ->
            NodeResults = lookup(Bt, Node, KeysInNode),
            NodeResults ++ lookup_kp(Bt, Rest, RestKeys)
    end.

lookup_kv(_Bt, [], Keys) ->
    [{Key, not_found} || Key <- Keys];
lookup_kv(_Bt, _RestKVs, []) ->
    % Done looking for keys in this node
    [];
lookup_kv(Bt, [{Key, Val} | RestKVs], [Key | RestKeys]) ->
    % Found key
    [{Key, Val} | lookup_kv(Bt, RestKVs, RestKeys)];
lookup_kv(Bt, [{BtKey, _Val} | RestKVs], [UserKey | _] = Keys) when BtKey < UserKey ->
    % Not a key we're looking for
    lookup_kv(Bt, RestKVs, Keys);
lookup_kv(Bt, [{BtKey, _Val} | _] = KVs, [UserKey | RestKeys]) when BtKey > UserKey ->
    % UserKey not found
    [{UserKey, not_found} | lookup_kv(Bt, KVs, RestKeys)].

seek(Bt, {Loc, _Count, _Size}, StartKey, Fun, Acc) ->
    {Type, Children} = get_node(Bt, Loc),
    case Type of
        kp_node -> seek_kp(Bt, Children, StartKey, Fun, Acc);
        kv_node -> seek_kv(Bt, Children, StartKey, Fun, Acc)
    end.

seek_kp(Bt, Children, StartKey, Fun, Acc) ->
    ToScan = lists:dropwhile(fun({K, _V}) -> K < StartKey end, Children),
    case ToScan of
        [] ->
            Acc;
        [{_Key, Node} | Rest] ->
            NewAcc = seek(Bt, Node, StartKey, Fun, Acc),
            stream_kp(Bt, Rest, Fun, NewAcc)
    end.

seek_kv(_Bt, KVs, StartKey, Fun, Acc0) ->
    ToScan = lists:dropwhile(fun({K, _V}) -> K < StartKey end, KVs),
    lists:foldl(fun({K, V}, Acc1) ->
        Fun(K, V, Acc1)
    end, Acc0, ToScan).

stream(Bt, {Loc, _Count, _Size}, Fun, Acc) ->
    {Type, Children} = get_node(Bt, Loc),
    case Type of
        kp_node -> stream_kp(Bt, Children, Fun, Acc);
        kv_node -> stream_kv(Bt, Children, Fun, Acc)
    end.

stream_kp(Bt, Children, Fun, Acc0) ->
    lists:foldl(fun({_Key, Ptr}, Acc1) ->
        stream(Bt, Ptr, Fun, Acc1)
    end, Acc0, Children).

stream_kv(_Bt, KVs, Fun, Acc0) ->
    lists:foldl(fun({K, V}, Acc1) ->
        Fun(K, V, Acc1)
    end, Acc0, KVs).

update_node(Bt, Node, Actions) ->
    {NodeType, Children} = case Node of
        {Loc, _Count, _Size} -> get_node(Bt, Loc);
        undefined -> {kv_node, []}
    end,

    {ok, NewChildren} = case NodeType of
        kp_node -> update_kp(Bt, Children, Actions, []);
        kv_node -> update_kv(Bt, Children, Actions, [])
    end,

    case NewChildren of
        [] ->
            {ok, []};
        Children ->
            % No changes to this node
            {LastKey, _} = lists:last(Children),
            {ok, [{LastKey, Node}]};
        _ when Node == undefined ->
            write_node(Bt, kv_node, NewChildren);
        _ ->
            {LastKey, _} = lists:last(Children),
            write_node(Bt, NodeType, NewChildren, {LastKey, Node}, Children)
    end.

update_kp(Bt, [], Actions, []) ->
    update_node(Bt, undefined, Actions);
update_kp(_Bt, Children, [], Result) ->
    {ok, lists:reverse(Result, Children)};
update_kp(Bt, [{_Key, Node}], Actions, Result) ->
    {ok, NewKPs} = update_node(Bt, Node, Actions),
    {ok, lists:reverse(Result, NewKPs)};
update_kp(Bt, [{Key, Node} | RestChildren], Actions, Result) ->
    {ActionsInNode, RestActions} = lists:splitwith(fun({_, K, _}) -> K =< Key end, Actions),
    NewResult = case ActionsInNode of
        [] ->
            [{Key, Node} | Result];
        _ ->
            {ok, NewKPs} = update_node(Bt, Node, ActionsInNode),
            lists:reverse(NewKPs, Result)
    end,
    update_kp(Bt, RestChildren, RestActions, NewResult).

update_kv(_Bt, [], Actions, Result) ->
    % Process the rest of the actions which means
    % adding any insertions and ignoring deletions
    NewKVs = [{K, V} || {insert, K, V} <- Actions],
    {ok, lists:reverse(Result, NewKVs)};
update_kv(_Bt, Rest, [], Result) ->
    % No more actions to process
    {ok, lists:reverse(Result, Rest)};
update_kv(Bt, [{Key1, _} = KV | RestKVs], [{AType, Key2, Val} = Action | RestActions], Result) ->
    if
        Key1 < Key2 ->
            % Next action is after this key
            update_kv(Bt, RestKVs, [Action | RestActions], [KV | Result]);
        Key1 == Key2 andalso AType == remove ->
            % Found a key to delete
            update_kv(Bt, RestKVs, RestActions, Result);
        Key1 == Key2 andalso AType == insert ->
            % Found a key to overwrite
            update_kv(Bt, RestKVs, RestActions, [{Key2, Val} | Result]);
        Key1 > Key2 andalso AType == remove ->
            % User request deletion of an unknown key
            update_kv(Bt, [KV | RestKVs], RestActions, Result);
        Key1 > Key2 andalso AType == insert ->
            % Inserting a new key
            update_kv(Bt, [KV | RestKVs], RestActions, [{Key2, Val} | Result])
    end.

cmp_actions({OpA, KeyA, _}, {OpB, KeyB, _}) ->
    case KeyA < KeyB of
        true ->
            true;
        false ->
            case KeyA > KeyB of
                true ->
                    false;
                false ->
                    op_order(OpA) =< op_order(OpB)
            end
    end.

op_order(remove) -> 1;
op_order(insert) -> 2.

complete_root(_Bt, []) ->
    {ok, undefined};
complete_root(_Bt, [{_Key, Node}])->
    {ok, Node};
complete_root(Bt, KPs) ->
    {ok, NewKPs} = write_node(Bt, kp_node, KPs),
    complete_root(Bt, NewKPs).

get_node(#btree{fd = Fd}, Loc) ->
    {ok, {NodeType, NodeList}} = sam_db_file:pread_term(Fd, Loc),
    {NodeType, NodeList}.

write_node(#btree{fd = Fd}, NodeType, NodeList) ->
    {ok, lists:map(fun(Children) ->
        {LastKey, _} = lists:last(Children),
        {ok, Loc} = sam_db_file:append_term(Fd, {NodeType, Children}),
        {Count, Size} = reduce_children(NodeType, Children),
        {LastKey, {Loc, Count, Size}}
    end, chunkify(NodeList))}.

write_node(Bt, NodeType, Children, OldNode, OldChildren) ->
    % If OldChildren exists somewhere within Children we
    % can re-use the old node if it contains more than ?FILL_RATIO
    % of ?CHUNK_SIZE.
    case erlang:external_size(OldChildren) > ?FILL_RATIO * ?CHUNK_SIZE of
        true ->
            case find_old_children(Children, OldChildren) of
                {Prefix, Suffix} ->
                    {ok, PrefixKPs} = if Prefix == [] -> {ok, []}; true ->
                        write_node(Bt, NodeType, Prefix)
                    end,
                    {ok, SuffixKPs} = if Suffix == [] -> {ok, []}; true ->
                        write_node(Bt, NodeType, Suffix)
                    end,
                    {ok, PrefixKPs ++ [OldNode] ++ SuffixKPs};
                not_found ->
                    write_node(Bt, NodeType, Children)
            end;
        false ->
            write_node(Bt, NodeType, Children)
    end.

find_old_children(NewChildren, OldChildren) ->
    {Prefix, RestNew} = remove_child_prefix(NewChildren, hd(OldChildren)),
    case remove_old_children(RestNew, OldChildren) of
        {ok, Suffix} ->
            {Prefix, Suffix};
        not_found ->
            not_found
    end.

remove_child_prefix([Child | Rest], Old) when Child < Old ->
    {Prefix, Tail} = remove_child_prefix(Rest, Old),
    {[Child | Prefix], Tail};
remove_child_prefix(Tail, _) ->
    {[], Tail}.

remove_old_children([], []) ->
    {ok, []};
remove_old_children(New, []) ->
    {ok, New};
remove_old_children([], _Old) ->
    not_found;
remove_old_children([KP | RestNew], [KP | RestOld]) ->
    remove_old_children(RestNew, RestOld);
remove_old_children(_, _) ->
    not_found.

%%%%%%%%%%%%% The chunkify function *still* sucks! %%%%%%%%%%%%%
% It is inaccurate as it does not account for compression when blocks are
% written.

chunkify(InList) ->
    case erlang:external_size(InList) of
        Size when Size > ?CHUNK_SIZE ->
            NumChunks = (Size div ?CHUNK_SIZE) + 1,
            ChunkSize = Size div NumChunks,
            chunkify(InList, ChunkSize, 0, [], []);
        _ ->
            [InList]
    end.

chunkify([], _ChunkSize, 0, [], AllChunks) ->
    lists:reverse(AllChunks);
chunkify([], _ChunkSize, _CurrSize, [Item], [PrevChunk | RestChunks]) ->
    % Avoid single child nodes
    lists:reverse(RestChunks, [PrevChunk ++ [Item]]);
chunkify([], _ChunkSize, _CurrSize, CurrChunk, AllChunks) ->
    NewChunk = lists:reverse(CurrChunk),
    lists:reverse(AllChunks, [NewChunk]);
chunkify([Item | RestItems], ChunkSize, CurrSize, CurrChunk, AllChunks) ->
    case erlang:external_size(Item) of
        Size when (Size + CurrSize) > ChunkSize andalso CurrChunk /= [] ->
            NewChunk = lists:reverse(CurrChunk, [Item]),
            chunkify(RestItems, ChunkSize, 0, [], [NewChunk | AllChunks]);
        Size ->
            chunkify(RestItems, ChunkSize, CurrSize + Size, [Item | CurrChunk], AllChunks)
    end.

reduce_children(kv_node, KVs) ->
    Count = length(KVs),
    Size = lists:foldl(fun(KV, Acc) ->
        Acc + erlang:external_size(KV)
    end, 0, KVs),
    {Count, Size};

reduce_children(kp_node, KPs) ->
    lists:foldl(fun({_K, {_L, C, S}}, {CAcc, SAcc}) ->
        {CAcc + C, SAcc + S}
    end, {0, 0}, KPs).
