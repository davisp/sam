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

-module(sam_db).
-behaviour(gen_server).

-export([
    start_link/0,

    set_uri/1,

    get_db/0,
    get_doc/1,
    get_doc/2,
    get_doc_for_mod/1,
    get_md5/1,
    get_refs/1,
    get_uris_from_tail/1,

    add_doc/1,
    rem_doc/1
]).

-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).

-record(db, {
    fd,
    docs,
    uris,
    mods,
    refs,
    sigs,
    timer_ref
}).

-define(DB_VERSION, 4).
-define(COMMIT_INTERVAL, 5000).

start_link() ->
    proc_lib:start_link(?MODULE, init, [nil]).

set_uri(Uri) ->
    whereis(?MODULE) ! {set_uri, Uri}.

get_db() ->
    gen_server:call(?MODULE, get_db, infinity).

get_doc(Uri) ->
    {ok, Db} = get_db(),
    get_doc(Db, Uri).

get_doc(Db, Uri) ->
    case sam_db_btree:lookup(Db#db.docs, [Uri]) of
        [{Uri, not_found}] -> not_found;
        [{Uri, #{} = Doc}] -> Doc
    end.

get_doc_for_mod(Mod) ->
    {ok, Db} = get_db(),
    case get_first(Db#db.mods, Mod) of
        {{Mod, Uri}, _} ->
            get_doc(Db, Uri);
        not_found ->
            not_found
    end.

get_md5(Uri) ->
    case get_doc(Uri) of
        #{md5 := Md5} -> Md5;
        not_found -> not_found
    end.

get_refs(MFA) ->
    {ok, Db} = get_db(),
    case get_all(Db#db.refs, MFA) of
        AllRefs when is_list(AllRefs) ->
            [{Uri, Refs} || {{_, Uri}, Refs} <- AllRefs];
        not_found ->
            not_found
    end.

get_uris_from_tail(Path) ->
    Prefix = rev_path(iolist_to_binary(Path)),
    {ok, Db} = get_db(),
    case get_all_startswith(Db#db.uris, Prefix) of
        KVs when is_list(KVs) ->
            [Uri || {_, Uri} <- KVs];
        not_found ->
            not_found
    end.

add_doc(NewDoc) ->
    #{
        uri := Uri
    } = NewDoc,

    {ok, Db} = get_db(),
    OldDoc = case get_doc(Db, Uri) of
        #{} = Doc -> Doc;
        not_found -> #{uri => Uri, pois => []}
    end,
    IdxUpdates = prepare_updates(Db, OldDoc, NewDoc),
    Updates = IdxUpdates#{
        docs_to_add => [{Uri, NewDoc}],
        docs_to_rem => [],
        uris_to_add => [{rev_uri(Uri), Uri}],
        uris_to_rem => []
    },
    gen_server:call(?MODULE, {update, Updates}, infinity).

rem_doc(Uri) ->
    {ok, Db} = get_db(),
    case get_doc(Db, Uri) of
        #{} = OldDoc ->
            NewDoc = #{uri => Uri, pois => []},
            IdxUpdates = prepare_updates(Db, OldDoc, NewDoc),
            Updates = IdxUpdates#{
                docs_to_add => [],
                docs_to_rem => [Uri],
                uris_to_add => [],
                uris_to_rem => [rev_uri(Uri)]
            },
            gen_server:call(?MODULE, {update, Updates}, infinity);
        not_found ->
            % Nothing to delete
            ok
    end.

init(_) ->
    % Let sam_sup continue on its merry way
    register(?MODULE, self()),
    proc_lib:init_ack({ok, self()}),

    % Wait for the LSP initialized message
    RootUri = receive
        {set_uri, RawUri} ->
            sam_uri:normalize(RawUri);
        Else ->
            erlang:error({sam_db_uninitialized, Else})
    end,

    {ok, Fd} = sam_db_file:open(db_file(RootUri)),
    try
        Db = case sam_db_file:read_header(Fd) of
            {ok, {sam_header, ?DB_VERSION, DocsSt, UrisSt, ModsSt, RefsSt, SigsSt}} ->
                lager:debug("Reopened database.", []),
                {ok, DocsBt} = sam_db_btree:open(Fd, DocsSt),
                {ok, UrisBt} = sam_db_btree:open(Fd, UrisSt),
                {ok, ModsBt} = sam_db_btree:open(Fd, ModsSt),
                {ok, RefsBt} = sam_db_btree:open(Fd, RefsSt),
                {ok, SigsBt} = sam_db_btree:open(Fd, SigsSt),
                #db{
                    fd = Fd,
                    docs = DocsBt,
                    uris = UrisBt,
                    mods = ModsBt,
                    refs = RefsBt,
                    sigs = SigsBt
                };
            BadHeader ->
                {ok, Size} = sam_db_file:fsize(Fd),
                if Size =< 16 -> ok; true ->
                    % Only log an error if we have a bad database
                    lager:warning("Failed to open database: ~p", [BadHeader])
                end,
                reset_db(#db{
                    fd = Fd
                })
        end,
        sam_db_scanner:scan(RootUri),
        sam_db_scanner:scan(sam_uri:from_path(code:root_dir())),
        gen_server:enter_loop(?MODULE, [], Db)
    catch T:R:S ->
        lager:error("Failed to initialize database: ~s :: ~p~n~p", [RootUri, {T, R}, S]),
        erlang:raise(T, R, S)
    end.

terminate(_Reason, _Db) ->
    ok.

handle_call(get_db, _From, Db) ->
    {reply, {ok, Db}, Db};
handle_call({update, Updates}, From, Db) ->
    {Clients, #{
        docs_to_add := DocsToAdd,
        docs_to_rem := DocsToRem,
        uris_to_add := UrisToAdd,
        uris_to_rem := UrisToRem,
        mods_to_add := ModsToAdd,
        mods_to_rem := ModsToRem,
        refs_to_add := RefsToAdd,
        refs_to_rem := RefsToRem,
        sigs_to_add := SigsToAdd,
        sigs_to_rem := SigsToRem
    }} = collect_updates([From], Updates),

    #db{
        docs = DocsBt,
        uris = UrisBt,
        mods = ModsBt,
        refs = RefsBt,
        sigs = SigsBt
    } = Db,

    {ok, NewDocsBt} = sam_db_btree:update(DocsBt, DocsToAdd, DocsToRem),
    {ok, NewUrisBt} = sam_db_btree:update(UrisBt, UrisToAdd, UrisToRem),
    {ok, NewModsBt} = sam_db_btree:update(ModsBt, ModsToAdd, ModsToRem),
    {ok, NewRefsBt} = sam_db_btree:update(RefsBt, RefsToAdd, RefsToRem),
    {ok, NewSigsBt} = sam_db_btree:update(SigsBt, SigsToAdd, SigsToRem),

    NewDb = Db#db{
        docs = NewDocsBt,
        uris = NewUrisBt,
        mods = NewModsBt,
        refs = NewRefsBt,
        sigs = NewSigsBt
    },

    lists:foreach(fun(Client) ->
        gen:reply(Client, ok)
    end, Clients),
    {noreply, reset_timer(NewDb)};
handle_call(Msg, _From, Db) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, Db}.

handle_cast(Msg, Db) ->
    {stop, {bad_cast, Msg}, Db}.

handle_info(commit, Db) ->
    #db{
        fd = Fd,
        docs = DocsBt,
        uris = UrisBt,
        mods = ModsBt,
        refs = RefsBt,
        sigs = SigsBt
    } = Db,

    DocsSt = sam_db_btree:get_state(DocsBt),
    UrisSt = sam_db_btree:get_state(UrisBt),
    ModsSt = sam_db_btree:get_state(ModsBt),
    RefsSt = sam_db_btree:get_state(RefsBt),
    SigsSt = sam_db_btree:get_state(SigsBt),
    Header = {sam_header, ?DB_VERSION, DocsSt, UrisSt, ModsSt, RefsSt, SigsSt},

    % Just your standard fsync, write_header, fsync dance
    sam_db_file:sync(Fd),
    sam_db_file:write_header(Fd, Header),
    sam_db_file:sync(Fd),

    lager:info("Committed index.", []),
    {noreply, Db#db{timer_ref = undefined}};
handle_info(Msg, Db) ->
    {stop, {bad_info, Msg}, Db}.

code_change(_OldVsn, Db, _Extra) ->
    {ok, Db}.

prepare_updates(_Db, OldDoc, NewDoc) ->
    #{
        uri := Uri,
        pois := OldPOIs
    } = OldDoc,
    #{
        uri := Uri,
        pois := NewPOIs
    } = NewDoc,

    OldModPOIs = sam_poi:search(#{type => module}, data, OldPOIs),
    OldMods = lists:map(fun(Mod) ->
        {Mod, Uri}
    end, OldModPOIs),

    OldRefPOIs = sam_poi:search(#{type => [remote_call, local_call]}, [type, data], OldPOIs),
    OldRefs = lists:map(fun(Ref) ->
        case Ref of
            #{type := remote_call, data := {M, F, A}} ->
                {{M, F, A}, Uri};
            #{type := local_call, data := {F, A}} ->
                lists:foreach(fun({Mod, _}) ->
                    {{Mod, F, A}, Uri}
                end, OldMods)
        end
    end, OldRefPOIs),

    NewModPOIs = sam_poi:search(#{type => module}, data, NewPOIs),
    NewMods = lists:map(fun(Mod) ->
        {{Mod, Uri}, []}
    end, NewModPOIs),

    NewRefPOIs = sam_poi:search(#{type => [remote_call, local_call]}, [type, data, range], NewPOIs),
    NewRefMap = lists:foldl(fun(POI, Acc1) ->
        case POI of
            #{type := remote_call, data := {M, F, A}, range := Range} ->
                Key = {{M, F, A}, Uri},
                maps:put(Key, [Range | maps:get(Key, Acc1, [])], Acc1);
            #{type := local_call, data := {F, A}, range := Range} ->
                lists:foldl(fun(Mod, Acc2) ->
                    Key = {{Mod, F, A}, Uri},
                    maps:put(Key, [Range | maps:get(Key, Acc2, [])], Acc2)
                end, Acc1, NewMods)
        end
    end, #{}, NewRefPOIs),
    NewRefs = maps:fold(fun({MFA, DocUri}, Ranges, Acc) ->
        [{{MFA, DocUri}, Ranges} | Acc]
    end, [], NewRefMap),

    #{
        mods_to_add => NewMods,
        mods_to_rem => to_rem(NewMods, OldMods),
        refs_to_add => NewRefs,
        refs_to_rem => to_rem(NewRefs, OldRefs),
        sigs_to_add => [],
        sigs_to_rem => []
    }.

get_first(Bt, Lookup) ->
    % This only works for indexes that have a
    % two-tuple key, namely, mods and refs.
    %
    % The negative integer is just a placeholder
    % very small term to handle Erlang term
    % comparisons.
    StartKey = {Lookup, -16#100000000},
    FoldFun = fun({K, _} = Key, Val, _Acc) ->
        case Key of
            _ when K == Lookup ->
                throw({found, {Key, Val}});
            _ when K > Lookup ->
                throw(not_found)
        end
    end,
    try
        sam_db_btree:fold(Bt, FoldFun, not_found, #{start_key => StartKey})
    catch
        throw:{found, {K, V}} ->
            {K, V};
        throw:not_found ->
            not_found
    end.

get_all(Bt, Lookup) ->
    % This only works for indexes that have a
    % two-tuple key, namely, mods and refs.
    %
    % The negative integer is just a placeholder
    % very small term to handle Erlang term
    % comparisons.
    StartKey = {Lookup, -16#100000000},
    FoldFun = fun({K, _} = Key, Val, Acc) ->
        case Key of
            _ when K == Lookup ->
                [{Key, Val} | Acc];
            _ when K > Lookup ->
                throw({found, Acc})
        end
    end,
    Result = try
        sam_db_btree:fold(Bt, FoldFun, [], #{start_key => StartKey})
    catch
        throw:{found, R} -> R
    end,
    case Result of
        [] -> not_found;
        _ -> Result
    end.

get_all_startswith(Bt, Prefix) when is_list(Prefix) ->
    % For btrees that use a list key (i.e., uris)
    % this will return all keys that start with
    % the given prefix.
    FoldFun = fun(Key, Val, Acc) ->
        case lists:prefix(Prefix, Key) of
            true ->
                [{Key, Val} | Acc];
            false ->
                throw({found, Acc})
        end
    end,
    Result = try
        sam_db_btree:fold(Bt, FoldFun, [], #{start_key => Prefix})
    catch
        throw:{found, R} -> R
    end,
    case Result of
        [] -> not_found;
        _ -> Result
    end.

collect_updates(Clients, Updates) ->
    receive
        {'$gen_call', From, {updates, NewUpdates}} ->
            AllUpdates = merge_updates(NewUpdates, Updates),
            collect_updates([From | Clients], AllUpdates)
    after 0 ->
        {Clients, Updates}
    end.

merge_updates(ToAdd, Acc) ->
    KeysToAdd = maps:keys(ToAdd),
    KeysToAdd = maps:keys(Acc),
    lists:foldl(fun(Key) ->
        maps:put(Key, maps:get(Key, ToAdd) ++ maps:get(Key, Acc), Acc)
    end, Acc, KeysToAdd).

reset_db(Db) ->
    #db{
        fd = Fd
    } = Db,
    sam_db_file:truncate(Fd, 0),
    {ok, DocsBt} = sam_db_btree:open(Fd),
    {ok, UrisBt} = sam_db_btree:open(Fd),
    {ok, ModsBt} = sam_db_btree:open(Fd),
    {ok, RefsBt} = sam_db_btree:open(Fd),
    {ok, SigsBt} = sam_db_btree:open(Fd),
    Db#db{
        docs = DocsBt,
        uris = UrisBt,
        mods = ModsBt,
        refs = RefsBt,
        sigs = SigsBt
    }.

reset_timer(#db{timer_ref = undefined} = Db) ->
    Db#db{
        timer_ref = erlang:send_after(?COMMIT_INTERVAL, self(), commit)
    };
reset_timer(#db{timer_ref = Ref} = Db) ->
    erlang:cancel_timer(Ref),
    receive
        commit -> ok
    after 0 ->
        ok
    end,
    reset_timer(Db#db{timer_ref = undefined}).

db_file(RootUri) when is_binary(RootUri) ->
    DbDir = iolist_to_binary(filename:basedir(user_cache, "sam")),
    OtpPath = list_to_binary(code:root_dir()),
    <<SHA:160/integer>> = crypto:hash(sha, <<RootUri/binary, OtpPath/binary>>),
    DbFile = iolist_to_binary(lists:flatten(io_lib:format("~40.16.0b.samdb", [SHA]))),
    filename:join(DbDir, DbFile).

rev_uri(Uri) ->
    rev_path(sam_uri:to_path(Uri)).

rev_path(Path) ->
    lists:reverse(filename:split(Path)).

% Any Key in Keys that also exists in KVs is
% wasted effort as we'll just overwrite it.
to_rem(KVs, Keys) ->
    [Key || Key <- Keys, not lists:keymember(Key, 1, KVs)].
    