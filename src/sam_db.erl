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

    add_doc/1,
    rem_doc/1,
    get_doc/1,

    uri_for_mod/1,
    get_refs/1,
    md5_for_uri/1
]).

-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).

-define(DB_VERSION, 2).
-define(NOT_READY, not_ready).
-define(COMMIT_INTERVAL, 5000).

-record(st, {
    root_uri,
    fd,
    docs,
    mods,
    refs,
    scanner,
    timer_ref
}).

start_link() ->
    {ok, Pid} = gen_server:start_link({local, ?MODULE}, ?MODULE, [], []),
    erlang:spawn(fun() ->
        Ref = erlang:monitor(process, Pid),
        receive
            {'DOWN', Ref, _, _, Reason} ->
                lager:info("sam_db died: ~p", [Reason])
        end
    end),
    {ok, Pid}.

set_uri(RootUri) ->
    gen_server:cast(?MODULE, {set_uri, RootUri}).

add_doc(Doc) ->
    gen_server:call(?MODULE, {add_doc, Doc}, infinity).

rem_doc(Uri) ->
    gen_server:call(?MODULE, {rem_doc, Uri}, infinity).

get_doc(Uri) ->
    {ok, DocBt} = gen_server:call(?MODULE, {get_tree, docs}, infinity),
    case sam_db_btree:lookup(DocBt, [Uri]) of
        [{Uri, not_found}] ->
            not_found;
        [{Uri, Doc}] ->
            {ok, Doc}
    end.

uri_for_mod(ModName) ->
    {ok, ModBt} = gen_server:call(?MODULE, {get_tree, mods}, infinity),
    try
        sam_db_btree:fold(ModBt, fun({M, Uri}, _, Acc) ->
            case M == ModName of
                true -> throw({found, Uri});
                false -> ok
            end,
            case M > ModName of
                true -> throw(not_found);
                false -> ok
            end,
            Acc
        end, not_found, #{start_key => {ModName, <<>>}})
    catch
        throw:{found, Uri} ->
            {ok, Uri};
        throw:not_found ->
            not_found
    end.

get_refs(MFA) ->
    {ok, RefsBt} = gen_server:call(?MODULE, {get_tree, refs}, infinity),
    Result = try
        sam_db_btree:fold(RefsBt, fun({RowMFA, Uri}, Ranges, Acc) ->
            lager:info("Checking: ~p ~p", [RowMFA, MFA]),
            case RowMFA == MFA of
                true ->
                    [{Uri, Ranges} | Acc];
                false ->
                    throw({found, Acc})
            end
        end, [], #{start_key => {MFA, <<>>}})
    catch
        throw:{found, Refs} ->
            Refs;
        throw:not_found ->
            []
    end,
    case Result of
        [] -> not_found;
        _ -> {ok, Result}
    end.

md5_for_uri(Uri) ->
    case get_doc(Uri) of
        {ok, #{md5 := Md5}} -> Md5;
        _ -> undefined
    end.

init(_) ->
    {ok, ?NOT_READY}.

terminate(_Reason, ?NOT_READY) ->
    ok;
terminate(_Reason, St) ->
    lager:info("sam_db terminating: ~p", [_Reason]),
    #st{
        fd = Fd,
        scanner = Scanner
    } = St,
    sam_db_file:close(Fd),
    exit(Scanner, shutdown).

handle_call(_Msg, _From, ?NOT_READY) ->
    {reply, ?NOT_READY, ?NOT_READY};
handle_call({get_tree, Tree}, _From, St) ->
    Reply = case Tree of
        docs -> {ok, St#st.docs};
        mods -> {ok, St#st.mods};
        refs -> {ok, St#st.refs};
        _ -> {error, unknown_tree, Tree}
    end,
    {reply, Reply, St};
handle_call({add_doc, Doc}, From, St) ->
    {Clients, Docs} = collect_docs(),
    NewSt = add_docs([Doc | Docs], St),
    lists:map(fun(Client) ->
        gen:reply(Client, ok)
    end, [From | Clients]),
    {noreply, NewSt};
handle_call({rem_doc, Uri}, _From, St) ->
    NewSt = case sam_db_btree:lookup(St#st.docs, [Uri]) of
        [{Uri, not_found}] ->
            St;
        [{Uri, Doc}] ->
            rem_doc(Doc, St)
    end,
    {reply, ok, NewSt};
handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast({set_uri, RootUri}, ?NOT_READY) ->
    {ok, Fd} = sam_db_file:open(db_file(RootUri)),
    NewSt = try
        BaseSt = case sam_db_file:read_header(Fd) of
            {ok, {sam_header, ?DB_VERSION, DocsSt, ModsSt, RefsSt}} ->
                lager:debug("Reopened database.", []),
                {ok, DocsBt} = sam_db_btree:open(Fd, DocsSt),
                {ok, ModsBt} = sam_db_btree:open(Fd, ModsSt),
                {ok, RefsBt} = sam_db_btree:open(Fd, RefsSt),
                #st{
                    root_uri = RootUri,
                    fd = Fd,
                    docs = DocsBt,
                    mods = ModsBt,
                    refs = RefsBt
                };
            Else ->
                lager:warning("Failed to open database: ~p", [Else]),
                reset_db(#st{
                    root_uri = RootUri,
                    fd = Fd
                })
        end,
        {ok, Scanner} = sam_db_scanner:start_link(RootUri),
        BaseSt#st{
            scanner = Scanner
        }
    catch T:R:S ->
        lager:error("Failed to initialize database: ~s :: ~p~n~p", [RootUri, {T, R}, S]),
        sam_db_file:close(Fd),
        ?NOT_READY
    end,
    {noreply, NewSt};
handle_cast({set_uri, RootUri}, OldSt) ->
    #st{
        fd = Fd,
        scanner = Scanner
    } = OldSt,
    sam_db_file:close(Fd),
    sam_db_scanner:close(Scanner),
    handle_cast({set_uri, RootUri}, ?NOT_READY);
handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.

handle_info(commit, St) ->
    #st{
        fd = Fd,
        docs = DocsBt,
        mods = ModsBt,
        refs = RefsBt,
        timer_ref = Timer
    } = St,
    erlang:cancel_timer(Timer),

    DocsSt = sam_db_btree:get_state(DocsBt),
    ModsSt = sam_db_btree:get_state(ModsBt),
    RefsSt = sam_db_btree:get_state(RefsBt),
    Header = {sam_header, ?DB_VERSION, DocsSt, ModsSt, RefsSt},

    % fsync, write_header, fsync
    sam_db_file:sync(Fd),
    sam_db_file:write_header(Fd, Header),
    sam_db_file:sync(Fd),

    lager:info("Committed index.", []),
    {noreply, St#st{timer_ref = undefined}};
handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.

reset_db(St) ->
    #st{
        fd = Fd
    } = St,
    sam_db_file:truncate(Fd, 0),
    {ok, DocsBt} = sam_db_btree:open(Fd),
    {ok, ModsBt} = sam_db_btree:open(Fd),
    {ok, RefsBt} = sam_db_btree:open(Fd),
    St#st{
        docs = DocsBt,
        mods = ModsBt,
        refs = RefsBt
    }.

collect_docs() ->
    receive
        {'$gen_call', From, {add_doc, Doc}} ->
            {Clients, Docs} = collect_docs(),
            {[From | Clients], [Doc | Docs]}
    after 0 ->
        {[], []}
    end.

add_docs(Docs, St) ->
    #{
        docs_to_add := DocsToAdd,
        mods_to_add := ModsToAdd,
        mods_to_rem := ModsToRem,
        refs_to_add := RefsToAdd,
        refs_to_rem := RefsToRem
    } = prepare_updates(Docs, St),
    {ok, NewDocsBt} = sam_db_btree:update(St#st.docs, DocsToAdd, []),
    {ok, NewModsBt} = sam_db_btree:update(St#st.mods, ModsToAdd, ModsToRem),
    {ok, NewRefsBt} = sam_db_btree:update(St#st.refs, RefsToAdd, RefsToRem),
    St#st{
        docs = NewDocsBt,
        mods = NewModsBt,
        refs = NewRefsBt,
        timer_ref = reset_timer(St#st.timer_ref)
    }.

prepare_updates(Docs, St) ->
    Uris = [Uri || #{uri := Uri} <- Docs],
    OldDocs = sam_db_btree:lookup(St#st.docs, Uris),
    InitAcc = #{
        docs_to_add => [],
        mods_to_add => [],
        mods_to_rem => [],
        refs_to_add => [],
        refs_to_rem => []
    },
    lists:foldl(fun(NewDoc, Acc) ->
        #{
            uri := Uri
        } = NewDoc,
        #{
            docs_to_add := DocsToAdd,
            mods_to_add := ModsToAdd,
            mods_to_rem := ModsToRem,
            refs_to_add := RefsToAdd,
            refs_to_rem := RefsToRem
        } = Acc,
        {Uri, OldDoc} = lists:keyfind(Uri, 1, OldDocs),
        OldMod = get_mod(OldDoc),
        NewMod = get_mod(NewDoc),
        {NewModsToAdd, NewModsToRem} = case {OldMod, NewMod} of
            {not_found, _} when NewMod /= not_found ->
                % Previous doc did not exist or did not have a module
                {[{{NewMod, Uri}, []} | ModsToAdd], ModsToRem};
            {_, not_found} when OldMod /= not_found ->
                % Module definition was removed
                {ModsToAdd, [{OldMod, Uri} | ModsToRem]};
            {NewMod, NewMod} ->
                % No change to module
                {ModsToAdd, ModsToRem};
            {OldMod, NewMod} ->
                % Module changed
                {[{{NewMod, Uri}, []} | ModsToAdd], [{OldMod, Uri} | ModsToRem]}
        end,
        OldRefs = get_refs_int(OldDoc),
        NewRefs = get_refs_int(NewDoc),
        NewRefsToRem = lists:foldl(fun({RefKey, _}, RefAcc) ->
            case lists:keymember(RefKey, 1, NewRefs) of
                true -> RefAcc;
                false -> [RefKey | RefAcc]
            end
        end, RefsToRem, OldRefs),
        Acc#{
            docs_to_add := [{Uri, NewDoc} | DocsToAdd],
            mods_to_add := NewModsToAdd,
            mods_to_rem := NewModsToRem,
            refs_to_add := NewRefs ++ RefsToAdd,
            refs_to_rem := NewRefsToRem
        }
    end, InitAcc, Docs).

rem_doc(Doc, St) ->
    #{
        uri := Uri,
        pois := POIs
    } = Doc,
    {ok, NewDocsBt} = sam_db_btree:update(St#st.docs, [], [Uri]),
    {ok, NewModsBt} = case get_mod(POIs) of
        not_found -> {ok, St#st.mods};
        ModName -> sam_db_btree:update(St#st.mods, [], [{ModName, Uri}])
    end,
    {RefsToRem, _} = lists:unzip(get_refs_int(Doc)),
    {ok, NewRefsBt} = sam_db_btree:update(St#st.refs, [], RefsToRem),
    St#st{
        docs = NewDocsBt,
        mods = NewModsBt,
        refs = NewRefsBt,
        timer_ref = reset_timer(St#st.timer_ref)
    }.

reset_timer(undefined) ->
    erlang:send_after(?COMMIT_INTERVAL, self(), commit);
reset_timer(Ref) ->
    erlang:cancel_timer(Ref),
    receive
        commit -> ok
    after 0 ->
        ok
    end,
    reset_timer(undefined).


get_mod(not_found) ->
    not_found;
get_mod(#{pois := POIs}) ->
    case pois_by_type(module, POIs) of
        [#{type := module, data := ModName} | _] ->
            ModName;
        _ ->
            not_found
    end.

get_refs_int(not_found) ->
    [];
get_refs_int(Doc) ->
    #{
        uri := Uri,
        pois := POIs
    } = Doc,
    ModName = get_mod(#{pois => POIs}),
    BaseRefs = lists:foldl(fun(POI, Acc) ->
        case POI of
            #{type := remote_call, data := MFA, range := Range} ->
                maps:put(MFA, [Range | maps:get(MFA, Acc, [])], Acc);
            #{type := local_call, data := {F, A}, range := Range} when ModName /= not_found ->
                MFA = {ModName, F, A},
                maps:put(MFA, [Range | maps:get(MFA, Acc, [])], Acc);
            _ ->
                Acc
        end
    end, #{}, POIs),
    lists:map(fun({MFA, Ranges}) ->
        {{MFA, Uri}, Ranges}
    end, maps:to_list(BaseRefs)).

pois_by_type(Type, POIs) ->
    lists:filter(fun(POI) ->
        maps:get(type, POI, undefined) == Type
    end, POIs).

db_file(RawRootUri) ->
    DbDir = iolist_to_binary(filename:basedir(user_cache, "sam")),
    RootUri = iolist_to_binary(RawRootUri),
    OtpPath = list_to_binary(code:root_dir()),
    <<SHA:160/integer>> = crypto:hash(sha, <<RootUri/binary, OtpPath/binary>>),
    DbFile = iolist_to_binary(lists:flatten(io_lib:format("~40.16.0b.samdb", [SHA]))),
    filename:join(DbDir, DbFile).
