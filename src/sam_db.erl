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

    get_md5/1,

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

-define(SAM_DB_DOCS, sam_db_docs_table).
-define(SAM_DB_MODS, sam_db_mods_table).
-define(SAM_DB_REFS, sam_db_refs_table).

start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

get_md5(Uri) ->
    case ets:lookup(?SAM_DB_DOCS, Uri) of
        [{Uri, Md5, _}] ->
            Md5;
        [] ->
            not_found
    end.

add_doc(Doc) ->
    #{
        uri := Uri,
        md5 := Md5,
        pois := POIs
    } = Doc,
    rem_doc(Uri),
    ets:insert(?SAM_DB_DOCS, {Uri, Md5, POIs}),
    Mods = sam_poi:search(#{type => module}, data, POIs),
    lists:foreach(fun(Mod) ->
        ets:insert(?SAM_DB_REFS, {Mod, Uri})
    end, Mods),
    RefPOIs = sam_poi:search(#{type => [remote_call, local_call]}, [type, data, range], POIs),
    RefMap = lists:foldl(fun(POI, Acc1) ->
        case POI of
            #{type := remote_call, data := {M, F, A}, range := Range} ->
                Key = {{M, F, A}, Uri},
                maps:put(Key, [Range | maps:get(Key, Acc1, [])], Acc1);
            #{type := local_call, data := {F, A}, range := Range} ->
                lists:foldl(fun(Mod, Acc2) ->
                    Key = {{Mod, F, A}, Uri},
                    maps:put(Key, [Range | maps:get(Key, Acc2, [])], Acc2)
                end, Acc1, Mods)
        end
    end, #{}, RefPOIs),
    Refs = maps:fold(fun({MFA, DocUri}, Ranges, Acc) ->
        [{MFA, DocUri, Ranges} | Acc]
    end, [], RefMap),
    ets:insert(?SAM_DB_REFS, Refs).

rem_doc(Uri) ->
    Doc = case ets:lookup(?SAM_DB_DOCS, Uri) of
        [D] -> D;
        [] -> #{uri => Uri, md5 => <<>>, pois => []}
    end,
    #{
        uri := Uri,
        pois := POIs
    } = Doc,
    ets:delete(?SAM_DB_DOCS, Uri),
    
    Mods = sam_poi:search(#{type => module}, data, POIs),
    lists:foreach(fun(Mod) ->
        ets:delete_object(?SAM_DB_MODS, {Mod, Uri})
    end, Mods),
    
    Refs = sam_poi:search(#{type => [remote_call, local_call]}, [type, data], POIs),
    lists:foreach(fun(Ref) ->
        case Ref of
            #{type := remote_call, data := {M, F, A}} ->
                ets:match_delete(?SAM_DB_REFS, {{M, F, A}, Uri, '_'});
            #{type := local_call, data := {F, A}} ->
                lists:foreach(fun(Mod) ->
                    ets:match_delete(?SAM_DB_REFS, {{Mod, F, A}, Uri, '_'})
                end, Mods)
        end
    end, Refs).

init(_) ->
    BaseOpts = [
        public,
        named_table,
        {write_concurrency, true},
        {read_concurrency, true},
        compressed
    ],
    ets:new(?SAM_DB_DOCS, [set | BaseOpts]),
    ets:new(?SAM_DB_MODS, [set | BaseOpts]),
    ets:new(?SAM_DB_REFS, [set | BaseOpts]),
    {ok, nil}.

terminate(_Reason, _St) ->
    ok.

handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.

handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.
