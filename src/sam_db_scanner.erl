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

-module(sam_db_scanner).
-behaviour(gen_server).

-export([
    start_link/1,
    close/1
]).

-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).

-export([
    scan/1
]).

-record(st, {
    root_uri,
    pid
}).

-define(INDEX_EXTENSIONS, [
    <<".erl">>,
    <<".hrl">>,
    <<".yrl">>,
    <<".escript">>
]).

start_link(RootUri) ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, RootUri, []).

close(Pid) ->
    gen_server:call(Pid, close, infinity).

init(RootUri) ->
    {ok, #st{
        root_uri = RootUri,
        pid = erlang:spawn(?MODULE, scan, [RootUri])
    }}.

terminate(_Reason, #st{pid = Worker}) when is_pid(Worker) ->
    exit(Worker, kill);
terminate(_Reason, _St) ->
    ok.

handle_call(close, _From, St) ->
    {stop, normal, ok, St};
handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.

handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.

scan(RootUri) ->
    Uris = [
        sam_uri:from_path(code:root_dir()),
        RootUri
    ],
    lists:foreach(fun(Uri) ->
        Path = sam_uri:to_path(Uri),
        lager:info("Scanning: ~s", [Path]),
        scan_dir(Path, list_dir(Path))
    end, Uris).

scan_dir(Dir, Files) ->
    lists:foreach(fun(File) ->
        Path = filename:join(Dir, File),
        case file_or_dir(Path) of
            file ->
                case lists:member(filename:extension(Path), ?INDEX_EXTENSIONS) of
                    true ->
                        sam_db_indexer:index(sam_uri:from_path(Path));
                    false ->
                        ok
                end;
            dir ->
                scan_dir(Path, list_dir(Path));
            ignore ->
                ok
        end
    end, Files).

list_dir(Path) ->
    case file:list_dir(Path) of
        {ok, Files} ->
            lists:sort(Files);
        {error, _} ->
            []
    end.

file_or_dir(Path) ->
    IsRegular = filelib:is_regular(Path),
    IsDir = filelib:is_dir(Path),
    IsFile = filelib:is_file(Path),
    IsSymlink = is_symlink(Path),
    case {IsRegular, IsFile, IsDir, IsSymlink} of
        {true, true, _, _} ->
            file;
        {false, _, true, false} ->
            dir;
        _ ->
            ignore
    end.

is_symlink(Path) ->
    case file:read_link(Path) of
        {ok, _} -> true;
        {error, _} -> false
    end.
