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

-module(sam_config).


-export([
    init/1,

    initialized/0,
    ready/0,
    
    root_uri/0,
    init_opts/0,
    capabilities/0,
    trace/0,
    workspace_folders/0
]).

init(Config) ->
    #{
        process_id := ProcessId,
        root_uri := RootUri,
        init_opts := InitOpts,
        capabilities := Capabilities,
        trace := Trace,
        workspace_folders := WorkspaceFolders
    } = Config,
    spawn_parent_monitor(ProcessId),
    application:set_env(sam, root_uri, RootUri),
    application:set_env(sam, init_opts, InitOpts),
    application:set_env(sam, capabilities, Capabilities),
    application:set_env(sam, trace, Trace),
    application:set_env(sam, workspace_folders, WorkspaceFolders).

initialized() ->
    application:set_env(sam, initialized, true).

ready() ->
    {ok, true} == application:get_env(sam, initialized).

root_uri() ->
    {ok, Uri} = application:get_env(sam, root_uri),
    Uri.

init_opts() ->
    {ok, InitOpts} = application:get_env(sam, init_opts),
    InitOpts.

capabilities() ->
    {ok, Capabilities} = application:get_env(sam, capabilities),
    Capabilities.

trace() ->
    {ok, Trace} = application:get_env(sam, trace),
    Trace.

workspace_folders() ->
    {ok, WorkspaceFolders} = application:get_env(sam, workspace_folders),
    WorkspaceFolders.

spawn_parent_monitor(null) ->
    ok;
spawn_parent_monitor(Pid) when is_integer(Pid) ->
    lager:error("Parent pid? ~p", [Pid]),
    Cmd = lists:flatten(io_lib:format("kill -0 ~b", [Pid])),
    spawn(fun() -> parent_monitor_loop(Cmd) end).

parent_monitor_loop(Cmd) ->
    case os:cmd(Cmd) of
        "" ->
            timer:sleep(1000),
            parent_monitor_loop(Cmd);
        _ ->
            % No such process output
            sam:exit(0)
    end.
