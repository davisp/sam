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

-module(sam).

-export([
    main/1,
    configure_lager/0
]).

-export([
    exit/1
]).

main(Opts) ->
    application:load(lager),
    parse_opts(Opts),
    configure_lager(),
    {ok, _} = application:ensure_all_started(sam),

    lager:info("Sam has started.", []),

    % Allow for cleanly shutting down
    application:set_env(sam, root_pid, self()),
    receive
        {exit, Code} -> erlang:halt(Code);
        Else -> erlang:error({bad_shutdown, Else})
    end.


exit(Code) ->
    Stack = process_info(self(), current_stacktrace),
    lager:debug("Attempting to exit from: ~p", [Stack]),
    {ok, RootPid} = application:get_env(sam, root_pid),
    RootPid ! {exit, Code}.


parse_opts(Opts) ->
    case getopt:parse(options(), Opts) of
        {ok, {Parsed, _}} ->
            lists:foreach(fun({Key, Value}) ->
                application:set_env(sam, Key, Value)
            end, Parsed);
        {error, {invalid_option, _}} ->
            getopt:usage(options(), "sam"),
            halt(1)
    end.


options() ->
    DefaultLogDir = filename:basedir(user_log, "sam"),
    DefaultLogLevel = "debug",
    [
        {log_dir, $d, "log-dir", {string, DefaultLogDir},
            "Directory for log files"},
        {log_level, $l, "log-level", {string, DefaultLogLevel},
            "The level at which to log"}
    ].


configure_lager() ->
    {ok, LogDir} = application:get_env(sam, log_dir),
    {ok, LogLevel} = application:get_env(sam, log_level),
    LogFile = filename:join(LogDir, "sam.log"),
    ok = filelib:ensure_dir(LogFile),
    Handlers = [
        {lager_file_backend, [{file, LogFile}, {level, LogLevel}]}
    ],
    ok = application:set_env(lager, handlers, Handlers),
    ok = application:set_env(lager, crash_log, "crash.log"),
    ok = application:set_env(lager, log_root, LogDir).
