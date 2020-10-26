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

-module(sam_diagnostics).
-behavior(gen_server).

-export([
    start_link/0,
    diagnose/1
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
    run_diagnosis/1
]).

-include("sam.hrl").

-define(JOBS, sam_diagnostics_jobs).
-define(URIS, sam_diagnostics_uris).

start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

diagnose(Uri) ->
    gen_server:cast(?MODULE, {diagnose, Uri}).

init(_) ->
    ets:new(?JOBS, [set, named_table]),
    ets:new(?URIS, [set, named_table]),
    {ok, nil}.

terminate(_, _) ->
    ok.

handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast({diagnose, Uri}, St) ->
    case ets:lookup(?URIS, Uri) of
        [{Uri, _}] -> ok;
        [] -> start_job(Uri)
    end,
    {noreply, St};
handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.

handle_info({'DOWN', _, _, Pid, Reason}, St) ->
    [{Pid, Uri}] = ets:lookup(?JOBS, Pid),
    ets:delete(?JOBS, Pid),
    ets:delete(?URIS, Uri),
    if Reason == normal -> ok; true ->
        lager:error("Failed to diagnose ~s: ~p", [Uri, Reason])
    end,
    {noreply, St};
handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.

run_diagnosis(Uri) ->
    Path = sam_uri:to_path(Uri),
    Diagnostics = case compile:file(binary_to_list(Path), compile_opts(Uri)) of
        {ok, _Module, _Binary, Warnings} ->
            lists:map(fun(Warning) ->
                make_diagnostics(Uri, Warning, ?LSP_DIAGNOSTIC_SEVERITY_WARNING)
            end, Warnings);
        {error, Errors, Warnings} ->
            ErrorDiagnostics = lists:map(fun(Error) ->
                make_diagnostics(Uri, Error, ?LSP_DIAGNOSTIC_SEVERITY_ERROR)
            end, Errors),
            WarningDiagnostics = lists:map(fun(Warning) ->
                make_diagnostics(Uri, Warning, ?LSP_DIAGNOSTIC_SEVERITY_WARNING)
            end, Warnings),
            ErrorDiagnostics ++ WarningDiagnostics
    end,
    Flattened = lists:flatten(Diagnostics),
    Msg = #{
        jsonrpc => <<"2.0">>,
        method => <<"textDocument/publishDiagnostics">>,
        params => #{
            uri => Uri,
            diagnostics => Flattened
        }
    },
    sam_client:send(publish_diagnostics_notification, Msg).

make_diagnostics(Uri, {Path, Msgs}, Severity) ->
    lists:map(fun({Line, Module, Desc}) ->
        MsgUri = sam_uri:from_path(Path),
        make_diagnostic(Uri, MsgUri, Line, Module, Desc, Severity)
    end, Msgs).

make_diagnostic(Uri, Uri, Line, Module, Desc, Severity) ->
    % An error message from the file that was compiled
    #{
        range => #{
            start => #{line => Line - 1, character => 0},
            'end' => #{line => Line, character => 0}
        },
        severity => Severity,
        source => <<"erlc">>,
        message => iolist_to_binary(Module:format_error(Desc))
    }.

compile_opts(Uri) ->
    BaseOpts = [
        binary,
        return_warnings,
        return_errors
    ],
    IncludeOpts = case sam_db:get_doc(Uri) of
        #{pois := POIs} ->
            Query = #{
                type => [include, include_lib, behavior]
            },
            Includes = sam_poi:search(Query, [type, data], POIs),
            lists:flatmap(fun(POI) ->
                process_include(Uri, POI)
            end, Includes);
        _ ->
            []
    end,
    BaseOpts ++ IncludeOpts.

process_include(Uri, #{type := include, data := FileName}) ->
    case sam_db:get_uris_from_tail(FileName) of
        not_found ->
            lager:info("No uris found for: ~p", [FileName]),
            [];
        [IncludeUri] ->
            [{i, binary_to_list(filename:dirname(sam_uri:to_path(IncludeUri)))}];
        Uris ->
            IncludeUri = closest_uri(Uri, Uris),
            [{i, binary_to_list(filename:dirname(sam_uri:to_path(IncludeUri)))}]
    end;
process_include(Uri, #{type := include_lib, data := FileName}) ->
    case sam_db:get_uris_from_tail(FileName) of
        not_found ->
            lager:info("No uris found for: ~p", [FileName]),
            [];
        [IncludeUri] ->
            IncludeDir = drop_common_tail(sam_uri:to_path(IncludeUri), iolist_to_binary(FileName)),
            [{i, binary_to_list(IncludeDir)}];
        Uris ->
            IncludeUri = closest_uri(Uri, Uris),
            IncludeDir = drop_common_tail(sam_uri:to_path(IncludeUri), iolist_to_binary(FileName)),
            [{i, binary_to_list(IncludeDir)}]
    end;
process_include(_Uri, #{type := behavior, data := Module}) ->
    case sam_db:get_doc_for_mod(Module) of
        #{uri := Uri} ->
            Path = sam_uri:to_path(Uri),
            Src = filename:dirname(Path),
            App = filename:dirname(Src),
            EBin = filename:join(App, "ebin"),
            code:add_path(binary_to_list(EBin)),
            [];
        _ ->
            []
    end.

closest_uri(Uri, Uris) ->
    UriParts = filename:split(Uri),
    Tagged = lists:map(fun(U) ->
        {lcp_len(UriParts, filename:split(sam_uri:to_path(U))), U}
    end, Uris),
    [{_Depth, Found} | _] = lists:reverse(lists:sort(Tagged)),
    Found.

lcp_len([H | T1], [H | T2]) ->
    lcp_len(T1, T2) + 1;
lcp_len(_, _) ->
    0.

drop_common_tail(Path, Tail) ->
    PathParts = lists:reverse(filename:split(Path)),
    TailParts = lists:reverse(filename:split(Tail)),
    true = lists:prefix(TailParts, PathParts),
    Dir = lists:nthtail(length(TailParts), PathParts),
    filename:join(lists:reverse(Dir)).

start_job(Uri) ->
    {Pid, _} = erlang:spawn_monitor(?MODULE, run_diagnosis, [Uri]),
    ets:insert(?JOBS, {Pid, Uri}),
    ets:insert(?URIS, {Uri, Pid}).

