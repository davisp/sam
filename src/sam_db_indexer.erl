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

-module(sam_db_indexer).
-behaviour(gen_server).

-export([
    start_link/0,

    index/1,
    clear/0
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
    add_to_index/1
]).

-record(st, {
    workers,
    queue
}).

-define(NUM_WORKERS, 16).

start_link() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).

index(Uri) ->
    gen_server:call(?MODULE, {index, Uri}, infinity).

clear() ->
    gen_server:call(?MODULE, clear, infinity).

init(_) ->
    {ok, #st{
        workers = #{},
        queue = queue:new()
    }}.

terminate(_Reason, St) ->
    #st{
        workers = Workers
    } = St,
    lists:foreach(fun(Pid) ->
        exit(Pid, kill)
    end, maps:keys(Workers)),
    ok.

handle_call({index, Uri}, _From, St) ->
    #st{
        queue = Q
    } = St,
    NewQ = queue:in(Uri, Q),
    {reply, ok, maybe_start_workers(St#st{queue = NewQ})};
handle_call(clear, _From, St) ->
    #st{
        workers = Workers
    } = St,
    lists:foreach(fun(Pid) ->
        exit(Pid, kill)
    end, maps:keys(Workers)),
    NewSt = #st{
        queue = queue:new(),
        workers = #{}
    },
    {reply, ok, NewSt};
handle_call(Msg, _From, St) ->
    {stop, {bad_call, Msg}, {bad_call, Msg}, St}.

handle_cast(Msg, St) ->
    {stop, {bad_cast, Msg}, St}.

handle_info({'DOWN', _, _, Pid, Reason}, St) ->
    #st{
        workers = Workers
    } = St,
    NewWorkers = maps:remove(Pid, Workers),
    case maps:get(Pid, Workers, undefined) of
        undefined ->
            lager:error("Unknown index worker died: ~p :: ~p", [Pid, Reason]);
        Uri when Reason /= normal ->
            lager:error("Failed to index: ~s :: ~p", [Uri, Reason]);
        _ when Reason == normal ->
            ok
    end,
    {noreply, maybe_start_workers(St#st{workers = NewWorkers})};
handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.

add_to_index(Uri) ->
    Path = sam_uri:to_path(Uri),
    case file:read_file(Path) of
        {ok, Contents} ->
            Md5 = crypto:hash(md5, Contents),
            IndexedMd5 = try
                sam_db:md5_for_uri(Uri)
            catch T:R:S ->
                lager:error("Failed to read md5 for ~s :: ~p~n~p", [Uri, {T, R}, S]),
                <<>>
            end,
            case Md5 == IndexedMd5 of
                true ->
                    % Already indexed
                    ok;
                false ->
                    lager:debug("~s : ~p /= ~p", [Uri, Md5, IndexedMd5]),
                    % Not indexed or changed since last index
                    POIs = sam_parser:parse(Uri, Contents),
                    sam_db:add_doc(#{
                        uri => Uri,
                        text => Contents,
                        md5 => crypto:hash(md5, Contents),
                        pois => POIs
                    }),
                    lager:debug("Indexed: ~s", [Uri])
            end;
        {error, Error} ->
            lager:error("Error reading file: ~s :: ~s", [Path, file:format_error(Error)])
    end.

maybe_start_workers(St) ->
    #st{
        queue = Q,
        workers = Workers
    } = St,
    QSize = queue:len(Q),
    NWorkers = maps:size(Workers),
    case QSize > 0 andalso NWorkers < ?NUM_WORKERS of
        true ->
            start_worker(St);
        false ->
            St
    end.

start_worker(St) ->
    #st{
        queue = Q,
        workers = Workers
    } = St,
    {{value, Uri}, RestQ} = queue:out(Q),
    {Pid, _} = erlang:spawn_monitor(?MODULE, add_to_index, [Uri]),
    #st{
        queue = RestQ,
        workers = Workers#{
            Pid => Uri
        }
    }.
