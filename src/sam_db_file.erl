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

% Based on a reduced version of couch_file from Apache CouchDB

-module(sam_db_file).
-behaviour(gen_server).

-define(MAX_PREAD_LEN, 16#40000000). % 1 GiB
-define(HEADER_OFFSET, 16#1000). % 4 KiB
-define(HEADER_SCAN_COUNT, 1024).
-define(HEADER_PREFIX_LEN, 24). % 16 UUID bytes + 8 size bytes

-record(file, {
    fname,
    fd,
    eof = 0
}).

% public API
-export([
    open/1,
    close/1,

    append_term/2,
    append_term_sha/2,
    append_binary/2,
    append_binary_sha/2,

    pread_term/2,
    pread_binary/2,

    write_header/2,
    read_header/1,

    fsize/1,
    sync/1,
    truncate/2,

    delete_tree/1
]).

-export([
    init/1,
    terminate/2,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    code_change/3
]).

open(FileName) ->
    proc_lib:start_link(?MODULE, init, [FileName]).

close(Fd) ->
    gen_server:call(Fd, close, infinity).
    
append_term(Fd, Term) ->
    append_binary(Fd, to_binary(Term)).

append_term_sha(Fd, Term) ->
    append_binary_sha(Fd, to_binary(Term)).

append_binary(Fd, Bin) when is_binary(Bin) ->
    gen_server:call(Fd, {append, Bin, <<>>}, infinity).

append_binary_sha(Fd, Bin) when is_binary(Bin) ->
    Hash = crypto:hash(sha, Bin),
    gen_server:call(Fd, {append, Bin, Hash}, infinity).

pread_term(Fd, Loc) ->
    case pread_binary(Fd, Loc) of
        {ok, Bin} ->
            {ok, to_term(Bin)};
        Error ->
            Error
    end.

pread_binary(Fd, Loc) ->
    case gen_server:call(Fd, {pread, Loc}, infinity) of
        {ok, Bin} ->
            {ok, Bin};
        {ok, Bin, Hash} ->
            case crypto:hash(sha, Bin) of
                Hash ->
                    {ok, Bin};
                _DifferentHash ->
                    erlang:error({file_corruption, Fd, Loc})
            end;
        Error ->
            Error
    end.

write_header(Fd, Data) ->
    Bin = to_binary(Data),
    Hash = crypto:hash(sha, Bin),
    gen_server:call(Fd, {write_header, Bin, Hash}, infinity).

read_header(Fd) ->
    case gen_server:call(Fd, read_header, infinity) of
        {ok, Bin} -> {ok, to_term(Bin)};
        Else -> Else
    end.

fsize(Fd) ->
    gen_server:call(Fd, fsize, infinity).

truncate(Fd, Pos) ->
    gen_server:call(Fd, {truncate, Pos}, infinity).

sync(Fd) ->
    case gen_server:call(Fd, sync, infinity) of
        ok ->
            ok;
        {error, Reason} ->
            erlang:error({fsync_error, Reason})
    end.

delete_tree(DirName) ->
    FoldFun = fun(File) ->
        Path = filename:join(DirName, File),
        case filelib:is_dir(Path) of
            true ->
                ok = delete_tree(Path),
                file:del_dir(Path);
            false ->
                file:delete(Path)
        end
    end,
    case file:list_dir(DirName) of
        {ok, Files} ->
            lists:foreach(FoldFun, Files),
            ok = file:del_dir(DirName);
        {error, enoent} ->
            ok
    end.

init(FileName) ->
    OpenOpts = [create, read, append, raw, binary],
    filelib:ensure_dir(FileName),
    case file:open(FileName, OpenOpts) of
        {ok, Fd} ->
            proc_lib:init_ack({ok, self()}),
            {ok, Length} = file:position(Fd, eof),
            St = maybe_write_uuid(#file{
                fname = FileName,
                fd = Fd,
                eof = Length
            }),
            gen_server:enter_loop(?MODULE, [], St);
        Error ->
            proc_lib:init_ack(Error)
    end.

terminate(_Reason, #file{fd = undefined}) ->
    ok;
terminate(_Reason, #file{fd = Fd}) ->
    ok = file:close(Fd).

handle_call(close, _From, St) ->
    {stop, normal, file:close(St#file.fd), #file{}};

handle_call({append, Bin, Hash}, _From, St) ->
    #file{
        fd = Fd,
        eof = Pos
    } = St,
    BinSize = size(Bin),
    HashSize = size(Hash),
    Size = BinSize + HashSize,
    case file:write(Fd, [Bin, Hash]) of
        ok ->
            {reply, {ok, {Pos, Size, HashSize}}, St#file{eof = Pos + Size}};
        Error ->
            {reply, Error, reset_eof(St)}
    end;

handle_call({pread, {Pos, Size, HashSize}}, _From, St) ->
    #file{
        fd = Fd,
        eof = Eof
    } = St,
    case Size of
        _ when Size > ?MAX_PREAD_LEN ->
            {reply, {error, pread_limit_exceeded}, St};
        _ when Pos + Size > Eof ->
            {reply, {error, read_beyond_eof}, St};
        _ ->
            case file:pread(Fd, Pos, Size) of
                {ok, <<Bin:Size/binary>>} ->
                    case HashSize of
                        0 ->
                            {reply, {ok, Bin}, St};
                        N when N > 0 ->
                            DataSize = Size - HashSize,
                            <<Data:DataSize/binary, Hash:HashSize/binary>> = Bin,
                            {reply, {ok, Data, Hash}, St}
                    end;
                Else ->
                    {reply, Else, St}
            end
    end;
        
handle_call(fsize, _From, St) ->
    {reply, file:position(St#file.fd, eof), St};

handle_call(sync, _From, St) ->
    case file:sync(St#file.fd) of
        ok ->
            {reply, ok, St};
        Error ->
            % We're intentionally dropping all knowledge
            % of this Fd so that we don't accidentally
            % recover in some whacky edge case that I
            % can't fathom.
            {stop, Error, Error, #file{}}
    end;

handle_call({truncate, Pos0}, _From, St) ->
    Pos1 = case Pos0 < 16 of
        true -> 0;
        false -> Pos0
    end,
    {ok, Pos1} = file:position(St#file.fd, Pos1),
    case file:truncate(St#file.fd) of
        ok ->
            {reply, ok, maybe_write_uuid(St#file{eof = Pos1})};
        Error ->
            {reply, Error, St}
    end;

handle_call({write_header, Bin, Hash}, _From, St) ->
    #file{
        fd = Fd,
        eof = Eof
    } = St,

    {ok, UUID} = file:pread(Fd, 0, 16),

    PaddingLen = case Eof rem ?HEADER_OFFSET of
        0 -> 0;
        N -> ?HEADER_OFFSET - N
    end,
    Padding = <<0:(8 * PaddingLen)>>,

    BinSize = size(Bin),
    HashSize = size(Hash),

    SizeInfo = <<BinSize:32/integer, HashSize:32/integer>>,

    ToWrite = [Padding, UUID, SizeInfo, Bin, Hash],

    case file:write(Fd, ToWrite) of
        ok ->
            {reply, ok, St#file{eof = Eof + iolist_size(ToWrite)}};
        Error ->
            {reply, Error, reset_eof(St)}
    end;

handle_call(read_header, _From, St) ->
    {reply, find_header(St, St#file.eof div ?HEADER_OFFSET), St}.

handle_cast(close, Fd) ->
    {stop, normal, Fd};

handle_cast(Msg, Fd) ->
    {stop, {bad_cast, Msg}, Fd}.

handle_info(Msg, St) ->
    {stop, {bad_info, Msg}, St}.

code_change(_OldVsn, St, _Extra) ->
    {ok, St}.

maybe_write_uuid(St) ->
    case St#file.eof > 0 of
        true ->
            St;
        false ->
            UUID = crypto:strong_rand_bytes(16),
            ok = file:write(St#file.fd, UUID),
            St#file{eof = 16}
    end.

find_header(St, CurrHeaderOffset) ->
    {ok, UUID} = file:pread(St#file.fd, 0, 16),
    find_header(St, CurrHeaderOffset, UUID).

find_header(_St, CurrHeaderOffset, _UUID) when CurrHeaderOffset < 0 ->
    no_valid_header;
find_header(St, CurrHeaderOffset, UUID) ->
    FirstOffset = max(0, CurrHeaderOffset - ?HEADER_SCAN_COUNT + 1),
    Offsets = [?HEADER_OFFSET * B || B <- lists:seq(FirstOffset, CurrHeaderOffset)],
    PreadLocs = [{Offset, ?HEADER_PREFIX_LEN} || Offset <- Offsets],
    
    {ok, Prefixes} = file:pread(St#file.fd, PreadLocs),

    % Prefixes come back in order from oldest to newest, after
    % we foldl over them the first valid header is the newest.
    PossibleHeaders = lists:foldl(fun({{Offset, ?HEADER_PREFIX_LEN}, Prefix}, Acc) ->
        case Prefix of
            <<UUID:16/binary, BSize:32/integer, HSize:32/integer>> when BSize + HSize > 0 ->
                [{Offset + ?HEADER_PREFIX_LEN, BSize, HSize} | Acc];
            _ ->
                % Not a header at this prefix
                Acc
        end
    end, [], lists:zip(PreadLocs, Prefixes)),

    case find_newest_header(St, PossibleHeaders) of
        {ok, HeaderBin} ->
            {ok, HeaderBin};
        not_found ->
            find_header(St, FirstOffset div ?HEADER_OFFSET - 1)
    end.

find_newest_header(_St, []) ->
    not_found;
find_newest_header(St, [{Offset, BinSize, HashSize} | RestPossible]) ->
    {ok, Data} = file:pread(St#file.fd, Offset, BinSize + HashSize),
    case Data of
        <<Bin:BinSize/binary, Hash:HashSize/binary>> ->
            case crypto:hash(sha, Bin) of
                Hash ->
                    {ok, Bin};
                _DifferentHash ->
                    find_newest_header(St, RestPossible)
            end;
        _ ->
            find_newest_header(St, RestPossible)
    end.

% In then event of a partially successful write we
% fixup our EOF position.
reset_eof(St) ->
    {ok, Eof} = file:position(St#file.fd, eof),
    St#file{eof = Eof}.

to_binary(Term) ->
    term_to_binary(Term, [compressed, {minor_version, 1}]).

to_term(Bin) ->
    binary_to_term(Bin, [safe]).
