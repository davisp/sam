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

-module(sam_db_file_test).


-include_lib("eunit/include/eunit.hrl").
-include("sam_test.hrl").


can_open_test() ->
    FileName = <<"test_file">>,
    {ok, Pid} = sam_db_file:open(FileName),
    ?assert(is_pid(Pid)),
    ?assertEqual({ok, 16}, sam_db_file:fsize(Pid)),
    sam_db_file:close(Pid),
    file:delete(FileName).
    

sam_db_file_test_() ->
    {
        setup,
        fun setup_all/0,
        fun teardown_all/1,
        {
            foreach,
            fun setup/0,
            fun teardown/1,
            [
                ?TDEF_FE(can_read_data),
                ?TDEF_FE(can_write_data),
                ?TDEF_FE(can_write_hashed),
                ?TDEF_FE(can_detect_corruption),
                ?TDEF_FE(read_beyond_eof_error),
                ?TDEF_FE(exceed_pread_limit),
                ?TDEF_FE(can_write_header),
                ?TDEF_FE(can_read_header),
                ?TDEF_FE(no_valid_header),
                ?TDEF_FE(no_valid_header_because_uuid_corruption),
                ?TDEF_FE(no_valid_header_because_hash_corruption),
                ?TDEF_FE(no_valid_header_because_truncation),
                ?TDEF_FE(last_of_many_headers),
                ?TDEF_FE(can_truncate),
                ?TDEF_FE(cannot_truncate_uuid),
                ?TDEF_FE(can_sync),
                ?TDEF_FE(can_delete_tree)
            ]
        }
    }.

setup_all() ->
    ok.

teardown_all(_) ->
    ok.

setup() ->
    FileNameStr = io_lib:format("test_file.~b", [rand:uniform(16#100000000)]),
    FileNameBin = iolist_to_binary(FileNameStr),
    {ok, Pid} = sam_db_file:open(FileNameBin),
    {Pid, FileNameBin}.

teardown({Pid, FileName}) ->
    sam_db_file:close(Pid),
    file:delete(FileName).

can_read_data({Pid, _}) ->
    {ok, UUID} = sam_db_file:pread_binary(Pid, {0, 16, 0}),
    ?assertEqual(16, size(UUID)).

can_write_data({Pid, _}) ->
    Bin = crypto:strong_rand_bytes(32),
    {ok, Loc} = sam_db_file:append_binary(Pid, Bin),
    {ok, ReadBin} = sam_db_file:pread_binary(Pid, Loc),
    ?assertEqual(Bin, ReadBin).

can_write_hashed({Pid, _}) ->
    {ok, Loc} = sam_db_file:append_term_sha(Pid, foo),
    ?assertEqual({ok, foo}, sam_db_file:pread_term(Pid, Loc)).

can_detect_corruption({Pid, FileName}) ->
    {ok, {Pos, Size, HashSize} = Loc} = sam_db_file:append_term_sha(Pid, foo),
    ?assertEqual({ok, foo}, sam_db_file:pread_term(Pid, Loc)),
    
    % Corrupt the file by zeroing out the hash
    {ok, Fd} = file:open(FileName, [read, write, raw, binary]),
    {ok, _} = file:position(Fd, Pos + Size - HashSize),
    ok = file:write(Fd, <<0:(8 * HashSize)>>),
    ok = file:close(Fd),

    ?assertError({file_corruption, _, _}, sam_db_file:pread_term(Pid, Loc)).

read_beyond_eof_error({Pid, _}) ->
    ?assertEqual({error, read_beyond_eof}, sam_db_file:pread_term(Pid, {100000, 100000, 0})).

exceed_pread_limit({Pid, _}) ->
    ?assertEqual({error, pread_limit_exceeded}, sam_db_file:pread_term(Pid, {0, 16#1000000000, 0})).

can_write_header({Pid, _}) ->
    ok = sam_db_file:write_header(Pid, header).

can_read_header({Pid, _}) ->
    ok = sam_db_file:write_header(Pid, header),
    {ok, _} = sam_db_file:append_term(Pid, some_data),
    ?assertEqual({ok, header}, sam_db_file:read_header(Pid)).


no_valid_header({Pid, _}) ->
    ?assertEqual(no_valid_header, sam_db_file:read_header(Pid)).

no_valid_header_because_uuid_corruption({Pid, FileName}) ->
    ok = sam_db_file:write_header(Pid, header),
    ?assertEqual({ok, header}, sam_db_file:read_header(Pid)),
    
    % Corrupt the file by zeroing out the hash
    {ok, Fd} = file:open(FileName, [read, write, raw, binary]),
    {ok, _} = file:position(Fd, 4095),
    ok = file:write(Fd, <<0:(8 * 16)>>),
    ok = file:close(Fd),

    ?assertEqual(no_valid_header, sam_db_file:read_header(Pid)).

no_valid_header_because_hash_corruption({Pid, FileName}) ->
    ok = sam_db_file:write_header(Pid, header),
    ?assertEqual({ok, header}, sam_db_file:read_header(Pid)),
    
    % Corrupt the file by zeroing out the hash
    {ok, Fd} = file:open(FileName, [read, write, raw, binary]),
    {ok, <<BinSize:32/integer>>} = file:pread(Fd, 4096 + 16, 4),
    {ok, _} = file:position(Fd, 4096 + 16 + 8 + BinSize),
    ok = file:write(Fd, <<0:(8 * 20)>>),
    ok = file:close(Fd),

    ?assertEqual(no_valid_header, sam_db_file:read_header(Pid)).

no_valid_header_because_truncation({Pid, FileName}) ->
    ok = sam_db_file:write_header(Pid, {header, crypto:strong_rand_bytes(1024)}),
    ?assertMatch({ok, {header, _}}, sam_db_file:read_header(Pid)),
    
    % Corrupt the file by zeroing out the hash
    {ok, Fd} = file:open(FileName, [read, write, raw, binary]),
    {ok, <<BinSize:32/integer>>} = file:pread(Fd, 4096 + 16, 4),
    {ok, _} = file:position(Fd, 4096 + 16 + 8 + round(BinSize / 2)),
    ok = file:truncate(Fd),
    ok = file:close(Fd),

    ?assertEqual(no_valid_header, sam_db_file:read_header(Pid)).

last_of_many_headers({Pid, _}) ->
    lists:foreach(fun(I) ->
        sam_db_file:write_header(Pid, {header, I})
    end, lists:seq(1, 2048)),
    ?assertEqual({ok, {header, 2048}}, sam_db_file:read_header(Pid)).

can_truncate({Pid, _}) ->
    UUID0 = sam_db_file:pread_binary(Pid, {0, 16, 0}),

    ok = sam_db_file:write_header(Pid, header),
    ?assert(sam_db_file:fsize(Pid) > 4096),
    ok = sam_db_file:truncate(Pid, 16),
    ?assertEqual({ok, 16}, sam_db_file:fsize(Pid)),

    UUID1 = sam_db_file:pread_binary(Pid, {0, 16, 0}),

    ?assertEqual(UUID0, UUID1).

cannot_truncate_uuid({Pid, _}) ->
    UUID0 = sam_db_file:pread_binary(Pid, {0, 16, 0}),

    ok = sam_db_file:write_header(Pid, header),
    ?assert(sam_db_file:fsize(Pid) > 4096),
    ok = sam_db_file:truncate(Pid, 8),
    ?assertEqual({ok, 16}, sam_db_file:fsize(Pid)),

    UUID1 = sam_db_file:pread_binary(Pid, {0, 16, 0}),

    ?assertNotEqual(UUID0, UUID1).

can_sync({Pid, _}) ->
    ?assertEqual(ok, sam_db_file:sync(Pid)).


can_delete_tree(_) ->
    Paths = [
        "__test_dir/a.txt",
        "__test_dir/foo/b.txt",
        "__test_dir/foo/bar/c.txt",
        "__test_dir/foo/baz/d.txt",
        "__test_dir/foo/baz/bam"
    ],
    lists:foreach(fun(Path) ->
        case lists:suffix(".txt", Path) of
            true ->
                filelib:ensure_dir(Path),
                file:write_file(Path, "some data\n");
            false ->
                filelib:ensure_dir(filename:join(Path, "stuff.txt"))
        end
    end, Paths),
    sam_db_file:delete_tree("__test_dir").
