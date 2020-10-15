

all: compile


compile:
	rebar3 do compile, escriptize

check:
	rebar3 do eunit, cover
