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

-module(sam_provider_notify_did_open).

-export([
    handle/1
]).

%#{
%    <<"jsonrpc">> => <<"2.0">>,
%    <<"method">> => <<"textDocument/didOpen">>,
%    <<"params">> => #{
%        <<"textDocument">> => #{
%            <<"languageId">> => <<"erlang">>,
%            <<"text">> => <<"% Licensed under the Apache License, Version 2.0 (the \"License\"); ...">>,
%            <<"uri">> => <<"file:///Volumes/Macintosh%20HD/Users/davisp/github/davisp/sam/src/sam_provider_notify_did_save.erl">>,
%            <<"version">> => 1
%        }
%    }
%}

handle(#{<<"params">> := Params}) ->
    #{
        <<"textDocument">> := #{
            <<"uri">> := RawUri,
            <<"text">> := Text
        }
    } = Params,
    Uri = sam_uri:normalize(RawUri),
    sam_file_server:opened(Uri, Text).
