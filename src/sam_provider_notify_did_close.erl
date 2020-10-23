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

-module(sam_provider_notify_did_close).

-export([
    handle/1
]).

%#{
%    <<"jsonrpc">> => <<"2.0">>,
%    <<"method">> => <<"textDocument/didClose">>,
%    <<"params">> => #{
%        <<"textDocument">> => #{
%            <<"uri">> => <<"file:///Volumes/Macintosh%20HD/Users/davisp/github/davisp/sam/src/sam_provider_notify_did_save.erl">>
%        }
%    }
%}

handle(#{<<"params">> := Params}) ->
    #{
        <<"textDocument">> := #{
            <<"uri">> := RawUri
        }
    } = Params,
    Uri = sam_uri:normalize(RawUri),
    sam_file_server:closed(Uri).
