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

-module(sam_provider_request_initialize).

-export([
    handle/1
]).

-include("sam.hrl").

handle(#{<<"params">> := Params} = Msg) ->
    Config = #{
        process_id => maps:get(<<"processId">>, Params),
        root_uri => case maps:get(<<"rootUri">>, Params) of
            null -> maps:get(<<"rootPath">>, Params, null);
            Uri -> Uri
        end,
        init_opts => maps:get(<<"initializationOptions">>, Params, #{}),
        capabilities => maps:get(<<"capabilities">>, Params),
        trace => maps:get(<<"trace">>, Params, <<"off">>),
        workspace_folders => maps:get(<<"workspaceFolders">>, Params, null)
    },
    sam_config:init(Config),
    sam_provider:response(Msg, #{
        serverInfo => #{
            name => <<"Sam - Your trusty Erlang Language Server hobbit helper">>,
            version => <<"0.0.0">>
        },
        capabilities => #{
            textDocumentSync => #{
                openClose => true,
                change => ?LSP_TEXT_DOCUMENT_SYNC_KIND_FULL,
                save => #{
                    includeText => false
                }
            },
            definitionProvider => true,
            hoverProvider => true,
            %completionProvider => #{
            %    triggerChars => [<<":">>, <<"(">>]
            %},
            signatureHelpProvider => #{
                triggerCharacters => [<<"(">>]
            }
        }
    }).