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

-define(JSONRPC_PARSE_ERROR, -32700).
-define(JSONRPC_INVALID_REQUEST, -32600).
-define(JSONRPC_METHOD_NOT_FOUND, -32601).
-define(JSONRPC_INVALID_PARAMS, -32602).
-define(JSONRPC_INTERNAL_ERROR, -32603).
-define(JSONRPC_SERVER_ERROR_START, -32099).
-define(JSONRPC_SERVER_ERROR_END, -32000).
-define(JSONRPC_SERVER_NOT_INITIALIZED, -32002).
-define(JSONRPC_UNKNOWN_ERROR_CODE, -32001).
-define(JSONRPC_REQUEST_CANCELLED, -32800).
-define(JSONRPC_CONTENT_MODIFIED, -32801).


-define(LSP_TEXT_DOCUMENT_SYNC_KIND_NONE, 0).
-define(LSP_TEXT_DOCUMENT_SYNC_KIND_FULL, 1).
-define(LSP_TEXT_DOCUMENT_SYNC_KIND_INCREMENTAL, 2).

-define(LSP_SYMBOL_KIND_FILE, 1).
-define(LSP_SYMBOL_KIND_MODULE, 2).
-define(LSP_SYMBOL_KIND_NAMESPACE, 3).
-define(LSP_SYMBOL_KIND_PACKAGE, 4).
-define(LSP_SYMBOL_KIND_CLASS, 5).
-define(LSP_SYMBOL_KIND_METHOD, 6).
-define(LSP_SYMBOL_KIND_PROPERTY, 7).
-define(LSP_SYMBOL_KIND_FIELD, 8).
-define(LSP_SYMBOL_KIND_CONSTRUCTOR, 9).
-define(LSP_SYMBOL_KIND_ENUM, 10).
-define(LSP_SYMBOL_KIND_INTERFACE, 11).
-define(LSP_SYMBOL_KIND_FUNCTION, 12).
-define(LSP_SYMBOL_KIND_VARIABLE, 13).
-define(LSP_SYMBOL_KIND_CONSTANT, 14).
-define(LSP_SYMBOL_KIND_STRING, 15).
-define(LSP_SYMBOL_KIND_NUMBER, 16).
-define(LSP_SYMBOL_KIND_BOOLEAN, 17).
-define(LSP_SYMBOL_KIND_ARRAY, 18).
-define(LSP_SYMBOL_KIND_OBJECT, 19).
-define(LSP_SYMBOL_KIND_KEY, 20).
-define(LSP_SYMBOL_KIND_NULL, 21).
-define(LSP_SYMBOL_KIND_ENUM_MEMBER, 22).
-define(LSP_SYMBOL_KIND_STRUCT, 23).
-define(LSP_SYMBOL_KIND_EVENT, 24).
-define(LSP_SYMBOL_KIND_OPERATOR, 25).
-define(LSP_SYMBOL_KIND_TYPE_PARAMETER, 26).
