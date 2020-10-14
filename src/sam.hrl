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


-define(JSONRPC_ERROR(Code, Mesg), throw({jsonrpc_error, Code, Msg})).
