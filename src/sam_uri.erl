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

-module(sam_uri).

-export([
    normalize/1,
    from_path/1,
    to_path/1
]).

normalize(Uri) ->
    case to_path(Uri) of
        <<"/Volumes/Macintosh%20HD", Rest/binary>> ->
            from_path(Rest);
        <<"/Volumes/Macintosh HD", Rest/binary>> ->
            from_path(Rest);
        _E ->
            Uri
    end.

from_path(Path) when is_list(Path) ->
    from_path(iolist_to_binary(Path));
from_path(Path) when is_binary(Path) ->
    AbsPath = filename:absname(Path),
    <<"file://", AbsPath/binary>>.

to_path(Uri) when is_list(Uri) ->
    to_path(iolist_to_binary(Uri));
to_path(Uri) when is_binary(Uri) ->
    case uri_string:normalize(Uri, [return_map]) of
        #{scheme := <<"file">>, path := Path} ->
            Path;
        _E ->
            lager:debug("uri_error: ~p", [_E]),
            uri_error
    end.
