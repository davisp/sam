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

-type position() :: #{
    line := number(),
    character := number()
}.

-type range() :: #{
    start := position(),
    'end' := position()
}.

-type poi_type() ::
    module |
    export |
    exported_fun |
    import |
    imported_fun |
    include |
    include_lib |
    record |
    type |
    export_type |
    exported_type |
    spec |
    callback |
    attribute |
    function |
    remote_call |
    local_call |
    remote_fun |
    local_fun |
    record_index |
    record_field |
    record_access |
    %variable |
    macro.

-type poi() :: #{
    id := term(),
    type := atom(),
    data := term(),
    range := range()
}.

-type doc() :: #{
    uri := binary(),
    text := binary(),
    md5 := binary(),
    pois := [pois()]
}.
