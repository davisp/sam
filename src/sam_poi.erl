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

-module(sam_poi).

-export([
    overlaps/3,
    range_to_tuple/1
]).


overlaps(POI, Line, Char) ->
    #{range := #{
        start := #{line := SLine, character := SChar},
        'end' := #{line := ELine, character := EChar}
    }} = POI,
    AfterStart = SLine =< Line andalso SChar =< Char,
    BeforeEnd = ELine >= Line andalso EChar >= Char,
    AfterStart andalso BeforeEnd.

range_to_tuple(#{start := Start, 'end' := End}) ->
    #{
        line := StartLine,
        character := StartChar
    } = Start,
    #{
        line := EndLine,
        character := EndChar
    } = End,
    {StartLine, StartChar, EndLine, EndChar}.
