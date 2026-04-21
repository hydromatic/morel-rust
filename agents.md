<!--
{% comment %}
Licensed to Julian Hyde under one or more contributor license
agreements.  See the NOTICE file distributed with this work
for additional information regarding copyright ownership.
Julian Hyde licenses this file to you under the Apache
License, Version 2.0 (the "License"); you may not use this
file except in compliance with the License.  You may obtain a
copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing,
software distributed under the License is distributed on an
"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied.  See the License for the specific
language governing permissions and limitations under the
License.
{% endcomment %}
-->
# Development notes for Claude

## Repositories

Morel has implementations in Rust and Java. The repositories are
[morel-rust](https://github.com/hydromatic/morel-rust] and
[morel-java](https://github.com/hydromatic/morel].

A common task is to propagate a change from one repository to the
other.

Read the commit message, the code changes, and especially the test
changes in `src/test/resources/script/*.smli` — those tests are
shared between the two projects, so the morel-rust test files are
the same `.smli` format and often the same content.

### Implementing the feature

Implement the feature in morel-rust. Then enable any disabled
regions by either:

- Removing the surrounding `(* ... *)` block-comment delimiters, or
- Replacing `set("mode","validate")` / `set("mode","evaluate")`
  brackets with ordinary enabled code.

### Verifying

Run `/usr/local/bin/fullMake --no-clean` and confirm it passes
before committing.

### Commit message

Use the original morel-java commit summary as the first line of
the commit message. Append a blank line and then a propagation
line that cites the morel-java issue and commit SHA:

```
Join (hydromatic/morel#72)

Add clauses to `from` to support inner joins. We continue to
allow comma joins, but only up until the first step (`where`,
`join`, `group`, `yield` or `order` keyword). After that,
commas would introduce ambiguity when combined with the
commas in `group` or `compute`.

We will add outer joins (`left`, `right`, `full` keywords)
in a later commit.

Propagates hydromatic/morel#72 commit ab102172
```

If a morel-java commit uses old `[MOREL-NNN]` format, convert it
to the new format `hydromatic/morel#NNN`. For example,
`[MOREL-72] Join` becomes `Join (hydromatic/morel#72)`.

## Regular development

Regular features (originating in morel-rust) use commit message that
references the morel-rust issue (30):

```
Add `banner`, `productName`, `productVersion` properties (#30)

Add three new read-only properties to the Sys structure.

Fixes #30
```
