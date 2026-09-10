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

Run `/usr/local/bin/fullMake --no-clean` and confirm it passes.

A propagation must move every changed `.smli` section literally,
adding any that do not yet exist — do not adapt or skip a section
because the implementation is hard. Gate this with
`etc/check-convergence.py HEAD`, which fails if any `.smli` file
diverged further from morel-java. Both it and `fullMake` must pass
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

## Test scripts

The `.smli` format, the harness and the rules by which output is
matched are described in morel-java's `docs/script-format.md`, which is
the contract that all three implementations share.

In expected output, a top-level string value that contains a newline,
has no space before a newline, and is otherwise printable ASCII is
written as a raw string literal, `{|...|}` (or `{id|...|id}` if the
content contains `|}`, the tag being lower-case letters and
underscores), with verbatim content; the `{_|` form, whose tag starts
with an underscore and whose content starts on the next line (the
newline after the fence is not content), is used when the second line
starts with a space. The harness generates these forms, and
`output_matcher` treats them as equivalent to the escaped literal.

## Quick experiments

To run a single Morel expression from the shell, pass `-e` (or
`--eval`, or `--eval=EXPR`) to the binary; the result is printed and
the process exits. Useful when reproducing a bug from a one-liner
without needing a script file:

```
$ ./target/debug/morel -e '1 + 2'
val it = 3 : int
$ ./target/debug/morel --eval='from x in [1,2,3] yield x * 2'
val it = [2,4,6] : int list
```
