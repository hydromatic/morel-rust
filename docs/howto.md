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
# Morel Rust HOWTO

This document describes how to do various things with Morel Rust.

## How to make a release (for committers)

A release is a git tag of the form `vX.Y.Z`; the crate is not
published to [crates.io](https://crates.io).

Write release notes, and add them to [CHANGELOG.md](../CHANGELOG.md),
following the commented-out template at the top of that file. Generate
the list of changes with `relNotes`, giving the previous release as the
starting point:

```bash
WIDTH=78 relNotes v0.2.0
```

It writes one bullet per commit, most recent first, and turns an issue
reference into a link: `#123` is an issue of this project,
`hydromatic/morel#234` one of Morel Java. Organize the bullets into the
sections of the template, keeping them in that order within each
section; copy-edit lightly, mostly adding backticks around identifiers;
and drop the commits that say nothing to a reader, such as `Clippy`, or
one that amends or reverts another.

Update the version number in [Cargo.toml](../Cargo.toml) (the
`version` field, from which the `banner` and `productVersion`
properties are derived), in [README](../README), in
[README.md](../README.md), in this file and in
[reference.md](reference.md); and the copyright date in
[NOTICE](../NOTICE).

Push the branch, and make sure that the
[GitHub build](https://github.com/hydromatic/morel-rust/actions) is
green.

Verify the release by hand (see below), then tag and push:

```bash
git tag v0.2.0
git push origin v0.2.0
```

Add the release notes to the
[github release list](https://github.com/hydromatic/morel-rust/releases),
and announce the release.

## Manually verify a release (for committers)

A few shell behaviors involve an interactive terminal and are not
covered by the automated tests, so check them by hand before publishing
a release. Run the following against the release artifact, or against a
clean build (`cargo build`).

Start the shell, and confirm that it reports the release version:

```bash
$ ./target/debug/morel
morel-rust version x.y.z (rust version 1.93.1)
```

Execute a command, and confirm that the result is printed:

```
- "Hello, world!";
val it = "Hello, world!" : string
```

Quit the shell (type `Ctrl-D`), and confirm that the command was saved
to the history file:

```bash
$ cat ~/.morel/history-rust
```

The file should contain the command you typed. If you have not run the
shell before, confirm that the `~/.morel` directory and the
`history-rust` file were created.

Start the shell again, press the up-arrow key, and confirm that the
previous command is recalled. Execute another command, quit, and confirm
that `~/.morel/history-rust` has grown: the new command is appended, and
the earlier history is preserved.
