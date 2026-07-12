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

## Manually verify a release (for committers)

A few shell behaviors involve an interactive terminal and are not
covered by the automated tests, so check them by hand before publishing
a release. Run the following against the release artifact, or against a
clean build (`cargo build`).

Start the shell, and confirm that it reports the release version:

```bash
$ ./target/debug/morel
morel-rust version 0.2.0 (rust version 1.95.0)
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
