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
[![Build Status](https://github.com/hydromatic/morel-rust/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/hydromatic/morel-rust/actions?query=branch%3Amain)
<img align="right" alt="Morel mushroom (credit: OldDesignShop.com)"
  src="etc/morel-1200x1200.jpg" with="300" height="300">

# Morel

A functional query language.

### Download and build

```bash
$ git clone git://github.com/hydromatic/morel-rust.git
$ cd morel-rust
$ cargo build; ./target/main
```

### Run the Morel shell

```bash
$ cargo run
morel-rust version 0.2.0 (rust version 1.90.0)
- "Hello, world!";
> val it = "Hello, world!" : string
```

Type control+D to exit the shell.

For quick testing, use the `-c` flag.

```bash
$ cargo run -- -c "1 + 2"
val it = 3 : int

$ cargo run -- -c "from i in [1,2,3] where i > 1"
val it = [2,3] : int list

$ cargo run -- -c 'let fun double x = x * 2 in map double [2,3,4] end'
val it = [4,6,8] : int list
```

## Documentation

* [Morel Rust language reference](docs/reference.md)
* [Morel Java language reference](https://github.com/hydromatic/morel/blob/main/docs/reference.md)
* [Query reference](https://github.com/hydromatic/morel/blob/main/docs/query.md)
* [Change log](CHANGELOG.md)
* Reading [test scripts](tests/script)
  can be instructive; try, for example,
  [built-in.smli](tests/script/built-in.smli)

## More information

* License: <a href="LICENSE">Apache License, Version 2.0</a>
* Author: Julian Hyde (<a href="https://twitter.com/julianhyde">@julianhyde</a>)
* Blog: http://blog.hydromatic.net
* Source code: https://github.com/hydromatic/morel-rust
* Issues: https://github.com/hydromatic/morel-rust/issues
* <a href="CHANGELOG.md">Change log and release notes</a>
