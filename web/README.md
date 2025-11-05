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
# Morel WebAssembly Build

This project can be compiled to WebAssembly for use in the browser
using [`wasm-pack`](https://github.com/drager/wasm-pack).

## Build

If you don't already have `wasm-pack` installed:

```bash
cargo install wasm-pack
```

To build the Wasm module:

```bash
wasm-pack build --target web --out-dir web/pkg
```

The resulting module can be found under `target/wasm32-unknown-unknown/`.
This will also generate a new subdirectory of `web` called `pkg`
containing some JS glue code that can be imported as an ES6 module.

## Demo

There is a bare-bones demo page showcasing the browser build in
action.  After building the Wasm target, start up a web server.  If
you just open the demo as a `file://` URI, you'll probably get a
[CORS](https://en.wikipedia.org/wiki/Cross-origin_resource_sharing)
error when it tries to load the module.

```bash
$ cd web
$ python -m http.server 8000
```

Then, navigate to http://127.0.0.1:8000/demo.html in your browser.
