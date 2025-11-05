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
wasm-pack build --target web
```

The resulting module can be found under `target/wasm32-unknown-unknown/`.
This will also generate a new directory called `pkg/`
containing some JS glue code that can be imported as an ES6 module.

## Demo

There is a bare-bones demo page showcasing the browser build in action.
After building the Wasm target, start up a web server.
If you just open the demo as a `file://` URI,
you'll probably get a CORS error when it tries to load the module.

```bash
python -m http.server 8000
```

Then, navigate to http://127.0.0.1:8000/web/demo.html in your browser.
