// Licensed to Julian Hyde under one or more contributor license
// agreements.  See the NOTICE file distributed with this work
// for additional information regarding copyright ownership.
// Julian Hyde licenses this file to you under the Apache
// License, Version 2.0 (the "License"); you may not use this
// file except in compliance with the License.  You may obtain a
// copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.  See the License for the specific
// language governing permissions and limitations under the
// License.

use crate::shell::Shell;
use crate::shell::config::Config;
use wasm_bindgen::prelude::*;

/// A stateful shell that implements a Morel REPL for Wasm.
///
/// # Example
/// ```javascript
/// const shell = new MorelShell();
/// const result = shell.process_statement('val x = 42\n');
/// ```
#[wasm_bindgen]
pub struct MorelShell(Shell);

#[wasm_bindgen]
impl MorelShell {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        // In Wasm, we can't use filesystem operations like current_dir(),
        // so we need `Shell::with_config` instead of `Shell::new`.
        let config = Config::default();

        Self(Shell::with_config(config))
    }

    /// Process a complete Morel statement, which must end in a newline,
    /// returning the result as a string on success,
    /// or an error message on failure.
    #[wasm_bindgen]
    pub fn process_statement(&mut self, input: &str) -> Result<String, String> {
        self.0
            .process_statement(input, None)
            .map_err(|e| e.to_string())
    }
}
