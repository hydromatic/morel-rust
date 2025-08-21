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

extern crate core;
use crate::shell::{ScriptTest, Shell as ShellMain};

mod shell;
mod syntax;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Check if we're running script tests
    if args.len() > 1 && args[1] == "test" {
        let test_args = args[2..].to_vec();
        match ScriptTest::main(test_args) {
            Ok(()) => {
                println!("All tests completed successfully");
                std::process::exit(0);
            }
            Err(e) => {
                eprintln!("Test error: {}", e);
                std::process::exit(1);
            }
        }
    }

    // Check if we're running a specific file
    if args.len() > 1 && args[1] != "--" && !args[1].starts_with("--") {
        let file_path = &args[1];
        let shell_args = args[2..].to_vec();

        let mut main = ShellMain::new(shell_args);
        match main.run_file(file_path, std::io::stdout()) {
            Ok(()) => {
                std::process::exit(0);
            }
            Err(e) => {
                eprintln!("Error running file: {}", e);
                std::process::exit(1);
            }
        }
    }

    let mut x = &args[1..];
    if args.len() > 1 && args[1] == "--" {
        x = &args[2..];
    };
    let mut shell_args = x.to_vec();
    shell_args.insert(0, "--echo".to_string());
    shell_args.insert(0, "--banner".to_string());

    let mut main = ShellMain::new(shell_args);
    match main.run(std::io::stdin(), std::io::stdout()) {
        Ok(()) => {
            println!("Goodbye!");
        }
        Err(e) => {
            eprintln!("Shell error: {}", e);
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_dummy() {
        // Placeholder test to ensure tests still run
        assert_eq!(2 + 2, 4);
    }
}
