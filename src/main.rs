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
use crate::parser::ast::Ast;
use crate::parser::parser::parse;

mod parser;

fn main() {
    println!("Morel Rust Parser");
    println!("A Standard ML interpreter with relational extensions");

    // Test string and char literals to verify our format! fix
    let test_cases = vec![
        ("42", "Integer"),
        ("\"hello world\"", "String"),
        ("#\"c\"", "Character"),
        ("true", "Boolean"),
        ("()", "Unit"),
    ];

    for (example, description) in test_cases {
        println!("\nParsing {} example: {}", description, example);

        match std::panic::catch_unwind(|| parse(example)) {
            Ok(node) => {
                let mut output = String::new();
                node.unparse(&mut output);
                println!("Result: {}", output);
            }
            Err(_) => {
                println!("Parse error");
            }
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
