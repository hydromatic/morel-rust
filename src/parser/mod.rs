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

use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "src/parser/csv.pest"]
struct CSVParser;

pub fn parse(input: &str) {
    match CSVParser::parse(Rule::field, input) {
        Ok(pairs) => {
            for pair in pairs {
                println!("Parsed field: {:?}", pair.as_str());
            }
        }
        Err(e) => {
            eprintln!("Failed to parse input: {}", e);
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_csv_parser() {
        use super::{CSVParser, Rule};
        use pest::Parser;

        // Test a successful parse
        let result = CSVParser::parse(Rule::field, "123.45");
        assert!(
            result.is_ok(),
            "Expected successful parse, got: {:?}",
            result
        );

        // Test an unsuccessful parse
        let result = CSVParser::parse(Rule::field, "not a number");
        assert!(result.is_err(), "Expected parse to fail, got: {:?}", result);
    }

    #[test]
    fn test_parse() {
        let input = "field1,field2,field3";
        super::parse(input);
    }
}
