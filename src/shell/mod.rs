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

pub mod main;
pub mod script_test;
mod error;
mod config;

pub use main::Shell;
pub use script_test::ScriptTest;

use std::io::{Read, Write};
use error::Error;

/// Result type for shell operations
pub type ShellResult<T> = Result<T, Error>;

/// Buffer for capturing output that can be flushed
pub struct BufferingReader<R: Read> {
    reader: R,
    buffer: String,
}

impl<R: Read> BufferingReader<R> {
    pub fn new(reader: R) -> Self {
        Self {
            reader,
            buffer: String::new(),
        }
    }

    pub fn flush(&mut self) -> String {
        let result = self.buffer.clone();
        self.buffer.clear();
        result
    }
}

impl<R: Read> Read for BufferingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let bytes_read = self.reader.read(buf)?;
        if bytes_read > 0 {
            let s = String::from_utf8_lossy(&buf[..bytes_read]);
            self.buffer.push_str(&s);
        }
        Ok(bytes_read)
    }
}

/// Utility functions for the shell
pub mod utils {
    use std::io::{BufRead, Write};
    use std::path::Path;

    /// Read a file to string with proper error handling
    pub fn read_file_to_string<P: AsRef<Path>>(path: P) -> std::io::Result<String> {
        std::fs::read_to_string(path)
    }

    /// Write content to a file
    pub fn write_file<P: AsRef<Path>>(path: P, content: &str) -> std::io::Result<()> {
        std::fs::write(path, content)
    }

    /// Compare two files and return diff as string (simplified version)
    pub fn diff_files<P: AsRef<Path>>(
        ref_file: P,
        out_file: P,
    ) -> std::io::Result<String> {
        let ref_content = read_file_to_string(ref_file)?;
        let out_content = read_file_to_string(out_file)?;

        if ref_content == out_content {
            Ok(String::new())
        } else {
            Ok(format!(
                "Files differ:\nExpected:\n{}\nActual:\n{}",
                ref_content, out_content
            ))
        }
    }

    /// Prefix each line with "> " for idempotent output
    pub fn prefix_lines(s: &str) -> String {
        let mut result = String::new();
        for line in s.lines() {
            if line.is_empty() {
                result.push_str(">\n");
            } else {
                result.push_str(&format!("> {}\n", line));
            }
        }
        // Remove trailing newline if present
        if result.ends_with('\n') {
            result.pop();
        }
        result
    }

    /// Strip output lines (lines starting with "> ") for idempotent processing
    pub fn strip_out_lines(input: &str) -> String {
        let mut result = String::new();
        let mut in_comment = false;

        for line in input.lines() {
            if line.starts_with("(*") && line.ends_with("*)") {
                // Single line comment, include it
                result.push_str(line);
                result.push('\n');
            } else if line.starts_with("(*") {
                // Start of multi-line comment
                in_comment = true;
                result.push_str(line);
                result.push('\n');
            } else if line.ends_with("*)") && in_comment {
                // End of multi-line comment
                in_comment = false;
                result.push_str(line);
                result.push('\n');
            } else if in_comment {
                // Inside multi-line comment
                result.push_str(line);
                result.push('\n');
            } else if line.starts_with("> ") || line == ">" {
                // Skip output lines
                continue;
            } else {
                // Regular input line
                result.push_str(line);
                result.push('\n');
            }
        }

        // Remove trailing newline if present
        if result.ends_with('\n') {
            result.pop();
        }
        result
    }

    /// Convert filename to test method name (camelCase)
    pub fn to_camel_case(s: &str) -> String {
        let mut result = String::new();
        let mut capitalize_next = false;

        for c in s.chars() {
            match c {
                '_' | '/' | '\\' | '.' => {
                    capitalize_next = true;
                }
                _ => {
                    if capitalize_next {
                        result.extend(c.to_uppercase());
                        capitalize_next = false;
                    } else {
                        result.push(c.to_lowercase().next().unwrap_or(c));
                    }
                }
            }
        }
        result
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_prefix_lines() {
            assert_eq!(prefix_lines("hello\nworld"), "> hello\n> world");
            assert_eq!(prefix_lines("single"), "> single");
            assert_eq!(prefix_lines(""), ">");
        }

        #[test]
        fn test_strip_out_lines() {
            let input = "> output\ninput\n> more output\nmore input";
            let expected = "input\nmore input";
            assert_eq!(strip_out_lines(input), expected);
        }

        #[test]
        fn test_to_camel_case() {
            assert_eq!(to_camel_case("test_script_simple"), "testScriptSimple");
            assert_eq!(to_camel_case("script/simple.sml"), "scriptSimpleSml");
        }
    }
}
