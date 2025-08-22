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

mod config;
mod error;
pub mod main;
pub mod script_test;

pub use main::Shell;
pub use script_test::ScriptTest;

use error::Error;
use std::io::Read;

/// Result type for shell operations.
pub type ShellResult<T> = Result<T, Error>;

/// Buffer for capturing output that can be flushed.
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
    use std::fs::read_to_string;
    use std::path::Path;

    /// Writes content to a file.
    pub fn write_file<P: AsRef<Path>>(
        path: P,
        content: &str,
    ) -> std::io::Result<()> {
        std::fs::write(path, content)
    }

    /// Compares two files and returns the difference as a string.
    pub fn diff_files<P: AsRef<Path>>(
        ref_file: P,
        out_file: P,
    ) -> std::io::Result<String> {
        let ref_path = ref_file.as_ref();
        let out_path = out_file.as_ref();
        let ref_content = read_to_string(ref_path)?;
        let out_content = read_to_string(out_path)?;

        use similar::TextDiff;
        let text_diff = TextDiff::from_lines(&ref_content, &out_content);
        print!(
            "{}",
            text_diff
                .unified_diff()
                .context_radius(10)
                .header(ref_path.to_str().unwrap(), out_path.to_str().unwrap())
        );

        if ref_content == out_content {
            Ok(String::new())
        } else {
            Ok(format!(
                "Files differ:\nExpected:\n{}\nActual:\n{}",
                ref_content, out_content
            ))
        }
    }

    /// Prefixes each line with "> ", for output in idempotent mode.
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

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_prefix_lines() {
            assert_eq!(prefix_lines("hello\nworld"), "> hello\n> world");
            assert_eq!(prefix_lines("single"), "> single");
        }
    }
}
