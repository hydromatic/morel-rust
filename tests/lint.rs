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

use phf::{Map, Set, phf_map, phf_set};
use std::fs;

#[test]
fn lint() {
    //
    let mut cmd = std::process::Command::new("git");
    cmd.arg("ls-files");

    let output = cmd.output().expect("Failed to run 'git ls-files' command");

    if !output.status.success() {
        panic!(
            "Clippy found issues:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let mut warnings: Vec<String> = Vec::new();
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .for_each(|l| {
            lint_file(l.trim(), &mut warnings);
        });
    assert!(
        warnings.is_empty(),
        "Linting issues found:\n{}",
        warnings.join("\n")
    );
}

static HEADER_LINES: &[&str] = &[
    "Licensed to Julian Hyde under one or more contributor license",
    "agreements.  See the NOTICE file distributed with this work",
    "for additional information regarding copyright ownership.",
    "Julian Hyde licenses this file to you under the Apache",
    "License, Version 2.0 (the \"License\"); you may not use this",
    "file except in compliance with the License.  You may obtain a",
    "copy of the License at",
    "",
    "http://www.apache.org/licenses/LICENSE-2.0",
    "",
    "Unless required by applicable law or agreed to in writing,",
    "software distributed under the License is distributed on an",
    "\"AS IS\" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,",
    "either express or implied.  See the License for the specific",
    "language governing permissions and limitations under the",
    "License.",
];

/// Comment format information for different file types.
struct CommentFormat {
    line_prefix: &'static str,
    block_start: &'static str,
    block_end: &'static str,
    max_line_length: usize,
}

impl CommentFormat {
    const fn new(
        block_start: &'static str,
        line_prefix: &'static str,
        block_end: &'static str,
        max_line_length: usize,
    ) -> Self {
        Self {
            line_prefix,
            block_start,
            block_end,
            max_line_length,
        }
    }

    /// Generates a header string for this format.
    fn header(&self) -> String {
        let lines = HEADER_LINES.iter().map(|line| {
            if line.is_empty() {
                self.line_prefix.trim_end().to_string()
            } else {
                format!("{}{}", self.line_prefix, line)
            }
        });
        // For .smli files (ML comments), don't include the closing '*)'
        // since files may have additional content
        let content = lines.collect::<Vec<_>>().join("\n");
        if self.line_prefix == " * " {
            format!("{}{}", self.block_start, content)
        } else {
            format!("{}{}{}", self.block_start, content, self.block_end)
        }
    }
}

/// Checks that a file starts with a header comment.
///
/// Appends a warning if not.
fn lint_file(file_name: &str, warnings: &mut Vec<String>) {
    let file_type = FileType::for_file(file_name);
    let vec_space = concat!("{}{}", "vec!", " ");
    let vec_paren = concat!("{}{}", "vec!", "(");
    if file_type.header.is_some() {
        let contents = fs::read_to_string(file_name).unwrap();
        if !contents.starts_with(file_type.header.unwrap().as_str()) {
            warnings.push(format!(
                "{}:{}: File does not start with a header",
                file_name, 1
            ));
        }
    }
    if file_type.text {
        let contents = fs::read_to_string(file_name).unwrap();
        let mut line = 0;
        contents.lines().for_each(|l| {
            line += 1;
            if l.ends_with(' ') {
                warnings
                    .push(format!("{}:{}: Trailing spaces", file_name, line));
            }
            if l.len() > file_type.max_line_length && !l.contains("://") {
                // ignore URLs
                warnings.push(format!(
                    "{}:{}: Line too long ({} > {}): {}",
                    file_name,
                    line,
                    l.len(),
                    file_type.max_line_length,
                    l
                ));
            }
            if l.contains(vec_space) || l.contains(vec_paren) {
                warnings.push(format!(
                    "{}:{}: Use `vec![]` rather than {} or {}",
                    file_name, line, vec_space, vec_paren
                ));
            }
        });
    }
}

/// Describes whether a file is text, and its required header, if any.
struct FileType {
    header: Option<String>,
    text: bool,
    max_line_length: usize,
}

impl FileType {
    /// Returns the appropriate header for a file based on its extension,
    /// or `None` if no header is needed.
    fn for_file(file_name: &str) -> Self {
        let suffix = file_name.split('.').last();
        if suffix.is_some() {
            let option = SUFFIX_MAP.get(suffix.unwrap());
            if option.is_some() {
                let format = option.unwrap();
                return FileType {
                    header: Some(format.header()),
                    text: true,
                    max_line_length: format.max_line_length,
                };
            }
        }
        FileType {
            header: None,
            text: TYPE_MAP.contains(suffix.unwrap()),
            max_line_length: usize::MAX,
        }
    }
}

static SUFFIX_MAP: Map<&'static str, CommentFormat> = phf_map! {
    "gitignore" => CommentFormat::new("", "# ", "", usize::MAX),
    "md" => CommentFormat::new(
        "<!--\n{% comment %}\n",
        "",
        "\n{% endcomment %}\n-->",
        80,
    ),
    "pest" => CommentFormat::new("", "// ", "", usize::MAX),
    "rs" => CommentFormat::new("", "// ", "", 80),
    "smli" => CommentFormat::new("(*\n", " * ", "\n *)", usize::MAX),
    "toml" => CommentFormat::new("", "# ", "", usize::MAX),
    "yml" => CommentFormat::new("", "# ", "", usize::MAX),
};

/// File suffixes of files that are considered text files.
static TYPE_MAP: Set<&'static str> =
    phf_set! {"gitignore","rs","pest","toml","md",};
