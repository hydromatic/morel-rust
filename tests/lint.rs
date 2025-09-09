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
use regex::Regex;
use std::collections::HashMap;
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
    let mut warnings = Vec::new();
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
    let impl_regex = Regex::new("^ *impl ").unwrap();
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
        let mut in_raw_string = false;
        let mut sort: Option<Sort> = None;
        let mut impl_lines: HashMap<String, usize> = HashMap::new();
        contents.lines().for_each(|l| {
            line += 1;
            if let Some(ref mut s) = sort {
                let l2 = if let Some(erase) = &s.erase {
                    erase.replace_all(l, "").to_string()
                } else {
                    l.to_string()
                };
                if s.until.is_match(l) {
                    sort = None;
                } else if s.where_.is_none()
                    || s.where_.as_ref().unwrap().is_match(l)
                {
                    if !s.previous_lines.is_empty()
                        && l2 < s.previous_lines.last().unwrap().0
                    {
                        let mut target_line = 0;
                        for i in (0..s.previous_lines.len()).rev() {
                            if l2 > s.previous_lines[i].0 {
                                target_line = s.previous_lines[i].1;
                                break;
                            }
                        }
                        warnings.push(format!(
                            "{}:{}: Line out of order; move to line {}",
                            file_name, line, target_line
                        ));
                    }
                    s.previous_lines.push((l2, line));
                }
            }
            if l.ends_with(' ') {
                warnings
                    .push(format!("{}:{}: Trailing spaces", file_name, line));
            }
            if l.contains("r#\"") {
                in_raw_string = true;
            }
            if l.contains("\"#") {
                in_raw_string = false;
            }
            if l.len() > file_type.max_line_length
                && !l.contains("://")
                && !in_raw_string
            {
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
            if impl_regex.is_match(l)
                && let Some(previous_line) =
                    impl_lines.insert(l.to_string(), line)
            {
                warnings.push(format!(
                    "{}:{}: Duplicate `impl` block (previously on line {})",
                    file_name, line, previous_line
                ));
            }
            if l.contains("lint: sort until")
                && !l.contains("\"lint: sort until")
            {
                match Sort::parse(l) {
                    Ok(s) => {
                        sort = Some(s);
                    }
                    Err(()) => {
                        sort = None;
                        warnings.push(format!(
                            "{}:{}: Malformed 'sort until' directive: {}",
                            file_name, line, l
                        ));
                    }
                }
            }
        });
    }
}

struct Sort {
    until: Regex,
    erase: Option<Regex>,
    where_: Option<Regex>,
    previous_lines: Vec<(String, usize)>,
}

impl Sort {
    fn parse(l: &str) -> Result<Sort, ()> {
        let indent = Self::leading_spaces(l);

        if let Some(start) = l.find('\'')
            && let l2 = &l[start + 1..]
            && let Some(end) = l2.find('\'')
        {
            let pattern = &l2[..end];
            let until = match compile_pattern(pattern, &indent) {
                Some(p) => p,
                None => return Err(()),
            };

            let mut erase = None;
            if let Some(start) = l.find(" erase \'")
                && let l2 = &l[start + " erase \'".len()..]
                && let Some(end) = l2.find('\'')
            {
                match compile_pattern(&l2[..end], &indent) {
                    Some(re) => {
                        erase = Some(re);
                    }
                    None => return Err(()),
                }
            }

            let mut where_ = None;
            if let Some(start) = l.find(" where \'")
                && let l2 = &l[start + " where \'".len()..]
                && let Some(end) = l2.find('\'')
            {
                match compile_pattern(&l2[..end], &indent) {
                    Some(re) => {
                        where_ = Some(re);
                    }
                    None => return Err(()),
                }
            }

            Ok(Sort {
                until,
                erase,
                where_,
                previous_lines: Vec::new(),
            })
        } else {
            Err(())
        }
    }

    fn leading_spaces(s: &str) -> String {
        for (i, c) in s.chars().enumerate() {
            if c != ' ' {
                return s[..i].to_string();
            }
        }
        s.to_string()
    }
}

/// Converts a string to a regular expression.
///
/// If "##" occurs in the string, it is replaced with a string that matches the
/// beginning of the line with a number of spaces equal to the current
/// indentation. "#" is replaced by the indentation of the enclosing block. The
/// following applies the sort to the lines "A::B => {" and "A::C => {".
///
/// ```rust
///     match {
///         // sort until '#}' where '##A::'
///         A::B => {
///         },
///         A::C => {
///         },
///     }
/// ```
fn compile_pattern(pattern: &str, mut indent: &str) -> Option<Regex> {
    let mut p = pattern.replace("##", format!("^{}", indent).as_str());
    indent = indent.strip_prefix("    ").unwrap_or(indent);
    p = p.replace("#", format!("^{}", indent).as_str());
    Some(
        Regex::new(p.as_str())
            .expect(format!("bad pattern {}", pattern).as_str()),
    )
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
