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
use std::{fs, iter};

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

/// Standard derive traits in priority order.
/// These traits come first, followed by non-standard traits in
/// alphabetical order.
static STANDARD_DERIVE_TRAITS: &[&str] = &[
    "Copy",
    "Clone",
    "Eq",
    "PartialEq",
    "Ord",
    "PartialOrd",
    "Hash",
    "Debug",
    "Display",
    "Default",
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
    let derive_regex = Regex::new(r"#\[derive\(([^)]+)\)\]").unwrap();
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
        let mut in_pre = false;
        let mut in_raw_string = false;
        let mut sort: Option<Sort> = None;
        let mut impl_lines: HashMap<String, usize> = HashMap::new();
        contents
            .lines()
            .chain(iter::once("")) // add a blank line at the end
            .for_each(|l| {
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
                            for p in s.previous_lines.iter().rev() {
                                target_line = p.1;
                                if l2 > p.0 {
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
                    warnings.push(format!(
                        "{}:{}: Trailing spaces",
                        file_name, line
                    ));
                }
                if l.contains("r#\"") {
                    in_raw_string = true;
                }
                if l.contains("\"#") {
                    in_raw_string = false;
                }
                if l.contains("<pre>") {
                    in_pre = true;
                }
                if l.contains("</pre>") {
                    in_pre = false;
                }
                if l.len() > file_type.max_line_length
                    && !l.contains("://")
                    && !l.starts_with("|") // markdown table
                    && !in_raw_string
                    && !in_pre
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
                    if let Ok(s) = Sort::parse(l) {
                        sort = Some(s);
                    } else {
                        sort = None;
                        warnings.push(format!(
                            "{}:{}: Malformed 'sort until' directive: {}",
                            file_name, line, l
                        ));
                    }
                }
                // Check for alphabetically sorted derive macros
                if let Some(caps) = derive_regex.captures(l) {
                    let traits_str = caps.get(1).unwrap().as_str();
                    let traits: Vec<&str> =
                        traits_str.split(',').map(str::trim).collect();

                    // Map each trait to (priority_index, trait_name)
                    let mut sorted_traits: Vec<&str> = traits.clone();
                    sorted_traits.sort_by_key(|trait_name| {
                        let index = STANDARD_DERIVE_TRAITS
                            .iter()
                            .position(|&s| s == *trait_name)
                            .unwrap_or(usize::MAX);
                        (index, *trait_name)
                    });

                    if traits != sorted_traits {
                        warnings.push(format!(
                            "{}:{}: Derive should be: #[derive({})]",
                            file_name,
                            line,
                            sorted_traits.join(", ")
                        ));
                    }
                }
            });
        if sort.is_some() {
            warnings.push(format!(
                "{}:{}: Unterminated 'sort until' directive",
                file_name, line
            ));
        }
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
        s.chars().take_while(|&c| c == ' ').collect()
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
///         // lint: sort until '#}' where '##A::'
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
            .unwrap_or_else(|_| panic!("bad pattern {}", pattern)),
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
        let suffix = file_name.split('.').next_back();
        if let Some(suffix) = suffix
            && let Some(format) = SUFFIX_MAP.get(suffix)
        {
            return FileType {
                header: Some(format.header()),
                text: true,
                max_line_length: format.max_line_length,
            };
        }
        FileType {
            header: None,
            text: TYPE_MAP.contains(suffix.unwrap()),
            max_line_length: usize::MAX,
        }
    }
}

static SUFFIX_MAP: Map<&'static str, CommentFormat> = phf_map! {
    // lint: sort until '#}' where '##"'
    "gitignore" => CommentFormat::new("", "# ", "", usize::MAX),
    "html" => CommentFormat::new(
        "<!DOCTYPE html>\n<!--\n",
        "",
        "\n-->\n",
        usize::MAX,
    ),
    "md" => CommentFormat::new(
        "<!--\n{% comment %}\n",
        "",
        "\n{% endcomment %}\n-->",
        80,
    ),
    "pest" => CommentFormat::new("", "// ", "", usize::MAX),
    "rs" => CommentFormat::new("", "// ", "", 80),
    "sig" => CommentFormat::new("(*\n", " * ", "\n *)", usize::MAX),
    "smli" => CommentFormat::new("(*\n", " * ", "\n *)", usize::MAX),
    "toml" => CommentFormat::new("", "# ", "", usize::MAX),
    "yml" => CommentFormat::new("", "# ", "", usize::MAX),
};

/// File suffixes of files that are considered text files.
static TYPE_MAP: Set<&'static str> =
    phf_set! {"gitignore","html","rs","pest","toml","md","sig",};

/// Validates that signature files in the lib directory are well-formed and
/// that their value and exception declarations match the corresponding entries
/// in the BuiltInFunction and BuiltInRecord enums.
#[test]
fn test_signatures() {
    use morel::compile::signature_validator::SignatureValidator;

    let validator = SignatureValidator::new("lib");
    validator
        .validate_all()
        .expect("Signature validation failed");

    // Also verify header format using lint_file
    let entries = fs::read_dir("lib")
        .expect("Failed to read lib directory")
        .filter_map(Result::ok)
        .filter(|e| {
            e.path()
                .extension()
                .is_some_and(|ext| ext == "sig" || ext == "sml")
        })
        .collect::<Vec<_>>();

    for entry in entries {
        let path = entry.path();
        let file_name = path.to_str().unwrap();
        lint_file(file_name, &mut Vec::new());
    }
}

/// Validates that for each .smli file in tests/script/, there is a
/// corresponding test method in tests/smile.rs.
#[test]
fn test_smli_coverage() {
    use std::collections::{HashMap, HashSet};
    use std::path::Path;

    // Read all .smli files from tests/script/
    let script_dir = Path::new("tests/script");
    let smli_files: HashSet<String> = fs::read_dir(script_dir)
        .expect("Failed to read tests/script directory")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "smli"))
        .map(|e| e.path().file_stem().unwrap().to_str().unwrap().to_string())
        .collect();

    // Read smile.rs and extract test function names
    let smile_rs = fs::read_to_string("tests/smile.rs")
        .expect("Failed to read tests/smile.rs");

    // Parse test functions and map them to expected .smli file names
    let test_fn_regex =
        Regex::new(r"(?m)^#\[test\]\s+fn ([a-z0-9_]+)\(\)").unwrap();
    let test_functions: HashMap<String, String> = test_fn_regex
        .captures_iter(&smile_rs)
        .filter_map(|cap| {
            let fn_name = cap.get(1)?.as_str();
            // Skip the helper function
            if fn_name == "run_script" {
                return None;
            }
            // Convert function name to expected .smli file name
            // Multi-word file names use kebab-case (hyphens)
            // Special cases: trailing underscores for reserved words
            let smli_name = match fn_name {
                "type_" => "type".to_string(),
                "match_test" => "match".to_string(),
                _ => fn_name.replace('_', "-"),
            };
            Some((smli_name, fn_name.to_string()))
        })
        .collect();

    // Check for .smli files without corresponding test functions
    let mut missing_tests = Vec::new();
    for smli_file in &smli_files {
        if !test_functions.contains_key(smli_file) {
            missing_tests.push(smli_file.clone());
        }
    }

    // Check for test functions without corresponding .smli files
    let mut extra_tests = Vec::new();
    for (smli_name, fn_name) in &test_functions {
        if !smli_files.contains(smli_name) {
            extra_tests.push(format!("{}() -> {}.smli", fn_name, smli_name));
        }
    }

    // Report errors
    if !missing_tests.is_empty() || !extra_tests.is_empty() {
        let mut error_msg = String::new();

        if !missing_tests.is_empty() {
            missing_tests.sort();
            error_msg.push_str(
                "\n.smli files without corresponding test in smile.rs:\n",
            );
            for file in missing_tests {
                let expected_fn = smli_to_fn_name(&file);
                error_msg.push_str(&format!(
                    "  - {}.smli (expected test function: {})\n",
                    file, expected_fn
                ));
            }
        }

        if !extra_tests.is_empty() {
            extra_tests.sort();
            error_msg.push_str(
                "\nTest functions without corresponding .smli file:\n",
            );
            for test in extra_tests {
                error_msg.push_str(&format!("  - {}\n", test));
            }
        }

        panic!("{}", error_msg);
    }
}

/// Converts a .smli file name to the expected test function name.
/// Examples: "type" -> "type_", "match" -> "match_test",
/// "regex-example" -> "regex_example", "fixed-point" -> "fixed_point"
fn smli_to_fn_name(smli_name: &str) -> String {
    match smli_name {
        "type" => "type_".to_string(),
        "match" => "match_test".to_string(),
        _ => smli_name.replace('-', "_"),
    }
}
