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

static RAW_HEADER: &str = r#"^Licensed to Julian Hyde under one or more contributor license
^agreements.  See the NOTICE file distributed with this work
^for additional information regarding copyright ownership.
^Julian Hyde licenses this file to you under the Apache
^License, Version 2.0 (the "License"); you may not use this
^file except in compliance with the License.  You may obtain a
^copy of the License at
^
^http://www.apache.org/licenses/LICENSE-2.0
^
^Unless required by applicable law or agreed to in writing,
^software distributed under the License is distributed on an
^"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
^either express or implied.  See the License for the specific
^language governing permissions and limitations under the
^License.
"#;

fn header_for_suffix(line_prefix: &str) -> String {
    let mut h = String::from(RAW_HEADER);
    h = h.replace("^\n", format!("{}\n", line_prefix.trim_end()).as_str());
    h = h.replace("^", format!("{}", line_prefix).as_str());
    if line_prefix == " * " {
        h = format!("(*\n{}", h);
    }
    h
}

/// Checks that a file starts with a header comment.
///
/// Appends a warning if not.
fn lint_file(file_name: &str, warnings: &mut Vec<String>) {
    let file_type = FileType::for_file(file_name);
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
        });
    }
}

/// Describes whether a file is text, and its required header, if any.
struct FileType {
    header: Option<String>,
    text: bool,
}

impl FileType {
    /// Returns the appropriate header for a file based on its extension,
    /// or `None` if no header is needed.
    fn for_file(file_name: &str) -> Self {
        let suffix = file_name.split('.').last();
        let mut header: Option<String> = None;
        let mut text = false;
        if suffix.is_some() {
            let option = SUFFIX_MAP.get(suffix.unwrap());
            if option.is_some() {
                header = Some(header_for_suffix(option.unwrap()));
                text = true;
            }
        }
        text = text || TYPE_MAP.contains(suffix.unwrap());
        FileType { header, text }
    }
}

static SUFFIX_MAP: Map<&'static str, &'static str> = phf_map! {
    "gitignore" => "# ",
    "rs" => "// ",
    "pest" => "// ",
    "smli" => " * ",
    "toml" => "# ",
    "yml" => "# ",
};

/// File suffixes of files that are considered text files.
static TYPE_MAP: Set<&'static str> =
    phf_set! {"gitignore","rs","pest","toml","md",};
