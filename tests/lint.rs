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

fn header() -> &'static str {
    r#"// Licensed to Julian Hyde under one or more contributor license
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
"#
}

/// Checks that a file starts with a header comment.
///
/// Appends a warning if not.
fn lint_file(file_name: &str, warnings: &mut Vec<String>) {
    let header = header_for(file_name);
    if header.is_some() {
        let contents = fs::read_to_string(file_name);
        if !contents.unwrap().starts_with(header.unwrap().as_str()) {
            warnings.push(format!(
                "{}:{}: File does not start with a header",
                file_name, 1
            ));
        }
    }
}

/// Returns the appropriate header for a file based on its extension,
/// or `None` if no header is needed.
fn header_for(file_name: &str) -> Option<String> {
    if file_name.ends_with(".rs") {
        Some(header().to_owned())
    } else if file_name.ends_with(".toml") || file_name.ends_with(".gitignore") {
        Some(header().replace("// ", "# ").replace("//\n", "#\n"))
    } else {
        None
    }
}
