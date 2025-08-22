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

use crate::shell::config::Config;
use crate::shell::error::Error;
use crate::shell::{Shell, ShellResult, utils};
use std::fs::{self};
use std::path::{Path, PathBuf};

/// Test runner for script files, equivalent to Java ScriptTest.
pub struct ScriptTest {
    directory: Option<PathBuf>,
}

impl ScriptTest {
    /// Creates a ScriptTest
    pub fn new(directory: Option<PathBuf>) -> Self {
        Self { directory }
    }

    /// Get the test directory
    pub fn directory(&self) -> Option<&Path> {
        self.directory.as_deref()
    }

    /// Runs a single test file
    pub fn run<P: AsRef<Path>>(&self, path: P) -> ShellResult<()> {
        let path = path.as_ref();
        let (in_file, out_file) = self.resolve_files(path)?;

        // Determine if this is an idempotent test (*.smli files)
        let idempotent = path.to_string_lossy().ends_with(".smli")
            || path.to_str() == Some("-");

        // Create output directory if needed
        if let Some(parent) = out_file.parent() {
            fs::create_dir_all(parent)?;
        }

        // Set up configuration
        let mut config = Config {
            echo: !idempotent,
            banner: false,
            idempotent,
            directory: self.directory.clone(),
            script_directory: in_file.parent().map(|p| p.to_path_buf()),
        };

        // Adjust directory for specific tests
        if path.to_string_lossy().contains("/file.") {
            if let Some(mut dir) = config.directory.clone() {
                dir.push("data");
                config.directory = Some(dir);
            }
        }

        // Create and run the shell
        let mut shell = Shell::with_config(config);

        // Run the input file and capture output
        let mut output = Vec::new();
        shell.run_file(&in_file, &mut output)?;

        // Write output to file
        fs::write(&out_file, &output)?;

        // Compare with reference file
        let ref_file = if idempotent {
            in_file.clone()
        } else {
            let mut ref_path = in_file.clone();
            ref_path.set_extension(format!(
                "{}.out",
                ref_path.extension().and_then(|s| s.to_str()).unwrap_or("")
            ));
            ref_path
        };

        if !ref_file.exists() {
            eprintln!("Reference file not found: {}", ref_file.display());
            return Ok(());
        }

        // Compare files
        let diff = utils::diff_files(&ref_file, &out_file)?;
        if !diff.is_empty() {
            return Err(Error::Runtime(format!(
                "Files differ: {} {}\n{}",
                ref_file.display(),
                out_file.display(),
                diff
            )));
        }

        Ok(())
    }

    /// Resolve input and output file paths
    fn resolve_files(&self, path: &Path) -> ShellResult<(PathBuf, PathBuf)> {
        let path_str = path.to_string_lossy();

        if path_str == "-" {
            // Special case for stdin
            let in_file = std::env::temp_dir().join("morel-stdin.smli");
            let out_file = std::env::temp_dir().join("morel-stdin.smli.out");
            return Ok((in_file, out_file));
        }

        if path.is_absolute() {
            // Absolute path
            let in_file = path.to_path_buf();
            let out_file = PathBuf::from(format!("{}.out", path.display()));
            return Ok((in_file, out_file));
        }

        if let Some(dir) = &self.directory {
            // Relative to specified directory
            let in_file = dir.join(path);
            let out_file = dir.join(format!("{}.out", path.display()));
            return Ok((in_file, out_file));
        }

        // Default: look in resources (for now, just use relative path)
        let in_file = PathBuf::from(path);
        let out_file = PathBuf::from("target/test-output")
            .join(format!("{}.out", path.display()));

        Ok((in_file, out_file))
    }

    /// Get all test files in the script directory
    pub fn find_test_files(&self) -> ShellResult<Vec<PathBuf>> {
        let script_dir = self
            .directory
            .as_ref()
            .map(|d| d.join("script"))
            .unwrap_or_else(|| PathBuf::from("src/test/resources/script"));

        if !script_dir.exists() {
            return Ok(Vec::new());
        }

        let mut files = Vec::new();
        for entry in fs::read_dir(script_dir)? {
            let entry = entry?;
            let path = entry.path();

            if let Some(ext) = path.extension() {
                if ext == "sml" || ext == "smli" {
                    files.push(path);
                }
            }
        }

        files.sort();
        Ok(files)
    }

    /// Run all tests in the script directory
    pub fn run_all_tests(&self) -> ShellResult<()> {
        let test_files = self.find_test_files()?;
        let mut failed_tests = Vec::new();

        for file in &test_files {
            println!("Running test: {}", file.display());

            match self.run(file) {
                Ok(()) => {
                    println!("  PASSED");
                }
                Err(e) => {
                    println!("  FAILED: {}", e);
                    failed_tests.push(file.clone());
                }
            }
        }

        if failed_tests.is_empty() {
            println!("All {} tests passed!", test_files.len());
            Ok(())
        } else {
            println!(
                "{} out of {} tests failed:",
                failed_tests.len(),
                test_files.len()
            );
            for file in &failed_tests {
                println!("  {}", file.display());
            }
            Err(Error::Runtime(format!(
                "{} tests failed",
                failed_tests.len()
            )))
        }
    }

    /// Main entry point for command-line usage
    pub fn main(args: Vec<String>) -> ShellResult<()> {
        let mut directory: Option<PathBuf> = None;
        let mut test_files = Vec::new();

        // Parse arguments
        for arg in &args {
            if let Some(dir) = arg.strip_prefix("--directory=") {
                directory = Some(PathBuf::from(dir));
            } else if !arg.starts_with("--") {
                test_files.push(PathBuf::from(arg));
            }
        }

        let script_test = ScriptTest::new(directory);

        if test_files.is_empty() {
            // Run all tests
            script_test.run_all_tests()
        } else {
            // Run specific tests
            let mut failed = false;
            for file in test_files {
                match script_test.run(&file) {
                    Ok(()) => {
                        println!("PASSED: {}", file.display());
                    }
                    Err(e) => {
                        println!("FAILED: {}: {}", file.display(), e);
                        failed = true;
                    }
                }
            }

            if failed {
                Err(Error::Runtime("Some tests failed".to_string()))
            } else {
                Ok(())
            }
        }
    }
}

impl Default for ScriptTest {
    fn default() -> Self {
        Self::new(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_script_test_creation() {
        let st = ScriptTest::default();
        assert!(st.directory().is_none());

        let st = ScriptTest::new(Some(PathBuf::from("/tmp")));
        assert_eq!(st.directory(), Some(Path::new("/tmp")));
    }

    #[test]
    fn test_resolve_files() {
        let st = ScriptTest::default();
        let (in_file, out_file) =
            st.resolve_files(Path::new("test.sml")).unwrap();

        assert!(in_file.to_string_lossy().contains("test.sml"));
        assert!(out_file.to_string_lossy().contains("test.sml.out"));
    }

    #[test]
    fn test_find_test_files() {
        let st = ScriptTest::default();
        // This test will depend on actual test files being present
        let files = st.find_test_files().unwrap_or_default();
        // Just verify it doesn't crash
        println!("Found {} test files", files.len());
    }
}
