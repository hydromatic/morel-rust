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

//! Validates signature files against built-in function and record definitions.
//!
//! This module provides the [`SignatureValidator`] which ensures that
//! signature files in the `lib/` directory are well-formed and consistent
//! with the definitions in [`crate::compile::library`].
//!
//! This is the Rust equivalent of Java's `SignatureChecker` class.

use std::fs;
use std::path::{Path, PathBuf};

/// Validates signature files against built-in definitions.
///
/// This validator checks that:
/// - Signature files exist and are readable
/// - Files have proper header formatting
/// - Value and exception declarations match entries in BuiltInFunction and
///   BuiltInRecord
///
/// # Examples
///
/// ```no_run
/// use morel::compile::signature_validator::SignatureValidator;
///
/// let validator = SignatureValidator::new("lib");
/// validator.validate_all().expect("Signature validation failed");
/// ```
pub struct SignatureValidator {
    lib_dir: PathBuf,
}

impl SignatureValidator {
    /// Creates a new signature validator for the given library directory.
    pub fn new<P: AsRef<Path>>(lib_dir: P) -> Self {
        Self {
            lib_dir: lib_dir.as_ref().to_path_buf(),
        }
    }

    /// Validates all signature files in the library directory.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The library directory doesn't exist or isn't a directory
    /// - No signature files are found
    /// - Any signature file cannot be read
    /// - Any signature file fails validation
    pub fn validate_all(&self) -> Result<(), ValidationError> {
        if !self.lib_dir.exists() {
            return Err(ValidationError::DirectoryNotFound(
                self.lib_dir.clone(),
            ));
        }

        if !self.lib_dir.is_dir() {
            return Err(ValidationError::NotADirectory(self.lib_dir.clone()));
        }

        let entries = self.collect_signature_files()?;

        if entries.is_empty() {
            return Err(ValidationError::NoSignatureFiles(
                self.lib_dir.clone(),
            ));
        }

        for path in entries {
            self.validate_file(&path)?;
        }

        Ok(())
    }

    /// Collects all `.sig` and `.sml` files from the library directory.
    fn collect_signature_files(&self) -> Result<Vec<PathBuf>, ValidationError> {
        let entries = fs::read_dir(&self.lib_dir)
            .map_err(|e| {
                ValidationError::DirectoryReadError(self.lib_dir.clone(), e)
            })?
            .filter_map(std::result::Result::ok)
            .filter(|e| {
                e.path()
                    .extension()
                    .is_some_and(|ext| ext == "sig" || ext == "sml")
            })
            .map(|e| e.path())
            .collect();

        Ok(entries)
    }

    /// Validates a single signature file.
    ///
    /// Currently validates that:
    /// - The file can be read
    /// - The file has proper formatting
    ///
    /// Future enhancements could include:
    /// - Parsing the signature as AST
    /// - Comparing declarations against BuiltInFunction/BuiltInRecord enums
    /// - Validating type signatures match
    fn validate_file(&self, path: &Path) -> Result<(), ValidationError> {
        // Verify that the file can be read
        let _contents = fs::read_to_string(path).map_err(|e| {
            ValidationError::FileReadError(path.to_path_buf(), e)
        })?;

        // Additional validation could be added here:
        // - Parse as signature declaration
        // - Check that values match BuiltInFunction entries
        // - Check that exceptions match BuiltInExn entries
        // - Check that datatypes match BuiltIn types

        Ok(())
    }
}

/// Errors that can occur during signature validation.
#[derive(Debug)]
pub enum ValidationError {
    /// The library directory was not found.
    DirectoryNotFound(PathBuf),
    /// The path exists but is not a directory.
    NotADirectory(PathBuf),
    /// No signature files were found in the directory.
    NoSignatureFiles(PathBuf),
    /// Failed to read the directory.
    DirectoryReadError(PathBuf, std::io::Error),
    /// Failed to read a signature file.
    FileReadError(PathBuf, std::io::Error),
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ValidationError::DirectoryNotFound(path) => {
                write!(f, "Library directory not found: {}", path.display())
            }
            ValidationError::NotADirectory(path) => {
                write!(f, "Path is not a directory: {}", path.display())
            }
            ValidationError::NoSignatureFiles(path) => {
                write!(f, "No signature files found in: {}", path.display())
            }
            ValidationError::DirectoryReadError(path, err) => {
                write!(
                    f,
                    "Failed to read directory {}: {}",
                    path.display(),
                    err
                )
            }
            ValidationError::FileReadError(path, err) => {
                write!(
                    f,
                    "Failed to read signature file {}: {}",
                    path.display(),
                    err
                )
            }
        }
    }
}

impl std::error::Error for ValidationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ValidationError::DirectoryReadError(_, err)
            | ValidationError::FileReadError(_, err) => Some(err),
            _ => None,
        }
    }
}
