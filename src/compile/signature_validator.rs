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

// Used by tests/lint.rs but not by the main shell.
#![allow(dead_code)]

//! Validates signature files against built-in function and record definitions.
//!
//! This module provides the [`SignatureValidator`] which ensures that
//! signature files in the `lib/` directory are well-formed and consistent
//! with the definitions in [`crate::compile::library`].
//!
//! This is the Rust equivalent of Java's `SignatureChecker` class.

use crate::compile::library::BuiltInFunction;
use crate::syntax::ast::{
    DeclKind, SigBind, SpecKind, Statement, StatementKind,
};
use crate::syntax::parser::{ParseError, parse_statement};
use std::collections::HashSet;
use std::error;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use strum::IntoEnumIterator;

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

        let mut all_missing: Vec<(PathBuf, String, String)> = Vec::new();
        for path in entries {
            match self.validate_file(&path) {
                Ok(()) => {}
                Err(ValidationError::SpecMissingInStrum { file, missing }) => {
                    for (s, n) in missing {
                        all_missing.push((file.clone(), s, n));
                    }
                }
                Err(other) => return Err(other),
            }
        }

        if !all_missing.is_empty() {
            return Err(ValidationError::AllSpecsMissingInStrum(all_missing));
        }

        Ok(())
    }

    /// Collects all `.sig` and `.sml` files from the library directory.
    fn collect_signature_files(&self) -> Result<Vec<PathBuf>, ValidationError> {
        let entries = fs::read_dir(&self.lib_dir)
            .map_err(|e| {
                ValidationError::DirectoryReadError(self.lib_dir.clone(), e)
            })?
            .filter_map(Result::ok)
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
    /// Reads the file, then parses it as a Morel statement to confirm
    /// the source is syntactically well-formed (including any attribute
    /// or doc-comment annotations on the contained specs).
    ///
    /// Future enhancements:
    /// - Walk the parse tree to compare each val/exception/datatype
    ///   spec against the strum-tagged `BuiltInFunction` /
    ///   `BuiltInExn` / `BuiltInDatatype` enums.
    /// - Validate that the type signatures match.
    fn validate_file(&self, path: &Path) -> Result<(), ValidationError> {
        let contents = fs::read_to_string(path).map_err(|e| {
            ValidationError::FileReadError(path.to_path_buf(), e)
        })?;
        let stmt = parse_statement(&contents).map_err(|e| {
            ValidationError::ParseError(path.to_path_buf(), Box::new(e))
        })?;
        self.check_strum_consistency(&stmt, path)?;
        Ok(())
    }

    /// Cross-checks each `val name : ...` spec in the parsed signature
    /// against the strum-tagged [`BuiltInFunction`] entries. Reports any
    /// spec name that has no matching `(structure, name)` pair in strum.
    fn check_strum_consistency(
        &self,
        stmt: &Statement,
        path: &Path,
    ) -> Result<(), ValidationError> {
        let Some(structure) = structure_from_sig_file_name(path) else {
            // Unknown file name; no strum coverage expected.
            return Ok(());
        };
        let strum_names = strum_names_for_structure(&structure);
        let binds = collect_sig_binds(stmt);
        let mut missing: Vec<(String, String)> = Vec::new();
        for bind in binds {
            for spec in &bind.specs {
                let sig_names: Vec<String> = match &spec.kind {
                    SpecKind::Val(descs) => {
                        descs.iter().map(|d| d.name.clone()).collect()
                    }
                    _ => Vec::new(),
                };
                for name in sig_names {
                    if strum_names.contains(&name) {
                        continue;
                    }
                    if SKIP_SPEC_PAIRS
                        .contains(&(structure.as_str(), name.as_str()))
                    {
                        continue;
                    }
                    missing.push((structure.clone(), name));
                }
            }
        }
        if !missing.is_empty() {
            return Err(ValidationError::SpecMissingInStrum {
                file: path.to_path_buf(),
                missing,
            });
        }
        Ok(())
    }
}

/// Specific `(structure, name)` pairs to skip in the strum-consistency
/// check. Each entry documents a known gap between the `.sig` source
/// and the `BuiltInFunction` strum entries; entries should be retired
/// as the gaps close.
const SKIP_SPEC_PAIRS: &[(&str, &str)] = &[
    // lint: sort until '#}' where '##\('
    ("Bag", "nth"),            // exposed as List.nth
    ("General", "before"),     // not yet implemented
    ("General", "exnMessage"), // not yet implemented
    ("General", "exnName"),    // not yet implemented
    ("Relational", "only"),    // exposed as Bag.only overload
];

/// Walks a parsed `.sig` statement and returns the contained signature
/// bindings (one per `signature X = sig ... end` inside the file).
fn collect_sig_binds(stmt: &Statement) -> Vec<SigBind> {
    if let StatementKind::Decl(DeclKind::Signature(binds)) = &stmt.kind {
        return binds.clone();
    }
    Vec::new()
}

/// Maps a `.sig` file name (e.g. `bool.sig`, `int.sig`, `string-cvt.sig`)
/// to the corresponding structure name as it appears in
/// `BuiltInFunction`'s `p` strum prop. Returns `None` only if the path
/// has no stem; the kebab-case stem is converted by [`from_kebab`].
fn structure_from_sig_file_name(path: &Path) -> Option<String> {
    let stem = path.file_stem()?.to_str()?;
    let name = from_kebab(stem);
    if name.is_empty() { None } else { Some(name) }
}

/// Title-cases a kebab-cased identifier. Splits at hyphens and
/// upper-cases the first character of each segment, with the single
/// exception of `"ieee"`, which uppercases to `"IEEE"`.
///
/// Examples:
/// - `"ieee-real"` → `"IEEEReal"`
/// - `"list-pair"` → `"ListPair"`
/// - `"string-cvt"` → `"StringCvt"`
/// - `"bool"` → `"Bool"`
fn from_kebab(kebab: &str) -> String {
    let mut s = String::with_capacity(kebab.len());
    for segment in kebab.split('-') {
        if segment.is_empty() {
            continue;
        }
        if segment == "ieee" {
            s.push_str("IEEE");
        } else {
            let mut chars = segment.chars();
            if let Some(c) = chars.next() {
                s.extend(c.to_uppercase());
                s.push_str(chars.as_str());
            }
        }
    }
    s
}

/// Returns the set of `name`s declared in `BuiltInFunction` strum
/// entries whose `p` prop matches the given structure.
fn strum_names_for_structure(structure: &str) -> HashSet<String> {
    BuiltInFunction::iter()
        .filter(|f| f.parent() == Some(structure))
        .map(|f| f.name().to_string())
        .collect()
}

/// Errors that can occur during signature validation.
#[derive(Debug)]
pub enum ValidationError {
    // lint: sort until '#}' where '##[A-Z]'
    /// Aggregated form: all (file, structure, name) tuples missing
    /// from strum across every signature file checked.
    AllSpecsMissingInStrum(Vec<(PathBuf, String, String)>),
    /// The library directory was not found.
    DirectoryNotFound(PathBuf),
    /// Failed to read the directory.
    DirectoryReadError(PathBuf, io::Error),
    /// Failed to read a signature file.
    FileReadError(PathBuf, io::Error),
    /// No signature files were found in the directory.
    NoSignatureFiles(PathBuf),
    /// The path exists but is not a directory.
    NotADirectory(PathBuf),
    /// A signature file did not parse as a Morel statement.
    ParseError(PathBuf, Box<ParseError>),
    /// A `.sig` file declares one or more `val structure.name : ...`
    /// specs for which no matching [`BuiltInFunction`] strum entry
    /// exists.
    SpecMissingInStrum {
        file: PathBuf,
        missing: Vec<(String, String)>,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // lint: sort until '#}' where '##ValidationError::'
            ValidationError::AllSpecsMissingInStrum(entries) => {
                write!(
                    f,
                    "{} spec(s) without matching BuiltInFunction strum \
                     entry across all signature files:",
                    entries.len(),
                )?;
                for (file, structure, name) in entries {
                    write!(
                        f,
                        "\n  {}: val {}.{}",
                        file.display(),
                        structure,
                        name
                    )?;
                }
                Ok(())
            }
            ValidationError::DirectoryNotFound(path) => {
                write!(f, "Library directory not found: {}", path.display())
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
            ValidationError::NoSignatureFiles(path) => {
                write!(f, "No signature files found in: {}", path.display())
            }
            ValidationError::NotADirectory(path) => {
                write!(f, "Path is not a directory: {}", path.display())
            }
            ValidationError::ParseError(path, err) => {
                write!(
                    f,
                    "Failed to parse signature file {}: {}",
                    path.display(),
                    err
                )
            }
            ValidationError::SpecMissingInStrum { file, missing } => {
                write!(
                    f,
                    "{}: {} spec(s) without matching BuiltInFunction \
                     strum entry:",
                    file.display(),
                    missing.len(),
                )?;
                for (structure, name) in missing {
                    write!(f, "\n  val {}.{}", structure, name)?;
                }
                Ok(())
            }
        }
    }
}

impl error::Error for ValidationError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            ValidationError::DirectoryReadError(_, err)
            | ValidationError::FileReadError(_, err) => Some(err),
            ValidationError::ParseError(_, err) => Some(err.as_ref()),
            _ => None,
        }
    }
}
