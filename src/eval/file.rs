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

//! File-system reader for the progressive `file` built-in.
//!
//! Port of morel-java's `Files.java`. Each [`File`] knows its
//! filesystem path and a [`FileType`] (directory, plain file, or a
//! known data format such as CSV). [`File::expand`] mutates the file's
//! [`FileState`] in place: a not-yet-explored entry becomes either a
//! [`FileState::Directory`] (with the listing of its children) or a
//! [`FileState::Data`] (with the header-derived row type and parsers
//! for each CSV column).
//!
//! The mutation is wired through `RefCell` so a child file can be
//! expanded without taking ownership of (or re-borrowing) its parent
//! directory. Children are held as `Rc<File>`, so expanding a child
//! is automatically visible to anyone holding a reference to it,
//! including the parent's `entries` map.

use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::prop::{Configurable, Prop};
use flate2::read::GzDecoder;
use std::any::Any;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs;
use std::io::{BufRead, BufReader, Read};
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// A file-system entry: a directory, a parseable data file, or
/// something we haven't yet decided about (an unexpanded entry whose
/// type was determined only from its file-name suffix).
#[derive(Debug)]
pub struct File {
    /// Absolute or relative path to this file on disk.
    pub path: PathBuf,
    /// File name with the [`FileType`] suffix stripped — used as the
    /// field name when this file appears in a parent directory's
    /// progressive record type.
    pub base_name: String,
    /// Suffix-derived category (directory / plain / CSV / CSV.gz).
    pub file_type: FileType,
    /// Mutable state. Starts as [`FileState::Unexpanded`]; transitions
    /// to [`FileState::Directory`] or [`FileState::Data`] on the first
    /// call to [`Self::expand`].
    pub state: RefCell<FileState>,
}

/// Discovered structure of a [`File`].
#[derive(Debug)]
pub enum FileState {
    /// Not yet expanded. [`File::expand`] decides what it is.
    Unexpanded,
    /// A directory whose listing has been read into `entries`. Each
    /// child starts [`FileState::Unexpanded`] and is expanded
    /// on-demand as its field is accessed.
    Directory { entries: BTreeMap<Label, Rc<File>> },
    /// A data file (CSV / CSV.gz) whose header has been parsed.
    /// `row_type` is the record type of one row; `field_parsers` says
    /// how to convert each header column into a value of that field's
    /// type, given as `(csv_column_index, parser)` pairs in
    /// `row_type` field order.
    Data {
        row_type: Rc<Type>,
        field_parsers: Vec<(usize, FieldParser)>,
    },
}

/// File category derived from the suffix of the file name.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum FileType {
    /// A directory; expands into a record of its entries.
    Directory,
    /// A plain file with an unrecognised suffix — never expands.
    Plain,
    /// `*.csv` — UTF-8, comma-separated, first row is header.
    Csv,
    /// `*.csv.gz` — gzipped CSV.
    CsvGz,
}

impl FileType {
    /// Returns true when files of this type represent a list of
    /// records (i.e. the progressive record's field type should be
    /// `_ list`, not a bare record).
    pub fn is_list(self) -> bool {
        matches!(self, FileType::Csv | FileType::CsvGz)
    }

    /// Returns the suffix this file type's path ends with, including
    /// the leading `.`, or `""` for directory / plain.
    pub fn suffix(self) -> &'static str {
        match self {
            FileType::Directory | FileType::Plain => "",
            FileType::Csv => ".csv",
            FileType::CsvGz => ".csv.gz",
        }
    }

    /// Suffix-matching order — longest first, so that `*.csv.gz` is
    /// recognised as `CsvGz` rather than `Csv`.
    const INSTANCES: &'static [FileType] = &[FileType::CsvGz, FileType::Csv];

    /// Derives the file type from a path: `Directory` if the path is
    /// a directory, `Csv`/`CsvGz` if the name matches a known suffix,
    /// or `Plain` otherwise.
    pub fn of(path: &Path) -> FileType {
        if path.is_dir() {
            return FileType::Directory;
        }
        let name = path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or_default();
        for &ft in FileType::INSTANCES {
            if name.ends_with(ft.suffix()) {
                return ft;
            }
        }
        FileType::Plain
    }
}

/// Per-column parser, one per non-string scalar primitive we
/// recognise in a CSV header (`name:type` syntax).
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum FieldParser {
    Int,
    Real,
    Bool,
    String,
}

impl FieldParser {
    /// Parses a single CSV cell into the appropriate scalar form,
    /// returned as a Morel runtime [`super::val::Val`] string-or-int-or-… value.
    /// Mirrors morel-java's `Files.parser` plus `unquoteString`.
    pub fn parse(self, s: &str) -> ParsedField {
        match self {
            FieldParser::Int => {
                let v = if s == "NULL" {
                    0
                } else {
                    s.parse().unwrap_or(0)
                };
                ParsedField::Int(v)
            }
            FieldParser::Real => {
                let v: f32 = if s == "NULL" {
                    0.0
                } else {
                    s.parse().unwrap_or(0.0)
                };
                ParsedField::Real(v)
            }
            FieldParser::Bool => {
                let v = matches!(
                    s.to_ascii_lowercase().as_str(),
                    "true" | "t" | "1"
                );
                ParsedField::Bool(v)
            }
            FieldParser::String => ParsedField::String(unquote(s).to_string()),
        }
    }
}

/// Result of parsing one CSV cell. Lives in this module so the
/// runtime conversion to `Val` happens at a higher layer (Stage 3).
#[derive(Clone, PartialEq, Debug)]
pub enum ParsedField {
    Int(i32),
    Real(f32),
    Bool(bool),
    String(String),
}

/// A value that knows its own (potentially progressive) type. Used
/// by the type-resolver to widen progressive record types on
/// demand. The Rust analog of morel-java's `TypedValue`.
pub trait TypedValue {
    /// Current type of this value. May widen over the lifetime of the
    /// value as `discover_field` succeeds.
    fn type_(&self) -> Rc<Type>;

    /// Tries to widen the type to include `field_name`. Returns
    /// `true` if the type widened (so the caller should re-resolve
    /// the field access), `false` if the field is unknown.
    fn discover_field(&self, field_name: &str) -> bool {
        let _ = field_name;
        false
    }

    /// Cast to `Any` so resolver hooks that only know they have a
    /// `Rc<dyn TypedValue>` can downcast to specific implementors
    /// (currently only [`File`]) to extract child values.
    fn as_any(&self) -> &dyn Any;
}

impl TypedValue for File {
    fn type_(&self) -> Rc<Type> {
        match &*self.state.borrow() {
            FileState::Unexpanded => {
                // We know the file's `FileType` (from its suffix)
                // even before we've parsed its contents: a CSV /
                // CSV.gz is a `_ list` (with `_` itself progressive
                // and empty until the header is parsed); anything
                // else acts as a progressive empty record.
                if self.file_type.is_list() {
                    Rc::new(Type::List(Rc::new(Type::Record(
                        true,
                        BTreeMap::new(),
                    ))))
                } else {
                    Rc::new(Type::Record(true, BTreeMap::new()))
                }
            }
            FileState::Directory { entries } => {
                let mut fields: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
                for (label, child) in entries {
                    fields.insert(label.clone(), child.type_());
                }
                Rc::new(Type::Record(true, fields))
            }
            FileState::Data { row_type, .. } => {
                Rc::new(Type::List(Rc::clone(row_type)))
            }
        }
    }

    fn discover_field(&self, field_name: &str) -> bool {
        // Make sure top-level is expanded so we know our children.
        self.expand();
        // Look up the child by name and expand it. If we're not a
        // directory (or the child doesn't exist), no widening.
        let child = match &*self.state.borrow() {
            FileState::Directory { entries } => {
                entries.get(&Label::from(field_name)).cloned()
            }
            _ => None,
        };
        match child {
            Some(c) => {
                let before = matches!(*c.state.borrow(), FileState::Unexpanded);
                c.expand();
                before
            }
            None => false,
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl File {
    /// Constructs an [`Rc<File>`] for the given path. The file's
    /// [`FileType`] is determined from `path`; the state starts
    /// [`FileState::Unexpanded`]. Callers typically follow up with
    /// [`Self::expand`] (or with the type-resolver's progressive
    /// discovery path).
    pub fn create(path: &Path) -> Rc<File> {
        let file_type = FileType::of(path);
        let base_name = base_name(path, file_type);
        Rc::new(File {
            path: path.to_path_buf(),
            base_name,
            file_type,
            state: RefCell::new(FileState::Unexpanded),
        })
    }

    /// If the file is still [`FileState::Unexpanded`], decides what it
    /// is and stores the result. A no-op if already expanded.
    pub fn expand(&self) {
        // Avoid double-expansion. Borrow immutably first so we can
        // short-circuit without taking a mutable borrow that might
        // conflict with re-entrant access.
        if !matches!(*self.state.borrow(), FileState::Unexpanded) {
            return;
        }
        let new_state = match self.file_type {
            FileType::Directory => expand_directory(&self.path),
            FileType::Plain => return,
            FileType::Csv | FileType::CsvGz => {
                match expand_data(&self.path, self.file_type) {
                    Some(s) => s,
                    None => return,
                }
            }
        };
        *self.state.borrow_mut() = new_state;
    }

    /// Reads the file's rows as `Vec<Vec<ParsedField>>`, one inner
    /// vector per row, in field-declaration order. Returns `None` if
    /// the file is not a data file or cannot be opened. Only valid
    /// after [`Self::expand`] has been called.
    pub fn read_rows(&self) -> Option<Vec<Vec<ParsedField>>> {
        let parsers: Vec<(usize, FieldParser)> = match &*self.state.borrow() {
            FileState::Data { field_parsers, .. } => field_parsers.clone(),
            _ => return None,
        };
        let reader = open_reader(&self.path, self.file_type)?;
        let mut rows = Vec::new();
        let mut lines = reader.lines();
        // Skip the header line.
        if lines.next().is_none() {
            return Some(rows);
        }
        for line in lines {
            let line = line.ok()?;
            let cells: Vec<&str> = line.split(',').collect();
            // Reorder cells from CSV-column order into row_type field
            // order: parsers[j] = (i, p) means field j's value comes
            // from CSV column `i`, parsed via `p`.
            let mut values =
                vec![ParsedField::String(String::new()); parsers.len()];
            for (j, (i, parser)) in parsers.iter().enumerate() {
                if let Some(cell) = cells.get(*i) {
                    values[j] = parser.parse(cell);
                }
            }
            rows.push(values);
        }
        Some(rows)
    }
}

/// Returns the [`File`] for this session — the directory configured by
/// the `directory` property, or `"."` if unset. Each call produces a
/// fresh unexpanded file; callers that need expansion to persist
/// across multiple `file` references must hold onto the `Rc` they
/// receive. (Caching the value per session is Stage 3b's job.)
pub fn session_file(session: &Session) -> Rc<File> {
    use crate::shell::prop::PropVal;
    let val = session.config.get(Prop::Directory);
    let path = match val {
        PropVal::PathBuf(p) => (*p).clone(),
        PropVal::String(s) => PathBuf::from(s.as_str()),
        _ => PathBuf::new(),
    };
    let path = if path.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        path
    };
    File::create(&path)
}

/// Converts a [`File`] to its Morel runtime value: a directory becomes
/// a `Val::File`, a data file becomes `Val::List` of record values
/// (one per CSV row), and an unexpanded / plain file becomes
/// `Val::Unit`. Used when projecting a directory entry through field
/// access.
pub fn file_as_val(file: &Rc<File>) -> Val {
    file.expand();
    match &*file.state.borrow() {
        FileState::Directory { .. } | FileState::Unexpanded => {
            Val::File(Rc::clone(file))
        }
        FileState::Data {
            field_parsers,
            row_type,
        } => {
            let rows = file.read_rows().unwrap_or_default();
            let field_count = field_parsers.len();
            let mut vals = Vec::with_capacity(rows.len());
            for row in rows {
                let mut fields = Vec::with_capacity(field_count);
                for v in row {
                    fields.push(match v {
                        ParsedField::Int(n) => Val::Int(n),
                        ParsedField::Real(x) => Val::Real(x),
                        ParsedField::Bool(b) => Val::Bool(b),
                        ParsedField::String(s) => Val::String(s),
                    });
                }
                vals.push(Val::List(fields));
            }
            // `row_type` is unused at runtime — kept only to placate
            // the type-resolver. Silence the unused-binding warning.
            let _ = row_type;
            Val::List(vals)
        }
    }
}

/// Formats a [`File`] for the runtime printer. Directories show
/// as `{name1=...,name2=...}` (mirroring morel-java); data files
/// show as `<relation>`; unexpanded files show as `{}` (a stub).
pub fn display_file(file: &File) -> String {
    match &*file.state.borrow() {
        FileState::Unexpanded => "{}".to_string(),
        FileState::Directory { entries } => {
            let mut s = String::from("{");
            let mut first = true;
            for (label, child) in entries {
                if !first {
                    s.push(',');
                }
                first = false;
                s.push_str(&format!("{}=", label));
                s.push_str(&display_file(child));
            }
            s.push('}');
            s
        }
        FileState::Data { .. } => "<relation>".to_string(),
    }
}

/// Strips a trailing suffix from a path's file name. For directories
/// (suffix `""`) or unknown plain files, the whole file name is the
/// base name.
fn base_name(path: &Path, file_type: FileType) -> String {
    let name = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    let suffix = file_type.suffix();
    if !suffix.is_empty() && name.ends_with(suffix) {
        name[..name.len() - suffix.len()].to_string()
    } else {
        name.to_string()
    }
}

/// Reads the directory listing at `dir` and returns a
/// [`FileState::Directory`] whose `entries` map is keyed on the
/// children's base names. Each child starts unexpanded.
fn expand_directory(dir: &Path) -> FileState {
    let mut entries: BTreeMap<Label, Rc<File>> = BTreeMap::new();
    if let Ok(read_dir) = fs::read_dir(dir) {
        for entry in read_dir.flatten() {
            let child = File::create(&entry.path());
            // Skip plain files (no recognised suffix) — they would
            // never have a useful expansion and just pollute the
            // type's field list.
            if matches!(child.file_type, FileType::Plain) {
                continue;
            }
            let label = Label::from(child.base_name.clone());
            entries.insert(label, child);
        }
    }
    FileState::Directory { entries }
}

/// Reads the header of a CSV / CSV.gz file and returns a
/// [`FileState::Data`] describing the row type. Returns `None` if the
/// file cannot be opened (caller leaves the state `Unexpanded`).
fn expand_data(path: &Path, file_type: FileType) -> Option<FileState> {
    let reader = open_reader(path, file_type)?;
    let mut lines = reader.lines();
    let header = lines.next()?.ok()?;
    if header.is_empty() {
        // Empty header — treat as `unit` row type.
        return Some(FileState::Data {
            row_type: Rc::new(Type::Primitive(PrimitiveType::Unit)),
            field_parsers: vec![],
        });
    }
    // Parse each "name[:type]" header column; default type is string.
    let mut declared: Vec<(String, FieldParser)> = Vec::new();
    for field in header.split(',') {
        let mut split = field.splitn(2, ':');
        let name = split.next().unwrap_or("").to_string();
        let ty = split.next().unwrap_or("string");
        let parser = match ty {
            "bool" => FieldParser::Bool,
            "decimal" | "double" => FieldParser::Real,
            "int" => FieldParser::Int,
            _ => FieldParser::String,
        };
        declared.push((name, parser));
    }
    // Row type: BTreeMap, so fields end up in label order. We
    // remember each field's *CSV column index* so `read_rows` can
    // reorder the cells at parse time.
    let mut field_types: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
    let mut name_to_csv_index: BTreeMap<String, usize> = BTreeMap::new();
    for (i, (name, parser)) in declared.iter().enumerate() {
        field_types
            .insert(Label::from(name.clone()), Rc::new(parser_type(*parser)));
        name_to_csv_index.insert(name.clone(), i);
    }
    let mut field_parsers: Vec<(usize, FieldParser)> = Vec::new();
    for label in field_types.keys() {
        let name = match label {
            Label::String(s) => s.to_string(),
            Label::Ordinal(n) => n.to_string(),
        };
        let csv_index = name_to_csv_index[&name];
        let parser = declared[csv_index].1;
        field_parsers.push((csv_index, parser));
    }
    let row_type = Type::Record(false, field_types);
    Some(FileState::Data {
        row_type: Rc::new(row_type),
        field_parsers,
    })
}

fn parser_type(parser: FieldParser) -> Type {
    match parser {
        FieldParser::Int => Type::Primitive(PrimitiveType::Int),
        FieldParser::Real => Type::Primitive(PrimitiveType::Real),
        FieldParser::Bool => Type::Primitive(PrimitiveType::Bool),
        FieldParser::String => Type::Primitive(PrimitiveType::String),
    }
}

/// Strips a single pair of leading/trailing `'` quotes, if present.
/// `"abc"` and `"'abc, def'"` both round-trip (the latter strips the
/// quotes to `abc, def`).
fn unquote(s: &str) -> &str {
    if s.starts_with('\'') && s.ends_with('\'') && s.len() >= 2 {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

/// Opens `path` for line-by-line reading, transparently decompressing
/// `.csv.gz` files. Returns `None` if the file cannot be opened.
fn open_reader(
    path: &Path,
    file_type: FileType,
) -> Option<BufReader<Box<dyn Read>>> {
    let file = fs::File::open(path).ok()?;
    let inner: Box<dyn Read> = match file_type {
        FileType::CsvGz => Box::new(GzDecoder::new(file)),
        _ => Box::new(file),
    };
    Some(BufReader::new(inner))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn data_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data")
    }

    #[test]
    fn read_csv_header_deduces_types() {
        let path = data_dir().join("scott/depts.csv");
        let file = File::create(&path);
        file.expand();
        match &*file.state.borrow() {
            FileState::Data { row_type, .. } => match row_type.as_ref() {
                Type::Record(false, fields) => {
                    let names: Vec<&str> = fields
                        .keys()
                        .filter_map(|l| match l {
                            Label::String(s) => Some(s.as_str()),
                            _ => None,
                        })
                        .collect();
                    assert_eq!(names, vec!["deptno", "dname", "loc"]);
                }
                other => panic!("unexpected row type: {:?}", other),
            },
            _ => panic!("expected Data state"),
        }
    }

    #[test]
    fn read_csv_gz_decompresses() {
        let path = data_dir().join("scott/emps.csv.gz");
        let file = File::create(&path);
        file.expand();
        assert!(matches!(*file.state.borrow(), FileState::Data { .. }));
        let rows = file.read_rows().unwrap();
        assert!(!rows.is_empty());
    }

    #[test]
    fn directory_lists_csv_children() {
        let path = data_dir().join("scott");
        let dir = File::create(&path);
        dir.expand();
        match &*dir.state.borrow() {
            FileState::Directory { entries } => {
                let names: Vec<String> =
                    entries.keys().map(|l| format!("{}", l)).collect();
                assert!(names.contains(&"depts".to_string()));
                assert!(names.contains(&"emps".to_string()));
            }
            _ => panic!("expected Directory state"),
        }
    }
}

// End file.rs
