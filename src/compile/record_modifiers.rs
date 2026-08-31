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

//! Where the fields of a modified record come from.
//!
//! Applying a modifier to a record whose field names are known yields a
//! list of fields, each taking its value from the record the modifier
//! was applied to, from an expression the modifier assigns, or from a
//! field of the modifier's `all` argument.
//!
//! [`crate::compile::type_resolver::TypeResolver`] reads that list to
//! deduce the type of the modified record, and
//! [`crate::compile::resolver::Resolver`] reads it again to build the
//! record. Deriving it twice from the same rules is what keeps the type
//! and the value in step.

use crate::shell::error::Error;
use crate::syntax::ast::{
    Absent, Exists, Expr, Label, LabeledExpr, Modifier, ModifierVerb, Span,
};

/// Where one field of a modified record gets its value.
#[derive(Clone, Debug)]
pub(crate) enum Source {
    /// Field that keeps the value of a field of the record the modifier
    /// was applied to. The name may differ, if the modifier is a
    /// `rename`.
    Kept(String),

    /// Field that is assigned the value of an expression.
    ///
    /// `same_type` says whether the field keeps the type it had. It is
    /// false if the field is being added, because then there is no type
    /// to keep, and if the modifier is `lenient`, which is what
    /// `lenient` means.
    Assigned { expr: Expr, same_type: bool },

    /// Field that is assigned a field of the argument of an `all`
    /// modifier. `same_type` means what it does in [`Source::Assigned`].
    Taken { field: String, same_type: bool },
}

/// Applies `modifier` to a record whose fields are `fields`, returning
/// where each field of the result gets its value.
///
/// Also checks the labels the modifier mentions against the fields it is
/// applied to, and fails if the verb says that a label present (or
/// absent) is an error.
///
/// `all_fields` holds the field names of the modifier's argument, if it
/// is an `all` modifier; otherwise it is `None`.
pub(crate) fn apply(
    modifier: &Modifier,
    fields: &[String],
    all_fields: Option<&[String]>,
) -> Result<Vec<(String, Source)>, Error> {
    match modifier {
        Modifier::Assign(verb, lenient, args) => {
            assign(*verb, *lenient, args, fields)
        }
        Modifier::All(verb, lenient, expr) => assign_all(
            *verb,
            *lenient,
            &expr.span,
            fields,
            all_fields.expect("'all' modifier needs its argument's fields"),
        ),
        Modifier::Remove(verb, labels) => remove(*verb, labels, fields),
        Modifier::Rename(args) => rename(args, fields),
    }
}

/// Applies an `extend` or `replace` modifier, in either case taking each
/// label to whichever of the verb's two cases it falls in: the record has
/// the label already, or it does not.
fn assign(
    verb: ModifierVerb,
    lenient: bool,
    args: &[LabeledExpr],
    fields: &[String],
) -> Result<Vec<(String, Source)>, Error> {
    let mut assigned: Vec<(String, &Expr)> = Vec::new();
    for arg in args {
        let (name, label_span) = label_of(arg)?;
        check_label(verb, fields.contains(&name), &name, &label_span)?;
        if assigned.iter().any(|(n, _)| *n == name) {
            return Err(duplicate_field(&name, &label_span));
        }
        assigned.push((name, &arg.expr));
    }

    let mut sources: Vec<(String, Source)> = Vec::new();
    // Fields the record has: assigned, or kept as they were.
    for field in fields {
        let expr = assigned.iter().find(|(n, _)| n == field).map(|(_, e)| *e);
        match expr {
            Some(expr) if verb.exists() != Exists::Skip => sources.push((
                field.clone(),
                Source::Assigned {
                    expr: expr.clone(),
                    same_type: !lenient,
                },
            )),
            _ => sources.push((field.clone(), Source::Kept(field.clone()))),
        }
    }

    // Labels the record does not have: added, or ignored. An added field
    // has no type to keep, so `lenient` does not arise.
    if verb.absent() == Absent::Add {
        for (name, expr) in &assigned {
            if !fields.contains(name) {
                sources.push((
                    name.clone(),
                    Source::Assigned {
                        expr: (*expr).clone(),
                        same_type: false,
                    },
                ));
            }
        }
    }
    Ok(sources)
}

/// Applies an `extend all` or `replace all` modifier: the same rules as
/// [`assign`], for every field of the modifier's record-valued argument.
fn assign_all(
    verb: ModifierVerb,
    lenient: bool,
    exp_span: &Span,
    fields: &[String],
    all_fields: &[String],
) -> Result<Vec<(String, Source)>, Error> {
    for field in all_fields {
        check_label(verb, fields.contains(field), field, exp_span)?;
    }

    let mut sources: Vec<(String, Source)> = Vec::new();
    for field in fields {
        if !all_fields.contains(field) || verb.exists() == Exists::Skip {
            sources.push((field.clone(), Source::Kept(field.clone())));
        } else {
            sources.push((
                field.clone(),
                Source::Taken {
                    field: field.clone(),
                    same_type: !lenient,
                },
            ));
        }
    }

    if verb.absent() == Absent::Add {
        for field in all_fields {
            if !fields.contains(field) {
                sources.push((
                    field.clone(),
                    Source::Taken {
                        field: field.clone(),
                        same_type: false,
                    },
                ));
            }
        }
    }
    Ok(sources)
}

/// Applies a `rename` modifier. It takes the value of each label on the
/// right, which must exist, and gives it to the label on the left, which
/// must not survive the renaming.
fn rename(
    args: &[(Label, Label)],
    fields: &[String],
) -> Result<Vec<(String, Source)>, Error> {
    let mut renamed: Vec<&str> = Vec::new();
    for (_, source) in args {
        if !fields.contains(&source.name) {
            return Err(field_not_found(&source.name, &source.span));
        }
        if renamed.contains(&source.name.as_str()) {
            return Err(duplicate_field(&source.name, &source.span));
        }
        renamed.push(&source.name);
    }

    let mut sources: Vec<(String, Source)> = Vec::new();
    for field in fields {
        if !renamed.contains(&field.as_str()) {
            sources.push((field.clone(), Source::Kept(field.clone())));
        }
    }
    for (target, source) in args {
        if sources.iter().any(|(name, _)| *name == target.name) {
            return Err(field_exists(&target.name, &target.span));
        }
        sources.push((target.name.clone(), Source::Kept(source.name.clone())));
    }
    Ok(sources)
}

/// Applies a `remove` modifier.
fn remove(
    verb: ModifierVerb,
    labels: &[Label],
    fields: &[String],
) -> Result<Vec<(String, Source)>, Error> {
    let mut removed: Vec<&str> = Vec::new();
    for label in labels {
        if !fields.contains(&label.name) && verb.absent() == Absent::Error {
            return Err(field_not_found(&label.name, &label.span));
        }
        if removed.contains(&label.name.as_str()) {
            return Err(duplicate_field(&label.name, &label.span));
        }
        removed.push(&label.name);
    }
    Ok(fields
        .iter()
        .filter(|f| !removed.contains(&f.as_str()))
        .map(|f| (f.clone(), Source::Kept(f.clone())))
        .collect())
}

/// Returns the label a modifier assigns to, and where it was written.
///
/// The label of `replace a = e` is written; that of `replace a` is the
/// expression's own name.
pub(crate) fn label_of(arg: &LabeledExpr) -> Result<(String, Span), Error> {
    if let Some(label) = &arg.label {
        return Ok((label.name.clone(), label.span.clone()));
    }
    let name = arg.expr.implicit_label_opt().ok_or_else(|| {
        Error::Compile(
            format!("cannot derive label for expression {}", arg.expr),
            arg.expr.span.clone(),
        )
    })?;
    Ok((name, arg.expr.span.clone()))
}

/// Fails if a verb makes it an error that a label is present, or that it
/// is absent.
fn check_label(
    verb: ModifierVerb,
    exists: bool,
    label: &str,
    span: &Span,
) -> Result<(), Error> {
    if exists {
        if verb.exists() == Exists::Error {
            return Err(field_exists(label, span));
        }
    } else if verb.absent() == Absent::Error {
        return Err(field_not_found(label, span));
    }
    Ok(())
}

pub(crate) fn field_not_found(field: &str, span: &Span) -> Error {
    Error::Compile(format!("field '{}' does not exist", field), span.clone())
}

pub(crate) fn field_exists(field: &str, span: &Span) -> Error {
    Error::Compile(format!("field '{}' already exists", field), span.clone())
}

fn duplicate_field(field: &str, span: &Span) -> Error {
    Error::Compile(
        format!("duplicate field '{}' in record", field),
        span.clone(),
    )
}
