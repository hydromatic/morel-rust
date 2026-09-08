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

//! Carrying a `check` condition from one record type to another.
//!
//! A record modifier that renames a field gives a record the condition
//! was not written for, but one it can be rewritten to hold of: where
//! the condition selects a field, the result names that field something
//! else, and the condition is made to say so.
//!
//! Mirrors morel-java's `Conditions`.

use crate::syntax::ast::{
    Decl, DeclKind, Expr, ExprKind, LabeledExpr, Match, Pat, PatField, PatKind,
    ValBind,
};
use std::collections::BTreeMap;

/// Returns `f`, a condition, rewritten to select the fields of a record
/// whose fields have been renamed, or none if it cannot be.
///
/// `kept` maps each field of the record the condition was written for to
/// its name in the new record. A field that is missing from the map is
/// one the modifier removed or assigned to, and a condition that depends
/// on it cannot be carried over: it would no longer typecheck, or it was
/// never shown to hold of the new value.
///
/// Returns none also where the condition uses the record as a whole
/// rather than by selecting fields from it -- a record of another shape
/// is not that record -- and where it is written in a way this cannot
/// walk. Both are answered conservatively: a condition that is dropped
/// claims less, which is sound.
pub(crate) fn rename_selections(
    f: &Expr,
    kept: &BTreeMap<String, String>,
) -> Option<Expr> {
    let ExprKind::Fn(matches) = &f.kind else {
        return None;
    };
    let [m] = matches.as_slice() else {
        return None;
    };
    let PatKind::Identifier(name) = &m.pat.kind else {
        return None;
    };
    let mut r = Renamer {
        name,
        kept,
        bound: Vec::new(),
        ok: true,
    };
    let expr = r.expr(&m.expr);
    if !r.ok {
        return None;
    }
    Some(
        ExprKind::Fn(vec![Match {
            pat: m.pat.clone(),
            expr,
        }])
        .spanned(&f.span),
    )
}

/// Rewrites the selections a condition makes on the record it was
/// written for, tracking the names bound around each one so that a use
/// under a binding of the record's name is left alone: it is not the
/// record.
struct Renamer<'a> {
    name: &'a str,
    kept: &'a BTreeMap<String, String>,
    bound: Vec<String>,
    ok: bool,
}

/// Rebuilds a binary node from rewritten operands.
macro_rules! binary {
    ($self:ident, $span:expr, $ctor:path, $a:expr, $b:expr) => {{
        let a2 = $self.expr($a);
        let b2 = $self.expr($b);
        $ctor(Box::new(a2), Box::new(b2)).spanned($span)
    }};
}

impl Renamer<'_> {
    fn expr(&mut self, e: &Expr) -> Expr {
        let span = &e.span;
        match &e.kind {
            // A selection of the record: the field must be one that
            // survives, and it is renamed to what the result calls it.
            ExprKind::Apply(f, a)
                if matches!(&f.kind, ExprKind::RecordSelector(_))
                    && matches!(&a.kind,
                        ExprKind::Identifier(n) if n == self.name)
                    && !self.bound.iter().any(|b| b == self.name) =>
            {
                let ExprKind::RecordSelector(field) = &f.kind else {
                    unreachable!("guarded above")
                };
                if let Some(field2) = self.kept.get(field) {
                    let f2 = ExprKind::RecordSelector(field2.clone())
                        .spanned(&f.span);
                    ExprKind::Apply(Box::new(f2), a.clone()).spanned(span)
                } else {
                    self.ok = false;
                    e.clone()
                }
            }
            // The record used as a whole: a record of another shape is
            // not that record, so the condition cannot be carried over.
            ExprKind::Identifier(n)
                if n == self.name
                    && !self.bound.iter().any(|b| b == self.name) =>
            {
                self.ok = false;
                e.clone()
            }
            ExprKind::Identifier(_)
            | ExprKind::Literal(_)
            | ExprKind::OpSection(_)
            | ExprKind::RecordSelector(_)
            | ExprKind::SafeRecordSelector(_)
            | ExprKind::Current
            | ExprKind::Ordinal
            | ExprKind::Elements => e.clone(),
            ExprKind::Aggregate(a, b) => {
                binary!(self, span, ExprKind::Aggregate, a, b)
            }
            ExprKind::AndAlso(a, b) => {
                binary!(self, span, ExprKind::AndAlso, a, b)
            }
            ExprKind::Append(a, b) => {
                binary!(self, span, ExprKind::Append, a, b)
            }
            ExprKind::Apply(a, b) => binary!(self, span, ExprKind::Apply, a, b),
            ExprKind::Caret(a, b) => binary!(self, span, ExprKind::Caret, a, b),
            ExprKind::Compose(a, b) => {
                binary!(self, span, ExprKind::Compose, a, b)
            }
            ExprKind::Cons(a, b) => binary!(self, span, ExprKind::Cons, a, b),
            ExprKind::Div(a, b) => binary!(self, span, ExprKind::Div, a, b),
            ExprKind::Divide(a, b) => {
                binary!(self, span, ExprKind::Divide, a, b)
            }
            ExprKind::Elem(a, b) => binary!(self, span, ExprKind::Elem, a, b),
            ExprKind::Equal(a, b) => binary!(self, span, ExprKind::Equal, a, b),
            ExprKind::GreaterThan(a, b) => {
                binary!(self, span, ExprKind::GreaterThan, a, b)
            }
            ExprKind::GreaterThanOrEqual(a, b) => {
                binary!(self, span, ExprKind::GreaterThanOrEqual, a, b)
            }
            ExprKind::Implies(a, b) => {
                binary!(self, span, ExprKind::Implies, a, b)
            }
            ExprKind::LessThan(a, b) => {
                binary!(self, span, ExprKind::LessThan, a, b)
            }
            ExprKind::LessThanOrEqual(a, b) => {
                binary!(self, span, ExprKind::LessThanOrEqual, a, b)
            }
            ExprKind::Minus(a, b) => binary!(self, span, ExprKind::Minus, a, b),
            ExprKind::Mod(a, b) => binary!(self, span, ExprKind::Mod, a, b),
            ExprKind::NotElem(a, b) => {
                binary!(self, span, ExprKind::NotElem, a, b)
            }
            ExprKind::NotEqual(a, b) => {
                binary!(self, span, ExprKind::NotEqual, a, b)
            }
            ExprKind::OrElse(a, b) => {
                binary!(self, span, ExprKind::OrElse, a, b)
            }
            ExprKind::Plus(a, b) => binary!(self, span, ExprKind::Plus, a, b),
            ExprKind::Times(a, b) => binary!(self, span, ExprKind::Times, a, b),
            ExprKind::Negate(a) => {
                let a2 = self.expr(a);
                ExprKind::Negate(Box::new(a2)).spanned(span)
            }
            ExprKind::Raise(a) => {
                let a2 = self.expr(a);
                ExprKind::Raise(Box::new(a2)).spanned(span)
            }
            ExprKind::If(c, t, f) => {
                let c2 = self.expr(c);
                let t2 = self.expr(t);
                let f2 = self.expr(f);
                ExprKind::If(Box::new(c2), Box::new(t2), Box::new(f2))
                    .spanned(span)
            }
            ExprKind::Tuple(es) => {
                let es2 = es.iter().map(|e| self.expr(e)).collect();
                ExprKind::Tuple(es2).spanned(span)
            }
            ExprKind::List(es) => {
                let es2 = es.iter().map(|e| self.expr(e)).collect();
                ExprKind::List(es2).spanned(span)
            }
            ExprKind::Record(base, fields, modifiers) => {
                if base.is_some() || !modifiers.is_empty() {
                    // A modifier reads the record's fields as names of
                    // its own, which this does not follow.
                    self.ok = false;
                    return e.clone();
                }
                let fields2 = fields
                    .iter()
                    .map(|f| LabeledExpr {
                        label: f.label.clone(),
                        expr: self.expr(&f.expr),
                    })
                    .collect();
                ExprKind::Record(None, fields2, Vec::new()).spanned(span)
            }
            ExprKind::Annotated(a, t) => {
                let a2 = self.expr(a);
                ExprKind::Annotated(Box::new(a2), t.clone()).spanned(span)
            }
            ExprKind::Check(a, checks) => {
                let a2 = self.expr(a);
                ExprKind::Check(Box::new(a2), checks.clone()).spanned(span)
            }
            // A match's pattern binds within its expression and nowhere
            // else, so a use of the record's name under one is not the
            // record.
            ExprKind::Fn(matches) => {
                let matches2 = self.matches(matches);
                ExprKind::Fn(matches2).spanned(span)
            }
            ExprKind::Case(a, matches) => {
                let a2 = self.expr(a);
                let matches2 = self.matches(matches);
                ExprKind::Case(Box::new(a2), matches2).spanned(span)
            }
            ExprKind::Let(decls, body) => {
                // The declarations are walked outside the scope they
                // create, which is wrong for a recursive one and wrong
                // in the safe direction: the name is not seen as bound,
                // so a selection on it is rewritten, and a recursive
                // binding of the record's name is rare.
                let decls2 = decls.iter().map(|d| self.decl(d)).collect();
                let mut names = Vec::new();
                for d in decls {
                    decl_names(d, &mut names);
                }
                let depth = self.bound.len();
                self.bound.extend(names);
                let body2 = self.expr(body);
                self.bound.truncate(depth);
                ExprKind::Let(decls2, Box::new(body2)).spanned(span)
            }
            // Anything else is not walked, and a condition written with
            // it is dropped rather than carried over wrongly.
            _ => {
                self.ok = false;
                e.clone()
            }
        }
    }

    fn matches(&mut self, matches: &[Match]) -> Vec<Match> {
        matches
            .iter()
            .map(|m| {
                let mut names = Vec::new();
                pat_names(&m.pat, &mut names);
                let depth = self.bound.len();
                self.bound.extend(names);
                let expr = self.expr(&m.expr);
                self.bound.truncate(depth);
                Match {
                    pat: m.pat.clone(),
                    expr,
                }
            })
            .collect()
    }

    fn decl(&mut self, d: &Decl) -> Decl {
        let DeclKind::Val(rec, inst, binds) = &d.kind else {
            // A declaration that is not a value binding -- a nested
            // type, say -- is not walked, and the condition is dropped.
            self.ok = false;
            return d.clone();
        };
        let binds2 = binds
            .iter()
            .map(|b| ValBind {
                pat: b.pat.clone(),
                type_annotation: b.type_annotation.clone(),
                expr: self.expr(&b.expr),
            })
            .collect();
        Decl {
            kind: DeclKind::Val(*rec, *inst, binds2),
            span: d.span.clone(),
            id: d.id,
        }
    }
}

/// Adds the names a pattern binds.
fn pat_names(pat: &Pat, names: &mut Vec<String>) {
    match &pat.kind {
        PatKind::Identifier(name) => names.push(name.clone()),
        PatKind::As(name, p) => {
            names.push(name.clone());
            pat_names(p, names);
        }
        PatKind::Annotated(p, _) => pat_names(p, names),
        PatKind::Constructor(_, Some(p)) => pat_names(p, names),
        PatKind::Cons(a, b) => {
            pat_names(a, names);
            pat_names(b, names);
        }
        PatKind::List(ps) | PatKind::Tuple(ps) => {
            ps.iter().for_each(|p| pat_names(p, names));
        }
        PatKind::Record(fields, _) => fields.iter().for_each(|f| match f {
            PatField::Labeled(_, _, p) | PatField::Anonymous(_, p) => {
                pat_names(p, names);
            }
        }),
        _ => {}
    }
}

/// Adds the names a declaration binds.
fn decl_names(decl: &Decl, names: &mut Vec<String>) {
    if let DeclKind::Val(_, _, binds) = &decl.kind {
        binds.iter().for_each(|b| pat_names(&b.pat, names));
    }
}
