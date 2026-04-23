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

//! Pattern coverage checker for match expressions.
//!
//! Checks whether match arms are exhaustive (every value is handled) and
//! non-redundant (no arm is covered by earlier arms). Uses a brute-force
//! SAT solver over boolean formulas derived from the pattern structure.
//!
//! Ported from morel-java: `PatternCoverageChecker.java`.

use crate::compile::sat::{Formula, Sat};
use crate::compile::type_resolver::{TypeMap, Warning};
use crate::compile::types::{PrimitiveType, Type};
use crate::shell::error::Error;
use crate::syntax::ast::{
    Decl, DeclKind, Expr, ExprKind, Literal, LiteralKind, Match, Pat, PatKind,
    Span,
};
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Coverage checker
// ---------------------------------------------------------------------------

/// A hierarchical position in a nested pattern, encoded as a list of
/// field indices. E.g., the head of the third cons cell is `[2, 0]`.
type Path = Vec<usize>;

/// Checks coverage of a single match expression.
struct CoverageChecker<'a> {
    type_map: &'a TypeMap,
    sat: Sat,
    /// Maps (path, constructor) → SAT variable.
    slots: HashMap<(Path, String), usize>,
}

impl<'a> CoverageChecker<'a> {
    fn new(type_map: &'a TypeMap) -> Self {
        CoverageChecker {
            type_map,
            sat: Sat::new(),
            slots: HashMap::new(),
        }
    }

    /// Returns the SAT variable for the given constructor at the given path,
    /// creating it (and all sibling variables for the same type) if needed.
    fn get_constructor_var(
        &mut self,
        path: &[usize],
        type_: &Type,
        constructor: &str,
    ) -> Option<usize> {
        let key = (path.to_vec(), constructor.to_string());
        if let Some(&v) = self.slots.get(&key) {
            return Some(v);
        }

        // Create SAT variables for all constructors of this type.
        let names =
            closed_constructors(type_, &self.type_map.datatype_constructors)?;
        let vars: Vec<usize> =
            names.iter().map(|_| self.sat.new_var()).collect();

        // At least one constructor must be active.
        let at_least_one =
            Formula::Or(vars.iter().map(|&v| Formula::Var(v)).collect());
        self.sat.add_constraint(at_least_one);

        // At most one constructor is active (pairwise exclusion).
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let not_both = Formula::Not(Box::new(Formula::And(vec![
                    Formula::Var(vars[i]),
                    Formula::Var(vars[j]),
                ])));
                self.sat.add_constraint(not_both);
            }
        }

        // Store all variables.
        for (name, &var) in names.iter().zip(vars.iter()) {
            self.slots.insert((path.to_vec(), name.clone()), var);
        }

        self.slots.get(&key).copied()
    }

    /// Converts a pattern to a propositional formula that is true when
    /// the input value matches the pattern.
    fn pat_formula(&mut self, pat: &Pat, path: &mut Vec<usize>) -> Formula {
        let type_ = match pat.id.and_then(|id| self.type_map.get_type(id)) {
            Some(t) => *t,
            None => return Formula::True,
        };
        self.pat_formula_typed(pat, path, &type_)
    }

    fn pat_formula_typed(
        &mut self,
        pat: &Pat,
        path: &mut Vec<usize>,
        type_: &Type,
    ) -> Formula {
        match &pat.kind {
            PatKind::Wildcard => Formula::True,

            PatKind::Identifier(_) => Formula::True,

            PatKind::As(_, sub) => self.pat_formula_typed(sub, path, type_),

            PatKind::Annotated(sub, _) => {
                self.pat_formula_typed(sub, path, type_)
            }

            PatKind::Literal(lit) => self.literal_formula(lit, path, type_),

            PatKind::Constructor(name, sub_pat) => {
                let var = match self.get_constructor_var(path, type_, name) {
                    Some(v) => v,
                    None => return Formula::True,
                };
                match sub_pat {
                    None => Formula::Var(var),
                    Some(sub) => {
                        let arg_type = match sub
                            .id
                            .and_then(|id| self.type_map.get_type(id))
                        {
                            Some(t) => *t,
                            None => return Formula::Var(var),
                        };
                        path.push(0);
                        let sub_f =
                            self.pat_formula_typed(sub, path, &arg_type);
                        path.pop();
                        and2(Formula::Var(var), sub_f)
                    }
                }
            }

            PatKind::Tuple(pats) => {
                let types = match type_ {
                    Type::Tuple(ts) => ts.clone(),
                    _ => return Formula::True,
                };
                let mut conjuncts = Vec::new();
                for (i, (sub, elem_type)) in
                    pats.iter().zip(types.iter()).enumerate()
                {
                    path.push(i);
                    let f = self.pat_formula_typed(sub, path, elem_type);
                    path.pop();
                    if !matches!(f, Formula::True) {
                        conjuncts.push(f);
                    }
                }
                if conjuncts.is_empty() {
                    Formula::True
                } else if conjuncts.len() == 1 {
                    conjuncts.remove(0)
                } else {
                    Formula::And(conjuncts)
                }
            }

            PatKind::List(pats) if pats.is_empty() => {
                // [] matches the nil constructor.
                match self.get_constructor_var(path, type_, "nil") {
                    Some(v) => Formula::Var(v),
                    None => Formula::True,
                }
            }

            PatKind::List(pats) => {
                // [a, b, c] desugars to a :: b :: c :: [].
                let elem_type = match type_ {
                    Type::List(t) => *t.clone(),
                    _ => return Formula::True,
                };
                self.list_pats_formula(pats, 0, path, type_, &elem_type)
            }

            PatKind::Cons(head, tail) => {
                // head :: tail
                let elem_type = match type_ {
                    Type::List(t) => *t.clone(),
                    _ => return Formula::True,
                };
                let cons_var =
                    match self.get_constructor_var(path, type_, "cons") {
                        Some(v) => v,
                        None => return Formula::True,
                    };
                path.push(0);
                let head_f = self.pat_formula_typed(head, path, &elem_type);
                path.pop();
                path.push(1);
                let tail_f = self.pat_formula_typed(tail, path, type_);
                path.pop();

                let mut parts = vec![Formula::Var(cons_var)];
                if !matches!(head_f, Formula::True) {
                    parts.push(head_f);
                }
                if !matches!(tail_f, Formula::True) {
                    parts.push(tail_f);
                }
                if parts.len() == 1 {
                    parts.remove(0)
                } else {
                    Formula::And(parts)
                }
            }

            PatKind::Record(_, _) => {
                // Records are product types; treat as exhaustive for now.
                Formula::True
            }
        }
    }

    /// Converts a literal pattern to a formula.
    fn literal_formula(
        &mut self,
        lit: &Literal,
        path: &mut [usize],
        _type_: &Type,
    ) -> Formula {
        match &lit.kind {
            LiteralKind::Bool(b) => {
                let name = if *b { "true" } else { "false" };
                match self.get_constructor_var(
                    path,
                    &Type::Primitive(PrimitiveType::Bool),
                    name,
                ) {
                    Some(v) => Formula::Var(v),
                    None => Formula::True,
                }
            }
            LiteralKind::Unit => {
                // Unit has exactly one value; always exhaustive.
                Formula::True
            }
            _ => {
                // For non-bool, non-unit literals (int, string, real, char):
                // each distinct literal value gets its own SAT variable.
                // There is no "at least one" constraint since these types
                // are infinite (a wildcard is needed for exhaustiveness).
                let key = lit_key(lit);
                let slot_key = (path.to_vec(), key);
                let v = if let Some(&v) = self.slots.get(&slot_key) {
                    v
                } else {
                    let v = self.sat.new_var();
                    self.slots.insert(slot_key, v);
                    v
                };
                Formula::Var(v)
            }
        }
    }

    /// Generates a formula for `pats[start..]` as a desugared cons chain.
    fn list_pats_formula(
        &mut self,
        pats: &[Pat],
        start: usize,
        path: &mut Vec<usize>,
        list_type: &Type,
        elem_type: &Type,
    ) -> Formula {
        if start >= pats.len() {
            // Tail must be nil.
            match self.get_constructor_var(path, list_type, "nil") {
                Some(v) => Formula::Var(v),
                None => Formula::True,
            }
        } else {
            let cons_var =
                match self.get_constructor_var(path, list_type, "cons") {
                    Some(v) => v,
                    None => return Formula::True,
                };
            path.push(0);
            let head_f = self.pat_formula_typed(&pats[start], path, elem_type);
            path.pop();
            path.push(1);
            let tail_f = self.list_pats_formula(
                pats,
                start + 1,
                path,
                list_type,
                elem_type,
            );
            path.pop();

            let mut parts = vec![Formula::Var(cons_var)];
            if !matches!(head_f, Formula::True) {
                parts.push(head_f);
            }
            if !matches!(tail_f, Formula::True) {
                parts.push(tail_f);
            }
            if parts.len() == 1 {
                parts.remove(0)
            } else {
                Formula::And(parts)
            }
        }
    }

    /// Returns the formula for the entire coverage space not matched by
    /// any of `formulas[..limit]`.
    fn not_covered(&self, formulas: &[Formula], limit: usize) -> Formula {
        let not_any: Vec<Formula> = formulas[..limit]
            .iter()
            .map(|f| Formula::Not(Box::new(f.clone())))
            .collect();
        Formula::And(not_any)
    }

    /// Checks coverage of a match arm list given the argument type.
    ///
    /// Returns `(exhaustive, first_redundant_index)`.
    fn check_match(
        &mut self,
        matches: &[Match],
        arg_type: &Type,
    ) -> (bool, Option<usize>) {
        let mut formulas: Vec<Formula> = Vec::new();
        let mut path = Vec::new();

        for m in matches {
            let f = self.pat_formula_typed(&m.pat, &mut path, arg_type);
            formulas.push(f);
        }

        // Check each arm for redundancy: arm i is redundant when
        // fi ∧ ¬f0 ∧ ... ∧ ¬f(i-1) is UNSAT.
        let mut first_redundant: Option<usize> = None;
        for i in 1..formulas.len() {
            let mut parts: Vec<Formula> = formulas[..i]
                .iter()
                .map(|f| Formula::Not(Box::new(f.clone())))
                .collect();
            parts.push(formulas[i].clone());
            let test = Formula::And(parts);
            if !self.sat.is_sat(&test) {
                first_redundant = Some(i);
                break;
            }
        }

        // Check exhaustiveness: ¬f0 ∧ ... ∧ ¬fn is UNSAT ⟹ exhaustive.
        let not_covered = self.not_covered(&formulas, formulas.len());
        let exhaustive = !self.sat.is_sat(&not_covered);

        (exhaustive, first_redundant)
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Returns the constructor names for a closed (finite) type, or `None` for
/// open (infinite) types like `int` and `string`.
fn closed_constructors(
    type_: &Type,
    user_datatypes: &HashMap<String, Vec<String>>,
) -> Option<Vec<String>> {
    match type_ {
        Type::Primitive(PrimitiveType::Bool) => {
            Some(vec!["true".to_string(), "false".to_string()])
        }
        Type::Data(name, _) if name == "order" => Some(vec![
            "LESS".to_string(),
            "EQUAL".to_string(),
            "GREATER".to_string(),
        ]),
        Type::Data(name, _) if name == "option" => {
            Some(vec!["NONE".to_string(), "SOME".to_string()])
        }
        Type::Data(name, _) if name == "either" => {
            Some(vec!["INL".to_string(), "INR".to_string()])
        }
        Type::Data(name, _) => {
            // Look up user-defined datatype constructors.
            user_datatypes.get(name).cloned()
        }
        Type::List(_) => Some(vec!["nil".to_string(), "cons".to_string()]),
        _ => None,
    }
}

/// Builds a unique string key for a literal value.
fn lit_key(lit: &Literal) -> String {
    match &lit.kind {
        LiteralKind::Int(s) => format!("int:{}", s),
        LiteralKind::Real(s) => format!("real:{}", s),
        LiteralKind::String(s) => format!("str:{}", s),
        LiteralKind::Char(s) => format!("char:{}", s),
        _ => format!("lit:{:?}", lit.kind),
    }
}

/// Returns `And([a, b])` unless one of them is `True`, simplifying eagerly.
fn and2(a: Formula, b: Formula) -> Formula {
    match (a, b) {
        (Formula::True, b) => b,
        (a, Formula::True) => a,
        (a, b) => Formula::And(vec![a, b]),
    }
}

// ---------------------------------------------------------------------------
// AST walker
// ---------------------------------------------------------------------------

/// Checks pattern coverage for all match expressions in a declaration.
///
/// Returns warnings (non-exhaustive) or an error (redundant arm).
pub fn check_coverage(
    decl: &Decl,
    type_map: &TypeMap,
) -> Result<Vec<Warning>, Error> {
    let mut warnings = Vec::new();
    visit_decl(decl, type_map, &mut warnings)?;
    Ok(warnings)
}

fn visit_decl(
    decl: &Decl,
    type_map: &TypeMap,
    warnings: &mut Vec<Warning>,
) -> Result<(), Error> {
    match &decl.kind {
        DeclKind::Val(_, _, val_binds) => {
            for vb in val_binds {
                visit_expr(&vb.expr, type_map, warnings)?;
            }
        }
        DeclKind::Fun(_) => {
            // Fun declarations are converted to Val by the time we run;
            // this branch should not be reached.
        }
        _ => {}
    }
    Ok(())
}

fn visit_expr(
    expr: &Expr,
    type_map: &TypeMap,
    warnings: &mut Vec<Warning>,
) -> Result<(), Error> {
    // Pattern-matching expressions: check coverage, then recurse.
    match &expr.kind {
        // lint: sort until '#}' where '##ExprKind::'
        ExprKind::Apply(f, arg) => {
            visit_expr(f, type_map, warnings)?;
            visit_expr(arg, type_map, warnings)?;
        }

        ExprKind::Caret(a, b)
        | ExprKind::Compose(a, b)
        | ExprKind::Elem(a, b)
        | ExprKind::NotElem(a, b)
        | ExprKind::Implies(a, b)
        | ExprKind::Aggregate(a, b) => {
            visit_expr(a, type_map, warnings)?;
            visit_expr(b, type_map, warnings)?;
        }

        ExprKind::Case(scrutinee, matches) => {
            if !matches.is_empty() {
                check_matches(matches, &expr.span, type_map, warnings)?;
            }
            visit_expr(scrutinee, type_map, warnings)?;
            for m in matches {
                visit_expr(&m.expr, type_map, warnings)?;
            }
        }

        ExprKind::Fn(matches) => {
            if !matches.is_empty() {
                check_matches(matches, &expr.span, type_map, warnings)?;
            }
            for m in matches {
                visit_expr(&m.expr, type_map, warnings)?;
            }
        }

        // Relational expressions: ignore for now.
        ExprKind::From(_) | ExprKind::Exists(_) | ExprKind::Forall(_) => {}

        ExprKind::If(cond, then_, else_) => {
            visit_expr(cond, type_map, warnings)?;
            visit_expr(then_, type_map, warnings)?;
            visit_expr(else_, type_map, warnings)?;
        }

        ExprKind::Let(decls, body) => {
            for d in decls {
                visit_decl(d, type_map, warnings)?;
            }
            visit_expr(body, type_map, warnings)?;
        }

        // Leaf expressions: nothing to recurse into.
        ExprKind::Literal(_)
        | ExprKind::Identifier(_)
        | ExprKind::OpSection(_)
        | ExprKind::RecordSelector(_)
        | ExprKind::Current
        | ExprKind::Ordinal
        | ExprKind::Elements => {}

        ExprKind::Negate(e) | ExprKind::Annotated(e, _) => {
            visit_expr(e, type_map, warnings)?;
        }

        ExprKind::Plus(a, b)
        | ExprKind::Minus(a, b)
        | ExprKind::Times(a, b)
        | ExprKind::Divide(a, b)
        | ExprKind::Div(a, b)
        | ExprKind::Mod(a, b)
        | ExprKind::Equal(a, b)
        | ExprKind::NotEqual(a, b)
        | ExprKind::LessThan(a, b)
        | ExprKind::LessThanOrEqual(a, b)
        | ExprKind::GreaterThan(a, b)
        | ExprKind::GreaterThanOrEqual(a, b)
        | ExprKind::AndAlso(a, b)
        | ExprKind::OrElse(a, b)
        | ExprKind::Cons(a, b)
        | ExprKind::Append(a, b) => {
            visit_expr(a, type_map, warnings)?;
            visit_expr(b, type_map, warnings)?;
        }

        ExprKind::Record(base, fields) => {
            if let Some(b) = base {
                visit_expr(b, type_map, warnings)?;
            }
            for field in fields {
                visit_expr(&field.expr, type_map, warnings)?;
            }
        }

        ExprKind::Tuple(elems) | ExprKind::List(elems) => {
            for e in elems {
                visit_expr(e, type_map, warnings)?;
            }
        }
    }
    Ok(())
}

/// Checks coverage of a match arm list and accumulates results.
fn check_matches(
    matches: &[Match],
    expr_span: &Span,
    type_map: &TypeMap,
    warnings: &mut Vec<Warning>,
) -> Result<(), Error> {
    // Determine the argument type from the first pattern's type.
    let arg_type = match matches[0].pat.id.and_then(|id| type_map.get_type(id))
    {
        Some(t) => *t,
        None => return Ok(()), // Unknown type; skip.
    };

    let mut checker = CoverageChecker::new(type_map);
    let (exhaustive, first_redundant) = checker.check_match(matches, &arg_type);

    if let Some(idx) = first_redundant {
        let m = &matches[idx];
        let span = m.pat.span.union(&m.expr.span);
        let message = if !exhaustive {
            "match redundant and nonexhaustive"
        } else {
            "match redundant"
        }
        .to_string();
        return Err(Error::Compile(message, span));
    }

    if !exhaustive {
        warnings.push(Warning {
            span: expr_span.clone(),
            message: "match nonexhaustive".to_string(),
        });
    }

    Ok(())
}
