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

//! Analyzer for Datalog programs: declaration / safety / stratification
//! checks. Mirrors morel-java's `DatalogAnalyzer`.
//!
//! The analyzer reports the first error it finds via `DatalogError`.

use std::collections::{HashMap, HashSet};

use crate::datalog::ast::{
    Atom, BodyAtom, DatalogType, Declaration, Fact, Program, Rule, Statement,
    Term,
};
use crate::datalog::error::DatalogError;

/// Runs every analysis pass on `program`.
pub fn analyze(program: &Program) -> Result<(), DatalogError> {
    let decls = program.declarations();
    check_declarations(program, &decls)?;
    check_safety(program)?;
    check_stratification(program)?;
    Ok(())
}

// -- Declaration / arity / type checks -------------------------------

fn check_declarations(
    program: &Program,
    decls: &HashMap<&str, &Declaration>,
) -> Result<(), DatalogError> {
    for input in program.inputs() {
        if !decls.contains_key(input.relation.as_str()) {
            return Err(DatalogError::Analysis(format!(
                "Relation '{}' used in .input but not declared",
                input.relation
            )));
        }
    }
    for stmt in &program.statements {
        match stmt {
            Statement::Fact(fact) => {
                check_atom_declaration(decls, &fact.atom, "fact")?;
                check_fact_constants(fact)?;
            }
            Statement::Rule(rule) => {
                check_atom_declaration(decls, &rule.head, "rule head")?;
                for body_atom in &rule.body {
                    if let BodyAtom::Atom { atom, .. } = body_atom {
                        check_atom_declaration(decls, atom, "rule body")?;
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// A fact may only contain constants (no variables, no arithmetic).
fn check_fact_constants(fact: &Fact) -> Result<(), DatalogError> {
    for term in &fact.atom.terms {
        match term {
            Term::Variable(name) => {
                return Err(DatalogError::Analysis(format!(
                    "Argument in fact is not constant: {}",
                    name
                )));
            }
            Term::Arith { .. } => {
                return Err(DatalogError::Analysis(format!(
                    "Argument in fact is not constant: {}",
                    fmt_term(term)
                )));
            }
            _ => {}
        }
    }
    Ok(())
}

fn check_atom_declaration(
    decls: &HashMap<&str, &Declaration>,
    atom: &Atom,
    context: &str,
) -> Result<(), DatalogError> {
    let decl = match decls.get(atom.name.as_str()) {
        Some(d) => *d,
        None => {
            return Err(DatalogError::Analysis(format!(
                "Relation '{}' used in {} but not declared",
                atom.name, context
            )));
        }
    };
    if atom.arity() != decl.arity() {
        return Err(DatalogError::Analysis(format!(
            "Atom {}/{} does not match declaration {}/{}",
            atom.name,
            atom.arity(),
            decl.name,
            decl.arity()
        )));
    }
    for (i, term) in atom.terms.iter().enumerate() {
        let expected = decl.params[i].ty;
        let actual = match term {
            Term::IntConst(_) => Some(DatalogType::Int),
            Term::StringConst(_) => Some(DatalogType::String),
            _ => None,
        };
        if let Some(actual_ty) = actual
            && actual_ty != expected
        {
            return Err(DatalogError::Analysis(format!(
                "Type mismatch in {} {}(...): expected {}, got {} for parameter {}",
                context, atom.name, expected, actual_ty, decl.params[i].name
            )));
        }
    }
    Ok(())
}

// -- Safety ---------------------------------------------------------

fn check_safety(program: &Program) -> Result<(), DatalogError> {
    for stmt in &program.statements {
        if let Statement::Rule(rule) = stmt {
            check_rule_safety(rule)?;
        }
    }
    Ok(())
}

fn check_rule_safety(rule: &Rule) -> Result<(), DatalogError> {
    // Variables grounded by a positive body atom. Only direct Variable
    // terms ground a name; variables nested inside ArithmeticExpr do
    // not (Souffle semantics, mirrored from morel-java).
    let mut grounded: HashSet<&str> = HashSet::new();
    for body_atom in &rule.body {
        if let BodyAtom::Atom {
            atom,
            negated: false,
        } = body_atom
        {
            for term in &atom.terms {
                if let Term::Variable(name) = term {
                    grounded.insert(name.as_str());
                }
            }
        }
    }

    // Head variables must be grounded.
    for term in &rule.head.terms {
        let mut vars = HashSet::new();
        extract_variables(term, &mut vars);
        for v in vars {
            if !grounded.contains(v) {
                return Err(DatalogError::Analysis(format!(
                    "Rule is unsafe. Variable '{}' in head does not appear in positive body atom",
                    v
                )));
            }
        }
    }

    // Variables appearing only in negated atoms or comparisons must be
    // grounded too.
    for body_atom in &rule.body {
        let (must_check, context) = match body_atom {
            BodyAtom::Atom { negated: true, .. } => (true, "negated atom"),
            BodyAtom::Comparison { .. } => (true, "comparison"),
            _ => (false, ""),
        };
        if !must_check {
            continue;
        }
        let mut vars: HashSet<&str> = HashSet::new();
        match body_atom {
            BodyAtom::Atom { atom, .. } => {
                for term in &atom.terms {
                    extract_variables(term, &mut vars);
                }
            }
            BodyAtom::Comparison { left, right, .. } => {
                extract_variables(left, &mut vars);
                extract_variables(right, &mut vars);
            }
        }
        for v in vars {
            if !grounded.contains(v) {
                return Err(DatalogError::Analysis(format!(
                    "Rule is unsafe. Variable '{}' in {} does not appear in positive body atom",
                    v, context
                )));
            }
        }
    }
    Ok(())
}

fn extract_variables<'a>(term: &'a Term, vars: &mut HashSet<&'a str>) {
    match term {
        Term::Variable(name) => {
            vars.insert(name.as_str());
        }
        Term::Arith { left, right, .. } => {
            extract_variables(left, vars);
            extract_variables(right, vars);
        }
        _ => {}
    }
}

// -- Stratification (no negation cycle) ------------------------------

fn check_stratification(program: &Program) -> Result<(), DatalogError> {
    let mut graph: HashMap<&str, Vec<(&str, bool)>> = HashMap::new();
    for stmt in &program.statements {
        if let Statement::Rule(rule) = stmt {
            let head = rule.head.name.as_str();
            graph.entry(head).or_default();
            for body_atom in &rule.body {
                if let BodyAtom::Atom { atom, negated } = body_atom {
                    graph
                        .entry(head)
                        .or_default()
                        .push((atom.name.as_str(), *negated));
                }
            }
        }
    }
    // Sort the entry points so the error message is deterministic
    // across runs (HashMap iteration is randomized).
    let mut nodes: Vec<&str> = graph.keys().copied().collect();
    nodes.sort();
    for n in nodes {
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        if has_negation_cycle(&graph, n, &mut visited, &mut rec_stack, false) {
            return Err(DatalogError::Analysis(format!(
                "Program is not stratified. Negation cycle detected involving relation: {}",
                n
            )));
        }
    }
    Ok(())
}

fn has_negation_cycle<'a>(
    graph: &HashMap<&'a str, Vec<(&'a str, bool)>>,
    node: &'a str,
    visited: &mut HashSet<&'a str>,
    rec_stack: &mut HashSet<&'a str>,
    seen_negation: bool,
) -> bool {
    if rec_stack.contains(node) {
        return seen_negation;
    }
    if visited.contains(node) {
        return false;
    }
    visited.insert(node);
    rec_stack.insert(node);

    if let Some(deps) = graph.get(node) {
        for (target, negated) in deps {
            let neg_in_path = seen_negation || *negated;
            if has_negation_cycle(
                graph,
                target,
                visited,
                rec_stack,
                neg_in_path,
            ) {
                return true;
            }
        }
    }
    rec_stack.remove(node);
    false
}

// -- Helpers ---------------------------------------------------------

fn fmt_term(t: &Term) -> String {
    match t {
        Term::Variable(s) => s.clone(),
        Term::IntConst(n) => n.to_string(),
        Term::StringConst(s) => format!("\"{}\"", s),
        Term::Arith { left, op, right } => {
            format!("{} {} {}", fmt_term(left), op, fmt_term(right))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datalog::parse;

    fn check(src: &str) -> Result<(), DatalogError> {
        analyze(&parse(src).expect("parse"))
    }

    #[test]
    fn ok_simple() {
        check(".decl edge(x:int, y:int) edge(1,2). edge(2,3).").expect("ok");
    }

    #[test]
    fn arity_mismatch_in_fact() {
        let err = check(".decl edge(x:int, y:int) edge(1,2,3).").unwrap_err();
        assert!(format!("{}", err).contains("does not match declaration"));
    }

    #[test]
    fn undeclared_relation() {
        let err = check(".decl edge(x:int, y:int) path(1,2).").unwrap_err();
        assert!(format!("{}", err).contains("not declared"));
    }

    #[test]
    fn fact_must_be_constant() {
        let err = check(".decl edge(x:int, y:int) edge(X, 2).").unwrap_err();
        assert!(format!("{}", err).contains("not constant"));
    }

    #[test]
    fn type_mismatch_in_fact() {
        let err =
            check(".decl edge(x:int, y:int) edge(\"a\", 2).").unwrap_err();
        assert!(format!("{}", err).contains("Type mismatch"));
    }

    #[test]
    fn unsafe_head_variable() {
        let src = ".decl edge(x:int, y:int) \
                   .decl path(x:int, y:int) \
                   path(X,Y) :- edge(X,Z).";
        let err = check(src).unwrap_err();
        assert!(format!("{}", err).contains("Variable 'Y' in head"));
    }

    #[test]
    fn unsafe_negated_variable() {
        let src = ".decl edge(x:int, y:int) \
                   .decl path(x:int, y:int) \
                   path(X,Y) :- edge(X,Z), !edge(Y,W).";
        let err = check(src).unwrap_err();
        // Either Y or W gets flagged first depending on iteration; both
        // are unsafe.
        let msg = format!("{}", err);
        assert!(msg.contains("Variable 'Y'") || msg.contains("Variable 'W'"));
    }

    #[test]
    fn negation_cycle_is_rejected() {
        let src = ".decl p(x:int) \
                   .decl q(x:int) \
                   p(X) :- q(X). \
                   q(X) :- !p(X), p(X).";
        let err = check(src).unwrap_err();
        assert!(format!("{}", err).contains("not stratified"));
    }

    #[test]
    fn positive_self_recursion_is_ok() {
        // Classic transitive closure — no negation in the cycle.
        let src = ".decl edge(x:int, y:int) \
                   .decl path(x:int, y:int) \
                   path(X,Y) :- edge(X,Y). \
                   path(X,Z) :- path(X,Y), edge(Y,Z).";
        check(src).expect("ok");
    }
}
