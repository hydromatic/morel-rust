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

//! Translates Datalog programs to Morel source code. Mirrors
//! morel-java's `DatalogTranslator` (hydromatic/morel#323).
//!
//! Translation strategy:
//! - Facts-only relations → list literals (`val rel = [...]`).
//! - Recursive rules → `Relational.iterate` with semi-naive evaluation.
//! - Non-recursive rules → `Relational.iterate` with empty seed for
//!   deduplication.
//! - Output → record with output relations, using
//!   `from (x, y) in rel` to convert tuples to records.

use std::collections::HashMap;
use std::fmt::Write;

use crate::datalog::ast::{
    ArithOp, Atom, BodyAtom, CompOp, Declaration, Fact, Program, Rule,
    Statement, Term,
};

/// Translates a parsed Datalog program to Morel source code.
pub fn translate(ast: &Program) -> String {
    let mut out = String::new();

    // Index declarations and group facts/rules by relation, keeping
    // source order.
    let mut decl_map: HashMap<&str, &Declaration> = HashMap::new();
    let mut ordered_decls: Vec<&Declaration> = Vec::new();
    let mut facts_by: HashMap<&str, Vec<&Fact>> = HashMap::new();
    let mut rules_by: HashMap<&str, Vec<&Rule>> = HashMap::new();

    for stmt in &ast.statements {
        match stmt {
            Statement::Declaration(d) => {
                decl_map.insert(d.name.as_str(), d);
                ordered_decls.push(d);
            }
            Statement::Fact(f) => {
                facts_by.entry(f.atom.name.as_str()).or_default().push(f);
            }
            Statement::Rule(r) => {
                rules_by.entry(r.head.name.as_str()).or_default().push(r);
            }
            _ => {}
        }
    }

    let has_definitions = ordered_decls.iter().any(|d| {
        facts_by.get(d.name.as_str()).is_some_and(|v| !v.is_empty())
            || rules_by.get(d.name.as_str()).is_some_and(|v| !v.is_empty())
    });

    if has_definitions {
        out.push_str("let\n");
        for decl in &ordered_decls {
            let facts = facts_by.get(decl.name.as_str());
            let rules = rules_by.get(decl.name.as_str());
            let has_facts = facts.is_some_and(|v| !v.is_empty());
            let has_rules = rules.is_some_and(|v| !v.is_empty());
            if !has_facts && !has_rules {
                continue;
            }
            if !has_rules {
                let _ = write!(out, "  val {} = ", decl.name);
                out.push_str(&translate_facts_to_list(decl, facts.unwrap()));
                out.push('\n');
            } else {
                append_rule_relation(
                    &mut out,
                    decl,
                    facts.map_or(&[][..], Vec::as_slice),
                    rules.unwrap(),
                );
            }
        }
        out.push_str("in\n  ");
    }

    let outputs: Vec<&str> = ast
        .outputs()
        .into_iter()
        .map(|o| o.relation.as_str())
        .collect();

    if outputs.is_empty() {
        out.push_str("()");
    } else {
        out.push('{');
        for (i, rel_name) in outputs.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            let _ = write!(out, "{} = ", rel_name);
            let decl = decl_map.get(rel_name);
            let has_facts =
                facts_by.get(rel_name).is_some_and(|v| !v.is_empty());
            let has_rules =
                rules_by.get(rel_name).is_some_and(|v| !v.is_empty());
            if has_facts || has_rules {
                let arity = decl.map_or(0, |d| d.arity());
                if arity <= 1 {
                    out.push_str(rel_name);
                } else {
                    // Parenthesize when there are multiple outputs to
                    // avoid the `from ...` comma being parsed as a new
                    // source.
                    let multi = outputs.len() > 1;
                    if multi {
                        out.push('(');
                    }
                    out.push_str("from (");
                    for (j, p) in decl.unwrap().params.iter().enumerate() {
                        if j > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(&p.name);
                    }
                    let _ = write!(out, ") in {}", rel_name);
                    if multi {
                        out.push(')');
                    }
                }
            } else {
                out.push_str("[]");
            }
        }
        out.push('}');
    }

    if has_definitions {
        out.push_str("\nend");
    }
    out
}

// -- Per-relation emitters -------------------------------------------

fn append_rule_relation(
    out: &mut String,
    decl: &Declaration,
    facts: &[&Fact],
    rules: &[&Rule],
) {
    let rel_name = decl.name.as_str();
    let recursive = rules.iter().any(|r| is_recursive(r, rel_name));

    let mut seed_parts: Vec<String> = Vec::new();
    let mut step_rules: Vec<&Rule> = Vec::new();

    if !facts.is_empty() {
        seed_parts.push(translate_facts_to_list(decl, facts));
    }

    if recursive {
        for r in rules {
            if !is_recursive(r, rel_name) && is_passthrough(r) {
                if let BodyAtom::Atom { atom, .. } = &r.body[0] {
                    seed_parts.push(atom.name.clone());
                }
            } else {
                step_rules.push(r);
            }
        }
    } else {
        step_rules.extend(rules.iter().copied());
    }

    let seed = if seed_parts.is_empty() {
        "[]".to_string()
    } else {
        seed_parts.join(" @ ")
    };

    let _ = write!(
        out,
        "  val {} =\n    Relational.iterate {}\n",
        rel_name, seed
    );

    let all_var = format!("all{}", capitalize(rel_name));
    let new_var = format!("new{}", capitalize(rel_name));

    if recursive {
        let _ = writeln!(out, "      (fn ({}, {}) =>", all_var, new_var);
    } else {
        out.push_str("      (fn (_, _) =>\n");
    }

    let step_exprs: Vec<String> = step_rules
        .iter()
        .map(|r| {
            rule_to_from(
                r,
                decl,
                if recursive { Some(rel_name) } else { None },
                if recursive { Some(&all_var) } else { None },
                if recursive { Some(&new_var) } else { None },
            )
        })
        .collect();

    if step_exprs.is_empty() {
        out.push_str("        []");
    } else if step_exprs.len() == 1 {
        let _ = write!(out, "        {}", step_exprs[0]);
    } else {
        for (i, e) in step_exprs.iter().enumerate() {
            if i > 0 {
                out.push_str("\n        @ ");
            } else {
                out.push_str("        ");
            }
            let _ = write!(out, "({})", e);
        }
    }
    out.push_str(")\n");
}

/// Translates one rule into a `from ... where ... yield ...` expression.
fn rule_to_from(
    rule: &Rule,
    head_decl: &Declaration,
    recursive_rel: Option<&str>,
    all_rel_var: Option<&str>,
    new_rel_var: Option<&str>,
) -> String {
    let mut from_sources: Vec<String> = Vec::new();
    let mut where_constraints: Vec<String> = Vec::new();

    // Datalog variable name → Morel variable name (insertion-ordered).
    let mut var_map: Vec<(String, String)> = Vec::new();
    let mut used_names: Vec<String> = Vec::new();
    let mut fresh_counter: usize = 0;
    let mut used_new_rel = false;

    let lookup = |key: &str, m: &Vec<(String, String)>| -> Option<String> {
        m.iter().find(|(k, _)| k == key).map(|(_, v)| v.clone())
    };

    for body_atom in &rule.body {
        match body_atom {
            BodyAtom::Comparison { left, op, right } => {
                let l = term_to_expr(left, &var_map, &lookup);
                let r = term_to_expr(right, &var_map, &lookup);
                where_constraints.push(format!(
                    "{} {} {}",
                    l,
                    comp_op_to_morel(*op),
                    r
                ));
            }
            BodyAtom::Atom {
                atom,
                negated: true,
            } => {
                where_constraints.push(format!(
                    "not ({})",
                    build_elem_expr(atom, &var_map, &lookup)
                ));
            }
            BodyAtom::Atom {
                atom,
                negated: false,
            } => {
                let source_name = if recursive_rel == Some(atom.name.as_str()) {
                    if !used_new_rel {
                        used_new_rel = true;
                        new_rel_var.unwrap().to_string()
                    } else {
                        all_rel_var.unwrap().to_string()
                    }
                } else {
                    atom.name.clone()
                };

                let mut pattern_vars: Vec<String> = Vec::new();
                for term in &atom.terms {
                    match term {
                        Term::Variable(name) => {
                            if lookup(name, &var_map).is_none() {
                                let mut morel_var = name.to_lowercase();
                                while used_names.contains(&morel_var) {
                                    morel_var = format!("v{}", fresh_counter);
                                    fresh_counter += 1;
                                }
                                var_map.push((name.clone(), morel_var.clone()));
                                used_names.push(morel_var.clone());
                                pattern_vars.push(morel_var);
                            } else {
                                let existing = lookup(name, &var_map).unwrap();
                                let mut fresh = format!("v{}", fresh_counter);
                                fresh_counter += 1;
                                while used_names.contains(&fresh) {
                                    fresh = format!("v{}", fresh_counter);
                                    fresh_counter += 1;
                                }
                                used_names.push(fresh.clone());
                                pattern_vars.push(fresh.clone());
                                where_constraints
                                    .push(format!("{} = {}", existing, fresh));
                            }
                        }
                        Term::IntConst(_) | Term::StringConst(_) => {
                            let mut fresh = format!("v{}", fresh_counter);
                            fresh_counter += 1;
                            while used_names.contains(&fresh) {
                                fresh = format!("v{}", fresh_counter);
                                fresh_counter += 1;
                            }
                            used_names.push(fresh.clone());
                            pattern_vars.push(fresh.clone());
                            where_constraints.push(format!(
                                "{} = {}",
                                fresh,
                                term_to_morel(term)
                            ));
                        }
                        Term::Arith { .. } => {
                            let mut fresh = format!("v{}", fresh_counter);
                            fresh_counter += 1;
                            while used_names.contains(&fresh) {
                                fresh = format!("v{}", fresh_counter);
                                fresh_counter += 1;
                            }
                            used_names.push(fresh.clone());
                            pattern_vars.push(fresh.clone());
                            where_constraints.push(format!(
                                "{} = {}",
                                fresh,
                                term_to_expr(term, &var_map, &lookup)
                            ));
                        }
                    }
                }

                let pattern = if pattern_vars.is_empty() {
                    "()".to_string()
                } else if pattern_vars.len() == 1 {
                    pattern_vars[0].clone()
                } else {
                    format!("({})", pattern_vars.join(", "))
                };
                from_sources.push(format!("{} in {}", pattern, source_name));
            }
        }
    }

    // Yield expression
    let yield_expr = if head_decl.arity() == 0 {
        "()".to_string()
    } else {
        let parts: Vec<String> = rule
            .head
            .terms
            .iter()
            .map(|t| term_to_expr(t, &var_map, &lookup))
            .collect();
        if parts.len() == 1 {
            parts.into_iter().next().unwrap()
        } else {
            format!("({})", parts.join(", "))
        }
    };

    let mut sb = String::from("from ");
    sb.push_str(&from_sources.join(", "));
    if !where_constraints.is_empty() {
        sb.push_str(" where ");
        sb.push_str(&where_constraints.join(" andalso "));
    }
    let _ = write!(sb, " yield {}", yield_expr);
    sb
}

fn build_elem_expr<F>(
    atom: &Atom,
    var_map: &Vec<(String, String)>,
    lookup: &F,
) -> String
where
    F: Fn(&str, &Vec<(String, String)>) -> Option<String>,
{
    let parts: Vec<String> = atom
        .terms
        .iter()
        .map(|t| term_to_expr(t, var_map, lookup))
        .collect();
    if parts.len() == 1 {
        format!("{} elem {}", parts[0], atom.name)
    } else {
        format!("({}) elem {}", parts.join(", "), atom.name)
    }
}

// -- Predicates and helpers ------------------------------------------

fn is_recursive(rule: &Rule, rel_name: &str) -> bool {
    rule.body.iter().any(|b| match b {
        BodyAtom::Atom { atom, .. } => atom.name == rel_name,
        _ => false,
    })
}

fn is_passthrough(rule: &Rule) -> bool {
    if rule.body.len() != 1 {
        return false;
    }
    let (atom, negated) = match &rule.body[0] {
        BodyAtom::Atom { atom, negated } => (atom, *negated),
        _ => return false,
    };
    if negated {
        return false;
    }
    if atom.terms.len() != rule.head.terms.len() {
        return false;
    }
    for (h, b) in rule.head.terms.iter().zip(atom.terms.iter()) {
        match (h, b) {
            (Term::Variable(hn), Term::Variable(bn)) if hn == bn => {}
            _ => return false,
        }
    }
    true
}

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => c.to_uppercase().chain(chars).collect(),
        None => String::new(),
    }
}

fn term_to_expr<F>(
    term: &Term,
    var_map: &Vec<(String, String)>,
    lookup: &F,
) -> String
where
    F: Fn(&str, &Vec<(String, String)>) -> Option<String>,
{
    match term {
        Term::Variable(name) => {
            lookup(name, var_map).unwrap_or_else(|| name.to_lowercase())
        }
        Term::IntConst(_) | Term::StringConst(_) => term_to_morel(term),
        Term::Arith { left, op, right } => {
            let l = term_to_expr_parens(left, *op, true, var_map, lookup);
            let r = term_to_expr_parens(right, *op, false, var_map, lookup);
            format!("{} {} {}", l, op.symbol(), r)
        }
    }
}

fn term_to_expr_parens<F>(
    term: &Term,
    parent_op: ArithOp,
    is_left: bool,
    var_map: &Vec<(String, String)>,
    lookup: &F,
) -> String
where
    F: Fn(&str, &Vec<(String, String)>) -> Option<String>,
{
    let s = term_to_expr(term, var_map, lookup);
    if let Term::Arith { op: sub_op, .. } = term {
        if is_multiplicative(parent_op) && !is_multiplicative(*sub_op) {
            return format!("({})", s);
        }
        if !is_left
            && (parent_op == ArithOp::Minus || parent_op == ArithOp::Divide)
            && !is_multiplicative(*sub_op)
        {
            return format!("({})", s);
        }
    }
    s
}

fn is_multiplicative(op: ArithOp) -> bool {
    matches!(op, ArithOp::Times | ArithOp::Divide)
}

fn comp_op_to_morel(op: CompOp) -> &'static str {
    match op {
        CompOp::Eq => "=",
        CompOp::Ne => "<>",
        CompOp::Lt => "<",
        CompOp::Le => "<=",
        CompOp::Gt => ">",
        CompOp::Ge => ">=",
    }
}

fn translate_facts_to_list(decl: &Declaration, facts: &[&Fact]) -> String {
    let mut sb = String::from("[");
    for (i, fact) in facts.iter().enumerate() {
        if i > 0 {
            sb.push_str(", ");
        }
        if decl.arity() == 1 {
            sb.push_str(&term_to_morel(&fact.atom.terms[0]));
        } else {
            sb.push('(');
            for (j, t) in fact.atom.terms.iter().enumerate() {
                if j > 0 {
                    sb.push_str(", ");
                }
                sb.push_str(&term_to_morel(t));
            }
            sb.push(')');
        }
    }
    sb.push(']');
    sb
}

fn term_to_morel(term: &Term) -> String {
    match term {
        Term::IntConst(n) => n.to_string(),
        Term::StringConst(s) => {
            let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
            format!("\"{}\"", escaped)
        }
        Term::Variable(name) => format!("\"{}\"", name),
        Term::Arith { .. } => {
            panic!("ArithmeticExpr cannot appear in a fact")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::datalog::parse;

    fn t(src: &str) -> String {
        translate(&parse(src).expect("parse"))
    }

    #[test]
    fn facts_only() {
        let src = ".decl edge(x:int, y:int)\n\
                   edge(1,2). edge(2,3).\n\
                   .output edge";
        assert_eq!(
            t(src),
            "let\n  val edge = [(1, 2), (2, 3)]\nin\n  {edge = from (x, y) in edge}\nend"
        );
    }

    #[test]
    fn transitive_closure() {
        let src = ".decl edge(x:int, y:int)\n\
                   .decl path(x:int, y:int)\n\
                   edge(1,2). edge(2,3).\n\
                   path(X,Y) :- edge(X,Y).\n\
                   path(X,Z) :- path(X,Y), edge(Y,Z).\n\
                   .output path";
        let expected = "let\n  val edge = [(1, 2), (2, 3)]\n  val path =\n    Relational.iterate edge\n      (fn (allPath, newPath) =>\n        from (x, y) in newPath, (v0, z) in edge where y = v0 yield (x, z))\nin\n  {path = from (x, y) in path}\nend";
        assert_eq!(t(src), expected);
    }

    #[test]
    fn arithmetic_in_head_with_grounded_index() {
        // Same shape as morel-java's fact rule.
        let src = ".decl fact(n:int, value:int)\n\
                   fact(0,1).\n\
                   fact(n + 1, value * (n + 1)) :- fact(n, value), n < 10.\n\
                   .output fact";
        let expected = "let\n  val fact =\n    Relational.iterate [(0, 1)]\n      (fn (allFact, newFact) =>\n        from (n, value) in newFact where n < 10 yield (n + 1, value * (n + 1)))\nin\n  {fact = from (n, value) in fact}\nend";
        assert_eq!(t(src), expected);
    }

    #[test]
    fn fib_with_shifted_index() {
        let src = ".decl fib(idx:int, value:int)\n\
                   fib(1,1).\n\
                   fib(2,1).\n\
                   fib(idx + 1, x + y) :- fib(idx, x), fib(idx - 1, y), idx <= 9.\n\
                   .output fib";
        let expected = "let\n  val fib =\n    Relational.iterate [(1, 1), (2, 1)]\n      (fn (allFib, newFib) =>\n        from (idx, x) in newFib, (v0, y) in allFib where v0 = idx - 1 andalso idx <= 9 yield (idx + 1, x + y))\nin\n  {fib = from (idx, value) in fib}\nend";
        assert_eq!(t(src), expected);
    }

    #[test]
    fn empty_relation_with_only_output() {
        let src = ".decl empty(x:int)\n.output empty";
        assert_eq!(t(src), "{empty = []}");
    }

    #[test]
    fn no_output_directive() {
        let src = ".decl edge(x:int, y:int)\n\
                   edge(1,2).";
        assert_eq!(t(src), "let\n  val edge = [(1, 2)]\nin\n  ()\nend");
    }
}
