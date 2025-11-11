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

//! Builds and optimizes query expressions (`from`/`where`/`yield`).
//!
//! The `FromBuilder` simplifies query patterns such as:
//! - Converting "from v in list" to just "list" (in `build_simplify`)
//! - Removing "where true" steps
//! - Removing empty "order" steps
//! - Removing trivial yields like "from v in list where condition yield v"
//! - Inlining nested from expressions

use crate::compile::core::{Binding, Expr, Pat, Step, StepEnv, StepKind};
use crate::compile::types::Type;
use crate::eval::val::Val;
use crate::shell::error::Error;
use std::fmt;

/// Checks if the type is a list type.
fn is_list_type(type_: &Type) -> bool {
    matches!(type_, Type::List(_))
}

/// Classification of tuple types for yield optimization.
#[derive(Eq, PartialEq, Debug)]
enum TupleType {
    /// A tuple whose expressions are the current fields and whose labels are
    /// the same as the right, e.g. "{deptno = deptno, dname = dname}".
    Identity,
    /// A tuple whose right side are the current fields, e.g.
    /// "{a = deptno, b = dname}".
    Rename,
    /// Any other tuple, e.g. "{a = deptno + 1, dname = dname}",
    /// "{deptno = deptno}" (too few fields).
    Other,
}

/// Returns whether the tuple is something like "{i = i, j = j}".
fn is_trivial(tuple: &Expr, env: &StepEnv, env2: Option<&StepEnv>) -> bool {
    tuple_type(tuple, env, env2) == TupleType::Identity
}

/// Classifies a tuple expression for yield optimization.
///
/// Determines if the tuple is:
/// - Identity: {x = x, y = y} - fields map to themselves
/// - Rename: {a = x, b = y} - fields are renamed but come from current bindings
/// - Other: anything else (computed values, missing fields, etc.)
fn tuple_type(
    tuple: &Expr,
    env: &StepEnv,
    env2: Option<&StepEnv>,
) -> TupleType {
    // Extract fields from the tuple.
    let fields = match tuple {
        Expr::Tuple(_, exprs) if !exprs.is_empty() => exprs,
        _ => return TupleType::Other,
    };

    // The tuple must have the same number of fields as bindings.
    if fields.len() != env.bindings.len() {
        return TupleType::Other;
    }

    // Start assuming identity, downgrade to rename if we find differences.
    let mut identity = match env2 {
        Some(e2) => env.bindings == e2.bindings,
        None => true,
    };

    // Check each field in the tuple.
    for (field_expr, binding) in fields.iter().zip(&env.bindings) {
        match field_expr {
            Expr::Identifier(_, field_name) => {
                // The field must reference a binding variable.
                if field_name != &binding.id.name {
                    identity = false;
                }
            }
            _ => {
                // Non-identifier expressions make this "Other".
                return TupleType::Other;
            }
        }
    }

    if identity {
        TupleType::Identity
    } else {
        TupleType::Rename
    }
}

/// Builds a `From` expression with optimizations.
///
/// This builder accumulates query steps and applies simplification rules
/// to produce optimized Core expressions.
#[derive(Default)]
pub struct FromBuilder {
    /// The steps in this query
    steps: Vec<Step>,

    /// Current bindings after the last step
    bindings: Vec<Binding>,

    /// Whether the result is an atom (scalar) as opposed to a record.
    atom: bool,

    /// If Some(index), that step should be removed if it's not the last step.
    /// For example, "yield {i = i}" only has meaning as the last step
    /// (forces the result to be a record instead of scalar).
    remove_if_not_last_index: Option<usize>,

    /// If Some(index), that step should be removed if it IS the last step.
    /// For example, when flattening "from p in (from q in list)" to
    /// "from q in list yield {p = q}", we want to remove "yield {p = q}"
    /// if it turns out to be the last step.
    remove_if_last_index: Option<usize>,
}

impl FromBuilder {
    /// Creates a FromBuilder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Resets this builder to its initial state.
    pub fn clear(&mut self) {
        self.steps.clear();
        self.bindings.clear();
        self.atom = false;
        self.remove_if_not_last_index = None;
        self.remove_if_last_index = None;
    }

    /// Returns the environment available after the most recent step.
    pub fn step_env(&self) -> StepEnv {
        let ordered = self.steps.last().is_none_or(|s| s.env.ordered);
        StepEnv::new(self.bindings.clone(), self.atom, ordered)
    }

    /// Adds a step to this builder.
    fn add_step(&mut self, step: Step) -> &mut Self {
        // Check if we should remove the previous step because it's no longer
        // the last step.
        if let Some(index) = self.remove_if_not_last_index
            && index == self.steps.len() - 1
        {
            // The previous step (a trivial yield) is no longer last.
            self.remove_if_not_last_index = None;
            self.remove_if_last_index = None;

            // Check if it's a trivial single-field record yield.
            if let Some(last_step) = self.steps.last()
                && matches!(last_step.kind, StepKind::Yield(_))
            {
                // TODO: Check if it's actually trivial.
                // For now, just remove it.
                self.steps.pop();
            }
        }

        // Update bindings and atom from the new step's environment.
        self.bindings = step.env.bindings.clone();
        self.atom = step.env.atom;

        self.steps.push(step);

        self
    }

    /// Adds a "where" (filter) step.
    /// Optimization: Skips "where true" since it has no effect.
    pub fn where_(&mut self, condition: Expr) -> &mut Self {
        // Check if the condition is a boolean literal true.
        if let Expr::Literal(_, Val::Bool(true)) = condition {
            // Skip "where true".
            return self;
        }

        let env = self.step_env();
        let step = Step::new(StepKind::Where(Box::new(condition)), env);
        self.add_step(step)
    }

    /// Adds a "skip" step.
    /// Optimization: Skips "skip 0" since it has no effect.
    pub fn skip(&mut self, count: Expr) -> &mut Self {
        // Check if the count is 0.
        if let Expr::Literal(_, Val::Int(n)) = &count
            && *n == 0
        {
            // Skip "skip 0".
            return self;
        }

        let env = self.step_env();
        let step = Step::new(StepKind::Skip(Box::new(count)), env);
        self.add_step(step)
    }

    /// Adds a "take" (limit) step.
    pub fn take(&mut self, count: Expr) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(StepKind::Take(Box::new(count)), env);
        self.add_step(step)
    }

    /// Adds a "distinct" step.
    pub fn distinct(&mut self) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(StepKind::Distinct, env);
        self.add_step(step)
    }

    /// Adds an "order" step.
    pub fn order(&mut self, exp: Expr) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(StepKind::Order(Box::new(exp)), env);
        self.add_step(step)
    }

    /// Makes the query unordered.
    /// No-op if already unordered.
    pub fn unorder(&mut self) -> &mut Self {
        let env = self.step_env();
        if !env.ordered {
            return self;
        }
        let env2 = env.with_ordered(false);
        let step = Step::new(StepKind::Unorder, env2);
        self.add_step(step)
    }

    /// Adds a "yield" step with optimization.
    ///
    /// This method applies several optimizations:
    /// - Skips trivial yields like "yield x" when x is the only binding
    ///   and already an atom
    /// - Skips non-singleton identity tuples like "yield {x=x, y=y}"
    /// - Marks singleton identity tuples like "yield {x=x}" as
    ///   useless-if-not-last (they only change scalar to record, which
    ///   only matters as last step)
    pub fn yield_(&mut self, exp: Expr) -> &mut Self {
        self.yield_internal(false, None, exp)
    }

    /// Internal yield implementation with full control over optimization
    /// flags.
    ///
    /// # Arguments
    /// * `useless_if_last` - Whether this yield will be useless if it's
    ///   the last step
    /// * `env2` - Desired step environment (for preserving variable
    ///   ordinals when copying)
    /// * `exp` - Expression to yield
    fn yield_internal(
        &mut self,
        useless_if_last: bool,
        env2: Option<StepEnv>,
        exp: Expr,
    ) -> &mut Self {
        let env = self.step_env();
        let mut useless_if_not_last = false;

        // Determine if the result will be an atom (single scalar value) or
        // a record. This depends on two factors:
        // 1. The number of bindings must be exactly 1 for atom.
        // 2. The yield expression must be non-tuple for atom.
        //
        // For example,
        // - "from x in [1,2] yield x" -> atom=true (1 binding, non-tuple exp);
        // - "from x in [1,2] yield {x=x}" -> atom=false (1 binding, tuple exp);
        // - "from x in [1], y in [2] yield {x,y}" -> atom=false (2 bindings).
        let is_tuple_expr = matches!(exp, Expr::Tuple(_, _));
        let atom = self.bindings.len() == 1 && !is_tuple_expr;

        match &exp {
            Expr::Tuple(_, _) => {
                let tuple_type = tuple_type(&exp, &env, env2.as_ref());
                match tuple_type {
                    TupleType::Identity => {
                        // A trivial record does not rename, so its only
                        // purpose is to change from a scalar to a record,
                        // and even then only when a singleton.
                        if self.bindings.len() == 1 {
                            // A singleton record that does not rename, e.g.
                            // 'yield {x=x}'. It only has meaning as the
                            // last step.
                            useless_if_not_last = true;
                            // Continue to add the step.
                        } else {
                            // This is a non-singleton record that does not
                            // rename any fields, e.g. 'yield {x=x,y=y}'. It is
                            // useless.
                            return self;
                        }
                    }
                    TupleType::Rename => {
                        // This is a singleton or non-singleton record that
                        // renames at least one field, e.g. 'yield {y=x}' or
                        // 'yield {y=x,z=y}'. It is always useful, so continue
                        // to add the step.
                    }
                    TupleType::Other => {
                        // Any other tuple (computed values, etc.).
                        // Always useful, continue to add the step.
                    }
                }
            }
            Expr::Identifier(_, name) => {
                // Check if this is a trivial "yield x" where x is the
                // only binding.
                if self.bindings.len() == 1
                    && self.bindings[0].id.name == *name
                    // After 'yield {x = something}', 'yield x' may seem
                    // trivial, but it converts a singleton record to an
                    // atom, so don't remove it.
                    && (self.steps.is_empty()
                        || self.steps.last().unwrap().env.atom)
                {
                    return self;
                }
            }
            _ => {
                // Other expressions, continue to add the step.
            }
        }

        // Create the yield step.
        let step_env = env2.unwrap_or_else(|| {
            StepEnv::new(self.bindings.clone(), atom, env.ordered)
        });
        let step = Step::new(StepKind::Yield(Box::new(exp)), step_env);
        self.add_step(step);

        // Update removal indices.
        self.remove_if_not_last_index = if useless_if_not_last {
            Some(self.steps.len() - 1)
        } else {
            None
        };
        self.remove_if_last_index = if useless_if_last {
            Some(self.steps.len() - 1)
        } else {
            None
        };

        self
    }

    /// Adds an "except" (set difference) step.
    pub fn except(&mut self, distinct: bool, args: Vec<Expr>) -> &mut Self {
        let env = self.step_env();
        // Except maintains order only if all arguments are lists.
        let ordered = env.ordered
            && args.iter().all(|arg| is_list_type(arg.type_().as_ref()));
        let env2 = env.with_ordered(ordered);
        let step = Step::new(StepKind::Except(distinct, args), env2);
        self.add_step(step)
    }

    /// Adds an "intersect" (set intersection) step.
    pub fn intersect(&mut self, distinct: bool, args: Vec<Expr>) -> &mut Self {
        let env = self.step_env();
        // Intersect maintains order only if all arguments are lists.
        let ordered = env.ordered
            && args.iter().all(|arg| is_list_type(arg.type_().as_ref()));
        let env2 = env.with_ordered(ordered);
        let step = Step::new(StepKind::Intersect(distinct, args), env2);
        self.add_step(step)
    }

    /// Adds a "union" (set union) step.
    pub fn union(&mut self, distinct: bool, args: Vec<Expr>) -> &mut Self {
        let env = self.step_env();
        // Union maintains order only if all arguments are lists.
        let ordered = env.ordered
            && args.iter().all(|arg| is_list_type(arg.type_().as_ref()));
        let env2 = env.with_ordered(ordered);
        let step = Step::new(StepKind::Union(distinct, args), env2);
        self.add_step(step)
    }

    /// Adds a "group" step.
    pub fn group(
        &mut self,
        key_expr: Expr,
        aggregate_expr: Option<Expr>,
    ) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(
            StepKind::Group(Box::new(key_expr), aggregate_expr.map(Box::new)),
            env,
        );
        self.add_step(step);

        self
    }

    /// Adds a scan step "from pat in exp".
    /// This is a simplified version - the Java implementation has complex
    /// logic for inlining nested froms and handling patterns.
    pub fn scan(&mut self, pat: Pat, exp: Expr) -> &mut Self {
        self.scan_with_condition(pat, exp, None)
    }

    /// Adds a scan step "from pat in exp where condition".
    pub fn scan_with_condition(
        &mut self,
        pat: Pat,
        exp: Expr,
        condition: Option<Expr>,
    ) -> &mut Self {
        // TODO: Implement the complex nested from inlining logic from Java.
        // For now, just add a simple scan step.

        // Update bindings based on the pattern.
        // For tuple patterns like `(i,j)`, this collects multiple bindings.
        Binding::collect_bindings(&pat, &mut self.bindings);
        self.atom = self.bindings.len() == 1;

        let env = self.step_env();
        let step = Step::new(
            StepKind::Scan(
                Box::new(pat),
                Box::new(exp),
                condition.map(Box::new),
            ),
            env,
        );
        self.add_step(step)
    }

    /// Builds the From expression.
    pub fn build(&mut self) -> Result<Expr, Error> {
        self.build_internal(false)
    }

    /// Builds the From expression with simplification.
    /// Can return a simple expression instead of a From if the query
    /// simplifies to "from x in list".
    pub fn build_simplify(&mut self) -> Result<Expr, Error> {
        self.build_internal(true)
    }

    fn build_internal(&mut self, simplify: bool) -> Result<Expr, Error> {
        // Remove the last step if flagged.
        if let Some(index) = self.remove_if_last_index
            && index == self.steps.len() - 1
        {
            self.steps.pop();
            self.remove_if_last_index = None;
        }

        // Simplification: "from v in list" -> "list".
        if simplify
            && self.steps.len() == 1
            && let StepKind::Scan(pat, exp, None) = &self.steps[0].kind
            && matches!(**pat, Pat::Identifier(_, _))
        {
            return Ok((**exp).clone());
        }

        // Build the From expression.
        let result_type = self.compute_result_type()?;
        Ok(Expr::From(Box::new(result_type), self.steps.clone()))
    }

    fn compute_result_type(&self) -> Result<Type, Error> {
        use crate::compile::types::Label;
        use std::collections::BTreeMap;

        // The element type is the type of each element in the result list.
        // If we have a single binding that matches the atom flag, use its type.
        // Otherwise, create a record type from all bindings.
        let env = self.step_env();
        if env.bindings.len() == 1 && env.atom {
            // Single scalar binding - element type is that binding's type.
            Ok(*env.bindings[0].type_.clone())
        } else {
            // Multiple bindings or non-atom - element type is a record.
            let fields: BTreeMap<Label, Type> = env
                .bindings
                .iter()
                .map(|b| (Label::String(b.id.name.clone()), *b.type_.clone()))
                .collect();
            Ok(Type::Record(false, fields))
        }
    }
}

impl fmt::Debug for FromBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FromBuilder({} steps)", self.steps.len())
    }
}

impl fmt::Display for FromBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.steps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::PrimitiveType;

    #[test]
    fn test_new_builder() {
        let builder = FromBuilder::new();
        assert_eq!(builder.steps.len(), 0);
        assert_eq!(builder.bindings.len(), 0);
        assert!(!builder.atom);
    }

    #[test]
    fn test_clear() {
        let mut builder = FromBuilder::new();
        // Add some state (would need actual steps to test fully)
        builder.atom = true;
        builder.clear();
        assert_eq!(builder.steps.len(), 0);
        assert!(!builder.atom);
    }

    #[test]
    fn test_where_true_skipped() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.where_(Expr::Literal(
            Box::new(Type::Primitive(PrimitiveType::Bool)),
            Val::Bool(true),
        ));
        // "where true" should be skipped
        assert_eq!(builder.steps.len(), initial_len);
    }

    #[test]
    fn test_skip_zero_skipped() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.skip(Expr::Literal(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            Val::Int(0),
        ));
        // "skip 0" should be skipped
        assert_eq!(builder.steps.len(), initial_len);
    }

    #[test]
    fn test_union_added() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.union(true, vec![]);
        // Union step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Union(true, _)));
        }
    }

    #[test]
    fn test_scan_updates_bindings() {
        use crate::compile::type_env::Id;
        let mut builder = FromBuilder::new();
        let pat = Pat::Identifier(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            "x".to_string(),
        );
        let exp = Expr::List(
            Box::new(Type::List(Box::new(Type::Primitive(PrimitiveType::Int)))),
            vec![],
        );
        builder.scan(pat, exp);
        // Should have one binding and atom should be true
        assert_eq!(builder.bindings.len(), 1);
        assert!(builder.atom);
        assert_eq!(builder.bindings[0].id, Id::new("x", 0));
    }

    #[test]
    fn test_group_added() {
        let mut builder = FromBuilder::new();
        let key_expr = Expr::Literal(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            Val::Int(1),
        );
        let initial_len = builder.steps.len();
        builder.group(key_expr, None);
        // Group step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Group(_, None)));
        }
    }

    #[test]
    fn test_except_added() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.except(false, vec![]);
        // Except step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Except(false, _)));
        }
    }

    #[test]
    fn test_yield_trivial_singleton_skipped() {
        let mut builder = FromBuilder::new();

        // Add a binding first via scan
        let pat = Pat::Identifier(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            "x".to_string(),
        );
        let exp = Expr::List(
            Box::new(Type::List(Box::new(Type::Primitive(PrimitiveType::Int)))),
            vec![],
        );
        builder.scan(pat, exp);

        // Now try to yield x (should be skipped as trivial)
        let initial_len = builder.steps.len();
        builder.yield_(Expr::Identifier(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            "x".to_string(),
        ));

        // Yield should have been skipped
        assert_eq!(builder.steps.len(), initial_len);
    }

    #[test]
    fn test_yield_non_singleton_identity_skipped() {
        use crate::compile::type_env::Id;
        let mut builder = FromBuilder::new();

        // Add two bindings
        builder.bindings.push(Binding::new(
            Id::new("x", 0),
            Box::new(Type::Primitive(PrimitiveType::Int)),
        ));
        builder.bindings.push(Binding::new(
            Id::new("y", 0),
            Box::new(Type::Primitive(PrimitiveType::Int)),
        ));

        // Yield {x=x, y=y} should be skipped as identity
        let initial_len = builder.steps.len();
        builder.yield_(Expr::Tuple(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            vec![
                Expr::Identifier(
                    Box::new(Type::Primitive(PrimitiveType::Int)),
                    "x".to_string(),
                ),
                Expr::Identifier(
                    Box::new(Type::Primitive(PrimitiveType::Int)),
                    "y".to_string(),
                ),
            ],
        ));

        // Yield should have been skipped
        assert_eq!(builder.steps.len(), initial_len);
    }

    #[test]
    fn test_distinct_adds_step() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.distinct();
        // Distinct step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Distinct));
        }
    }

    #[test]
    fn test_order_adds_step() {
        let mut builder = FromBuilder::new();
        let expr = Expr::Literal(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            Val::Int(1),
        );
        let initial_len = builder.steps.len();
        builder.order(expr);
        // Order step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Order(_)));
        }
    }

    #[test]
    fn test_take_adds_step() {
        let mut builder = FromBuilder::new();
        let count = Expr::Literal(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            Val::Int(10),
        );
        let initial_len = builder.steps.len();
        builder.take(count);
        // Take step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Take(_)));
        }
    }

    #[test]
    fn test_unorder_noop_when_already_unordered() {
        let mut builder = FromBuilder::new();
        // Add a scan step first (which sets ordered=true by default)
        let pat = Pat::Identifier(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            "x".to_string(),
        );
        let exp = Expr::List(
            Box::new(Type::List(Box::new(Type::Primitive(PrimitiveType::Int)))),
            vec![],
        );
        builder.scan(pat, exp);

        // First unorder should add a step
        builder.unorder();
        let len_after_first = builder.steps.len();
        // Second call should be a no-op since already unordered
        builder.unorder();
        assert_eq!(builder.steps.len(), len_after_first);
    }

    #[test]
    fn test_method_chaining() {
        let mut builder = FromBuilder::new();

        // Test that methods can be chained
        let pat = Pat::Identifier(
            Box::new(Type::Primitive(PrimitiveType::Int)),
            "x".to_string(),
        );
        let exp = Expr::List(
            Box::new(Type::List(Box::new(Type::Primitive(PrimitiveType::Int)))),
            vec![],
        );
        let condition = Expr::Literal(
            Box::new(Type::Primitive(PrimitiveType::Bool)),
            Val::Bool(true),
        );

        builder.scan(pat, exp).where_(condition).distinct().take(
            Expr::Literal(
                Box::new(Type::Primitive(PrimitiveType::Int)),
                Val::Int(5),
            ),
        );

        // Should have scan, (where true skipped), distinct, and take
        assert_eq!(builder.steps.len(), 3);
    }

    #[test]
    fn test_intersect_added() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.intersect(true, vec![]);
        // Intersect step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Intersect(true, _)));
        }
    }
}
