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

//! Synthesises generator expressions from `where` conjuncts.
//! Phase 1 of predicate inversion (hydromatic/morel#217).
//!
//! Mirrors morel-java's `compile.Generators::maybeGenerator`
//! with the leaf strategies — point, elem, range. Later phases
//! add string-prefix, function inlining, exists, case, and
//! constructor patterns.

use crate::compile::core::{Binding, Expr, Match, Pat};
use crate::compile::expander::{DatatypeMap, FnEnv, and_all, expr_eq};
use crate::compile::free_finder::free_names_in;
use crate::compile::generator::{Cache, Cardinality, Generator};
use crate::compile::library::{BuiltInFunction, lookup_struct_field};
use crate::compile::replacer::substitute;
use crate::compile::span::Span;
use crate::compile::type_env::Id;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::val::Val;
use std::collections::{BTreeSet, HashMap};

/// Tries to derive a generator for `pat` from the conjuncts in
/// `constraints`. Returns `true` if a generator was added to the
/// cache.
///
/// `ordered` is `true` when the surrounding `from` is producing a
/// list (vs a bag). It influences which `tabulate` built-in we use
/// for ranges (`List.tabulate` vs `Bag.tabulate`).
pub fn maybe_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    let empty: BTreeSet<String> = BTreeSet::new();
    maybe_generator_with_scope(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
        &empty,
        &empty,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn maybe_generator_with_scope(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
    unbounded_siblings: &BTreeSet<String>,
) -> bool {
    // Phase A: classify each conjunct.
    let mut elem_match: Option<&Expr> = None;
    let mut elem_collection: Option<&Expr> = None;

    let mut point_match: Option<&Expr> = None;
    let mut point_value: Option<&Expr> = None;

    let mut has_bounds = false;

    let mut prefix_match: Option<&Expr> = None;
    let mut prefix_string: Option<&Expr> = None;

    for c in constraints {
        if elem_match.is_none()
            && let Some((lhs, rhs)) =
                call2_args(c, &[BuiltInFunction::ListElem])
            && references(lhs, pat_name)
        {
            elem_match = Some(c);
            elem_collection = Some(rhs);
        }
        if point_match.is_none()
            && let Some((lhs, rhs)) = call2_args(
                c,
                &[
                    BuiltInFunction::IntEq,
                    BuiltInFunction::RealEq,
                    BuiltInFunction::StringEq,
                    BuiltInFunction::CharEq,
                    BuiltInFunction::BoolEq,
                    BuiltInFunction::GEq,
                ],
            )
        {
            if references(lhs, pat_name) {
                point_match = Some(c);
                point_value = Some(rhs);
            } else if references(rhs, pat_name) {
                // Reverse direction: `value = pat`. Reject if the
                // value references another unbounded sibling — the
                // sibling will pick up this constraint via the
                // forward direction (`sibling = value`), and using
                // both directions would create a cycle that
                // topo_order can't resolve.
                let lhs_free = free_names_in(lhs);
                let cycles = lhs_free
                    .iter()
                    .any(|n| n != pat_name && unbounded_siblings.contains(n));
                if !cycles {
                    point_match = Some(c);
                    point_value = Some(lhs);
                }
            }
        }
        if !has_bounds && is_bound_constraint(c, pat_name) {
            has_bounds = true;
        }
        if prefix_match.is_none()
            && matches!(pat_type, Type::Primitive(PrimitiveType::String))
            && let Some(s) = is_string_prefix_call(c, pat_name)
        {
            prefix_match = Some(c);
            prefix_string = Some(s);
        }
    }

    // Phase B: synthesise leaf generators in priority order.
    if let (Some(c), Some(coll)) = (elem_match, elem_collection) {
        return create_collection_generator(cache, pat, pat_name, coll, c);
    }
    if maybe_record_elem_projection(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        outer_scope,
    ) {
        return true;
    }
    if let (Some(c), Some(value)) = (point_match, point_value) {
        return create_point_generator(cache, pat, pat_name, value, c);
    }
    if has_bounds && matches!(pat_type, Type::Primitive(PrimitiveType::Int)) {
        return create_range_generator(
            cache,
            pat,
            pat_name,
            ordered,
            constraints,
        );
    }
    if matches!(pat_type, Type::Tuple(_))
        && create_tuple_range_generator(
            cache,
            pat,
            pat_name,
            pat_type,
            ordered,
            constraints,
        )
    {
        return true;
    }
    if let (Some(c), Some(s)) = (prefix_match, prefix_string) {
        return create_string_prefix_generator(
            cache, pat, pat_name, ordered, s, c,
        );
    }
    if maybe_exists(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
    ) {
        return true;
    }
    if maybe_function(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
    ) {
        return true;
    }
    if maybe_case(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
    ) {
        return true;
    }
    if maybe_union(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
    ) {
        return true;
    }
    if maybe_case_constructor(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
    ) {
        return true;
    }
    // Fallback: enumerate all values of the pattern's type, when
    // that type is finite (bool, option of finite, tuple of
    // finite, user datatype with all-nullary constructors).
    // Surrounding `where` conjuncts filter as needed (e.g.
    // `not b` keeps only `false`, `Option.getOpt i` keeps only
    // the tuples whose option/default product is true).
    if let Some(extent) = finite_extent(pat_type, datatypes) {
        return create_finite_extent_generator(cache, pat, pat_name, extent);
    }
    false
}

// ---------------------------------------------------------------------------
// Leaf strategies
// ---------------------------------------------------------------------------

fn create_collection_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    collection: &Expr,
    source_constraint: &Expr,
) -> bool {
    let mut free = free_names_in(collection);
    free.remove(pat_name);
    let generator = Generator::new(
        pat.clone(),
        collection.clone(),
        Cardinality::Finite,
        free,
        true, // assume the user-supplied collection has unique elements
        true, // sealed: the elem-conjunct is fully encoded by the scan
        vec![source_constraint.clone()],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

fn create_point_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    value: &Expr,
    source_constraint: &Expr,
) -> bool {
    let elem_t = value.type_();
    let list_t = Box::new(Type::List(Box::new((*elem_t).clone())));
    let exp = Expr::List(list_t, vec![value.clone()]);
    let mut free = free_names_in(value);
    free.remove(pat_name);
    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Single,
        free,
        true,
        true,
        vec![source_constraint.clone()],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

fn create_range_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    ordered: bool,
    constraints: &[Expr],
) -> bool {
    let lower = match lower_bound(pat_name, constraints) {
        Some(l) => l,
        None => return false,
    };
    let upper = match upper_bound(pat_name, constraints) {
        Some(u) => u,
        None => return false,
    };

    // Provenance: every bound constraint involving the pattern.
    let provenance: Vec<Expr> = constraints
        .iter()
        .filter(|c| is_bound_constraint(c, pat_name))
        .cloned()
        .collect();

    // Build:
    //   List.tabulate (upper - lower + 1, fn k => lower + k)
    // (for ordered; Bag.tabulate otherwise.)
    let int_t = Box::new(Type::Primitive(PrimitiveType::Int));

    let lower_expr = if lower.strict {
        // x > lower  ⇒  use `lower + 1` as the inclusive low.
        binop_int(BuiltInFunction::IntPlus, lower.bound.clone(), int_lit(1))
    } else {
        lower.bound.clone()
    };
    let upper_expr = if upper.strict {
        binop_int(BuiltInFunction::IntMinus, upper.bound.clone(), int_lit(1))
    } else {
        upper.bound.clone()
    };

    let count = binop_int(
        BuiltInFunction::IntPlus,
        binop_int(
            BuiltInFunction::IntMinus,
            upper_expr.clone(),
            lower_expr.clone(),
        ),
        int_lit(1),
    );

    // fn k => lower + k
    let k_pat = Pat::Identifier(int_t.clone(), "k".to_string());
    let body = binop_int(
        BuiltInFunction::IntPlus,
        lower_expr.clone(),
        Expr::Identifier(int_t.clone(), "k".to_string()),
    );
    let fn_t = Box::new(Type::Fn(int_t.clone(), int_t.clone()));
    let fn_expr = Expr::Fn(
        fn_t.clone(),
        vec![Match {
            pat: k_pat,
            expr: body,
        }],
        Span::new(""),
    );

    let tabulate = if ordered {
        BuiltInFunction::ListTabulate
    } else {
        BuiltInFunction::BagTabulate
    };
    let coll_t = if ordered {
        Box::new(Type::List(int_t.clone()))
    } else {
        Box::new(Type::Bag(int_t.clone()))
    };
    let exp = call2(tabulate, count, fn_expr, coll_t);

    let mut free = free_names_in(&lower.bound);
    free.append(&mut free_names_in(&upper.bound));
    free.remove(pat_name);

    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Finite,
        free,
        true,
        true,
        provenance,
    );
    cache.add(pat_name.to_string(), generator);
    true
}

/// Recognises a constraint of the form
///   `t >= (l1, …, lk) andalso t <= (u1, …, uk)`
/// (or just `t = (v1, …, vk)`) where every component is a
/// literal and the tuple type is enumerable, and emits a
/// `Bag.fromList`/`List` of the lex-ordered values between
/// `lo` and `hi` inclusive. Required for queries like
///
///   from t where t >= (false, 3) andalso t <= (false, 5)
///
/// where the range generator can't operate on `int` alone.
///
/// Returns `true` if a generator was added.
fn create_tuple_range_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
) -> bool {
    // Separate component types.
    let component_types: Vec<Type> = match pat_type {
        Type::Tuple(ts) => ts.clone(),
        _ => return false,
    };
    // Collect lo and hi tuples from the constraints. Look for
    // `t >= lit_tuple` (or `t > …`), `t <= lit_tuple` (or `t < …`).
    let mut lo: Option<(Vec<Val>, bool)> = None; // (vals, strict)
    let mut hi: Option<(Vec<Val>, bool)> = None;
    let mut bound_constraints: Vec<Expr> = Vec::new();
    for c in constraints {
        let Some((lhs, rhs, op)) = call2_args_op(c, &[BuiltInFunction::GEq])
        else {
            continue;
        };
        // We only handle the polymorphic comparison op `GEq` here
        // (which dispatches by type at runtime). Either side
        // could be the literal.
        let _ = op;
        // The comparison-op literal tells us whether it's >, <,
        // >=, or <=. We don't have that info from `GEq` alone, so
        // skip — comparisons on tuples in our codebase use
        // primitive ops only.
        let _ = (lhs, rhs);
    }
    // Comparison-by-value-on-tuples isn't supported by our
    // codebase via `GEq`; tuples compare via specific `<`, `>`,
    // `<=`, `>=` builtins. Look for those instead.
    for c in constraints {
        let result = call2_args_op(
            c,
            &[
                BuiltInFunction::IntGe,
                BuiltInFunction::IntGt,
                BuiltInFunction::IntLe,
                BuiltInFunction::IntLt,
                BuiltInFunction::IntEq,
                BuiltInFunction::GEq,
                BuiltInFunction::GGe,
                BuiltInFunction::GGt,
                BuiltInFunction::GLe,
                BuiltInFunction::GLt,
            ],
        );
        let Some((lhs, rhs, op)) = result else {
            continue;
        };
        // The pattern side is `Identifier(_, pat_name)`; the
        // other side must be a literal tuple.
        let (lit_side, pat_first) = match (lhs, rhs) {
            (Expr::Identifier(_, n), other) if n == pat_name => (other, true),
            (other, Expr::Identifier(_, n)) if n == pat_name => (other, false),
            _ => continue,
        };
        let Expr::Tuple(_, items) = lit_side else {
            continue;
        };
        let Some(vals) = items
            .iter()
            .map(|e| match e {
                Expr::Literal(_, v) => Some(v.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        // Map the operator to a (lo|hi, strict) classification.
        let (is_lo, strict) = match (op, pat_first) {
            (BuiltInFunction::IntGe | BuiltInFunction::GGe, true) => {
                // pat >= lit ⇒ lit is the lower bound.
                (true, false)
            }
            (BuiltInFunction::IntGt | BuiltInFunction::GGt, true) => {
                (true, true)
            }
            (BuiltInFunction::IntLe | BuiltInFunction::GLe, true) => {
                (false, false)
            }
            (BuiltInFunction::IntLt | BuiltInFunction::GLt, true) => {
                (false, true)
            }
            (BuiltInFunction::IntEq | BuiltInFunction::GEq, _) => {
                // pat = lit ⇒ both bounds are lit.
                lo = Some((vals.clone(), false));
                hi = Some((vals.clone(), false));
                bound_constraints.push(c.clone());
                continue;
            }
            (BuiltInFunction::IntGe | BuiltInFunction::GGe, false) => {
                (false, false)
            }
            (BuiltInFunction::IntGt | BuiltInFunction::GGt, false) => {
                (false, true)
            }
            (BuiltInFunction::IntLe | BuiltInFunction::GLe, false) => {
                (true, false)
            }
            (BuiltInFunction::IntLt | BuiltInFunction::GLt, false) => {
                (true, true)
            }
            _ => continue,
        };
        if is_lo {
            lo = Some((vals, strict));
        } else {
            hi = Some((vals, strict));
        }
        bound_constraints.push(c.clone());
    }
    let Some((lo_vals, lo_strict)) = lo else {
        return false;
    };
    let Some((hi_vals, hi_strict)) = hi else {
        return false;
    };
    if lo_vals.len() != component_types.len()
        || hi_vals.len() != component_types.len()
    {
        return false;
    }
    // Bump strict bounds to inclusive by stepping the int-most
    // component (we only know how to step ints). For now reject
    // strict bounds on non-int trailing component.
    let lo_inclusive = if lo_strict {
        match step_tuple(&lo_vals, &component_types, true) {
            Some(v) => v,
            None => return false,
        }
    } else {
        lo_vals
    };
    let hi_inclusive = if hi_strict {
        match step_tuple(&hi_vals, &component_types, false) {
            Some(v) => v,
            None => return false,
        }
    } else {
        hi_vals
    };

    let Some(values) =
        enumerate_tuple_range(&lo_inclusive, &hi_inclusive, &component_types)
    else {
        return false;
    };

    // Build a list literal of the enumerated tuples.
    let elem_t = Box::new(pat_type.clone());
    let list_t = Box::new(Type::List(elem_t.clone()));
    let items: Vec<Expr> = values
        .into_iter()
        .map(|tv| {
            Expr::Tuple(
                elem_t.clone(),
                tv.into_iter()
                    .zip(component_types.iter())
                    .map(|(v, t)| Expr::Literal(Box::new(t.clone()), v))
                    .collect(),
            )
        })
        .collect();
    let exp = Expr::List(list_t, items);
    let _ = ordered;

    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Finite,
        BTreeSet::new(),
        true,
        true,
        bound_constraints,
    );
    cache.add(pat_name.to_string(), generator);
    true
}

/// Steps a tuple value by ±1 at its trailing int component
/// (for converting strict bounds to inclusive). Returns `None`
/// if the trailing component isn't int.
fn step_tuple(
    vals: &[Val],
    types: &[Type],
    increase: bool,
) -> Option<Vec<Val>> {
    if vals.is_empty() {
        return None;
    }
    let last_t = types.last()?;
    if !matches!(last_t, Type::Primitive(PrimitiveType::Int)) {
        return None;
    }
    let Val::Int(n) = vals.last()? else {
        return None;
    };
    let mut out = vals.to_vec();
    *out.last_mut().unwrap() = Val::Int(if increase { n + 1 } else { n - 1 });
    Some(out)
}

/// Lex-enumerates the tuples `[lo, …, hi]` (inclusive). Returns
/// `None` if any "middle" component would require enumerating
/// values of a non-finite type (e.g. `int` between two bools).
fn enumerate_tuple_range(
    lo: &[Val],
    hi: &[Val],
    types: &[Type],
) -> Option<Vec<Vec<Val>>> {
    if lo.is_empty() {
        return Some(vec![vec![]]);
    }
    if compare_tuple(lo, hi) > 0 {
        return Some(vec![]);
    }
    let lo_v = &lo[0];
    let hi_v = &hi[0];
    let t = &types[0];
    let mut out: Vec<Vec<Val>> = Vec::new();
    for v in iter_values_inclusive(lo_v, hi_v, t)? {
        let lo_eq = compare_val(&v, lo_v) == 0;
        let hi_eq = compare_val(&v, hi_v) == 0;
        let sub_lo: Vec<Val> = if lo_eq {
            lo[1..].to_vec()
        } else {
            type_mins(&types[1..])?
        };
        let sub_hi: Vec<Val> = if hi_eq {
            hi[1..].to_vec()
        } else {
            type_maxes(&types[1..])?
        };
        let subs = enumerate_tuple_range(&sub_lo, &sub_hi, &types[1..])?;
        for sub in subs {
            let mut full = vec![v.clone()];
            full.extend(sub);
            out.push(full);
        }
    }
    Some(out)
}

/// Iterates [lo, hi] inclusive, in lex order. Returns `None` if
/// the type isn't enumerable (e.g. `string`).
fn iter_values_inclusive(lo: &Val, hi: &Val, t: &Type) -> Option<Vec<Val>> {
    match t {
        Type::Primitive(PrimitiveType::Int) => {
            let Val::Int(a) = lo else { return None };
            let Val::Int(b) = hi else { return None };
            Some((*a..=*b).map(Val::Int).collect())
        }
        Type::Primitive(PrimitiveType::Bool) => {
            let Val::Bool(a) = lo else { return None };
            let Val::Bool(b) = hi else { return None };
            // Order: false < true.
            let mut out = Vec::new();
            for v in [false, true] {
                if (!a || v) && (*b || !v) {
                    out.push(Val::Bool(v));
                }
            }
            Some(out)
        }
        _ => None,
    }
}

/// Min values of a tuple of types (the lex-smallest tuple).
/// Returns `None` if any type lacks a known minimum.
fn type_mins(types: &[Type]) -> Option<Vec<Val>> {
    types.iter().map(type_min).collect()
}

fn type_min(t: &Type) -> Option<Val> {
    match t {
        Type::Primitive(PrimitiveType::Bool) => Some(Val::Bool(false)),
        // Ints have no smallest value we want to enumerate;
        // disallow.
        _ => None,
    }
}

/// Max values of a tuple of types.
fn type_maxes(types: &[Type]) -> Option<Vec<Val>> {
    types.iter().map(type_max).collect()
}

fn type_max(t: &Type) -> Option<Val> {
    match t {
        Type::Primitive(PrimitiveType::Bool) => Some(Val::Bool(true)),
        _ => None,
    }
}

/// Lexicographic comparison of two tuples of values.
fn compare_tuple(a: &[Val], b: &[Val]) -> i32 {
    for (x, y) in a.iter().zip(b.iter()) {
        let c = compare_val(x, y);
        if c != 0 {
            return c;
        }
    }
    a.len() as i32 - b.len() as i32
}

fn compare_val(a: &Val, b: &Val) -> i32 {
    match (a, b) {
        (Val::Int(x), Val::Int(y)) => x.cmp(y) as i32,
        (Val::Bool(x), Val::Bool(y)) => x.cmp(y) as i32,
        _ => 0, // unsupported — caller has already filtered
    }
}

/// Generator of last resort: yield every value of the pattern's
/// type, provided the type is finite. The surrounding `where`
/// clause filters down. Used for `from b where not b` (single
/// bool), `from i where Option.getOpt i` (tuple of bool option *
/// bool), etc.
fn create_finite_extent_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    extent: Expr,
) -> bool {
    let generator = Generator::new(
        pat.clone(),
        extent,
        Cardinality::Finite,
        BTreeSet::new(),
        true,
        false, // unsealed: doesn't subsume any specific predicate
        Vec::new(),
    );
    cache.add(pat_name.to_string(), generator);
    true
}

/// Returns a Core list expression containing every value of `t`,
/// or `None` if `t` is infinite (int, real, string, …) or
/// references a feature this builder doesn't yet handle (user
/// datatype, list, fn, …). Built-in types covered: `bool`,
/// `'a option` for finite `'a`, tuples of finite components, and
/// user datatypes whose constructors are all nullary.
fn finite_extent(t: &Type, datatypes: &DatatypeMap) -> Option<Expr> {
    match t {
        Type::Primitive(PrimitiveType::Bool) => Some(bool_extent_list()),
        Type::Data(name, args) if name == "option" && args.len() == 1 => {
            let inner = finite_extent(&args[0], datatypes)?;
            Some(option_extent_list(&args[0], inner))
        }
        Type::Data(name, _) => {
            let constructors = datatypes.get(name)?;
            // Phase 1 of datatype extents: only nullary
            // constructors. Constructors that take arguments would
            // need the arg type's extent, plus a way to construct
            // `Val::Constructor(ord, val)` in Core for each one.
            Some(datatype_extent_list(t, name, constructors))
        }
        Type::Tuple(types) => {
            let mut extents = Vec::with_capacity(types.len());
            for ti in types {
                extents.push(finite_extent(ti, datatypes)?);
            }
            Some(tuple_extent_cartesian(types, extents))
        }
        _ => None,
    }
}

/// Produces a list-expression of every nullary-constructor value of
/// the given datatype. `data_t` is the datatype's `Type`, `name` is
/// the datatype name, and `constructors` is the constructor list in
/// declaration order.
fn datatype_extent_list(
    data_t: &Type,
    _name: &str,
    constructors: &[String],
) -> Expr {
    let data_t_box = Box::new(data_t.clone());
    let list_t = Box::new(Type::List(data_t_box.clone()));
    // Each constructor is a global `CoreExpr::Identifier` after
    // resolution — that's how the user-typed `BLUE` reaches Core.
    // It carries the datatype's `Type::Data` directly (constants
    // have no parameter). The compiler later re-interprets the
    // identifier through the resolver/eval lookup tables.
    let elems: Vec<Expr> = constructors
        .iter()
        .map(|cname| Expr::Identifier(data_t_box.clone(), cname.clone()))
        .collect();
    Expr::List(list_t, elems)
}

fn bool_extent_list() -> Expr {
    let bool_t = Box::new(Type::Primitive(PrimitiveType::Bool));
    let list_t = Box::new(Type::List(bool_t.clone()));
    // `false` first, `true` second — matches morel-java's
    // ordering for tuple enumeration over bool components, and
    // also matches `compare` semantics (false < true).
    Expr::List(
        list_t,
        vec![
            Expr::Literal(bool_t.clone(), Val::Bool(false)),
            Expr::Literal(bool_t, Val::Bool(true)),
        ],
    )
}

fn option_extent_list(inner_t: &Type, inner_extent: Expr) -> Expr {
    let inner_t_box = Box::new(inner_t.clone());
    let option_t =
        Box::new(Type::Data("option".to_string(), vec![inner_t.clone()]));
    let list_t = Box::new(Type::List(option_t.clone()));

    // NONE: Expr::Literal carrying the OptionNone built-in value.
    // The compiler converts this to `Code::new_constant(t,
    // Val::Unit)` (the runtime encoding of `NONE`).
    let none_expr =
        Expr::Literal(option_t.clone(), Val::Fn(BuiltInFunction::OptionNone));

    // SOME : 'a -> 'a option
    let some_fn_t = Box::new(Type::Fn(inner_t_box.clone(), option_t.clone()));
    let some_fn_expr =
        Expr::Literal(some_fn_t, Val::Fn(BuiltInFunction::OptionSome));

    let inner_elems = match inner_extent {
        Expr::List(_, vs) => vs,
        _ => return none_expr, // shouldn't happen
    };

    let mut elems = Vec::with_capacity(inner_elems.len() + 1);
    elems.push(none_expr);
    for v in inner_elems {
        elems.push(Expr::Apply(
            option_t.clone(),
            Box::new(some_fn_expr.clone()),
            Box::new(v),
            Span::new(""),
        ));
    }
    Expr::List(list_t, elems)
}

fn tuple_extent_cartesian(types: &[Type], extents: Vec<Expr>) -> Expr {
    let tuple_t = Box::new(Type::Tuple(types.to_vec()));
    let list_t = Box::new(Type::List(tuple_t.clone()));

    // Each `extents[i]` is `Expr::List(_, values_i)`. Compute the
    // cartesian product of the value lists, then build a
    // tuple-list whose entries are the product tuples.
    let value_lists: Vec<Vec<Expr>> = extents
        .into_iter()
        .map(|e| match e {
            Expr::List(_, vs) => vs,
            _ => Vec::new(),
        })
        .collect();

    let products = cartesian_product(&value_lists);
    let elems: Vec<Expr> = products
        .into_iter()
        .map(|values| Expr::Tuple(tuple_t.clone(), values))
        .collect();
    Expr::List(list_t, elems)
}

fn cartesian_product(lists: &[Vec<Expr>]) -> Vec<Vec<Expr>> {
    let mut acc: Vec<Vec<Expr>> = vec![Vec::new()];
    for list in lists {
        let mut next = Vec::with_capacity(acc.len() * list.len());
        for prefix in &acc {
            for v in list {
                let mut row = prefix.clone();
                row.push(v.clone());
                next.push(row);
            }
        }
        acc = next;
    }
    acc
}

/// Inverts `String.isPrefix p s` (where `p` is the pattern, `s` is
/// any string expression) into
///   `Bag.tabulate(String.size s + 1, fn i => String.substring(s, 0, i))`
/// (or `List.tabulate` when the surrounding `from` is ordered).
fn create_string_prefix_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    ordered: bool,
    s: &Expr,
    source_constraint: &Expr,
) -> bool {
    let int_t = Box::new(Type::Primitive(PrimitiveType::Int));
    let str_t = Box::new(Type::Primitive(PrimitiveType::String));

    // String.size s
    let size_s = call1(BuiltInFunction::StringSize, s.clone(), int_t.clone());
    // String.size s + 1
    let count = binop_int(BuiltInFunction::IntPlus, size_s, int_lit(1));

    // fn i => String.substring (s, 0, i)
    let i_pat = Pat::Identifier(int_t.clone(), "i".to_string());
    let i_id = Expr::Identifier(int_t.clone(), "i".to_string());
    let triple_t = Box::new(Type::Tuple(vec![
        (*str_t).clone(),
        (*int_t).clone(),
        (*int_t).clone(),
    ]));
    let triple =
        Expr::Tuple(triple_t.clone(), vec![s.clone(), int_lit(0), i_id]);
    let fn_substr_t = Box::new(Type::Fn(triple_t.clone(), str_t.clone()));
    let fn_substr_lit =
        Expr::Literal(fn_substr_t, Val::Fn(BuiltInFunction::StringSubstring));
    let body = Expr::Apply(
        str_t.clone(),
        Box::new(fn_substr_lit),
        Box::new(triple),
        Span::new(""),
    );
    let fn_t = Box::new(Type::Fn(int_t.clone(), str_t.clone()));
    let fn_expr = Expr::Fn(
        fn_t,
        vec![Match {
            pat: i_pat,
            expr: body,
        }],
        Span::new(""),
    );

    let tabulate = if ordered {
        BuiltInFunction::ListTabulate
    } else {
        BuiltInFunction::BagTabulate
    };
    let coll_t = if ordered {
        Box::new(Type::List(str_t.clone()))
    } else {
        Box::new(Type::Bag(str_t.clone()))
    };
    let exp = call2(tabulate, count, fn_expr, coll_t);

    let mut free = free_names_in(s);
    free.remove(pat_name);

    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Finite,
        free,
        true,
        true,
        vec![source_constraint.clone()],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

// ---------------------------------------------------------------------------
// Complex strategies
// ---------------------------------------------------------------------------

/// Recognises a constraint of the form
/// `exists s1 in c1 [, s2 in c2, ...] where pred`
/// (which morel-rust resolves to a `From` whose last step is
/// `StepKind::Exists`). When the inner `where` predicate, combined
/// with the outer constraints, yields a generator for `pat` whose
/// free patterns include any inner scan-pat, we wrap the inner
/// scans around the inner generator and yield `pat` with `distinct`.
///
/// Example: `from p where (exists s in ["abcd","ant"] where
/// String.isPrefix p s)` becomes
/// `from s in ["abcd","ant"]
///   join p in Bag.tabulate(String.size s + 1,
///                          fn i => String.substring(s, 0, i))
///   yield p distinct`.
fn maybe_exists(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    use crate::compile::core::{Step, StepEnv, StepKind};

    for (idx, c) in constraints.iter().enumerate() {
        let Expr::From(from_t, steps) = c else {
            continue;
        };
        // Last step must be `Exists` for this to be an
        // `exists` expression.
        if !matches!(steps.last().map(|s| &s.kind), Some(StepKind::Exists)) {
            continue;
        }

        // Drop the trailing Exists; collect inner scans and
        // where-conjuncts.
        let inner_steps = &steps[..steps.len() - 1];
        let mut inner_scans: Vec<Step> = Vec::new();
        let mut inner_conjuncts: Vec<Expr> = Vec::new();
        for s in inner_steps {
            match &s.kind {
                StepKind::Scan(_, _, _) => inner_scans.push(s.clone()),
                StepKind::Where(cond) => {
                    inner_conjuncts.extend(split_conjuncts(cond));
                }
                _ => {} // skip yields, groups, orders, etc. — Phase 3a is
                        // intentionally narrow.
            }
        }

        // Build the augmented constraint set: outer minus this
        // exists, plus inner conjuncts.
        let mut augmented: Vec<Expr> =
            Vec::with_capacity(constraints.len() - 1 + inner_conjuncts.len());
        for (j, oc) in constraints.iter().enumerate() {
            if j != idx {
                augmented.push(oc.clone());
            }
        }
        augmented.extend(inner_conjuncts);

        // Try to derive a generator from the augmented set, into
        // a temporary cache so we can inspect the result before
        // adding to the real cache.
        let mut probe = Cache::new();
        if !maybe_generator(
            &mut probe, pat, pat_name, pat_type, ordered, &augmented, fn_env,
            datatypes,
        ) {
            continue;
        }
        let inner_gen = match probe.best(pat_name) {
            Some(g) => g.clone(),
            None => continue,
        };

        // Find inner scans that bind any of the generator's free
        // patterns. If none, the generator stands on its own and
        // we can just promote it.
        let inner_names: BTreeSet<String> = inner_scans
            .iter()
            .filter_map(|s| match &s.kind {
                StepKind::Scan(p, _, _) => match p.as_ref() {
                    Pat::Identifier(_, n) => Some(n.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let needed: Vec<&Step> = inner_scans
            .iter()
            .filter(|s| {
                if let StepKind::Scan(p, _, _) = &s.kind
                    && let Pat::Identifier(_, n) = p.as_ref()
                {
                    inner_gen.free_pats.contains(n)
                } else {
                    false
                }
            })
            .collect();

        if needed.is_empty() {
            // The generator doesn't depend on the inner scans;
            // just promote it.
            cache.add(pat_name.to_string(), inner_gen);
            return true;
        }

        // Wrap: build `from <needed-scans> join pat in inner_gen.exp
        //        yield pat distinct`.
        let elem_t = pat.type_();
        let coll_t = if ordered {
            Box::new(Type::List(elem_t.clone()))
        } else {
            Box::new(Type::Bag(elem_t.clone()))
        };
        let mut new_steps: Vec<Step> = Vec::new();
        for s in &needed {
            new_steps.push((*s).clone());
        }
        // join pat in inner_gen.exp
        let scan_env = StepEnv::new(
            vec![Binding::new(Id::new(pat_name, 0), elem_t.clone())],
            true,
            ordered,
        );
        new_steps.push(Step::new(
            StepKind::Scan(
                Box::new(pat.clone()),
                Box::new(inner_gen.exp.clone()),
                None,
            ),
            scan_env.clone(),
        ));
        // yield pat
        new_steps.push(Step::new(
            StepKind::Yield(Box::new(Expr::Identifier(
                elem_t.clone(),
                pat_name.to_string(),
            ))),
            scan_env.clone(),
        ));
        // distinct
        new_steps.push(Step::new(StepKind::Distinct, scan_env));

        let exp = Expr::From(coll_t, new_steps);

        let mut free = inner_gen.free_pats.clone();
        for n in &inner_names {
            free.remove(n);
        }
        let provenance = vec![c.clone()];
        let unsealed = Generator::new(
            pat.clone(),
            exp,
            Cardinality::Finite,
            free,
            false, // not unique — distinct handles dedup
            false, // unsealed: composite
            provenance,
        );
        cache.add(pat_name.to_string(), unsealed);
        // Suppress unused `from_t` warning (the type is implicit
        // in the new wrap).
        let _ = from_t;
        return true;
    }
    false
}

/// Recognises a constraint of the form `f arg` where `f` is a let-
/// bound single-argument function (i.e. `val rec f = fn p => body`).
/// Inlines the body with `p` substituted by `arg`, expands any
/// resulting `andalso` into multiple conjuncts, and recursively
/// runs `maybe_generator` on the augmented constraint set.
///
/// A small "in-progress" stack guards against infinite inlining
/// of recursive functions; recursion stays unsupported in Phase 3
/// (it lands in 3ec81171 / Phase 7).
fn maybe_function(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    if fn_env.is_empty() {
        return false;
    }
    for (idx, c) in constraints.iter().enumerate() {
        // Recognise both the inlined form (`Apply(Literal(Fn(_)),
        // arg)`, which doesn't apply here) and the un-inlined
        // identifier form: `Apply(Identifier(name), arg)`.
        let Expr::Apply(_, f, arg, _) = c else {
            continue;
        };
        let Expr::Identifier(_, fn_name) = f.as_ref() else {
            continue;
        };
        let Some((param_pat, body)) = fn_env.get(fn_name) else {
            continue;
        };
        // Build the substitution map. `fn x => body` substitutes
        // `x → arg`. `fn (a, b) => body` substitutes `a → arg.0`,
        // `b → arg.1` if `arg` is a literal tuple expression of
        // matching arity; otherwise we'd need a record-selector
        // application (or a let-in to materialise the tuple
        // once), which we don't bother with here.
        let mut subst_map: HashMap<String, Expr> = HashMap::new();
        match param_pat {
            Pat::Identifier(_, param_name) => {
                subst_map.insert(param_name.clone(), (**arg).clone());
            }
            Pat::Tuple(_, sub_pats) => {
                let Expr::Tuple(_, arg_elems) = arg.as_ref() else {
                    continue;
                };
                if sub_pats.len() != arg_elems.len() {
                    continue;
                }
                let mut ok = true;
                for (sp, ae) in sub_pats.iter().zip(arg_elems.iter()) {
                    if let Pat::Identifier(_, n) = sp {
                        subst_map.insert(n.clone(), ae.clone());
                    } else {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }
            }
            _ => continue,
        };
        let inlined = substitute(body, &subst_map);
        // Decompose `andalso`; merge with the rest of the outer
        // constraints.
        let inner_conjuncts = split_conjuncts(&inlined);
        let mut augmented: Vec<Expr> =
            Vec::with_capacity(constraints.len() - 1 + inner_conjuncts.len());
        for (j, oc) in constraints.iter().enumerate() {
            if j != idx {
                augmented.push(oc.clone());
            }
        }
        augmented.extend(inner_conjuncts);

        // Probe with a fresh cache so we don't pollute on failure.
        let mut probe = Cache::new();
        // Pass an env *without* this fn so we don't recurse on it.
        let mut env2 = fn_env.clone();
        env2.remove(fn_name);
        if !maybe_generator(
            &mut probe, pat, pat_name, pat_type, ordered, &augmented, &env2,
            datatypes,
        ) {
            continue;
        }
        let mut inner_gen = match probe.best(pat_name) {
            Some(g) => g.clone(),
            None => continue,
        };

        // Identify inlined conjuncts that the chosen leaf strategy
        // didn't fold into `inner_gen.exp`. They came from the
        // function body and aren't visible in any surrounding
        // `where` step, so without an explicit row filter they'd
        // be silently dropped. Attach the AND of unconsumed inner
        // conjuncts as `extra_filter`; the rebuild emits it as
        // the Scan's per-row condition.
        let inner_conjuncts2 = split_conjuncts(&inlined);
        let unconsumed: Vec<Expr> = inner_conjuncts2
            .into_iter()
            .filter(|ic| !inner_gen.provenance.iter().any(|p| expr_eq(p, ic)))
            .collect();
        if !unconsumed.is_empty() {
            let combined = and_all(unconsumed);
            inner_gen.extra_filter =
                Some(match inner_gen.extra_filter.take() {
                    Some(existing) => and_all(vec![existing, combined]),
                    None => combined,
                });
        }

        // Add the original function-call conjunct to provenance so
        // the surrounding `where` can drop it.
        inner_gen.provenance.push(c.clone());
        cache.add(pat_name.to_string(), inner_gen);
        return true;
    }
    false
}

/// Recognises a constraint of the form `case e of …` and, when
/// possible, derives a generator for the unbounded pattern.
///
/// Phase 4 handled the single-arm case (`case e of name => body`).
/// Phase 5 extends to:
///   * multi-arm with literal-pattern → `true` arms (collect the
///     literals into an elem-generator), and
///   * single arm with id-pattern + body referencing the rebound
///     identifier (carried over from Phase 4).
///
/// Mixed-shape multi-arm (literal arms + a variable-arm with a
/// non-trivial condition) needs a union strategy and lands in
/// Phase 6's maybeUnion.
fn maybe_case(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    for (idx, c) in constraints.iter().enumerate() {
        let Expr::Case(_, subject, arms, _) = c else {
            continue;
        };

        // 4a: single-arm case `case e of name => body` rebinds the
        // subject to `name` inside `body`.
        if arms.len() == 1
            && let Some(name) = arm_id_pat(&arms[0])
        {
            let mut subst_map: HashMap<String, Expr> = HashMap::new();
            subst_map.insert(name, (**subject).clone());
            let inlined = substitute(&arms[0].expr, &subst_map);
            let inner_conjuncts = split_conjuncts(&inlined);
            if try_recurse(
                cache,
                pat,
                pat_name,
                pat_type,
                ordered,
                constraints,
                idx,
                &inner_conjuncts,
                fn_env,
                datatypes,
                c,
            ) {
                return true;
            }
            continue;
        }

        // 5a: build a per-arm constraint and combine with `orelse`.
        // Each arm contributes:
        //   * literal pattern + body=`true`  ⇒  `subject = lit`
        //   * literal pattern + body=`false` ⇒  no contribution
        //   * id pattern + body              ⇒  `body[id := subject]`
        //   * wildcard + body=`false`        ⇒  no contribution (terminal
        //                                          no-match arm)
        // (Constructor patterns and exclusion-constraints from
        // false-arms are deferred to a later phase.)
        let Some(or_expr) = arms_to_orelse(subject, arms) else {
            continue;
        };
        if try_recurse(
            cache,
            pat,
            pat_name,
            pat_type,
            ordered,
            constraints,
            idx,
            &[or_expr],
            fn_env,
            datatypes,
            c,
        ) {
            return true;
        }
    }
    false
}

/// Builds an `orelse`-chained boolean expression from a list of
/// case arms. Returns `None` if any arm is in a shape we don't yet
/// know how to invert (constructor pattern, tuple pattern, etc.).
fn arms_to_orelse(subject: &Expr, arms: &[Match]) -> Option<Expr> {
    let mut branches: Vec<Expr> = Vec::with_capacity(arms.len());
    for arm in arms {
        match (&arm.pat, &arm.expr) {
            (Pat::Literal(t, v), body) => {
                let lit = Expr::Literal(t.clone(), v.clone());
                let eq = make_eq_for_type(t, subject.clone(), lit);
                if let Expr::Literal(_, Val::Bool(true)) = body {
                    branches.push(eq);
                } else if let Expr::Literal(_, Val::Bool(false)) = body {
                    // No contribution (and an exclusion constraint
                    // should be added to subsequent arms — we don't
                    // yet do that).
                } else {
                    return None;
                }
            }
            (Pat::Identifier(_, name), body) => {
                if let Expr::Literal(_, Val::Bool(false)) = body {
                    // Terminal "no-match" arm; contributes nothing.
                    continue;
                }
                let mut subst_map: HashMap<String, Expr> = HashMap::new();
                subst_map.insert(name.clone(), subject.clone());
                let body2 = substitute(body, &subst_map);
                branches.push(body2);
            }
            (Pat::Wildcard(_), body) => {
                if let Expr::Literal(_, Val::Bool(false)) = body {
                    // Terminal no-match arm.
                    continue;
                }
                // A `_ => non-false` body would always match — we'd
                // need to enumerate the subject's type to handle it.
                // Skip for now.
                return None;
            }
            _ => return None,
        }
    }
    if branches.is_empty() {
        return None;
    }
    let mut iter = branches.into_iter();
    let first = iter.next().unwrap();
    Some(iter.fold(first, make_orelse))
}

fn make_eq_for_type(t: &Type, lhs: Expr, rhs: Expr) -> Expr {
    let bool_t = Box::new(Type::Primitive(PrimitiveType::Bool));
    let arg_t = Box::new(Type::Tuple(vec![(*t).clone(), (*t).clone()]));
    let f = match t {
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::Real) => BuiltInFunction::RealEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        _ => BuiltInFunction::GEq,
    };
    let fn_t = Box::new(Type::Fn(arg_t.clone(), bool_t.clone()));
    let fn_lit = Expr::Literal(fn_t, Val::Fn(f));
    let arg = Expr::Tuple(arg_t, vec![lhs, rhs]);
    Expr::Apply(bool_t, Box::new(fn_lit), Box::new(arg), Span::new(""))
}

fn make_orelse(lhs: Expr, rhs: Expr) -> Expr {
    let bool_t = Box::new(Type::Primitive(PrimitiveType::Bool));
    let pair_t =
        Box::new(Type::Tuple(vec![(*bool_t).clone(), (*bool_t).clone()]));
    let fn_t = Box::new(Type::Fn(pair_t.clone(), bool_t.clone()));
    let fn_lit = Expr::Literal(fn_t, Val::Fn(BuiltInFunction::BoolOrElse));
    let arg = Expr::Tuple(pair_t, vec![lhs, rhs]);
    Expr::Apply(bool_t, Box::new(fn_lit), Box::new(arg), Span::new(""))
}

/// Helper: re-runs `maybe_generator` with `replacements` substituted
/// for the constraint at index `idx`, then promotes the generator
/// (if any) into the real `cache` after adding the original
/// constraint to its provenance.
#[allow(clippy::too_many_arguments)]
fn try_recurse(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    skip_idx: usize,
    replacements: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    original: &Expr,
) -> bool {
    let mut augmented: Vec<Expr> =
        Vec::with_capacity(constraints.len() - 1 + replacements.len());
    for (j, oc) in constraints.iter().enumerate() {
        if j != skip_idx {
            augmented.push(oc.clone());
        }
    }
    augmented.extend(replacements.iter().cloned());
    let mut probe = Cache::new();
    if !maybe_generator(
        &mut probe, pat, pat_name, pat_type, ordered, &augmented, fn_env,
        datatypes,
    ) {
        return false;
    }
    let mut inner_gen = match probe.best(pat_name) {
        Some(g) => g.clone(),
        None => return false,
    };
    inner_gen.provenance.push(original.clone());
    cache.add(pat_name.to_string(), inner_gen);
    true
}

/// If a single-arm match is `name => body`, returns `name`.
fn arm_id_pat(m: &Match) -> Option<String> {
    if let Pat::Identifier(_, n) = &m.pat {
        Some(n.clone())
    } else {
        None
    }
}

/// Recognises a constraint of the form
///   `branch_1 orelse branch_2 [orelse branch_3 ...]`
/// (decomposed via the BoolOrElse builtin), derives a generator
/// for each branch by recursing `maybe_generator` with that
/// branch as the only constraint, and concatenates the resulting
/// expressions with `Bag.concat`/`List.concat`.
///
/// The combined generator is unsealed: it doesn't subsume any
/// individual branch as a where-conjunct (the surrounding `where`
/// will keep the original `orelse` for correctness).
/// Recognises a constraint `{f1=v1, …, fk=pat_name, …} elem coll`
/// where one tuple/record component is `pat_name` and the
/// others are literals or outer-scope identifiers (free
/// variables not bound by any from-step in this query). Builds
/// a generator that scans `coll`, filters on the literal /
/// outer-bound components, and projects the `pat_name`
/// component. Used for queries like
///
///   exists price where {bar="cask", beer=b, price=price}
///                       elem barBeers
///
/// where `b` is a function parameter (outer-scope) and
/// `price` is the unbounded variable.
fn maybe_record_elem_projection(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    _pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    outer_scope: &BTreeSet<String>,
) -> bool {
    for c in constraints {
        let Some((lhs, rhs)) = call2_args(c, &[BuiltInFunction::ListElem])
        else {
            continue;
        };
        // lhs must be a tuple/record with exactly one
        // component that's `Identifier(pat_name)` and all
        // other components either literals or non-pat-name
        // identifiers (assumed outer-scope).
        let Expr::Tuple(tuple_t, ids) = lhs else {
            continue;
        };
        // Field labels in alphabetical order from the type.
        let labels: Vec<String> = match tuple_t.as_ref() {
            Type::Record(_, fields) => fields
                .keys()
                .filter_map(|l| match l {
                    Label::String(n) => Some(n.clone()),
                    _ => None,
                })
                .collect(),
            Type::Tuple(_) => {
                // Position-indexed labels "1", "2", …
                (1..=ids.len()).map(|i| i.to_string()).collect()
            }
            _ => continue,
        };
        if labels.len() != ids.len() {
            continue;
        }
        let mut pat_field: Option<String> = None;
        let mut filters: Vec<(String, Expr)> = Vec::new();
        let mut ok = true;
        for (label, id) in labels.iter().zip(ids.iter()) {
            match id {
                Expr::Identifier(_, n) if n == pat_name => {
                    if pat_field.is_some() {
                        // Multiple components claim pat_name —
                        // skip; let decompose handle it.
                        ok = false;
                        break;
                    }
                    pat_field = Some(label.clone());
                }
                Expr::Identifier(_, n) => {
                    // Only treat as filter if the name is known
                    // to be in outer scope (function parameter,
                    // let-bound val, …). Names not in
                    // outer_scope are likely from-step extents
                    // that `decompose_tuple_elems` should handle.
                    if !outer_scope.contains(n) {
                        ok = false;
                        break;
                    }
                    filters.push((label.clone(), id.clone()));
                }
                Expr::Literal(_, _) => {
                    filters.push((label.clone(), id.clone()));
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let Some(pat_field) = pat_field else {
            continue;
        };

        // Build: from r in coll where r.f1 = v1 andalso …
        //        yield #pat_field r
        use crate::compile::core::{Step, StepEnv, StepKind};
        use crate::compile::type_env::Id;

        let row_t = match tuple_t.as_ref() {
            Type::Record(prog, fields) => {
                Box::new(Type::Record(*prog, fields.clone()))
            }
            _ => continue,
        };
        let bool_t = Box::new(Type::Primitive(PrimitiveType::Bool));
        let row_var = "__rep$".to_string();
        let scan_env = StepEnv::new(
            vec![Binding::new(Id::new(&row_var, 0), row_t.clone())],
            true,
            ordered,
        );
        let mut steps: Vec<Step> = Vec::new();
        steps.push(Step::new(
            StepKind::Scan(
                Box::new(Pat::Identifier(row_t.clone(), row_var.clone())),
                Box::new(rhs.clone()),
                None,
            ),
            scan_env.clone(),
        ));
        // Build filter conditions: r.f = v.
        if !filters.is_empty() {
            let filter_exprs: Vec<Expr> = filters
                .iter()
                .map(|(label, value_expr)| {
                    let field_t = match tuple_t.as_ref() {
                        Type::Record(_, fields) => fields
                            .get(&Label::String(label.clone()))
                            .cloned()
                            .map(Box::new),
                        _ => None,
                    };
                    let Some(field_t) = field_t else {
                        return Expr::Literal(bool_t.clone(), Val::Bool(false));
                    };
                    let slot = match tuple_t.as_ref() {
                        Type::Record(_, fields) => fields
                            .keys()
                            .position(
                                |l| matches!(l, Label::String(n) if n == label),
                            )
                            .unwrap(),
                        _ => 0,
                    };
                    let sel_fn_t =
                        Box::new(Type::Fn(row_t.clone(), field_t.clone()));
                    let sel = Expr::RecordSelector(sel_fn_t.clone(), slot);
                    let r_id = Expr::Identifier(row_t.clone(), row_var.clone());
                    let lhs_field = Expr::Apply(
                        field_t.clone(),
                        Box::new(sel),
                        Box::new(r_id),
                        Span::new(""),
                    );
                    make_eq_for_type(&field_t, lhs_field, value_expr.clone())
                })
                .collect();
            let cond = and_all(filter_exprs);
            steps.push(Step::new(
                StepKind::Where(Box::new(cond)),
                scan_env.clone(),
            ));
        }
        // Build the projection: `#pat_field r` (a record selector).
        let pat_field_t = match tuple_t.as_ref() {
            Type::Record(_, fields) => {
                match fields.get(&Label::String(pat_field.clone())).cloned() {
                    Some(t) => Box::new(t),
                    None => continue,
                }
            }
            _ => continue,
        };
        let pat_field_slot = match tuple_t.as_ref() {
            Type::Record(_, fields) => fields
                .keys()
                .position(|l| matches!(l, Label::String(n) if n == &pat_field))
                .unwrap(),
            _ => 0,
        };
        let sel_fn_t = Box::new(Type::Fn(row_t.clone(), pat_field_t.clone()));
        let sel = Expr::RecordSelector(sel_fn_t, pat_field_slot);
        let r_id = Expr::Identifier(row_t.clone(), row_var.clone());
        let yield_expr = Expr::Apply(
            pat_field_t.clone(),
            Box::new(sel),
            Box::new(r_id),
            Span::new(""),
        );
        let yield_env = StepEnv::new(
            vec![Binding::new(Id::new(pat_name, 0), pat_field_t.clone())],
            true,
            ordered,
        );
        steps.push(Step::new(StepKind::Yield(Box::new(yield_expr)), yield_env));
        let coll_t = if ordered {
            Box::new(Type::List(pat_field_t.clone()))
        } else {
            Box::new(Type::Bag(pat_field_t.clone()))
        };
        let exp = Expr::From(coll_t, steps);

        let mut free = free_names_in(&exp);
        free.remove(pat_name);
        let generator = Generator::new(
            pat.clone(),
            exp,
            Cardinality::Finite,
            free,
            true,
            true,
            vec![c.clone()],
        );
        cache.add(pat_name.to_string(), generator);
        return true;
    }
    false
}

/// Recognises a `case` constraint whose subject is the pattern
/// we're trying to ground, and whose arms include constructor
/// patterns (e.g. `INL n => n >= 5 andalso n <= 8`). For each
/// constructor arm we derive a generator for the sub-pattern
/// from the arm's body, then wrap the generator's exp with
/// the constructor (`Bag.map (fn x => INL x) <inner>`). All
/// arms' results are union'd via `Bag.concat` (or
/// `List.concat` for ordered scope).
///
/// Wildcard / nullary-constructor / `_ => false` arms
/// contribute nothing; an arm with a non-bool body and a non-
/// invertible sub-constraint causes us to skip the whole case.
fn maybe_case_constructor(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    _pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    for c in constraints {
        let Expr::Case(_, subject, arms, _) = c else {
            continue;
        };
        let Expr::Identifier(_, sn) = subject.as_ref() else {
            continue;
        };
        if sn != pat_name {
            continue;
        }
        // At least one constructor arm with a non-`false` body.
        let has_constructor_arm = arms.iter().any(|a| {
            matches!(a.pat, Pat::Constructor(_, _, _))
                && !matches!(a.expr, Expr::Literal(_, Val::Bool(false)))
        });
        if !has_constructor_arm {
            continue;
        }

        let mut branch_exps: Vec<Expr> = Vec::new();
        let all_free: BTreeSet<String> = BTreeSet::new();
        let mut ok = true;
        for arm in arms {
            // Skip false-body arms.
            if matches!(arm.expr, Expr::Literal(_, Val::Bool(false))) {
                continue;
            }
            match &arm.pat {
                Pat::Constructor(_ctor_t, ctor_name, Some(sub_pat)) => {
                    let Some(ctor_fn) = constructor_to_builtin(ctor_name)
                    else {
                        ok = false;
                        break;
                    };
                    let elem_t = pat.type_();
                    let sub_t = sub_pat.type_();
                    let Some((sub_pat_name, sub_exp)) =
                        derive_payload_generator(
                            sub_pat, &arm.expr, ordered, fn_env, datatypes,
                        )
                    else {
                        ok = false;
                        break;
                    };
                    let wrapped = build_map_constructor(
                        ctor_fn,
                        sub_t,
                        elem_t,
                        sub_pat_name,
                        sub_exp,
                        ordered,
                    );
                    branch_exps.push(wrapped);
                }
                // Constant constructor `Pat::Constructor(_, ctor, None)`
                // with non-false body: support `body == true` only —
                // the constructor's single value is a member.
                Pat::Constructor(_, _, None) => {
                    // Not yet supported.
                    ok = false;
                    break;
                }
                Pat::Wildcard(_) => {
                    // Already filtered false bodies above; a non-false
                    // wildcard body would always match — needs
                    // enumeration of subject's type.
                    ok = false;
                    break;
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok || branch_exps.is_empty() {
            continue;
        }

        // Build `Bag.concat [b1, b2, ...]` (or List.concat).
        let elem_t = pat.type_();
        let coll_t = if ordered {
            Box::new(Type::List(elem_t.clone()))
        } else {
            Box::new(Type::Bag(elem_t.clone()))
        };
        let combined = if branch_exps.len() == 1 {
            branch_exps.into_iter().next().unwrap()
        } else {
            let list_of_coll_t =
                Box::new(Type::List(Box::new((*coll_t).clone())));
            let arg_list = Expr::List(list_of_coll_t.clone(), branch_exps);
            let concat_fn = if ordered {
                BuiltInFunction::ListConcat
            } else {
                BuiltInFunction::BagConcat
            };
            let fn_t = Box::new(Type::Fn(list_of_coll_t, coll_t.clone()));
            let fn_lit = Expr::Literal(fn_t, Val::Fn(concat_fn));
            Expr::Apply(
                coll_t,
                Box::new(fn_lit),
                Box::new(arg_list),
                Span::new(""),
            )
        };

        let generator = Generator::new(
            pat.clone(),
            combined,
            Cardinality::Finite,
            all_free,
            false,
            false,
            vec![c.clone()],
        );
        cache.add(pat_name.to_string(), generator);
        return true;
    }
    false
}

/// Builds a generator for the payload of a constructor arm:
/// returns `(bind_name, exp)` where `exp` is a list/bag of
/// payload values and `bind_name` is the name to use in the
/// `Bag.map (fn bind_name => CTOR bind_name)` wrapping.
///
/// For a Pat::Identifier sub-pattern the bind_name is the
/// identifier itself and `exp` comes from `maybe_generator`
/// on the body.
///
/// For a Pat::Tuple sub-pattern (e.g. `INR (b, i)`) we build
/// a synthetic `from b, i where <body> yield (b, i)` query,
/// expand it with predicate inversion, and use a fresh
/// bind_name for the wrapping fn (the map argument will be
/// the whole tuple).
fn derive_payload_generator(
    sub_pat: &Pat,
    body: &Expr,
    ordered: bool,
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Option<(String, Expr)> {
    match sub_pat {
        Pat::Identifier(t, n) => {
            let inner_constraints = split_conjuncts(body);
            let mut probe = Cache::new();
            if !maybe_generator(
                &mut probe,
                sub_pat,
                n,
                t,
                ordered,
                &inner_constraints,
                fn_env,
                datatypes,
            ) {
                return None;
            }
            let g = probe.best(n)?;
            Some((n.clone(), g.exp.clone()))
        }
        // Literal sub-pat (e.g. `INL 0`) — only contributes when
        // the body is `true`; one element list.
        Pat::Literal(lit_t, v) => {
            if !matches!(body, Expr::Literal(_, Val::Bool(true))) {
                return None;
            }
            let elem = Expr::Literal(lit_t.clone(), v.clone());
            let coll_t = if ordered {
                Box::new(Type::List(lit_t.clone()))
            } else {
                Box::new(Type::Bag(lit_t.clone()))
            };
            // `[lit]` as a List value; bags are formed at the
            // outer concat layer if needed.
            let list_t = Box::new(Type::List(lit_t.clone()));
            let list_lit = Expr::List(list_t.clone(), vec![elem]);
            // For bag scope, wrap with `Bag.fromList`-equivalent —
            // but our concat happily mixes lists into bags via
            // the type system. Keep as List for simplicity; the
            // outer bag-concat will treat it as elements.
            let _ = coll_t;
            Some(("__lit".to_string(), list_lit))
        }
        Pat::Tuple(tuple_t, sub_pats) => {
            // Build `from <each leaf> where body yield (leaves)`
            // and let `expand_from_with` derive the generators.
            use crate::compile::core::{Step, StepEnv, StepKind};
            use crate::compile::expander::expand_from_with;
            use crate::compile::type_env::Id;

            let mut steps: Vec<Step> = Vec::new();
            let mut leaves: Vec<(String, Box<Type>)> = Vec::new();
            for sp in sub_pats {
                let (n, t) = match sp {
                    Pat::Identifier(t, n) => (n.clone(), t.clone()),
                    _ => return None,
                };
                leaves.push((n.clone(), t.clone()));
                let scan_env = StepEnv::new(
                    leaves
                        .iter()
                        .map(|(n, t)| Binding::new(Id::new(n, 0), t.clone()))
                        .collect(),
                    leaves.len() == 1,
                    ordered,
                );
                steps.push(Step::new(
                    StepKind::Scan(
                        Box::new(Pat::Identifier(t.clone(), n)),
                        Box::new(Expr::Extent(t.clone(), Span::new(""))),
                        None,
                    ),
                    scan_env,
                ));
            }
            let last_env = steps.last().unwrap().env.clone();
            steps.push(Step::new(
                StepKind::Where(Box::new(body.clone())),
                last_env.clone(),
            ));
            // Yield the tuple in original sub-pattern order.
            let yield_items: Vec<Expr> = sub_pats
                .iter()
                .map(|sp| match sp {
                    Pat::Identifier(t, n) => {
                        Expr::Identifier(t.clone(), n.clone())
                    }
                    _ => unreachable!(),
                })
                .collect();
            let yield_expr = Expr::Tuple(tuple_t.clone(), yield_items);
            // After the yield the from result is `tuple_t bag`.
            let yield_env = StepEnv::new(
                vec![Binding::new(Id::new("__pl", 0), tuple_t.clone())],
                true,
                ordered,
            );
            steps.push(Step::new(
                StepKind::Yield(Box::new(yield_expr)),
                yield_env,
            ));
            let coll_t = if ordered {
                Box::new(Type::List(tuple_t.clone()))
            } else {
                Box::new(Type::Bag(tuple_t.clone()))
            };
            let from = Expr::From(coll_t, steps);
            let expanded = expand_from_with(from, fn_env, datatypes);
            // If predicate-inversion left an Extent in the
            // expanded steps, we couldn't ground a sub-pattern;
            // bail.
            if let Expr::From(_, ref est) = expanded
                && est.iter().any(|s| {
                    matches!(
                        &s.kind,
                        StepKind::Scan(_, src, _) if matches!(
                            src.as_ref(), Expr::Extent(_, _)
                        )
                    )
                })
            {
                return None;
            }
            Some(("__pl".to_string(), expanded))
        }
        _ => None,
    }
}

/// Maps a constructor name to its `BuiltInFunction` value.
/// Returns `None` for user-defined or unsupported constructors.
fn constructor_to_builtin(name: &str) -> Option<BuiltInFunction> {
    match name {
        "INL" => Some(BuiltInFunction::EitherInl),
        "INR" => Some(BuiltInFunction::EitherInr),
        "SOME" => Some(BuiltInFunction::OptionSome),
        _ => None,
    }
}

/// Builds `Bag.map (fn x => CTOR x) inner` (or List.map for
/// ordered scope), wrapping every payload in `inner` with the
/// given constructor.
#[allow(clippy::needless_pass_by_value)]
fn build_map_constructor(
    ctor_fn: BuiltInFunction,
    payload_t: Box<Type>,
    elem_t: Box<Type>,
    sub_pat_name: String,
    inner: Expr,
    ordered: bool,
) -> Expr {
    let coll_t = if ordered {
        Box::new(Type::List(elem_t.clone()))
    } else {
        Box::new(Type::Bag(elem_t.clone()))
    };
    let inner_coll_t = if ordered {
        Box::new(Type::List(payload_t.clone()))
    } else {
        Box::new(Type::Bag(payload_t.clone()))
    };
    // `fn x => CTOR x`
    let ctor_fn_t = Box::new(Type::Fn(payload_t.clone(), elem_t.clone()));
    let ctor_lit = Expr::Literal(ctor_fn_t.clone(), Val::Fn(ctor_fn));
    let body = Expr::Apply(
        elem_t.clone(),
        Box::new(ctor_lit),
        Box::new(Expr::Identifier(payload_t.clone(), sub_pat_name.clone())),
        Span::new(""),
    );
    let fn_pat = Pat::Identifier(payload_t.clone(), sub_pat_name);
    let map_arg_fn_t = Box::new(Type::Fn(payload_t.clone(), elem_t.clone()));
    let map_arg = Expr::Fn(
        map_arg_fn_t.clone(),
        vec![Match {
            pat: fn_pat,
            expr: body,
        }],
        Span::new(""),
    );
    // `Bag.map`-curried: Apply(Apply(map_fn, fn_arg), inner)
    let map_builtin = if ordered {
        BuiltInFunction::ListMap
    } else {
        BuiltInFunction::BagMap
    };
    let map_t = Box::new(Type::Fn(
        map_arg_fn_t,
        Box::new(Type::Fn(inner_coll_t.clone(), coll_t.clone())),
    ));
    let map_lit = Expr::Literal(map_t, Val::Fn(map_builtin));
    let map_partial_t = Box::new(Type::Fn(inner_coll_t, coll_t.clone()));
    let map_partial = Expr::Apply(
        map_partial_t,
        Box::new(map_lit),
        Box::new(map_arg),
        Span::new(""),
    );
    Expr::Apply(
        coll_t,
        Box::new(map_partial),
        Box::new(inner),
        Span::new(""),
    )
}

fn maybe_union(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    for c in constraints {
        let branches = split_orelse(c);
        if branches.len() < 2 {
            continue;
        }
        let mut sub_gens: Vec<Generator> = Vec::with_capacity(branches.len());
        let mut all_ok = true;
        for branch in &branches {
            // Split each branch into its top-level `andalso`
            // conjuncts so leaf strategies see e.g. `i > 0` and
            // `i < 10` as separate constraints.
            let branch_conjuncts = split_conjuncts(branch);
            let mut probe = Cache::new();
            if !maybe_generator(
                &mut probe,
                pat,
                pat_name,
                pat_type,
                ordered,
                &branch_conjuncts,
                fn_env,
                datatypes,
            ) {
                all_ok = false;
                break;
            }
            if let Some(g) = probe.best(pat_name) {
                sub_gens.push(g.clone());
            } else {
                all_ok = false;
                break;
            }
        }
        if !all_ok {
            continue;
        }

        // Build `Bag.concat [g1.exp, g2.exp, ...]` (or
        // `List.concat …`).
        let elem_t = pat.type_();
        let coll_t = if ordered {
            Box::new(Type::List(elem_t.clone()))
        } else {
            Box::new(Type::Bag(elem_t.clone()))
        };
        let list_of_coll_t = Box::new(Type::List(Box::new((*coll_t).clone())));
        let exps: Vec<Expr> = sub_gens.iter().map(|g| g.exp.clone()).collect();
        let arg_list = Expr::List(list_of_coll_t.clone(), exps);
        let concat_fn = if ordered {
            BuiltInFunction::ListConcat
        } else {
            BuiltInFunction::BagConcat
        };
        let fn_t = Box::new(Type::Fn(list_of_coll_t, coll_t.clone()));
        let fn_lit = Expr::Literal(fn_t, Val::Fn(concat_fn));
        let exp = Expr::Apply(
            coll_t,
            Box::new(fn_lit),
            Box::new(arg_list),
            Span::new(""),
        );

        let mut free: BTreeSet<String> = BTreeSet::new();
        for g in &sub_gens {
            for n in &g.free_pats {
                free.insert(n.clone());
            }
        }

        let generator = Generator::new(
            pat.clone(),
            exp,
            Cardinality::Finite,
            free,
            false, // not unique — branches may overlap
            false, // unsealed: composite
            vec![c.clone()],
        );
        cache.add(pat_name.to_string(), generator);
        return true;
    }
    false
}

/// Flattens `a orelse b orelse c …` into `[a, b, c, …]`.
/// Returns a single-element list if `expr` isn't an orelse.
pub(crate) fn split_orelse(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    push_orelse(expr, &mut out);
    out
}

fn push_orelse(expr: &Expr, out: &mut Vec<Expr>) {
    if let Some((lhs, rhs)) = call2_args(expr, &[BuiltInFunction::BoolOrElse]) {
        push_orelse(lhs, out);
        push_orelse(rhs, out);
    } else {
        out.push(expr.clone());
    }
}

// ---------------------------------------------------------------------------
// Bound extraction
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Bound {
    bound: Expr,
    /// `true` for strict (`>`, `<`); `false` for inclusive (`>=`, `<=`).
    strict: bool,
}

fn is_bound_constraint(constraint: &Expr, pat_name: &str) -> bool {
    try_isolate_bound(constraint, pat_name).is_some()
}

/// Returns `(bound, strict)` for the pattern's lower bound, picking
/// the first matching constraint. Strict means `>` (exclusive).
fn lower_bound(pat_name: &str, constraints: &[Expr]) -> Option<Bound> {
    for c in constraints {
        if let Some((op, rhs)) = try_isolate_bound(c, pat_name)
            && (op == BuiltInFunction::IntGt || op == BuiltInFunction::IntGe)
        {
            return Some(Bound {
                bound: rhs,
                strict: op == BuiltInFunction::IntGt,
            });
        }
    }
    None
}

/// Returns `(bound, strict)` for the pattern's upper bound. Strict
/// means `<` (exclusive).
fn upper_bound(pat_name: &str, constraints: &[Expr]) -> Option<Bound> {
    for c in constraints {
        if let Some((op, rhs)) = try_isolate_bound(c, pat_name)
            && (op == BuiltInFunction::IntLt || op == BuiltInFunction::IntLe)
        {
            return Some(Bound {
                bound: rhs,
                strict: op == BuiltInFunction::IntLt,
            });
        }
    }
    None
}

/// Normalises a comparison constraint into the form `pat op expr`,
/// where `op` is one of the `Int{Lt,Le,Gt,Ge}` built-ins and
/// `expr` doesn't reference `pat_name`. Returns `None` if the
/// constraint isn't a comparison or `pat_name` doesn't appear in a
/// shape we can isolate.
///
/// Supported shapes (with `k` not referencing `pat_name`):
///   * `pat`              isolated already
///   * `pat + k` or `k + pat`  (subtract `k` from the other side)
///   * `pat - k`               (add `k` to the other side)
fn try_isolate_bound(
    c: &Expr,
    pat_name: &str,
) -> Option<(BuiltInFunction, Expr)> {
    let ops = [
        BuiltInFunction::IntGt,
        BuiltInFunction::IntGe,
        BuiltInFunction::IntLt,
        BuiltInFunction::IntLe,
    ];
    let (lhs, rhs, op) = call2_args_op(c, &ops)?;
    // Try lhs-side: `(pat ± k) op rhs` ⇒ `pat op (rhs ∓ k)`.
    if let Some(adj) = isolate_pat_offset(lhs, pat_name)
        && !free_names_in(rhs).contains(pat_name)
    {
        let new_rhs = apply_offset(rhs.clone(), adj);
        return Some((op, new_rhs));
    }
    // Try rhs-side: `lhs op (pat ± k)` ⇒ flip op, then move offset:
    // `lhs op (pat ± k)` ⇔ `(pat ± k) flip(op) lhs` ⇒
    //   `pat flip(op) (lhs ∓ k)`.
    if let Some(adj) = isolate_pat_offset(rhs, pat_name)
        && !free_names_in(lhs).contains(pat_name)
    {
        let flipped = match op {
            BuiltInFunction::IntLt => BuiltInFunction::IntGt,
            BuiltInFunction::IntLe => BuiltInFunction::IntGe,
            BuiltInFunction::IntGt => BuiltInFunction::IntLt,
            BuiltInFunction::IntGe => BuiltInFunction::IntLe,
            _ => return None,
        };
        let new_rhs = apply_offset(lhs.clone(), adj);
        return Some((flipped, new_rhs));
    }
    None
}

/// If `side` has the form `pat`, `pat + k`, `k + pat`, or `pat - k`
/// (with `k` not referencing `pat_name`), returns the offset `delta`
/// that, when added to *the other side* of the comparison, isolates
/// `pat`. `pat` alone gives `Some(IntLit(0))`. Returns `None` when
/// pat is missing or appears in a shape we can't invert (e.g. `k -
/// pat`, multiplication).
fn isolate_pat_offset(side: &Expr, pat_name: &str) -> Option<Expr> {
    if let Expr::Identifier(_, n) = side
        && n == pat_name
    {
        return Some(int_lit(0));
    }
    let (a, b, op) = call2_args_op(
        side,
        &[BuiltInFunction::IntPlus, BuiltInFunction::IntMinus],
    )?;
    let a_is_pat = matches!(a, Expr::Identifier(_, n) if n == pat_name);
    let b_is_pat = matches!(b, Expr::Identifier(_, n) if n == pat_name);
    match op {
        BuiltInFunction::IntPlus => {
            // pat + k: subtract k from the other side ⇒ delta = -k.
            if a_is_pat && !free_names_in(b).contains(pat_name) {
                return Some(negate_int(b.clone()));
            }
            // k + pat: same.
            if b_is_pat && !free_names_in(a).contains(pat_name) {
                return Some(negate_int(a.clone()));
            }
            None
        }
        BuiltInFunction::IntMinus => {
            // pat - k: add k to the other side ⇒ delta = +k.
            if a_is_pat && !free_names_in(b).contains(pat_name) {
                return Some(b.clone());
            }
            // k - pat: would require flipping the comparison; skip.
            None
        }
        _ => None,
    }
}

/// `expr + delta`, simplified when `delta` is the literal `0`.
fn apply_offset(expr: Expr, delta: Expr) -> Expr {
    if matches!(&delta, Expr::Literal(_, Val::Int(0))) {
        return expr;
    }
    binop_int(BuiltInFunction::IntPlus, expr, delta)
}

fn negate_int(expr: Expr) -> Expr {
    binop_int(BuiltInFunction::IntMinus, int_lit(0), expr)
}

// ---------------------------------------------------------------------------
// Core-expression helpers
// ---------------------------------------------------------------------------

/// Matches `Apply(_, Literal(Fn(f)), Tuple(_, [a, b]))` where `f` is
/// one of the built-ins in `ops`. Returns `(a, b)` on a match.
fn call2_args<'a>(
    expr: &'a Expr,
    ops: &[BuiltInFunction],
) -> Option<(&'a Expr, &'a Expr)> {
    call2_args_op(expr, ops).map(|(a, b, _)| (a, b))
}

fn call2_args_op<'a>(
    expr: &'a Expr,
    ops: &[BuiltInFunction],
) -> Option<(&'a Expr, &'a Expr, BuiltInFunction)> {
    if let Expr::Apply(_, f, arg, _) = expr
        && let Expr::Literal(_, Val::Fn(builtin)) = f.as_ref()
        && ops.contains(builtin)
        && let Expr::Tuple(_, args) = arg.as_ref()
        && args.len() == 2
    {
        return Some((&args[0], &args[1], *builtin));
    }
    None
}

/// True if `expr` is a direct reference to the pattern named `name`,
/// or contains it transitively. For now only the direct case is
/// handled — Phase 1 doesn't need offset detection.
fn references(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Identifier(_, n) if n == name)
}

/// If `expr` is `String.isPrefix p s` (curried, i.e.
/// `Apply(Apply(StringIsPrefix, p), s)`) where `p` references the
/// named pattern, returns `s`.
///
/// `String.isPrefix` may surface in either of two shapes depending
/// on whether the inliner has already lowered structure-field
/// access to a `Literal(Fn(...))`:
///
///   1. `Apply(Apply(Literal(Fn(StringIsPrefix)), p), s)`
///   2. `Apply(Apply(Apply(RecordSelector(_, slot),
///                         Identifier("String")), p), s)`
///
/// At the point the Expander runs (immediately after resolution,
/// before `inliner::inline_decl`), shape 2 is the common form;
/// shape 1 will appear once we move the Expander after inlining.
fn is_string_prefix_call<'a>(
    expr: &'a Expr,
    pat_name: &str,
) -> Option<&'a Expr> {
    let Expr::Apply(_, outer_fn, s, _) = expr else {
        return None;
    };
    let Expr::Apply(_, mid_fn, p, _) = outer_fn.as_ref() else {
        return None;
    };
    if !references(p, pat_name) {
        return None;
    }
    if as_builtin_fn(mid_fn) == Some(BuiltInFunction::StringIsPrefix) {
        return Some(s);
    }
    None
}

/// Resolves an expression to a built-in function, if it is one. Handles
/// both an inlined literal and a record-selector application against a
/// builtin structure (e.g. `Apply(RecordSelector(_, slot),
/// Identifier("String"))`).
fn as_builtin_fn(expr: &Expr) -> Option<BuiltInFunction> {
    match expr {
        Expr::Literal(_, Val::Fn(f)) => Some(*f),
        Expr::Apply(_, f, a, _) => {
            if let Expr::RecordSelector(t, slot) = f.as_ref()
                && let Expr::Identifier(_, struct_name) = a.as_ref()
                && let Type::Fn(record_t, _) = t.as_ref()
                && let Some(field_name) = record_t.field_name(*slot)
            {
                return lookup_struct_field(struct_name, field_name);
            }
            None
        }
        _ => None,
    }
}

/// Splits an `andalso`-rooted expression into its conjuncts. Anything
/// else is returned as a single-element vector.
pub fn split_conjuncts(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    push_conjuncts(expr, &mut out);
    out
}

fn push_conjuncts(expr: &Expr, out: &mut Vec<Expr>) {
    if let Some((lhs, rhs)) = call2_args(expr, &[BuiltInFunction::BoolAndAlso])
    {
        push_conjuncts(lhs, out);
        push_conjuncts(rhs, out);
    } else {
        out.push(expr.clone());
    }
}

// ---------------------------------------------------------------------------
// Mini Core builders — local to this module, intentionally narrow.
// ---------------------------------------------------------------------------

fn int_lit(n: i32) -> Expr {
    Expr::Literal(Box::new(Type::Primitive(PrimitiveType::Int)), Val::Int(n))
}

fn binop_int(f: BuiltInFunction, a: Expr, b: Expr) -> Expr {
    let int_t = Box::new(Type::Primitive(PrimitiveType::Int));
    let pair_t =
        Box::new(Type::Tuple(vec![(*int_t).clone(), (*int_t).clone()]));
    let fn_t = Box::new(Type::Fn(pair_t.clone(), int_t.clone()));
    let fn_expr = Expr::Literal(fn_t.clone(), Val::Fn(f));
    let arg = Expr::Tuple(pair_t, vec![a, b]);
    Expr::Apply(int_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
}

fn call1(f: BuiltInFunction, a: Expr, result_t: Box<Type>) -> Expr {
    let arg_t = a.type_();
    let fn_t = Box::new(Type::Fn(arg_t, result_t.clone()));
    let fn_expr = Expr::Literal(fn_t, Val::Fn(f));
    Expr::Apply(result_t, Box::new(fn_expr), Box::new(a), Span::new(""))
}

fn call2(f: BuiltInFunction, a: Expr, b: Expr, result_t: Box<Type>) -> Expr {
    let arg_t = Box::new(Type::Tuple(vec![
        (*a.type_()).clone(),
        (*b.type_()).clone(),
    ]));
    let fn_t = Box::new(Type::Fn(arg_t.clone(), result_t.clone()));
    let fn_expr = Expr::Literal(fn_t, Val::Fn(f));
    let arg = Expr::Tuple(arg_t, vec![a, b]);
    Expr::Apply(result_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
}

#[allow(dead_code)]
fn unused_warn() -> BTreeSet<String> {
    // Suppress an "unused import" warning until the BTreeSet usage
    // shows up in a follow-up phase. (free_names_in already returns
    // a BTreeSet, so we use it indirectly.)
    BTreeSet::new()
}
