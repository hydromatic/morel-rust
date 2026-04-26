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

//! Postfix method-call dispatch tables, shared between type
//! resolution and core resolution. See hydromatic/morel#346.
//!
//! The dispatch table is built once at startup by inspecting each
//! `BuiltInFunction`'s declared type signature. For every function
//! whose first parameter (or first curried argument) has a "known
//! receiver type" (`int`, `string`, `'a list`, `'a bag`, `time`,
//! `date`, `'a option`, `'a range`, `'a continuous_set`,
//! `'a discrete_set`, `vector`), an entry is added that lets
//! `recv.method args` rewrite to `Method.fn ...`.
//!
//! Adding a new built-in whose signature already names a known
//! receiver type at the right position requires no changes here —
//! the new function appears in the dispatch table automatically.

use crate::compile::library::BuiltInFunction;
use crate::compile::types::{PrimitiveType, Type};
use std::collections::{HashMap, HashSet};
use std::sync::LazyLock;
use strum::IntoEnumIterator;

/// Calling convention for a postfix method-call dispatch.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum PostfixKind {
    /// `recv.m ()` — method takes only the receiver; argument (if
    /// any) is a unit placeholder that gets discarded.
    Unary,
    /// `recv.m a` — method takes a 2-tuple (recv, a).
    Tupled2,
    /// `recv.m (a, b)` — method takes a 3-tuple (recv, a, b).
    Tupled3,
    /// `recv.m a` — method is curried; rewrites to `m recv a` (the
    /// receiver becomes the first curried argument). Used by
    /// built-ins like `Range.contains : 'a range -> 'a -> bool`.
    Curried2,
    /// `recv.m a` — method is curried; rewrites to `m a recv` (the
    /// receiver becomes the second curried argument). Used by
    /// built-ins like `Time.fmt : int -> time -> string` where the
    /// receiver type appears in the second curried position.
    Curried2Rev,
}

/// Returns a short string key identifying a "receiver type" for
/// postfix dispatch. Returns `None` if `t` isn't a known receiver
/// type — function types, tuples, records, and unbound type
/// variables are all skipped.
fn type_recv_key(t: &Type) -> Option<&'static str> {
    match peel_type(t) {
        Type::Primitive(PrimitiveType::Bool) => Some("bool"),
        Type::Primitive(PrimitiveType::Char) => Some("char"),
        Type::Primitive(PrimitiveType::Int) => Some("int"),
        Type::Primitive(PrimitiveType::Real) => Some("real"),
        Type::Primitive(PrimitiveType::String) => Some("string"),
        Type::List(_) => Some("list"),
        Type::Bag(_) => Some("bag"),
        // The type parser canonicalises `'a list` to `Type::List` and
        // `'a bag` to `Type::Named(_, "bag")` — accept both spellings,
        // and similarly for the other built-in datatypes.
        Type::Named(_, name) | Type::Data(name, _) => match name.as_str() {
            "bag" => Some("bag"),
            "continuous_set" => Some("continuous_set"),
            "date" => Some("date"),
            "discrete_set" => Some("discrete_set"),
            "list" => Some("list"),
            "option" => Some("option"),
            "range" => Some("range"),
            "time" => Some("time"),
            "vector" => Some("vector"),
            _ => None,
        },
        _ => None,
    }
}

/// Maps a parent structure name (the `p` strum prop) to its primary
/// receiver key, used to disambiguate Curried2 vs Curried2Rev when
/// both curried arguments have a known receiver type.
fn parent_recv_key(parent: &str) -> Option<&'static str> {
    Some(match parent {
        "Bag" => "bag",
        "Bool" => "bool",
        "Char" => "char",
        "Date" => "date",
        "Int" => "int",
        "List" => "list",
        "Option" => "option",
        "Range" => "range",
        "Real" => "real",
        "String" => "string",
        "Time" => "time",
        "Vector" => "vector",
        _ => return None,
    })
}

/// Strips `Type::Forall` wrappers, returning a borrowed `Type`.
fn strip_forall(t: &Type) -> &Type {
    let mut cur = t;
    while let Type::Forall(inner, _) = cur {
        cur = inner;
    }
    cur
}

/// Peels type aliases and Forall wrappers for dispatch purposes.
pub fn peel_type(t: &Type) -> &Type {
    match t {
        Type::Alias(_, inner, _) => peel_type(inner),
        Type::Forall(inner, _) => peel_type(inner),
        _ => t,
    }
}

/// Derives the user-facing method name from a function's `name`
/// strum prop. Most names map directly; the `$cs…` / `$ds…` internal
/// helpers used for `continuous_set` / `discrete_set` dispatch get
/// their `$` prefix stripped and their first letter lowercased
/// (e.g. `$csContains` → `contains`).
fn method_name_for(f: BuiltInFunction) -> &'static str {
    let name = f.name();
    if let Some(rest) = name.strip_prefix("$cs")
        && let Some(out) = lowercase_first_static(rest)
    {
        return out;
    }
    if let Some(rest) = name.strip_prefix("$ds")
        && let Some(out) = lowercase_first_static(rest)
    {
        return out;
    }
    name
}

/// Returns a borrowed `&'static str` whose first character is the
/// lowercase form of `s`'s first character. We can't allocate, so we
/// only handle the small fixed set of names that appear after the
/// `$cs` / `$ds` prefixes; returning `None` for unknown ones causes
/// the caller to fall back to the original name.
fn lowercase_first_static(s: &str) -> Option<&'static str> {
    Some(match s {
        "Complement" => "complement",
        "Contains" => "contains",
        "Ranges" => "ranges",
        _ => return None,
    })
}

/// Decides whether and how to dispatch a built-in function as a
/// postfix method. Returns `((method_name, recv_key), kind)` if
/// dispatchable, `None` otherwise.
fn infer_dispatch(
    f: BuiltInFunction,
) -> Option<((&'static str, &'static str), PostfixKind)> {
    let ty = f.get_type();
    let stripped = strip_forall(&ty);
    let Type::Fn(arg, ret) = stripped else {
        return None;
    };
    let parent_key = f.parent().and_then(parent_recv_key);
    let (recv_key, kind) = match arg.as_ref() {
        Type::Tuple(fields) if fields.len() == 2 => {
            (type_recv_key(&fields[0])?, PostfixKind::Tupled2)
        }
        Type::Tuple(fields) if fields.len() == 3 => {
            (type_recv_key(&fields[0])?, PostfixKind::Tupled3)
        }
        Type::Tuple(_) => return None,
        a => match ret.as_ref() {
            Type::Fn(a2, _) => {
                // Curried. Prefer the parameter whose type matches the
                // parent structure's primary receiver type; otherwise
                // dispatch on the first parameter.
                let k1 = type_recv_key(a);
                let k2 = type_recv_key(a2);
                match (parent_key, k1, k2) {
                    (Some(p), _, Some(k2)) if k2 == p => {
                        (k2, PostfixKind::Curried2Rev)
                    }
                    (Some(p), Some(k1), _) if k1 == p => {
                        (k1, PostfixKind::Curried2)
                    }
                    (_, Some(k1), _) => (k1, PostfixKind::Curried2),
                    (_, None, Some(k2)) => (k2, PostfixKind::Curried2Rev),
                    _ => return None,
                }
            }
            _ => (type_recv_key(a)?, PostfixKind::Unary),
        },
    };
    Some(((method_name_for(f), recv_key), kind))
}

type DispatchKey = (&'static str, &'static str);
type DispatchValue = (BuiltInFunction, PostfixKind);

/// Built-once dispatch table populated from `BuiltInFunction`
/// metadata.
static POSTFIX_TABLE: LazyLock<HashMap<DispatchKey, DispatchValue>> =
    LazyLock::new(|| {
        let mut table = HashMap::new();
        for f in BuiltInFunction::iter() {
            if let Some((key, kind)) = infer_dispatch(f) {
                // First entry wins. Built-in functions are iterated in
                // source order (which puts e.g. `RangeContains` before
                // `RangeCsContains`); keeping the first preserves the
                // current dispatch semantics.
                table.entry(key).or_insert((f, kind));
            }
        }
        table
    });

/// Set of method names that appear under more than one receiver type
/// in the postfix dispatch table; built once from the same metadata.
static OVERLOADED_NAMES: LazyLock<HashSet<&'static str>> =
    LazyLock::new(|| {
        let mut by_method: HashMap<&'static str, HashSet<&'static str>> =
            HashMap::new();
        for ((method, recv), _) in POSTFIX_TABLE.iter() {
            by_method.entry(*method).or_default().insert(*recv);
        }
        by_method
            .into_iter()
            .filter(|(_, recvs)| recvs.len() > 1)
            .map(|(m, _)| m)
            .collect()
    });

/// Maps a postfix method name + receiver type to the corresponding
/// built-in function. Returns `None` if no postfix method is defined
/// for this receiver type / method-name combination.
pub fn postfix_dispatch(
    method: &str,
    recv_type: &Type,
) -> Option<(BuiltInFunction, PostfixKind)> {
    let recv_key = type_recv_key(recv_type)?;
    POSTFIX_TABLE.get(&(method, recv_key)).copied()
}

/// Returns true if `method` is a known overloaded postfix method —
/// that is, more than one receiver type supports it. Used by the
/// type-resolver's pre-inference rewrite to decide whether the
/// receiver's concrete type must already be known before we can
/// dispatch.
pub fn is_overloaded_name(method: &str) -> bool {
    OVERLOADED_NAMES.contains(method)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sanity-check a few well-known dispatches. If any of these fail
    /// the auto-inference probably regressed.
    #[test]
    fn known_dispatches_present() {
        for (method, recv) in [
            ("only", "bag"),
            ("only", "list"),
            ("size", "string"),
            ("toString", "int"),
            ("toString", "time"),
            ("compare", "int"),
            ("compare", "real"),
            ("contains", "range"),
            ("contains", "continuous_set"),
            ("contains", "discrete_set"),
            ("fmt", "time"),
        ] {
            assert!(
                POSTFIX_TABLE.contains_key(&(method, recv)),
                "missing dispatch entry: ({}, {})",
                method,
                recv
            );
        }
    }

    #[test]
    fn overloaded_names_includes_compare() {
        assert!(is_overloaded_name("compare"));
        assert!(is_overloaded_name("toString"));
        assert!(!is_overloaded_name("explode"));
    }
}
