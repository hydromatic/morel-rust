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

use crate::compile::library::BuiltInFunction;
use crate::compile::types::{PrimitiveType, Type};

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
    /// `recv.m a` — method is curried; rewrites to `m recv a`.
    /// Used by built-ins whose declared type is curried (e.g.
    /// `Range.contains : 'a -> 'b -> bool`) so that the existing
    /// compile-time intercepts (which look at the curried Apply
    /// shape) fire correctly.
    Curried2,
}

/// Maps a postfix method name + receiver type to the corresponding
/// built-in function. Returns `None` if no postfix method is defined
/// for this receiver type / method-name combination.
pub fn postfix_dispatch(
    method: &str,
    recv_type: &Type,
) -> Option<(BuiltInFunction, PostfixKind)> {
    use BuiltInFunction::{
        BagDrop, BagHd, BagLength, BagNull, BagOnly, BagTake, BagTl, BoolNot,
        BoolToString, CharCompare, CharIsAlpha, CharIsDigit, CharOrd, CharPred,
        CharSucc, CharToLower, CharToString, CharToUpper, IntAbs, IntCompare,
        IntMax, IntMin, IntRem, IntSameSign, IntSign, IntToString, ListDrop,
        ListHd, ListLength, ListNth, ListNull, ListOnly, ListTake, ListTl,
        OptionGetOpt, OptionIsSome, OptionValOf, RangeContains,
        RangeCsComplement, RangeCsContains, RangeCsRanges, RangeDsComplement,
        RangeDsContains, RangeDsRanges, RangeToBag, RangeToList, RealAbs,
        RealCeil, RealCompare, RealFloor, RealMax, RealMin, RealRem, RealSign,
        RealToString, RealTrunc, StringExplode, StringSize, StringSub,
        StringSubstring,
    };
    use PostfixKind::{Curried2, Tupled2, Tupled3, Unary};
    let ty = peel_type(recv_type);
    match (method, ty) {
        // String
        ("size", Type::Primitive(PrimitiveType::String)) => {
            Some((StringSize, Unary))
        }
        ("sub", Type::Primitive(PrimitiveType::String)) => {
            Some((StringSub, Tupled2))
        }
        ("substring", Type::Primitive(PrimitiveType::String)) => {
            Some((StringSubstring, Tupled3))
        }
        ("explode", Type::Primitive(PrimitiveType::String)) => {
            Some((StringExplode, Unary))
        }
        // List
        ("length", Type::List(_)) => Some((ListLength, Unary)),
        ("hd", Type::List(_)) => Some((ListHd, Unary)),
        ("tl", Type::List(_)) => Some((ListTl, Unary)),
        ("null", Type::List(_)) => Some((ListNull, Unary)),
        ("only", Type::List(_)) => Some((ListOnly, Unary)),
        ("drop", Type::List(_)) => Some((ListDrop, Tupled2)),
        ("take", Type::List(_)) => Some((ListTake, Tupled2)),
        ("nth", Type::List(_)) => Some((ListNth, Tupled2)),
        // Bag
        ("length", Type::Bag(_)) => Some((BagLength, Unary)),
        ("hd", Type::Bag(_)) => Some((BagHd, Unary)),
        ("tl", Type::Bag(_)) => Some((BagTl, Unary)),
        ("null", Type::Bag(_)) => Some((BagNull, Unary)),
        ("only", Type::Bag(_)) => Some((BagOnly, Unary)),
        ("drop", Type::Bag(_)) => Some((BagDrop, Tupled2)),
        ("take", Type::Bag(_)) => Some((BagTake, Tupled2)),
        // Int (overloaded)
        ("abs", Type::Primitive(PrimitiveType::Int)) => Some((IntAbs, Unary)),
        ("compare", Type::Primitive(PrimitiveType::Int)) => {
            Some((IntCompare, Tupled2))
        }
        ("max", Type::Primitive(PrimitiveType::Int)) => Some((IntMax, Tupled2)),
        ("min", Type::Primitive(PrimitiveType::Int)) => Some((IntMin, Tupled2)),
        ("rem", Type::Primitive(PrimitiveType::Int)) => Some((IntRem, Tupled2)),
        ("sameSign", Type::Primitive(PrimitiveType::Int)) => {
            Some((IntSameSign, Tupled2))
        }
        ("sign", Type::Primitive(PrimitiveType::Int)) => Some((IntSign, Unary)),
        ("toString", Type::Primitive(PrimitiveType::Int)) => {
            Some((IntToString, Unary))
        }
        // Real (overloaded)
        ("abs", Type::Primitive(PrimitiveType::Real)) => Some((RealAbs, Unary)),
        ("ceil", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealCeil, Unary))
        }
        ("compare", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealCompare, Tupled2))
        }
        ("floor", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealFloor, Unary))
        }
        ("max", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealMax, Tupled2))
        }
        ("min", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealMin, Tupled2))
        }
        ("rem", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealRem, Tupled2))
        }
        ("sign", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealSign, Unary))
        }
        ("toString", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealToString, Unary))
        }
        ("trunc", Type::Primitive(PrimitiveType::Real)) => {
            Some((RealTrunc, Unary))
        }
        // Char (overloaded)
        ("compare", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharCompare, Tupled2))
        }
        ("isAlpha", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharIsAlpha, Unary))
        }
        ("isDigit", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharIsDigit, Unary))
        }
        ("ord", Type::Primitive(PrimitiveType::Char)) => Some((CharOrd, Unary)),
        ("pred", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharPred, Unary))
        }
        ("succ", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharSucc, Unary))
        }
        ("toLower", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharToLower, Unary))
        }
        ("toString", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharToString, Unary))
        }
        ("toUpper", Type::Primitive(PrimitiveType::Char)) => {
            Some((CharToUpper, Unary))
        }
        // Bool (overloaded)
        ("not", Type::Primitive(PrimitiveType::Bool)) => Some((BoolNot, Unary)),
        ("toString", Type::Primitive(PrimitiveType::Bool)) => {
            Some((BoolToString, Unary))
        }
        // Option
        ("getOpt", Type::Data(n, _)) if n == "option" => {
            Some((OptionGetOpt, Tupled2))
        }
        ("isSome", Type::Data(n, _)) if n == "option" => {
            Some((OptionIsSome, Unary))
        }
        ("valOf", Type::Data(n, _)) if n == "option" => {
            Some((OptionValOf, Unary))
        }
        // Range
        ("contains", Type::Data(n, _)) if n == "range" => {
            Some((RangeContains, Curried2))
        }
        ("contains", Type::Data(n, _)) if n == "continuous_set" => {
            Some((RangeCsContains, Curried2))
        }
        ("contains", Type::Data(n, _)) if n == "discrete_set" => {
            Some((RangeDsContains, Curried2))
        }
        ("ranges", Type::Data(n, _)) if n == "continuous_set" => {
            Some((RangeCsRanges, Unary))
        }
        ("ranges", Type::Data(n, _)) if n == "discrete_set" => {
            Some((RangeDsRanges, Unary))
        }
        ("complement", Type::Data(n, _)) if n == "continuous_set" => {
            Some((RangeCsComplement, Unary))
        }
        ("complement", Type::Data(n, _)) if n == "discrete_set" => {
            Some((RangeDsComplement, Unary))
        }
        ("toList", Type::Data(n, _)) if n == "discrete_set" => {
            Some((RangeToList, Unary))
        }
        ("toBag", Type::Data(n, _)) if n == "discrete_set" => {
            Some((RangeToBag, Unary))
        }
        _ => None,
    }
}

/// Peels type aliases and Forall wrappers for dispatch purposes.
pub fn peel_type(t: &Type) -> &Type {
    match t {
        Type::Alias(_, inner, _) => peel_type(inner),
        Type::Forall(inner, _) => peel_type(inner),
        _ => t,
    }
}

/// Returns true if `method` is a known overloaded postfix method —
/// that is, more than one receiver type supports it. Used by the
/// type-resolver's pre-inference rewrite to decide whether the
/// receiver's concrete type must already be known before we can
/// dispatch.
pub fn is_overloaded_name(method: &str) -> bool {
    matches!(
        method,
        "abs"
            | "compare"
            | "complement"
            | "contains"
            | "drop"
            | "getItem"
            | "hd"
            | "length"
            | "max"
            | "min"
            | "nth"
            | "null"
            | "only"
            | "ranges"
            | "rem"
            | "sign"
            | "sub"
            | "take"
            | "tl"
            | "toString"
    )
}
