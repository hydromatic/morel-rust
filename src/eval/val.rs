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

use crate::compile::library::BuiltInFunction;
use crate::compile::types::Label;
use crate::compile::types::Type;
use crate::eval::code::{
    Code, EvalEnv, Frame as CodeFrame, Frame, Impl, LIBRARY,
};
use crate::eval::date;
use crate::eval::frame::FrameDef;
use crate::eval::order::Order;
use crate::eval::real::Real;
use crate::shell::main::MorelError;
use crate::syntax::parser;
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Weak};

/// Sentinel ordinal for the built-in `DESC` constructor of the
/// `descending` datatype. Distinct from any user-defined constructor
/// ordinal (which are 0-based).
pub const DESC_ORDINAL: usize = usize::MAX;

/// Sentinel ordinals for the 10 built-in constructors of the `range`
/// datatype. Distinct from any user-defined constructor ordinal (which
/// are 0-based) and from [`DESC_ORDINAL`].
pub const RANGE_ALL_ORDINAL: usize = usize::MAX - 10;
pub const RANGE_AT_LEAST_ORDINAL: usize = usize::MAX - 11;
pub const RANGE_AT_MOST_ORDINAL: usize = usize::MAX - 12;
pub const RANGE_CLOSED_ORDINAL: usize = usize::MAX - 13;
pub const RANGE_CLOSED_OPEN_ORDINAL: usize = usize::MAX - 14;
pub const RANGE_GREATER_THAN_ORDINAL: usize = usize::MAX - 15;
pub const RANGE_LESS_THAN_ORDINAL: usize = usize::MAX - 16;
pub const RANGE_OPEN_ORDINAL: usize = usize::MAX - 17;
pub const RANGE_OPEN_CLOSED_ORDINAL: usize = usize::MAX - 18;
pub const RANGE_POINT_ORDINAL: usize = usize::MAX - 19;

/// Sentinel ordinals for the `continuous_set` and `discrete_set`
/// wrapper types. A value wraps a `Val::List` of `range` constructors.
pub const CONTINUOUS_SET_ORDINAL: usize = usize::MAX - 20;
pub const DISCRETE_SET_ORDINAL: usize = usize::MAX - 21;

/// Sentinel ordinals for the 7 nullary constructors of the `weekday`
/// datatype. Stored values are `Val::Constructor(o, Box::new(Val::Unit))`.
pub const WEEKDAY_MON_ORDINAL: usize = usize::MAX - 30;
pub const WEEKDAY_TUE_ORDINAL: usize = usize::MAX - 31;
pub const WEEKDAY_WED_ORDINAL: usize = usize::MAX - 32;
pub const WEEKDAY_THU_ORDINAL: usize = usize::MAX - 33;
pub const WEEKDAY_FRI_ORDINAL: usize = usize::MAX - 34;
pub const WEEKDAY_SAT_ORDINAL: usize = usize::MAX - 35;
pub const WEEKDAY_SUN_ORDINAL: usize = usize::MAX - 36;

/// Sentinel ordinals for the 12 nullary constructors of the `month`
/// datatype. Stored values are `Val::Constructor(o, Box::new(Val::Unit))`.
pub const MONTH_JAN_ORDINAL: usize = usize::MAX - 40;
pub const MONTH_FEB_ORDINAL: usize = usize::MAX - 41;
pub const MONTH_MAR_ORDINAL: usize = usize::MAX - 42;
pub const MONTH_APR_ORDINAL: usize = usize::MAX - 43;
pub const MONTH_MAY_ORDINAL: usize = usize::MAX - 44;
pub const MONTH_JUN_ORDINAL: usize = usize::MAX - 45;
pub const MONTH_JUL_ORDINAL: usize = usize::MAX - 46;
pub const MONTH_AUG_ORDINAL: usize = usize::MAX - 47;
pub const MONTH_SEP_ORDINAL: usize = usize::MAX - 48;
pub const MONTH_OCT_ORDINAL: usize = usize::MAX - 49;
pub const MONTH_NOV_ORDINAL: usize = usize::MAX - 50;
pub const MONTH_DEC_ORDINAL: usize = usize::MAX - 51;

/// Runtime value.
///
/// The [Val::Typed], [Val::Named], [Val::Labeled], and [Val::Type] variants are
/// used to annotate values with additional information for pretty-printing.
/// [Val::Raw] is also used for pretty-printing.
///
/// Passing [Val] by value is OK because it is small.
/// We box the arguments to [Val::Typed] to keep it small.
#[derive(Clone, Debug)]
#[allow(clippy::needless_pass_by_value)]
pub enum Val {
    Unit,
    Bool(bool),
    Char(char),
    Int(i32),
    Order(Order),
    Real(f32),
    String(String),
    /// `Time(nanoseconds)` represents a `time` value as a 64-bit signed
    /// nanosecond count from the Unix epoch (or as a duration).
    Time(i64),
    /// `Date(utc_nanos, offset_secs)` represents a `date` value: an
    /// instant (UTC nanoseconds since the Unix epoch) plus a local
    /// timezone offset in seconds east of UTC. Field accessors like
    /// `Date.year` use the local broken-down time (`utc_nanos +
    /// offset_secs * 1e9`).
    Date(i64, i32),
    List(Vec<Val>),
    /// Built-in function.
    Fn(BuiltInFunction),

    /// `Some(v)` represents the `Option` value `SOME v`. (The other `Option`
    /// value, `NONE`, is represented as [Val::Unit].)
    Some(Box<Val>),

    /// `Inl(v)` represents the `Either` value `INL v`.
    Inl(Box<Val>),

    /// `Inr(v)` represents the `Either` value `INR v`.
    Inr(Box<Val>),

    /// `Variant(type, value)` represents an instance of the built-in
    /// `variant` datatype: a value of any Morel type, tagged at runtime
    /// with its inner type. Constructed by the `Variant.UNIT`, `INT`,
    /// `STRING`, `LIST`, etc. functions.
    Variant(Box<(Type, Val)>),

    /// `Constructor(ordinal, v)` represents a user-defined datatype
    /// constructor application. `ordinal` is the 0-based position of the
    /// constructor in the datatype declaration (used for comparison
    /// ordering). Nullary constructors carry `Val::Unit`. For example,
    /// `Y 0` of `datatype foo = X | Y of int` becomes
    /// `Constructor(1, Box::new(Int(0)))`. The built-in `DESC`
    /// constructor uses [`DESC_ORDINAL`] as its ordinal.
    Constructor(usize, Box<Val>),

    /// Wrapper that indicates that a value should be printed with its name
    /// and type.
    ///
    /// For example:
    ///
    /// ```sml
    /// val name = value : type
    /// ```
    Typed(Box<(String, Val, Type)>),

    /// Wrapper that indicates that a value should be printed with its name.
    ///
    /// For example:
    ///
    /// ```sml
    /// val name = value : type
    /// ```
    Named(Box<(String, Val)>),

    Labeled(Box<(Label, Type)>),
    /// `Type(prefix, type_)`
    Type(Box<(String, Type)>),
    /// `Raw(value)` is printed to the output as-is, without any quoting.
    Raw(String),

    /// A constant piece of code. TODO This is a short-term way of representing
    /// user-defined functions. Long-term, they should be handled by inlining.
    Code(Arc<Code>),

    /// A closure: a function that has captured variables from its
    /// definition site. Evaluated similarly to `Code::Fn` except that
    /// the frame is pre-populated with the captured values. Wrapped in
    /// `Arc<ClosureData>` so that a closure can refer to itself
    /// (through `Val::ClosureWeak`) without leaking memory — the
    /// self-reference is a `Weak`, and the closure is reaped when no
    /// strong reference remains.
    Closure(Arc<ClosureData>),

    /// Weak self-reference inside a closure's `bound_vals`. Set up by
    /// `Code::CreateClosure` for a closure-bound recursive `fun` that
    /// references itself; upgraded back to `Val::Closure` on access.
    /// Never observed outside the closure that owns the `Arc<ClosureData>`
    /// it points into.
    ClosureWeak(Weak<ClosureData>),

    /// Sentinel returned by [`Code::TailApply`] from a tail-position
    /// function call. The trampoline in `Frame::create_bind_and_eval`
    /// (and `Frame::create_and_eval`) bounces on this so that
    /// tail-recursive calls execute in O(1) Rust stack space. Other
    /// consumers should never observe this variant.
    TailCall(Box<Val>, Box<Val>),
}

/// The data inside a [`Val::Closure`]. Boxed in an `Arc` so that the
/// closure can hold a [`Weak`] reference to itself for self-recursion.
#[derive(Clone, Debug)]
pub struct ClosureData {
    pub frame_def: Arc<FrameDef>,
    pub matches: Vec<(Code, Code)>,
    pub bound_vals: Vec<Val>,
    pub no_match: Option<MorelError>,
}

impl PartialEq for ClosureData {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.frame_def, &other.frame_def)
            && self.bound_vals == other.bound_vals
    }
}

// REVIEW Should we use `Into` or `From` traits?
impl Val {
    /// Returns the `slot`th field if this value is a list.
    /// (Instances of tuple and record types are represented as lists.)
    pub(crate) fn get_field(&self, slot: usize) -> Option<&Val> {
        match self {
            Val::List(l) => Some(&l[slot]),
            _ => None,
        }
    }

    /// Creates a new Type value with the given prefix and type.
    pub fn new_type(prefix: &str, type_: &Type) -> Self {
        Val::Type(Box::new((prefix.to_string(), type_.clone())))
    }

    /// Creates a new Typed value with the given name, value, and type.
    pub fn new_typed(name: &str, value: Val, type_: &Type) -> Self {
        Val::Typed(Box::new((name.to_string(), value, type_.clone())))
    }

    /// Creates a new Named value with the given name and value.
    pub fn new_named(name: &str, value: Val) -> Self {
        Val::Named(Box::new((name.to_string(), value)))
    }

    /// Creates a new Labeled value with the given label and type.
    pub fn new_labeled(label: &Label, type_: &Type) -> Self {
        Val::Labeled(Box::new((label.clone(), type_.clone())))
    }

    pub(crate) fn expect_bool(&self) -> bool {
        match &self {
            Val::Bool(b) => *b,
            _ => panic!("Not a bool"),
        }
    }

    pub(crate) fn expect_code(&self) -> Arc<Code> {
        match self {
            Val::Code(c) => c.clone(),
            _ => panic!("Expected code"),
        }
    }

    pub(crate) fn expect_int(&self) -> i32 {
        match self {
            Val::Int(i) => *i,
            _ => panic!("Expected int"),
        }
    }

    pub(crate) fn expect_order(&self) -> Order {
        match self {
            Val::Order(i) => i.clone(),
            _ => panic!("Expected order"),
        }
    }

    pub(crate) fn expect_real(&self) -> f32 {
        match self {
            Val::Real(r) => *r,
            _ => panic!("Expected real"),
        }
    }

    pub(crate) fn expect_list(&self) -> &[Val] {
        match self {
            Val::List(list) => list,
            _ => panic!("Expected list"),
        }
    }

    pub(crate) fn expect_string(&self) -> String {
        match self {
            Val::String(s) => s.clone(),
            _ => panic!("Expected string"),
        }
    }

    pub(crate) fn expect_char(&self) -> char {
        match self {
            Val::Char(c) => *c,
            _ => panic!("Expected char"),
        }
    }

    pub(crate) fn expect_time(&self) -> i64 {
        match self {
            Val::Time(t) => *t,
            _ => panic!("Expected time"),
        }
    }

    pub(crate) fn expect_date(&self) -> (i64, i32) {
        match self {
            Val::Date(t, o) => (*t, *o),
            _ => panic!("Expected date"),
        }
    }

    pub(crate) fn maybe_bool(&self) -> Option<bool> {
        match self {
            Val::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub(crate) fn maybe_int(&self) -> Option<i32> {
        match self {
            Val::Int(i) => Some(*i),
            _ => None,
        }
    }

    pub(crate) fn maybe_string(&self) -> Option<String> {
        match self {
            Val::String(s) => Some(s.clone()),
            _ => None,
        }
    }

    /// Applies this value as a function to a single argument.
    /// Handles Val::Code, Val::Closure, and Val::Fn (built-in functions).
    ///
    /// May return a [`Val::TailCall`] sentinel if the called body is in
    /// tail position. The trampoline in [`Frame::create_and_eval`] /
    /// [`Frame::create_bind_and_eval`] catches sentinels at the top of
    /// each closure activation, so that tail-recursive calls execute in
    /// O(1) Rust stack space.
    pub(crate) fn apply_f1(
        &self,
        r: &mut EvalEnv,
        f: &mut Frame,
        arg: &Val,
    ) -> Result<Val, MorelError> {
        match self {
            Val::Code(code) => code.eval_f1(r, f, arg),
            Val::Closure(data) => CodeFrame::create_bind_and_eval(
                &data.frame_def,
                &data.matches,
                &data.bound_vals,
                data.no_match.as_ref(),
                r,
                arg,
            ),
            Val::ClosureWeak(weak) => {
                let arc = weak
                    .upgrade()
                    .expect("self-referential closure already dropped");
                Val::Closure(arc).apply_f1(r, f, arg)
            }
            Val::Fn(built_in_fn) => {
                let (_, impl_) = LIBRARY
                    .fn_map
                    .get(built_in_fn)
                    .expect("Function not in library");
                match impl_ {
                    Impl::E1(eager1) => Ok(eager1.apply(arg.clone())),
                    Impl::EF1(eagerf1) => {
                        eagerf1.apply(r, f, arg.clone(), None)
                    }
                    Impl::E2(eager2) => {
                        // Binary operators take a tuple as a single argument
                        if let Val::List(args) = arg {
                            if args.len() == 2 {
                                Ok(eager2
                                    .apply(args[0].clone(), args[1].clone()))
                            } else {
                                panic!(
                                    "Expected tuple with 2 elements, got {}",
                                    args.len()
                                )
                            }
                        } else {
                            panic!(
                                "Expected tuple argument for binary operator"
                            )
                        }
                    }
                    _ => panic!(
                        "Expected function with 1 argument, got {:?}",
                        impl_
                    ),
                }
            }
            _ => panic!("Expected code, closure, or fn, got {:?}", self),
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self {
            // lint: sort until '#}' where '##Val::'
            Val::Bool(b) => write!(f, "{}", b),
            Val::Char(c) => {
                write!(f, "#\"{}\"", parser::string_to_string(&c.to_string()))
            }
            Val::Closure(..) | Val::Code(_) => write!(f, "fn"),
            Val::Constructor(ordinal, v) => {
                if **v == Val::Unit {
                    write!(f, "#{}", ordinal)
                } else {
                    write!(f, "#{} {}", ordinal, v)
                }
            }
            Val::Date(d, o) => write!(f, "{}", date::format_iso(*d, *o)),
            Val::Fn(func) => {
                let name = func.name();
                // Symbolic operator names (e.g. `^`, `+`, `=`) are shown
                // as `op name`. Constructor names (e.g. `SOME`, `INL`,
                // `LESS`) are shown unqualified — they're parsed and
                // resolved without their structure name. Other
                // alphabetic names use the record-selector form
                // `#name Package` (e.g. `#size String`, `#set Sys`)
                // when they have a structure prefix; otherwise they
                // are shown bare. Mirrors morel-java's unparser, which
                // keeps the record-selector form because in core a
                // call like `String.size x` is `#size String x`.
                if name.is_empty()
                    || name
                        .chars()
                        .all(|c| c.is_alphanumeric() || c == '.' || c == '_')
                {
                    if func.is_constructor() {
                        write!(f, "{}", name)
                    } else if let Some(p) = func.package() {
                        write!(f, "#{} {}", name, p)
                    } else {
                        write!(f, "{}", name)
                    }
                } else {
                    write!(f, "op {}", name)
                }
            }
            Val::Inl(v) => write!(f, "INL {}", v),
            Val::Inr(v) => write!(f, "INR {}", v),
            Val::Int(i) => {
                if *i < 0 {
                    let s = i.to_string();
                    write!(f, "{}", s.replace("-", "~"))
                } else {
                    write!(f, "{}", i)
                }
            }
            Val::List(l) => {
                let mut first = true;
                write!(f, "[")?;
                for v in l {
                    if first {
                        first = false;
                    } else {
                        write!(f, ",")?;
                    }
                    v.fmt(f)?;
                }
                write!(f, "]")
            }
            Val::Order(o) => write!(f, "{}", o.name()),
            Val::Raw(s) => write!(f, "{}", s),
            Val::Real(r) => {
                // Use Real.toString to format real values
                write!(f, "{}", Real::to_string(*r))
            }
            Val::Some(v) => write!(f, "SOME {}", v),
            Val::String(s) => write!(f, "\"{}\"", parser::string_to_string(s)),
            Val::Time(t) => {
                // Format as decimal seconds with 3 fractional digits.
                let neg = *t < 0;
                let abs = t.unsigned_abs();
                let secs = abs / 1_000_000_000;
                let millis = (abs % 1_000_000_000) / 1_000_000;
                if neg {
                    write!(f, "~{}.{:03}", secs, millis)
                } else {
                    write!(f, "{}.{:03}", secs, millis)
                }
            }
            Val::Unit => write!(f, "()"),
            _ => write!(f, "{:?}", self),
        }
    }
}

// Implement Eq for Val (needed for HashMap keys)
impl PartialEq for Val {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Val::Unit, Val::Unit) => true,
            (Val::Bool(a), Val::Bool(b)) => a == b,
            (Val::Char(a), Val::Char(b)) => a == b,
            (Val::Int(a), Val::Int(b)) => a == b,
            (Val::Order(a), Val::Order(b)) => a == b,
            (Val::Real(a), Val::Real(b)) => a == b,
            (Val::String(a), Val::String(b)) => a == b,
            (Val::List(a), Val::List(b)) => a == b,
            (Val::Fn(a), Val::Fn(b)) => a == b,
            (Val::Some(a), Val::Some(b)) => a == b,
            (Val::Inl(a), Val::Inl(b)) => a == b,
            (Val::Inr(a), Val::Inr(b)) => a == b,
            (Val::Variant(a), Val::Variant(b)) => a == b,
            (Val::Constructor(a, x), Val::Constructor(b, y)) => {
                a == b && x == y
            }
            (Val::Typed(a), Val::Typed(b)) => a == b,
            (Val::Named(a), Val::Named(b)) => a == b,
            (Val::Labeled(a), Val::Labeled(b)) => a == b,
            (Val::Type(a), Val::Type(b)) => a == b,
            (Val::Raw(a), Val::Raw(b)) => a == b,
            (Val::Code(a), Val::Code(b)) => Arc::ptr_eq(a, b),
            (Val::Closure(a), Val::Closure(b)) => Arc::ptr_eq(a, b),
            (Val::ClosureWeak(a), Val::ClosureWeak(b)) => Weak::ptr_eq(a, b),
            _ => false,
        }
    }
}

impl Eq for Val {}

// Implement Hash for Val (needed for HashMap keys)
impl Hash for Val {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Val::Unit => 0.hash(state),
            Val::Bool(b) => {
                1.hash(state);
                b.hash(state);
            }
            Val::Char(c) => {
                2.hash(state);
                c.hash(state);
            }
            Val::Int(i) => {
                3.hash(state);
                i.hash(state);
            }
            Val::Order(o) => {
                4.hash(state);
                o.hash(state);
            }
            Val::Real(f) => {
                // Hash floats using their bit representation
                5.hash(state);
                f.to_bits().hash(state);
            }
            Val::String(s) => {
                6.hash(state);
                s.hash(state);
            }
            Val::Time(t) => {
                22.hash(state);
                t.hash(state);
            }
            Val::Date(d, o) => {
                23.hash(state);
                d.hash(state);
                o.hash(state);
            }
            Val::List(vs) => {
                7.hash(state);
                vs.hash(state);
            }
            Val::Fn(f) => {
                8.hash(state);
                (*f as usize).hash(state);
            }
            // NONE is represented as Val::Unit
            Val::Some(v) => {
                10.hash(state);
                v.hash(state);
            }
            Val::Inl(v) => {
                11.hash(state);
                v.hash(state);
            }
            Val::Inr(v) => {
                12.hash(state);
                v.hash(state);
            }
            Val::Variant(boxed) => {
                21.hash(state);
                // Hash only the value; the inner type is derivable from it.
                boxed.as_ref().1.hash(state);
            }
            Val::Constructor(ordinal, v) => {
                20.hash(state);
                ordinal.hash(state);
                v.hash(state);
            }
            Val::Typed(boxed) => {
                13.hash(state);
                let (name, val, _type) = boxed.as_ref();
                name.hash(state);
                val.hash(state);
                // Skip type for hashing
            }
            Val::Named(boxed) => {
                14.hash(state);
                let (name, val) = boxed.as_ref();
                name.hash(state);
                val.hash(state);
            }
            Val::Labeled(boxed) => {
                15.hash(state);
                let (label, _type) = boxed.as_ref();
                label.hash(state);
                // Skip type for hashing
            }
            Val::Type(boxed) => {
                16.hash(state);
                let (name, _type) = boxed.as_ref();
                name.hash(state);
                // Skip type for hashing
            }
            Val::Raw(s) => {
                17.hash(state);
                s.hash(state);
            }
            Val::Code(code) => {
                18.hash(state);
                // Hash the pointer address
                Arc::as_ptr(code).hash(state);
            }
            Val::Closure(data) => {
                19.hash(state);
                Arc::as_ptr(&data.frame_def).hash(state);
                data.matches.len().hash(state);
                data.bound_vals.hash(state);
            }
            Val::ClosureWeak(weak) => {
                20.hash(state);
                Weak::as_ptr(weak).hash(state);
            }
            Val::TailCall(fn_, arg) => {
                20.hash(state);
                fn_.hash(state);
                arg.hash(state);
            }
        }
    }
}
