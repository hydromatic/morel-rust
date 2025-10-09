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
use crate::eval::code::{Code, Frame as CodeFrame, Impl, LIBRARY, Span};
use crate::eval::frame::FrameDef;
use crate::eval::order::Order;
use crate::syntax::parser;
use std::fmt::{Display, Formatter};
use std::sync::Arc;

/// Runtime value.
///
/// The [Val::Typed], [Val::Named], [Val::Labeled], and [Val::Type] variants are
/// used to annotate values with additional information for pretty-printing.
/// [Val::Raw] is also used for pretty-printing.
///
/// Passing [Val] by value is OK because it is small.
/// We box the arguments to [Val::Typed] to keep it small.
#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::needless_pass_by_value)]
pub enum Val {
    Unit,
    Bool(bool),
    Char(char),
    Int(i32),
    Order(Order),
    Real(f32),
    String(String),
    List(Vec<Val>),
    /// Built-in function.
    Fn(BuiltInFunction),

    /// `Some(v)` represents the `Option` value `SOME v`. (The other `Option`
    /// value, `NONE`, is represented as [Val::Unit].)
    Some(Box<Val>),

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

    /// `Closure(frame_def, matches, bound_vals)` is a closure.
    /// It is evaluated similarly to `Fn(frame_def, matches)`, except
    /// that the frame is pre-populated with the values.
    Closure(Arc<FrameDef>, Vec<(Code, Code)>, Vec<Val>),
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

    pub(crate) fn expect_span(&self) -> Span {
        match self {
            Val::String(s) => Span::new(s),
            _ => panic!("Expected span"),
        }
    }

    pub(crate) fn expect_char(&self) -> char {
        match self {
            Val::Char(c) => *c,
            _ => panic!("Expected char"),
        }
    }

    /// Applies this value as a function to a single argument.
    /// Handles Val::Code, Val::Closure, and Val::Fn (built-in functions).
    pub(crate) fn apply_f1(
        &self,
        r: &mut crate::eval::code::EvalEnv,
        f: &mut crate::eval::code::Frame,
        arg: &Val,
    ) -> Result<Val, crate::shell::main::MorelError> {
        match self {
            Val::Code(code) => code.eval_f1(r, f, arg),
            Val::Closure(frame_def, matches, bound_vals) => {
                CodeFrame::create_bind_and_eval(
                    frame_def, matches, bound_vals, r, arg,
                )
            }
            Val::Fn(built_in_fn) => {
                let (_, impl_) = LIBRARY
                    .fn_map
                    .get(built_in_fn)
                    .expect("Function not in library");
                match impl_ {
                    Impl::E1(eager1) => Ok(eager1.apply(arg.clone())),
                    Impl::EF1(eagerf1) => eagerf1.apply(r, f, arg.clone()),
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
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            // lint: sort until '#}' where '##Val::'
            Val::Bool(b) => write!(f, "{}", b),
            Val::Char(c) => {
                write!(f, "#\"{}\"", parser::string_to_string(&c.to_string()))
            }
            Val::Fn(func) => write!(f, "{:?}", func),
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
            Val::Raw(s) => write!(f, "{}", s),
            Val::Real(r) => {
                if *r < 0.0 {
                    write!(f, "-{}", -*r)
                } else {
                    write!(f, "{}", r)
                }
            }
            Val::Some(v) => write!(f, "SOME {}", v),
            Val::String(s) => write!(f, "\"{}\"", parser::string_to_string(s)),
            Val::Unit => write!(f, "()"),
            _ => todo!("{:?}", self),
        }
    }
}
