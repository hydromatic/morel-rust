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

use crate::compile::library::{BuiltIn, BuiltInFunction, BuiltInRecord};
use crate::compile::type_env::Binding;
use crate::compile::type_parser;
use crate::compile::types::{Label, Type};
use crate::eval::code::EagerV2::SysSet;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::main::{MorelError, Shell};
use std::collections::{BTreeMap, HashMap};
use std::iter::zip;
use std::str::FromStr;
use std::sync::LazyLock;
use strum::{EnumProperty, IntoEnumIterator};

/// Evaluation mode.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum EvalMode {
    /// Evaluation with a frame and no arguments.
    EagerV0,
    /// Evaluation with a frame and one argument.
    EagerV1,
    Eager0,
    Eager1,
    Eager2,
    Eager3,
    EagerV2,
}

/// Effects that can be applied to modify the state of the current shell or
/// session.
///
/// This allows evaluation to be pure while still describing side effects.
/// Shell and session are immutable during statement execution; statements such
/// as `Sys.set("output", "tabular")` do not modify the session while the
/// command is executing; the shell mutates its own and the session state after
/// the command completes.
#[derive(Debug, Clone)]
pub enum Effect {
    /// Emits an output line.
    EmitLine(String),
    /// Sets a shell property.
    SetShellProp(String, Val),
    /// Sets a session property.
    SetSessionProp(String, Val),
    /// Adds a binding to the environment.
    AddBinding(Binding),
}

/// Generated code that can be evaluated.
#[derive(Clone, Debug, PartialEq)]
pub enum Code {
    // lint: sort until '#}' where '##[A-Z][A-Za-z0-9]*\('
    /// `Apply(fn_code, arg_code)` calls a function.
    Apply(Box<Code>, Box<Code>),
    /// `ApplyFixed(fn_code, arg_code)` calls a function whose code is known at
    /// compile time.
    ApplyConstant(Box<Code>, Box<Code>),
    /// `Bind(pat, expr)` binds the pattern to the expression; throws if the
    /// value does not match.
    Bind(Box<(Code, Code)>),
    /// `BindCons(head, tail)` succeeds if the argument `head :: tail` (i.e.
    /// a list of length at least 1).
    BindCons(Box<Code>, Box<Code>),
    /// `BindConstructor(name, pat)` succeeds if the argument is a call to the
    /// type-constructor called `name` and its argument matches `pat`.
    /// (Zero argument constructors become [Code::BindLiteral].)
    BindConstructor(String, Box<Code>),
    /// `BindList(patterns)` succeeds if the argument is a list the same length
    /// as `patterns` and each element successfully binds.
    BindList(Vec<Code>),
    /// `BindLiteral(val)` succeeds if the argument is equal to `val`.
    BindLiteral(Val),
    /// `BindSlot(slot, name)` assigns the argument to the `slot`th
    /// variable in the current frame. `name` is for debugging purposes.
    BindSlot(usize, String),
    /// `BindTuple(patterns)` succeeds if all patterns successfully bind.
    /// Every pattern is a code that takes 1 argument and returns a boolean
    /// value.
    BindTuple(Vec<Code>),
    /// `BindWildcard` ignores its argument and always succeeds.
    BindWildcard,
    /// `Case(codes)` evaluates `e`, iterates the (pattern, expression)
    /// pairs until it can find the value to a pattern and finally evaluates
    /// the expression.
    Case(Vec<Code>),
    Constant(Val),
    /// `Fn(local_names, matches)` first creates a frame to contain the required
    /// local variables, next iterates the (pattern, expression) pairs until it
    /// can bind the argument to a pattern and finally evaluates the
    /// expression.
    Fn(Vec<Binding>, Vec<(Code, Code)>),
    /// `GetLocal(slot)` returns the value of the `slot`th variable in the
    /// current stack frame. See [Code::BindSlot].
    GetLocal(usize),
    Let(Vec<Code>, Box<Code>),
    /// `Link(slot, name)` is a reference to the code in the `slot`th slot of
    /// the code table. It used to represent recursive functions, because at
    /// the time the recursive function is being compiled, there is not yet
    /// code to refer to. `name` is for debugging.
    Link(usize, String),
    Native0(Eager0),
    Native1(Eager1, Box<Code>),
    Native2(Eager2, Box<Code>, Box<Code>),
    Native3(Eager3, Box<Code>, Box<Code>, Box<Code>),
    NativeF2(EagerV2, Box<Code>, Box<Code>),
    Tuple(Vec<Code>),
}

impl Code {
    pub(crate) fn new_apply(f: &Code, a: &Code) -> Code {
        if let Code::Constant(Val::Code(c)) = f {
            Code::ApplyConstant(c.clone(), Box::new(a.clone()))
        } else {
            Code::Apply(Box::new(f.clone()), Box::new(a.clone()))
        }
    }

    pub(crate) fn new_bind_cons(h: &Code, t: &Code) -> Code {
        Code::BindCons(Box::new(h.clone()), Box::new(t.clone()))
    }

    pub(crate) fn new_bind_constructor(name: &str, t: &Option<Code>) -> Code {
        if let Some(t) = t {
            Code::BindConstructor(name.to_string(), Box::new(t.clone()))
        } else {
            Self::new_bind_literal(&Val::String(name.to_string()))
        }
    }

    pub(crate) fn new_bind_literal(val: &Val) -> Code {
        Code::BindLiteral(val.clone())
    }

    pub(crate) fn new_bind_slot(slot: usize, name: &str) -> Code {
        Code::BindSlot(slot, name.to_string())
    }

    pub(crate) fn new_bind(pat_code: &Code, expr_code: &Code) -> Code {
        Code::Bind(Box::new((pat_code.clone(), expr_code.clone())))
    }

    pub(crate) fn new_constant(v: Val) -> Code {
        Code::Constant(v)
    }

    pub(crate) fn new_fn(
        local_vars: &[Binding],
        pat_expr_codes: &[(Code, Code)],
    ) -> Code {
        // REVIEW A function could also support Eager1 (without environment)
        // if it does not use global variables or have effects. The environment
        // is currently necessary to create a frame.
        for (pat_code, _) in pat_expr_codes {
            pat_code.assert_supports_eval_mode(&EvalMode::EagerV1);
        }
        Code::Fn(local_vars.to_vec(), pat_expr_codes.to_vec())
    }

    pub(crate) fn new_bind_list(codes: &[Code]) -> Code {
        codes.iter().for_each(|code| {
            code.assert_supports_eval_mode(&EvalMode::EagerV1)
        });
        Code::BindList(codes.to_vec())
    }

    pub(crate) fn new_bind_tuple(codes: &[Code]) -> Code {
        codes.iter().for_each(|code| {
            code.assert_supports_eval_mode(&EvalMode::EagerV1)
        });
        Code::BindTuple(codes.to_vec())
    }

    pub(crate) fn new_match(codes: &[Code]) -> Code {
        assert_eq!(codes.len() % 2, 1);
        codes.iter().enumerate().for_each(|(i, code)| {
            code.assert_supports_eval_mode(if i % 2 == 0 {
                &EvalMode::EagerV0
            } else {
                &EvalMode::EagerV1
            })
        });
        Code::Case(codes.to_vec())
    }

    pub(crate) fn new_native(impl_: Impl, codes: &[Code]) -> Code {
        match impl_ {
            // lint: sort until '#}' where '##Impl::'
            Impl::Custom => {
                unreachable!(
                    "Custom functions should be handled in \
                    Codes::apply"
                )
            }
            Impl::E0(e0) => {
                assert_eq!(codes.len(), 0);
                Code::Native0(e0)
            }
            Impl::E1(e1) => {
                assert_eq!(codes.len(), 1);
                Code::Native1(e1, Box::new(codes[0].clone()))
            }
            Impl::E2(e2) => {
                assert_eq!(codes.len(), 2);
                Code::Native2(
                    e2,
                    Box::new(codes[0].clone()),
                    Box::new(codes[1].clone()),
                )
            }
            Impl::E3(e3) => {
                assert_eq!(codes.len(), 3);
                Code::Native3(
                    e3,
                    Box::new(codes[0].clone()),
                    Box::new(codes[1].clone()),
                    Box::new(codes[2].clone()),
                )
            }
            Impl::EV2(ev2) => {
                // TODO: handle cases like 'let args = (1, 2) in f args
                // end'; see Gather in Morel-Java
                assert_eq!(codes.len(), 2);
                Code::NativeF2(
                    ev2,
                    Box::new(codes[0].clone()),
                    Box::new(codes[1].clone()),
                )
            }
        }
    }

    pub fn new_list(codes: &[Code]) -> Code {
        Self::new_tuple(codes)
    }

    pub fn new_tuple(codes: &[Code]) -> Code {
        Code::Tuple(codes.to_vec())
    }

    pub fn assert_supports_eval_mode(&self, eval_mode: &EvalMode) {
        assert!(
            self.supports_eval_mode(eval_mode),
            "Code {:?} does not support eval mode {:?}",
            self,
            eval_mode
        );
    }

    fn supports_eval_mode(&self, mode: &EvalMode) -> bool {
        match self {
            // lint: sort until '#}' where '##Code::'
            Code::Apply(_, _) => *mode == EvalMode::Eager0,
            Code::ApplyConstant(_, _) => *mode == EvalMode::Eager0,
            Code::Bind(_) => *mode == EvalMode::Eager0,
            Code::BindCons(_, _) => {
                *mode == EvalMode::EagerV1 || *mode == EvalMode::Eager1
            }
            Code::BindConstructor(_, _) => {
                *mode == EvalMode::EagerV1 || *mode == EvalMode::Eager1
            }
            Code::BindList(_) => {
                *mode == EvalMode::EagerV1 || *mode == EvalMode::Eager1
            }
            Code::BindLiteral(_) => {
                *mode == EvalMode::EagerV1 || *mode == EvalMode::Eager1
            }
            Code::BindSlot(_, _) => *mode == EvalMode::EagerV1,
            Code::BindTuple(_) => *mode == EvalMode::EagerV1,
            Code::BindWildcard => *mode == EvalMode::EagerV1,
            Code::Case(_) => *mode == EvalMode::EagerV1,
            Code::Constant(_) => {
                *mode == EvalMode::Eager0 || *mode == EvalMode::EagerV0
            }
            Code::Fn(_, _) => *mode == EvalMode::EagerV1,
            Code::GetLocal(_) => *mode == EvalMode::EagerV0,
            Code::Let(_, _) => *mode == EvalMode::Eager0,
            Code::Link(_, _) => todo!("{:?}", self),
            Code::Native0(_) => *mode == EvalMode::Eager0,
            Code::Native1(_, _) => {
                *mode == EvalMode::Eager1 || *mode == EvalMode::EagerV0
            }
            Code::Native2(_, _, _) => {
                *mode == EvalMode::Eager2 || *mode == EvalMode::EagerV0
            }
            Code::Native3(_, _, _, _) => *mode == EvalMode::Eager3,
            Code::NativeF2(_, _, _) => *mode == EvalMode::EagerV2,
            Code::Tuple(_) => *mode == EvalMode::EagerV0,
        }
    }

    pub fn eval_f0(
        &self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        match &self {
            // lint: sort until '#}' where '##Code::'
            Code::Apply(fn_code, arg_code) => {
                let arg = arg_code.eval_f0(r, f)?;
                let fn_ = fn_code.eval_f0(r, f)?;
                let fn_code2 = fn_.expect_code();
                fn_code2.eval_f1(r, f, &arg)
            }
            Code::ApplyConstant(fn_code, arg_code) => {
                let arg = arg_code.eval_f0(r, f)?;
                fn_code.eval_f1(r, f, &arg)
            }
            Code::Bind(b) => {
                let (pat_code, expr_code) = &**b;
                let v = expr_code.eval_f0(r, f)?;
                match pat_code.eval_f1(r, f, &v) {
                    Ok(Val::Bool(true)) => Ok(Val::Unit),
                    Ok(_) => Err(MorelError::Bind),
                    Err(e) => Err(e),
                }
            }
            Code::Case(codes) => {
                let v = codes[0].eval_f0(r, f)?;
                let mut i = 1;
                while i < codes.len() {
                    let pat = &codes[i];
                    let matched = pat.eval_f1(r, f, &v)?;
                    if matched.expect_bool() {
                        let expr = &codes[i + 1];
                        return expr.eval_f0(r, f);
                    }
                    i += 2;
                }
                Err(MorelError::Bind)
            }
            Code::Constant(c) => Ok(c.clone()),
            Code::Fn(_, _) => {
                // Fn is practically a literal. When evaluated, it returns
                // itself.
                Ok(Val::Code(Box::new(self.clone())))
            }
            Code::GetLocal(ordinal) => Ok(f.vals[*ordinal].clone()),
            Code::Let(codes, code) => {
                // REVIEW: Could codes and code be merged into one vector?
                for code in codes {
                    code.eval_f0(r, f)?;
                }
                code.eval_f0(r, f)
            }
            Code::Link(_, _) => {
                todo!()
            }
            Code::Native0(eager) => Ok(eager.apply()),
            Code::Native1(eager, code0) => {
                let v0 = code0.eval_f0(r, f)?;
                Ok(eager.apply(v0))
            }
            Code::Native2(eager, code0, code1) => {
                let v0 = code0.eval_f0(r, f)?;
                let v1 = code1.eval_f0(r, f)?;
                Ok(eager.apply(v0, v1))
            }
            Code::Native3(eager, code0, code1, code2) => {
                let v0 = code0.eval_f0(r, f)?;
                let v1 = code1.eval_f0(r, f)?;
                let v2 = code2.eval_f0(r, f)?;
                Ok(eager.apply(v0, v1, v2))
            }
            Code::NativeF2(eager, code0, code1) => {
                let v0 = code0.eval_f0(r, f)?;
                let v1 = code1.eval_f0(r, f)?;
                eager.apply(r, f, v0, v1)
            }
            Code::Tuple(codes) => {
                let mut values = Vec::with_capacity(codes.capacity());
                for code in codes {
                    values.push(code.eval_f0(r, f)?);
                }
                Ok(Val::List(values))
            }
            _ => {
                todo!("eval_f0: {:?}", self)
            }
        }
    }

    pub fn eval_f1(
        &self,
        r: &mut EvalEnv,
        f: &mut Frame,
        a0: &Val,
    ) -> Result<Val, MorelError> {
        match &self {
            // lint: sort until '#}' where '##Code::'
            Code::BindCons(head_code, tail_code) => {
                let list = a0.expect_list();
                if list.is_empty() {
                    return Ok(Val::Bool(false));
                }
                let head_result = head_code.eval_f1(r, f, &list[0])?;
                if !head_result.expect_bool() {
                    return Ok(Val::Bool(false));
                }
                let tail = Val::List(list[1..].to_vec());
                let tail_result = tail_code.eval_f1(r, f, &tail)?;
                Ok(tail_result)
            }
            Code::BindConstructor(_name, pat_code) => {
                // Constructor call delegation to pattern
                pat_code.eval_f1(r, f, a0)
            }
            Code::BindList(codes) => {
                let list = a0.expect_list();
                if list.len() != codes.len() {
                    return Ok(Val::Bool(false));
                }
                for (code, val) in zip(codes, list) {
                    let result = code.eval_f1(r, f, val)?;
                    if !result.expect_bool() {
                        return Ok(result);
                    }
                }
                Ok(Val::Bool(true))
            }
            Code::BindLiteral(val) => Ok(Val::Bool(a0 == val)),
            Code::BindSlot(ordinal, _) => {
                f.vals[*ordinal] = a0.clone();
                Ok(Val::Bool(true))
            }
            Code::BindTuple(codes) => {
                let list = a0.expect_list();
                for (code, val) in zip(codes, list) {
                    let result = code.eval_f1(r, f, val)?;
                    if !result.expect_bool() {
                        // One match failed. Return false.
                        return Ok(result);
                    }
                }
                // All matches succeeded. Return true.
                Ok(Val::Bool(true))
            }
            Code::BindWildcard => Ok(Val::Bool(true)),
            Code::Constant(v) => Ok(v.clone()),
            Code::Fn(local_names, matches) => {
                Frame::create_and_eval(local_names, matches, r, a0)
            }
            Code::GetLocal(ordinal) => Ok(f.vals[*ordinal].clone()),
            Code::Link(slot, _) => {
                let code = r.link_codes[*slot].clone();
                code.eval_f1(r, f, a0)
            }
            _ => {
                todo!("eval: {:?}", self)
            }
        }
    }
}

/// Stack frame for evaluating [Code].
pub struct Frame<'a> {
    pub vals: &'a mut [Val],
}

impl<'a> Frame<'a> {
    /// Creates a frame, binds an argument to one of a list of patterns,
    /// and executes the corresponding expression.
    ///
    /// This is the implementation of a function call.
    fn create_and_eval(
        local_names: &[Binding],
        matches: &[(Code, Code)],
        r: &mut EvalEnv,
        arg: &Val,
    ) -> Result<Val, MorelError> {
        let mut val_vec: Vec<Val> = vec![Val::Unit; local_names.len()];

        for (pat_code, expr_code) in matches {
            let mut frame = Frame {
                vals: &mut val_vec[..],
            };
            match pat_code.eval_f1(r, &mut frame, arg) {
                Ok(Val::Bool(true)) => {
                    // We got a match, and value(s) were bound to the frame.
                    // Now evaluate the expression.
                    return expr_code.eval_f0(r, &mut frame);
                }
                Ok(_) => {
                    // This one did not match.
                    // Carry on to the next pattern-expression pair.
                }
                Err(e) => return Err(e),
            }
        }
        Err(MorelError::Bind)
    }

    pub(crate) fn assign(&mut self, ordinal: usize, a0: &Val) {
        self.vals[ordinal] = a0.clone();
    }
}

/// Evaluation environment for [Code].
///
/// Function parameters holding an evaluation environment are typically named
/// `r`.
pub struct EvalEnv<'a> {
    pub session: &'a Session,
    pub shell: &'a Shell,
    effects: &'a mut Vec<Effect>,
    link_codes: Vec<Code>,
}

impl<'a> EvalEnv<'a> {
    pub(crate) fn new(
        session: &'a Session,
        shell: &'a Shell,
        effects: &'a mut Vec<Effect>,
        link_codes: &[Code],
    ) -> Self {
        EvalEnv {
            session,
            shell,
            effects,
            link_codes: link_codes.to_vec(),
        }
    }
}

impl EvalEnv<'_> {
    /// Emits an effect to be applied later.
    pub fn emit_effect(&mut self, effect: Effect) {
        self.effects.push(effect);
    }
}

/// Implementation of a function is an [Eager2] or ...
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Impl {
    // lint: sort until '#}'
    Custom,
    E0(Eager0),
    E1(Eager1),
    E2(Eager2),
    E3(Eager3),
    EV2(EagerV2),
}

pub struct Applicable;

/// Function implementation that takes no arguments (constants).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager0 {
    // lint: sort until '#}'
    BoolFalse,
    BoolTrue,
    ListNil,
    OptionNone,
}

impl Eager0 {
    // Passing Val by value is OK because it is small.
    fn apply(&self) -> Val {
        match &self {
            // lint: sort until '#}' where 'Eager0::'
            Eager0::BoolFalse => Val::Bool(false),
            Eager0::BoolTrue => Val::Bool(true),
            Eager0::ListNil => Val::List(vec![]),
            Eager0::OptionNone => {
                // TODO: Proper option none implementation
                Val::Unit
            }
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::E0(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }
}

/// Function implementation that takes one argument.
/// The argument is eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager1 {
    // lint: sort until '#}'
    IntNegate,
    OptionSome,
    RealNegate,
}

impl Eager1 {
    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val) -> Val {
        match &self {
            // lint: sort until '#}' where 'Eager1::'
            Eager1::IntNegate => Val::Int(-a0.expect_int()),
            Eager1::OptionSome => {
                // TODO: Proper option some implementation
                // For now return the value
                a0
            }
            Eager1::RealNegate => Val::Real(-a0.expect_real()),
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::E1(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }
}

/// Function implementation that takes two arguments.
/// The arguments are eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager2 {
    // lint: sort until '#}'
    BoolAndAlso,
    BoolImplies,
    BoolOpEq,
    BoolOpNe,
    BoolOrElse,
    CharOpEq,
    CharOpGe,
    CharOpGt,
    CharOpLe,
    CharOpLt,
    CharOpNe,
    IntDiv,
    IntMinus,
    IntMod,
    IntOpEq,
    IntOpGe,
    IntOpGt,
    IntOpLe,
    IntOpLt,
    IntOpNe,
    IntPlus,
    IntTimes,
    ListOpCons,
    RealDivide,
    RealOpEq,
    RealOpGe,
    RealOpGt,
    RealOpLe,
    RealOpLt,
    RealOpMinus,
    RealOpNe,
    RealOpPlus,
    RealOpTimes,
    StringOpEq,
    StringOpGe,
    StringOpGt,
    StringOpLe,
    StringOpLt,
    StringOpNe,
}

impl Eager2 {
    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val, a1: Val) -> Val {
        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            Eager2::BoolAndAlso => {
                Val::Bool(a0.expect_bool() && a1.expect_bool())
            }
            Eager2::BoolImplies => {
                Val::Bool(!a0.expect_bool() || a1.expect_bool())
            }
            Eager2::BoolOpEq => Val::Bool(a0.expect_bool() == a1.expect_bool()),
            Eager2::BoolOpNe => Val::Bool(a0.expect_bool() != a1.expect_bool()),
            Eager2::BoolOrElse => {
                Val::Bool(a0.expect_bool() || a1.expect_bool())
            }
            Eager2::CharOpEq => Val::Bool(a0.expect_char() == a1.expect_char()),
            Eager2::CharOpGe => Val::Bool(a0.expect_char() >= a1.expect_char()),
            Eager2::CharOpGt => Val::Bool(a0.expect_char() > a1.expect_char()),
            Eager2::CharOpLe => Val::Bool(a0.expect_char() <= a1.expect_char()),
            Eager2::CharOpLt => Val::Bool(a0.expect_char() < a1.expect_char()),
            Eager2::CharOpNe => Val::Bool(a0.expect_char() != a1.expect_char()),
            Eager2::IntDiv => Val::Int(a0.expect_int() / a1.expect_int()),
            Eager2::IntMinus => Val::Int(a0.expect_int() - a1.expect_int()),
            Eager2::IntMod => Val::Int(a0.expect_int() % a1.expect_int()),
            Eager2::IntOpEq => Val::Bool(a0.expect_int() == a1.expect_int()),
            Eager2::IntOpGe => Val::Bool(a0.expect_int() >= a1.expect_int()),
            Eager2::IntOpGt => Val::Bool(a0.expect_int() > a1.expect_int()),
            Eager2::IntOpLe => Val::Bool(a0.expect_int() <= a1.expect_int()),
            Eager2::IntOpLt => Val::Bool(a0.expect_int() < a1.expect_int()),
            Eager2::IntOpNe => Val::Bool(a0.expect_int() != a1.expect_int()),
            Eager2::IntPlus => Val::Int(a0.expect_int() + a1.expect_int()),
            Eager2::IntTimes => Val::Int(a0.expect_int() * a1.expect_int()),
            Eager2::ListOpCons => {
                let mut list = vec![a0];
                if let Val::List(mut rest) = a1 {
                    list.append(&mut rest);
                } else {
                    // If a1 is not a list, treat it as a single element
                    list.push(a1);
                }
                Val::List(list)
            }
            Eager2::RealDivide => {
                Val::Real(a0.expect_real() / a1.expect_real())
            }
            Eager2::RealOpEq => Val::Bool(a0.expect_real() == a1.expect_real()),
            Eager2::RealOpGe => Val::Bool(a0.expect_real() >= a1.expect_real()),
            Eager2::RealOpGt => Val::Bool(a0.expect_real() > a1.expect_real()),
            Eager2::RealOpLe => Val::Bool(a0.expect_real() <= a1.expect_real()),
            Eager2::RealOpLt => Val::Bool(a0.expect_real() < a1.expect_real()),
            Eager2::RealOpMinus => {
                Val::Real(a0.expect_real() - a1.expect_real())
            }
            Eager2::RealOpNe => Val::Bool(a0.expect_real() != a1.expect_real()),
            Eager2::RealOpPlus => {
                Val::Real(a0.expect_real() + a1.expect_real())
            }
            Eager2::RealOpTimes => {
                Val::Real(a0.expect_real() * a1.expect_real())
            }
            Eager2::StringOpEq => {
                Val::Bool(a0.expect_string() == a1.expect_string())
            }
            Eager2::StringOpGe => {
                Val::Bool(a0.expect_string() >= a1.expect_string())
            }
            Eager2::StringOpGt => {
                Val::Bool(a0.expect_string() > a1.expect_string())
            }
            Eager2::StringOpLe => {
                Val::Bool(a0.expect_string() <= a1.expect_string())
            }
            Eager2::StringOpLt => {
                Val::Bool(a0.expect_string() < a1.expect_string())
            }
            Eager2::StringOpNe => {
                Val::Bool(a0.expect_string() != a1.expect_string())
            }
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::E2(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }
}

/// Function implementation that takes two arguments and an evaluation
/// environment.
///
/// The environment is not required for evaluating arguments -- the arguments
/// are eagerly evaluated before the function is called -- but allows the
/// implementation to have side effects such as modifying the state of the
/// session.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EagerV2 {
    // lint: sort until '#}'
    SysSet,
}

impl EagerV2 {
    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::EV2(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }

    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(
        &self,
        r: &mut EvalEnv,
        _f: &mut Frame,
        a0: Val,
        a1: Val,
    ) -> Result<Val, MorelError> {
        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            SysSet => {
                let prop = a0.expect_string();
                let val = a1;
                r.emit_effect(Effect::SetShellProp(prop, val));
                Ok(Val::Unit)
            }
        }
    }
}

/// Function implementation that takes three arguments.
/// The arguments are eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager3 {
    // lint: sort until '#}'
    BoolIf,
}

impl Eager3 {
    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val, a1: Val, a2: Val) -> Val {
        match &self {
            Eager3::BoolIf => {
                if a0.expect_bool() {
                    a1
                } else {
                    a2
                }
            }
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::E3(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }
}

/// Enumerates built-in functions that have a custom implementation.
#[allow(clippy::enum_variant_names)]
enum Custom {
    // lint: sort until '#}'
    GOpEq,
    GOpGe,
    GOpGt,
    GOpLe,
    GOpLt,
    GOpMinus,
    GOpNe,
    GOpNegate,
    GOpPlus,
    GOpTimes,
}

impl Custom {
    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val, a1: Val) -> Val {
        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            Custom::GOpEq => Val::Bool(a0 == a1),
            Custom::GOpGe => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x >= y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x >= y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(x >= y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x >= y),
                _ => panic!("Type error in >= comparison"),
            },
            Custom::GOpGt => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x > y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x > y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(x & !y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x > y),
                _ => panic!("Type error in > comparison"),
            },
            Custom::GOpLe => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x <= y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x <= y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(x <= y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x <= y),
                _ => panic!("Type error in <= comparison"),
            },
            Custom::GOpLt => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x < y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x < y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(!x & y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x < y),
                _ => panic!("Type error in < comparison"),
            },
            Custom::GOpMinus => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Int(x - y),
                (Val::Real(x), Val::Real(y)) => Val::Real(x - y),
                _ => panic!("Type error in - operation"),
            },
            Custom::GOpNe => Val::Bool(a0 != a1),
            Custom::GOpNegate => match a0 {
                Val::Int(_) => Eager1::IntNegate.apply(a0),
                Val::Real(_) => Eager1::RealNegate.apply(a0),
                _ => panic!("Type error in ~ operation"),
            },
            Custom::GOpPlus => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Int(x + y),
                (Val::Real(x), Val::Real(y)) => Val::Real(x + y),
                _ => panic!("Type error in + operation"),
            },
            Custom::GOpTimes => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Int(x * y),
                (Val::Real(x), Val::Real(y)) => Val::Real(x * y),
                _ => panic!("Type error in * operation"),
            },
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::Custom).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }
}

pub struct Lib {
    pub fn_map: BTreeMap<BuiltInFunction, (Type, Impl)>,
    pub structure_map: BTreeMap<BuiltInRecord, (Type, Val)>,
    pub name_to_built_in: HashMap<String, BuiltIn>,
}

#[derive(Default)]
struct LibBuilder {
    fn_types: BTreeMap<BuiltInFunction, Type>,
    fn_impls: BTreeMap<BuiltInFunction, Impl>,
}

pub static LIBRARY: LazyLock<Lib> = LazyLock::new(|| {
    #[allow(clippy::enum_glob_use)]
    use crate::compile::library::BuiltInFunction::*;

    let mut b: LibBuilder = Default::default();
    // lint: sort until '^$' erase '^.*, '
    Eager2::BoolAndAlso.implements(&mut b, BoolAndAlso);
    Eager0::BoolFalse.implements(&mut b, BoolFalse);
    Eager3::BoolIf.implements(&mut b, BoolIf);
    Eager2::BoolImplies.implements(&mut b, BoolImplies);
    Eager2::BoolOpEq.implements(&mut b, BoolOpEq);
    Eager2::BoolOpNe.implements(&mut b, BoolOpNe);
    Eager2::BoolOrElse.implements(&mut b, BoolOrElse);
    Eager0::BoolTrue.implements(&mut b, BoolTrue);
    Eager2::CharOpEq.implements(&mut b, CharOpEq);
    Eager2::CharOpGe.implements(&mut b, CharOpGe);
    Eager2::CharOpGt.implements(&mut b, CharOpGt);
    Eager2::CharOpLe.implements(&mut b, CharOpLe);
    Eager2::CharOpLt.implements(&mut b, CharOpLt);
    Eager2::CharOpNe.implements(&mut b, CharOpNe);
    Custom::GOpEq.implements(&mut b, GOpEq);
    Custom::GOpGe.implements(&mut b, GOpGe);
    Custom::GOpGt.implements(&mut b, GOpGt);
    Custom::GOpLe.implements(&mut b, GOpLe);
    Custom::GOpLt.implements(&mut b, GOpLt);
    Custom::GOpMinus.implements(&mut b, GOpMinus);
    Custom::GOpNe.implements(&mut b, GOpNe);
    Custom::GOpNegate.implements(&mut b, GOpNegate);
    Custom::GOpPlus.implements(&mut b, GOpPlus);
    Custom::GOpTimes.implements(&mut b, GOpTimes);
    Eager2::IntDiv.implements(&mut b, IntDiv);
    Eager2::IntMinus.implements(&mut b, IntMinus);
    Eager2::IntMod.implements(&mut b, IntMod);
    Eager1::IntNegate.implements(&mut b, IntNegate);
    Eager2::IntOpEq.implements(&mut b, IntOpEq);
    Eager2::IntOpGe.implements(&mut b, IntOpGe);
    Eager2::IntOpGt.implements(&mut b, IntOpGt);
    Eager2::IntOpLe.implements(&mut b, IntOpLe);
    Eager2::IntOpLt.implements(&mut b, IntOpLt);
    Eager2::IntOpNe.implements(&mut b, IntOpNe);
    Eager2::IntPlus.implements(&mut b, IntPlus);
    Eager2::IntTimes.implements(&mut b, IntTimes);
    Eager0::ListNil.implements(&mut b, ListNil);
    Eager2::ListOpCons.implements(&mut b, ListOpCons);
    Eager0::OptionNone.implements(&mut b, OptionNone);
    Eager1::OptionSome.implements(&mut b, OptionSome);
    Eager2::RealDivide.implements(&mut b, RealDivide);
    Eager1::RealNegate.implements(&mut b, RealNegate);
    Eager2::RealOpEq.implements(&mut b, RealOpEq);
    Eager2::RealOpGe.implements(&mut b, RealOpGe);
    Eager2::RealOpGt.implements(&mut b, RealOpGt);
    Eager2::RealOpLe.implements(&mut b, RealOpLe);
    Eager2::RealOpLt.implements(&mut b, RealOpLt);
    Eager2::RealOpMinus.implements(&mut b, RealOpMinus);
    Eager2::RealOpNe.implements(&mut b, RealOpNe);
    Eager2::RealOpPlus.implements(&mut b, RealOpPlus);
    Eager2::RealOpTimes.implements(&mut b, RealOpTimes);
    Eager2::StringOpEq.implements(&mut b, StringOpEq);
    Eager2::StringOpGe.implements(&mut b, StringOpGe);
    Eager2::StringOpGt.implements(&mut b, StringOpGt);
    Eager2::StringOpLe.implements(&mut b, StringOpLe);
    Eager2::StringOpLt.implements(&mut b, StringOpLt);
    Eager2::StringOpNe.implements(&mut b, StringOpNe);
    EagerV2::SysSet.implements(&mut b, SysSet);

    b.build()
});

impl LibBuilder {
    fn build(&mut self) -> Lib {
        // Populate a table of functions and structures that are in the global
        // namespace.
        let mut name_to_built_in: HashMap<String, BuiltIn> = HashMap::new();

        // Populate a table of functions and their types.
        let mut fn_map: BTreeMap<BuiltInFunction, (Type, Impl)> =
            BTreeMap::new();

        // Populate a table of structures and the functions that belong to them.
        let mut structure_names_fns: BTreeMap<
            BuiltInRecord,
            BTreeMap<String, BuiltInFunction>,
        > = BTreeMap::new();
        for f in BuiltInFunction::iter() {
            let type_code = f.get_str("type").expect("type");
            let name = f.get_str("name").expect("name");
            let global = f.get_bool("global").unwrap_or_default();

            let t = type_parser::string_to_type(type_code);
            if let Some(fn_impl) = self.fn_impls.remove(&f) {
                fn_map.insert(f, (*t, fn_impl));
            } else {
                panic!("missing implementation for {:?}", f);
            }

            if global {
                name_to_built_in.insert(name.to_string(), BuiltIn::Fn(f));
            }

            if let Some((parent, name)) = BuiltIn::Fn(f).heritage()
                && let Ok(r) = BuiltInRecord::from_str(parent)
            {
                structure_names_fns
                    .entry(r)
                    .or_default()
                    .insert(name.to_string(), f);
            }
            // Skip functions with parents that aren't records
            // (like "G" for global)
        }

        let mut structure_map = BTreeMap::new();
        for (r, names_fns) in &mut structure_names_fns {
            let mut vals = Vec::new();
            let mut name_types: BTreeMap<Label, Type> = BTreeMap::new();
            for (n, f) in names_fns {
                vals.push(Val::Fn(*f));
                let t = &fn_map.get(f).unwrap().0;
                name_types.insert(Label::String(n.clone()), t.clone());
            }
            let t = Type::Record(false, name_types.clone());
            structure_map.insert(*r, (t, Val::List(vals)));
        }

        for r in BuiltInRecord::iter() {
            let name = r.get_str("name").expect("name");
            name_to_built_in.insert(name.to_string(), BuiltIn::Record(r));
        }

        Lib {
            fn_map,
            structure_map,
            name_to_built_in,
        }
    }
}
