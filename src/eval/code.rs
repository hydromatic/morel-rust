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
use crate::eval::char::Char;
use crate::eval::frame::FrameDef;
use crate::eval::int::Int;
use crate::eval::list::List;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::main::{MorelError, Shell};
use std::collections::{BTreeMap, HashMap};
use std::fmt::{Display, Formatter};
use std::iter::zip;
use std::ops::Deref;
use std::str::FromStr;
use std::sync::{Arc, LazyLock};
use strum::{EnumProperty, IntoEnumIterator};

/// Evaluation mode.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum EvalMode {
    /// Evaluation with a frame and no arguments.
    EagerF0,
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
    // lint: sort until '#}' where '##[A-Z]'
    /// Adds a binding to the environment.
    AddBinding(Binding),
    /// Emits a piece of code.
    EmitCode(Arc<Code>),
    /// Emits an output line.
    EmitLine(String),
    /// Sets a session property.
    SetSessionProp(String, Val),
    /// Sets a shell property.
    SetShellProp(String, Val),
    /// Unsets a shell property.
    UnsetShellProp(String),
}

/// Generated code that can be evaluated.
#[derive(Clone, Debug, PartialEq)]
pub enum Code {
    // lint: sort until '#}' where '##[A-Z][A-Za-z0-9]*\('
    /// `Apply(fn_code, arg_code)` calls a function.
    Apply(Box<Code>, Box<Code>),
    /// `ApplyClosure(fn_code, arg_code, bind_codes)` calls a closure.
    ApplyClosure(Box<Code>, Box<Code>, Vec<Code>),
    /// `ApplyConstant(fn_code, arg_code)` calls a function whose code is known
    /// at compile time.
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
    /// variable in the current frame. `name` is for debugging.
    BindSlot(Arc<FrameDef>, usize),
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

    /// `Constant(val)` returns the value `val`.
    Constant(Val),

    /// `CreateClosure(frame, matches, binds)` creates a [Val::Closure] value
    /// that is similar to a function, but has a frame pre-populated with one
    /// or more values.
    CreateClosure(Arc<FrameDef>, Vec<(Code, Code)>, Vec<Code>),

    /// `Fn(frame, pat_expr_codes)` first creates a frame to contain the
    /// required local variables, next iterates the (pattern, expression) pairs
    /// until it can bind the argument to a pattern and finally evaluates the
    /// expression.
    Fn(Arc<FrameDef>, Vec<(Code, Code)>),

    /// `GetLocal(frame_def, slot)` returns the value of the `slot`th variable
    /// in the current stack frame.
    /// `frame_def` is for debugging. See [Code::BindSlot].
    GetLocal(Arc<FrameDef>, usize),

    /// `Let(codes, result_code)` evaluates all the `codes` in the current
    /// frame, to bind values to variables, then evaluates the result code.
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
    NativeF0(EagerF0),
    NativeF1(EagerF1, Box<Code>),
    NativeF2(EagerF2, Box<Code>, Box<Code>),
    /// `Nth(Type, slot)` returns the `slot`th element of a record.
    /// The type must be a record type.
    Nth(Box<Type>, usize),
    Tuple(Vec<Code>),
}

impl Code {
    // lint: sort until '#}' where '##pub'
    pub(crate) fn new_apply(f: &Code, a: &Code, refs: &[Binding]) -> Code {
        if !refs.is_empty() {
            let bind_codes: Vec<Code> = Vec::new();
            Code::ApplyClosure(
                Box::new(f.clone()),
                Box::new(a.clone()),
                bind_codes,
            )
        } else if let Code::Constant(Val::Code(c)) = f {
            Code::ApplyConstant(
                Box::new(c.deref().clone()),
                Box::new(a.clone()),
            )
        } else {
            Code::Apply(Box::new(f.clone()), Box::new(a.clone()))
        }
    }

    pub(crate) fn new_bind(pat_code: &Code, expr_code: &Code) -> Code {
        Code::Bind(Box::new((pat_code.clone(), expr_code.clone())))
    }

    pub(crate) fn new_bind_cons(h: &Code, t: &Code) -> Code {
        Code::BindCons(Box::new(h.clone()), Box::new(t.clone()))
    }

    pub(crate) fn new_bind_constructor(
        type_: &Type,
        name: &str,
        t: &Option<Code>,
    ) -> Code {
        if let Some(t) = t {
            Code::BindConstructor(name.to_string(), Box::new(t.clone()))
        } else if let Type::Data(type_name, _) = type_
            && type_name == "option"
        {
            // Option value NONE is represented by Unit
            Self::new_bind_literal(&Val::Unit)
        } else {
            Self::new_bind_literal(&Val::String(name.to_string()))
        }
    }

    pub(crate) fn new_bind_list(codes: &[Code]) -> Code {
        codes.iter().for_each(|code| {
            code.assert_supports_eval_mode(&EvalMode::EagerV1)
        });
        Code::BindList(codes.to_vec())
    }

    pub(crate) fn new_bind_literal(val: &Val) -> Code {
        Code::BindLiteral(val.clone())
    }

    pub(crate) fn new_bind_slot(
        frame_def: &Arc<FrameDef>,
        slot: usize,
    ) -> Code {
        assert!(slot < frame_def.bound_vars.len() + frame_def.local_vars.len());
        Code::BindSlot(frame_def.clone(), slot)
    }

    pub(crate) fn new_bind_tuple(codes: &[Code]) -> Code {
        codes.iter().for_each(|code| {
            code.assert_supports_eval_mode(&EvalMode::EagerV1)
        });
        Code::BindTuple(codes.to_vec())
    }

    pub(crate) fn new_constant(v: Val) -> Code {
        Code::Constant(v)
    }

    pub(crate) fn new_create_closure(
        frame_def: &Arc<FrameDef>,
        pat_expr_codes: &[(Code, Code)],
        bind_codes: &[Code],
    ) -> Code {
        // If there are no refs, you don't need a closure; a fn is enough.
        assert!(!frame_def.bound_vars.is_empty());
        assert_eq!(frame_def.bound_vars.len(), bind_codes.len());

        for (pat_code, _) in pat_expr_codes {
            pat_code.assert_supports_eval_mode(&EvalMode::EagerV1);
        }
        Code::CreateClosure(
            frame_def.clone(),
            pat_expr_codes.to_vec(),
            bind_codes.to_vec(),
        )
    }

    pub(crate) fn new_fn(
        frame_def: &Arc<FrameDef>,
        pat_expr_codes: &[(Code, Code)],
    ) -> Code {
        // Check there are no bound variables. If variables are bound, you need
        // a closure, not a fn.
        assert!(frame_def.bound_vars.is_empty());

        // REVIEW A function could also support Eager1 (without environment)
        // if it does not use global variables or have effects. The environment
        // is currently necessary to create a frame.
        for (pat_code, _) in pat_expr_codes {
            pat_code.assert_supports_eval_mode(&EvalMode::EagerV1);
        }
        Code::Fn(frame_def.clone(), pat_expr_codes.to_vec())
    }

    pub(crate) fn new_get_local(
        frame_def: &Arc<FrameDef>,
        slot: usize,
    ) -> Code {
        Code::GetLocal(frame_def.clone(), slot)
    }

    pub(crate) fn new_let(match_codes: &[Code], result_code: Code) -> Code {
        Code::Let(match_codes.to_vec(), Box::new(result_code))
    }

    pub(crate) fn new_link(slot: usize, name: &str) -> Code {
        Code::Link(slot, name.to_string())
    }

    pub(crate) fn new_match(codes: &[Code]) -> Code {
        assert_eq!(codes.len() % 2, 1);
        codes.iter().enumerate().for_each(|(i, code)| {
            code.assert_supports_eval_mode(if i % 2 == 0 {
                &EvalMode::EagerF0
            } else {
                &EvalMode::EagerV1
            })
        });
        Code::Case(codes.to_vec())
    }

    pub(crate) fn new_native(
        impl_: Impl,
        codes: &[Box<Code>],
        span: &Span,
    ) -> Code {
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
                Code::Native1(e1, codes[0].clone())
            }
            Impl::E2(e2) => {
                assert_eq!(codes.len(), 2);
                Code::Native2(e2, codes[0].clone(), codes[1].clone())
            }
            Impl::E3(e3) => {
                assert_eq!(codes.len(), 3);
                Code::Native3(
                    e3,
                    codes[0].clone(),
                    codes[1].clone(),
                    codes[2].clone(),
                )
            }
            Impl::EF0(ev0) => {
                assert_eq!(codes.len(), 1);
                assert!(matches!(*codes[0], Code::Constant(Val::Unit)));
                Code::NativeF0(ev0)
            }
            Impl::EF1(ev1) => {
                assert_eq!(codes.len(), 1);
                Code::NativeF1(ev1, codes[0].clone())
            }
            Impl::EF2(ev2) => {
                // TODO: handle cases like 'let args = (1, 2) in f args
                // end'; see Gather in Morel-Java
                Code::NativeF2(
                    ev2,
                    codes[0].clone(),
                    code_or_span(codes, span, 1),
                )
            }
        }
    }

    pub fn new_list(codes: &[Code]) -> Code {
        Self::new_tuple(codes)
    }

    pub fn new_nth(type_: &Type, slot: usize) -> Code {
        assert!(slot < type_.expect_record().1.len());
        Code::Nth(Box::new(type_.clone()), slot)
    }

    pub fn new_tuple(codes: &[Code]) -> Code {
        Code::Tuple(codes.to_vec())
    }

    pub(crate) fn assert_supports_eval_mode(&self, eval_mode: &EvalMode) {
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
            Code::ApplyClosure(_, _, _) => *mode == EvalMode::Eager0,
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
                *mode == EvalMode::Eager0 || *mode == EvalMode::EagerF0
            }
            Code::CreateClosure(_, _, _) => *mode == EvalMode::EagerF0,
            Code::Fn(_, _) => *mode == EvalMode::EagerV1,
            Code::GetLocal(_, _) => *mode == EvalMode::EagerF0,
            Code::Let(_, _) => *mode == EvalMode::Eager0,
            Code::Link(_, _) => todo!("{:?}", self),
            Code::Native0(_) => *mode == EvalMode::Eager0,
            Code::Native1(_, _) => {
                *mode == EvalMode::Eager1 || *mode == EvalMode::EagerF0
            }
            Code::Native2(_, _, _) => {
                *mode == EvalMode::Eager2 || *mode == EvalMode::EagerF0
            }
            Code::Native3(_, _, _, _) => *mode == EvalMode::Eager3,
            Code::NativeF0(_) => *mode == EvalMode::EagerF0,
            Code::NativeF1(_, _) => *mode == EvalMode::EagerV1,
            Code::NativeF2(_, _, _) => *mode == EvalMode::EagerV2,
            Code::Nth(_, _) => {
                *mode == EvalMode::Eager1 || *mode == EvalMode::EagerF0
            }
            Code::Tuple(_) => *mode == EvalMode::EagerF0,
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
                let fn_ = fn_code.eval_f0(r, f)?;
                let arg = arg_code.eval_f0(r, f)?;
                match &fn_ {
                    Val::Code(c) => c.eval_f1(r, f, &arg),
                    Val::Closure(frame_def, matches, bound_vals) => {
                        Frame::create_bind_and_eval(
                            frame_def, matches, bound_vals, r, &arg,
                        )
                    }
                    _ => panic!("Expected code"),
                }
            }
            Code::ApplyClosure(fn_code, arg_code, _bind_codes) => {
                let arg = arg_code.eval_f0(r, f)?;
                let fun = fn_code.eval_f0(r, f)?;
                fun.expect_code().eval_f1(r, f, &arg)
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
            Code::CreateClosure(frame_def, matches, bind_codes) => {
                let mut values = Vec::with_capacity(bind_codes.len());
                for bind_code in bind_codes {
                    values.push(bind_code.eval_f0(r, f)?);
                }
                Ok(Val::Closure(frame_def.clone(), matches.clone(), values))
            }
            Code::Fn(_, _) | Code::Nth(_, _) => {
                // Fn and Nth are practically literals. When evaluated, they
                // return themselves.
                Ok(Val::Code(Arc::new(self.clone())))
            }
            Code::GetLocal(frame_def, slot) => {
                debug_assert!(
                    f.has_def(frame_def),
                    "bad frame in GetLocal({}, {})",
                    frame_def.description,
                    slot
                );
                Ok(f.vals[*slot].clone())
            }
            Code::Let(codes, result_code) => {
                // REVIEW: Could codes and result_code be merged into one vec?
                for code in codes {
                    code.eval_f0(r, f)?;
                }
                result_code.eval_f0(r, f)
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
            Code::NativeF0(eager) => Ok(eager.apply(r, f)),
            Code::NativeF1(eager, code0) => {
                let v0 = code0.eval_f0(r, f)?;
                eager.apply(r, f, v0)
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
            Code::Apply(fn_code, arg_code) => {
                let fun = fn_code.eval_f0(r, f)?;
                let arg = arg_code.eval_f0(r, f)?;
                let closure = fun.expect_code().eval_f1(r, f, &arg)?;
                match closure {
                    Val::Closure(frame_def, matches, bound_vals) => {
                        Frame::create_bind_and_eval(
                            &frame_def,
                            &matches,
                            &bound_vals,
                            r,
                            a0,
                        )
                    }
                    _ => panic!("Expected closure"),
                }
            }
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
                match a0 {
                    Val::Some(a) => pat_code.eval_f1(r, f, a),
                    _ => Ok(Val::Bool(false)),
                }
            }
            Code::BindList(codes) => {
                let list = a0.expect_list();
                if list.len() != codes.len() {
                    return Ok(Val::Bool(false));
                }
                Self::eval_all_f1(r, f, codes, list)
            }
            Code::BindLiteral(val) => Ok(Val::Bool(a0 == val)),
            Code::BindSlot(frame_def, slot) => {
                debug_assert!(
                    f.has_def(frame_def),
                    "bad frame in BindSlot(frame '{}', slot {})",
                    frame_def.description,
                    slot
                );
                f.vals[*slot] = a0.clone();
                Ok(Val::Bool(true))
            }
            Code::BindTuple(codes) => {
                let list = a0.expect_list();
                Self::eval_all_f1(r, f, codes, list)
            }
            Code::BindWildcard => Ok(Val::Bool(true)),
            Code::Constant(v) => Ok(v.clone()),
            Code::Fn(frame_def, pat_expr_codes) => {
                Frame::create_and_eval(frame_def, pat_expr_codes, r, a0)
            }
            Code::Link(slot, _) => {
                let code = r.link_codes[*slot].clone();
                code.eval_f1(r, f, a0)
            }
            Code::Nth(_, slot) => Ok(a0.expect_list()[*slot].clone()),
            _ => {
                todo!("eval: {:?}", self)
            }
        }
    }

    fn eval_all_f1(
        r: &mut EvalEnv,
        f: &mut Frame,
        codes: &[Code],
        list: &[Val],
    ) -> Result<Val, MorelError> {
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
}

fn code_or_span(codes: &[Box<Code>], span: &Span, n: usize) -> Box<Code> {
    if codes.len() == n + 1 {
        codes[n].clone()
    } else {
        assert_eq!(codes.len(), n);
        Box::new(Code::Constant(Val::String(span.0.clone())))
    }
}

impl Display for Code {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Code::BindLiteral(v) => write!(f, "{}", v),
            Code::Constant(v) => match v {
                Val::String(s) => write!(f, "constant({})", s),
                _ => write!(f, "constant({})", v),
            },
            Code::Fn(_, matches) => {
                write!(f, "fn(")?;
                let mut first = true;
                for (pat, expr) in matches {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} => {}", pat, expr)?;
                }
                write!(f, ")")
            }
            Code::Native2(eager, code0, code1) => {
                write!(
                    f,
                    "apply2(fnValue {}, {}, {})",
                    eager.plan(),
                    code0,
                    code1
                )
            }
            Code::NativeF2(eager, code0, code1) => {
                write!(
                    f,
                    "apply(fnValue {}, argCode tuple({}, {}))",
                    eager.plan(),
                    code0,
                    code1
                )
            }
            _ => todo!("fmt: {:?}", self),
        }
    }
}

/// Code location.
#[derive(Clone, Debug, PartialEq)]
pub struct Span(String);

impl Span {
    pub fn new(s: &str) -> Self {
        Span(s.to_string())
    }

    pub fn from_pest_span(span: &pest::Span) -> Self {
        let start = span.start_pos().line_col();
        let end = span.end_pos().line_col();
        Self::new(&format!(
            "stdIn:{}.{}-{}.{}",
            start.0, start.1, end.0, end.1
        ))
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Stack frame for evaluating [Code].
pub struct Frame<'a> {
    pub vals: &'a mut [Val],
}

impl<'a> Frame<'a> {
    /// Returns whether this frame is consistent with the given definition.
    /// We can't be sure because the definition is not stored in the frame.
    pub(crate) fn has_def(&self, frame_def: &Arc<FrameDef>) -> bool {
        self.vals.len()
            == frame_def.local_vars.len() + frame_def.bound_vars.len()
    }
}

impl<'a> Frame<'a> {
    /// Creates a frame, binds an argument to one of several patterns,
    /// and executes the corresponding expression.
    ///
    /// This is the implementation of a function call.
    fn create_and_eval(
        frame_def: &FrameDef,
        matches: &[(Code, Code)],
        r: &mut EvalEnv,
        arg: &Val,
    ) -> Result<Val, MorelError> {
        assert!(frame_def.bound_vars.is_empty());
        let mut val_vec: Vec<Val> =
            vec![Val::Char('a'); frame_def.local_vars.len()];
        Self::eval(&mut val_vec, matches, r, arg)
    }

    fn create_bind_and_eval(
        frame_def: &FrameDef,
        matches: &[(Code, Code)],
        bound_vals: &[Val],
        r: &mut EvalEnv,
        arg: &Val,
    ) -> Result<Val, MorelError> {
        let mut val_vec: Vec<Val> = bound_vals
            .iter()
            .cloned()
            .chain(std::iter::repeat_n(Val::Unit, frame_def.local_vars.len()))
            .collect();
        Self::eval(&mut val_vec, matches, r, arg)
    }

    fn eval(
        val_vec: &mut [Val],
        matches: &[(Code, Code)],
        r: &mut EvalEnv,
        arg: &Val,
    ) -> Result<Val, MorelError> {
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
    EF0(EagerF0),
    EF1(EagerF1),
    EF2(EagerF2),
}

pub struct Applicable;

/// Function implementation that takes no arguments (constants).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager0 {
    // lint: sort until '#}'
    BoolFalse,
    BoolTrue,
    IntMaxInt,
    IntMinInt,
    IntPrecision,
    ListNil,
    OptionNone,
    OrderEqual,
    OrderGreater,
    OrderLess,
}

impl Eager0 {
    fn apply(&self) -> Val {
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::Eager0::*;

        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            BoolFalse => Val::Bool(false),
            BoolTrue => Val::Bool(true),
            IntMaxInt => Val::Some(Box::new(Val::Int(i32::MAX))),
            IntMinInt => Val::Some(Box::new(Val::Int(i32::MIN))),
            IntPrecision => Val::Some(Box::new(Val::Int(32))),
            ListNil => Val::List(vec![]),
            OptionNone => Val::Unit,
            OrderEqual => Val::Int(0),
            OrderGreater => Val::Int(1),
            OrderLess => Val::Int(-1),
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::E0(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }
}

/// Function implementation that takes no arguments and an evaluation
/// environment.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EagerF0 {
    // lint: sort until '#}'
    SysPlan,
}

impl EagerF0 {
    fn apply(&self, r: &mut EvalEnv, _f: &mut Frame) -> Val {
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::EagerF0::*;

        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            SysPlan => {
                let s = if let Some(c) = r.session.code.as_ref() {
                    if let Code::Fn(_, matches) = c.deref()
                        && matches.len() == 1
                    {
                        format!("{}", matches[0].1)
                    } else {
                        format!("{}", c)
                    }
                } else {
                    "".to_string()
                };
                Val::String(s)
            }
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::EF0(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }
}

/// Function implementation that takes one argument and an evaluation
/// environment.
///
/// The environment is not required for evaluating arguments -- the arguments
/// are eagerly evaluated before the function is called -- but allows the
/// implementation to have side effects such as modifying the state of the
/// session.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EagerF1 {
    // lint: sort until '#}'
    SysUnset,
}

impl EagerF1 {
    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::EF1(*self)).is_some() {
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
    ) -> Result<Val, MorelError> {
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::EagerF1::*;

        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            SysUnset => {
                let prop = a0.expect_string();
                r.emit_effect(Effect::UnsetShellProp(prop));
                Ok(Val::Unit)
            }
        }
    }
}

/// Function implementation that takes one argument.
/// The argument is eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager1 {
    // lint: sort until '#}'
    GeneralIgnore,
    IntAbs,
    IntFromInt,
    IntFromLarge,
    IntFromString,
    IntNegate,
    IntSign,
    IntToInt,
    IntToLarge,
    IntToString,
    OptionSome,
    RealNegate,
}

impl Eager1 {
    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val) -> Val {
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::Eager1::*;

        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            GeneralIgnore => Val::Unit,
            IntAbs => Val::Int(a0.expect_int().abs()),
            IntFromInt => a0,
            IntFromLarge => a0,
            IntFromString => match Int::from_string(&a0.expect_string()) {
                Some(n) => Val::Some(Box::new(Val::Int(n))),
                None => Val::Unit,
            },
            IntNegate => Val::Int(-a0.expect_int()),
            IntSign => Val::Int(Int::sign(a0.expect_int())),
            IntToInt => a0,
            IntToLarge => a0,
            IntToString => Val::String(Int::_to_string(a0.expect_int())),
            OptionSome => Val::Some(Box::new(a0)),
            RealNegate => Val::Real(-a0.expect_real()),
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
#[derive(Clone, Copy, Debug, strum_macros::Display, PartialEq)]
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
    GeneralOpO,
    IntCompare,
    IntDiv,
    IntMax,
    IntMin,
    IntMinus,
    IntMod,
    IntOpEq,
    IntOpGe,
    IntOpGt,
    IntOpLe,
    IntOpLt,
    IntOpNe,
    IntPlus,
    IntQuot,
    IntRem,
    IntSameSign,
    IntTimes,
    ListOpAt,
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
    StringOpCaret,
    StringOpEq,
    StringOpGe,
    StringOpGt,
    StringOpLe,
    StringOpLt,
    StringOpNe,
}

impl Eager2 {
    fn plan(&self) -> String {
        match self {
            Eager2::IntPlus => "+".to_string(),
            _ => self.to_string(),
        }
    }

    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val, a1: Val) -> Val {
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::Eager2::*;

        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            BoolAndAlso => Val::Bool(a0.expect_bool() && a1.expect_bool()),
            BoolImplies => Val::Bool(!a0.expect_bool() || a1.expect_bool()),
            BoolOpEq => Val::Bool(a0.expect_bool() == a1.expect_bool()),
            BoolOpNe => Val::Bool(a0.expect_bool() != a1.expect_bool()),
            BoolOrElse => Val::Bool(a0.expect_bool() || a1.expect_bool()),
            CharOpEq => Val::Bool(a0.expect_char() == a1.expect_char()),
            CharOpGe => Val::Bool(a0.expect_char() >= a1.expect_char()),
            CharOpGt => Val::Bool(a0.expect_char() > a1.expect_char()),
            CharOpLe => Val::Bool(a0.expect_char() <= a1.expect_char()),
            CharOpLt => Val::Bool(a0.expect_char() < a1.expect_char()),
            CharOpNe => Val::Bool(a0.expect_char() != a1.expect_char()),
            GeneralOpO => Val::Unit,
            IntCompare => {
                Val::Order(Int::compare(a0.expect_int(), a1.expect_int()))
            }
            IntDiv => Val::Int(Int::div(a0.expect_int(), a1.expect_int())),
            IntMax => Val::Int(a0.expect_int().max(a1.expect_int())),
            IntMin => Val::Int(a0.expect_int().min(a1.expect_int())),
            IntMinus => Val::Int(a0.expect_int() - a1.expect_int()),
            IntMod => Val::Int(Int::_mod(a0.expect_int(), a1.expect_int())),
            IntOpEq => Val::Bool(a0.expect_int() == a1.expect_int()),
            IntOpGe => Val::Bool(a0.expect_int() >= a1.expect_int()),
            IntOpGt => Val::Bool(a0.expect_int() > a1.expect_int()),
            IntOpLe => Val::Bool(a0.expect_int() <= a1.expect_int()),
            IntOpLt => Val::Bool(a0.expect_int() < a1.expect_int()),
            IntOpNe => Val::Bool(a0.expect_int() != a1.expect_int()),
            IntPlus => Val::Int(a0.expect_int() + a1.expect_int()),
            IntQuot => {
                let n1 = a0.expect_int();
                let n2 = a1.expect_int();
                Val::Int(n1 / n2) // Truncation towards zero
            }
            IntRem => {
                let n1 = a0.expect_int();
                let n2 = a1.expect_int();
                Val::Int(n1 - (n1 / n2) * n2) // Remainder after quot
            }
            IntSameSign => {
                let n1 = a0.expect_int();
                let n2 = a1.expect_int();
                Val::Bool((n1 >= 0 && n2 >= 0) || (n1 < 0 && n2 < 0))
            }
            IntTimes => Val::Int(a0.expect_int() * a1.expect_int()),
            ListOpAt => {
                Val::List(List::append(a0.expect_list(), a1.expect_list()))
            }
            ListOpCons => Val::List(List::cons(&a0, a1.expect_list())),
            RealDivide => Val::Real(a0.expect_real() / a1.expect_real()),
            RealOpEq => Val::Bool(a0.expect_real() == a1.expect_real()),
            RealOpGe => Val::Bool(a0.expect_real() >= a1.expect_real()),
            RealOpGt => Val::Bool(a0.expect_real() > a1.expect_real()),
            RealOpLe => Val::Bool(a0.expect_real() <= a1.expect_real()),
            RealOpLt => Val::Bool(a0.expect_real() < a1.expect_real()),
            RealOpMinus => Val::Real(a0.expect_real() - a1.expect_real()),
            RealOpNe => Val::Bool(a0.expect_real() != a1.expect_real()),
            RealOpPlus => Val::Real(a0.expect_real() + a1.expect_real()),
            RealOpTimes => Val::Real(a0.expect_real() * a1.expect_real()),
            StringOpCaret => Val::String(format!(
                "{}{}",
                a0.expect_string(),
                a1.expect_string()
            )),
            StringOpEq => Val::Bool(a0.expect_string() == a1.expect_string()),
            StringOpGe => Val::Bool(a0.expect_string() >= a1.expect_string()),
            StringOpGt => Val::Bool(a0.expect_string() > a1.expect_string()),
            StringOpLe => Val::Bool(a0.expect_string() <= a1.expect_string()),
            StringOpLt => Val::Bool(a0.expect_string() < a1.expect_string()),
            StringOpNe => Val::Bool(a0.expect_string() != a1.expect_string()),
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
#[derive(Clone, Copy, Debug, strum_macros::Display, PartialEq)]
pub enum EagerF2 {
    // lint: sort until '#}'
    CharChr,
    ListTabulate,
    SysSet,
}

impl EagerF2 {
    fn plan(&self) -> String {
        match self {
            EagerF2::CharChr => "Char.chr".to_string(),
            EagerF2::SysSet => "Sys.set".to_string(),
            EagerF2::ListTabulate => "List.tabulate".to_string(),
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        if b.fn_impls.insert(f, Impl::EF2(*self)).is_some() {
            panic!("Already implemented {:?}", f);
        }
    }

    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(
        &self,
        r: &mut EvalEnv,
        f: &mut Frame,
        a0: Val,
        a1: Val,
    ) -> Result<Val, MorelError> {
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::EagerF2::*;

        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            CharChr => Char::chr(a0.expect_int(), &a1.expect_span()),
            ListTabulate => {
                List::tabulate(r, f, a0.expect_int(), &a1.expect_code())
            }
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
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::Eager3::*;

        match &self {
            BoolIf => {
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

/// Built-in functions that have a custom implementation.
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
        #[expect(clippy::enum_glob_use)]
        use crate::eval::code::Custom::*;

        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            GOpEq => Val::Bool(a0 == a1),
            GOpGe => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x >= y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x >= y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(x >= y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x >= y),
                _ => panic!("Type error in >= comparison"),
            },
            GOpGt => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x > y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x > y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(x & !y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x > y),
                _ => panic!("Type error in > comparison"),
            },
            GOpLe => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x <= y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x <= y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(x <= y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x <= y),
                _ => panic!("Type error in <= comparison"),
            },
            GOpLt => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Bool(x < y),
                (Val::Real(x), Val::Real(y)) => Val::Bool(x < y),
                (Val::Bool(x), Val::Bool(y)) => Val::Bool(!x & y),
                (Val::Char(x), Val::Char(y)) => Val::Bool(x < y),
                _ => panic!("Type error in < comparison"),
            },
            GOpMinus => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Int(x - y),
                (Val::Real(x), Val::Real(y)) => Val::Real(x - y),
                _ => panic!("Type error in - operation"),
            },
            GOpNe => Val::Bool(a0 != a1),
            GOpNegate => match a0 {
                Val::Int(_) => Eager1::IntNegate.apply(a0),
                Val::Real(_) => Eager1::RealNegate.apply(a0),
                _ => panic!("Type error in ~ operation"),
            },
            GOpPlus => match (a0, a1) {
                (Val::Int(x), Val::Int(y)) => Val::Int(x + y),
                (Val::Real(x), Val::Real(y)) => Val::Real(x + y),
                _ => panic!("Type error in + operation"),
            },
            GOpTimes => match (a0, a1) {
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
    EagerF2::CharChr.implements(&mut b, CharChr);
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
    Eager1::GeneralIgnore.implements(&mut b, GeneralIgnore);
    Eager2::GeneralOpO.implements(&mut b, GeneralOpO);
    Eager1::IntAbs.implements(&mut b, IntAbs);
    Eager2::IntCompare.implements(&mut b, IntCompare);
    Eager2::IntDiv.implements(&mut b, IntDiv);
    Eager1::IntFromInt.implements(&mut b, IntFromInt);
    Eager1::IntFromLarge.implements(&mut b, IntFromLarge);
    Eager1::IntFromString.implements(&mut b, IntFromString);
    Eager2::IntMax.implements(&mut b, IntMax);
    Eager0::IntMaxInt.implements(&mut b, IntMaxInt);
    Eager2::IntMin.implements(&mut b, IntMin);
    Eager0::IntMinInt.implements(&mut b, IntMinInt);
    Eager2::IntMinus.implements(&mut b, IntMinus);
    Eager2::IntMod.implements(&mut b, IntMod);
    Eager1::IntNegate.implements(&mut b, IntNegate);
    Eager2::IntDiv.implements(&mut b, IntOpDiv);
    Eager2::IntOpEq.implements(&mut b, IntOpEq);
    Eager2::IntOpGe.implements(&mut b, IntOpGe);
    Eager2::IntOpGt.implements(&mut b, IntOpGt);
    Eager2::IntOpLe.implements(&mut b, IntOpLe);
    Eager2::IntOpLt.implements(&mut b, IntOpLt);
    Eager2::IntMod.implements(&mut b, IntOpMod);
    Eager2::IntOpNe.implements(&mut b, IntOpNe);
    Eager2::IntPlus.implements(&mut b, IntPlus);
    Eager0::IntPrecision.implements(&mut b, IntPrecision);
    Eager2::IntQuot.implements(&mut b, IntQuot);
    Eager2::IntRem.implements(&mut b, IntRem);
    Eager2::IntSameSign.implements(&mut b, IntSameSign);
    Eager1::IntSign.implements(&mut b, IntSign);
    Eager2::IntTimes.implements(&mut b, IntTimes);
    Eager1::IntToInt.implements(&mut b, IntToInt);
    Eager1::IntToLarge.implements(&mut b, IntToLarge);
    Eager1::IntToString.implements(&mut b, IntToString);
    Eager0::ListNil.implements(&mut b, ListNil);
    Eager2::ListOpAt.implements(&mut b, ListOpAt);
    Eager2::ListOpCons.implements(&mut b, ListOpCons);
    EagerF2::ListTabulate.implements(&mut b, ListTabulate);
    Eager0::OptionNone.implements(&mut b, OptionNone);
    Eager1::OptionSome.implements(&mut b, OptionSome);
    Eager0::OrderEqual.implements(&mut b, OrderEqual);
    Eager0::OrderGreater.implements(&mut b, OrderGreater);
    Eager0::OrderLess.implements(&mut b, OrderLess);
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
    Eager2::StringOpCaret.implements(&mut b, StringOpCaret);
    Eager2::StringOpEq.implements(&mut b, StringOpEq);
    Eager2::StringOpGe.implements(&mut b, StringOpGe);
    Eager2::StringOpGt.implements(&mut b, StringOpGt);
    Eager2::StringOpLe.implements(&mut b, StringOpLe);
    Eager2::StringOpLt.implements(&mut b, StringOpLt);
    Eager2::StringOpNe.implements(&mut b, StringOpNe);
    EagerF0::SysPlan.implements(&mut b, SysPlan);
    EagerF2::SysSet.implements(&mut b, SysSet);
    EagerF1::SysUnset.implements(&mut b, SysUnset);

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
            let global = f.is_global();

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
                let t = &fn_map.get(f).unwrap().0;
                if matches!(t.unqualified_quick(), Type::Fn(_, _)) {
                    vals.push(Val::Fn(*f));
                } else if let Some((_t, Impl::E0(eager0))) = fn_map.get(f) {
                    // Built-in is a constant such as Int.maxInt.
                    vals.push(eager0.apply());
                } else {
                    panic!("missing implementation for {:?}", f);
                }
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
