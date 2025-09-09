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

use crate::compile::compiler::BuiltInFunction;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::main::{MorelError, Shell};
use crate::syntax::ast::Pat;
use std::collections::BTreeMap;
use std::rc::Rc;

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
#[derive(Clone)]
pub enum Code {
    Constant(Val),
    Link(Rc<Option<Code>>),
    Match(Vec<(Pat, Box<Code>)>, Rc<Code>),
    ApplyE2(Eager2),
    ApplyEV2(EagerV2, Box<Code>, Box<Code>),
}

impl Code {
    pub fn eval(&self, v: &mut EvalEnv) -> Result<Val, MorelError> {
        match &self {
            Code::Constant(c) => Ok(c.clone()),
            Code::Link(_) => {
                todo!()
            }
            Code::Match(_, _) => {
                todo!()
            }
            Code::ApplyE2(_) => {
                todo!()
            }
            Code::ApplyEV2(eager, code0, code1) => {
                let v0 = code0.eval(v)?;
                let v1 = code1.eval(v)?;
                eager.apply(v, v0, v1)
            }
        }
    }
}

/// Utilities for [Code].
pub struct Codes;

impl Codes {
    pub(crate) fn constant(v: Val) -> Box<Code> {
        Box::new(Code::Constant(v))
    }

    pub(crate) fn apply(f: BuiltInFunction, codes: &[Box<Code>]) -> Box<Code> {
        match built_in_to_applicable(f) {
            Some(impl_) => match impl_ {
                Impl::E2(e2) => Box::new(Code::ApplyE2(e2)),
                Impl::EV2(ev2) => {
                    // TODO: handle cases like 'let args = (1, 2) in f args
                    // end'; see Gather in Morel-Java
                    assert_eq!(codes.len(), 2);
                    Box::new(Code::ApplyEV2(
                        ev2,
                        codes[0].clone(),
                        codes[1].clone(),
                    ))
                }
            },
            _ => todo!("{:?}", f),
        }
    }
}

/// Evaluation environment for [Code].
///
/// Function parameters holding an evaluation environment are typically named
/// `v`.
pub enum EvalEnv<'a> {
    /// Trivial environment with no session. To be used for
    /// simple tasks such as compilation.
    Empty,

    /// Root environment with immutable references and effects collector.
    Root(&'a Session, &'a Shell, &'a mut Vec<Effect>, &'a TypeMap),

    /// Child environment.
    Child(&'a mut EvalEnv<'a>),
}

impl EvalEnv<'_> {
    /// Emits an effect to be applied later.
    pub fn emit_effect(&mut self, effect: Effect) {
        match self {
            EvalEnv::Empty => {
                // No effects can be emitted in the empty environment.
            }
            EvalEnv::Root(_session, _shell, effects, _type_map) => {
                effects.push(effect);
            }
            EvalEnv::Child(parent) => {
                // For child environments, we need to delegate to the parent.
                // This requires careful handling of the mutable borrow.
                parent.emit_effect(effect);
            }
        }
    }

    /// Returns the type map.
    pub fn type_map(&self) -> Option<&TypeMap> {
        match self {
            EvalEnv::Empty => None,
            EvalEnv::Root(_session, _shell, _effects, type_map) => {
                Some(type_map)
            }
            EvalEnv::Child(parent) => parent.type_map(),
        }
    }
}

/// Implementation of a function is an [Eager2] or ...
#[derive(Debug, Clone, Copy)]
pub enum Impl {
    E2(Eager2),
    EV2(EagerV2),
}

pub struct Applicable;

/// Function implementation that takes two arguments.
/// The arguments are eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy)]
pub enum Eager2 {
    IntPlus,
}

/// Function implementation that takes two arguments and an evaluation
/// environment.
/// The arguments are eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy)]
pub enum EagerV2 {
    SysSet,
}

impl EagerV2 {
    pub(crate) fn implements(
        &self,
        map: &mut BTreeMap<u8, Impl>,
        f: BuiltInFunction,
    ) {
        map.insert(f as u8, Impl::EV2(*self));
    }

    fn apply(
        &self,
        v: &mut EvalEnv,
        a0: Val,
        a1: Val,
    ) -> Result<Val, MorelError> {
        match &self {
            SysSet => {
                let prop = a0.as_string();
                let val = a1;
                v.emit_effect(Effect::SetShellProp(prop, val));
                Ok(Val::Unit)
            }
        }
    }
}

impl Eager2 {
    fn apply(&self, a0: Val, a1: Val) -> Val {
        match &self {
            Eager2::IntPlus => Val::Int(a0.as_int() + a1.as_int()),
        }
    }

    pub(crate) fn implements(
        &self,
        map: &mut BTreeMap<u8, Impl>,
        f: BuiltInFunction,
    ) {
        map.insert(f as u8, Impl::E2(*self));
    }
}

use crate::compile::type_env::Binding;
use crate::compile::type_resolver::TypeMap;
use crate::eval::code::EagerV2::SysSet;
use std::sync::LazyLock;

static BUILT_IN_VALUES: LazyLock<BTreeMap<u8, Impl>> = LazyLock::new(|| {
    use BuiltInFunction::*;

    let mut map = BTreeMap::new();
    // lint: sort until '^ *map' erase '^.*, '
    Eager2::IntPlus.implements(&mut map, IntPlus);
    EagerV2::SysSet.implements(&mut map, SysSet);
    map
});

pub fn built_in_to_applicable(b: BuiltInFunction) -> Option<Impl> {
    BUILT_IN_VALUES.get(&(b as u8)).copied()
}
