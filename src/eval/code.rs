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

use crate::compile::core::Pat;
use crate::compile::library::{BuiltIn, BuiltInFunction, BuiltInRecord};
use crate::compile::type_env::Binding;
use crate::compile::type_parser;
use crate::compile::type_resolver::TypeMap;
use crate::compile::types::{Label, Type};
use crate::eval::code::EagerV2::SysSet;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::main::{MorelError, Shell};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::LazyLock;
use strum::{EnumProperty, IntoEnumIterator};

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
    // lint: sort until '^}$'
    Constant(Val),
    Link(Rc<Option<Code>>),
    Match(Vec<(Pat, Code)>, Rc<Code>),
    Native0(Eager0),
    Native1(Eager1, Box<Code>),
    Native2(Eager2, Box<Code>, Box<Code>),
    Native3(Eager3, Box<Code>, Box<Code>, Box<Code>),
    NativeF2(EagerV2, Box<Code>, Box<Code>),
    Tuple(Vec<Code>),
}

impl Code {
    pub(crate) fn new_constant(v: Val) -> Code {
        Code::Constant(v)
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

    pub fn eval(&self, v: &mut EvalEnv) -> Result<Val, MorelError> {
        match &self {
            // lint: sort until '#}' where '##Code::'
            Code::Constant(c) => Ok(c.clone()),
            Code::Link(_) => {
                todo!()
            }
            Code::Match(_, _) => {
                todo!()
            }
            Code::Native0(eager) => Ok(eager.apply()),
            Code::Native1(eager, code0) => {
                let v0 = code0.eval(v)?;
                Ok(eager.apply(v0))
            }
            Code::Native2(eager, code0, code1) => {
                let v0 = code0.eval(v)?;
                let v1 = code1.eval(v)?;
                Ok(eager.apply(v0, v1))
            }
            Code::Native3(eager, code0, code1, code2) => {
                let v0 = code0.eval(v)?;
                let v1 = code1.eval(v)?;
                let v2 = code2.eval(v)?;
                Ok(eager.apply(v0, v1, v2))
            }
            Code::NativeF2(eager, code0, code1) => {
                let v0 = code0.eval(v)?;
                let v1 = code1.eval(v)?;
                eager.apply(v, v0, v1)
            }
            Code::Tuple(codes) => {
                let mut values = Vec::with_capacity(codes.capacity());
                for code in codes {
                    values.push(code.eval(v)?);
                }
                Ok(Val::List(values))
            }
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

    /// Returns the root.
    pub fn root(&self) -> Option<(&Session, &Shell, &TypeMap)> {
        match self {
            EvalEnv::Empty => None,
            EvalEnv::Root(session, shell, _effects, type_map) => {
                Some((session, shell, type_map))
            }
            EvalEnv::Child(parent) => parent.root(),
        }
    }

    /// Returns the session.
    pub fn session(&self) -> Option<&Session> {
        if let Some((session, _shell, _type_map)) = self.root() {
            Some(session)
        } else {
            None
        }
    }

    /// Returns the shell.
    pub fn shell(&self) -> Option<&Shell> {
        if let Some((_, shell, _type_map)) = self.root() {
            Some(shell)
        } else {
            None
        }
    }

    /// Returns the type map.
    pub fn type_map(&self) -> Option<&TypeMap> {
        if let Some((_session, _shell, type_map)) = self.root() {
            Some(type_map)
        } else {
            None
        }
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
    #[allow(clippy::needless_pass_by_value)]
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
        b.fn_impls.insert(f, Impl::E0(*self));
    }
}

/// Function implementation that takes one argument.
/// The argument is eagerly evaluated before the function is called.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Eager1 {
    // lint: sort until '#}'
    OptionSome,
}

impl Eager1 {
    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(&self, a0: Val) -> Val {
        match &self {
            // lint: sort until '#}' where 'Eager1::'
            Eager1::OptionSome => {
                // TODO: Proper option some implementation
                // For now return the value
                a0
            }
        }
    }

    fn implements(&self, b: &mut LibBuilder, f: BuiltInFunction) {
        b.fn_impls.insert(f, Impl::E1(*self));
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
        b.fn_impls.insert(f, Impl::E2(*self));
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
        b.fn_impls.insert(f, Impl::EV2(*self));
    }

    // Passing Val by value is OK because it is small.
    #[allow(clippy::needless_pass_by_value)]
    fn apply(
        &self,
        v: &mut EvalEnv,
        a0: Val,
        a1: Val,
    ) -> Result<Val, MorelError> {
        match &self {
            // lint: sort until '#}' where '##[A-Z]'
            SysSet => {
                let prop = a0.expect_string();
                let val = a1;
                v.emit_effect(Effect::SetShellProp(prop, val));
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
        b.fn_impls.insert(f, Impl::E3(*self));
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
        b.fn_impls.insert(f, Impl::Custom);
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
    Custom::GOpPlus.implements(&mut b, GOpPlus);
    Custom::GOpTimes.implements(&mut b, GOpTimes);
    Eager2::IntDiv.implements(&mut b, IntDiv);
    Eager2::IntMinus.implements(&mut b, IntMinus);
    Eager2::IntMod.implements(&mut b, IntMod);
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
