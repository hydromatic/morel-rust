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

use crate::compile::library::BuiltInExn;
use crate::eval::code::{EvalEnv, Frame, Span};
use crate::eval::val::Val;
use crate::shell::main::MorelError;

/// Support for the `option` built-in type and the `Option` structure.
pub struct Opt;

impl Opt {
    // lint: sort until '#}' where '##pub'

    /// Computes the Morel expression `Option.app f opt`.
    ///
    /// Applies the function `f` to the value `v` if `opt` is `SOME v`,
    /// and otherwise does nothing.
    pub(crate) fn app(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        opt: &Val,
    ) -> Result<Val, MorelError> {
        match opt {
            Val::Some(v) => {
                func.apply_f1(r, f, v)?;
                Ok(Val::Unit)
            }
            Val::Unit => Ok(Val::Unit),
            _ => panic!("Expected option, got {:?}", opt),
        }
    }

    /// Computes the Morel expression `Option.compose (f, g) a`.
    ///
    /// Returns `NONE` if `g(a)` is `NONE`; otherwise, if `g(a)` is `SOME v`,
    /// it returns `SOME (f v)`.
    pub(crate) fn compose(
        r: &mut EvalEnv,
        frame: &mut Frame,
        f: &Val,
        g: &Val,
        a: &Val,
    ) -> Result<Val, MorelError> {
        let g_result = g.apply_f1(r, frame, a)?;
        match g_result {
            Val::Some(v) => {
                let f_result = f.apply_f1(r, frame, &v)?;
                Ok(Val::Some(Box::new(f_result)))
            }
            Val::Unit => Ok(Val::Unit),
            _ => panic!("Expected option from g, got {:?}", g_result),
        }
    }

    /// Computes the Morel expression `Option.composePartial (f, g) a`.
    ///
    /// Returns `NONE` if `g(a)` is `NONE`; otherwise, if `g(a)` is `SOME v`,
    /// returns `f(v)`.
    pub(crate) fn compose_partial(
        r: &mut EvalEnv,
        frame: &mut Frame,
        f: &Val,
        g: &Val,
        a: &Val,
    ) -> Result<Val, MorelError> {
        let g_result = g.apply_f1(r, frame, a)?;
        match g_result {
            Val::Some(v) => f.apply_f1(r, frame, &v),
            Val::Unit => Ok(Val::Unit),
            _ => panic!("Expected option from g, got {:?}", g_result),
        }
    }

    /// Computes the Morel expression `Option.filter f a`.
    ///
    /// Returns `SOME a` if `f(a)` is `true`, `NONE` otherwise.
    pub(crate) fn filter(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        a: &Val,
    ) -> Result<Val, MorelError> {
        let result = func.apply_f1(r, f, a)?;
        if result.expect_bool() {
            Ok(Val::Some(Box::new(a.clone())))
        } else {
            Ok(Val::Unit)
        }
    }

    /// Computes the Morel expression `Option.getOpt (opt, a)`.
    ///
    /// Returns `v` if `opt` is `SOME (v)`; otherwise returns `a`.
    pub(crate) fn get_opt(opt: &Val, default: &Val) -> Val {
        match opt {
            Val::Some(v) => (**v).clone(),
            Val::Unit => default.clone(),
            _ => panic!("Expected option, got {:?}", opt),
        }
    }

    /// Computes the Morel expression `Option.isSome opt`.
    ///
    /// Returns `true` if `opt` is `SOME v`; otherwise returns `false`.
    pub(crate) fn is_some(opt: &Val) -> bool {
        matches!(opt, Val::Some(_))
    }

    /// Computes the Morel expression `Option.join opt`.
    ///
    /// Maps `NONE` to `NONE` and `SOME v` to `v`.
    pub(crate) fn join(opt: &Val) -> Val {
        match opt {
            Val::Some(v) => (**v).clone(),
            Val::Unit => Val::Unit,
            _ => panic!("Expected option, got {:?}", opt),
        }
    }

    /// Computes the Morel expression `Option.map f opt`.
    ///
    /// Maps `NONE` to `NONE` and `SOME v` to `SOME (f v)`.
    pub(crate) fn map(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        opt: &Val,
    ) -> Result<Val, MorelError> {
        match opt {
            Val::Some(v) => {
                let result = func.apply_f1(r, f, v)?;
                Ok(Val::Some(Box::new(result)))
            }
            Val::Unit => Ok(Val::Unit),
            _ => panic!("Expected option, got {:?}", opt),
        }
    }

    /// Computes the Morel expression `Option.mapPartial f opt`.
    ///
    /// Maps `NONE` to `NONE` and `SOME v` to `f(v)`.
    pub(crate) fn map_partial(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        opt: &Val,
    ) -> Result<Val, MorelError> {
        match opt {
            Val::Some(v) => func.apply_f1(r, f, v),
            Val::Unit => Ok(Val::Unit),
            _ => panic!("Expected option, got {:?}", opt),
        }
    }

    /// Computes the Morel expression `Option.valOf opt`.
    /// May throw [BuiltInExn::Option].
    ///
    /// Returns `v` if `opt` is `SOME v`, otherwise raises `Option`.
    pub(crate) fn val_of(opt: &Val, span: &Span) -> Result<Val, MorelError> {
        match opt {
            Val::Some(v) => Ok((**v).clone()),
            Val::Unit => {
                Err(MorelError::Runtime(BuiltInExn::Option, span.clone()))
            }
            _ => panic!("Expected option, got {:?}", opt),
        }
    }
}
