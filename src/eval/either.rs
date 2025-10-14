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

use crate::eval::code::{Code, EvalEnv, Frame};
use crate::eval::val::Val;
use crate::shell::main::MorelError;

/// Support for the `Either` structure.
pub struct Either;

impl Either {
    /// Returns true if the value is a left value (INL).
    pub(crate) fn is_left(val: &Val) -> bool {
        matches!(val, Val::Inl(_))
    }

    /// Returns true if the value is a right value (INR).
    pub(crate) fn is_right(val: &Val) -> bool {
        matches!(val, Val::Inr(_))
    }

    /// Returns SOME(x) if val is INL(x), otherwise NONE.
    pub(crate) fn as_left(val: &Val) -> Val {
        match val {
            Val::Inl(v) => Val::Some(v.clone()),
            Val::Inr(_) => Val::Unit,
            _ => panic!("Expected either value"),
        }
    }

    /// Returns SOME(x) if val is INR(x), otherwise NONE.
    pub(crate) fn as_right(val: &Val) -> Val {
        match val {
            Val::Inl(_) => Val::Unit,
            Val::Inr(v) => Val::Some(v.clone()),
            _ => panic!("Expected either value"),
        }
    }

    /// Maps (fl, fr) over an either value.
    /// If INL(v), returns INL(fl(v)). If INR(v), returns INR(fr(v)).
    pub(crate) fn map(
        r: &mut EvalEnv,
        f: &mut Frame,
        fl: &Val,
        fr: &Val,
        val: &Val,
    ) -> Result<Val, MorelError> {
        match val {
            Val::Inl(v) => {
                let result = fl.apply_f1(r, f, v)?;
                Ok(Val::Inl(Box::new(result)))
            }
            Val::Inr(v) => {
                let result = fr.apply_f1(r, f, v)?;
                Ok(Val::Inr(Box::new(result)))
            }
            _ => panic!("Expected either value"),
        }
    }

    /// Maps f over left values, acts as identity on right values.
    pub(crate) fn map_left(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        val: &Val,
    ) -> Result<Val, MorelError> {
        match val {
            Val::Inl(v) => {
                let result = func.eval_f1(r, f, v)?;
                Ok(Val::Inl(Box::new(result)))
            }
            Val::Inr(_) => Ok(val.clone()),
            _ => panic!("Expected either value"),
        }
    }

    /// Maps f over right values, acts as identity on left values.
    pub(crate) fn map_right(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        val: &Val,
    ) -> Result<Val, MorelError> {
        match val {
            Val::Inl(_) => Ok(val.clone()),
            Val::Inr(v) => {
                let result = func.eval_f1(r, f, v)?;
                Ok(Val::Inr(Box::new(result)))
            }
            _ => panic!("Expected either value"),
        }
    }

    /// Applies the pair of functions `(fl, fr)` to an `either` value.
    /// If `INL(v)`, applies `fl(v)`. If `INR(v)`, applies `fr(v)`.
    pub(crate) fn app(
        r: &mut EvalEnv,
        f: &mut Frame,
        fl: &Val,
        fr: &Val,
        val: &Val,
    ) -> Result<(), MorelError> {
        match val {
            Val::Inl(v) => {
                fl.apply_f1(r, f, v)?;
                Ok(())
            }
            Val::Inr(v) => {
                fr.apply_f1(r, f, v)?;
                Ok(())
            }
            _ => panic!("Expected either value"),
        }
    }

    /// Applies f to left values, ignores right values.
    pub(crate) fn app_left(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        val: &Val,
    ) -> Result<(), MorelError> {
        match val {
            Val::Inl(v) => {
                func.eval_f1(r, f, v)?;
                Ok(())
            }
            Val::Inr(_) => Ok(()),
            _ => panic!("Expected either value"),
        }
    }

    /// Applies f to right values, ignores left values.
    pub(crate) fn app_right(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        val: &Val,
    ) -> Result<(), MorelError> {
        match val {
            Val::Inl(_) => Ok(()),
            Val::Inr(v) => {
                func.eval_f1(r, f, v)?;
                Ok(())
            }
            _ => panic!("Expected either value"),
        }
    }

    /// Folds (fl, fr) over an either value with an accumulator.
    /// If INL(v), computes fl(v, init). If INR(v), computes fr(v, init).
    pub(crate) fn fold(
        r: &mut EvalEnv,
        f: &mut Frame,
        fl: &Val,
        fr: &Val,
        init: &Val,
        val: &Val,
    ) -> Result<Val, MorelError> {
        match val {
            Val::Inl(v) => {
                let pair = Val::List(vec![v.as_ref().clone(), init.clone()]);
                fl.apply_f1(r, f, &pair)
            }
            Val::Inr(v) => {
                let pair = Val::List(vec![v.as_ref().clone(), init.clone()]);
                fr.apply_f1(r, f, &pair)
            }
            _ => panic!("Expected either value"),
        }
    }

    /// Projects out the contents of an `Either` value where both types are the
    /// same. If INL(v) or INR(v), returns v.
    pub(crate) fn proj(val: &Val) -> Val {
        match val {
            Val::Inl(v) => v.as_ref().clone(),
            Val::Inr(v) => v.as_ref().clone(),
            _ => panic!("Expected either value"),
        }
    }

    /// Partitions a list of `Either` values into a list of left values and a
    /// list of right values.
    pub(crate) fn partition(list: &[Val]) -> Val {
        let mut lefts = Vec::new();
        let mut rights = Vec::new();
        for v in list {
            match v {
                Val::Inl(left) => lefts.push(left.as_ref().clone()),
                Val::Inr(right) => rights.push(right.as_ref().clone()),
                _ => panic!("Expected either value"),
            }
        }
        Val::List(vec![Val::List(lefts), Val::List(rights)])
    }
}
