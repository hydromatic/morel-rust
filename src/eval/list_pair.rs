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
use crate::eval::code::{Code, EvalEnv, Frame, Span};
use crate::eval::val::Val;
use crate::shell::main::MorelError;

/// Support for the `ListPair` structure.
pub struct ListPair;

impl ListPair {
    // lint: sort until '#}' where '##pub'

    /// Applies `f` to pairs from `l1` and `l2`, short-circuiting when `f`
    /// returns false. Returns false if such a pair exists, true otherwise.
    pub(crate) fn all(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        l1: &[Val],
        l2: &[Val],
    ) -> Result<bool, MorelError> {
        for (v1, v2) in l1.iter().zip(l2.iter()) {
            let pair = Val::List(vec![v1.clone(), v2.clone()]);
            let result = func.eval_f1(r, f, &pair)?;
            if !result.expect_bool() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns true if l1 and l2 have equal length and all pairs satisfy f.
    pub(crate) fn all_eq(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        l1: &[Val],
        l2: &[Val],
    ) -> Result<bool, MorelError> {
        // Return false if lengths don't match
        if l1.len() != l2.len() {
            return Ok(false);
        }
        Self::all(r, f, func, l1, l2)
    }

    /// Applies f to pairs from l1 and l2 in order.
    pub(crate) fn app(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        l1: &[Val],
        l2: &[Val],
    ) -> Result<(), MorelError> {
        for (v1, v2) in l1.iter().zip(l2.iter()) {
            let pair = Val::List(vec![v1.clone(), v2.clone()]);
            func.eval_f1(r, f, &pair)?;
        }
        Ok(())
    }

    /// Applies f to pairs from l1 and l2.
    /// Raises UnequalLengths if lists are unequal length.
    pub(crate) fn app_eq(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        l1: &[Val],
        l2: &[Val],
        span: &Span,
    ) -> Result<(), MorelError> {
        if l1.len() != l2.len() {
            return Err(MorelError::Runtime(
                BuiltInExn::UnequalLengths,
                span.clone(),
            ));
        }
        Self::app(r, f, func, l1, l2)
    }

    /// Applies f to pairs from l1 and l2, short-circuiting when f returns true.
    /// Returns true if such a pair exists, false otherwise.
    pub(crate) fn exists(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        l1: &[Val],
        l2: &[Val],
    ) -> Result<bool, MorelError> {
        for (v1, v2) in l1.iter().zip(l2.iter()) {
            let pair = Val::List(vec![v1.clone(), v2.clone()]);
            let result = func.eval_f1(r, f, &pair)?;
            if result.expect_bool() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Folds f over pairs from l1 and l2, left to right.
    /// f takes (a, b, acc) and returns new acc.
    pub(crate) fn foldl(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        init: &Val,
        l1: &[Val],
        l2: &[Val],
    ) -> Result<Val, MorelError> {
        let mut acc = init.clone();
        for (v1, v2) in l1.iter().zip(l2.iter()) {
            let triple = Val::List(vec![v1.clone(), v2.clone(), acc]);
            acc = func.eval_f1(r, f, &triple)?;
        }
        Ok(acc)
    }

    /// Folds f over pairs from l1 and l2, left to right.
    /// Raises UnequalLengths if lists are unequal length.
    pub(crate) fn foldl_eq(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        init: &Val,
        l1: &[Val],
        l2: &[Val],
        span: &Span,
    ) -> Result<Val, MorelError> {
        if l1.len() != l2.len() {
            return Err(MorelError::Runtime(
                BuiltInExn::UnequalLengths,
                span.clone(),
            ));
        }
        Self::foldl(r, f, func, init, l1, l2)
    }

    /// Folds f over pairs from l1 and l2, right to left.
    /// f takes (a, b, acc) and returns new acc.
    pub(crate) fn foldr(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        init: &Val,
        l1: &[Val],
        l2: &[Val],
    ) -> Result<Val, MorelError> {
        let mut acc = init.clone();
        let min_len = l1.len().min(l2.len());
        for i in (0..min_len).rev() {
            let triple = Val::List(vec![l1[i].clone(), l2[i].clone(), acc]);
            acc = func.eval_f1(r, f, &triple)?;
        }
        Ok(acc)
    }

    /// Folds f over pairs from l1 and l2, right to left.
    /// Raises UnequalLengths if lists are unequal length.
    pub(crate) fn foldr_eq(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        init: &Val,
        l1: &[Val],
        l2: &[Val],
        span: &Span,
    ) -> Result<Val, MorelError> {
        if l1.len() != l2.len() {
            return Err(MorelError::Runtime(
                BuiltInExn::UnequalLengths,
                span.clone(),
            ));
        }
        Self::foldr(r, f, func, init, l1, l2)
    }

    /// Maps f over pairs from l1 and l2, returning list of results.
    pub(crate) fn map(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        l1: &[Val],
        l2: &[Val],
    ) -> Result<Val, MorelError> {
        let mut result = Vec::new();
        for (v1, v2) in l1.iter().zip(l2.iter()) {
            let pair = Val::List(vec![v1.clone(), v2.clone()]);
            result.push(func.eval_f1(r, f, &pair)?);
        }
        Ok(Val::List(result))
    }

    /// Maps f over pairs from l1 and l2, returning list of results.
    /// Raises UnequalLengths if lists are unequal length.
    pub(crate) fn map_eq(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        l1: &[Val],
        l2: &[Val],
        span: &Span,
    ) -> Result<Val, MorelError> {
        if l1.len() != l2.len() {
            return Err(MorelError::Runtime(
                BuiltInExn::UnequalLengths,
                span.clone(),
            ));
        }
        Self::map(r, f, func, l1, l2)
    }

    /// Splits a list of pairs into a pair of lists.
    pub(crate) fn unzip(pairs: &[Val]) -> Val {
        let mut list1 = Vec::new();
        let mut list2 = Vec::new();
        for pair in pairs {
            if let Val::List(pair_vals) = pair
                && pair_vals.len() >= 2
            {
                list1.push(pair_vals[0].clone());
                list2.push(pair_vals[1].clone());
            }
        }
        Val::List(vec![Val::List(list1), Val::List(list2)])
    }

    /// Combines two lists into a list of pairs.
    /// If lists are unequal length, ignores excess elements.
    pub(crate) fn zip(l1: &[Val], l2: &[Val]) -> Val {
        let result: Vec<Val> = l1
            .iter()
            .zip(l2.iter())
            .map(|(v1, v2)| Val::List(vec![v1.clone(), v2.clone()]))
            .collect();
        Val::List(result)
    }

    /// Combines two lists into a list of pairs.
    /// Raises UnequalLengths if lists are unequal length.
    pub(crate) fn zip_eq(
        l1: &[Val],
        l2: &[Val],
        span: &Span,
    ) -> Result<Val, MorelError> {
        if l1.len() != l2.len() {
            return Err(MorelError::Runtime(
                BuiltInExn::UnequalLengths,
                span.clone(),
            ));
        }
        Ok(Self::zip(l1, l2))
    }
}
