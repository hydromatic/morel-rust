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

/// Support for the `Vector` structure.
///
/// Vectors are represented internally as lists (`Val::List`), but have
/// different semantics - they are immutable, indexed, and support constant-time
/// random access (conceptually).
pub struct Vector;

impl Vector {
    // lint: sort until '#}' where '##pub'

    /// Applies function `f` to each element of the vector.
    pub(crate) fn app(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        vec: &[Val],
    ) -> Result<(), MorelError> {
        for v in vec {
            func.apply_f1(r, f, v)?;
        }
        Ok(())
    }

    /// Applies function `f` to each element and its index.
    pub(crate) fn appi(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        vec: &[Val],
    ) -> Result<(), MorelError> {
        for (i, v) in vec.iter().enumerate() {
            let pair = Val::List(vec![Val::Int(i as i32), v.clone()]);
            func.apply_f1(r, f, &pair)?;
        }
        Ok(())
    }

    /// Converts a list of vectors to a single concatenated vector.
    pub(crate) fn concat(lists: &[Val]) -> Val {
        let mut result = Vec::new();
        for v in lists {
            match v {
                Val::List(inner) => result.extend(inner.clone()),
                _ => panic!("Expected list"),
            }
        }
        Val::List(result)
    }

    /// Finds an element and its index satisfying predicate `f`.
    pub(crate) fn findi(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        vec: &[Val],
    ) -> Result<Val, MorelError> {
        for (i, v) in vec.iter().enumerate() {
            let pair = Val::List(vec![Val::Int(i as i32), v.clone()]);
            if func.apply_f1(r, f, &pair)?.expect_bool() {
                return Ok(Val::Some(Box::new(pair)));
            }
        }
        Ok(Val::Unit)
    }

    /// Folds left over the vector with indices.
    pub(crate) fn foldli(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        init: &Val,
        vec: &[Val],
    ) -> Result<Val, MorelError> {
        let mut acc = init.clone();
        for (i, v) in vec.iter().enumerate() {
            let triple = Val::List(vec![Val::Int(i as i32), v.clone(), acc]);
            acc = func.apply_f1(r, f, &triple)?;
        }
        Ok(acc)
    }

    /// Folds right over the vector with indices.
    pub(crate) fn foldri(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        init: &Val,
        vec: &[Val],
    ) -> Result<Val, MorelError> {
        let mut acc = init.clone();
        for (i, v) in vec.iter().enumerate().rev() {
            let triple = Val::List(vec![Val::Int(i as i32), v.clone(), acc]);
            acc = func.apply_f1(r, f, &triple)?;
        }
        Ok(acc)
    }

    /// Returns the length of a vector.
    pub(crate) fn length(vec: &[Val]) -> i32 {
        vec.len() as i32
    }

    /// Maps function `f` over the vector with indices.
    pub(crate) fn mapi(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        vec: &[Val],
    ) -> Result<Val, MorelError> {
        let mut result = Vec::new();
        for (i, v) in vec.iter().enumerate() {
            let pair = Val::List(vec![Val::Int(i as i32), v.clone()]);
            result.push(func.apply_f1(r, f, &pair)?);
        }
        Ok(Val::List(result))
    }

    /// Maximum length of a vector.
    pub(crate) fn max_len() -> i32 {
        i32::MAX
    }

    /// Returns the element at index `i` in vector `vec`.
    /// Raises `Subscript` if `i` < 0 or `i` >= length.
    pub(crate) fn sub(
        vec: &[Val],
        i: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if i < 0 || i >= vec.len() as i32 {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            Ok(vec[i as usize].clone())
        }
    }

    /// Returns a new vector with element at index `i` set to `x`.
    pub(crate) fn update(
        vec: &[Val],
        i: i32,
        x: Val,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if i < 0 || i >= vec.len() as i32 {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            let mut new_vec = vec.to_vec();
            new_vec[i as usize] = x;
            Ok(Val::List(new_vec))
        }
    }
}
