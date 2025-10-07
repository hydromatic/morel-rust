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

/// Support for the `list` built-in type and the `List` structure.
pub struct List;

impl List {
    /// Computes the Morel expression `list1 @ list2`.
    pub(crate) fn append(list1: &[Val], list2: &[Val]) -> Vec<Val> {
        let mut list = list1.to_vec();
        list.extend_from_slice(list2);
        list
    }

    /// Computes the Morel expression `head :: tail`.
    pub(crate) fn cons(head: &Val, tail: &[Val]) -> Vec<Val> {
        let mut list = Vec::with_capacity(tail.len() + 1);
        list.push(head.clone());
        list.extend_from_slice(tail);
        list
    }

    pub(crate) fn tabulate(
        r: &mut EvalEnv,
        f: &mut Frame,
        count: i32,
        fun: &Code,
    ) -> Result<Val, MorelError> {
        /*
        if count < 0 {
            throw new MorelRuntimeException(BuiltInExn.SIZE, pos);
        }
         */
        let mut list = Vec::with_capacity(count as usize);
        for i in 0..count {
            let v = fun.eval_f1(r, f, &Val::Int(i))?;
            list.push(v);
        }
        Ok(Val::List(list))
    }
}
