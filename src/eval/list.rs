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
use crate::eval::order::Order;
use crate::eval::val::Val;
use crate::shell::main::MorelError;
use std::cmp::Ordering;
use std::collections::HashSet;

/// Support for the `list` built-in type and the `List` structure.
pub struct List;

impl List {
    // lint: sort until '#}' where '##pub'

    /// Applies f to each element x of the list l, from left to right, until
    /// f(x) evaluates to false; it returns false if such an x exists and true
    /// otherwise.
    pub(crate) fn all(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<bool, MorelError> {
        for v in list {
            let result = func.apply_f1(r, f, v)?;
            if !result.expect_bool() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Applies f to the elements of l, from left to right.
    pub(crate) fn app(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<(), MorelError> {
        for v in list {
            func.apply_f1(r, f, v)?;
        }
        Ok(())
    }

    /// Computes the Morel expression `list1 @ list2`.
    pub(crate) fn append(list1: &[Val], list2: &[Val]) -> Vec<Val> {
        let mut list = list1.to_vec();
        list.extend_from_slice(list2);
        list
    }

    /// Performs lexicographic comparison of the two lists using the given
    /// ordering f on the list elements.
    pub(crate) fn collate(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list1: &[Val],
        list2: &[Val],
    ) -> Result<Order, MorelError> {
        for (v1, v2) in list1.iter().zip(list2.iter()) {
            let pair = Val::List(vec![v1.clone(), v2.clone()]);
            let result = func.apply_f1(r, f, &pair)?;
            let order = result.expect_order();
            if order.0 != Ordering::Equal {
                return Ok(order);
            }
        }
        // All elements compared equal, so compare lengths.
        Ok(Order(list1.len().cmp(&list2.len())))
    }

    /// Returns the list that is the concatenation of all the lists in l.
    pub(crate) fn concat(lists: &[Val]) -> Vec<Val> {
        let mut result = Vec::new();
        for val in lists {
            if let Val::List(list) = val {
                result.extend_from_slice(list);
            }
        }
        result
    }

    /// Computes the Morel expression `head :: tail`.
    pub(crate) fn cons(head: &Val, tail: &[Val]) -> Vec<Val> {
        let mut list = Vec::with_capacity(tail.len() + 1);
        list.push(head.clone());
        list.extend_from_slice(tail);
        list
    }

    /// Returns what is left after dropping the first i elements of the list.
    /// Raises Subscript if i < 0 or i > length l.
    pub(crate) fn drop(
        list: &[Val],
        i: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if i < 0 || i > list.len() as i32 {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            Ok(Val::List(list[i as usize..].to_vec()))
        }
    }

    /// Returns the elements that are in list1 but not in list2.
    pub(crate) fn except(lists: &[Val]) -> Vec<Val> {
        match lists.len() {
            0 => Vec::new(),
            1 => lists[0].expect_list().to_vec(),
            _ => {
                let hd_list = lists[0].expect_list();
                let mut tl_sets: Vec<HashSet<&Val>> = Vec::new();
                for list in &lists[1..] {
                    tl_sets.push(HashSet::from_iter(list.expect_list()));
                }
                hd_list
                    .iter()
                    .filter(|v| !tl_sets.iter().any(|set| set.contains(v)))
                    .cloned()
                    .collect()
            }
        }
    }

    /// Applies f to each element x of the list l, from left to right, until
    /// f(x) evaluates to true; it returns true if such an x exists and false
    /// otherwise.
    pub(crate) fn exists(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<bool, MorelError> {
        for v in list {
            let result = func.apply_f1(r, f, v)?;
            if result.expect_bool() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Applies f to each element x of l, from left to right, and returns the
    /// list of those x for which f x evaluated to true.
    pub(crate) fn filter(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        let mut result = Vec::new();
        for v in list {
            let keep = func.apply_f1(r, f, v)?;
            if keep.expect_bool() {
                result.push(v.clone());
            }
        }
        Ok(Val::List(result))
    }

    /// Applies f to each element x of the list l, from left to right, until
    /// f x evaluates to true. Returns SOME (x) if such an x exists;
    /// otherwise returns NONE.
    pub(crate) fn find(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        for v in list {
            let result = func.apply_f1(r, f, v)?;
            if result.expect_bool() {
                return Ok(Val::Some(Box::new(v.clone())));
            }
        }
        Ok(Val::Unit) // NONE
    }

    /// `foldl f init [x1, x2, ..., xn]` returns
    /// f`(xn, ... , f(x2, f(x1, init))...)` or `init` if the list is empty.
    pub(crate) fn foldl(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        init: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        let mut acc = init.clone();
        for v in list {
            let pair = Val::List(vec![v.clone(), acc]);
            acc = func.apply_f1(r, f, &pair)?;
        }
        Ok(acc)
    }

    /// foldr f init [x1, x2, ..., xn] returns
    /// f(x1, f(x2, ..., f(xn, init)...)) or init if the list is empty.
    pub(crate) fn foldr(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        init: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        let mut acc = init.clone();
        for v in list.iter().rev() {
            let pair = Val::List(vec![v.clone(), acc]);
            acc = func.apply_f1(r, f, &pair)?;
        }
        Ok(acc)
    }

    /// Returns NONE if the list is empty, and SOME (hd l, tl l) otherwise.
    pub(crate) fn get_item(list: &[Val]) -> Val {
        if list.is_empty() {
            Val::Unit // NONE
        } else {
            Val::Some(Box::new(Val::List(vec![
                list[0].clone(),
                Val::List(list[1..].to_vec()),
            ])))
        }
    }

    /// Returns the first element of the list.
    /// Raises Empty if the list is empty.
    pub(crate) fn hd(list: &[Val], span: &Span) -> Result<Val, MorelError> {
        if list.is_empty() {
            Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()))
        } else {
            Ok(list[0].clone())
        }
    }

    /// Returns the list of elements that are in all lists.
    pub(crate) fn intersect(lists: &[Val]) -> Vec<Val> {
        match lists.len() {
            0 => Vec::new(),
            1 => lists[0].expect_list().to_vec(),
            _ => {
                let hd_list = lists[0].expect_list();
                let mut tl_sets: Vec<HashSet<&Val>> = Vec::new();
                for list in &lists[1..] {
                    tl_sets.push(HashSet::from_iter(list.expect_list()));
                }
                hd_list
                    .iter()
                    .filter(|v| tl_sets.iter().all(|set| set.contains(v)))
                    .cloned()
                    .collect()
            }
        }
    }

    /// Returns the last element of the list.
    /// Raises Empty if the list is empty.
    pub(crate) fn last(list: &[Val], span: &Span) -> Result<Val, MorelError> {
        if list.is_empty() {
            Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()))
        } else {
            Ok(list[list.len() - 1].clone())
        }
    }

    /// Returns the number of elements in the list.
    pub(crate) fn length(list: &[Val]) -> i32 {
        list.len() as i32
    }

    pub(crate) fn map(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        let results: Result<Vec<Val>, _> =
            list.iter().map(|v| func.apply_f1(r, f, v)).collect();
        Ok(Val::List(results?))
    }

    /// Applies f to each element of l from left to right, returning a list
    /// of results, with SOME stripped, where f was defined.
    pub(crate) fn map_partial(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        let mut result = Vec::new();
        for v in list {
            let mapped = func.apply_f1(r, f, v)?;
            // If the result is SOME, unwrap it and add to result.
            if let Val::Some(boxed_val) = mapped {
                result.push(*boxed_val);
            }
            // If NONE (Val::Unit), skip it.
        }
        Ok(Val::List(result))
    }

    /// Applies the function f to the elements of the argument list,
    /// supplying the list index and element as arguments to each call.
    pub(crate) fn mapi(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        let mut result = Vec::with_capacity(list.len());
        for (i, v) in list.iter().enumerate() {
            let index_and_val = Val::List(vec![Val::Int(i as i32), v.clone()]);
            let mapped = func.apply_f1(r, f, &index_and_val)?;
            result.push(mapped);
        }
        Ok(Val::List(result))
    }

    /// Returns the i-th element of the list, counting from 0.
    /// Raises Subscript if i < 0 or i >= length l.
    pub(crate) fn nth(
        list: &[Val],
        i: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if i < 0 || i >= list.len() as i32 {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            Ok(list[i as usize].clone())
        }
    }

    /// Returns true if the list is empty.
    pub(crate) fn null(list: &[Val]) -> bool {
        list.is_empty()
    }

    /// Applies f to each element x of l, from left to right, and returns a
    /// pair (pos, neg) where pos is the list of those x for which f x
    /// evaluated to true, and neg is the list of those for which f x
    /// evaluated to false.
    pub(crate) fn partition(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Val,
        list: &[Val],
    ) -> Result<Val, MorelError> {
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for v in list {
            let result = func.apply_f1(r, f, v)?;
            if result.expect_bool() {
                pos.push(v.clone());
            } else {
                neg.push(v.clone());
            }
        }
        Ok(Val::List(vec![Val::List(pos), Val::List(neg)]))
    }

    /// Returns a list consisting of l's elements in reverse order.
    pub(crate) fn rev(list: &[Val]) -> Vec<Val> {
        let mut result = list.to_vec();
        result.reverse();
        result
    }

    /// Returns (rev l1) @ l2.
    pub(crate) fn rev_append(list1: &[Val], list2: &[Val]) -> Vec<Val> {
        let mut result = list1.to_vec();
        result.reverse();
        result.extend_from_slice(list2);
        result
    }

    pub(crate) fn tabulate(
        r: &mut EvalEnv,
        f: &mut Frame,
        count: i32,
        fun: &Val,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if count < 0 {
            return Err(MorelError::Runtime(BuiltInExn::Size, span.clone()));
        }
        let mut list = Vec::with_capacity(count as usize);
        for i in 0..count {
            let v = fun.apply_f1(r, f, &Val::Int(i))?;
            list.push(v);
        }
        Ok(Val::List(list))
    }

    /// Returns the first i elements of the list.
    /// Raises Subscript if i < 0 or i > length l.
    pub(crate) fn take(
        list: &[Val],
        i: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if i < 0 || i > list.len() as i32 {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            Ok(Val::List(list[..i as usize].to_vec()))
        }
    }

    /// Returns all but the first element of the list.
    /// Raises Empty if the list is empty.
    pub(crate) fn tl(list: &[Val], span: &Span) -> Result<Val, MorelError> {
        if list.is_empty() {
            Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()))
        } else {
            Ok(Val::List(list[1..].to_vec()))
        }
    }
}
