(*
 * Licensed to Julian Hyde under one or more contributor license
 * agreements.  See the NOTICE file distributed with this work
 * for additional information regarding copyright ownership.
 * Julian Hyde licenses this file to you under the Apache
 * License, Version 2.0 (the "License"); you may not use this
 * file except in compliance with the License.  You may obtain a
 * copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.  See the License for the specific
 * language governing permissions and limitations under the
 * License.
 *
 * The RELATIONAL signature, a Morel extension.
 *)
signature RELATIONAL =
sig
  (* Values of the "descending" type sort in reverse order to the type that
     they wrap. Thus 'order DESC i' sorts elements in the opposite direction to
     'order i'. *)
  datatype descending = DESC of 'a

  (* "compare (x, y)" returns LESS, EQUAL, or GREATER according to
   * whether its first argument is less than, equal to, or greater
   * than the second.
   *
   * Comparisons are based on the structure of the type
   * &alpha;. Primitive types are compared using their natural order;
   * Option types compare with NONE last; Tuple types compare
   * lexicographically; Record types compare lexicographically, with
   * the fields compared in alphabetical order; List values compare
   * lexicographically; Bag values compare lexicographically, the
   * elements appearing in an order that is arbitrary but is
   * consistent for each particular value. *)
  val compare : 'a * 'a -> order

  (* "count list" returns the number of elements in list. Often used
   * with `group`, for example `from e in emps group e.deptno compute
   * countId = count`. *)
  val count : int list -> int

  (* "empty list" returns whether the list is empty, for example `from
   * d in depts where empty (from e where e.deptno = d.deptno)`. *)
  val empty : 'a list -> bool

  (* "max list" returns the greatest element of list. Often used with
   * `group`, for example `from e in emps group e.deptno compute maxId
   * = max over e.id`. *)
  val max : 'a list -> 'a

  (* "min list" returns the least element of list. Often used with
   * `group`, for example `from e in emps group e.deptno compute minId
   * = min over e.id`. *)
  val min : 'a list -> 'a

  (* "nonEmpty list" returns whether the list has at least one
   * element, for example `from d in depts where nonEmpty (from e
   * where e.deptno = d.deptno)`. *)
  val nonEmpty : 'a list -> bool

  (* "only list" returns the sole element of `list`, for example `from
   * e in emps yield only (from d where d.deptno = e.deptno)`. Raises
   * `Empty` if the list does not have exactly one element. *)
  val only : 'a list -> 'a

  (* "e elem collection" returns whether `e` is a member of
   * `collection`. *)
  val elem : 'a * 'a bag -> bool | 'a * 'a list -> bool

  (* "e notelem collection" returns whether `e` is not a member of
   * `collection`. *)
  val notelem : 'a * 'a bag -> bool | 'a * 'a list -> bool

  (* "sum list" returns the sum of the elements of `list`. Often used
   * with `group`, for example `from e in emps group e.deptno compute
   * sumId = sum over e.id`. *)
  val sum : int list -> int
end

(*) End relational.sig
