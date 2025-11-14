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
 * The SYS signature for system interaction and configuration.
 *)
signature SYS =
sig
  (* Restores the environment to the initial environment. *)
  val clearEnv : unit -> unit

  (* Returns the current environment as a list of variable names. *)
  val env : unit -> string list

  (* Returns the plan of the most recently executed expression. *)
  val plan : unit -> string

  (* Sets the value of a property.
   * Example: set ("hybrid", true) *)
  val set : string * 'a -> unit

  (* Returns the current value of a property as a string option.
   * Returns NONE if the property is unset.
   * Example: show "hybrid" *)
  val show : string -> string option

  (* Returns a list of all properties and their current values.
   * Each property is paired with SOME(value) if set, or NONE if unset.
   * Example: showAll () *)
  val showAll : unit -> (string * string option) list

  (* Clears the current value of a property, restoring it to default.
   * Example: unset "hybrid" *)
  val unset : string -> unit
end

(*) End sys.sig
