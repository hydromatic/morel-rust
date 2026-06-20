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
 * The WORD signature, per the Standard ML Basis Library.
 *)
(**
 * The `Word` structure provides a type of unsigned integer with modular
 * arithmetic, logical (bit-wise) operations, and conversions.
 *
 * In Morel, `word` is a 64-bit unsigned integer (`wordSize` is 64),
 * `LargeWord.word` = `word`, and `LargeInt.int` = `int`.
 *)
signature WORD =
sig

  (** is the type of unsigned, fixed-precision integers (words). *)
  eqtype word

  (** is the number of bits in type `word`. In Morel, `wordSize` is 64. *)
  val wordSize : int [@@prototype "wordSize"]

  (** converts `w` to an equivalent value in `LargeWord.word`. *)
  val toLarge   : word -> word [@@prototype "toLarge w"]

  (** is like `toLarge`, but sign-extends `w`. *)
  val toLargeX  : word -> word [@@prototype "toLargeX w"]

  (** converts `w` to an equivalent value in `LargeWord.word`. *)
  val toLargeWord  : word -> word [@@prototype "toLargeWord w"]

  (** is like `toLargeWord`, but sign-extends `w`. *)
  val toLargeWordX : word -> word [@@prototype "toLargeWordX w"]

  (** converts `w` from `LargeWord.word`, discarding excess high bits. *)
  val fromLarge     : word -> word [@@prototype "fromLarge w"]

  (** converts `w` from `LargeWord.word`, discarding excess high bits. *)
  val fromLargeWord : word -> word [@@prototype "fromLargeWord w"]

  (** converts `w` to the equivalent unsigned `LargeInt.int`. *)
  val toLargeInt  : word -> int [@@prototype "toLargeInt w"]

  (** converts `w` to the equivalent signed `LargeInt.int`. *)
  val toLargeIntX : word -> int [@@prototype "toLargeIntX w"]

  (** converts `i` from `LargeInt.int` to a word, modulo 2 ^ wordSize. *)
  val fromLargeInt : int -> word [@@prototype "fromLargeInt i"]

  (** converts `w` to the equivalent unsigned `Int.int`. *)
  val toInt  : word -> int [@@prototype "toInt w"]

  (** converts `w` to the equivalent signed `Int.int`. *)
  val toIntX : word -> int [@@prototype "toIntX w"]

  (** converts `i` to a word, modulo 2 ^ wordSize. *)
  val fromInt : int -> word [@@prototype "fromInt i"]

  (** returns the bit-wise AND of `i` and `j`. *)
  val andb : word * word -> word [@@method] [@@prototype "andb (i, j)"]

  (** returns the bit-wise OR of `i` and `j`. *)
  val orb  : word * word -> word [@@method] [@@prototype "orb (i, j)"]

  (** returns the bit-wise exclusive OR of `i` and `j`. *)
  val xorb : word * word -> word [@@method] [@@prototype "xorb (i, j)"]

  (** returns the bit-wise complement (NOT) of `i`. *)
  val notb : word -> word [@@method] [@@prototype "notb i"]

  (** shifts `i` left by `n` bits, filling with zeros. *)
  val `<<`  : word * word -> word [@@prototype "i << n"] [@@syntax "infix"]

  (** shifts `i` right by `n` bits, filling with zeros (logical). *)
  val `>>`  : word * word -> word [@@prototype "i >> n"] [@@syntax "infix"]

  (** shifts `i` right by `n` bits, filling with the sign bit (arithmetic). *)
  val `~>>` : word * word -> word [@@prototype "i ~>> n"] [@@syntax "infix"]

  (** returns the sum of `i` and `j`, modulo 2 ^ wordSize. *)
  val `+` : word * word -> word [@@prototype "i + j"] [@@syntax "infix"]

  (** returns the difference of `i` and `j`, modulo 2 ^ wordSize. *)
  val `-` : word * word -> word [@@prototype "i - j"] [@@syntax "infix"]

  (** returns the product of `i` and `j`, modulo 2 ^ wordSize. *)
  val `*` : word * word -> word [@@prototype "i * j"] [@@syntax "infix"]

  (** returns the truncated quotient of `i` and `j` (unsigned). *)
  val div : word * word -> word [@@prototype "i div j"]

  (** returns the remainder of `i` divided by `j` (unsigned). *)
  val mod : word * word -> word [@@prototype "i mod j"]

  (** returns the unsigned ordering of `i` and `j`. *)
  val compare : word * word -> `order` [@@method] [@@prototype "compare (i, j)"]

  (** returns true if `i` is unsigned-less than `j`. *)
  val `<`  : word * word -> bool [@@prototype "i < j"] [@@syntax "infix"]

  (** returns true if `i` is unsigned-less-than-or-equal to `j`. *)
  val `<=` : word * word -> bool [@@prototype "i <= j"] [@@syntax "infix"]

  (** returns true if `i` is unsigned-greater than `j`. *)
  val `>`  : word * word -> bool [@@prototype "i > j"] [@@syntax "infix"]

  (** returns true if `i` is unsigned-greater-than-or-equal to `j`. *)
  val `>=` : word * word -> bool [@@prototype "i >= j"] [@@syntax "infix"]

  (** returns the negation of `i`, modulo 2 ^ wordSize. *)
  val `~` : word -> word [@@prototype "~ i"] [@@syntax "prefix"]

  (** returns the unsigned-smaller of `i` and `j`. *)
  val min : word * word -> word [@@method] [@@prototype "min (i, j)"]

  (** returns the unsigned-larger of `i` and `j`. *)
  val max : word * word -> word [@@method] [@@prototype "max (i, j)"]

  (** formats `i` in the given radix, without a `0wx` prefix. *)
  val fmt      : `radix` -> word -> string [@@prototype "fmt radix i"]

  (** converts `i` to a hexadecimal string, without a `0wx` prefix. *)
  val toString : word -> string [@@method] [@@prototype "toString i"]

  (** scans a word from a string, with an optional `0x` / `0wx` prefix. *)
  val fromString : string -> word option [@@prototype "fromString s"]
end
[@@description "Unsigned fixed-precision integers and bit-wise operations."]

(*) End word.sig
