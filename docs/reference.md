<!--
{% comment %}
Licensed to Julian Hyde under one or more contributor license
agreements.  See the NOTICE file distributed with this work
for additional information regarding copyright ownership.
Julian Hyde licenses this file to you under the Apache
License, Version 2.0 (the "License"); you may not use this
file except in compliance with the License.  You may obtain a
copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing,
software distributed under the License is distributed on an
"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied.  See the License for the specific
language governing permissions and limitations under the
License.
{% endcomment %}
-->

# Morel language reference

This document describes the grammar of Morel
([constants](#constants),
[identifiers](#identifiers),
[expressions](#expressions),
[patterns](#patterns),
[types](#types),
[declarations](#declarations)),
and then lists its built-in
[operators](#built-in-operators),
[types](#built-in-types),
[functions](#built-in-functions).
[Properties](#properties) affect the execution strategy and the
behavior of the shell.

As of release 0.1, Morel Rust (the Rust implementation of the Morel
language) has fewer features than Morel Java (the
[Java implementation](https://github.com/hydromatic/morel)).
For example, Morel Java version 0.7 supports query expressions
(`from`, `exists`, `forall`), and has a larger library of built-in
functions, including exceptions and `List` and `Bag` data types.
Hopefully, Morel Rust will support these features in the future.

See the
[Morel Java reference](https://github.com/hydromatic/morel/blob/main/docs/reference.md)
for details.

## Grammar

This reference is based on
[Andreas Rossberg's grammar for Standard ML](https://people.mpi-sws.org/~rossberg/sml.html).
While the files have a different [notation](#notation),
they are similar enough to the two languages.

### Differences between Morel and SML

Morel aims to be compatible with Standard ML.
It extends Standard ML in areas related to relational operations.
Some features in Standard ML are missing
just because they take effort to build.
Contributions are welcome!

In Morel-Rust but not Standard ML:
* <code><i>lab</i> =</code> is optional in <code><i>exprow</i></code>
* <code><i>record</i>.<i>lab</i></code> as an alternative to
  <code>#<i>lab</i> <i>record</i></code>
* identifiers and type names may be quoted
  (for example, <code>\`an identifier\`</code>)

In Standard ML but not in Morel:
* `word` constant
* `longid` identifier
* references (`ref` and operators `!` and `:=`)
* exceptions (`raise`, `handle`, `exception`)
* `while` loop
* data type replication (`type`)
* `withtype` in `datatype` declaration
* abstract type (`abstype`)
* modules (`structure` and `signature`)
* local declarations (`local`)
* operator declarations (`nonfix`, `infix`, `infixr`)
* `open`
* `before` and `o` operators

### Constants

<pre>
<i>con</i> <b>&rarr;</b> <i>int</i>                       integer
    | <i>float</i>                     floating point
    | <i>char</i>                      character
    | <i>string</i>                    string
<i>int</i> &rarr; [<b>~</b>]<i>num</i>                    decimal
    | [<b>~</b>]<b>0x</b><i>hex</i>                  hexadecimal
<i>float</i> &rarr; [<b>~</b>]<i>num</i><b>.</b><i>num</i>              floating point
    | [<b>~</b>]<i>num</i>[<b>.</b><i>num</i>]<b>e</b>[<b>~</b>]<i>num</i>
                                scientific
<i>char</i> &rarr; <b>#"</b><i>ascii</i><b>"</b>                 character
<i>string</i> &rarr; <b>"</b><i>ascii</i>*<b>"</b>               string
<i>num</i> &rarr; <i>digit</i> <i>digit</i>*              number
<i>hex</i> &rarr; (<i>digit</i> | <i>letter</i>) (<i>digit</i> | <i>letter</i>)*
                                hexadecimal number (letters
                                may only be in the range A-F)
<i>ascii</i> &rarr; ...                     single non-" ASCII character
                                or \-headed escape sequence
</pre>

### Identifiers

<pre>
<i>id</i> &rarr;  <i>letter</i> (<i>letter</i> | <i>digit</i> | ''' | <b>_</b>)*
                                alphanumeric
    | <i>symbol</i> <i>symbol</i>*            symbolic (not allowed for type
                                variables or module language
                                identifiers)
<i>symbol</i> &rarr; <b>!</b>
    | <b>%</b>
    | <b>&amp;</b>
    | <b>$</b>
    | <b>#</b>
    | <b>+</b>
    | <b>-</b>
    | <b>/</b>
    | <b>:</b>
    | <b>&lt;</b>
    | <b>=</b>
    | <b>&gt;</b>
    | <b>?</b>
    | <b>@</b>
    | <b>\</b>
    | <b>~</b>
    | <b>`</b>
    | <b>^</b>
    | '<b>|</b>'
    | '<b>*</b>'
<i>var</i> &rarr; '''(<i>letter</i> | <i>digit</i> | ''' | <b>_</b>)*
                                unconstrained
      ''''(<i>letter</i> | <i>digit</i> | ''' | <b>_</b>⟩*
                                equality
<i>lab</i> &rarr; <i>id</i>                        identifier
      <i>num</i>                       number (may not start with 0)
</pre>

### Expressions

<pre>
<i>exp</i> &rarr; <i>con</i>                       constant
    | [ <b>op</b> ] <i>id</i>                 value or constructor identifier
    | <i>exp<sub>1</sub></i> <i>exp<sub>2</sub></i>                 application
    | <i>exp<sub>1</sub></i> <i>id</i> <i>exp<sub>2</sub></i>              infix application
    | '<b>(</b>' <i>exp</i> '<b>)</b>'               parentheses
    | '<b>(</b>' <i>exp<sub>1</sub></i> <b>,</b> ... <b>,</b> <i>exp<sub>n</sub></i> '<b>)</b>' tuple (n &ne; 1)
    | <b>{</b> [ <i>exprow</i> ] <b>}</b>            record
    | <b>#</b><i>lab</i>                      record selector
    | '<b>[</b>' <i>exp<sub>1</sub></i> <b>,</b> ... <b>,</b> <i>exp<sub>n</sub></i> '<b>]</b>' list (n &ge; 0)
    | '<b>(</b>' <i>exp<sub>1</sub></i> <b>;</b> ... <b>;</b> <i>exp<sub>n</sub></i> '<b>)</b>' sequence (n &ge; 2)
    | <b>let</b> <i>dec</i> <b>in</b> <i>exp<sub>1</sub></i> ; ... ; <i>exp<sub>n</sub></i> <b>end</b>
                                local declaration (n ≥ 1)
    | <i>exp</i> <b>:</b> <i>type</i>                type annotation
    | <i>exp<sub>1</sub></i> <b>andalso</b> <i>exp<sub>2</sub></i>         conjunction
    | <i>exp<sub>1</sub></i> <b>orelse</b> <i>exp<sub>2</sub></i>          disjunction
    | <b>if</b> <i>exp<sub>1</sub></i> <b>then</b> <i>exp<sub>2</sub></i> <b>else</b> <i>exp<sub>3</sub></i>
                                conditional
    | <b>case</b> <i>exp</i> <b>of</b> <i>match</i>         case analysis
    | <b>fn</b> <i>match</i>                  function
<i>exprow</i> &rarr; [ <i>exp</i> <b>with</b> ] <i>exprowItem</i> [<b>,</b> <i>exprowItem</i> ]*
                                expression row
<i>exprowItem</i> &rarr; [ <i>lab</i> <b>=</b> ] <i>exp</i>
<i>match</i> &rarr; <i>matchItem</i> [ '<b>|</b>' <i>matchItem</i> ]*
                                match
<i>matchItem</i> &rarr; <i>pat</i> <b>=&gt;</b> <i>exp</i>
</pre>

### Patterns

<pre>
<i>pat</i> &rarr; <i>con</i>                       constant
    | <b>_</b>                         wildcard
    | [ <b>op</b> ] <i>id</i>                 variable
    | [ <b>op</b> ] <i>id</i> [ <i>pat</i> ]         construction
    | <i>pat<sub>1</sub></i> <i>id</i> <i>pat<sub>2</sub></i>              infix construction
    | '<b>(</b>' <i>pat</i> '<b>)</b>'               parentheses
    | '<b>(</b>' <i>pat<sub>1</sub></i> , ... , <i>pat<sub>n</sub></i> '<b>)</b>' tuple (n &ne; 1)
    | <b>{</b> [ <i>patrow</i> ] <b>}</b>            record
    | '<b>[</b>' <i>pat<sub>1</sub></i> <b>,</b> ... <b>,</b> <i>pat<sub>n</sub></i> '<b>]</b>' list (n &ge; 0)
    | <i>pat</i> <b>:</b> <i>type</i>                type annotation
    | <i>id</i> <b>as</b> <i>pat</i>                 layered
<i>patrow</i> &rarr; '<b>...</b>'                  wildcard
    | <i>lab</i> <b>=</b> <i>pat</i> [<b>,</b> <i>patrow</i>]      pattern
    | <i>id</i> [<b>,</b> <i>patrow</i>]             label as variable
</pre>

### Types

<pre>
<i>typ</i> &rarr; <i>var</i>                       variable
    | [ <i>typ</i> ] <i>id</i>                constructor
    | '<b>(</b>' <i>typ</i> [<b>,</b> <i>typ</i> ]* '<b>)</b>' <i>id</i>  constructor
    | '<b>(</b>' <i>typ</i> '<b>)</b>'               parentheses
    | <i>typ<sub>1</sub></i> <b>-&gt;</b> <i>typ<sub>2</sub></i>              function
    | <i>typ<sub>1</sub></i> '<b>*</b>' ... '<b>*</b>' <i>typ<sub>n</sub></i>     tuple (n &ge; 2)
    | <b>{</b> [ <i>typrow</i> ] <b>}</b>            record
    | <b>typeof</b> <i>exp</i>                expression type
<i>typrow</i> &rarr; <i>lab</i> : <i>typ</i> [, <i>typrow</i>]   type row
</pre>

### Declarations

<pre>
<i>dec</i> &rarr; <i>vals</i> <i>valbind</i>              value
    | <b>fun</b> <i>funbind</i>               function
    | <b>datatype</b> <i>datbind</i>          data type
    | <i>empty</i>
    | <i>dec<sub>1</sub></i> [<b>;</b>] <i>dec<sub>2</sub></i>              sequence
<i>valbind</i> &rarr; <i>pat</i> <b>=</b> <i>exp</i> [ <b>and</b> <i>valbind</i> ]*
                                destructuring
    | <b>rec</b> <i>valbind</i>               recursive
<i>funbind</i> &rarr; <i>funmatch</i> [ <b>and</b> <i>funmatch</i> ]*
                                clausal function
<i>funmatch</i> &rarr; <i>funmatchItem</i> [ '<b>|</b>' funmatchItem ]*
<i>funmatchItem</i> &rarr; [ <b>op</b> ] <i>id</i> <i>pat<sub>1</sub></i> ... <i>pat<sub>n</sub></i> [ <b>:</b> <i>type</i> ] <b>=</b> <i>exp</i>
                                nonfix (n &ge; 1)
    | <i>pat<sub>1</sub></i> <i>id</i> <i>pat<sub>2</sub></i> [ <b>:</b> <i>type</i> ] <b>=</b> <i>exp</i>
                                infix
    | '<b>(</b>' <i>pat<sub>1</sub></i> <i>id</i> <i>pat<sub>2</sub></i> '<b>)</b>' <i>pat'<sub>1</sub></i> ... <i>pat'<sub>n</sub></i> [ <b>:</b> <i>type</i> ] = <i>exp</i>
                                infix (n &ge; 0)
<i>datbind</i> &rarr; <i>datbindItem</i> [ <b>and</b> <i>datbindItem</i> ]*
                                data type
<i>datbindItem</i> &rarr; [ <i>vars</i> ] <i>id</i> <b>=</b> <i>conbind</i>
<i>conbind</i> &rarr; <i>conbindItem</i> [ '<b>|</b>' <i>conbindItem</i> ]*
                                data constructor
<i>conbindItem</i> &rarr; <i>id</i> [ <b>of</b> <i>typ</i> ]
<i>vals</i> &rarr; <i>val</i>
    | '<b>(</b>' <i>val</i> [<b>,</b> <i>val</i>]* '<b>)</b>'
<i>vars</i> &rarr; <i>var</i>
    | '<b>(</b>' <i>var</i> [<b>,</b> <i>var</i>]* '<b>)</b>'
</pre>

### Notation

This grammar uses the following notation:

| Syntax      | Meaning |
| ----------- | ------- |
| *symbol*    | Grammar symbol (e.g. *con*) |
| **keyword** | Morel keyword (e.g. **if**) and symbol (e.g. **~**, "**(**") |
| \[ term \]  | Option: term may occur 0 or 1 times |
| \[ term1 \| term2 \] | Alternative: term1 may occur, or term2 may occur, or neither |
| term*       | Repetition: term may occur 0 or more times |
| 's'         | Quotation: Symbols used in the grammar &mdash; ( ) \[ \] \| * ... &mdash; are quoted when they appear in Morel language |

## Built-in operators

| Operator | Precedence | Meaning |
| :------- | ---------: | :------ |
| *        |    infix 7 | Multiplication |
| /        |    infix 7 | Division |
| div      |    infix 7 | Integer division |
| mod      |    infix 7 | Modulo |
| +        |    infix 6 | Plus |
| -        |    infix 6 | Minus |
| ^        |    infix 6 | String concatenate |
| ~        |   prefix 6 | Negate |
| ::       |   infixr 5 | List cons |
| @        |   infixr 5 | List append |
| &lt;=    |    infix 4 | Less than or equal |
| &lt;     |    infix 4 | Less than |
| &gt;=    |    infix 4 | Greater than or equal |
| &gt;     |    infix 4 | Greater than |
| =        |    infix 4 | Equal |
| &lt;&gt; |    infix 4 | Not equal |
| elem     |    infix 4 | Member of list |
| notelem  |    infix 4 | Not member of list |
| :=       |    infix 3 | Assign |
| o        |    infix 3 | Compose |
| andalso  |    infix 2 | Logical and |
| orelse   |    infix 1 | Logical or |
| implies  |    infix 0 | Logical implication |

## Built-in types

Primitive: `bool`, `char`, `int`, `real`, `string`, `unit`

Datatype:
* `datatype 'a list = nil | :: of 'a * 'a list` (in structure `List`)
* `datatype 'a option = NONE | SOME of 'a` (in structure `Option`)
* `datatype 'a order = LESS | EQUAL | GREATER` (in structure `General`)

Exception:
* `Bind` (in structure `General`)
* `Chr` (in structure `General`)
* `Div` (in structure `General`)
* `Domain` (in structure `General`)
* `Option` (in structure `Option`)
* `Overflow` (in structure `Option`)
* `Subscript` (in structure `General`)
* `Unordered` (in structure `IEEEReal`)

## Built-in functions

{% comment %}START TABLE{% endcomment %}

| Name | Type | Description |
| ---- | ---- | ----------- |
| Bool.not | bool &rarr; bool | "not b" returns the logical negation of the boolean value `b`. |
| Bool.op implies | bool * bool &rarr; bool | "b1 implies b2" returns `true` if `b1` is `false` or `b2` is `true`. |
| Bool.toString | bool &rarr; string | "toString b" returns the string representation of `b`, either "true" or "false". |
| Char.chr | int &rarr; char | "chr i" returns the character whose code is `i`. Raises `Chr` if `i` &lt; 0 or `i` &gt; `maxOrd`. |
| Char.compare | char * char &rarr; order | "compare (c1, c2)" returns `LESS`, `EQUAL`, or `GREATER` according to whether its first argument is less than, equal to, or greater than the second. |
| Char.contains | char &rarr; string &rarr; bool | "contains s c" returns true if character `c` occurs in the string `s`; false otherwise. The function, when applied to `s`, builds a table and returns a function which uses table lookup to decide whether a given character is in the string or not. Hence it is relatively expensive to compute `val p = contains s` but very fast to compute `p(c)` for any given character. |
| Char.fromCString | string &rarr; char option | "fromCString s" scans a `char` value from a string. Returns `SOME (r)` if a `char` value can be scanned from a prefix of `s`, ignoring any initial whitespace; otherwise, it returns `NONE`. Equivalent to `StringCvt.scanString (scan StringCvt.ORD)`. |
| Char.fromInt | int &rarr; char option | "fromInt i" converts an `int` into a `char`. Raises `Chr` if `i` &lt; 0 or `i` &gt; `maxOrd`. |
| Char.fromString | string &rarr; char option | "fromString s" attempts to scan a character or ML escape sequence from the string `s`. Does not skip leading whitespace. For instance, `fromString "\\065"` equals `#"A"`. |
| Char.isAlpha | char &rarr; bool | "isAlpha c" returns true if `c` is a letter (lowercase or uppercase). |
| Char.isAlphaNum | char &rarr; bool | "isAlphaNum c" returns true if `c` is alphanumeric (a letter or a decimal digit). |
| Char.isAscii | char &rarr; bool | "isAscii c" returns true if 0 &le; `ord c` &le; 127 `c`. |
| Char.isCntrl | char &rarr; bool | "isCntrl c" returns true if `c` is a control character, that is, if `not (isPrint c)`. |
| Char.isDigit | char &rarr; bool | "isDigit c" returns true if `c` is a decimal digit (0 to 9). |
| Char.isGraph | char &rarr; bool | "isGraph c" returns true if `c` is a graphical character, that is, it is printable and not a whitespace character. |
| Char.isHexDigit | char &rarr; bool | "isHexDigit c" returns true if `c` is a hexadecimal digit. |
| Char.isLower | char &rarr; bool | "isLower c" returns true if `c` is a hexadecimal digit (0 to 9 or a to f or A to F). |
| Char.isOctDigit | char &rarr; bool | "isOctDigit c" returns true if `c` is an octal digit. |
| Char.isPrint | char &rarr; bool | "isPrint c" returns true if `c` is a printable character (space or visible). |
| Char.isPunct | char &rarr; bool | "isPunct c" returns true if `c` is a punctuation character, that is, graphical but not alphanumeric. |
| Char.isSpace | char &rarr; bool | "isSpace c" returns true if `c` is a whitespace character (blank, newline, tab, vertical tab, new page). |
| Char.isUpper | char &rarr; bool | "isUpper c" returns true if `c` is an uppercase letter (A to Z). |
| Char.maxOrd | int | "maxOrd" is the greatest character code; it equals `ord maxChar`. |
| Char.maxChar | int | "maxChar" is the greatest character in the ordering `&lt;`. |
| Char.minChar | char | "minChar" is the minimal (most negative) character representable by `char`. If a value is `NONE`, `char` can represent all negative integers, within the limits of the heap size. If `precision` is `SOME (n)`, then we have `minChar` = -2<sup>(n-1)</sup>. |
| Char.notContains | char &rarr; string &rarr; bool | "notContains s c" returns true if character `c` does not occur in the string `s`; false otherwise. Works by construction of a lookup table in the same way as `Char.contains`. |
| Char.ord | char &rarr; int | "ord c" returns the code of character `c`. |
| Char.pred | char &rarr; char | "pred c" returns the predecessor of `c`. Raises `Subscript` if `c` is `minOrd`. |
| Char.succ | char &rarr; char | "succ c" returns the character immediately following `c`, or raises `Chr` if `c` = `maxChar` |
| Char.toCString | char &rarr; string | "toCString c" converts a `char` into a `string`; equivalent to `(fmt StringCvt.ORD r)`. |
| Char.toLower | char &rarr; char | "toLower c" returns the lowercase letter corresponding to `c`, if `c` is a letter (a to z or A to Z); otherwise returns `c`. |
| Char.toString | char &rarr; string | "toString c" converts a `char` into a `string`; equivalent to `(fmt StringCvt.ORD r)`. |
| Char.toUpper | char &rarr; char | "toUpper c" returns the uppercase letter corresponding to `c`, if `c` is a letter (a to z or A to Z); otherwise returns `c`. |
| General.ignore | &alpha; &rarr; unit | "ignore x" always returns `unit`. The function evaluates its argument but throws away the value. |
| General.op o | (&beta; &rarr; &gamma;) (&alpha; &rarr; &beta;) &rarr; &alpha; &rarr; &gamma; | "f o g" is the function composition of `f` and `g`. Thus, `(f o g) a` is equivalent to `f (g a)`. |
| Int.op * | int * int &rarr; int | "i * j" is the product of `i` and `j`. It raises `Overflow` when the result is not representable. |
| Int.op + | int * int &rarr; int | "i + j" is the sum of `i` and `j`. It raises `Overflow` when the result is not representable. |
| Int.op - | int * int &rarr; int | "i - j" is the difference of `i` and `j`. It raises `Overflow` when the result is not representable. |
| Int.op div | int * int &rarr; int | "i div j" returns the greatest integer less than or equal to the quotient of i by j, i.e., `floor(i / j)`. It raises `Overflow` when the result is not representable, or Div when `j = 0`. Note that rounding is towards negative infinity, not zero. |
| Int.op mod | int * int &rarr; int | "i mod j" returns the remainder of the division of i by j. It raises `Div` when `j = 0`. When defined, `(i mod j)` has the same sign as `j`, and `(i div j) * j + (i mod j) = i`. |
| Int.op &lt; | int * int &rarr; bool | "i &lt; j" returns true if i is less than j. |
| Int.op &lt;= | int * int &rarr; bool | "i &lt; j" returns true if i is less than or equal to j. |
| Int.op &gt; | int * int &rarr; bool | "i &lt; j" returns true if i is greater than j. |
| Int.op &gt;= | int * int &rarr; bool | "i &lt; j" returns true if i is greater than or equal to j. |
| Int.op ~ | int &rarr; int | "~ i" returns the negation of `i`. |
| Int.abs | int &rarr; int | "abs i" returns the absolute value of `i`. |
| Int.compare | int * int &rarr; order | "compare (i, j)" returns `LESS`, `EQUAL`, or `GREATER` according to whether its first argument is less than, equal to, or greater than the second. |
| Int.fromInt, int | int &rarr; int | "fromInt i" converts a value from type `int` to the default integer type. Raises `Overflow` if the value does not fit. |
| Int.fromString | string &rarr; int option | "fromString s" scans a `int` value from a string. Returns `SOME (r)` if a `int` value can be scanned from a prefix of `s`, ignoring any initial whitespace; otherwise, it returns `NONE`. Equivalent to `StringCvt.scanString (scan StringCvt.DEC)`. |
| Int.max | int * int &rarr; int | "max (i, j)" returns the larger of the arguments. |
| Int.maxInt | int | "maxInt" is the maximal (most positive) integer representable by `int`. If a value is `NONE`, `int` can represent all positive integers, within the limits of the heap size. If `precision` is `SOME (n)`, then we have `maxInt` = 2<sup>(n-1)</sup> - 1. |
| Int.min | int * int &rarr; int | "min (i, j)" returns the smaller of the arguments. |
| Int.minInt | int | "minInt" is the minimal (most negative) integer representable by `int`. If a value is `NONE`, `int` can represent all negative integers, within the limits of the heap size. If `precision` is `SOME (n)`, then we have `minInt` = -2<sup>(n-1)</sup>. |
| Int.mod | int * int &rarr; int | "mod (i, j)" returns the remainder of the division of `i` by `j`. It raises `Div` when `j = 0`. When defined, `(i mod j)` has the same sign as `j`, and `(i div j) * j + (i mod j) = i`. |
| Int.precision | int | "precision" is the precision. If `SOME (n)`, this denotes the number `n` of significant bits in type `int`, including the sign bit. If it is `NONE`, int has arbitrary precision. The precision need not necessarily be a power of two. |
| Int.quot | int * int &rarr; int | "quot (i, j)" returns the truncated quotient of the division of `i` by `j`, i.e., it computes `(i / j)` and then drops any fractional part of the quotient. It raises `Overflow` when the result is not representable, or `Div` when `j = 0`. Note that unlike `div`, `quot` rounds towards zero. In addition, unlike `div` and `mod`, neither `quot` nor `rem` are infix by default; an appropriate infix declaration would be `infix 7 quot rem`. This is the semantics of most hardware divide instructions, so `quot` may be faster than `div`. |
| Int.rem | int * int &rarr; int | "rem (i, j)" returns the remainder of the division of `i` by `j`. It raises `Div` when `j = 0`. `(i rem j)` has the same sign as i, and it holds that `(i quot j) * j + (i rem j) = i`. This is the semantics of most hardware divide instructions, so `rem` may be faster than `mod`. |
| Int.sameSign | int * int &rarr; bool | "sameSign (i, j)" returns true if `i` and `j` have the same sign. It is equivalent to `(sign i = sign j)`. |
| Int.sign | int &rarr; int | "sign i" returns ~1, 0, or 1 when `i` is less than, equal to, or greater than 0, respectively. |
| Int.toInt | int &rarr; int | "toInt i" converts a value from the default integer type to type `int`. Raises `Overflow` if the value does not fit. |
| Int.toString | int &rarr; string | "toString i" converts a `int` into a `string`; equivalent to `(fmt StringCvt.DEC r)`. |
| List.map | (&alpha; &rarr; &beta;) &rarr; &alpha; list &rarr; &beta; list | "map f l" applies `f` to each element of `l` from left to right, returning the list of results. |
| List.tabulate | int * (int &rarr; &alpha;) &rarr; &alpha; list | "tabulate (n, f)" returns a list of length `n` equal to `[f(0), f(1), ..., f(n-1)]`, created from left to right. Raises `Size` if `n` &lt; 0. |
| Option.app | (&alpha; &rarr; unit) &rarr; &alpha; option &rarr; unit | "app f opt" applies the function `f` to the value `v` if `opt` is `SOME v`, and otherwise does nothing. |
| Option.compose | (&alpha; &rarr; &beta;) * (&gamma; &rarr; &alpha; option) &rarr; &gamma; &rarr; &beta; option | "compose (f, g) a" returns `NONE` if `g(a)` is `NONE`; otherwise, if `g(a)` is `SOME v`, it returns `SOME (f v)`. |
| Option.composePartial | (&alpha; &rarr; &beta; option) * (&gamma; &rarr; &alpha; option) &rarr; &gamma; &rarr; &beta; option | "composePartial (f, g) a" returns `NONE` if `g(a)` is `NONE`; otherwise, if `g(a)` is `SOME v`, returns `f(v)`. |
| Option.map | &alpha; &rarr; &beta;) &rarr; &alpha; option &rarr; &beta; option | "map f opt" maps `NONE` to `NONE` and `SOME v` to `SOME (f v)`. |
| Option.mapPartial | &alpha; &rarr; &beta; option) &rarr; &alpha; option &rarr; &beta; option | "mapPartial f opt" maps `NONE` to `NONE` and `SOME v` to `f(v)`. |
| Option.getOpt | &alpha; option * &alpha; &rarr; &alpha; | "getOpt (opt, a)" returns `v` if `opt` is `SOME (v)`; otherwise returns `a`. |
| Option.isSome | &alpha; option &rarr; bool | "isSome opt" returns `true` if `opt` is `SOME v`; otherwise returns `false`. |
| Option.filter | (&alpha; &rarr; bool) &rarr; &alpha; &rarr; &alpha; option | "filter f a" returns `SOME a` if `f(a)` is `true`, `NONE` otherwise. |
| Option.join | &alpha; option option &rarr; &alpha; option | "join opt" maps `NONE` to `NONE` and `SOME v` to `v`. |
| Option.valOf | &alpha; option &rarr; &alpha; | "valOf opt" returns `v` if `opt` is `SOME v`, otherwise raises `Option`. |
| Real.op * | real * real &rarr; real | "r1 * r2" is the product of `r1` and `r2`. The product of zero and an infinity produces NaN. Otherwise, if one argument is infinite, the result is infinite with the correct sign, e.g., -5 * (-infinity) = infinity, infinity * (-infinity) = -infinity. |
| Real.op + | real * real &rarr; real | "r1 + r2" is the sum of `r1` and `r2`. If one argument is finite and the other infinite, the result is infinite with the correct sign, e.g., 5 - (-infinity) = infinity. We also have infinity + infinity = infinity and (-infinity) + (-infinity) = (-infinity). Any other combination of two infinities produces NaN. |
| Real.op - | real * real &rarr; real | "r1 - r2" is the difference of `r1` and `r2`. If one argument is finite and the other infinite, the result is infinite with the correct sign, e.g., 5 - (-infinity) = infinity. We also have infinity + infinity = infinity and (-infinity) + (-infinity) = (-infinity). Any other combination of two infinities produces NaN. |
| Real.op / | real * real &rarr; real | "r1 / r2" is the quotient of `r1` and `r2`. We have 0 / 0 = NaN and +-infinity / +-infinity = NaN. Dividing a finite, non-zero number by a zero, or an infinity by a finite number produces an infinity with the correct sign. (Note that zeros are signed.) A finite number divided by an infinity is 0 with the correct sign. |
| Real.op &lt; | real * real &rarr; bool | "x &lt; y" returns true if x is less than y. Return false on unordered arguments, i.e., if either argument is NaN, so that the usual reversal of comparison under negation does not hold, e.g., `a &lt; b` is not the same as `not (a &gt;= b)`. |
| Real.op &lt;= | real * real &rarr; bool | As "&lt;" |
| Real.op &gt; | real * real &rarr; bool | As "&lt;" |
| Real.op &gt;= | real * real &rarr; bool | As "&lt;" |
| Real.op ~ | real &rarr; real | "~ r" returns the negation of `r`. |
| Real.abs | real &rarr; real | "abs r" returns the absolute value of `r`. |
| Real.ceil | real &rarr; int | "floor r" produces `ceil(r)`, the smallest int not less than `r`. |
| Real.checkFloat | real &rarr; real | "checkFloat x" raises `Overflow` if x is an infinity, and raises `Div` if x is NaN. Otherwise, it returns its argument. |
| Real.compare | real * real &rarr; order | "compare (x, y)" returns `LESS`, `EQUAL`, or `GREATER` according to whether its first argument is less than, equal to, or greater than the second. It raises `IEEEReal.Unordered` on unordered arguments. |
| Real.copySign | real * real &rarr; real | "copySign (x, y)" returns `x` with the sign of `y`, even if `y` is NaN. |
| Real.floor | real &rarr; int | "floor r" produces `floor(r)`, the largest int not larger than `r`. |
| Real.fromInt, real | int &rarr; real | "fromInt i" (also "real i") converts the integer `i` to a `real` value. If the absolute value of `i` is larger than `maxFinite`, then the appropriate infinity is returned. If `i` cannot be exactly represented as a `real` value, uses current rounding mode to determine the resulting value. |
| Real.fromManExp | {exp:int, man:real} &rarr; real | "fromManExp r" returns `{man, exp}`, where `man` and `exp` are the mantissa and exponent of r, respectively. |
| Real.fromString | string &rarr; real option | "fromString s" scans a `real` value from a string. Returns `SOME (r)` if a `real` value can be scanned from a prefix of `s`, ignoring any initial whitespace; otherwise, it returns `NONE`. This function is equivalent to `StringCvt.scanString scan`. |
| Real.isFinite | real &rarr; bool | "isFinite x" returns true if x is neither NaN nor an infinity. |
| Real.isNan | real &rarr; bool | "isNan x" returns true if x NaN. |
| Real.isNormal | real &rarr; bool | "isNormal x" returns true if x is normal, i.e., neither zero, subnormal, infinite nor NaN. |
| Real.max | real * real &rarr; real | "max (x, y)" returns the larger of the arguments. If exactly one argument is NaN, returns the other argument. If both arguments are NaN, returns NaN. |
| Real.maxFinite | real | "maxFinite" is the maximum finite number. |
| Real.min | real * real &rarr; real | "min (x, y)" returns the smaller of the arguments. If exactly one argument is NaN, returns the other argument. If both arguments are NaN, returns NaN. |
| Real.minNormalPos | real | "minNormalPos" is the minimum non-zero normalized number. |
| Real.minPos | real | "minPos" is the minimum non-zero positive number. |
| Real.negInf | real | "negInf" is the negative infinity value. |
| Real.posInf | real | "posInf" is the positive infinity value. |
| Real.precision | int | "precision" is the number of digits, each between 0 and `radix` - 1, in the mantissa. Note that the precision includes the implicit (or hidden) bit used in the IEEE representation (e.g., the value of Real64.precision is 53). |
| Real.radix | int | "radix" is the base of the representation, e.g., 2 or 10 for IEEE floating point. |
| Real.realCeil | real &rarr; real | "realCeil r" produces `ceil(r)`, the smallest integer not less than `r`. |
| Real.realFloor | real &rarr; real | "realFloor r" produces `floor(r)`, the largest integer not larger than `r`. |
| Real.realMod | real &rarr; real | "realMod r" returns the fractional parts of `r`; `realMod` is equivalent to `#frac o split`. |
| Real.realRound | real &rarr; real | "realRound r" rounds to the integer-valued real value that is nearest to `r`. In the case of a tie, it rounds to the nearest even integer. |
| Real.realTrunc | real &rarr; real | "realTrunc r" rounds `r` towards zero. |
| Real.rem | real * real &rarr; real | "rem (x, y)" returns the remainder `x - n * y`, where `n` = `trunc (x / y)`. The result has the same sign as `x` and has absolute value less than the absolute value of `y`. If `x` is an infinity or `y` is 0, `rem` returns NaN. If `y` is an infinity, rem returns `x`. |
| Real.round | real &rarr; int | "round r" yields the integer nearest to `r`. In the case of a tie, it rounds to the nearest even integer. |
| Real.sameSign | real * real &rarr; bool | "sameSign (r1, r2)" returns true if and only if `signBit r1` equals `signBit r2`. |
| Real.sign | real &rarr; int | "sign r" returns ~1 if r is negative, 0 if r is zero, or 1 if r is positive. An infinity returns its sign; a zero returns 0 regardless of its sign. It raises `Domain` on NaN. |
| Real.signBit | real &rarr; bool | "signBit r" returns true if and only if the sign of `r` (infinities, zeros, and NaN, included) is negative. |
| Real.split | real &rarr; {frac:real, whole:real} | "split r" returns `{frac, whole}`, where `frac` and `whole` are the fractional and integral parts of `r`, respectively. Specifically, `whole` is integral, and `abs frac` &lt; 1.0. |
| Real.trunc | real &rarr; int | "trunc r" rounds r towards zero. |
| Real.toManExp | real &rarr; {man:real, exp:int} | "toManExp r" returns `{man, exp}`, where `man` and `exp` are the mantissa and exponent of r, respectively. |
| Real.toString | real &rarr; string | "toString r" converts a `real` into a `string`; equivalent to `(fmt (StringCvt.GEN NONE) r)` |
| Real.unordered | real * real &rarr; bool | "unordered (x, y)" returns true if x and y are unordered, i.e., at least one of x and y is NaN. |
| String.collate | (char * char &rarr; order) &rarr; string * string &rarr; order | "collate (f, (s, t))" performs lexicographic comparison of the two strings using the given ordering `f` on characters. |
| String.compare | string * string &rarr; order | "compare (s, t)" does a lexicographic comparison of the two strings using the ordering `Char.compare` on the characters. It returns `LESS`, `EQUAL`, or `GREATER`, if `s` is less than, equal to, or greater than `t`, respectively. |
| String.fields | (char &rarr; bool) &rarr; string &rarr; string list | "fields f s" returns a list of fields derived from `s` from left to right. A field is a (possibly empty) maximal substring of `s` not containing any delimiter. A delimiter is a character satisfying the predicate `f`.  Two tokens may be separated by more than one delimiter, whereas two fields are separated by exactly one delimiter. For example, if the only delimiter is the character `#"\|"`, then the string `"\|abc\|\|def"` contains two tokens `"abc"` and `"def"`, whereas it contains the four fields `""`, `"abc"`, `""` and `"def"`. |
| String.op ^ | string * string &rarr; string | "s ^ t" is the concatenation of the strings `s` and `t`. This raises `Size` if `\|s\| + \|t\| &gt; maxSize`. |
| String.concat | string list &rarr; string | "concat l" is the concatenation of all the strings in `l`. This raises `Size` if the sum of all the sizes is greater than `maxSize`. |
| String.concatWith | string &rarr; string list &rarr; string | "concatWith s l" returns the concatenation of the strings in the list `l` using the string `s` as a separator. This raises `Size` if the size of the resulting string would be greater than `maxSize`. |
| String.explode | string &rarr; char list | "explode s" is the list of characters in the string `s`. |
| String.extract | string * int * int option &rarr; string | "extract (s, i, NONE)" and "extract (s, i, SOME j)" return substrings of `s`. The first returns the substring of `s` from the `i`(th) character to the end of the string, i.e., the string `s`[`i`..\|`s`\|-1]. This raises `Subscript` if `i` &lt; 0 or \|`s`\| &lt; `i`.<br><br>The second form returns the substring of size `j` starting at index `i`, i.e., the string `s`[`i`..`i`+`j`-1]. Raises `Subscript` if `i` &lt; 0 or `j` &lt; 0 or \|`s`\| &lt; `i` + `j`. Note that, if defined, `extract` returns the empty string when `i` = \|`s`\|. |
| String.implode | char list &rarr; string | "implode l" generates the string containing the characters in the list `l`. This is equivalent to `concat (List.map str l)`. This raises `Size` if the resulting string would have size greater than `maxSize`. |
| String.isPrefix | string &rarr; string &rarr; bool | "isPrefix s1 s2" returns `true` if the string `s1` is a prefix of the string `s2`. Note that the empty string is a prefix of any string, and that a string is a prefix of itself. |
| String.isSubstring | string &rarr; string &rarr; bool | "isSubstring s1 s2" returns `true` if the string `s1` is a substring of the string `s2`. Note that the empty string is a substring of any string, and that a string is a substring of itself. |
| String.isSuffix | string &rarr; string &rarr; bool | "isSuffix s1 s2" returns `true` if the string `s1` is a suffix of the string `s2`. Note that the empty string is a suffix of any string, and that a string is a suffix of itself. |
| String.map | (char &rarr; char) &rarr; string &rarr; string | "map f s" applies `f` to each element of `s` from left to right, returning the resulting string. It is equivalent to `implode(List.map f (explode s))`. |
| String.maxSize | int | "maxSize" is the longest allowed size of a string. |
| String.size | string &rarr; int | "size s" returns \|`s`\|, the number of characters in string `s`. |
| String.str | char &rarr; string | "str c" is the string of size one containing the character `c`. |
| String.sub | string * int &rarr; char | "sub (s, i)" returns the `i`(th) character of `s`, counting from zero. This raises `Subscript` if `i` &lt; 0 or \|`s`\| &le; `i`. |
| String.substring | string * int * int &rarr; string | "substring (s, i, j)" returns the substring `s`[`i`..`i`+`j`-1], i.e., the substring of size `j` starting at index `i`. This is equivalent to `extract(s, i, SOME j)`. |
| String.translate | (char &rarr; string) &rarr; string &rarr; string | "translate f s" returns the string generated from `s` by mapping each character in `s` by `f`. It is equivalent to `concat(List.map f (explode s))`. |
| String.tokens | (char &rarr; bool) &rarr; string &rarr; string list | "tokens f s" returns a list of tokens derived from `s` from left to right. A token is a non-empty maximal substring of `s` not containing any delimiter. A delimiter is a character satisfying the predicate `f`.  Two tokens may be separated by more than one delimiter, whereas two fields are separated by exactly one delimiter. For example, if the only delimiter is the character `#"\|"`, then the string `"\|abc\|\|def"` contains two tokens `"abc"` and `"def"`, whereas it contains the four fields `""`, `"abc"`, `""` and `"def"`. |
| Sys.plan | unit &rarr; string | "plan ()" prints the plan of the most recently executed expression. |
| Sys.set | string * &alpha; &rarr; unit | "set (property, value)" sets the value of `property` to `value`. (See [Properties](#properties) below.) |
| Sys.unset | string &rarr; unit | "unset property" clears the current the value of `property`. |

{% comment %}END TABLE{% endcomment %}

## Properties

Each property is set using the function `Sys.set (name, value)`,
displayed using `Sys.show name`,
and unset using `Sys.unset name`.
`Sys.showAll ()` shows all properties and their values.

| Name                 | Type | Default | Description |
| -------------------- | ---- | ------- | ----------- |
| hybrid               | bool | false   | Whether to try to create a hybrid execution plan that uses Apache Calcite relational algebra. |
| inlinePassCount      | int  | 5       | Maximum number of inlining passes. |
| lineWidth            | int  | 79      | When printing, the length at which lines are wrapped. |
| matchCoverageEnabled | bool | true    | Whether to check whether patterns are exhaustive and/or redundant. |
| output               | enum | classic | How values should be formatted. "classic" (the default) prints values in a compact nested format; "tabular" prints values in a table if their type is a list of records. |
| printDepth           | int  | 5       | When printing, the depth of nesting of recursive data structure at which ellipsis begins. |
| printLength          | int  | 12      | When printing, the length of lists at which ellipsis begins. |
| stringDepth          | int  | 70      | When printing, the length of strings at which ellipsis begins. |
