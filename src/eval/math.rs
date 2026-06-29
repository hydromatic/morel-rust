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

use std::f32::consts;

/// Support for the `Math` structure.
pub struct Math;

impl Math {
    // lint: sort until '#}' where '##pub'

    /// The constant e (base of natural logarithm).
    pub(crate) const E: f32 = consts::E;

    /// The constant pi.
    pub(crate) const PI: f32 = consts::PI;

    /// Computes the arc cosine of x.
    ///
    /// Like the other functions in this structure, computes in `f64` and
    /// narrows to `f32`, matching the JVM Morel reference, where `real` is
    /// a `float` but every `Math` function takes a `double`. The
    /// single-precision libm routines (`acosf`, `tanf`, ...) differ from
    /// the narrowed double result by up to 1 ULP (e.g. `acos 0.5`), which
    /// changes the printed value.
    pub(crate) fn acos(x: f32) -> f32 {
        (x as f64).acos() as f32
    }

    /// Computes the arc sine of x.
    pub(crate) fn asin(x: f32) -> f32 {
        (x as f64).asin() as f32
    }

    /// Computes the arc tangent of x.
    pub(crate) fn atan(x: f32) -> f32 {
        (x as f64).atan() as f32
    }

    /// Computes the arc tangent of y/x.
    pub(crate) fn atan2(y: f32, x: f32) -> f32 {
        (y as f64).atan2(x as f64) as f32
    }

    /// Computes the cosine of x (in radians).
    pub(crate) fn cos(x: f32) -> f32 {
        (x as f64).cos() as f32
    }

    /// Computes the hyperbolic cosine of x.
    pub(crate) fn cosh(x: f32) -> f32 {
        (x as f64).cosh() as f32
    }

    /// Computes e^x.
    pub(crate) fn exp(x: f32) -> f32 {
        (x as f64).exp() as f32
    }

    /// Computes the natural logarithm of x.
    pub(crate) fn ln(x: f32) -> f32 {
        (x as f64).ln() as f32
    }

    /// Computes the base-10 logarithm of x.
    pub(crate) fn log10(x: f32) -> f32 {
        (x as f64).log10() as f32
    }

    /// Computes x^y.
    pub(crate) fn pow(x: f32, y: f32) -> f32 {
        (x as f64).powf(y as f64) as f32
    }

    /// Computes the sine of x (in radians).
    pub(crate) fn sin(x: f32) -> f32 {
        (x as f64).sin() as f32
    }

    /// Computes the hyperbolic sine of x.
    pub(crate) fn sinh(x: f32) -> f32 {
        (x as f64).sinh() as f32
    }

    /// Computes the square root of x.
    pub(crate) fn sqrt(x: f32) -> f32 {
        (x as f64).sqrt() as f32
    }

    /// Computes the tangent of x (in radians).
    pub(crate) fn tan(x: f32) -> f32 {
        (x as f64).tan() as f32
    }

    /// Computes the hyperbolic tangent of x.
    pub(crate) fn tanh(x: f32) -> f32 {
        (x as f64).tanh() as f32
    }
}
