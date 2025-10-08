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

/// Support for the `Math` structure.
pub struct Math;

impl Math {
    // lint: sort until '#}' where '##pub'

    /// The constant e (base of natural logarithm).
    pub(crate) const E: f32 = std::f32::consts::E;

    /// The constant pi.
    pub(crate) const PI: f32 = std::f32::consts::PI;

    /// Computes the arc cosine of x.
    pub(crate) fn acos(x: f32) -> f32 {
        x.acos()
    }

    /// Computes the arc sine of x.
    pub(crate) fn asin(x: f32) -> f32 {
        x.asin()
    }

    /// Computes the arc tangent of x.
    pub(crate) fn atan(x: f32) -> f32 {
        x.atan()
    }

    /// Computes the arc tangent of y/x.
    pub(crate) fn atan2(y: f32, x: f32) -> f32 {
        y.atan2(x)
    }

    /// Computes the cosine of x (in radians).
    pub(crate) fn cos(x: f32) -> f32 {
        x.cos()
    }

    /// Computes the hyperbolic cosine of x.
    pub(crate) fn cosh(x: f32) -> f32 {
        x.cosh()
    }

    /// Computes e^x.
    pub(crate) fn exp(x: f32) -> f32 {
        x.exp()
    }

    /// Computes the natural logarithm of x.
    pub(crate) fn ln(x: f32) -> f32 {
        x.ln()
    }

    /// Computes the base-10 logarithm of x.
    pub(crate) fn log10(x: f32) -> f32 {
        x.log10()
    }

    /// Computes x^y.
    pub(crate) fn pow(x: f32, y: f32) -> f32 {
        x.powf(y)
    }

    /// Computes the sine of x (in radians).
    pub(crate) fn sin(x: f32) -> f32 {
        x.sin()
    }

    /// Computes the hyperbolic sine of x.
    pub(crate) fn sinh(x: f32) -> f32 {
        x.sinh()
    }

    /// Computes the square root of x.
    pub(crate) fn sqrt(x: f32) -> f32 {
        x.sqrt()
    }

    /// Computes the tangent of x (in radians).
    pub(crate) fn tan(x: f32) -> f32 {
        x.tan()
    }

    /// Computes the hyperbolic tangent of x.
    pub(crate) fn tanh(x: f32) -> f32 {
        x.tanh()
    }
}
