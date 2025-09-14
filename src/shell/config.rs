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

use crate::shell::prop::{Configurable, Mode, Output, Prop, PropVal};

/// Configuration for the Morel shell.
///
/// See also: [crate::eval::session::Config].
pub struct Config {
    // lint: sort until '^ *}'
    pub banner: Option<bool>,
    pub echo: Option<bool>,
    pub idempotent: Option<bool>,
    pub line_width: Option<i32>,
    pub mode: Option<Mode>,
    pub output: Option<Output>,
    pub print_depth: Option<i32>,
    pub print_length: Option<i32>,
    pub string_depth: Option<i32>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            // lint: sort until '^ *}'
            banner: Some(Prop::Banner.default_value().as_bool()),
            echo: Some(Prop::Echo.default_value().as_bool()),
            idempotent: Some(Prop::Idempotent.default_value().as_bool()),
            line_width: Some(Prop::LineWidth.default_value().as_int()),
            mode: Some(Prop::Mode.default_value().as_mode()),
            output: Some(Prop::Output.default_value().as_output()),
            print_depth: Some(Prop::PrintDepth.default_value().as_int()),
            print_length: Some(Prop::PrintLength.default_value().as_int()),
            string_depth: Some(Prop::StringDepth.default_value().as_int()),
        }
    }
}

impl Configurable for Config {
    fn set(&mut self, prop: Prop, val: &PropVal) {
        match (prop, val) {
            // lint: sort until '#}' where '##\(Prop::'
            (Prop::Banner, PropVal::Bool(b)) => {
                self.banner = Some(*b);
            }
            (Prop::LineWidth, PropVal::Int(i)) => {
                self.line_width = Some(*i);
            }
            (Prop::Output, PropVal::Output(x)) => {
                self.output = Some(*x);
            }
            (Prop::PrintDepth, PropVal::Int(i)) => {
                self.print_depth = Some(*i);
            }
            (Prop::PrintLength, PropVal::Int(i)) => {
                self.print_length = Some(*i);
            }
            (Prop::StringDepth, PropVal::Int(i)) => {
                self.string_depth = Some(*i);
            }
            _ => todo!("set {}", prop.name()),
        }
    }

    fn get(&self, prop: Prop) -> PropVal {
        match prop {
            // lint: sort until '#}' where '##Prop::'
            Prop::Banner => {
                if let Some(b) = self.banner {
                    PropVal::Bool(b)
                } else {
                    prop.default_value()
                }
            }
            Prop::Echo => {
                if let Some(b) = self.echo {
                    PropVal::Bool(b)
                } else {
                    prop.default_value()
                }
            }
            Prop::LineWidth => {
                if let Some(i) = self.line_width {
                    PropVal::Int(i)
                } else {
                    prop.default_value()
                }
            }
            Prop::Output => {
                if let Some(x) = self.output {
                    PropVal::Output(x)
                } else {
                    prop.default_value()
                }
            }
            Prop::PrintDepth => {
                if let Some(i) = self.print_depth {
                    PropVal::Int(i)
                } else {
                    prop.default_value()
                }
            }
            Prop::PrintLength => {
                if let Some(i) = self.print_length {
                    PropVal::Int(i)
                } else {
                    prop.default_value()
                }
            }
            Prop::StringDepth => {
                if let Some(i) = self.string_depth {
                    PropVal::Int(i)
                } else {
                    prop.default_value()
                }
            }
            _ => todo!("set {}", prop.name()),
        }
    }
}
