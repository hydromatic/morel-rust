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

use std::fmt;
use std::ops::Deref;
use std::path::PathBuf;
use std::rc::Rc;
use std::str::FromStr;

/// A value whose components can be accessed via properties.
pub trait Configurable {
    fn set(&mut self, prop: Prop, val: &PropVal);
    fn get(&self, prop: Prop) -> PropVal;
}

/// Tagged value of a property.
pub enum PropVal {
    Bool(bool),
    Int(i32),
    Output(Output),
    Mode(Mode),
    String(Rc<String>),
    PathBuf(Rc<PathBuf>),
}

impl PropVal {
    pub fn as_bool(&self) -> bool {
        match &self {
            PropVal::Bool(b) => *b,
            _ => todo!("wrong type"),
        }
    }

    pub fn as_int(&self) -> i32 {
        match &self {
            PropVal::Int(i) => *i,
            _ => todo!("wrong type"),
        }
    }

    pub fn as_mode(&self) -> Mode {
        match &self {
            PropVal::Mode(s) => *s,
            _ => todo!("wrong type"),
        }
    }

    pub fn as_output(&self) -> Output {
        match &self {
            PropVal::Output(s) => *s,
            _ => todo!("wrong type"),
        }
    }

    pub fn as_path_buf(&self) -> PathBuf {
        match &self {
            PropVal::PathBuf(p) => (*p).deref().clone(),
            _ => todo!("wrong type"),
        }
    }

    pub fn as_string(&self) -> String {
        match &self {
            PropVal::String(s) => (*s).deref().clone(),
            _ => todo!("wrong type"),
        }
    }
}

macro_rules! define_props {
    ($(
        $variant:ident => {
            doc: $doc:literal,
            camel_name: $camel:literal,
            default: $default:expr,
            required: $required:expr,
        }
    ),* $(,)?) => {
        #[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
        pub enum Prop {
            $(
                #[doc = $doc]
                $variant,
            )*
        }

        impl Prop {
            /// Returns the camelCase name of the property
            pub fn camel_name(self) -> &'static str {
                match self {
                    $(Prop::$variant => $camel,)*
                }
            }

            /// Returns the UPPER_CASE name of the property
            pub fn name(self) -> &'static str {
                match self {
                    $(Prop::$variant => stringify!($variant),)*
                }
            }

            /// Returns whether this property is required
            pub fn is_required(self) -> bool {
                match self {
                    $(Prop::$variant => $required,)*
                }
            }

            /// Returns the default value of property
            pub fn default_value(self) -> PropVal {
                match self {
                    $(Prop::$variant => $default.unwrap(),)*
                }
            }

            /// Returns the documentation for this property
            pub fn documentation(self) -> &'static str {
                match self {
                    $(Prop::$variant => $doc,)*
                }
            }

            /// Looks up a property by name (case-insensitive)
            pub fn lookup(prop_name: &str) -> Option<Self> {
                let upper_name = prop_name.to_uppercase();
                let lower_name = prop_name.to_lowercase();

                $(
                    if upper_name == stringify!($variant)
                        || lower_name == $camel
                    {
                        return Some(Prop::$variant);
                    }
                )*

                None
            }

            /// Returns all properties in declaration order
            pub fn all() -> &'static [Self] {
                &[$(Prop::$variant,)*]
            }

            pub fn str_to_val(&self, str: &str) -> PropVal {
                match &self {
                    Prop::Directory | Prop::ScriptDirectory => {
                        PropVal::PathBuf(Rc::new(PathBuf::from(str)))
                    }
                    Prop::Output => {
                        PropVal::Output(Output::from_str(str).unwrap())
                    },
                    Prop::InlinePassCount => {
                        PropVal::Int(str.parse().unwrap())
                    },
                    _ => todo!("str_to_val: {}", self.camel_name())
                }
            }

            fn get_bool(&self, configurable: &impl Configurable) -> bool {
                match configurable.get(*self) {
                    PropVal::Bool(b) => b,
                    _ => todo!("wrong type")
                }
            }

            pub fn get_int(&self, configurable: &impl Configurable) -> i32 {
                match configurable.get(*self) {
                    PropVal::Int(i) => i,
                    _ => todo!("wrong type")
                }
            }

            pub fn get_output(
                &self,
                configurable: &impl Configurable,
            ) -> Output {
                match configurable.get(*self) {
                    PropVal::Output(x) => x,
                    _ => todo!("wrong type")
                }
            }

            pub fn set_bool(
                &self,
                configurable: &mut impl Configurable,
                b: bool,
            ) {
                configurable.set(*self, &PropVal::Bool(b));
            }

            pub fn set_int(
                &self,
                configurable: &mut impl Configurable,
                i: i32,
            ) {
                configurable.set(*self, &PropVal::Int(i));
            }

            pub fn set_output(
                &self,
                configurable: &mut impl Configurable,
                x: Output,
            ) {
                configurable.set(*self, &PropVal::Output(x));
            }
        }
    };
}

define_props! {
    // lint: sort until '#}' where '##[A-Za-z]+'
    Banner => {
        doc: "Boolean property 'banner' controls whether to print the banner \
              at the start of the shell. Default is true.",
        camel_name: "banner",
        default: Some(PropVal::Bool(true)),
        required: true,
    },

    Directory => {
        doc: "File property 'directory' is the path of the directory that the \
               `file` variable maps to in this connection. The default value \
               is the empty string; many tests use the 'src/test/resources' \
               directory; when launched via the `morel` shell script, the \
               default value is the shell's current directory.",
        camel_name: "directory",
        default: Some(PropVal::String(Rc::new(String::new()))),
        required: true,
    },

    Echo => {
        doc: "Boolean property 'echo' controls whether the shell \
                outputs each command.",
        camel_name: "echo",
        default: Some(PropVal::Bool(false)),
        required: true,
    },

    Hybrid => {
        doc: "Boolean property 'hybrid' controls whether to try to create a \
               hybrid execution plan that uses Apache Calcite relational \
               algebra wherever possible. Default is false.",
        camel_name: "hybrid",
        default: Some(PropVal::Bool(false)),
        required: true,
    },

    Idempotent => {
        doc: "Boolean property 'idempotent' controls whether the shell \
                generates itself on successful execution.",
        camel_name: "idempotent",
        default: Some(PropVal::Bool(false)),
        required: true,
    },

    InlinePassCount => {
        doc: "Maximum number of inlining passes.",
        camel_name: "inlinePassCount",
        default: Some(PropVal::Int(5)),
        required: true,
    },

    LineWidth => {
        doc: "Integer property 'lineWidth' controls printing. The length at \
               which lines are wrapped. It is based upon the 'linewidth' \
               property in the PRINTCONTROL signature of the Standard Basis \
               Library. Default is 79.",
        camel_name: "lineWidth",
        default: Some(PropVal::Int(79)),
        required: true,
    },

    MatchCoverageEnabled => {
        doc: "Boolean property 'matchCoverageEnabled' controls whether to \
               check the coverage of patterns. If true (the default), Morel \
               warns if patterns are redundant and gives errors if patterns \
               are not exhaustive. If false, Morel does not analyze pattern \
               coverage, and therefore will not give warnings or errors.",
        camel_name: "matchCoverageEnabled",
        default: Some(PropVal::Bool(true)),
        required: true,
    },

    Mode => {
        doc: "How much to validate each statement in a script.",
        camel_name: "mode",
        default: Some(PropVal::Mode(Mode::Evaluate)),
        required: true,
    },

    OptionalInt => {
        doc: "Integer property 'optionalInt' is for testing. Default is null.",
        camel_name: "optionalInt",
        default: None as Option<PropVal>,
        required: false,
    },

    Output => {
        doc: "String property 'output' controls how values are printed in \
               the shell. Default is 'classic'.",
        camel_name: "output",
        default: Some(PropVal::Output(Output::Classic)),
        required: true,
    },

    PrintDepth => {
        doc: "Integer property 'printDepth' controls printing. The depth of \
               nesting of recursive data structure at which ellipsis begins. \
               It is based upon the 'printDepth' property in the \
               PRINTCONTROL signature of the Standard Basis Library. \
               Default is 5.",
        camel_name: "printDepth",
        default: Some(PropVal::Int(5)),
        required: true,
    },

    PrintLength => {
        doc: "Integer property 'printLength' controls printing. The length \
               of lists at which ellipsis begins. It is based upon the \
               'printLength' property in the PRINTCONTROL signature of the \
               Standard Basis Library. Default is 12.",
        camel_name: "printLength",
        default: Some(PropVal::Int(12)),
        required: true,
    },

    Relationalize => {
        doc: "Boolean property 'relationalize' controls conversion to \
                relational algebra. Default is false.",
        camel_name: "relationalize",
        default: Some(PropVal::Bool(false)),
        required: true,
    },

    ScriptDirectory => {
        doc: "File property 'scriptDirectory' is the path of the directory \
               where the `use` command looks for scripts. When running a \
               script, it is generally set to the directory that contains \
               the script.",
        camel_name: "scriptDirectory",
        default: Some(PropVal::String(Rc::new(String::new()))),
        required: true,
    },

    StringDepth => {
        doc: "Integer property 'stringDepth' is the length of strings at \
               which ellipsis begins. It is based upon the 'stringDepth' \
               property in the PRINTCONTROL signature of the Standard Basis \
               Library. Default is 70.",
        camel_name: "stringDepth",
        default: Some(PropVal::Int(70)),
        required: true,
    },
}

/// Allowed values for the Output property.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Output {
    /// Classic output type, same as Standard ML. The default.
    Classic,
    /// Tabular output if the value is a list of records, otherwise classic.
    Tabular,
}

impl fmt::Display for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Output::Classic => write!(f, "CLASSIC"),
            Output::Tabular => write!(f, "TABULAR"),
        }
    }
}

impl FromStr for Output {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_uppercase().as_str() {
            "CLASSIC" => Ok(Output::Classic),
            "TABULAR" => Ok(Output::Tabular),
            _ => Err(format!("Invalid output type: {}", s)),
        }
    }
}

/// How thoroughly to execute a statement.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Mode {
    Parse,
    Validate,
    Evaluate,
}

impl FromStr for Mode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_uppercase().as_str() {
            "EVALUATE" => Ok(Mode::Evaluate),
            "PARSE" => Ok(Mode::Parse),
            "VALIDATE" => Ok(Mode::Validate),
            _ => Err(format!("Invalid mode type: {}", s)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::session::Config as SessionConfig;
    use crate::shell::config::Config;

    #[test]
    fn test_lookup() {
        assert_eq!(Prop::lookup("directory"), Some(Prop::Directory));
        assert_eq!(Prop::lookup("DIRECTORY"), Some(Prop::Directory));
        assert_eq!(Prop::lookup("invalid"), None);
    }

    #[test]
    fn test_documentation() {
        assert!(Prop::Directory.documentation().contains("directory"));
        assert!(Prop::Hybrid.documentation().contains("hybrid"));
    }

    #[test]
    fn test_default_values() {
        let shell_config = Config::default();
        assert_eq!(Prop::LineWidth.get_int(&shell_config), 79);

        let session_config = SessionConfig::default();
        assert!(!Prop::Hybrid.get_bool(&session_config));
        assert_eq!(Prop::Output.get_output(&session_config), Output::Classic);

        let mut session_config2 = SessionConfig::default();
        assert!(!Prop::Hybrid.get_bool(&session_config2));
        Prop::Hybrid.set_bool(&mut session_config2, true);
        assert!(Prop::Hybrid.get_bool(&session_config2));
        Prop::Hybrid.set_bool(&mut session_config2, false);
        assert!(!Prop::Hybrid.get_bool(&session_config2));

        let mut shell_config2 = Config::default();
        Prop::LineWidth.set_int(&mut shell_config2, 100);
        assert_eq!(Prop::LineWidth.get_int(&shell_config2), 100);
    }

    #[test]
    fn test_all_properties() {
        let all_props = Prop::all();
        assert_eq!(all_props.len(), 16);
        assert!(all_props.contains(&Prop::Directory));
        assert!(all_props.contains(&Prop::LineWidth));
    }
}
