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

use std::fmt::{Display, Formatter, Result as FmtResult};
use std::sync::Arc;

/// Code location.
#[derive(Clone, PartialEq, Debug)]
pub struct Span(Arc<str>);

impl Span {
    pub fn new(s: &str) -> Self {
        Span(Arc::from(s))
    }

    pub fn from_pest_span(span: &pest::Span, base_line: usize) -> Self {
        let start_pos = span.start_pos();
        let end_pos = span.end_pos();
        let start = start_pos.line_col();
        let end = end_pos.line_col();
        let start_line = start.0.saturating_sub(base_line);
        let end_line = end.0.saturating_sub(base_line);
        if start_line == end_line && end.1 == start.1 + 1 {
            // Single-character span: just print the start position.
            Self::new(&format!("stdIn:{}.{}", start_line, start.1))
        } else {
            Self::new(&format!(
                "stdIn:{}.{}-{}.{}",
                start_line, start.1, end_line, end.1
            ))
        }
    }

    pub fn from_line_col(lc: &pest::error::LineColLocation) -> Self {
        use pest::error::LineColLocation;
        match lc {
            LineColLocation::Pos((line, col)) => {
                Self::new(&format!("stdIn:{}.{}", line, col))
            }
            LineColLocation::Span((l1, c1), (l2, c2)) => {
                Self::new(&format!("stdIn:{}.{}-{}.{}", l1, c1, l2, c2))
            }
        }
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.0)
    }
}
