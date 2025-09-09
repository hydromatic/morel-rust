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

# Style Guide

## Comments
- All comments must end with a period.
- Use complete sentences.
- Avoid stating the obvious.

## Documentation Comments
- Use `///` for public APIs, `//` for internal code.
- Write in third-person declarative voice: "Returns the value" not
  "Return the value".
- Use present tense and active voice.

### Structure
```rust
/// Parses the input string into an abstract syntax tree.
///
/// Returns an error if the input contains invalid syntax.
fn parse(input: &str) -> Result<Ast, ParseError> {
    // Convert the raw token into a parsed expression.
    let expr = self.parse_token(token)?;
}
```

## Module Documentation
```rust
//! Parser for the Morel language.
//!
//! This module provides functionality for parsing Morel source code
//! into abstract syntax trees.
```

## Error Messages
- Use sentence case and end with a period.
- Be specific and suggest solutions when possible.

```rust
return Err("Failed to parse expression: unexpected token 'let' at line 42."
    .into());
```

## Commit Messages
- Use imperative mood: "Add parser support".
- Capitalize first letter, keep under 72 characters.

## Code structure
- Use 4 spaces for indentation.
- Consolidate `impl` blocks for the same type within the same file.
- Reduce uses of qualified names by adding imports;
  if duplicate names are used in the same file, consider adding aliases.
