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

//! Color schemes for syntax highlighting in the shell.
//!
//! A [`ColorScheme`] maps each token [`Category`] (keyword, string, …) to a
//! style spec such as `"bold cyan"` or `"italic 245"`. Three schemes are
//! built in: `dark` and `light` (tuned for the respective terminal
//! backgrounds) and `none` (no styling). When the `colorScheme` property is
//! not set, the shell [deduces](deduce) a scheme from the terminal's
//! background color.

/// A token category that syntax highlighting can style. The names match the
/// record fields of `Sys.colorSchemes`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Category {
    Keyword,
    Symbol,
    Numeric,
    Constant,
    String,
    Comment,
    TypeVar,
    Identifier,
    Error,
}

/// A named color scheme: a style spec for each token category. An empty spec
/// (`""`) means the category is left in the terminal's default style.
pub struct ColorScheme {
    pub name: &'static str,
    keyword: &'static str,
    symbol: &'static str,
    numeric: &'static str,
    constant: &'static str,
    string: &'static str,
    comment: &'static str,
    type_var: &'static str,
    identifier: &'static str,
    error: &'static str,
}

impl ColorScheme {
    /// The style spec for `category` (an attribute/color string such as
    /// `"bold cyan"`), or `""` if the category is unstyled.
    pub fn spec(&self, category: Category) -> &'static str {
        match category {
            Category::Keyword => self.keyword,
            Category::Symbol => self.symbol,
            Category::Numeric => self.numeric,
            Category::Constant => self.constant,
            Category::String => self.string,
            Category::Comment => self.comment,
            Category::TypeVar => self.type_var,
            Category::Identifier => self.identifier,
            Category::Error => self.error,
        }
    }
}

/// The `none` scheme: nothing is styled.
pub const NONE: ColorScheme = ColorScheme {
    name: "none",
    keyword: "",
    symbol: "",
    numeric: "",
    constant: "",
    string: "",
    comment: "",
    type_var: "",
    identifier: "",
    error: "",
};

/// The `dark` scheme, tuned for a dark terminal background.
pub const DARK: ColorScheme = ColorScheme {
    name: "dark",
    keyword: "bold cyan",
    symbol: "cyan",
    numeric: "yellow",
    constant: "yellow",
    string: "green",
    comment: "italic 245",
    type_var: "magenta",
    identifier: "",
    error: "underline red",
};

/// The `light` scheme, tuned for a light terminal background.
pub const LIGHT: ColorScheme = ColorScheme {
    name: "light",
    keyword: "bold blue",
    symbol: "blue",
    numeric: "magenta",
    constant: "magenta",
    string: "green",
    comment: "italic bright-black",
    type_var: "magenta",
    identifier: "",
    error: "underline red",
};

/// The built-in schemes, in the order `Sys.colorSchemes` reports them.
pub fn builtins() -> [&'static ColorScheme; 3] {
    [&DARK, &LIGHT, &NONE]
}

/// Returns the built-in scheme with the given `name`, or `None`.
pub fn built_in(name: &str) -> Option<&'static ColorScheme> {
    match name {
        "none" => Some(&NONE),
        "dark" => Some(&DARK),
        "light" => Some(&LIGHT),
        _ => None,
    }
}

/// A background whose luma exceeds this is treated as "light".
const LIGHT_LUMA_THRESHOLD: f64 = 0.5;

/// Deduces a scheme from a terminal background color: `light` if the
/// background is bright, `dark` if it is dim, and `none` if the background is
/// unknown or unparsable.
pub fn deduce(background: Option<&str>) -> &'static ColorScheme {
    match rgb_to_luma(background) {
        None => &NONE,
        Some(luma) if luma > LIGHT_LUMA_THRESHOLD => &LIGHT,
        Some(_) => &DARK,
    }
}

/// Resolves the scheme in effect: the built-in named `name` if it is one,
/// otherwise the scheme [deduced](deduce) from `background`.
pub fn resolve(
    name: Option<&str>,
    background: Option<&str>,
) -> &'static ColorScheme {
    if let Some(name) = name
        && let Some(scheme) = built_in(name)
    {
        return scheme;
    }
    deduce(background)
}

/// Computes the luma (perceived brightness, 0.0–1.0) of a terminal background
/// color of the form `"rgb:RRRR/GGGG/BBBB"` (each channel 1–4 hex digits), as
/// reported by the OSC 11 query. Returns `None` if `rgb` is absent or not in
/// that form. Uses the Rec. 601 weights, matching Morel-Java.
pub fn rgb_to_luma(rgb: Option<&str>) -> Option<f64> {
    let rgb = rgb?;
    let rest = &rgb[rgb.find("rgb:")? + 4..];
    let channels: Vec<&str> = rest.split('/').collect();
    if channels.len() < 3 {
        return None;
    }
    let r = hex_channel(channels[0])?;
    let g = hex_channel(channels[1])?;
    let b = hex_channel(channels[2])?;
    Some(0.299 * r + 0.587 * g + 0.114 * b)
}

/// Parses a 1–4 digit hex color channel, normalized to 0.0–1.0.
fn hex_channel(s: &str) -> Option<f64> {
    let hex: String = s.chars().take_while(char::is_ascii_hexdigit).collect();
    if hex.is_empty() || hex.len() > 4 {
        return None;
    }
    let value = u64::from_str_radix(&hex, 16).ok()?;
    let max = (1u64 << (hex.len() * 4)) - 1;
    Some(value as f64 / max as f64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rgb_to_luma() {
        // Black -> 0, white -> 1 (the weights sum to ~1.0 in f64).
        assert_eq!(rgb_to_luma(Some("rgb:0000/0000/0000")), Some(0.0));
        assert!(
            (rgb_to_luma(Some("rgb:ffff/ffff/ffff")).unwrap() - 1.0).abs()
                < 1e-9
        );
        // Green weight dominates (0.587).
        let g = rgb_to_luma(Some("rgb:0000/ffff/0000")).unwrap();
        assert!((g - 0.587).abs() < 1e-9);
        // Shorter channels are normalized by their own width.
        assert!(
            (rgb_to_luma(Some("rgb:ff/ff/ff")).unwrap() - 1.0).abs() < 1e-9
        );
        // Absent or malformed -> None.
        assert_eq!(rgb_to_luma(None), None);
        assert_eq!(rgb_to_luma(Some("black")), None);
        assert_eq!(rgb_to_luma(Some("rgb:0/0")), None);
    }

    #[test]
    fn test_deduce_and_resolve() {
        assert_eq!(deduce(None).name, "none");
        assert_eq!(deduce(Some("rgb:0000/0000/0000")).name, "dark");
        assert_eq!(deduce(Some("rgb:ffff/ffff/ffff")).name, "light");

        // A named built-in wins over the background.
        assert_eq!(
            resolve(Some("dark"), Some("rgb:ffff/ffff/ffff")).name,
            "dark"
        );
        // An unknown name falls through to deduction.
        assert_eq!(resolve(Some("bogus"), None).name, "none");
        assert_eq!(resolve(None, Some("rgb:ffff/ffff/ffff")).name, "light");
    }

    #[test]
    fn test_builtins_specs() {
        assert_eq!(DARK.spec(Category::Keyword), "bold cyan");
        assert_eq!(LIGHT.spec(Category::Keyword), "bold blue");
        assert_eq!(NONE.spec(Category::Keyword), "");
        assert_eq!(DARK.spec(Category::Identifier), "");
    }
}
