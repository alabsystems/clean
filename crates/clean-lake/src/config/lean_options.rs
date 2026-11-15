// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `where`-block values that change WHICH LANGUAGE a module is compiled
//! in: `leanOptions`, `moreLeanArgs`, `weakLeanArgs` (and `moreLinkArgs`,
//! which changes only the link) (gap G50).
//!
//! Lake hands a library's modules to `lean` with (Lake 4.8.0,
//! `Lake/Config/LeanLib.lean` `leanArgs`, `Lake/Config/Package.lean`
//! `moreLeanArgs`), in this order:
//!
//! 1. the package's `leanOptions`, each as `-D<name>=<value>`;
//! 2. the package's `moreLeanArgs`;
//! 3. the library's `leanOptions`, as `-D…`;
//! 4. the library's `moreLeanArgs`;
//!
//! preceded by the package's then the library's `weakLeanArgs`
//! (`Lake/Build/Module.lean`: `mod.weakLeanArgs ++ mod.leanArgs`).
//!
//! `trust_ir-semantics` sets `leanOptions := #[⟨`autoImplicit, false⟩]`; a
//! frontend that skips that elaborates a different language from the one the
//! package's build checks, and accepts declarations it refuses.
//!
//! What is read here, and nothing more: an array literal of anonymous
//! constructors `⟨`name, value⟩` or structure instances `{ name := `name,
//! value := value }`, with `true` / `false`, a natural-number literal or a
//! string literal as the value (Lean's `LeanOptionValue` coercions); string
//! arrays whose elements may contain commas; an `if <platform> then A else
//! B` whose condition is one of `System.Platform`'s constants, evaluated for
//! the host, as Lake evaluates the lakefile on the host; and `A ++ B` of any
//! of these, a continuation line that opens with `++` included. Anything
//! else (an identifier such as Mathlib's `mathlibLeanOptions`) is not read;
//! the field stays a skipped-construct diagnostic AND is recorded as
//! unreadable, so a build refuses the modules it would have governed instead
//! of compiling them under options it never saw. A field the block parser
//! never attributes to a target at all is caught by `option_scan`.

use serde::{Deserialize, Serialize};

/// One `leanOptions` entry: Lake's `LeanOption` (`name`, `LeanOptionValue`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanOption {
    /// The option name, dotted (`autoImplicit`, `pp.unicode.fun`).
    pub name: String,
    /// The value.
    pub value: LeanOptionValue,
}

/// Lean's `LeanOptionValue`: exactly the kinds `-D` can carry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum LeanOptionValue {
    /// `ofString`.
    String(String),
    /// `ofBool`.
    Bool(bool),
    /// `ofNat`.
    Nat(u64),
}

impl LeanOption {
    /// The `-D` argument Lake passes for this option, without the `-D`
    /// (`LeanOption.asCliArg`). A string value keeps its quotes, as Lake's
    /// `asCliFlagValue` renders it (`s!"\"{s}\""`).
    #[must_use]
    pub fn define_arg(&self) -> String {
        let value = match &self.value {
            LeanOptionValue::String(s) => format!("\"{s}\""),
            LeanOptionValue::Bool(b) => b.to_string(),
            LeanOptionValue::Nat(n) => n.to_string(),
        };
        format!("{}={value}", self.name)
    }
}

/// Join the field starting at `lines[start]` with the continuation lines that
/// belong to it, returning the joined text and the index of the first line
/// after it.
///
/// A field continues while a bracket (`[`, `(`, `{`, `⟨`) opened outside a
/// string literal is unclosed, while the text so far ends in `:=`, `then` or
/// `else`, or while the next line opens with `then` / `else` — but never into
/// a column-0 line that is not a closing bracket, which starts the next
/// top-level construct. A `--` comment ends the line's contribution.
#[must_use]
pub(crate) fn join_field_lines(lines: &[&str], start: usize) -> (String, usize) {
    let mut text = strip_line_comment(lines[start].trim()).to_string();
    let mut next = start + 1;
    while next < lines.len() {
        let follow = lines[next].trim();
        let open = bracket_depth(&text) > 0;
        let dangling = text.ends_with(":=")
            || text.ends_with(" then")
            || text.ends_with(" else")
            || ends_with_operator(&text);
        let continues = follow.starts_with("then ")
            || follow.starts_with("else ")
            || starts_with_operator(follow);
        // A column-0 line other than a closing bracket starts the next
        // top-level construct: an unclosed bracket never swallows it.
        let top_level = lines[next].starts_with(|c: char| !c.is_whitespace())
            && !follow.starts_with([']', ')', '}', '⟩']);
        if top_level || !(open || dangling || continues) {
            break;
        }
        let piece = strip_line_comment(follow);
        if !piece.is_empty() {
            text.push(' ');
            text.push_str(piece);
        }
        next += 1;
    }
    (text, next)
}

/// Binary operators a value may continue across a line break with. Lean's
/// whitespace rules let `#[a]` on one line and `++ #[b]` on the next be one
/// term; stopping at the bracket would read only half of it.
const CONTINUATION_OPERATORS: [&str; 4] = ["++", "|>", "<|", "<|>"];

fn starts_with_operator(line: &str) -> bool {
    CONTINUATION_OPERATORS.iter().any(|op| line.starts_with(op))
}

fn ends_with_operator(text: &str) -> bool {
    CONTINUATION_OPERATORS.iter().any(|op| text.ends_with(op))
}

/// [`join_field_lines`] for a field that starts mid-line, after a
/// declaration's `where` (`first`, the text from the field name on, written
/// on `lines[line]`).
#[must_use]
pub(crate) fn join_inline_field(lines: &[&str], line: usize, first: &str) -> (String, usize) {
    let mut tail: Vec<&str> = Vec::with_capacity(lines.len().saturating_sub(line));
    tail.push(first);
    tail.extend_from_slice(lines.get(line + 1..).unwrap_or_default());
    let (text, next) = join_field_lines(&tail, 0);
    (text, line + next)
}

/// `line` up to a `--` comment that starts outside a string literal.
fn strip_line_comment(line: &str) -> &str {
    let mut in_string = false;
    let mut escaped = false;
    let bytes = line.as_bytes();
    for (idx, &b) in bytes.iter().enumerate() {
        if in_string {
            match (escaped, b) {
                (true, _) => escaped = false,
                (false, b'\\') => escaped = true,
                (false, b'"') => in_string = false,
                _ => {}
            }
        } else if b == b'"' {
            in_string = true;
        } else if b == b'-' && bytes.get(idx + 1) == Some(&b'-') {
            return line[..idx].trim_end();
        }
    }
    line
}

/// Net bracket depth of `text` outside string literals.
fn bracket_depth(text: &str) -> i64 {
    let mut depth = 0_i64;
    let mut in_string = false;
    let mut escaped = false;
    for c in text.chars() {
        if in_string {
            match (escaped, c) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => in_string = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '[' | '(' | '{' | '⟨' => depth += 1,
            ']' | ')' | '}' | '⟩' => depth -= 1,
            _ => {}
        }
    }
    depth
}

/// Split `text` at the top-level occurrences of `sep` (outside brackets and
/// string literals).
fn split_top_level(text: &str, sep: char) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0_i64;
    let mut in_string = false;
    let mut escaped = false;
    let mut from = 0;
    for (idx, c) in text.char_indices() {
        if in_string {
            match (escaped, c) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => in_string = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '[' | '(' | '{' | '⟨' => depth += 1,
            ']' | ')' | '}' | '⟩' => depth -= 1,
            c if c == sep && depth == 0 => {
                parts.push(&text[from..idx]);
                from = idx + c.len_utf8();
            }
            _ => {}
        }
    }
    parts.push(&text[from..]);
    parts
}

/// The elements of an array literal `#[a, b, …]`, trimmed; `None` when `text`
/// is not one. `#[]` has no elements.
fn array_elements(text: &str) -> Option<Vec<&str>> {
    let inner = text.trim().strip_prefix("#[")?.strip_suffix(']')?;
    if bracket_depth(inner) != 0 {
        return None;
    }
    if inner.trim().is_empty() {
        return Some(Vec::new());
    }
    Some(
        split_top_level(inner, ',')
            .into_iter()
            .map(str::trim)
            .collect(),
    )
}

/// A Lean string literal's contents (`"a\"b"` → `a"b`); `None` otherwise.
fn string_literal(text: &str) -> Option<String> {
    let inner = text.trim().strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next()? {
                'n' => out.push('\n'),
                't' => out.push('\t'),
                c @ ('\\' | '"' | '\'') => out.push(c),
                _ => return None,
            },
            '"' => return None,
            c => out.push(c),
        }
    }
    Some(out)
}

/// An array-valued expression: an array literal, a parenthesized one, an
/// `if <platform> then A else B` (resolved for the host), or `A ++ B` of
/// these, each element read by `element`. `None` when any part is none of
/// those, so the caller refuses rather than reads half of it.
fn eval_array_expr<T>(text: &str, element: &dyn Fn(&str) -> Option<T>) -> Option<Vec<T>> {
    let text = text.trim();
    if text.starts_with("if ") {
        return eval_array_expr(eval_platform_conditional(text)?, element);
    }
    let parts = split_top_level_str(text, "++");
    if parts.len() > 1 {
        let mut out = Vec::new();
        for part in parts {
            out.extend(eval_array_expr(part, element)?);
        }
        return Some(out);
    }
    if let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        if bracket_depth(inner) == 0 {
            return eval_array_expr(inner, element);
        }
    }
    array_elements(text)?.into_iter().map(element).collect()
}

/// Split `text` at top-level occurrences of `sep` (outside brackets and
/// string literals).
fn split_top_level_str<'a>(text: &'a str, sep: &str) -> Vec<&'a str> {
    let mut parts = Vec::new();
    let mut from = 0;
    let mut search = 0;
    while let Some(found) = text[search..].find(sep) {
        let idx = search + found;
        if bracket_depth(&text[from..idx]) == 0 && !inside_string(&text[from..idx]) {
            parts.push(&text[from..idx]);
            from = idx + sep.len();
        }
        search = idx + sep.len();
    }
    parts.push(&text[from..]);
    parts
}

/// Whether `prefix` ends inside an open string literal.
fn inside_string(prefix: &str) -> bool {
    let mut in_string = false;
    let mut escaped = false;
    for c in prefix.chars() {
        match (in_string, escaped, c) {
            (true, true, _) => escaped = false,
            (true, false, '\\') => escaped = true,
            (_, false, '"') => in_string = !in_string,
            _ => {}
        }
    }
    in_string
}

/// A string-array-valued expression (`#["-Wl,-no_data_const", "-lfoo"]`,
/// commas inside a string kept; see [`eval_array_expr`]); `None` when any
/// element is not a string literal.
pub(crate) fn parse_string_array_expr(text: &str) -> Option<Vec<String>> {
    eval_array_expr(text, &string_literal)
}

/// Resolve an `if <cond> then A else B` over `System.Platform` for the host,
/// returning the chosen branch's text; `text` itself when it is no `if`.
/// `None` for a condition this does not know.
#[must_use]
pub(crate) fn eval_platform_conditional(text: &str) -> Option<&str> {
    let text = text.trim();
    let Some(rest) = text.strip_prefix("if ") else {
        return Some(text);
    };
    let (cond, branches) = split_keyword(rest, " then ")?;
    let (then_branch, else_branch) = split_keyword(branches, " else ")?;
    let chosen = if platform_condition(cond.trim())? {
        then_branch
    } else {
        else_branch
    };
    eval_platform_conditional(chosen)
}

/// Split at the first top-level `keyword` (outside brackets and strings).
fn split_keyword<'a>(text: &'a str, keyword: &str) -> Option<(&'a str, &'a str)> {
    let mut search_from = 0;
    while let Some(found) = text[search_from..].find(keyword) {
        let idx = search_from + found;
        if bracket_depth(&text[..idx]) == 0 {
            return Some((&text[..idx], &text[idx + keyword.len()..]));
        }
        search_from = idx + keyword.len();
    }
    None
}

/// The host's value of a `System.Platform` constant (optionally negated with
/// `!` / `¬`), as the lakefile sees it when Lake elaborates it on this host.
fn platform_condition(cond: &str) -> Option<bool> {
    if let Some(inner) = cond.strip_prefix('!').or_else(|| cond.strip_prefix('¬')) {
        return platform_condition(inner.trim()).map(|v| !v);
    }
    let constant = cond
        .strip_prefix("System.Platform.")
        .or_else(|| cond.strip_prefix("Platform."))?;
    match constant {
        "isOSX" => Some(cfg!(target_os = "macos")),
        "isWindows" => Some(cfg!(windows)),
        "isEmscripten" => Some(cfg!(target_os = "emscripten")),
        _ => None,
    }
}

/// The option-carrying fields of one target, as the block parser fills them.
pub(crate) struct OptionSlots<'a> {
    pub(crate) lean_options: &'a mut Vec<LeanOption>,
    pub(crate) more_lean_args: &'a mut Vec<String>,
    pub(crate) weak_lean_args: &'a mut Vec<String>,
    /// `None` where the target has no `moreLinkArgs` (a library).
    pub(crate) more_link_args: Option<&'a mut Vec<String>>,
    pub(crate) unreadable: &'a mut Vec<String>,
}

/// Read `line` when it is a `leanOptions` / `moreLeanArgs` / `weakLeanArgs` /
/// `moreLinkArgs` field.
///
/// `None`: not one of these fields. `Some(true)`: read into its slot.
/// `Some(false)`: the field is there but its value is not a form this module
/// reads; the caller records the skipped-construct diagnostic, and a
/// `leanOptions` / `moreLeanArgs` / `weakLeanArgs` line is also pushed onto
/// `unreadable`, which a build refuses (`Workspace::module_lean_args`). An
/// unread `moreLinkArgs` changes no elaboration, so it is a diagnostic only.
pub(crate) fn parse_option_field(line: &str, slots: OptionSlots<'_>) -> Option<bool> {
    let field_value = |name: &str| field_value_of(line, name);
    let OptionSlots {
        lean_options,
        more_lean_args,
        weak_lean_args,
        more_link_args,
        unreadable,
    } = slots;
    if let Some(value) = field_value("leanOptions") {
        return Some(match parse_lean_options(value) {
            Some(options) => {
                *lean_options = options;
                true
            }
            None => {
                unreadable.push(line.to_string());
                false
            }
        });
    }
    let mut read_into = |parsed: Option<Vec<String>>, slot: &mut Vec<String>| match parsed {
        Some(args) => {
            *slot = args;
            true
        }
        None => {
            unreadable.push(line.to_string());
            false
        }
    };
    if let Some(value) = field_value("moreLeanArgs") {
        return Some(read_into(parse_string_array_expr(value), more_lean_args));
    }
    if let Some(value) = field_value("weakLeanArgs") {
        return Some(read_into(parse_string_array_expr(value), weak_lean_args));
    }
    let slot = more_link_args?;
    let value = field_value("moreLinkArgs")?;
    Some(match parse_string_array_expr(value) {
        Some(args) => {
            *slot = args;
            true
        }
        None => false,
    })
}

/// The text after `name :=` when `line` assigns field `name`.
fn field_value_of<'a>(line: &'a str, name: &str) -> Option<&'a str> {
    let rest = line.strip_prefix(name)?.trim_start();
    rest.strip_prefix(":=").map(str::trim)
}

/// A `leanOptions` array literal; `None` when any part of it is not one of
/// the forms the module docs list.
#[must_use]
pub(crate) fn parse_lean_options(text: &str) -> Option<Vec<LeanOption>> {
    eval_array_expr(text, &parse_lean_option)
}

/// `⟨`name, value⟩` or `{ name := `name, value := value }`.
fn parse_lean_option(text: &str) -> Option<LeanOption> {
    let text = text.trim();
    let (name, value) = if let Some(inner) = text.strip_prefix('⟨') {
        let parts = split_top_level(inner.strip_suffix('⟩')?, ',');
        let [name, value] = parts.as_slice() else {
            return None;
        };
        (*name, *value)
    } else {
        let inner = text.strip_prefix('{')?.strip_suffix('}')?;
        let mut name = None;
        let mut value = None;
        for field in split_top_level(inner, ',') {
            let (key, val) = field.split_once(":=")?;
            match key.trim() {
                "name" => name = Some(val),
                "value" => value = Some(val),
                _ => return None,
            }
        }
        (name?, value?)
    };
    Some(LeanOption {
        name: option_name(name)?,
        value: option_value(value)?,
    })
}

/// A name literal `` `a.b `` (a single backtick; Lake's `Lean.Name`).
fn option_name(text: &str) -> Option<String> {
    let name = text.trim().strip_prefix('`')?;
    let ok = !name.is_empty()
        && name
            .split('.')
            .all(|part| !part.is_empty() && part.chars().all(|c| c.is_alphanumeric() || c == '_'));
    ok.then(|| name.to_string())
}

/// A `LeanOptionValue` literal, through its `Coe` instances.
fn option_value(text: &str) -> Option<LeanOptionValue> {
    let text = text.trim();
    match text {
        "true" => Some(LeanOptionValue::Bool(true)),
        "false" => Some(LeanOptionValue::Bool(false)),
        _ if text.starts_with('"') => string_literal(text).map(LeanOptionValue::String),
        _ if !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()) => {
            text.parse().ok().map(LeanOptionValue::Nat)
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "lean_options_tests.rs"]
mod tests;
