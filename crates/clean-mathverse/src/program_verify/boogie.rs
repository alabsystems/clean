// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boogie verification condition parser for the Mathverse Library.
//!
//! Dafny compiles programs to Boogie intermediate verification language.
//! Boogie generates verification conditions (VCs) and dispatches them to
//! an SMT solver (typically Z3). This module parses Boogie's structured
//! VC export format and produces [`VerificationCondition`] values.

use thiserror::Error;

use super::types::{VcFormula, VcFormulaKind, VcStatus, VerificationCondition};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors raised during Boogie VC parsing.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum BoogieParseError {
    /// The input is empty or contains no parseable content.
    #[error("empty or blank input")]
    EmptyInput,

    /// No procedure declarations found in the input.
    #[error("no procedure declarations found")]
    NoProcedures,

    /// Malformed procedure declaration.
    #[error("malformed procedure at line {line}: {reason}")]
    MalformedProcedure { line: usize, reason: String },

    /// Unsupported Boogie type encountered.
    #[error("unsupported Boogie type: {typ}")]
    UnsupportedType { typ: String },
}

// ---------------------------------------------------------------------------
// Boogie type system
// ---------------------------------------------------------------------------

/// Boogie type representation (subset for VC parsing).
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum BoogieType {
    /// Integer type.
    Int,
    /// Boolean type.
    Bool,
    /// Bitvector type with width.
    Bv(u32),
    /// Map (array) type: `[K]V`.
    Map(Box<BoogieType>, Box<BoogieType>),
    /// Uninterpreted (user-defined) type.
    Named(String),
}

impl BoogieType {
    /// Parse a Boogie type from a string token.
    pub(crate) fn parse(s: &str) -> Result<Self, BoogieParseError> {
        let s = s.trim();
        match s {
            "int" => Ok(Self::Int),
            "bool" => Ok(Self::Bool),
            _ if s.starts_with("bv") => {
                let width_str = &s[2..];
                let width: u32 = width_str
                    .parse()
                    .map_err(|_| BoogieParseError::UnsupportedType { typ: s.to_string() })?;
                Ok(Self::Bv(width))
            }
            _ if s.starts_with('[') && s.contains(']') => {
                let bracket_end = s.find(']').expect("checked above");
                let key_str = &s[1..bracket_end];
                let val_str = &s[bracket_end + 1..];
                let key = Self::parse(key_str)?;
                let val = Self::parse(val_str)?;
                Ok(Self::Map(Box::new(key), Box::new(val)))
            }
            _ if !s.is_empty() && s.chars().next().is_some_and(|c| c.is_alphabetic()) => {
                Ok(Self::Named(s.to_string()))
            }
            _ => Err(BoogieParseError::UnsupportedType { typ: s.to_string() }),
        }
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Mutable state carried through Boogie VC parsing.
struct BoogieParseState {
    vcs: Vec<VerificationCondition>,
    current_proc: Option<String>,
    current_source_file: Option<String>,
    vc_index: u32,
}

/// Parse Boogie VCs from a text input and produce verification conditions.
///
/// Extracts procedure blocks with `requires`/`ensures`/`modifies` annotations
/// and internal `assert` statements.
///
/// # Errors
///
/// Returns `BoogieParseError` if the input is empty or contains no
/// recognizable procedure declarations.
pub fn parse_boogie_vcs(input: &str) -> Result<Vec<VerificationCondition>, BoogieParseError> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err(BoogieParseError::EmptyInput);
    }

    let mut state = BoogieParseState {
        vcs: Vec::new(),
        current_proc: None,
        current_source_file: None,
        vc_index: 0,
    };

    for (line_idx, line) in trimmed.lines().enumerate() {
        let line = line.trim();
        let line_num = line_idx + 1;
        parse_boogie_line(line, line_num, &mut state);
    }

    if state.vcs.is_empty() {
        return Err(BoogieParseError::NoProcedures);
    }

    Ok(state.vcs)
}

/// Process a single line of Boogie input.
fn parse_boogie_line(line: &str, line_num: usize, state: &mut BoogieParseState) {
    // Skip empty lines and comments (but check for source annotations).
    if line.is_empty() || line.starts_with("//") {
        if let Some(rest) = line.strip_prefix("// source_file:") {
            state.current_source_file = Some(rest.trim().to_string());
        }
        return;
    }

    // Detect procedure declaration.
    if line.starts_with("procedure") {
        state.current_proc = extract_procedure_name(line);
        state.vc_index = 0;
        return;
    }

    // Opening/closing braces.
    if line == "{" || line == "}" {
        if line == "}" {
            state.current_proc = None;
        }
        return;
    }

    let proc_name = state.current_proc.as_deref().unwrap_or("global");

    // Parse `requires`, `ensures`, and `assert` clauses.
    let clause_kind = if let Some(rest) = line.strip_prefix("requires") {
        Some(("requires", rest))
    } else if let Some(rest) = line.strip_prefix("ensures") {
        Some(("ensures", rest))
    } else {
        line.strip_prefix("assert").map(|rest| ("assert", rest))
    };

    if let Some((kind, rest)) = clause_kind {
        let expr_str = strip_trailing_semicolon(rest.trim());
        let formula = parse_boogie_expr(expr_str);
        let source_line = extract_source_line(line);
        state.vcs.push(VerificationCondition {
            name: format!("{proc_name}::{kind}::{}", state.vc_index),
            source_file: state.current_source_file.clone(),
            source_line: source_line.or(Some(line_num as u32)),
            formula,
            status: VcStatus::Unknown,
        });
        state.vc_index += 1;
    }
}

// ---------------------------------------------------------------------------
// Expression parsing
// ---------------------------------------------------------------------------

/// Parse a Boogie expression string into a `VcFormula`.
fn parse_boogie_expr(expr: &str) -> VcFormula {
    let expr = expr.trim();
    if expr.is_empty() {
        return VcFormula::bool_lit(true);
    }

    // Literals and negation.
    if let Some(f) = parse_boogie_atom(expr) {
        return f;
    }

    // Parenthesized expression.
    if expr.starts_with('(') && matching_paren(expr) == Some(expr.len() - 1) {
        return parse_boogie_expr(&expr[1..expr.len() - 1]);
    }

    // Binary operators (lowest precedence first).
    if let Some(f) = parse_boogie_binary_op(expr) {
        return f;
    }

    // Function application / map access.
    if let Some(f) = parse_boogie_application(expr) {
        return f;
    }

    // Fallback: variable reference.
    VcFormula::var(expr)
}

/// Parse atomic Boogie expressions: literals, negation, variables.
fn parse_boogie_atom(expr: &str) -> Option<VcFormula> {
    if expr == "true" {
        return Some(VcFormula::bool_lit(true));
    }
    if expr == "false" {
        return Some(VcFormula::bool_lit(false));
    }
    if let Ok(n) = expr.parse::<i64>() {
        return Some(VcFormula::int_lit(n));
    }
    if let Some(rest) = expr.strip_prefix('!') {
        return Some(VcFormula::not(parse_boogie_expr(rest.trim())));
    }
    None
}

/// Parse binary operator expressions in Boogie.
fn parse_boogie_binary_op(expr: &str) -> Option<VcFormula> {
    // Implication: ==>
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, "==>") {
        return Some(VcFormula::implies(
            parse_boogie_expr(lhs),
            parse_boogie_expr(rhs),
        ));
    }
    // Disjunction: ||
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, "||") {
        return Some(VcFormula::or(vec![
            parse_boogie_expr(lhs),
            parse_boogie_expr(rhs),
        ]));
    }
    // Conjunction: &&
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, "&&") {
        return Some(VcFormula::and(vec![
            parse_boogie_expr(lhs),
            parse_boogie_expr(rhs),
        ]));
    }
    // Equality: ==
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, "==") {
        return Some(VcFormula::eq(
            parse_boogie_expr(lhs),
            parse_boogie_expr(rhs),
        ));
    }
    // Inequality: !=
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, "!=") {
        return Some(VcFormula::not(VcFormula::eq(
            parse_boogie_expr(lhs),
            parse_boogie_expr(rhs),
        )));
    }
    parse_boogie_comparison_op(expr)
}

/// Parse comparison operators (`<=`, `>=`, `<`, `>`).
fn parse_boogie_comparison_op(expr: &str) -> Option<VcFormula> {
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, "<=") {
        return Some(VcFormula {
            kind: VcFormulaKind::Le,
            args: vec![parse_boogie_expr(lhs), parse_boogie_expr(rhs)],
            bound_vars: Vec::new(),
        });
    }
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, ">=") {
        return Some(VcFormula {
            kind: VcFormulaKind::Le,
            args: vec![parse_boogie_expr(rhs), parse_boogie_expr(lhs)],
            bound_vars: Vec::new(),
        });
    }
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, "<") {
        return Some(VcFormula {
            kind: VcFormulaKind::Lt,
            args: vec![parse_boogie_expr(lhs), parse_boogie_expr(rhs)],
            bound_vars: Vec::new(),
        });
    }
    if let Some((lhs, rhs)) = split_at_top_level_op(expr, ">") {
        return Some(VcFormula {
            kind: VcFormulaKind::Lt,
            args: vec![parse_boogie_expr(rhs), parse_boogie_expr(lhs)],
            bound_vars: Vec::new(),
        });
    }
    None
}

/// Parse function applications and map access in Boogie.
fn parse_boogie_application(expr: &str) -> Option<VcFormula> {
    // Function application: name(args...)
    if let Some(paren_start) = expr.find('(') {
        let name = expr[..paren_start].trim();
        if !name.is_empty()
            && name
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '.')
        {
            let args_str = &expr[paren_start + 1..expr.len().saturating_sub(1)];
            let args = split_args(args_str)
                .iter()
                .map(|a| parse_boogie_expr(a))
                .collect();
            return Some(VcFormula::func_app(name, args));
        }
    }
    // Map access: arr[idx] — represented as `select(arr, idx)`.
    if let Some(bracket_start) = expr.find('[') {
        if expr.ends_with(']') {
            let map_name = expr[..bracket_start].trim();
            let idx_str = &expr[bracket_start + 1..expr.len() - 1];
            if !map_name.is_empty() {
                return Some(VcFormula::func_app(
                    "select",
                    vec![parse_boogie_expr(map_name), parse_boogie_expr(idx_str)],
                ));
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract a procedure name from a `procedure` line.
fn extract_procedure_name(line: &str) -> Option<String> {
    let rest = line.strip_prefix("procedure")?.trim();
    let end = rest
        .find(|c: char| c == '(' || c.is_whitespace())
        .unwrap_or(rest.len());
    let name = &rest[..end];
    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
}

/// Strip a trailing semicolon from an expression string.
fn strip_trailing_semicolon(s: &str) -> &str {
    let s = s.trim();
    s.strip_suffix(';').unwrap_or(s).trim()
}

/// Extract a source line number from a `// source: file:line` comment.
fn extract_source_line(line: &str) -> Option<u32> {
    let comment_start = line.find("//")?;
    let comment = line[comment_start + 2..].trim();
    let rest = comment.strip_prefix("source:")?.trim();
    let num_str = if let Some(colon_pos) = rest.rfind(':') {
        &rest[colon_pos + 1..]
    } else {
        rest
    };
    num_str.trim().parse::<u32>().ok()
}

/// Find the index of the matching closing parenthesis for the first `(`.
fn matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Split at a top-level binary operator (not inside parentheses or brackets).
fn split_at_top_level_op<'a>(s: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let op_len = op.len();
    let bytes = s.as_bytes();

    // Scan from end for left-associative splitting.
    let mut i = s.len();
    while i >= op_len {
        let ch = bytes[i - 1] as char;
        match ch {
            ')' | ']' => depth += 1,
            '(' | '[' => depth -= 1,
            _ => {}
        }
        if depth == 0 && i >= op_len && &s[i - op_len..i] == op {
            let lhs = s[..i - op_len].trim();
            let rhs = s[i..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                return Some((lhs, rhs));
            }
        }
        i -= 1;
    }
    None
}

/// Split a comma-separated argument list, respecting parentheses/brackets.
fn split_args(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                let arg = s[start..i].trim();
                if !arg.is_empty() {
                    result.push(arg);
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = s[start..].trim();
    if !last.is_empty() {
        result.push(last);
    }
    result
}

#[cfg(test)]
#[path = "tests_boogie.rs"]
mod tests;
