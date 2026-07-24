// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WhyML verification condition parser for the Mathverse Library.
//!
//! Why3 exports VCs from WhyML programs as goal blocks within theory
//! declarations. This module parses that format into [`VerificationCondition`]
//! values with structured formulas.

use thiserror::Error;

use super::types::{VcFormula, VcFormulaKind, VcStatus, VerificationCondition};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors raised during WhyML VC parsing.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum WhymlParseError {
    /// The input is empty or contains no parseable content.
    #[error("empty or blank input")]
    EmptyInput,

    /// No goal declarations found in the input.
    #[error("no goal declarations found")]
    NoGoals,

    /// Malformed goal declaration.
    #[error("malformed goal at line {line}: {reason}")]
    MalformedGoal { line: usize, reason: String },

    /// Unsupported WhyML type annotation.
    #[error("unsupported WhyML type: {typ}")]
    UnsupportedType { typ: String },
}

// ---------------------------------------------------------------------------
// Parser state
// ---------------------------------------------------------------------------

/// Mutable state carried through WhyML VC parsing.
struct WhymlParseState {
    vcs: Vec<VerificationCondition>,
    current_theory: Option<String>,
    current_source_file: Option<String>,
    in_goal: bool,
    goal_name: String,
    goal_body: String,
    goal_line: usize,
}

impl WhymlParseState {
    fn new() -> Self {
        Self {
            vcs: Vec::new(),
            current_theory: None,
            current_source_file: None,
            in_goal: false,
            goal_name: String::new(),
            goal_body: String::new(),
            goal_line: 0,
        }
    }

    /// Flush the current goal (if any) into the VC list.
    fn flush_goal(&mut self) {
        if !self.in_goal {
            return;
        }
        let formula = parse_whyml_formula(&self.goal_body);
        let vc_name = make_vc_name(self.current_theory.as_deref(), &self.goal_name);
        self.vcs.push(VerificationCondition {
            name: vc_name,
            source_file: self.current_source_file.clone(),
            source_line: Some(self.goal_line as u32),
            formula,
            status: VcStatus::Unknown,
        });
        self.in_goal = false;
        self.goal_body.clear();
    }
}

// ---------------------------------------------------------------------------
// Top-level parser
// ---------------------------------------------------------------------------

/// Parse WhyML VCs from text input into verification conditions.
///
/// Extracts `goal` blocks from Why3's VC export format. Supports standalone
/// goals and goals within `theory ... end` blocks.
///
/// # Errors
///
/// Returns `WhymlParseError` if the input is empty or has no goals.
pub fn parse_whyml_vcs(input: &str) -> Result<Vec<VerificationCondition>, WhymlParseError> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err(WhymlParseError::EmptyInput);
    }

    let mut state = WhymlParseState::new();

    for (line_idx, line) in trimmed.lines().enumerate() {
        parse_whyml_line(line.trim(), line_idx + 1, &mut state);
    }

    // Flush final goal if file doesn't end with `end`.
    state.flush_goal();

    if state.vcs.is_empty() {
        return Err(WhymlParseError::NoGoals);
    }

    Ok(state.vcs)
}

/// Process a single line of WhyML input.
fn parse_whyml_line(line: &str, line_num: usize, state: &mut WhymlParseState) {
    // Source file annotation in comments.
    if line.starts_with("(*") {
        if let Some(rest) = line.strip_prefix("(* file:") {
            let rest = rest.trim().strip_suffix("*)").unwrap_or(rest).trim();
            if !rest.is_empty() {
                state.current_source_file = Some(rest.to_string());
            }
        }
        return;
    }

    // Theory declaration.
    if line.starts_with("theory") {
        state.current_theory = extract_whyml_name(line, "theory");
        return;
    }

    // End of theory.
    if line == "end" {
        state.flush_goal();
        state.current_theory = None;
        return;
    }

    // Goal declaration.
    if line.starts_with("goal") {
        state.flush_goal();
        state.goal_name = extract_goal_name(line).unwrap_or_else(|| "anon".to_string());
        state.goal_line = line_num;
        state.in_goal = true;

        // Check if formula starts on the same line after the colon.
        if let Some(colon_pos) = line.find(':') {
            let rest = line[colon_pos + 1..].trim();
            if !rest.is_empty() {
                state.goal_body.push_str(rest);
                state.goal_body.push(' ');
            }
        }
        return;
    }

    // Accumulate goal body lines.
    if state.in_goal {
        state.goal_body.push_str(line);
        state.goal_body.push(' ');
    }
}

// ---------------------------------------------------------------------------
// Formula parsing
// ---------------------------------------------------------------------------

/// Parse a WhyML formula string into a `VcFormula`.
fn parse_whyml_formula(formula: &str) -> VcFormula {
    let formula = formula.trim();
    if formula.is_empty() {
        return VcFormula::bool_lit(true);
    }

    // Atoms (literals, negation).
    if let Some(f) = parse_whyml_atom(formula) {
        return f;
    }

    // Parenthesized expression.
    if formula.starts_with('(') && matching_paren_whyml(formula) == Some(formula.len() - 1) {
        return parse_whyml_formula(&formula[1..formula.len() - 1]);
    }

    // Quantifiers.
    if let Some(f) = parse_whyml_quantifier(formula) {
        return f;
    }

    // Binary connectives (lowest precedence first).
    if let Some(f) = parse_whyml_connective(formula) {
        return f;
    }

    // Comparisons.
    if let Some(f) = parse_whyml_comparison(formula) {
        return f;
    }

    // Function application (WhyML uses juxtaposition).
    let tokens = tokenize_whyml(formula);
    if tokens.len() > 1 {
        let name = &tokens[0];
        let args: Vec<VcFormula> = tokens[1..].iter().map(|t| parse_whyml_formula(t)).collect();
        return VcFormula::func_app(name.as_str(), args);
    }

    // Fallback: variable reference.
    VcFormula::var(formula)
}

/// Parse atomic WhyML expressions: boolean/integer literals, negation.
fn parse_whyml_atom(formula: &str) -> Option<VcFormula> {
    if formula == "true" {
        return Some(VcFormula::bool_lit(true));
    }
    if formula == "false" {
        return Some(VcFormula::bool_lit(false));
    }
    if let Ok(n) = formula.parse::<i64>() {
        return Some(VcFormula::int_lit(n));
    }
    if let Some(rest) = formula.strip_prefix("not ") {
        return Some(VcFormula::not(parse_whyml_formula(rest.trim())));
    }
    None
}

/// Parse WhyML quantifier expressions (`forall`, `exists`).
fn parse_whyml_quantifier(formula: &str) -> Option<VcFormula> {
    let is_forall = formula.starts_with("forall ");
    let is_exists = formula.starts_with("exists ");
    if !is_forall && !is_exists {
        return None;
    }

    let rest = &formula[7..]; // skip "forall " or "exists "
    let dot_pos = find_quantifier_dot(rest)?;
    let vars_str = rest[..dot_pos].trim();
    let body_str = rest[dot_pos + 1..].trim();
    let bound_vars = parse_whyml_bound_vars(vars_str);
    let body = parse_whyml_formula(body_str);
    let kind = if is_forall {
        VcFormulaKind::Forall
    } else {
        VcFormulaKind::Exists
    };
    Some(VcFormula {
        kind,
        args: vec![body],
        bound_vars,
    })
}

/// Parse WhyML logical connectives: `<->`, `->`, `\/`, `/\`, `<>`, `=`.
fn parse_whyml_connective(formula: &str) -> Option<VcFormula> {
    if let Some((lhs, rhs)) = split_at_top_level(formula, "<->") {
        return Some(VcFormula::and(vec![
            VcFormula::implies(parse_whyml_formula(lhs), parse_whyml_formula(rhs)),
            VcFormula::implies(parse_whyml_formula(rhs), parse_whyml_formula(lhs)),
        ]));
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, "->") {
        return Some(VcFormula::implies(
            parse_whyml_formula(lhs),
            parse_whyml_formula(rhs),
        ));
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, r"\/") {
        return Some(VcFormula::or(vec![
            parse_whyml_formula(lhs),
            parse_whyml_formula(rhs),
        ]));
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, r"/\") {
        return Some(VcFormula::and(vec![
            parse_whyml_formula(lhs),
            parse_whyml_formula(rhs),
        ]));
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, "<>") {
        return Some(VcFormula::not(VcFormula::eq(
            parse_whyml_formula(lhs),
            parse_whyml_formula(rhs),
        )));
    }
    None
}

/// Parse WhyML comparison operators: `<=`, `>=`, `<`, `>`, `=`.
fn parse_whyml_comparison(formula: &str) -> Option<VcFormula> {
    if let Some((lhs, rhs)) = split_at_top_level(formula, "<=") {
        return Some(VcFormula {
            kind: VcFormulaKind::Le,
            args: vec![parse_whyml_formula(lhs), parse_whyml_formula(rhs)],
            bound_vars: Vec::new(),
        });
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, ">=") {
        return Some(VcFormula {
            kind: VcFormulaKind::Le,
            args: vec![parse_whyml_formula(rhs), parse_whyml_formula(lhs)],
            bound_vars: Vec::new(),
        });
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, "<") {
        return Some(VcFormula {
            kind: VcFormulaKind::Lt,
            args: vec![parse_whyml_formula(lhs), parse_whyml_formula(rhs)],
            bound_vars: Vec::new(),
        });
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, ">") {
        return Some(VcFormula {
            kind: VcFormulaKind::Lt,
            args: vec![parse_whyml_formula(rhs), parse_whyml_formula(lhs)],
            bound_vars: Vec::new(),
        });
    }
    if let Some((lhs, rhs)) = split_at_top_level(formula, "=") {
        return Some(VcFormula::eq(
            parse_whyml_formula(lhs),
            parse_whyml_formula(rhs),
        ));
    }
    None
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract a name after a keyword: `<keyword> <name>`.
fn extract_whyml_name(line: &str, keyword: &str) -> Option<String> {
    let rest = line.strip_prefix(keyword)?.trim();
    let end = rest
        .find(|c: char| !c.is_alphanumeric() && c != '_' && c != '.')
        .unwrap_or(rest.len());
    let name = &rest[..end];
    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
}

/// Extract a goal name from `goal <name>:`.
fn extract_goal_name(line: &str) -> Option<String> {
    let rest = line.strip_prefix("goal")?.trim();
    let end = rest.find(':')?;
    let name = rest[..end].trim();
    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
}

/// Construct a VC name with optional theory prefix.
fn make_vc_name(theory: Option<&str>, goal: &str) -> String {
    if let Some(t) = theory {
        format!("{t}.{goal}")
    } else {
        goal.to_string()
    }
}

/// Find the matching close paren for an opening `(`.
fn matching_paren_whyml(s: &str) -> Option<usize> {
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

/// Find the dot separating quantifier variables from the body.
fn find_quantifier_dot(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            '.' if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// Parse WhyML bound variable declarations.
fn parse_whyml_bound_vars(s: &str) -> Vec<String> {
    let mut vars = Vec::new();
    for part in s.split(',') {
        let part = part.trim();
        let name_part = if let Some(colon_pos) = part.find(':') {
            part[..colon_pos].trim()
        } else {
            part
        };
        for name in name_part.split_whitespace() {
            let name = name.trim();
            if !name.is_empty() && name != ":" {
                vars.push(name.to_string());
            }
        }
    }
    vars
}

/// Split at a top-level operator (not inside parentheses).
fn split_at_top_level<'a>(s: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let op_len = op.len();
    let bytes = s.as_bytes();
    let mut i = s.len();
    while i >= op_len {
        let ch = bytes[i - 1] as char;
        match ch {
            ')' => depth += 1,
            '(' => depth -= 1,
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

/// Tokenize a WhyML formula into top-level tokens, respecting parentheses.
fn tokenize_whyml(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();

    for ch in s.chars() {
        match ch {
            '(' => {
                if depth == 0 && !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth -= 1;
                current.push(ch);
                if depth == 0 {
                    tokens.push(current.clone());
                    current.clear();
                }
            }
            ' ' | '\t' | '\n' if depth == 0 => {
                let token = current.trim().to_string();
                if !token.is_empty() {
                    tokens.push(token);
                }
                current.clear();
            }
            _ => current.push(ch),
        }
    }

    let last = current.trim().to_string();
    if !last.is_empty() {
        tokens.push(last);
    }

    tokens
}

#[cfg(test)]
#[path = "tests_whyml.rs"]
mod tests;
