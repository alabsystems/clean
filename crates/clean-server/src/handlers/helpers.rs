// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helper utilities for request handlers.
//!
//! This module provides common formatting, parsing, and suggestion utilities
//! used across different handler implementations.

use clean_kernel::Expr;
use clean_parser::ParseError;

/// Format an expression for display using the Lean-style pretty printer.
pub fn format_expr(expr: &Expr) -> String {
    expr.to_string()
}

/// Format a parse error for API response.
pub fn format_parse_error(e: &ParseError) -> String {
    e.to_string()
}

/// Extract line number from parse error.
pub fn parse_error_line(e: &ParseError) -> Option<usize> {
    match e {
        ParseError::UnexpectedToken { line, .. } => Some(*line),
        ParseError::UnexpectedEof | ParseError::NumericOverflow { .. } => None,
        _ => None, // Handle future variants
    }
}

/// Extract column number from parse error.
pub fn parse_error_col(e: &ParseError) -> Option<usize> {
    match e {
        ParseError::UnexpectedToken { col, .. } => Some(*col),
        ParseError::UnexpectedEof | ParseError::NumericOverflow { .. } => None,
        _ => None, // Handle future variants
    }
}

/// Parse a tactic script into individual tactics.
///
/// Splits by semicolons or newlines, handling both styles.
pub fn parse_tactic_script(script: &str) -> Vec<String> {
    clean_elab::tactic::parse_tactic_script(script)
}

/// Generate suggestions for a failed tactic.
///
/// This helps LLMs recover from errors by suggesting related tactics.
pub fn generate_tactic_suggestions(tactic: &str) -> Vec<String> {
    let parts: Vec<&str> = tactic.split_whitespace().collect();
    let tactic_name = parts.first().copied().unwrap_or("");

    match tactic_name {
        "exact" => vec![
            "try 'apply' instead of 'exact'".to_string(),
            "check that the term has the correct type".to_string(),
        ],
        "apply" => vec![
            "check that the function type matches goal".to_string(),
            "try 'exact' for terms".to_string(),
        ],
        "simp" => vec![
            "try 'simp only [...]' with specific lemmas".to_string(),
            "try 'simp_all' to use all hypotheses".to_string(),
        ],
        "rfl" => vec![
            "the goal may not be definitionally equal".to_string(),
            "try 'eq_refl' or 'Eq.refl'".to_string(),
        ],
        "intro" | "intros" => vec!["check that the goal is a forall/arrow type".to_string()],
        "induction" => vec![
            "check variable name and type".to_string(),
            "ensure the type has a recursor".to_string(),
        ],
        _ => vec![format!(
            "tactic '{}' may not exist or have different syntax",
            tactic_name
        )],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Expr, ExprKind};

    #[test]
    fn test_format_expr_basic() {
        let expr = Expr::from_kind(ExprKind::Sort(clean_kernel::Level::Zero));
        let formatted = format_expr(&expr);
        // Sort(Level::Zero) is Prop (Sort 0), which displays as "Prop"
        assert!(
            formatted.contains("Prop"),
            "expected 'Prop' in '{formatted}'"
        );
    }

    #[test]
    fn test_format_parse_error() {
        let err = ParseError::UnexpectedEof;
        let formatted = format_parse_error(&err);
        assert!(!formatted.is_empty());
    }

    #[test]
    fn test_parse_error_line_with_token() {
        let err = ParseError::UnexpectedToken {
            message: "expected identifier, found number".to_string(),
            line: 5,
            col: 10,
        };
        assert_eq!(parse_error_line(&err), Some(5));
    }

    #[test]
    fn test_parse_error_line_eof() {
        let err = ParseError::UnexpectedEof;
        assert_eq!(parse_error_line(&err), None);
    }

    #[test]
    fn test_parse_error_col_with_token() {
        let err = ParseError::UnexpectedToken {
            message: "expected identifier, found number".to_string(),
            line: 5,
            col: 10,
        };
        assert_eq!(parse_error_col(&err), Some(10));
    }

    #[test]
    fn test_parse_error_col_eof() {
        let err = ParseError::UnexpectedEof;
        assert_eq!(parse_error_col(&err), None);
    }

    #[test]
    fn test_parse_tactic_script_basic() {
        let script = "intro h\napply h\nrfl";
        let tactics = parse_tactic_script(script);
        assert_eq!(tactics, vec!["intro h", "apply h", "rfl"]);
    }

    #[test]
    fn test_parse_tactic_script_with_semicolons() {
        let script = "intro h; apply h; rfl";
        let tactics = parse_tactic_script(script);
        assert_eq!(tactics, vec!["intro h", "apply h", "rfl"]);
    }

    #[test]
    fn test_parse_tactic_script_with_blanks() {
        let script = "\n  intro h  \n\n  apply h\n\n";
        let tactics = parse_tactic_script(script);
        assert_eq!(tactics, vec!["intro h", "apply h"]);
    }

    #[test]
    fn test_generate_suggestions_simp() {
        let suggestions = generate_tactic_suggestions("simp");
        assert!(suggestions.iter().any(|s| s.contains("simp only")));
    }

    #[test]
    fn test_generate_suggestions_exact() {
        let suggestions = generate_tactic_suggestions("exact foo");
        assert!(suggestions.iter().any(|s| s.contains("apply")));
    }

    #[test]
    fn test_generate_suggestions_unknown() {
        let suggestions = generate_tactic_suggestions("unknown_tactic");
        assert!(suggestions.iter().any(|s| s.contains("unknown_tactic")));
    }
}
