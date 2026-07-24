// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Post-processing for LLM-generated Lean code.
//!
//! Applies repairs for common LLM output errors:
//! - Strip residual LaTeX artifacts
//! - Fix incomplete `let` bindings (auto-close with `sorry`)
//! - Rewrite dot notation on auto-implicit variables to explicit calls

/// Known dot-notation patterns on auto-implicit variables that should be
/// rewritten to explicit function-call style.
///
/// Each entry: `(dot_suffix, replacement_prefix)`.
const DOT_NOTATION_REWRITES: &[(&str, &str)] = &[
    (".Adj", "SimpleGraph.Adj"),
    (".IsTree", "IsTree"),
    (".IsConnected", "IsConnected"),
    (".IsBipartite", "SimpleGraph.IsBipartite"),
    (".Nonempty", "Nonempty"),
    (".degree", "SimpleGraph.degree"),
    (".edgeSet", "SimpleGraph.edgeSet"),
    (".neighborSet", "SimpleGraph.neighborSet"),
];

/// Post-process LLM-generated Lean code to fix common errors.
///
/// Applies these repairs in order:
/// 1. Strip residual LaTeX artifacts
/// 2. Fix incomplete `let` bindings (auto-close with `sorry`)
/// 3. Rewrite dot notation on auto-implicit variables
#[must_use]
pub fn postprocess_lean_code(code: &str) -> String {
    let code = strip_latex_artifacts(code);
    let code = fix_incomplete_let_bindings(&code);
    rewrite_dot_notation(&code)
}

/// Strip common LaTeX artifacts that slip through extraction.
#[must_use]
pub(crate) fn strip_latex_artifacts(code: &str) -> String {
    let mut result = String::with_capacity(code.len());
    for line in code.lines() {
        let trimmed = line.trim();
        // Skip pure-LaTeX lines
        if trimmed.starts_with("\\[")
            || trimmed.starts_with("\\]")
            || trimmed.starts_with("\\begin{")
            || trimmed.starts_with("\\end{")
            || trimmed.starts_with("$$")
        {
            continue;
        }
        // Remove inline LaTeX commands that sometimes appear
        let cleaned = line
            .replace("\\emph{", "")
            .replace("\\textbf{", "")
            .replace("\\textit{", "")
            .replace("\\text{", "")
            .replace("\\mathbb{", "")
            .replace("\\mathrm{", "");
        result.push_str(&cleaned);
        result.push('\n');
    }
    // Remove trailing newline if input didn't have one
    if !code.ends_with('\n') {
        result.truncate(result.trim_end_matches('\n').len());
    }
    result
}

/// Fix incomplete `let` bindings that lack a body expression.
///
/// LLMs often produce `let x := expr` without a continuation. This detects
/// the pattern and appends `; sorry` to make it syntactically valid.
#[must_use]
pub(crate) fn fix_incomplete_let_bindings(code: &str) -> String {
    let lines: Vec<&str> = code.lines().collect();
    let mut result = Vec::with_capacity(lines.len());

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        // Detect `let ... := ...` where the next non-empty line is NOT indented
        // more (i.e., there's no continuation body).
        if trimmed.starts_with("let ") && trimmed.contains(":=") {
            let has_continuation = if i + 1 < lines.len() {
                let next = lines[i + 1];
                let next_trimmed = next.trim();
                // A continuation is either:
                // - a non-empty line that's more indented, or
                // - a line starting with typical continuation tokens
                !next_trimmed.is_empty()
                    && (next.len() - next.trim_start().len() > line.len() - line.trim_start().len()
                        || next_trimmed.starts_with("let ")
                        || next_trimmed.starts_with("have ")
                        || next_trimmed.starts_with("show ")
                        || next_trimmed.starts_with("in ")
                        || next_trimmed.starts_with("return ")
                        || next_trimmed.starts_with("exact "))
            } else {
                false
            };

            if !has_continuation {
                // Check if the let already has a semicolon continuation
                if !trimmed.ends_with(';') && !trimmed.contains("; ") {
                    result.push(format!("{line}; sorry"));
                    continue;
                }
            }
        }
        result.push((*line).to_string());
    }

    result.join("\n")
}

/// Rewrite dot notation on auto-implicit type variables to explicit calls.
///
/// Converts patterns like `G.Adj u v` to `SimpleGraph.Adj G u v`.
#[must_use]
pub(crate) fn rewrite_dot_notation(code: &str) -> String {
    let mut result = code.to_string();

    for &(dot_suffix, replacement) in DOT_NOTATION_REWRITES {
        let mut new_result = String::with_capacity(result.len());
        let mut chars = result.char_indices().peekable();

        while let Some((i, ch)) = chars.next() {
            if ch.is_ascii_uppercase() {
                let var_name = &result[i..i + 1];
                let rest = &result[i + 1..];
                if rest.starts_with(dot_suffix) {
                    let at_boundary = i == 0 || !result.as_bytes()[i - 1].is_ascii_alphanumeric();
                    if at_boundary {
                        new_result.push_str(replacement);
                        new_result.push(' ');
                        new_result.push_str(var_name);
                        for _ in 0..dot_suffix.len() {
                            chars.next();
                        }
                        continue;
                    }
                }
            }
            new_result.push(ch);
        }

        result = new_result;
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser_handles_incomplete_let() {
        let code = "def foo : Nat :=\n  let x := 42";
        let fixed = fix_incomplete_let_bindings(code);
        assert!(
            fixed.contains("let x := 42; sorry"),
            "incomplete let should be closed with sorry, got: {fixed}"
        );
    }

    #[test]
    fn test_parser_handles_incomplete_let_at_eof() {
        let code = "let result := compute a b";
        let fixed = fix_incomplete_let_bindings(code);
        assert!(
            fixed.contains("; sorry"),
            "EOF let should get sorry: {fixed}"
        );
    }

    #[test]
    fn test_parser_preserves_complete_let() {
        let code = "def foo : Nat :=\n  let x := 42\n    x + 1";
        let fixed = fix_incomplete_let_bindings(code);
        assert!(
            !fixed.contains("sorry"),
            "complete let should not be modified: {fixed}"
        );
    }

    #[test]
    fn test_parser_handles_dot_notation() {
        let code = "theorem foo (G : SimpleGraph V) : G.Adj u v := sorry";
        let fixed = rewrite_dot_notation(code);
        assert!(
            fixed.contains("SimpleGraph.Adj G"),
            "G.Adj should become SimpleGraph.Adj G, got: {fixed}"
        );
        assert!(
            !fixed.contains("G.Adj"),
            "original dot notation should be gone: {fixed}"
        );
    }

    #[test]
    fn test_parser_handles_dot_notation_is_tree() {
        let code = "hypothesis : T.IsTree";
        let fixed = rewrite_dot_notation(code);
        assert!(
            fixed.contains("IsTree T"),
            "T.IsTree should become IsTree T, got: {fixed}"
        );
    }

    #[test]
    fn test_strip_latex_artifacts() {
        let code = "\\[\ntheorem foo : Nat := 0\n\\]";
        let cleaned = strip_latex_artifacts(code);
        assert!(
            !cleaned.contains("\\["),
            "LaTeX display delimiters should be removed: {cleaned}"
        );
        assert!(cleaned.contains("theorem foo"));
    }

    #[test]
    fn test_strip_latex_inline_commands() {
        let code = "def \\emph{prime} := sorry";
        let cleaned = strip_latex_artifacts(code);
        assert!(
            !cleaned.contains("\\emph{"),
            "inline LaTeX should be stripped: {cleaned}"
        );
        assert!(cleaned.contains("prime"));
    }

    #[test]
    fn test_postprocess_combined() {
        let code = "\\[\ndef foo :=\n  let x := G.Adj u v\n\\]";
        let fixed = postprocess_lean_code(code);
        assert!(!fixed.contains("\\["), "LaTeX gone: {fixed}");
        assert!(
            fixed.contains("SimpleGraph.Adj G"),
            "dot notation fixed: {fixed}"
        );
        assert!(fixed.contains("; sorry"), "incomplete let fixed: {fixed}");
    }
}
