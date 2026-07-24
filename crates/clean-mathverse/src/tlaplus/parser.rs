// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ file parser.
//!
//! Parses `.tla` TLA+ specification files into structured AST. Handles
//! module delimiters (`---- MODULE Name ----` / `====`), `\*` line comments,
//! `(* ... *)` block comments, and the main declaration forms:
//! CONSTANT, VARIABLE, THEOREM, LEMMA, PROPOSITION, COROLLARY, AXIOM,
//! ASSUME, INSTANCE, and operator definitions (`Op(...) == body`).
//!
//! The parser is line-oriented for declarations (TLA+ is not fully
//! context-free at the lexical level), with best-effort expression parsing
//! for operator bodies and theorem statements.

use super::types::{QuantifierKind, TlaDecl, TlaDeclKind, TlaExpr, TlaModule};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error type
// ════════════════════════════════════════════════════════════════════════════

/// Errors raised during TLA+ parsing.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TlaParseError {
    /// I/O error reading file.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Syntax error.
    #[error("parse error at line {line}: {msg}")]
    Syntax { line: usize, msg: String },
    /// No module found.
    #[error("no TLA+ module found")]
    NoModule,
}

pub(crate) type TlaParseResult<T> = Result<T, TlaParseError>;

// ════════════════════════════════════════════════════════════════════════════
// Line-level utilities
// ════════════════════════════════════════════════════════════════════════════

/// Strip TLA+ comments from a line.
fn strip_comment(line: &str) -> &str {
    // \* is a line comment prefix.
    if let Some(idx) = line.find("\\*") {
        &line[..idx]
    } else {
        line
    }
}

/// Check if a line is a module header: `---- MODULE Name ----`
fn parse_module_header(line: &str) -> Option<String> {
    let trimmed = line.trim();
    if !trimmed.starts_with("----") {
        return None;
    }
    // Strip leading dashes.
    let after_dashes = trimmed.trim_start_matches('-').trim();
    if !after_dashes.starts_with("MODULE") {
        return None;
    }
    let after_module = after_dashes["MODULE".len()..].trim();
    // Strip trailing dashes.
    let name = after_module.trim_end_matches('-').trim();
    if name.is_empty() {
        return None;
    }
    Some(name.to_owned())
}

/// Check if a line is a module footer: `====...`
fn is_module_footer(line: &str) -> bool {
    line.trim().starts_with("====")
}

/// Split comma-separated identifiers: `x, y, z`.
fn split_identifiers(text: &str) -> Vec<String> {
    text.split(',')
        .map(|s| s.trim().to_owned())
        .filter(|s| !s.is_empty())
        .collect()
}

// ════════════════════════════════════════════════════════════════════════════
// Expression parser (best-effort)
// ════════════════════════════════════════════════════════════════════════════

/// Parse a TLA+ expression from a string (best-effort).
///
/// This is a simplified parser that handles the most common patterns.
/// Complex expressions are returned as `TlaExpr::Raw`.
fn parse_expr(text: &str) -> TlaExpr {
    let trimmed = text.trim();
    if trimmed.is_empty() {
        return TlaExpr::Raw(String::new());
    }

    // Boolean literals.
    if trimmed == "TRUE" {
        return TlaExpr::BoolLit(true);
    }
    if trimmed == "FALSE" {
        return TlaExpr::BoolLit(false);
    }

    // Integer literal.
    if let Ok(n) = trimmed.parse::<i64>() {
        return TlaExpr::IntLit(n);
    }

    // String literal.
    if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() >= 2 {
        return TlaExpr::StringLit(trimmed[1..trimmed.len() - 1].to_owned());
    }

    // Check for common binary operators.
    for (op, op_str) in &[
        ("/\\", "/\\"),
        ("\\/", "\\/"),
        ("=>", "=>"),
        ("=", "="),
        ("#", "#"),
        ("/=", "/="),
        ("\\in", "\\in"),
        ("\\notin", "\\notin"),
        ("\\subseteq", "\\subseteq"),
        ("\\cup", "\\cup"),
        ("\\cap", "\\cap"),
        (">=", ">="),
        ("<=", "<="),
        (">", ">"),
        ("<", "<"),
        ("+", "+"),
        ("-", "-"),
        ("*", "*"),
    ] {
        // Find the operator not inside brackets/parens.
        if let Some(idx) = find_top_level_op(trimmed, op) {
            let lhs = trimmed[..idx].trim();
            let rhs = trimmed[idx + op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                return TlaExpr::BinOp(
                    op_str.to_string(),
                    Box::new(parse_expr(lhs)),
                    Box::new(parse_expr(rhs)),
                );
            }
        }
    }

    // Universal quantifier: \A x \in S : P
    if trimmed.starts_with("\\A ") || trimmed.starts_with("\\A") {
        if let Some(body) = parse_quantifier_expr(trimmed, QuantifierKind::ForAll) {
            return body;
        }
    }

    // Existential quantifier: \E x \in S : P
    if trimmed.starts_with("\\E ") || trimmed.starts_with("\\E") {
        if let Some(body) = parse_quantifier_expr(trimmed, QuantifierKind::Exists) {
            return body;
        }
    }

    // Primed: x'
    if trimmed.ends_with('\'') && trimmed.len() > 1 {
        let inner = &trimmed[..trimmed.len() - 1];
        if is_identifier(inner) {
            return TlaExpr::Prime(Box::new(TlaExpr::Ident(inner.to_owned())));
        }
    }

    // Simple identifier.
    if is_identifier(trimmed) {
        return TlaExpr::Ident(trimmed.to_owned());
    }

    // Function application: Op(arg1, arg2, ...)
    if let Some(paren) = trimmed.find('(') {
        let name = trimmed[..paren].trim();
        if is_identifier(name) && trimmed.ends_with(')') {
            let args_str = &trimmed[paren + 1..trimmed.len() - 1];
            let args: Vec<TlaExpr> = args_str.split(',').map(|a| parse_expr(a.trim())).collect();
            return TlaExpr::App(name.to_owned(), args);
        }
    }

    // Fall back to raw text.
    TlaExpr::Raw(trimmed.to_owned())
}

/// Find a top-level occurrence of `op` in `text` (not inside parens, brackets, or braces).
fn find_top_level_op(text: &str, op: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let op_bytes = op.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i + op_bytes.len() <= bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' | b'<' if i + 1 < bytes.len() && bytes[i + 1] == b'<' => {
                depth += 1;
                i += 1;
            }
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'>' if i + 1 < bytes.len() && bytes[i + 1] == b'>' => {
                depth -= 1;
                i += 1;
            }
            _ => {}
        }
        if depth == 0
            && i + op_bytes.len() <= bytes.len()
            && &bytes[i..i + op_bytes.len()] == op_bytes
        {
            // Make sure it's not part of a larger operator.
            let before_ok = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
            let after_ok = i + op_bytes.len() >= bytes.len()
                || !bytes[i + op_bytes.len()].is_ascii_alphanumeric();
            if before_ok && after_ok {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

fn parse_quantifier_expr(text: &str, kind: QuantifierKind) -> Option<TlaExpr> {
    // \A x \in S : P or \A x : P
    let prefix = if kind == QuantifierKind::ForAll {
        "\\A"
    } else {
        "\\E"
    };
    let after = text[prefix.len()..].trim();
    if let Some(colon) = after.find(':') {
        let binding = after[..colon].trim();
        let body = after[colon + 1..].trim();
        // Check for \in
        if let Some(in_idx) = binding.find("\\in") {
            let var = binding[..in_idx].trim();
            let set = binding[in_idx + 3..].trim();
            return Some(TlaExpr::Quantifier(
                kind,
                vec![(var.to_owned(), Some(parse_expr(set)))],
                Box::new(parse_expr(body)),
            ));
        }
        return Some(TlaExpr::Quantifier(
            kind,
            vec![(binding.to_owned(), None)],
            Box::new(parse_expr(body)),
        ));
    }
    None
}

fn is_identifier(s: &str) -> bool {
    !s.is_empty()
        && (s.as_bytes()[0].is_ascii_alphabetic() || s.as_bytes()[0] == b'_')
        && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

// ════════════════════════════════════════════════════════════════════════════
// Module-level parser
// ════════════════════════════════════════════════════════════════════════════

/// Parse a TLA+ module from text.
///
/// # Errors
///
/// Returns `TlaParseError` if no module header is found.
pub fn parse_tlaplus(text: &str) -> TlaParseResult<TlaModule> {
    let lines: Vec<&str> = text.lines().collect();
    let mut module = TlaModule::default();
    let mut in_module = false;
    let mut in_block_comment = false;

    // Accumulator for multi-line definitions.
    let mut current_def_name: Option<String> = None;
    let mut current_def_lines: Vec<String> = Vec::new();
    let mut current_def_kind: TlaDeclKind = TlaDeclKind::Operator;
    let mut current_def_params: Vec<String> = Vec::new();

    for &line in lines.iter() {
        // Block comment handling.
        if in_block_comment {
            if line.contains("*)") {
                in_block_comment = false;
            }
            continue;
        }
        if line.contains("(*") && !line.contains("*)") {
            in_block_comment = true;
            continue;
        }

        // Strip inline block comments and line comments.
        let cleaned = strip_comment(line);
        let trimmed = cleaned.trim();

        if trimmed.is_empty() {
            continue;
        }

        // Module header.
        if let Some(name) = parse_module_header(trimmed) {
            module.name = name;
            in_module = true;
            continue;
        }

        // Module footer.
        if is_module_footer(trimmed) {
            // Flush any pending definition.
            if let Some(name) = current_def_name.take() {
                let body_text = current_def_lines.join(" ");
                module.declarations.push(TlaDecl {
                    name,
                    kind: current_def_kind,
                    params: std::mem::take(&mut current_def_params),
                    body: if body_text.is_empty() {
                        None
                    } else {
                        Some(parse_expr(&body_text))
                    },
                });
                current_def_lines.clear();
            }
            break;
        }

        if !in_module {
            continue;
        }

        // Flush pending definition if this line starts a new declaration.
        if starts_new_declaration(trimmed) {
            if let Some(name) = current_def_name.take() {
                let body_text = current_def_lines.join(" ");
                module.declarations.push(TlaDecl {
                    name,
                    kind: current_def_kind,
                    params: std::mem::take(&mut current_def_params),
                    body: if body_text.is_empty() {
                        None
                    } else {
                        Some(parse_expr(&body_text))
                    },
                });
                current_def_lines.clear();
            }
        }

        // EXTENDS
        if let Some(rest) = trimmed.strip_prefix("EXTENDS") {
            let rest = rest.trim();
            module.extends = split_identifiers(rest);
            continue;
        }

        // CONSTANT / CONSTANTS
        if trimmed.starts_with("CONSTANT ") || trimmed.starts_with("CONSTANTS ") {
            let keyword_len = if trimmed.starts_with("CONSTANTS") {
                9
            } else {
                8
            };
            let rest = trimmed[keyword_len..].trim();
            for name in split_identifiers(rest) {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Constant,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }

        // VARIABLE / VARIABLES
        if trimmed.starts_with("VARIABLE ") || trimmed.starts_with("VARIABLES ") {
            let keyword_len = if trimmed.starts_with("VARIABLES") {
                9
            } else {
                8
            };
            let rest = trimmed[keyword_len..].trim();
            for name in split_identifiers(rest) {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Variable,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }

        // THEOREM / LEMMA / PROPOSITION / COROLLARY
        for (keyword, kind) in &[
            ("THEOREM", TlaDeclKind::Theorem),
            ("LEMMA", TlaDeclKind::Lemma),
            ("PROPOSITION", TlaDeclKind::Proposition),
            ("COROLLARY", TlaDeclKind::Corollary),
        ] {
            if let Some(rest) = trimmed.strip_prefix(keyword) {
                let rest = rest.trim();
                // May have a name: THEOREM Name == ...
                if let Some(eq_idx) = rest.find("==") {
                    let name = rest[..eq_idx].trim().to_owned();
                    let body = rest[eq_idx + 2..].trim();
                    current_def_name = Some(if name.is_empty() {
                        format!("{keyword}_{}", module.declarations.len())
                    } else {
                        name
                    });
                    current_def_kind = *kind;
                    current_def_params = Vec::new();
                    if !body.is_empty() {
                        current_def_lines.push(body.to_owned());
                    }
                } else {
                    // Unnamed theorem: THEOREM body
                    let name = format!("{keyword}_{}", module.declarations.len());
                    current_def_name = Some(name);
                    current_def_kind = *kind;
                    current_def_params = Vec::new();
                    if !rest.is_empty() {
                        current_def_lines.push(rest.to_owned());
                    }
                }
                break;
            }
        }
        if current_def_name.is_some()
            && (trimmed.starts_with("THEOREM")
                || trimmed.starts_with("LEMMA")
                || trimmed.starts_with("PROPOSITION")
                || trimmed.starts_with("COROLLARY"))
        {
            continue;
        }

        // AXIOM
        if let Some(rest) = trimmed.strip_prefix("AXIOM") {
            let rest = rest.trim();
            if let Some(eq_idx) = rest.find("==") {
                let name = rest[..eq_idx].trim();
                let body = rest[eq_idx + 2..].trim();
                module.declarations.push(TlaDecl {
                    name: name.to_owned(),
                    kind: TlaDeclKind::Axiom,
                    params: Vec::new(),
                    body: if body.is_empty() {
                        None
                    } else {
                        Some(parse_expr(body))
                    },
                });
            } else {
                module.declarations.push(TlaDecl {
                    name: format!("AXIOM_{}", module.declarations.len()),
                    kind: TlaDeclKind::Axiom,
                    params: Vec::new(),
                    body: if rest.is_empty() {
                        None
                    } else {
                        Some(parse_expr(rest))
                    },
                });
            }
            continue;
        }

        // ASSUME / ASSUMPTION
        if trimmed.starts_with("ASSUME") {
            let keyword_len = if trimmed.starts_with("ASSUMPTION") {
                10
            } else {
                6
            };
            let rest = trimmed[keyword_len..].trim();
            if let Some(eq_idx) = rest.find("==") {
                let name = rest[..eq_idx].trim();
                let body = rest[eq_idx + 2..].trim();
                module.declarations.push(TlaDecl {
                    name: name.to_owned(),
                    kind: TlaDeclKind::Assumption,
                    params: Vec::new(),
                    body: if body.is_empty() {
                        None
                    } else {
                        Some(parse_expr(body))
                    },
                });
            } else {
                module.declarations.push(TlaDecl {
                    name: format!("ASSUME_{}", module.declarations.len()),
                    kind: TlaDeclKind::Assumption,
                    params: Vec::new(),
                    body: if rest.is_empty() {
                        None
                    } else {
                        Some(parse_expr(rest))
                    },
                });
            }
            continue;
        }

        // INSTANCE
        if let Some(rest) = trimmed.strip_prefix("INSTANCE") {
            let rest = rest.trim();
            let name = rest.split_whitespace().next().unwrap_or("unknown");
            module.declarations.push(TlaDecl {
                name: name.to_owned(),
                kind: TlaDeclKind::Instance,
                params: Vec::new(),
                body: None,
            });
            continue;
        }

        // Operator definition: Name == body  or  Name(p1, p2) == body
        if let Some(eq_idx) = trimmed.find("==") {
            let lhs = trimmed[..eq_idx].trim();
            let rhs = trimmed[eq_idx + 2..].trim();

            let (name, params) = parse_operator_lhs(lhs);
            if !name.is_empty() && is_identifier(&name) {
                current_def_name = Some(name);
                current_def_kind = TlaDeclKind::Operator;
                current_def_params = params;
                if !rhs.is_empty() {
                    current_def_lines.push(rhs.to_owned());
                }
                continue;
            }
        }

        // Continuation of a multi-line definition.
        if current_def_name.is_some() {
            current_def_lines.push(trimmed.to_owned());
            continue;
        }
    }

    // Flush any remaining definition.
    if let Some(name) = current_def_name.take() {
        let body_text = current_def_lines.join(" ");
        module.declarations.push(TlaDecl {
            name,
            kind: current_def_kind,
            params: current_def_params,
            body: if body_text.is_empty() {
                None
            } else {
                Some(parse_expr(&body_text))
            },
        });
    }

    // If we never found a module header, try to parse declarations anyway.
    if module.name.is_empty() && !module.declarations.is_empty() {
        module.name = "unnamed".to_owned();
    }

    Ok(module)
}

/// Check if a line starts a new top-level declaration.
fn starts_new_declaration(line: &str) -> bool {
    let prefixes = [
        "CONSTANT ",
        "CONSTANTS ",
        "VARIABLE ",
        "VARIABLES ",
        "THEOREM ",
        "LEMMA ",
        "PROPOSITION ",
        "COROLLARY ",
        "AXIOM ",
        "ASSUME ",
        "ASSUMPTION ",
        "INSTANCE ",
        "EXTENDS ",
    ];
    for prefix in &prefixes {
        if line.starts_with(prefix) {
            return true;
        }
    }
    // Check for `Name == ...` pattern (operator definition).
    if let Some(eq_idx) = line.find("==") {
        let lhs = line[..eq_idx].trim();
        let (name, _) = parse_operator_lhs(lhs);
        if !name.is_empty() && is_identifier(&name) {
            return true;
        }
    }
    false
}

/// Parse the LHS of an operator definition.
/// Returns (name, params).
fn parse_operator_lhs(lhs: &str) -> (String, Vec<String>) {
    let trimmed = lhs.trim();
    if let Some(paren) = trimmed.find('(') {
        let name = trimmed[..paren].trim().to_owned();
        if trimmed.ends_with(')') {
            let params_str = &trimmed[paren + 1..trimmed.len() - 1];
            let params = split_identifiers(params_str);
            return (name, params);
        }
        return (name, Vec::new());
    }
    (trimmed.to_owned(), Vec::new())
}

/// Parse a TLA+ file from disk.
///
/// # Errors
///
/// Returns `TlaParseError::Io` on read failure, or parse errors.
pub fn parse_tlaplus_file(path: &std::path::Path) -> TlaParseResult<TlaModule> {
    let text = std::fs::read_to_string(path)?;
    parse_tlaplus(&text)
}

// ════════════════════════════════════════════════════════════════════════════
// Quint parser (minimal)
// ════════════════════════════════════════════════════════════════════════════

/// Parse a Quint `.qnt` file (minimal keyword-based extraction).
///
/// Quint is an alternative TLA+ syntax. We extract declarations based
/// on keywords: `val`, `def`, `action`, `temporal`, `type`, `assume`.
pub fn parse_quint(text: &str) -> TlaParseResult<TlaModule> {
    let mut module = TlaModule {
        name: "quint".to_owned(),
        ..TlaModule::default()
    };

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }

        // Module declaration.
        if trimmed.starts_with("module ") {
            let rest = trimmed["module".len()..].trim();
            let name = rest.split_whitespace().next().unwrap_or("quint");
            module.name = name.trim_end_matches('{').trim().to_owned();
            continue;
        }

        // val / def / pure val / pure def — operator definitions.
        if trimmed.starts_with("val ")
            || trimmed.starts_with("def ")
            || trimmed.starts_with("pure val ")
            || trimmed.starts_with("pure def ")
        {
            let rest = if let Some(after_pure) = trimmed.strip_prefix("pure ") {
                after_pure
            } else {
                trimmed
            };
            // Both `val` and the fallback branch yield the same length-3
            // skip; the explicit `starts_with` check is retained so future
            // branches (`def`, `let`, …) can diverge without code shuffling.
            let keyword_len = 3;
            let after = rest[keyword_len..].trim();
            let name = after
                .split(|c: char| c == '(' || c == ':' || c == '=' || c.is_whitespace())
                .next()
                .unwrap_or("unknown")
                .to_owned();
            if !name.is_empty() {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Operator,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }

        // action — state transition.
        if trimmed.starts_with("action ") {
            let rest = trimmed["action".len()..].trim();
            let name = rest
                .split(|c: char| c == '(' || c == ':' || c == '=' || c.is_whitespace())
                .next()
                .unwrap_or("unknown")
                .to_owned();
            if !name.is_empty() {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Operator,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }

        // temporal — temporal property.
        if trimmed.starts_with("temporal ") {
            let rest = trimmed["temporal".len()..].trim();
            let name = rest
                .split(|c: char| c == '=' || c.is_whitespace())
                .next()
                .unwrap_or("unknown")
                .to_owned();
            if !name.is_empty() {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Theorem,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }

        // type — type alias.
        if trimmed.starts_with("type ") {
            let rest = trimmed["type".len()..].trim();
            let name = rest
                .split(|c: char| c == '=' || c.is_whitespace())
                .next()
                .unwrap_or("unknown")
                .to_owned();
            if !name.is_empty() {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Constant,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }

        // assume.
        if trimmed.starts_with("assume ") {
            let rest = trimmed["assume".len()..].trim();
            let name = rest
                .split(|c: char| c == '=' || c.is_whitespace())
                .next()
                .unwrap_or("unknown")
                .to_owned();
            module.declarations.push(TlaDecl {
                name,
                kind: TlaDeclKind::Assumption,
                params: Vec::new(),
                body: None,
            });
            continue;
        }

        // var — state variable.
        if trimmed.starts_with("var ") {
            let rest = trimmed["var".len()..].trim();
            let name = rest
                .split(|c: char| c == ':' || c.is_whitespace())
                .next()
                .unwrap_or("unknown")
                .to_owned();
            if !name.is_empty() {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Variable,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }

        // const — constant.
        if trimmed.starts_with("const ") {
            let rest = trimmed["const".len()..].trim();
            let name = rest
                .split(|c: char| c == ':' || c.is_whitespace())
                .next()
                .unwrap_or("unknown")
                .to_owned();
            if !name.is_empty() {
                module.declarations.push(TlaDecl {
                    name,
                    kind: TlaDeclKind::Constant,
                    params: Vec::new(),
                    body: None,
                });
            }
            continue;
        }
    }

    Ok(module)
}

/// Parse a Quint file from disk.
pub fn parse_quint_file(path: &std::path::Path) -> TlaParseResult<TlaModule> {
    let text = std::fs::read_to_string(path)?;
    parse_quint(&text)
}

// ════════════════════════════════════════════════════════════════════════════
// Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE_MODULE: &str = "\
---- MODULE Example ----
EXTENDS Naturals, Sequences

CONSTANT N
VARIABLE x, y

Init == x = 0 /\\ y = 0
Next == x' = x + 1 /\\ y' = y + 1

TypeOK == x \\in Nat /\\ y \\in Nat
Safety == x >= 0

THEOREM Init /\\ [][Next]_<<x,y>> => []Safety

====
";

    #[test]
    fn test_parse_module_header() {
        assert_eq!(
            parse_module_header("---- MODULE Example ----"),
            Some("Example".to_owned())
        );
        assert_eq!(
            parse_module_header("------- MODULE Foo -------"),
            Some("Foo".to_owned())
        );
        assert_eq!(parse_module_header("not a header"), None);
    }

    #[test]
    fn test_parse_module_footer() {
        assert!(is_module_footer("===="));
        assert!(is_module_footer("========"));
        assert!(!is_module_footer("not a footer"));
    }

    #[test]
    fn test_parse_empty() {
        let module = parse_tlaplus("").expect("should parse");
        assert!(module.is_empty());
    }

    #[test]
    fn test_parse_example_module() {
        let module = parse_tlaplus(EXAMPLE_MODULE).expect("should parse");
        assert_eq!(module.name, "Example");
        assert_eq!(module.extends, vec!["Naturals", "Sequences"]);
        assert_eq!(module.constant_count(), 1);
        assert_eq!(module.variable_count(), 2);
        assert!(module.operator_count() >= 3); // Init, Next, TypeOK, Safety
        assert_eq!(module.theorem_count(), 1);
    }

    #[test]
    fn test_parse_constants() {
        let input = "---- MODULE T ----\nCONSTANT N, M, K\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.constant_count(), 3);
    }

    #[test]
    fn test_parse_variables() {
        let input = "---- MODULE T ----\nVARIABLES a, b, c\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.variable_count(), 3);
    }

    #[test]
    fn test_parse_operator_with_params() {
        let input = "---- MODULE T ----\nMax(a, b) == IF a >= b THEN a ELSE b\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.operator_count(), 1);
        let op = &module.declarations[0];
        assert_eq!(op.name, "Max");
        assert_eq!(op.params, vec!["a", "b"]);
    }

    #[test]
    fn test_parse_axiom() {
        let input = "---- MODULE T ----\nAXIOM Ax1 == TRUE\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.axiom_count(), 1);
        assert_eq!(module.declarations[0].name, "Ax1");
    }

    #[test]
    fn test_parse_assume() {
        let input = "---- MODULE T ----\nASSUME N > 0\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.axiom_count(), 1); // axiom_count includes assumptions
    }

    #[test]
    fn test_parse_comment() {
        let input = "---- MODULE T ----\n\\* This is a comment\nCONSTANT N\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.constant_count(), 1);
    }

    #[test]
    fn test_parse_block_comment() {
        let input =
            "---- MODULE T ----\n(* block comment\n   spanning lines *)\nCONSTANT N\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.constant_count(), 1);
    }

    #[test]
    fn test_parse_theorem_named() {
        let input = "---- MODULE T ----\nTHEOREM Safety == TRUE\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.theorem_count(), 1);
        let thm = module
            .declarations
            .iter()
            .find(|d| d.is_theorem_like())
            .expect("should have theorem");
        assert_eq!(thm.name, "Safety");
    }

    #[test]
    fn test_parse_multiple_theorems() {
        let input = "\
---- MODULE T ----
THEOREM T1 == TRUE
LEMMA L1 == FALSE
PROPOSITION P1 == TRUE
COROLLARY C1 == TRUE
====
";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.theorem_count(), 4);
    }

    #[test]
    fn test_parse_instance() {
        let input = "---- MODULE T ----\nINSTANCE Naturals\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        assert_eq!(module.count_by_kind(TlaDeclKind::Instance), 1);
    }

    #[test]
    fn test_declared_names() {
        let input = "---- MODULE T ----\nCONSTANT N\nVARIABLE x\nInit == TRUE\n====\n";
        let module = parse_tlaplus(input).expect("should parse");
        let names = module.declared_names();
        assert!(names.contains(&"N"));
        assert!(names.contains(&"x"));
        assert!(names.contains(&"Init"));
    }

    #[test]
    fn test_parse_quint_basic() {
        let input = "\
module Counter {
    var count: int
    const MAX: int

    action init = { count' = 0 }
    action step = { count' = count + 1 }

    val isValid = count >= 0
    temporal safety = always(isValid)
}
";
        let module = parse_quint(input).expect("should parse");
        assert_eq!(module.name, "Counter");
        assert!(module.variable_count() >= 1);
        assert!(module.constant_count() >= 1);
    }

    #[test]
    fn test_parse_expr_bool() {
        assert_eq!(parse_expr("TRUE"), TlaExpr::BoolLit(true));
        assert_eq!(parse_expr("FALSE"), TlaExpr::BoolLit(false));
    }

    #[test]
    fn test_parse_expr_int() {
        assert_eq!(parse_expr("42"), TlaExpr::IntLit(42));
    }

    #[test]
    fn test_parse_expr_ident() {
        assert_eq!(parse_expr("foo"), TlaExpr::Ident("foo".to_owned()));
    }
}
