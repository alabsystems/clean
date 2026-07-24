// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lambdapi (.lp) parser for logical framework declarations.
//!
//! Lambdapi syntax:
//! - `symbol name : type;` — symbol declaration
//! - `rule lhs ↪ rhs;` or `rule lhs --> rhs;` — rewrite rule
//! - `definition name : type ≔ body;` — definition

use std::path::Path;

use super::TypeTheoryError;

/// A declaration extracted from a Lambdapi `.lp` file.
#[derive(Clone, Debug)]
pub struct LambdapiDeclaration {
    pub name: String,
    pub kind: LambdapiDeclKind,
    pub type_signature: Option<String>,
    pub body: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub modifiers: Vec<String>,
}

/// Kind of Lambdapi declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum LambdapiDeclKind {
    /// Symbol declaration: `symbol name : type;`
    Symbol,
    /// Rewrite rule: `rule lhs ↪ rhs;`
    Rule,
    /// Definition: `definition name : type ≔ body;`
    Definition,
    /// Theorem: `theorem name : type ≔ proof;`
    Theorem,
}

/// Import declarations from a Lambdapi `.lp` file.
pub fn import_lambdapi_file(path: &Path) -> Result<Vec<LambdapiDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_lambdapi_text(&text, &filename)
}

pub(crate) fn parse_lambdapi_text(
    text: &str,
    filename: &str,
) -> Result<Vec<LambdapiDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();
    let mut current_stmt = String::new();
    let mut stmt_start_line = 0usize;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();

        // Skip comments.
        if trimmed.starts_with("//") {
            continue;
        }

        if current_stmt.is_empty() {
            stmt_start_line = line_idx + 1;
        }
        if !current_stmt.is_empty() {
            current_stmt.push(' ');
        }
        current_stmt.push_str(trimmed);

        // Statements end with `;`.
        if !trimmed.ends_with(';') {
            continue;
        }

        let stmt = current_stmt.trim_end_matches(';').trim().to_owned();
        current_stmt.clear();

        if stmt.is_empty() {
            continue;
        }

        if let Some(decl) = parse_lambdapi_stmt(&stmt, filename, stmt_start_line) {
            decls.push(decl);
        }
    }

    Ok(decls)
}

fn parse_lambdapi_stmt(
    stmt: &str,
    filename: &str,
    line_number: usize,
) -> Option<LambdapiDeclaration> {
    // Collect modifiers (constant, injective, private, etc.).
    let mut modifiers = Vec::new();
    let mut rest = stmt;
    loop {
        let word = rest.split_whitespace().next()?;
        match word {
            "constant" | "injective" | "private" | "protected" | "opaque" | "commutative"
            | "associative" | "sequential" => {
                modifiers.push(word.to_owned());
                rest = rest[word.len()..].trim_start();
            }
            _ => break,
        }
    }

    // Rule: `rule ...`
    if let Some(after_rule) = rest.strip_prefix("rule ") {
        let rule_body = after_rule.trim();
        // Try to find the rewrite arrow.
        let arrow_pos = rule_body.find("↪").or_else(|| rule_body.find("-->"));
        let name = if let Some(pos) = arrow_pos {
            let lhs = rule_body[..pos].trim();
            lhs.split_whitespace().next().unwrap_or("_rule").to_owned()
        } else {
            "_rule".to_owned()
        };
        return Some(LambdapiDeclaration {
            name,
            kind: LambdapiDeclKind::Rule,
            type_signature: Some(rule_body.to_owned()),
            body: None,
            source_file: filename.to_owned(),
            line_number,
            modifiers,
        });
    }

    // Symbol: `symbol name ...`
    if let Some(after_symbol) = rest.strip_prefix("symbol ") {
        let after_kw = after_symbol.trim();
        let name = after_kw
            .split(|c: char| c.is_whitespace() || c == ':')
            .next()
            .unwrap_or("")
            .to_owned();
        let type_sig = after_kw
            .find(':')
            .map(|i| after_kw[i + 1..].trim().to_owned());
        if !name.is_empty() {
            return Some(LambdapiDeclaration {
                name,
                kind: LambdapiDeclKind::Symbol,
                type_signature: type_sig,
                body: None,
                source_file: filename.to_owned(),
                line_number,
                modifiers,
            });
        }
    }

    // Definition / theorem.
    for (keyword, kind) in [
        ("definition ", LambdapiDeclKind::Definition),
        ("theorem ", LambdapiDeclKind::Theorem),
    ] {
        if let Some(after_keyword) = rest.strip_prefix(keyword) {
            let after_kw = after_keyword.trim();
            let name = after_kw
                .split(|c: char| c.is_whitespace() || c == ':')
                .next()
                .unwrap_or("")
                .to_owned();
            // Split at ≔ or :=
            let (type_sig, body) =
                if let Some(def_pos) = after_kw.find("≔").or_else(|| after_kw.find(":=")) {
                    let before = after_kw[..def_pos].trim();
                    let after = after_kw[def_pos
                        + if after_kw[def_pos..].starts_with("≔") {
                            "≔".len()
                        } else {
                            2
                        }..]
                        .trim();
                    let ts = before.find(':').map(|i| before[i + 1..].trim().to_owned());
                    (ts, Some(after.to_owned()))
                } else {
                    let ts = after_kw
                        .find(':')
                        .map(|i| after_kw[i + 1..].trim().to_owned());
                    (ts, None)
                };
            if !name.is_empty() {
                return Some(LambdapiDeclaration {
                    name,
                    kind,
                    type_signature: type_sig,
                    body,
                    source_file: filename.to_owned(),
                    line_number,
                    modifiers,
                });
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_symbol() {
        let src = "symbol Nat : TYPE;\n";
        let decls = parse_lambdapi_text(src, "test.lp").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LambdapiDeclKind::Symbol);
        assert_eq!(decls[0].name, "Nat");
    }

    #[test]
    fn test_parse_rule() {
        let src = "rule plus zero $n ↪ $n;\n";
        let decls = parse_lambdapi_text(src, "test.lp").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LambdapiDeclKind::Rule);
    }

    #[test]
    fn test_parse_definition() {
        let src = "definition id : Nat -> Nat ≔ fun x => x;\n";
        let decls = parse_lambdapi_text(src, "test.lp").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LambdapiDeclKind::Definition);
        assert!(decls[0].body.is_some());
    }

    #[test]
    fn test_parse_with_modifiers() {
        let src = "constant symbol Prop : TYPE;\n";
        let decls = parse_lambdapi_text(src, "test.lp").unwrap();
        assert_eq!(decls.len(), 1);
        assert!(decls[0].modifiers.contains(&"constant".to_owned()));
    }
}
