// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedukti (.dk) parser for logical framework declarations.
//!
//! Covers: dedukti, krajono, dedukti-libs (all use .dk format).
//!
//! Dedukti syntax:
//! - `name : type.` — typed declaration
//! - `name : type := body.` — definition with body
//! - `[vars] lhs --> rhs.` — rewrite rule

use std::path::Path;

use super::TypeTheoryError;

/// A declaration extracted from a Dedukti `.dk` file.
#[derive(Clone, Debug)]
pub struct DeduktiDeclaration {
    pub name: String,
    pub kind: DeduktiDeclKind,
    pub type_signature: Option<String>,
    pub body: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub module_name: Option<String>,
}

/// Kind of Dedukti declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum DeduktiDeclKind {
    /// Typed declaration: `name : type.`
    Declaration,
    /// Definition: `name : type := body.`
    Definition,
    /// Rewrite rule: `[vars] lhs --> rhs.`
    RewriteRule,
}

/// Import declarations from a Dedukti `.dk` file.
pub fn import_dedukti_file(path: &Path) -> Result<Vec<DeduktiDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_dedukti_text(&text, &filename)
}

/// Parse Dedukti text (shared by file and test entry points).
pub(crate) fn parse_dedukti_text(
    text: &str,
    filename: &str,
) -> Result<Vec<DeduktiDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();
    let mut module_name: Option<String> = None;

    // Derive module name from filename (e.g., "Nat" from "Nat.dk").
    if let Some(stem) = Path::new(filename).file_stem() {
        module_name = Some(stem.to_string_lossy().to_string());
    }

    // Accumulate multi-line statements (Dedukti statements end with `.`).
    let mut current_stmt = String::new();
    let mut stmt_start_line = 0usize;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();

        // Skip comments: `(; ... ;)` and empty lines.
        if trimmed.starts_with("(;") || trimmed.is_empty() {
            continue;
        }

        if current_stmt.is_empty() {
            stmt_start_line = line_idx + 1;
        }
        if !current_stmt.is_empty() {
            current_stmt.push(' ');
        }
        current_stmt.push_str(trimmed);

        // Check if the statement is complete (ends with `.`).
        if !trimmed.ends_with('.') {
            continue;
        }

        // Remove trailing `.`.
        let stmt = current_stmt.trim_end_matches('.').trim().to_owned();
        current_stmt.clear();

        if stmt.is_empty() {
            continue;
        }

        // Parse the statement.
        if let Some(decl) = parse_dedukti_stmt(&stmt, filename, stmt_start_line, &module_name) {
            decls.push(decl);
        }
    }

    Ok(decls)
}

fn parse_dedukti_stmt(
    stmt: &str,
    filename: &str,
    line_number: usize,
    module_name: &Option<String>,
) -> Option<DeduktiDeclaration> {
    // Rewrite rule: starts with `[` (variable context).
    if stmt.starts_with('[') {
        // Extract rule name from LHS if possible.
        if let Some(arrow_pos) = stmt.find("-->") {
            let lhs = stmt[..arrow_pos].trim();
            let rhs = stmt[arrow_pos + 3..].trim();
            // Try to extract the head symbol from LHS.
            let name = extract_head_symbol(lhs);
            return Some(DeduktiDeclaration {
                name: qualify(module_name, &name),
                kind: DeduktiDeclKind::RewriteRule,
                type_signature: Some(lhs.to_owned()),
                body: Some(rhs.to_owned()),
                source_file: filename.to_owned(),
                line_number,
                module_name: module_name.clone(),
            });
        }
        return None;
    }

    // Definition: `name : type := body` or `name := body`
    if let Some(def_pos) = stmt.find(":=") {
        let before_def = &stmt[..def_pos].trim();
        let body = stmt[def_pos + 2..].trim();
        if let Some(colon_pos) = before_def.find(':') {
            let name = before_def[..colon_pos].trim();
            let type_sig = before_def[colon_pos + 1..].trim();
            if is_valid_name(name) {
                return Some(DeduktiDeclaration {
                    name: qualify(module_name, name),
                    kind: DeduktiDeclKind::Definition,
                    type_signature: Some(type_sig.to_owned()),
                    body: Some(body.to_owned()),
                    source_file: filename.to_owned(),
                    line_number,
                    module_name: module_name.clone(),
                });
            }
        } else {
            let name = *before_def;
            if is_valid_name(name) {
                return Some(DeduktiDeclaration {
                    name: qualify(module_name, name),
                    kind: DeduktiDeclKind::Definition,
                    type_signature: None,
                    body: Some(body.to_owned()),
                    source_file: filename.to_owned(),
                    line_number,
                    module_name: module_name.clone(),
                });
            }
        }
        return None;
    }

    // Declaration: `name : type`
    if let Some(colon_pos) = stmt.find(':') {
        let name = stmt[..colon_pos].trim();
        let type_sig = stmt[colon_pos + 1..].trim();
        if is_valid_name(name) {
            return Some(DeduktiDeclaration {
                name: qualify(module_name, name),
                kind: DeduktiDeclKind::Declaration,
                type_signature: Some(type_sig.to_owned()),
                body: None,
                source_file: filename.to_owned(),
                line_number,
                module_name: module_name.clone(),
            });
        }
    }

    None
}

/// Extract the head symbol from a Dedukti LHS (after optional variable context `[...]`).
fn extract_head_symbol(lhs: &str) -> String {
    let s = if let Some(close_bracket) = lhs.find(']') {
        lhs[close_bracket + 1..].trim()
    } else {
        lhs.trim()
    };
    s.split_whitespace().next().unwrap_or("_rule").to_owned()
}

fn is_valid_name(name: &str) -> bool {
    !name.is_empty()
        && !name.contains(' ')
        && name
            .chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
}

fn qualify(module: &Option<String>, name: &str) -> String {
    match module {
        Some(m) => format!("{m}.{name}"),
        None => name.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_declaration() {
        let src = "Nat : Type.\n";
        let decls = parse_dedukti_text(src, "test.dk").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, DeduktiDeclKind::Declaration);
        assert!(decls[0].name.contains("Nat"));
        assert_eq!(decls[0].type_signature.as_deref(), Some("Type"));
    }

    #[test]
    fn test_parse_definition() {
        let src = "zero : Nat := Z.\n";
        let decls = parse_dedukti_text(src, "test.dk").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, DeduktiDeclKind::Definition);
        assert!(decls[0].body.is_some());
    }

    #[test]
    fn test_parse_rewrite_rule() {
        let src = "[n] plus Z n --> n.\n";
        let decls = parse_dedukti_text(src, "test.dk").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, DeduktiDeclKind::RewriteRule);
    }

    #[test]
    fn test_skip_comments() {
        let src = "(; comment ;)\nNat : Type.\n";
        let decls = parse_dedukti_text(src, "test.dk").unwrap();
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn test_multiline_statement() {
        let src = "plus : Nat ->\n  Nat ->\n  Nat.\n";
        let decls = parse_dedukti_text(src, "test.dk").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, DeduktiDeclKind::Declaration);
    }
}
