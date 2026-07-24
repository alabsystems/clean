// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsers for HoTT / dependent type systems:
//! - Arend (.ard)
//! - Metamath Zero (.mm0, .mm1)
//! - Kind2 (.kind2, .kind)
//! - Rzk (.rzk)

use std::path::Path;

use super::TypeTheoryError;

/// A declaration extracted from a HoTT / dependent type source file.
#[derive(Clone, Debug)]
pub struct HottDeclaration {
    pub name: String,
    pub kind: HottDeclKind,
    pub type_signature: Option<String>,
    pub body: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub system: HottSystem,
}

/// Which HoTT system.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HottSystem {
    Arend,
    Mm0,
    Kind2,
    Rzk,
}

/// Kind of HoTT declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum HottDeclKind {
    Function,
    Lemma,
    Theorem,
    Axiom,
    Definition,
    Data,
    Class,
    Record,
    Sort,
    Postulate,
}

// ─── Arend (.ard) ───────────────────────────────────────────────────────

/// Import declarations from an Arend `.ard` file.
pub fn import_arend_file(path: &Path) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_arend_text(&text, &filename)
}

pub(crate) fn parse_arend_text(
    text: &str,
    filename: &str,
) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") || trimmed.starts_with("{-") {
            continue;
        }

        for (keyword, kind) in [
            ("\\func ", HottDeclKind::Function),
            ("\\sfunc ", HottDeclKind::Function),
            ("\\lemma ", HottDeclKind::Lemma),
            ("\\axiom ", HottDeclKind::Axiom),
            ("\\class ", HottDeclKind::Class),
            ("\\record ", HottDeclKind::Record),
            ("\\data ", HottDeclKind::Data),
            ("\\type ", HottDeclKind::Definition),
            ("\\instance ", HottDeclKind::Definition),
            ("\\open ", HottDeclKind::Definition),
            ("\\truncated \\data ", HottDeclKind::Data),
        ] {
            if let Some(rest) = trimmed.strip_prefix(keyword) {
                let name = rest
                    .split(|c: char| {
                        c.is_whitespace() || c == ':' || c == '(' || c == '{' || c == '='
                    })
                    .next()
                    .unwrap_or("")
                    .to_owned();
                let type_sig = rest.find(':').map(|i| {
                    let after = &rest[i + 1..];
                    let end = after.find(['=', '{']).unwrap_or(after.len());
                    after[..end].trim().to_owned()
                });
                if !name.is_empty() {
                    decls.push(HottDeclaration {
                        name,
                        kind,
                        type_signature: type_sig,
                        body: None,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: HottSystem::Arend,
                    });
                }
                break;
            }
        }
    }

    Ok(decls)
}

// ─── Metamath Zero (.mm0, .mm1) ─────────────────────────────────────────

/// Import declarations from a Metamath Zero `.mm0` or `.mm1` file.
pub fn import_mm0_file(path: &Path) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_mm0_text(&text, &filename)
}

pub(crate) fn parse_mm0_text(
    text: &str,
    filename: &str,
) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();
    let mut current_stmt = String::new();
    let mut stmt_start_line = 0usize;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        // Skip comments (-- to end of line).
        let trimmed = if let Some(comment_pos) = trimmed.find("--") {
            trimmed[..comment_pos].trim()
        } else {
            trimmed
        };

        if trimmed.is_empty() {
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

        for (keyword, kind) in [
            ("axiom ", HottDeclKind::Axiom),
            ("theorem ", HottDeclKind::Theorem),
            ("def ", HottDeclKind::Definition),
            ("sort ", HottDeclKind::Sort),
            ("term ", HottDeclKind::Definition),
            ("local def ", HottDeclKind::Definition),
        ] {
            if let Some(rest) = stmt.strip_prefix(keyword) {
                let name = rest
                    .split(|c: char| c.is_whitespace() || c == ':' || c == '(' || c == '{')
                    .next()
                    .unwrap_or("")
                    .to_owned();
                let type_sig = rest.find(':').map(|i| {
                    let after = &rest[i + 1..];
                    let end = after.find(['=', ':']).unwrap_or(after.len());
                    after[..end].trim().to_owned()
                });
                if !name.is_empty() {
                    decls.push(HottDeclaration {
                        name,
                        kind,
                        type_signature: type_sig,
                        body: None,
                        source_file: filename.to_owned(),
                        line_number: stmt_start_line,
                        system: HottSystem::Mm0,
                    });
                }
                break;
            }
        }
    }

    Ok(decls)
}

// ─── Kind2 (.kind2, .kind) ──────────────────────────────────────────────

/// Import declarations from a Kind2 `.kind2` or `.kind` file.
pub fn import_kind2_file(path: &Path) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_kind2_text(&text, &filename)
}

pub(crate) fn parse_kind2_text(
    text: &str,
    filename: &str,
) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }

        // Kind2 top-level: `Name : Type = body` or `Name = body`
        // Top-level definitions start at column 0, no indentation.
        if !line.starts_with(' ') && !line.starts_with('\t') {
            if let Some(colon_pos) = trimmed.find(" : ") {
                let name = trimmed[..colon_pos].trim();
                if is_valid_ident(name) {
                    let rest = &trimmed[colon_pos + 3..];
                    let (type_sig, body) = if let Some(eq_pos) = rest.find(" = ") {
                        (
                            Some(rest[..eq_pos].trim().to_owned()),
                            Some(rest[eq_pos + 3..].trim().to_owned()),
                        )
                    } else {
                        (Some(rest.trim().to_owned()), None)
                    };
                    decls.push(HottDeclaration {
                        name: name.to_owned(),
                        kind: HottDeclKind::Definition,
                        type_signature: type_sig,
                        body,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: HottSystem::Kind2,
                    });
                }
            } else if let Some(eq_pos) = trimmed.find(" = ") {
                let name = trimmed[..eq_pos].trim();
                if is_valid_ident(name) {
                    decls.push(HottDeclaration {
                        name: name.to_owned(),
                        kind: HottDeclKind::Definition,
                        type_signature: None,
                        body: Some(trimmed[eq_pos + 3..].trim().to_owned()),
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: HottSystem::Kind2,
                    });
                }
            }
        }
    }

    Ok(decls)
}

// ─── Rzk (.rzk) ────────────────────────────────────────────────────────

/// Import declarations from an Rzk `.rzk` file.
pub fn import_rzk_file(path: &Path) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_rzk_text(&text, &filename)
}

pub(crate) fn parse_rzk_text(
    text: &str,
    filename: &str,
) -> Result<Vec<HottDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }

        for (keyword, kind) in [
            ("#def ", HottDeclKind::Definition),
            ("#define ", HottDeclKind::Definition),
            ("#postulate ", HottDeclKind::Postulate),
            ("#check ", HottDeclKind::Definition),
            ("#section ", HottDeclKind::Definition),
            ("#variable ", HottDeclKind::Definition),
        ] {
            if let Some(rest) = trimmed.strip_prefix(keyword) {
                let name = rest
                    .split(|c: char| c.is_whitespace() || c == ':' || c == '(')
                    .next()
                    .unwrap_or("")
                    .to_owned();
                let type_sig = rest.find(':').map(|i| {
                    let after = &rest[i + 1..];
                    let end = after.find(":=").unwrap_or(after.len());
                    after[..end].trim().to_owned()
                });
                let body = rest.find(":=").map(|i| rest[i + 2..].trim().to_owned());
                if !name.is_empty() {
                    decls.push(HottDeclaration {
                        name,
                        kind,
                        type_signature: type_sig,
                        body,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: HottSystem::Rzk,
                    });
                }
                break;
            }
        }
    }

    Ok(decls)
}

fn is_valid_ident(s: &str) -> bool {
    !s.is_empty()
        && !s.contains(' ')
        && s.chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Arend ---

    #[test]
    fn test_arend_func() {
        let src = "\\func add (n m : Nat) : Nat\n";
        let decls = parse_arend_text(src, "test.ard").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Function);
        assert_eq!(decls[0].name, "add");
    }

    #[test]
    fn test_arend_data() {
        let src = "\\data Nat | zero | suc Nat\n";
        let decls = parse_arend_text(src, "test.ard").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Data);
    }

    #[test]
    fn test_arend_class() {
        let src = "\\class Group (A : \\Set)\n";
        let decls = parse_arend_text(src, "test.ard").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Class);
    }

    // --- mm0 ---

    #[test]
    fn test_mm0_axiom() {
        let src = "axiom mp (h1 : $ ph -> ps $) (h2 : $ ph $) : $ ps $;\n";
        let decls = parse_mm0_text(src, "test.mm0").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Axiom);
        assert_eq!(decls[0].name, "mp");
    }

    #[test]
    fn test_mm0_theorem() {
        let src = "theorem id (h : $ ph $) : $ ph $;\n";
        let decls = parse_mm0_text(src, "test.mm0").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Theorem);
    }

    #[test]
    fn test_mm0_sort() {
        let src = "sort wff;\n";
        let decls = parse_mm0_text(src, "test.mm0").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Sort);
        assert_eq!(decls[0].name, "wff");
    }

    // --- Kind2 ---

    #[test]
    fn test_kind2_def() {
        let src = "Nat : Type = #[ind] {zero} | {succ : Nat}\n";
        let decls = parse_kind2_text(src, "test.kind2").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "Nat");
        assert!(decls[0].type_signature.is_some());
    }

    // --- Rzk ---

    #[test]
    fn test_rzk_def() {
        let src = "#def id : (A : U) -> A -> A := \\A x -> x\n";
        let decls = parse_rzk_text(src, "test.rzk").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Definition);
        assert_eq!(decls[0].name, "id");
        assert!(decls[0].body.is_some());
    }

    #[test]
    fn test_rzk_postulate() {
        let src = "#postulate funext : FunExt\n";
        let decls = parse_rzk_text(src, "test.rzk").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, HottDeclKind::Postulate);
    }
}
