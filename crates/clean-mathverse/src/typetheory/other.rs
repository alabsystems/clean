// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsers for other type-theory systems:
//! - Cedille (.ced)
//! - ATS2 (.sats, .dats)
//! - LaTTe (.clj)

use std::path::Path;

use super::TypeTheoryError;

/// A declaration extracted from a miscellaneous type theory source file.
#[derive(Clone, Debug)]
pub struct OtherTTDeclaration {
    pub name: String,
    pub kind: OtherTTDeclKind,
    pub type_signature: Option<String>,
    pub body: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub system: OtherTTSystem,
}

/// Which system.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OtherTTSystem {
    Cedille,
    Ats2,
    Latte,
}

/// Kind of declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum OtherTTDeclKind {
    Module,
    Definition,
    Theorem,
    Axiom,
    Type,
    Function,
    ProofFunction,
}

// ─── Cedille (.ced) ─────────────────────────────────────────────────────

/// Import declarations from a Cedille `.ced` file.
pub fn import_cedille_file(path: &Path) -> Result<Vec<OtherTTDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_cedille_text(&text, &filename)
}

pub(crate) fn parse_cedille_text(
    text: &str,
    filename: &str,
) -> Result<Vec<OtherTTDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") || trimmed.starts_with("{-") {
            continue;
        }

        // `module Name.` — module declaration.
        if let Some(rest) = trimmed.strip_prefix("module ") {
            let name = rest
                .trim_end_matches('.')
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_owned();
            if !name.is_empty() {
                decls.push(OtherTTDeclaration {
                    name,
                    kind: OtherTTDeclKind::Module,
                    type_signature: None,
                    body: None,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: OtherTTSystem::Cedille,
                });
            }
            continue;
        }

        // Top-level: `name : type = body.` or `name = body.` or `name : type.`
        // Cedille uses `◂` for type ascription sometimes, and `:` for declarations.
        if !line.starts_with(' ') && !line.starts_with('\t') {
            // Check for definition with `:=` or `=`.
            let has_def = trimmed.contains(" = ") || trimmed.contains(":=");
            let has_type = trimmed.contains(" : ") || trimmed.contains("◂");

            if has_type || has_def {
                let name = trimmed
                    .split(|c: char| c.is_whitespace() || c == ':' || c == '=' || c == '◂')
                    .next()
                    .unwrap_or("")
                    .to_owned();
                if is_valid_ident(&name) {
                    let type_sig = if let Some(colon_pos) = trimmed.find(" : ") {
                        let after = &trimmed[colon_pos + 3..];
                        let end = after.find(['=', '.']).unwrap_or(after.len());
                        Some(after[..end].trim().to_owned())
                    } else {
                        None
                    };
                    let body = trimmed
                        .find(" = ")
                        .map(|i| trimmed[i + 3..].trim_end_matches('.').trim().to_owned());
                    decls.push(OtherTTDeclaration {
                        name,
                        kind: if has_def {
                            OtherTTDeclKind::Definition
                        } else {
                            OtherTTDeclKind::Type
                        },
                        type_signature: type_sig,
                        body,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: OtherTTSystem::Cedille,
                    });
                }
            }
        }
    }

    Ok(decls)
}

// ─── ATS2 (.sats, .dats) ───────────────────────────────────────────────

/// Import declarations from an ATS2 `.sats` or `.dats` file.
pub fn import_ats2_file(path: &Path) -> Result<Vec<OtherTTDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_ats2_text(&text, &filename)
}

pub(crate) fn parse_ats2_text(
    text: &str,
    filename: &str,
) -> Result<Vec<OtherTTDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("(*") {
            continue;
        }

        for (keyword, kind) in [
            ("fun ", OtherTTDeclKind::Function),
            ("fn ", OtherTTDeclKind::Function),
            ("implement ", OtherTTDeclKind::Function),
            ("val ", OtherTTDeclKind::Definition),
            ("typedef ", OtherTTDeclKind::Type),
            ("datatype ", OtherTTDeclKind::Type),
            ("dataprop ", OtherTTDeclKind::Type),
            ("dataview ", OtherTTDeclKind::Type),
            ("datasort ", OtherTTDeclKind::Type),
            ("sortdef ", OtherTTDeclKind::Type),
            ("stadef ", OtherTTDeclKind::Type),
            ("prfun ", OtherTTDeclKind::ProofFunction),
            ("prfn ", OtherTTDeclKind::ProofFunction),
            ("praxi ", OtherTTDeclKind::Axiom),
            ("prval ", OtherTTDeclKind::ProofFunction),
            ("propdef ", OtherTTDeclKind::Type),
            ("abstype ", OtherTTDeclKind::Type),
            ("abst@ype ", OtherTTDeclKind::Type),
            ("absprop ", OtherTTDeclKind::Type),
            ("absview ", OtherTTDeclKind::Type),
        ] {
            if let Some(rest) = trimmed.strip_prefix(keyword) {
                let name = rest
                    .split(|c: char| {
                        c.is_whitespace()
                            || c == '('
                            || c == ':'
                            || c == '='
                            || c == '{'
                            || c == '<'
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
                    decls.push(OtherTTDeclaration {
                        name,
                        kind,
                        type_signature: type_sig,
                        body: None,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: OtherTTSystem::Ats2,
                    });
                }
                break;
            }
        }
    }

    Ok(decls)
}

// ─── LaTTe (.clj) ──────────────────────────────────────────────────────

/// Import declarations from a LaTTe `.clj` file.
pub fn import_latte_file(path: &Path) -> Result<Vec<OtherTTDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_latte_text(&text, &filename)
}

pub(crate) fn parse_latte_text(
    text: &str,
    filename: &str,
) -> Result<Vec<OtherTTDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with(';') {
            continue;
        }

        for (prefix, kind) in [
            ("(defthm ", OtherTTDeclKind::Theorem),
            ("(defthm\n", OtherTTDeclKind::Theorem),
            ("(definition ", OtherTTDeclKind::Definition),
            ("(defaxiom ", OtherTTDeclKind::Axiom),
            ("(deflemma ", OtherTTDeclKind::Theorem),
            ("(defimplicit ", OtherTTDeclKind::Definition),
            ("(defnotation ", OtherTTDeclKind::Definition),
        ] {
            if let Some(rest) = trimmed.strip_prefix(prefix) {
                let name = rest
                    .split(|c: char| c.is_whitespace() || c == ')')
                    .next()
                    .unwrap_or("")
                    .to_owned();
                if !name.is_empty() {
                    decls.push(OtherTTDeclaration {
                        name,
                        kind,
                        type_signature: Some(rest.to_owned()),
                        body: None,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: OtherTTSystem::Latte,
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

    // --- Cedille ---

    #[test]
    fn test_cedille_module() {
        let src = "module Nat.\n";
        let decls = parse_cedille_text(src, "test.ced").unwrap();
        assert!(decls.iter().any(|d| d.kind == OtherTTDeclKind::Module));
    }

    #[test]
    fn test_cedille_def() {
        let src = "id : Nat -> Nat = fun x. x.\n";
        let decls = parse_cedille_text(src, "test.ced").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, OtherTTDeclKind::Definition);
        assert_eq!(decls[0].name, "id");
    }

    // --- ATS2 ---

    #[test]
    fn test_ats2_fun() {
        let src = "fun add (n: int, m: int): int = n + m\n";
        let decls = parse_ats2_text(src, "test.dats").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, OtherTTDeclKind::Function);
        assert_eq!(decls[0].name, "add");
    }

    #[test]
    fn test_ats2_prfun() {
        let src = "prfun lemma_nat_pos {n:nat | n > 0} (): void\n";
        let decls = parse_ats2_text(src, "test.sats").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, OtherTTDeclKind::ProofFunction);
    }

    #[test]
    fn test_ats2_typedef() {
        let src = "typedef Nat = [n:int | n >= 0] int n\n";
        let decls = parse_ats2_text(src, "test.sats").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, OtherTTDeclKind::Type);
    }

    // --- LaTTe ---

    #[test]
    fn test_latte_defthm() {
        let src = "(defthm nat-induction\n  \"Induction on natural numbers.\"\n  ...)\n";
        let decls = parse_latte_text(src, "test.clj").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, OtherTTDeclKind::Theorem);
        assert_eq!(decls[0].name, "nat-induction");
    }

    #[test]
    fn test_latte_definition() {
        let src = "(definition nat-succ\n  \"The successor.\"\n  ...)\n";
        let decls = parse_latte_text(src, "test.clj").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, OtherTTDeclKind::Definition);
    }
}
