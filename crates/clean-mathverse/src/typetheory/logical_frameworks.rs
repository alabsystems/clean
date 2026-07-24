// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsers for logical framework systems:
//! - Abella (.thm)
//! - Beluga (.bel)
//! - Twelf (.elf)
//! - Naproche (.ftl)
//! - Minlog (.scm)

use std::path::Path;

use super::TypeTheoryError;

/// A declaration extracted from a logical framework source file.
#[derive(Clone, Debug)]
pub struct LfDeclaration {
    pub name: String,
    pub kind: LfDeclKind,
    pub type_signature: Option<String>,
    pub body: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub system: LfSystem,
}

/// Which logical framework system.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LfSystem {
    Abella,
    Beluga,
    Twelf,
    Naproche,
    Minlog,
}

/// Kind of logical framework declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum LfDeclKind {
    Theorem,
    Definition,
    Axiom,
    Type,
    Proof,
    /// LF type family or term (Twelf, Beluga).
    LfDeclaration,
    /// Inductive/recursive definition.
    Inductive,
    /// Goal or proof obligation (Minlog).
    Goal,
    /// Lemma.
    Lemma,
    /// Proposition.
    Proposition,
}

// ─── Abella (.thm) ─────────────────────────────────────────────────────

/// Import declarations from an Abella `.thm` file.
pub fn import_abella_file(path: &Path) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_abella_text(&text, &filename)
}

pub(crate) fn parse_abella_text(
    text: &str,
    filename: &str,
) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('%') {
            continue;
        }

        for (keyword, kind) in [
            ("Theorem ", LfDeclKind::Theorem),
            ("theorem ", LfDeclKind::Theorem),
            ("Lemma ", LfDeclKind::Lemma),
            ("Define ", LfDeclKind::Definition),
            ("CoDefine ", LfDeclKind::Definition),
            ("Type ", LfDeclKind::Type),
        ] {
            if let Some(rest) = trimmed.strip_prefix(keyword) {
                let name = rest
                    .split(|c: char| c.is_whitespace() || c == ':' || c == '.')
                    .next()
                    .unwrap_or("")
                    .to_owned();
                let type_sig = rest
                    .find(':')
                    .map(|i| rest[i + 1..].trim_end_matches('.').trim().to_owned());
                if !name.is_empty() {
                    decls.push(LfDeclaration {
                        name,
                        kind,
                        type_signature: type_sig,
                        body: None,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: LfSystem::Abella,
                    });
                }
                break;
            }
        }
    }

    Ok(decls)
}

// ─── Beluga (.bel) ──────────────────────────────────────────────────────

/// Import declarations from a Beluga `.bel` file.
pub fn import_beluga_file(path: &Path) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_beluga_text(&text, &filename)
}

pub(crate) fn parse_beluga_text(
    text: &str,
    filename: &str,
) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('%') {
            continue;
        }

        for (keyword, kind) in [
            ("proof ", LfDeclKind::Proof),
            ("rec ", LfDeclKind::Proof),
            ("LF ", LfDeclKind::LfDeclaration),
            ("inductive ", LfDeclKind::Inductive),
            ("stratified ", LfDeclKind::Inductive),
            ("coinductive ", LfDeclKind::Inductive),
            ("typedef ", LfDeclKind::Definition),
            ("schema ", LfDeclKind::Type),
        ] {
            if let Some(rest) = trimmed.strip_prefix(keyword) {
                let name = rest
                    .split(|c: char| c.is_whitespace() || c == ':' || c == '=')
                    .next()
                    .unwrap_or("")
                    .to_owned();
                let type_sig = rest.find(':').map(|i| {
                    let after = &rest[i + 1..];
                    let end = after.find('=').unwrap_or(after.len());
                    after[..end].trim().to_owned()
                });
                if !name.is_empty() {
                    decls.push(LfDeclaration {
                        name,
                        kind,
                        type_signature: type_sig,
                        body: None,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: LfSystem::Beluga,
                    });
                }
                break;
            }
        }
    }

    Ok(decls)
}

// ─── Twelf (.elf) ───────────────────────────────────────────────────────

/// Import declarations from a Twelf `.elf` file.
pub fn import_twelf_file(path: &Path) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_twelf_text(&text, &filename)
}

pub(crate) fn parse_twelf_text(
    text: &str,
    filename: &str,
) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();
    let mut current_stmt = String::new();
    let mut stmt_start_line = 0usize;

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        // Skip comments (start with %).
        if trimmed.starts_with('%') || trimmed.is_empty() {
            continue;
        }

        if current_stmt.is_empty() {
            stmt_start_line = line_idx + 1;
        }
        if !current_stmt.is_empty() {
            current_stmt.push(' ');
        }
        current_stmt.push_str(trimmed);

        // Twelf declarations end with `.`
        if !trimmed.ends_with('.') {
            continue;
        }

        let stmt = current_stmt.trim_end_matches('.').trim().to_owned();
        current_stmt.clear();

        if stmt.is_empty() {
            continue;
        }

        // `name : type` or `name : type = body`
        if let Some(colon_pos) = stmt.find(':') {
            let name = stmt[..colon_pos].trim();
            if is_valid_ident(name) {
                let after_colon = &stmt[colon_pos + 1..];
                let (type_sig, body, kind) = if let Some(eq_pos) = after_colon.find('=') {
                    (
                        Some(after_colon[..eq_pos].trim().to_owned()),
                        Some(after_colon[eq_pos + 1..].trim().to_owned()),
                        LfDeclKind::Definition,
                    )
                } else {
                    (
                        Some(after_colon.trim().to_owned()),
                        None,
                        LfDeclKind::LfDeclaration,
                    )
                };
                decls.push(LfDeclaration {
                    name: name.to_owned(),
                    kind,
                    type_signature: type_sig,
                    body,
                    source_file: filename.to_owned(),
                    line_number: stmt_start_line,
                    system: LfSystem::Twelf,
                });
            }
        }
    }

    Ok(decls)
}

// ─── Naproche (.ftl) ────────────────────────────────────────────────────

/// Import declarations from a Naproche `.ftl` file.
pub fn import_naproche_file(path: &Path) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_naproche_text(&text, &filename)
}

pub(crate) fn parse_naproche_text(
    text: &str,
    filename: &str,
) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        for (keyword, kind) in [
            ("Theorem", LfDeclKind::Theorem),
            ("Lemma", LfDeclKind::Lemma),
            ("Proposition", LfDeclKind::Proposition),
            ("Corollary", LfDeclKind::Theorem),
            ("Definition", LfDeclKind::Definition),
            ("Axiom", LfDeclKind::Axiom),
            ("Signature", LfDeclKind::Type),
        ] {
            if let Some(after_keyword) = trimmed.strip_prefix(keyword) {
                // Extract name: often `Theorem name.` or `Theorem.`
                let rest = after_keyword.trim();
                let name = if rest.is_empty() || rest == "." {
                    format!("{keyword}_{}", line_idx + 1)
                } else {
                    rest.split(|c: char| c == '.' || c.is_whitespace())
                        .next()
                        .unwrap_or("")
                        .to_owned()
                };
                let type_sig = if rest.contains('.') {
                    let after_dot_or_space = rest
                        .find(['.', ':'])
                        .map(|i| rest[i + 1..].trim().to_owned());
                    after_dot_or_space
                } else {
                    Some(rest.to_owned())
                };
                decls.push(LfDeclaration {
                    name: if name.is_empty() {
                        format!("{keyword}_{}", line_idx + 1)
                    } else {
                        name
                    },
                    kind,
                    type_signature: type_sig,
                    body: None,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: LfSystem::Naproche,
                });
                break;
            }
        }
    }

    Ok(decls)
}

// ─── Minlog (.scm) ─────────────────────────────────────────────────────

/// Import declarations from a Minlog `.scm` file.
pub fn import_minlog_file(path: &Path) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_minlog_text(&text, &filename)
}

pub(crate) fn parse_minlog_text(
    text: &str,
    filename: &str,
) -> Result<Vec<LfDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with(';') {
            continue;
        }

        for (prefix, kind) in [
            ("(set-goal ", LfDeclKind::Goal),
            ("(prove ", LfDeclKind::Proof),
            ("(set-totality-goal ", LfDeclKind::Goal),
            ("(add-var-name ", LfDeclKind::Type),
            ("(add-pvar-name ", LfDeclKind::Type),
            ("(add-alg ", LfDeclKind::Definition),
            ("(define ", LfDeclKind::Definition),
            ("(add-totality ", LfDeclKind::Definition),
        ] {
            if let Some(rest) = trimmed.strip_prefix(prefix) {
                // Extract the first quoted string or symbol as name.
                let name = extract_scheme_name(rest);
                let type_sig = Some(rest.trim_end_matches(')').trim().to_owned());
                decls.push(LfDeclaration {
                    name,
                    kind,
                    type_signature: type_sig,
                    body: None,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: LfSystem::Minlog,
                });
                break;
            }
        }
    }

    Ok(decls)
}

/// Extract a name from a Scheme-like s-expression argument.
fn extract_scheme_name(rest: &str) -> String {
    let trimmed = rest.trim();
    if let Some(after_quote) = trimmed.strip_prefix('"') {
        // Quoted string: "(set-goal \"name\" ...)"
        if let Some(end) = after_quote.find('"') {
            return after_quote[..end].to_owned();
        }
    }
    // Unquoted symbol
    trimmed
        .split(|c: char| c.is_whitespace() || c == ')' || c == '(')
        .next()
        .unwrap_or("_unnamed")
        .trim_matches('"')
        .to_owned()
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

    // --- Abella ---

    #[test]
    fn test_abella_theorem() {
        let src = "Theorem add_comm : forall n m, add n m = add m n.\n";
        let decls = parse_abella_text(src, "test.thm").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LfDeclKind::Theorem);
        assert_eq!(decls[0].name, "add_comm");
        assert_eq!(decls[0].system, LfSystem::Abella);
    }

    #[test]
    fn test_abella_define() {
        let src = "Define nat : type by\n  nat zero;\n  nat (suc N) := nat N.\n";
        let decls = parse_abella_text(src, "test.thm").unwrap();
        assert!(decls.iter().any(|d| d.kind == LfDeclKind::Definition));
    }

    // --- Beluga ---

    #[test]
    fn test_beluga_proof() {
        let src = "proof add_assoc : [g |- eq (add (add M N) P) (add M (add N P))] =\n";
        let decls = parse_beluga_text(src, "test.bel").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LfDeclKind::Proof);
        assert_eq!(decls[0].name, "add_assoc");
    }

    #[test]
    fn test_beluga_lf() {
        let src = "LF nat : type =\n  | zero : nat\n  | suc : nat -> nat;\n";
        let decls = parse_beluga_text(src, "test.bel").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LfDeclKind::LfDeclaration);
        assert_eq!(decls[0].name, "nat");
    }

    // --- Twelf ---

    #[test]
    fn test_twelf_decl() {
        let src = "nat : type.\nzero : nat.\nsuc : nat -> nat.\n";
        let decls = parse_twelf_text(src, "test.elf").unwrap();
        assert_eq!(decls.len(), 3);
        assert_eq!(decls[0].name, "nat");
        assert_eq!(decls[0].type_signature.as_deref(), Some("type"));
    }

    #[test]
    fn test_twelf_definition() {
        let src = "plus_zero : plus zero N N = pz.\n";
        let decls = parse_twelf_text(src, "test.elf").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LfDeclKind::Definition);
    }

    // --- Naproche ---

    #[test]
    fn test_naproche_theorem() {
        let src = "Theorem. Every natural number is non-negative.\n";
        let decls = parse_naproche_text(src, "test.ftl").unwrap();
        assert!(decls.iter().any(|d| d.kind == LfDeclKind::Theorem));
    }

    #[test]
    fn test_naproche_definition() {
        let src = "Definition. A natural number is an element of N.\n";
        let decls = parse_naproche_text(src, "test.ftl").unwrap();
        assert!(decls.iter().any(|d| d.kind == LfDeclKind::Definition));
    }

    // --- Minlog ---

    #[test]
    fn test_minlog_goal() {
        let src = "(set-goal \"all n. n+0 = n\")\n";
        let decls = parse_minlog_text(src, "test.scm").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LfDeclKind::Goal);
        assert_eq!(decls[0].name, "all n. n+0 = n");
    }

    #[test]
    fn test_minlog_add_var() {
        let src = "(add-var-name \"n\" (py \"nat\"))\n";
        let decls = parse_minlog_text(src, "test.scm").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, LfDeclKind::Type);
    }
}
