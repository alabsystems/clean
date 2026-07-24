// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cubical type theory parsers for CubicalTT (.ctt), cooltt (.cooltt), and redtt (.red).

use std::path::Path;

use super::TypeTheoryError;

/// A declaration extracted from a cubical type theory source file.
#[derive(Clone, Debug)]
pub struct CubicalDeclaration {
    pub name: String,
    pub kind: CubicalDeclKind,
    pub type_signature: Option<String>,
    pub body: Option<String>,
    pub source_file: String,
    pub line_number: usize,
    pub system: CubicalSystem,
}

/// Which cubical system this declaration comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CubicalSystem {
    CubicalTT,
    Cooltt,
    Redtt,
}

/// Kind of cubical declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CubicalDeclKind {
    /// Definition: `name : type = body` or `def name ...`
    Definition,
    /// Data type: `data Name = ...`
    Data,
    /// Let binding: `let name = ...`
    Let,
    /// Import or module directive.
    Module,
}

/// Import declarations from a CubicalTT `.ctt` file.
pub fn import_cubicaltt_file(path: &Path) -> Result<Vec<CubicalDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_cubicaltt_text(&text, &filename)
}

pub(crate) fn parse_cubicaltt_text(
    text: &str,
    filename: &str,
) -> Result<Vec<CubicalDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }

        // `data Name = ...`
        if let Some(rest) = trimmed.strip_prefix("data ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == '=' || c == '(')
                .next()
                .unwrap_or("")
                .to_owned();
            if !name.is_empty() {
                decls.push(CubicalDeclaration {
                    name,
                    kind: CubicalDeclKind::Data,
                    type_signature: None,
                    body: rest.find('=').map(|i| rest[i + 1..].trim().to_owned()),
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: CubicalSystem::CubicalTT,
                });
            }
            continue;
        }

        // `module ...`
        if let Some(rest) = trimmed.strip_prefix("module ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_owned();
            if !name.is_empty() {
                decls.push(CubicalDeclaration {
                    name,
                    kind: CubicalDeclKind::Module,
                    type_signature: None,
                    body: None,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: CubicalSystem::CubicalTT,
                });
            }
            continue;
        }

        // `import ...` — skip.
        if trimmed.starts_with("import ") {
            continue;
        }

        // Top-level definitions: `name : type = body` or `name = body`
        // Must be at column 0 (not indented).
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
                    decls.push(CubicalDeclaration {
                        name: name.to_owned(),
                        kind: CubicalDeclKind::Definition,
                        type_signature: type_sig,
                        body,
                        source_file: filename.to_owned(),
                        line_number: line_idx + 1,
                        system: CubicalSystem::CubicalTT,
                    });
                }
            }
        }
    }

    Ok(decls)
}

/// Import declarations from a cooltt `.cooltt` file.
pub fn import_cooltt_file(path: &Path) -> Result<Vec<CubicalDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_cooltt_text(&text, &filename)
}

pub(crate) fn parse_cooltt_text(
    text: &str,
    filename: &str,
) -> Result<Vec<CubicalDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }

        // `def name : type := body` or `def name := body`
        if let Some(rest) = trimmed.strip_prefix("def ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':')
                .next()
                .unwrap_or("")
                .to_owned();
            let type_sig = if let Some(colon_pos) = rest.find(':') {
                let after_colon = &rest[colon_pos + 1..];
                if let Some(def_pos) = after_colon.find(":=") {
                    Some(after_colon[..def_pos].trim().to_owned())
                } else {
                    Some(after_colon.trim().to_owned())
                }
            } else {
                None
            };
            let body = rest.find(":=").map(|i| rest[i + 2..].trim().to_owned());
            if !name.is_empty() {
                decls.push(CubicalDeclaration {
                    name,
                    kind: CubicalDeclKind::Definition,
                    type_signature: type_sig,
                    body,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: CubicalSystem::Cooltt,
                });
            }
            continue;
        }

        // `let name ...`
        if let Some(rest) = trimmed.strip_prefix("let ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':' || c == '=')
                .next()
                .unwrap_or("")
                .to_owned();
            if !name.is_empty() {
                decls.push(CubicalDeclaration {
                    name,
                    kind: CubicalDeclKind::Let,
                    type_signature: None,
                    body: None,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: CubicalSystem::Cooltt,
                });
            }
        }
    }

    Ok(decls)
}

/// Import declarations from a redtt `.red` file.
pub fn import_redtt_file(path: &Path) -> Result<Vec<CubicalDeclaration>, TypeTheoryError> {
    let text = std::fs::read_to_string(path)?;
    let filename = path.display().to_string();
    parse_redtt_text(&text, &filename)
}

pub(crate) fn parse_redtt_text(
    text: &str,
    filename: &str,
) -> Result<Vec<CubicalDeclaration>, TypeTheoryError> {
    let mut decls = Vec::new();

    for (line_idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }

        // `def name : type = body`
        if let Some(rest) = trimmed.strip_prefix("def ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':')
                .next()
                .unwrap_or("")
                .to_owned();
            let type_sig = if let Some(colon_pos) = rest.find(':') {
                let after_colon = &rest[colon_pos + 1..];
                if let Some(eq_pos) = after_colon.find(" = ") {
                    Some(after_colon[..eq_pos].trim().to_owned())
                } else {
                    Some(after_colon.trim().to_owned())
                }
            } else {
                None
            };
            let body = rest.find(" = ").map(|i| rest[i + 3..].trim().to_owned());
            if !name.is_empty() {
                decls.push(CubicalDeclaration {
                    name,
                    kind: CubicalDeclKind::Definition,
                    type_signature: type_sig,
                    body,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: CubicalSystem::Redtt,
                });
            }
            continue;
        }

        // `let name ...`
        if let Some(rest) = trimmed.strip_prefix("let ") {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':' || c == '=')
                .next()
                .unwrap_or("")
                .to_owned();
            if !name.is_empty() {
                decls.push(CubicalDeclaration {
                    name,
                    kind: CubicalDeclKind::Let,
                    type_signature: None,
                    body: None,
                    source_file: filename.to_owned(),
                    line_number: line_idx + 1,
                    system: CubicalSystem::Redtt,
                });
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

    #[test]
    fn test_cubicaltt_data() {
        let src = "data Nat = zero | suc (n : Nat)\n";
        let decls = parse_cubicaltt_text(src, "test.ctt").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, CubicalDeclKind::Data);
        assert_eq!(decls[0].name, "Nat");
    }

    #[test]
    fn test_cubicaltt_def() {
        let src = "add : Nat -> Nat -> Nat = split\n";
        let decls = parse_cubicaltt_text(src, "test.ctt").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].kind, CubicalDeclKind::Definition);
    }

    #[test]
    fn test_cooltt_def() {
        let src = "def my_func : Nat -> Nat := fun x => x\n";
        let decls = parse_cooltt_text(src, "test.cooltt").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "my_func");
        assert_eq!(decls[0].system, CubicalSystem::Cooltt);
    }

    #[test]
    fn test_redtt_def() {
        let src = "def id : (A : type) -> A -> A = fun A x => x\n";
        let decls = parse_redtt_text(src, "test.red").unwrap();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "id");
        assert_eq!(decls[0].system, CubicalSystem::Redtt);
    }
}
