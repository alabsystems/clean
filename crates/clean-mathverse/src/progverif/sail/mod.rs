// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sail ISA description language structured parser.
//!
//! Extracts `function`, `val`, `type`, `register`, `let`, `union`, `enum`,
//! `struct`, and `bitfield` declarations from `.sail` files.

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Kind of Sail declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SailDeclKind {
    Function,
    Val,
    TypeAlias,
    Register,
    Let,
    Union,
    Enum,
    Struct,
    Bitfield,
}

/// A single extracted Sail declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SailDeclaration {
    pub name: String,
    pub kind: SailDeclKind,
    /// Type annotation or signature content (if present on the same line).
    pub type_content: Option<String>,
    pub source_file: Option<String>,
}

/// Import statistics for a Sail directory.
#[derive(Clone, Debug, Default)]
pub struct SailImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub functions_found: usize,
    pub vals_found: usize,
    pub types_found: usize,
    pub registers_found: usize,
    pub lets_found: usize,
    pub other_found: usize,
}

impl SailImportStats {
    pub fn total_declarations(&self) -> usize {
        self.functions_found
            + self.vals_found
            + self.types_found
            + self.registers_found
            + self.lets_found
            + self.other_found
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a single `.sail` file into structured declarations.
pub fn parse_sail_file(text: &str, source_file: Option<&str>) -> Vec<SailDeclaration> {
    let mut decls = Vec::new();
    let src = source_file.map(String::from);

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("/*") {
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("function ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Function,
                    type_content: extract_after_colon(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("val ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Val,
                    type_content: extract_after_colon(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("type ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::TypeAlias,
                    type_content: extract_after_equals(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("register ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Register,
                    type_content: extract_after_colon(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("let ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Let,
                    type_content: extract_after_colon(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("union ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Union,
                    type_content: None,
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("enum ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Enum,
                    type_content: None,
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("struct ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Struct,
                    type_content: None,
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("bitfield ") {
            if let Some(name) = extract_sail_name(rest) {
                decls.push(SailDeclaration {
                    name,
                    kind: SailDeclKind::Bitfield,
                    type_content: None,
                    source_file: src.clone(),
                });
            }
        }
    }

    decls
}

/// Import all `.sail` files in a directory recursively.
pub fn import_sail_dir(
    dir: &Path,
) -> Result<(Vec<SailDeclaration>, SailImportStats), std::io::Error> {
    let mut files = Vec::new();
    collect_sail_files(dir, &mut files);
    files.sort();

    let mut decls = Vec::new();
    let mut stats = SailImportStats::default();

    for path in &files {
        stats.files_scanned += 1;
        match fs::read_to_string(path) {
            Ok(text) => {
                let file_str = path.to_string_lossy().to_string();
                let file_decls = parse_sail_file(&text, Some(&file_str));
                for d in &file_decls {
                    match d.kind {
                        SailDeclKind::Function => stats.functions_found += 1,
                        SailDeclKind::Val => stats.vals_found += 1,
                        SailDeclKind::TypeAlias => stats.types_found += 1,
                        SailDeclKind::Register => stats.registers_found += 1,
                        SailDeclKind::Let => stats.lets_found += 1,
                        _ => stats.other_found += 1,
                    }
                }
                decls.extend(file_decls);
            }
            Err(_) => {
                stats.files_failed += 1;
            }
        }
    }

    Ok((decls, stats))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_sail_name(rest: &str) -> Option<String> {
    let rest = rest.trim();
    let name: String = rest
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}

fn extract_after_colon(rest: &str) -> Option<String> {
    rest.split_once(':').map(|(_, t)| t.trim().to_owned())
}

fn extract_after_equals(rest: &str) -> Option<String> {
    rest.split_once('=').map(|(_, t)| t.trim().to_owned())
}

fn collect_sail_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_sail_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "sail") {
                out.push(path);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_sail_function() {
        let text = "function clause execute (RTYPE(rs2, rs1, rd, op)) = {\n  let result = ...\n}";
        let decls = parse_sail_file(text, Some("test.sail"));
        // The keyword-line scanner also matches the inner `let` as a declaration.
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].name, "clause");
        assert_eq!(decls[0].kind, SailDeclKind::Function);
        assert_eq!(decls[1].name, "result");
        assert_eq!(decls[1].kind, SailDeclKind::Let);
    }

    #[test]
    fn test_parse_sail_val() {
        let text = "val execute : ast -> bool effect {rreg, wreg, wmem}\n";
        let decls = parse_sail_file(text, None);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "execute");
        assert_eq!(decls[0].kind, SailDeclKind::Val);
        assert!(decls[0].type_content.is_some());
    }

    #[test]
    fn test_parse_sail_type() {
        let text = "type xlen = 64\ntype regidx = bits(5)\n";
        let decls = parse_sail_file(text, None);
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].name, "xlen");
        assert_eq!(decls[0].kind, SailDeclKind::TypeAlias);
    }

    #[test]
    fn test_parse_sail_register() {
        let text = "register PC : xlenbits\n";
        let decls = parse_sail_file(text, None);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "PC");
        assert_eq!(decls[0].kind, SailDeclKind::Register);
    }

    #[test]
    fn test_parse_sail_empty() {
        let decls = parse_sail_file("", None);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_parse_sail_comments_skipped() {
        let text = "// function foo\n/* val bar */\nval baz : int\n";
        let decls = parse_sail_file(text, None);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].name, "baz");
    }
}
