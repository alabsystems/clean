// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured spec-annotation extractor for the Move Prover.
//!
//! Move uses specification blocks and inline specs:
//! - `spec fun name(...)` — specification functions
//! - `spec module { ... }` — module-level specifications
//! - `ensures ...` / `requires ...` / `aborts_if ...` — inline specs
//! - `public fun name(...)` / `fun name(...)` — function declarations

use std::fs;
use std::path::Path;

use crate::types::SourceSystem;

use super::types::{DeclKind, StructuredDecl};

// ---------------------------------------------------------------------------
// Move Prover extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Move source files.
pub fn extract_move_prover(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_move_files(dir, &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();

        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // spec fun name(...)
            if trimmed.starts_with("spec fun ") {
                let name = extract_move_name(trimmed, "spec fun ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::SpecFn,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::MoveProver,
                });
            }
            // spec module { ... }
            else if trimmed.starts_with("spec module") {
                decls.push(StructuredDecl {
                    name: "module".to_string(),
                    kind: DeclKind::SpecModule,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::MoveProver,
                });
            }
            // spec <name> { ... } (named spec blocks for functions)
            else if trimmed.starts_with("spec ")
                && !trimmed.starts_with("spec fun ")
                && !trimmed.starts_with("spec module")
            {
                let rest = &trimmed[5..];
                let name_end = rest
                    .find(|c: char| !c.is_alphanumeric() && c != '_')
                    .unwrap_or(rest.len());
                let name = if name_end > 0 {
                    rest[..name_end].to_string()
                } else {
                    "unnamed".to_string()
                };
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::SpecFn,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::MoveProver,
                });
            }

            // ensures ...
            if let Some(rest) = trimmed.strip_prefix("ensures ") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Ensures,
                    spec_content: rest.trim_end_matches(';').to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::MoveProver,
                });
            }

            // requires ...
            if let Some(rest) = trimmed.strip_prefix("requires ") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Requires,
                    spec_content: rest.trim_end_matches(';').to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::MoveProver,
                });
            }

            // aborts_if ...
            if let Some(rest) = trimmed.strip_prefix("aborts_if ") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::AbortsIf,
                    spec_content: rest.trim_end_matches(';').to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::MoveProver,
                });
            }

            // public fun name(...) / fun name(...)
            if (trimmed.starts_with("public fun ") || trimmed.starts_with("fun "))
                && !trimmed.starts_with("spec fun ")
            {
                let prefix = if trimmed.starts_with("public fun ") {
                    "public fun "
                } else {
                    "fun "
                };
                let name = extract_move_name(trimmed, prefix);
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Function,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::MoveProver,
                });
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract a name from a line like `prefix name(...)`.
fn extract_move_name(line: &str, prefix: &str) -> String {
    let after = &line.trim()[prefix.len()..];
    let end = after
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(after.len());
    if end > 0 {
        after[..end].to_string()
    } else {
        "unknown".to_string()
    }
}

/// Recursively collect `.move` and `.rs` files from a directory.
fn collect_move_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_move_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "move" || e == "rs") {
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
    fn test_extract_move_prover() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("example.move");
        std::fs::write(
            &src,
            r#"
module 0x1::example {
    spec module {
        pragma verify = true;
    }

    spec fun spec_add(a: u64, b: u64): u64 {
        a + b
    }

    public fun transfer(from: address, to: address, amount: u64) {
        requires amount > 0;
        ensures balance(to) == old(balance(to)) + amount;
        aborts_if balance(from) < amount;
    }

    fun helper(): u64 {
        42
    }

    spec transfer {
        ensures result == true;
    }
}
"#,
        )
        .unwrap();

        let decls = extract_move_prover(dir.path());
        assert!(!decls.is_empty());

        let spec_modules: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::SpecModule)
            .collect();
        assert_eq!(spec_modules.len(), 1);

        let spec_fns: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::SpecFn)
            .collect();
        assert!(spec_fns.len() >= 2); // spec_add + spec transfer

        let requires: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Requires)
            .collect();
        assert_eq!(requires.len(), 1);
        assert!(requires[0].spec_content.contains("amount > 0"));

        let ensures: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Ensures)
            .collect();
        assert!(ensures.len() >= 2);

        let aborts: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::AbortsIf)
            .collect();
        assert_eq!(aborts.len(), 1);

        let fns: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Function)
            .collect();
        assert!(fns.len() >= 2);
    }
}
