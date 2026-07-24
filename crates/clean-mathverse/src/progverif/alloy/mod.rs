// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alloy (.als) relational modeling language structured parser.
//!
//! Extracts `sig`, `fact`, `pred`, `fun`, `assert`, `check`, `run`,
//! `module`, and `open` declarations from `.als` files.

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Kind of Alloy declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AlloyDeclKind {
    Sig,
    Fact,
    Pred,
    Fun,
    Assert,
    Check,
    Run,
    Module,
    Open,
    Enum,
}

/// A single extracted Alloy declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlloyDeclaration {
    pub name: String,
    pub kind: AlloyDeclKind,
    /// Block content (text between `{` and `}` for sig/fact/pred/fun/assert).
    pub content: Option<String>,
    pub source_file: Option<String>,
}

/// Import statistics for an Alloy directory.
#[derive(Clone, Debug, Default)]
pub struct AlloyImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub sigs_found: usize,
    pub facts_found: usize,
    pub preds_found: usize,
    pub funs_found: usize,
    pub asserts_found: usize,
    pub checks_found: usize,
    pub runs_found: usize,
    pub other_found: usize,
}

impl AlloyImportStats {
    pub fn total_declarations(&self) -> usize {
        self.sigs_found
            + self.facts_found
            + self.preds_found
            + self.funs_found
            + self.asserts_found
            + self.checks_found
            + self.runs_found
            + self.other_found
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a single `.als` file into structured declarations.
///
/// Uses a line-based approach: declarations are identified by their keyword
/// at the start of a (possibly trimmed) line. Block content between braces
/// is accumulated until the closing `}`.
pub fn parse_alloy_file(text: &str, source_file: Option<&str>) -> Vec<AlloyDeclaration> {
    let mut decls = Vec::new();
    let src = source_file.map(String::from);

    // Track brace-delimited blocks for content extraction.
    let mut in_block = false;
    let mut block_content = String::new();
    let mut block_depth = 0i32;
    let mut pending_name = String::new();
    let mut pending_kind = AlloyDeclKind::Sig;

    for line in text.lines() {
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("--") {
            if in_block {
                block_content.push('\n');
                block_content.push_str(trimmed);
            }
            continue;
        }

        // If inside a block, accumulate content.
        if in_block {
            for ch in trimmed.chars() {
                if ch == '{' {
                    block_depth += 1;
                } else if ch == '}' {
                    block_depth -= 1;
                }
            }
            block_content.push('\n');
            block_content.push_str(trimmed);

            if block_depth <= 0 {
                let content = block_content.trim().to_owned();
                decls.push(AlloyDeclaration {
                    name: pending_name.clone(),
                    kind: pending_kind.clone(),
                    content: if content.is_empty() {
                        None
                    } else {
                        Some(content)
                    },
                    source_file: src.clone(),
                });
                in_block = false;
                block_content.clear();
            }
            continue;
        }

        // Module declaration.
        if let Some(rest) = trimmed.strip_prefix("module ") {
            let name = rest.trim().to_owned();
            if !name.is_empty() {
                decls.push(AlloyDeclaration {
                    name,
                    kind: AlloyDeclKind::Module,
                    content: None,
                    source_file: src.clone(),
                });
            }
            continue;
        }

        // Open (import) declaration.
        if let Some(rest) = trimmed.strip_prefix("open ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_owned();
            if !name.is_empty() {
                decls.push(AlloyDeclaration {
                    name,
                    kind: AlloyDeclKind::Open,
                    content: None,
                    source_file: src.clone(),
                });
            }
            continue;
        }

        // Check and run (no block).
        if let Some(rest) = trimmed.strip_prefix("check ") {
            let name = rest.split_whitespace().next().unwrap_or("check").to_owned();
            decls.push(AlloyDeclaration {
                name,
                kind: AlloyDeclKind::Check,
                content: None,
                source_file: src.clone(),
            });
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("run ") {
            let name = rest.split_whitespace().next().unwrap_or("run").to_owned();
            decls.push(AlloyDeclaration {
                name,
                kind: AlloyDeclKind::Run,
                content: None,
                source_file: src.clone(),
            });
            continue;
        }

        // Block-starting declarations: sig, fact, pred, fun, assert, enum.
        let (keyword, kind) = if trimmed.starts_with("sig ")
            || trimmed.starts_with("abstract sig ")
            || trimmed.starts_with("one sig ")
            || trimmed.starts_with("lone sig ")
        {
            // Extract sig name after the last "sig " occurrence.
            let sig_pos = trimmed.rfind("sig ").unwrap_or(0);
            let after_sig = &trimmed[sig_pos + 4..];
            (after_sig, AlloyDeclKind::Sig)
        } else if trimmed.starts_with("fact ") || trimmed == "fact" {
            let rest = trimmed.strip_prefix("fact").unwrap_or("").trim();
            (rest, AlloyDeclKind::Fact)
        } else if trimmed.starts_with("pred ") {
            (
                trimmed.strip_prefix("pred ").unwrap_or(""),
                AlloyDeclKind::Pred,
            )
        } else if trimmed.starts_with("fun ") {
            (
                trimmed.strip_prefix("fun ").unwrap_or(""),
                AlloyDeclKind::Fun,
            )
        } else if trimmed.starts_with("assert ") {
            (
                trimmed.strip_prefix("assert ").unwrap_or(""),
                AlloyDeclKind::Assert,
            )
        } else if trimmed.starts_with("enum ") {
            (
                trimmed.strip_prefix("enum ").unwrap_or(""),
                AlloyDeclKind::Enum,
            )
        } else {
            continue;
        };

        // Extract the name (identifier before `[`, `{`, `extends`, etc.).
        let name = keyword
            .split(|c: char| !c.is_alphanumeric() && c != '_')
            .next()
            .unwrap_or("")
            .to_owned();
        let name = if name.is_empty() {
            format!("anon_{}", kind_str(&kind))
        } else {
            name
        };

        // Check if block starts on this line.
        let open_count = trimmed.chars().filter(|c| *c == '{').count() as i32;
        let close_count = trimmed.chars().filter(|c| *c == '}').count() as i32;
        let net = open_count - close_count;

        if open_count > 0 && net <= 0 {
            // Single-line block (e.g., `sig Foo {}`).
            let block_start = trimmed.find('{').unwrap_or(trimmed.len());
            let content = trimmed[block_start..].to_owned();
            decls.push(AlloyDeclaration {
                name,
                kind,
                content: Some(content),
                source_file: src.clone(),
            });
        } else if open_count > 0 {
            // Multi-line block starting.
            in_block = true;
            block_depth = net;
            let block_start = trimmed.find('{').unwrap_or(trimmed.len());
            block_content = trimmed[block_start..].to_owned();
            pending_name = name;
            pending_kind = kind;
        } else {
            // No block (e.g., `fact Name` on its own line — block may follow later).
            // For simplicity, emit without content.
            decls.push(AlloyDeclaration {
                name,
                kind,
                content: None,
                source_file: src.clone(),
            });
        }
    }

    // Flush pending block if file ended mid-block.
    if in_block {
        let content = block_content.trim().to_owned();
        decls.push(AlloyDeclaration {
            name: pending_name,
            kind: pending_kind,
            content: if content.is_empty() {
                None
            } else {
                Some(content)
            },
            source_file: src,
        });
    }

    decls
}

/// Import all `.als` files in a directory recursively.
pub fn import_alloy_dir(
    dir: &Path,
) -> Result<(Vec<AlloyDeclaration>, AlloyImportStats), std::io::Error> {
    let mut files = Vec::new();
    collect_alloy_files(dir, &mut files);
    files.sort();

    let mut decls = Vec::new();
    let mut stats = AlloyImportStats::default();

    for path in &files {
        stats.files_scanned += 1;
        match fs::read_to_string(path) {
            Ok(text) => {
                let file_str = path.to_string_lossy().to_string();
                let file_decls = parse_alloy_file(&text, Some(&file_str));
                for d in &file_decls {
                    match d.kind {
                        AlloyDeclKind::Sig => stats.sigs_found += 1,
                        AlloyDeclKind::Fact => stats.facts_found += 1,
                        AlloyDeclKind::Pred => stats.preds_found += 1,
                        AlloyDeclKind::Fun => stats.funs_found += 1,
                        AlloyDeclKind::Assert => stats.asserts_found += 1,
                        AlloyDeclKind::Check => stats.checks_found += 1,
                        AlloyDeclKind::Run => stats.runs_found += 1,
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

fn kind_str(kind: &AlloyDeclKind) -> &'static str {
    match kind {
        AlloyDeclKind::Sig => "sig",
        AlloyDeclKind::Fact => "fact",
        AlloyDeclKind::Pred => "pred",
        AlloyDeclKind::Fun => "fun",
        AlloyDeclKind::Assert => "assert",
        AlloyDeclKind::Check => "check",
        AlloyDeclKind::Run => "run",
        AlloyDeclKind::Module => "module",
        AlloyDeclKind::Open => "open",
        AlloyDeclKind::Enum => "enum",
    }
}

fn collect_alloy_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_alloy_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "als") {
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

    const MOCK_ALLOY: &str = r#"module filesystem

open util/ordering[Time]

sig File {}
abstract sig DirEntry {
  contents: set File
}
fact noOrphans {
  all f: File | some d: DirEntry | f in d.contents
}
pred move[f: File, d1, d2: DirEntry] {
  f in d1.contents
  d2.contents' = d2.contents + f
}
fun children[d: DirEntry] : set File {
  d.contents
}
assert movePreserves {
  all f: File | some d: DirEntry | f in d.contents
}
check movePreserves for 5
run move for 3 but 2 File
"#;

    #[test]
    fn test_parse_alloy_module() {
        let decls = parse_alloy_file(MOCK_ALLOY, Some("test.als"));
        let modules: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Module)
            .collect();
        assert_eq!(modules.len(), 1);
        assert_eq!(modules[0].name, "filesystem");
    }

    #[test]
    fn test_parse_alloy_sigs() {
        let decls = parse_alloy_file(MOCK_ALLOY, None);
        let sigs: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Sig)
            .collect();
        assert_eq!(sigs.len(), 2);
    }

    #[test]
    fn test_parse_alloy_fact() {
        let decls = parse_alloy_file(MOCK_ALLOY, None);
        let facts: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Fact)
            .collect();
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].name, "noOrphans");
    }

    #[test]
    fn test_parse_alloy_pred() {
        let decls = parse_alloy_file(MOCK_ALLOY, None);
        let preds: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Pred)
            .collect();
        assert_eq!(preds.len(), 1);
        assert_eq!(preds[0].name, "move");
    }

    #[test]
    fn test_parse_alloy_fun() {
        let decls = parse_alloy_file(MOCK_ALLOY, None);
        let funs: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Fun)
            .collect();
        assert_eq!(funs.len(), 1);
        assert_eq!(funs[0].name, "children");
    }

    #[test]
    fn test_parse_alloy_assert_check_run() {
        let decls = parse_alloy_file(MOCK_ALLOY, None);
        let asserts: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Assert)
            .collect();
        let checks: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Check)
            .collect();
        let runs: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Run)
            .collect();
        assert_eq!(asserts.len(), 1);
        assert_eq!(checks.len(), 1);
        assert_eq!(runs.len(), 1);
    }

    #[test]
    fn test_parse_alloy_empty() {
        let decls = parse_alloy_file("", None);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_parse_alloy_open() {
        let decls = parse_alloy_file(MOCK_ALLOY, None);
        let opens: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == AlloyDeclKind::Open)
            .collect();
        assert_eq!(opens.len(), 1);
        assert_eq!(opens[0].name, "util/ordering[Time]");
    }
}
