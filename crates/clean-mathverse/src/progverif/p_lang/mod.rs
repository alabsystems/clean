// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! P language (.p) state-machine modeling structured parser.
//!
//! Extracts `machine`, `spec`, `event`, `state`, `fun`, and `type`
//! declarations from `.p` files.

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Kind of P language declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PDeclKind {
    Machine,
    Spec,
    Event,
    State,
    Fun,
    TypeDef,
    Enum,
    Interface,
}

/// A single extracted P language declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PDeclaration {
    pub name: String,
    pub kind: PDeclKind,
    pub content: Option<String>,
    pub source_file: Option<String>,
}

/// Import statistics for a P language directory.
#[derive(Clone, Debug, Default)]
pub struct PImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub machines_found: usize,
    pub specs_found: usize,
    pub events_found: usize,
    pub states_found: usize,
    pub funs_found: usize,
    pub other_found: usize,
}

impl PImportStats {
    pub fn total_declarations(&self) -> usize {
        self.machines_found
            + self.specs_found
            + self.events_found
            + self.states_found
            + self.funs_found
            + self.other_found
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a single `.p` file into structured declarations.
pub fn parse_p_file(text: &str, source_file: Option<&str>) -> Vec<PDeclaration> {
    let mut decls = Vec::new();
    let src = source_file.map(String::from);

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("machine ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::Machine,
                    content: extract_p_tail(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("spec ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::Spec,
                    content: extract_p_tail(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("event ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::Event,
                    content: extract_p_tail(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("state ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::State,
                    content: None,
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("fun ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::Fun,
                    content: extract_p_tail(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("type ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::TypeDef,
                    content: extract_p_tail(rest),
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("enum ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::Enum,
                    content: None,
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("interface ") {
            if let Some(name) = extract_p_name(rest) {
                decls.push(PDeclaration {
                    name,
                    kind: PDeclKind::Interface,
                    content: extract_p_tail(rest),
                    source_file: src.clone(),
                });
            }
        }
    }

    decls
}

/// Import all `.p` files in a directory recursively.
pub fn import_p_dir(dir: &Path) -> Result<(Vec<PDeclaration>, PImportStats), std::io::Error> {
    let mut files = Vec::new();
    collect_p_files(dir, &mut files);
    files.sort();

    let mut decls = Vec::new();
    let mut stats = PImportStats::default();

    for path in &files {
        stats.files_scanned += 1;
        match fs::read_to_string(path) {
            Ok(text) => {
                let file_str = path.to_string_lossy().to_string();
                let file_decls = parse_p_file(&text, Some(&file_str));
                for d in &file_decls {
                    match d.kind {
                        PDeclKind::Machine => stats.machines_found += 1,
                        PDeclKind::Spec => stats.specs_found += 1,
                        PDeclKind::Event => stats.events_found += 1,
                        PDeclKind::State => stats.states_found += 1,
                        PDeclKind::Fun => stats.funs_found += 1,
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

fn extract_p_name(rest: &str) -> Option<String> {
    let name: String = rest
        .trim()
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}

fn extract_p_tail(rest: &str) -> Option<String> {
    let name_end = rest
        .trim()
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .count();
    let tail = rest.trim()[name_end..].trim();
    if tail.is_empty() {
        None
    } else {
        Some(tail.to_owned())
    }
}

fn collect_p_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_p_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "p") {
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

    const MOCK_P: &str = r#"event eRequest : int;
event eResponse : bool;

machine Server {
  state Init {
    on eRequest do (payload: int) { ... }
  }
}

spec Safety observes eRequest, eResponse {
  state Init {
    on eRequest goto Processing;
  }
}

fun helper(x: int) : bool { ... }
type tBuffer = seq[int];
"#;

    #[test]
    fn test_parse_p_events() {
        let decls = parse_p_file(MOCK_P, None);
        let events: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == PDeclKind::Event)
            .collect();
        assert_eq!(events.len(), 2);
        assert_eq!(events[0].name, "eRequest");
        assert_eq!(events[1].name, "eResponse");
    }

    #[test]
    fn test_parse_p_machine() {
        let decls = parse_p_file(MOCK_P, None);
        let machines: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == PDeclKind::Machine)
            .collect();
        assert_eq!(machines.len(), 1);
        assert_eq!(machines[0].name, "Server");
    }

    #[test]
    fn test_parse_p_spec() {
        let decls = parse_p_file(MOCK_P, None);
        let specs: Vec<_> = decls.iter().filter(|d| d.kind == PDeclKind::Spec).collect();
        assert_eq!(specs.len(), 1);
        assert_eq!(specs[0].name, "Safety");
    }

    #[test]
    fn test_parse_p_fun() {
        let decls = parse_p_file(MOCK_P, None);
        let funs: Vec<_> = decls.iter().filter(|d| d.kind == PDeclKind::Fun).collect();
        assert_eq!(funs.len(), 1);
        assert_eq!(funs[0].name, "helper");
    }

    #[test]
    fn test_parse_p_type() {
        let decls = parse_p_file(MOCK_P, None);
        let types: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == PDeclKind::TypeDef)
            .collect();
        assert_eq!(types.len(), 1);
        assert_eq!(types[0].name, "tBuffer");
    }

    #[test]
    fn test_parse_p_empty() {
        let decls = parse_p_file("", None);
        assert!(decls.is_empty());
    }
}
