// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ethereum Act (.act) smart contract specification structured parser.
//!
//! Extracts `behaviour`, `creates`, `interface`, `iff`, `storage`,
//! `returns`, and `ensures` declarations from `.act` files.

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Kind of Act specification declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ActDeclKind {
    Behaviour,
    Creates,
    Interface,
    Iff,
    Storage,
    Returns,
    Ensures,
}

/// A single extracted Act declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActDeclaration {
    pub name: String,
    pub kind: ActDeclKind,
    pub content: Option<String>,
    pub source_file: Option<String>,
}

/// Import statistics for an Act directory.
#[derive(Clone, Debug, Default)]
pub struct ActImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub behaviours_found: usize,
    pub creates_found: usize,
    pub interfaces_found: usize,
    pub iffs_found: usize,
    pub storages_found: usize,
    pub other_found: usize,
}

impl ActImportStats {
    pub fn total_declarations(&self) -> usize {
        self.behaviours_found
            + self.creates_found
            + self.interfaces_found
            + self.iffs_found
            + self.storages_found
            + self.other_found
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a single `.act` file into structured declarations.
pub fn parse_act_file(text: &str, source_file: Option<&str>) -> Vec<ActDeclaration> {
    let mut decls = Vec::new();
    let src = source_file.map(String::from);

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") || trimmed.starts_with("#") {
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("behaviour ") {
            // Format: `behaviour name of Contract`
            let parts: Vec<&str> = rest.split_whitespace().collect();
            let name = parts.first().unwrap_or(&"").to_string();
            let contract = parts
                .iter()
                .position(|&w| w == "of")
                .and_then(|i| parts.get(i + 1))
                .map(|s| s.to_string());
            let content = contract.map(|c| format!("of {c}"));
            if !name.is_empty() {
                decls.push(ActDeclaration {
                    name,
                    kind: ActDeclKind::Behaviour,
                    content,
                    source_file: src.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("creates ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_owned();
            decls.push(ActDeclaration {
                name: if name.is_empty() {
                    "creates".to_owned()
                } else {
                    name
                },
                kind: ActDeclKind::Creates,
                content: Some(rest.to_owned()),
                source_file: src.clone(),
            });
        } else if let Some(rest) = trimmed.strip_prefix("interface ") {
            // Format: `interface name(args)`
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            let content = Some(rest.to_owned());
            decls.push(ActDeclaration {
                name: if name.is_empty() {
                    "interface".to_owned()
                } else {
                    name
                },
                kind: ActDeclKind::Interface,
                content,
                source_file: src.clone(),
            });
        } else if trimmed.starts_with("iff") {
            let content = trimmed.strip_prefix("iff").map(|r| r.trim().to_owned());
            decls.push(ActDeclaration {
                name: "iff".to_owned(),
                kind: ActDeclKind::Iff,
                content,
                source_file: src.clone(),
            });
        } else if trimmed.starts_with("storage") {
            let content = trimmed.strip_prefix("storage").map(|r| r.trim().to_owned());
            decls.push(ActDeclaration {
                name: "storage".to_owned(),
                kind: ActDeclKind::Storage,
                content,
                source_file: src.clone(),
            });
        } else if trimmed.starts_with("returns ") {
            decls.push(ActDeclaration {
                name: "returns".to_owned(),
                kind: ActDeclKind::Returns,
                content: Some(trimmed.strip_prefix("returns ").unwrap_or("").to_owned()),
                source_file: src.clone(),
            });
        } else if trimmed.starts_with("ensures ") {
            decls.push(ActDeclaration {
                name: "ensures".to_owned(),
                kind: ActDeclKind::Ensures,
                content: Some(trimmed.strip_prefix("ensures ").unwrap_or("").to_owned()),
                source_file: src.clone(),
            });
        }
    }

    decls
}

/// Import all `.act` files in a directory recursively.
pub fn import_act_dir(dir: &Path) -> Result<(Vec<ActDeclaration>, ActImportStats), std::io::Error> {
    let mut files = Vec::new();
    collect_act_files(dir, &mut files);
    files.sort();

    let mut decls = Vec::new();
    let mut stats = ActImportStats::default();

    for path in &files {
        stats.files_scanned += 1;
        match fs::read_to_string(path) {
            Ok(text) => {
                let file_str = path.to_string_lossy().to_string();
                let file_decls = parse_act_file(&text, Some(&file_str));
                for d in &file_decls {
                    match d.kind {
                        ActDeclKind::Behaviour => stats.behaviours_found += 1,
                        ActDeclKind::Creates => stats.creates_found += 1,
                        ActDeclKind::Interface => stats.interfaces_found += 1,
                        ActDeclKind::Iff => stats.iffs_found += 1,
                        ActDeclKind::Storage => stats.storages_found += 1,
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

fn collect_act_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_act_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "act") {
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

    const MOCK_ACT: &str = r#"behaviour transfer of ERC20
interface transfer(address to, uint256 value)

iff
  VCallValue == 0
  balances[CALLER] >= value

storage
  balances[CALLER] => balances[CALLER] - value
  balances[to] => balances[to] + value

returns true
"#;

    #[test]
    fn test_parse_act_behaviour() {
        let decls = parse_act_file(MOCK_ACT, None);
        let behaviours: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == ActDeclKind::Behaviour)
            .collect();
        assert_eq!(behaviours.len(), 1);
        assert_eq!(behaviours[0].name, "transfer");
        assert_eq!(behaviours[0].content.as_deref(), Some("of ERC20"));
    }

    #[test]
    fn test_parse_act_interface() {
        let decls = parse_act_file(MOCK_ACT, None);
        let ifaces: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == ActDeclKind::Interface)
            .collect();
        assert_eq!(ifaces.len(), 1);
        assert_eq!(ifaces[0].name, "transfer");
    }

    #[test]
    fn test_parse_act_iff() {
        let decls = parse_act_file(MOCK_ACT, None);
        let iffs: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == ActDeclKind::Iff)
            .collect();
        assert_eq!(iffs.len(), 1);
    }

    #[test]
    fn test_parse_act_storage() {
        let decls = parse_act_file(MOCK_ACT, None);
        let storages: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == ActDeclKind::Storage)
            .collect();
        assert_eq!(storages.len(), 1);
    }

    #[test]
    fn test_parse_act_returns() {
        let decls = parse_act_file(MOCK_ACT, None);
        let returns: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == ActDeclKind::Returns)
            .collect();
        assert_eq!(returns.len(), 1);
    }

    #[test]
    fn test_parse_act_empty() {
        let decls = parse_act_file("", None);
        assert!(decls.is_empty());
    }
}
