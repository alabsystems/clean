// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! K Framework structured parser.
//!
//! Extracts `module ... endmodule` blocks, `syntax`, `rule`, and
//! `configuration` declarations from `.k` files.

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Kind of K Framework declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum KDeclKind {
    Module,
    Syntax,
    Rule,
    Configuration,
    Import,
    Context,
    Claim,
}

/// A single extracted K Framework declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KDeclaration {
    pub name: String,
    pub kind: KDeclKind,
    /// Content string (e.g., sort name for syntax, rule body excerpt).
    pub content: Option<String>,
    pub source_file: Option<String>,
    /// Enclosing module name (if inside a module block).
    pub module_name: Option<String>,
}

/// Import statistics for a K Framework directory.
#[derive(Clone, Debug, Default)]
pub struct KImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub modules_found: usize,
    pub syntax_found: usize,
    pub rules_found: usize,
    pub configurations_found: usize,
    pub imports_found: usize,
    pub other_found: usize,
}

impl KImportStats {
    pub fn total_declarations(&self) -> usize {
        self.modules_found
            + self.syntax_found
            + self.rules_found
            + self.configurations_found
            + self.imports_found
            + self.other_found
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a single `.k` file into structured declarations.
pub fn parse_k_file(text: &str, source_file: Option<&str>) -> Vec<KDeclaration> {
    let mut decls = Vec::new();
    let src = source_file.map(String::from);
    let mut current_module: Option<String> = None;
    let mut rule_counter = 0u32;

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("module ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_owned();
            if !name.is_empty() && name != "imports" {
                current_module = Some(name.clone());
                decls.push(KDeclaration {
                    name,
                    kind: KDeclKind::Module,
                    content: None,
                    source_file: src.clone(),
                    module_name: None,
                });
            }
        } else if trimmed == "endmodule" {
            current_module = None;
        } else if let Some(rest) = trimmed.strip_prefix("syntax ") {
            let sort_name = rest.split("::=").next().unwrap_or(rest).trim().to_owned();
            let content = rest.split_once("::=").map(|(_, r)| r.trim().to_owned());
            decls.push(KDeclaration {
                name: sort_name,
                kind: KDeclKind::Syntax,
                content,
                source_file: src.clone(),
                module_name: current_module.clone(),
            });
        } else if trimmed.starts_with("rule ") || trimmed == "rule" {
            rule_counter += 1;
            let rule_content = trimmed.strip_prefix("rule ").map(|r| r.to_owned());
            decls.push(KDeclaration {
                name: format!("rule_{rule_counter}"),
                kind: KDeclKind::Rule,
                content: rule_content,
                source_file: src.clone(),
                module_name: current_module.clone(),
            });
        } else if trimmed.starts_with("configuration ") || trimmed == "configuration" {
            decls.push(KDeclaration {
                name: "configuration".to_owned(),
                kind: KDeclKind::Configuration,
                content: trimmed.strip_prefix("configuration ").map(|r| r.to_owned()),
                source_file: src.clone(),
                module_name: current_module.clone(),
            });
        } else if let Some(rest) = trimmed.strip_prefix("imports ") {
            let import_name = rest.trim().to_owned();
            if !import_name.is_empty() {
                decls.push(KDeclaration {
                    name: import_name,
                    kind: KDeclKind::Import,
                    content: None,
                    source_file: src.clone(),
                    module_name: current_module.clone(),
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("context ") {
            decls.push(KDeclaration {
                name: "context".to_owned(),
                kind: KDeclKind::Context,
                content: Some(rest.to_owned()),
                source_file: src.clone(),
                module_name: current_module.clone(),
            });
        } else if let Some(rest) = trimmed.strip_prefix("claim ") {
            decls.push(KDeclaration {
                name: "claim".to_owned(),
                kind: KDeclKind::Claim,
                content: Some(rest.to_owned()),
                source_file: src.clone(),
                module_name: current_module.clone(),
            });
        }
    }

    decls
}

/// Import all `.k` files in a directory recursively.
pub fn import_k_dir(dir: &Path) -> Result<(Vec<KDeclaration>, KImportStats), std::io::Error> {
    let mut files = Vec::new();
    collect_k_files(dir, &mut files);
    files.sort();

    let mut decls = Vec::new();
    let mut stats = KImportStats::default();

    for path in &files {
        stats.files_scanned += 1;
        match fs::read_to_string(path) {
            Ok(text) => {
                let file_str = path.to_string_lossy().to_string();
                let file_decls = parse_k_file(&text, Some(&file_str));
                for d in &file_decls {
                    match d.kind {
                        KDeclKind::Module => stats.modules_found += 1,
                        KDeclKind::Syntax => stats.syntax_found += 1,
                        KDeclKind::Rule => stats.rules_found += 1,
                        KDeclKind::Configuration => stats.configurations_found += 1,
                        KDeclKind::Import => stats.imports_found += 1,
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

fn collect_k_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_k_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "k") {
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

    const MOCK_K: &str = r#"module EVM
  imports INT
  imports BOOL

  syntax Schedule ::= "FRONTIER" | "HOMESTEAD"
  syntax InternalOp ::= #next

  configuration <k> $PGM:EVM </k>

  rule <k> ADD W0 W1 => W0 +Int W1 ... </k>
  rule <k> MUL W0 W1 => W0 *Int W1 ... </k>
endmodule
"#;

    #[test]
    fn test_parse_k_module() {
        let decls = parse_k_file(MOCK_K, Some("evm.k"));
        assert!(!decls.is_empty());

        let modules: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == KDeclKind::Module)
            .collect();
        assert_eq!(modules.len(), 1);
        assert_eq!(modules[0].name, "EVM");
    }

    #[test]
    fn test_parse_k_syntax() {
        let decls = parse_k_file(MOCK_K, None);
        let syntax: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == KDeclKind::Syntax)
            .collect();
        assert_eq!(syntax.len(), 2);
        assert_eq!(syntax[0].name, "Schedule");
        assert!(syntax[0].content.is_some());
    }

    #[test]
    fn test_parse_k_rules() {
        let decls = parse_k_file(MOCK_K, None);
        let rules: Vec<_> = decls.iter().filter(|d| d.kind == KDeclKind::Rule).collect();
        assert_eq!(rules.len(), 2);
        // Rules should have enclosing module name
        assert_eq!(rules[0].module_name.as_deref(), Some("EVM"));
    }

    #[test]
    fn test_parse_k_imports() {
        let decls = parse_k_file(MOCK_K, None);
        let imports: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == KDeclKind::Import)
            .collect();
        assert_eq!(imports.len(), 2);
        assert_eq!(imports[0].name, "INT");
        assert_eq!(imports[1].name, "BOOL");
    }

    #[test]
    fn test_parse_k_configuration() {
        let decls = parse_k_file(MOCK_K, None);
        let configs: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == KDeclKind::Configuration)
            .collect();
        assert_eq!(configs.len(), 1);
    }

    #[test]
    fn test_parse_k_empty() {
        let decls = parse_k_file("", None);
        assert!(decls.is_empty());
    }
}
