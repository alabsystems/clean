// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured spec-annotation extractors for Scala verification tools.
//!
//! Covers 3 sources:
//! - **Stainless** / **Stainless-Bolts** — `require(...)`, `ensuring(...)`,
//!   `def lemma(...)`, `@opaque`, `@extern`
//! - **LISA** — `Theorem`, `Lemma`, `val name = ...`, `def name = ...`

use std::fs;
use std::path::Path;

use crate::types::SourceSystem;

use super::types::{DeclKind, StructuredDecl};

// ---------------------------------------------------------------------------
// Stainless extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Stainless / Stainless-Bolts source.
///
/// Stainless uses:
/// - `require(expr)` — preconditions
/// - `ensuring(expr)` — postconditions
/// - `def lemma(...)` — lemma functions
/// - `@opaque` / `@extern` — annotations
pub fn extract_stainless(dir: &Path, source_system: SourceSystem) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_scala_files(dir, &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();

        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // require(expr)
            if trimmed.contains("require(") {
                let content = extract_call_content(trimmed, "require").unwrap_or_default();
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::ScalaRequire,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system,
                });
            }

            // ensuring(expr) or .ensuring(expr)
            if trimmed.contains("ensuring(") || trimmed.contains(".ensuring(") {
                let content = extract_call_content(trimmed, "ensuring").unwrap_or_default();
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::ScalaEnsuring,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system,
                });
            }

            // def lemma(...)
            if trimmed.starts_with("def ") && trimmed.contains("lemma") {
                let name = extract_scala_def_name(trimmed).unwrap_or("unknown");
                decls.push(StructuredDecl {
                    name: name.to_string(),
                    kind: DeclKind::Lemma,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system,
                });
            }

            // @opaque / @extern annotations
            if trimmed.starts_with("@opaque") || trimmed.starts_with("@extern") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::StainlessAnnotation,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system,
                });
            }

            // Regular def/val declarations (not already captured as lemma)
            if (trimmed.starts_with("def ") || trimmed.starts_with("val "))
                && !trimmed.contains("lemma")
            {
                let name = if trimmed.starts_with("def ") {
                    extract_scala_def_name(trimmed)
                } else {
                    extract_scala_val_name(trimmed)
                };
                if let Some(n) = name {
                    decls.push(StructuredDecl {
                        name: n.to_string(),
                        kind: DeclKind::ValDef,
                        spec_content: trimmed.to_string(),
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system,
                    });
                }
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// LISA extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from LISA source files.
///
/// LISA uses:
/// - `Theorem` / `Lemma` — theorem declarations
/// - `val name = ...` / `def name = ...` — definitions
pub fn extract_lisa(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_scala_files(dir, &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();

        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // Theorem / Lemma declarations
            if trimmed.contains("Theorem") || trimmed.contains("Lemma") {
                // Try to extract name from patterns like:
                // val myThm = Theorem(...)
                // val myLemma: THM = Lemma(...)
                let name =
                    extract_lisa_theorem_name(trimmed).unwrap_or_else(|| "unnamed".to_string());
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Theorem,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Lisa,
                });
            }
            // val / def declarations (that aren't Theorem/Lemma)
            else if trimmed.starts_with("val ") || trimmed.starts_with("def ") {
                let name = if trimmed.starts_with("val ") {
                    extract_scala_val_name(trimmed)
                } else {
                    extract_scala_def_name(trimmed)
                };
                if let Some(n) = name {
                    decls.push(StructuredDecl {
                        name: n.to_string(),
                        kind: DeclKind::ValDef,
                        spec_content: trimmed.to_string(),
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system: SourceSystem::Lisa,
                    });
                }
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract the content of a Scala-style call like `require(expr)`.
fn extract_call_content(line: &str, fn_name: &str) -> Option<String> {
    let pattern = format!("{fn_name}(");
    let pos = line.find(&pattern)?;
    let after = &line[pos + pattern.len()..];
    let mut depth = 1i32;
    for (i, b) in after.bytes().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(after[..i].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

/// Extract `def` name from `def name(...)` or `def name[T](...) = ...`.
fn extract_scala_def_name(line: &str) -> Option<&str> {
    let trimmed = line.trim();
    if !trimmed.starts_with("def ") {
        return None;
    }
    let after = &trimmed[4..];
    let end = after
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(after.len());
    if end == 0 {
        return None;
    }
    Some(&after[..end])
}

/// Extract `val` name from `val name = ...` or `val name: Type = ...`.
fn extract_scala_val_name(line: &str) -> Option<&str> {
    let trimmed = line.trim();
    if !trimmed.starts_with("val ") {
        return None;
    }
    let after = &trimmed[4..];
    let end = after
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(after.len());
    if end == 0 {
        return None;
    }
    Some(&after[..end])
}

/// Extract theorem name from LISA-style patterns like `val myThm = Theorem(...)`.
fn extract_lisa_theorem_name(line: &str) -> Option<String> {
    let trimmed = line.trim();
    // Pattern: val <name> = Theorem/Lemma(...)
    if let Some(after) = trimmed.strip_prefix("val ") {
        let end = after
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(0);
        if end > 0 {
            return Some(after[..end].to_string());
        }
    }
    None
}

/// Recursively collect `.scala` files from a directory.
fn collect_scala_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_scala_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "scala") {
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
    fn test_extract_call_content() {
        assert_eq!(
            extract_call_content("require(x > 0)", "require"),
            Some("x > 0".to_string())
        );
        assert_eq!(
            extract_call_content("  .ensuring(res => res > 0)", "ensuring"),
            Some("res => res > 0".to_string())
        );
        assert_eq!(extract_call_content("no match here", "require"), None);
    }

    #[test]
    fn test_extract_scala_def_name() {
        assert_eq!(
            extract_scala_def_name("def foo(x: Int): Int = x"),
            Some("foo")
        );
        assert_eq!(
            extract_scala_def_name("def lemmaAdd(a: BigInt) = {"),
            Some("lemmaAdd")
        );
        assert_eq!(extract_scala_def_name("val x = 1"), None);
    }

    #[test]
    fn test_extract_scala_val_name() {
        assert_eq!(
            extract_scala_val_name("val myThm = Theorem(...)"),
            Some("myThm")
        );
        assert_eq!(extract_scala_val_name("val x: Int = 42"), Some("x"));
        assert_eq!(extract_scala_val_name("def foo() = 1"), None);
    }

    #[test]
    fn test_stainless_extraction() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("example.scala");
        std::fs::write(
            &src,
            r#"
object Example {
  def abs(x: BigInt): BigInt = {
    require(x >= -100)
    if (x < 0) -x else x
  } ensuring(res => res >= 0)

  @opaque
  def helper(): Unit = ()

  @extern
  def external(): Int = 0
}
"#,
        )
        .unwrap();

        let decls = extract_stainless(dir.path(), SourceSystem::Stainless);
        assert!(!decls.is_empty());

        let requires: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::ScalaRequire)
            .collect();
        assert_eq!(requires.len(), 1);
        assert_eq!(requires[0].spec_content, "x >= -100");

        let ensures: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::ScalaEnsuring)
            .collect();
        assert_eq!(ensures.len(), 1);

        let annots: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::StainlessAnnotation)
            .collect();
        assert_eq!(annots.len(), 2);
    }

    #[test]
    fn test_lisa_extraction() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("Proofs.scala");
        std::fs::write(
            &src,
            r#"
object Proofs {
  val myTheorem = Theorem(p => p)
  val myLemma = Lemma(q => q)
  def helper(x: Int): Boolean = true
  val constant = 42
}
"#,
        )
        .unwrap();

        let decls = extract_lisa(dir.path());
        assert!(!decls.is_empty());

        let theorems: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Theorem)
            .collect();
        assert_eq!(theorems.len(), 2);
        assert_eq!(theorems[0].name, "myTheorem");
        assert_eq!(theorems[1].name, "myLemma");

        let valdefs: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::ValDef)
            .collect();
        assert!(valdefs.len() >= 2);
    }
}
