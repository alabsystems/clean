// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured spec-annotation extractors for intermediate verification languages.
//!
//! Covers 3 sources:
//! - **Boogie** (.bpl) — `axiom expr;`, `procedure name(...)`, `function name(...): type`, `type name;`
//! - **Viper** (.vpr, .scala) — `method name(...)`, `predicate name(...)`,
//!   `function name(...): type`, `domain name { ... }`
//! - **VeriFast** (.c) — `//@` and `/*@...@*/` specification comments containing
//!   `requires`, `ensures`, `predicate`, `lemma`

use std::fs;
use std::path::Path;

use crate::types::SourceSystem;

use super::types::{DeclKind, StructuredDecl};

// ---------------------------------------------------------------------------
// Boogie extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Boogie source files (.bpl).
///
/// Boogie has a proper grammar with top-level declarations:
/// - `axiom expr;`
/// - `procedure name(params) ...`
/// - `function name(params): type`
/// - `type name;`
pub fn extract_boogie(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_files_with_ext(dir, "bpl", &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();

        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // axiom expr;
            if let Some(rest) = trimmed.strip_prefix("axiom ") {
                let content = rest.trim_end_matches(';').trim().to_string();
                decls.push(StructuredDecl {
                    name: format!("axiom_{line_num}"),
                    kind: DeclKind::Axiom,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Boogie,
                });
            }
            // procedure name(...)
            else if trimmed.starts_with("procedure ") {
                let name = extract_boogie_name(trimmed, "procedure ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Procedure,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Boogie,
                });
            }
            // function name(...): type
            else if trimmed.starts_with("function ") {
                let name = extract_boogie_name(trimmed, "function ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Function,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Boogie,
                });
            }
            // type name;
            else if trimmed.starts_with("type ") {
                let name = extract_boogie_name(trimmed, "type ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::TypeDecl,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Boogie,
                });
            }
            // requires / ensures in procedure bodies
            else if let Some(rest) = trimmed.strip_prefix("requires ") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Requires,
                    spec_content: rest.trim_end_matches(';').trim().to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Boogie,
                });
            } else if let Some(rest) = trimmed.strip_prefix("ensures ") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Ensures,
                    spec_content: rest.trim_end_matches(';').trim().to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Boogie,
                });
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// Viper extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Viper source files (.vpr, .scala).
///
/// Viper uses:
/// - `method name(...)` — verified methods
/// - `predicate name(...)` — heap predicates
/// - `function name(...): type` — mathematical functions
/// - `domain name { ... }` — abstract domains
pub fn extract_viper(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_files_with_ext(dir, "vpr", &mut files);
    collect_files_with_ext(dir, "scala", &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();

        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // method name(...)
            if trimmed.starts_with("method ") {
                let name = extract_boogie_name(trimmed, "method ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Procedure,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Viper,
                });
            }
            // predicate name(...)
            else if trimmed.starts_with("predicate ") {
                let name = extract_boogie_name(trimmed, "predicate ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Predicate,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Viper,
                });
            }
            // function name(...): type
            else if trimmed.starts_with("function ") {
                let name = extract_boogie_name(trimmed, "function ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Function,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Viper,
                });
            }
            // domain name { ... }
            else if trimmed.starts_with("domain ") {
                let name = extract_boogie_name(trimmed, "domain ");
                decls.push(StructuredDecl {
                    name,
                    kind: DeclKind::Domain,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Viper,
                });
            }
            // requires / ensures in method bodies
            else if let Some(rest) = trimmed.strip_prefix("requires ") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Requires,
                    spec_content: rest.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Viper,
                });
            } else if let Some(rest) = trimmed.strip_prefix("ensures ") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Ensures,
                    spec_content: rest.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Viper,
                });
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// VeriFast extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from VeriFast source files (.c).
///
/// VeriFast uses specification comments:
/// - `//@` single-line spec comments
/// - `/*@...@*/` multi-line spec comments
///   Inside these, look for: `requires`, `ensures`, `predicate`, `lemma`
pub fn extract_verifast(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_files_with_ext(dir, "c", &mut files);
    collect_files_with_ext(dir, "h", &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();
        let mut in_spec_block = false;

        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // Track /*@ ... @*/ blocks
            if trimmed.contains("/*@") {
                in_spec_block = true;
            }
            if trimmed.contains("@*/") {
                in_spec_block = false;
            }

            // //@  single-line spec comment
            let spec_content = if let Some(rest) = trimmed.strip_prefix("//@") {
                Some(rest.trim())
            } else if in_spec_block && !trimmed.starts_with("/*@") && !trimmed.contains("@*/") {
                Some(trimmed)
            } else if let (Some(start_idx), Some(end_idx)) =
                (trimmed.find("/*@"), trimmed.find("@*/"))
            {
                // Inline spec: /*@ content @*/
                let start = start_idx + 3;
                Some(trimmed[start..end_idx].trim())
            } else {
                None
            };

            if let Some(spec) = spec_content {
                if spec.is_empty() {
                    continue;
                }

                // Classify the spec content
                if spec.starts_with("requires") {
                    decls.push(StructuredDecl {
                        name: String::new(),
                        kind: DeclKind::Requires,
                        spec_content: spec.trim_start_matches("requires").trim().to_string(),
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system: SourceSystem::VeriFast,
                    });
                } else if spec.starts_with("ensures") {
                    decls.push(StructuredDecl {
                        name: String::new(),
                        kind: DeclKind::Ensures,
                        spec_content: spec.trim_start_matches("ensures").trim().to_string(),
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system: SourceSystem::VeriFast,
                    });
                } else if spec.starts_with("predicate") {
                    let rest = spec.trim_start_matches("predicate").trim();
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
                        kind: DeclKind::Predicate,
                        spec_content: spec.to_string(),
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system: SourceSystem::VeriFast,
                    });
                } else if spec.starts_with("lemma") {
                    let rest = spec.trim_start_matches("lemma").trim();
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
                        kind: DeclKind::Lemma,
                        spec_content: spec.to_string(),
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system: SourceSystem::VeriFast,
                    });
                } else {
                    // Generic spec comment
                    decls.push(StructuredDecl {
                        name: String::new(),
                        kind: DeclKind::SpecComment,
                        spec_content: spec.to_string(),
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system: SourceSystem::VeriFast,
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

/// Extract a name from `prefix name(...)` or `prefix name;`.
fn extract_boogie_name(line: &str, prefix: &str) -> String {
    let after = &line.trim()[prefix.len()..];
    // Skip optional attributes like {:inline}
    let after = if after.starts_with('{') {
        let close = after.find('}').map(|i| i + 1).unwrap_or(0);
        after[close..].trim()
    } else {
        after
    };
    let end = after
        .find(|c: char| !c.is_alphanumeric() && c != '_' && c != '.')
        .unwrap_or(after.len());
    if end > 0 {
        after[..end].to_string()
    } else {
        "unknown".to_string()
    }
}

/// Recursively collect files with a given extension.
fn collect_files_with_ext(dir: &Path, ext: &str, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_files_with_ext(&path, ext, out);
            } else if path.extension().is_some_and(|e| e == ext) {
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
    fn test_boogie_extraction() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("example.bpl");
        fs::write(
            &src,
            r#"
type Ref;
type Field;

axiom (forall x: int :: x >= 0 ==> x * x >= 0);

function abs(x: int): int;

procedure Increment(x: int) returns (y: int)
  requires x >= 0;
  ensures y == x + 1;
{
    y := x + 1;
}
"#,
        )
        .unwrap();

        let decls = extract_boogie(dir.path());
        assert!(!decls.is_empty());

        let types: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::TypeDecl)
            .collect();
        assert_eq!(types.len(), 2);
        assert_eq!(types[0].name, "Ref");

        let axioms: Vec<_> = decls.iter().filter(|d| d.kind == DeclKind::Axiom).collect();
        assert_eq!(axioms.len(), 1);

        let fns: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Function)
            .collect();
        assert_eq!(fns.len(), 1);
        assert_eq!(fns[0].name, "abs");

        let procs: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Procedure)
            .collect();
        assert_eq!(procs.len(), 1);
        assert_eq!(procs[0].name, "Increment");

        let requires: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Requires)
            .collect();
        assert_eq!(requires.len(), 1);

        let ensures: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Ensures)
            .collect();
        assert_eq!(ensures.len(), 1);
    }

    #[test]
    fn test_viper_extraction() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("example.vpr");
        fs::write(
            &src,
            r#"
domain Pair[A, B] {
  function fst(p: Pair[A, B]): A
  function snd(p: Pair[A, B]): B
}

predicate valid(x: Ref)

method increment(x: Int) returns (y: Int)
  requires x >= 0
  ensures y == x + 1
{
    y := x + 1
}

function abs(x: Int): Int
  ensures result >= 0
"#,
        )
        .unwrap();

        let decls = extract_viper(dir.path());
        assert!(!decls.is_empty());

        let domains: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Domain)
            .collect();
        assert_eq!(domains.len(), 1);

        let predicates: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Predicate)
            .collect();
        assert_eq!(predicates.len(), 1);
        assert_eq!(predicates[0].name, "valid");

        let methods: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Procedure)
            .collect();
        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].name, "increment");
    }

    #[test]
    fn test_verifast_extraction() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("example.c");
        fs::write(
            &src,
            r#"
//@ predicate counter(struct counter *c, int v);

/*@
lemma void counter_lemma(struct counter *c)
    requires counter(c, ?v);
    ensures counter(c, v + 1);
@*/

void increment(int *x)
//@ requires *x |-> ?v;
//@ ensures *x |-> v + 1;
{
    *x = *x + 1;
}
"#,
        )
        .unwrap();

        let decls = extract_verifast(dir.path());
        assert!(!decls.is_empty());

        let predicates: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Predicate)
            .collect();
        assert_eq!(predicates.len(), 1);
        assert_eq!(predicates[0].name, "counter");

        let lemmas: Vec<_> = decls.iter().filter(|d| d.kind == DeclKind::Lemma).collect();
        assert_eq!(lemmas.len(), 1);

        let requires: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Requires)
            .collect();
        assert!(requires.len() >= 2);

        let ensures: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Ensures)
            .collect();
        assert!(ensures.len() >= 2);
    }

    #[test]
    fn test_extract_boogie_name() {
        assert_eq!(
            extract_boogie_name("procedure Foo(x: int)", "procedure "),
            "Foo"
        );
        assert_eq!(
            extract_boogie_name("function {:inline} bar(): int", "function "),
            "bar"
        );
        assert_eq!(extract_boogie_name("type Ref;", "type "), "Ref");
    }
}
