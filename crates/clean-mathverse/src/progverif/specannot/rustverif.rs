// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured spec-annotation extractors for Rust verification tools.
//!
//! Covers 7 tools:
//! - **Verus** — `proof fn`, `spec fn`, `broadcast proof fn`, `requires(...)`, `ensures(...)`
//! - **Creusot** — `#[ensures(...)]`, `#[requires(...)]`, `#[variant(...)]`, `#[logic]`
//! - **Kani** — `#[kani::proof]`, `#[kani::requires(...)]`, `#[kani::ensures(...)]`,
//!   `kani::assume(...)`, `kani::assert(...)`
//! - **Prusti** — `#[ensures(...)]`, `#[requires(...)]`, `#[trusted]`, `#[pure]`
//! - **Aeneas** — Standard Rust `#[test]` annotations plus `.lean` output
//! - **Hax** — `#[hax_lib::requires(...)]`, `#[hax_lib::ensures(...)]`
//! - **CreuSAT** — Creusot-style annotations on SAT solver code

use std::fs;
use std::path::Path;

use crate::types::SourceSystem;

use super::types::{DeclKind, StructuredDecl};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Extract the content inside balanced parentheses from a string starting
/// at the first `(`. Returns `None` if no balanced parens found.
fn extract_paren_content(s: &str) -> Option<&str> {
    let start = s.find('(')?;
    let mut depth = 0i32;
    let bytes = s.as_bytes();
    for (i, &b) in bytes.iter().enumerate().skip(start) {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&s[start + 1..i]);
                }
            }
            _ => {}
        }
    }
    None
}

/// Extract the function name from a line like `fn foo(...)` or `pub fn bar(...)`.
fn extract_fn_name(line: &str) -> Option<&str> {
    let trimmed = line.trim();
    // Find "fn " and take the identifier after it.
    let fn_pos = trimmed.find("fn ")?;
    let after_fn = &trimmed[fn_pos + 3..];
    let name_end = after_fn
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(after_fn.len());
    if name_end == 0 {
        return None;
    }
    Some(&after_fn[..name_end])
}

/// Extract the attribute content from `#[attr(content)]`.
fn extract_attr_content(line: &str, attr_name: &str) -> Option<String> {
    let pattern = format!("#[{attr_name}(");
    if let Some(pos) = line.find(&pattern) {
        let after = &line[pos + pattern.len()..];
        // Find matching )]
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
    }
    None
}

/// Scan lines looking for attribute + function pairs. When an attribute is
/// found on line N, the function name is extracted from subsequent lines.
fn find_fn_after_attr(lines: &[&str], attr_line_idx: usize) -> Option<String> {
    // Offset range (start = attr_line_idx + 1, end = capped at +5); a plain
    // iterator with `.take(4)` is less self-explanatory than the bounded range.
    #[allow(clippy::needless_range_loop)]
    for i in (attr_line_idx + 1)..lines.len().min(attr_line_idx + 5) {
        if let Some(name) = extract_fn_name(lines[i]) {
            return Some(name.to_string());
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Verus extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Verus source files.
///
/// Verus uses *syntax-level* spec constructs:
/// - `proof fn name(...)` — proof functions
/// - `spec fn name(...)` — specification functions
/// - `broadcast proof fn name(...)` — broadcast proof functions
/// - `requires(...)` / `ensures(...)` — inline pre/postconditions
pub fn extract_verus(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_rs_files(dir, &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();
        let lines: Vec<&str> = text.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // broadcast proof fn
            if trimmed.starts_with("broadcast proof fn ")
                || trimmed.starts_with("pub broadcast proof fn ")
            {
                let name = extract_fn_name(trimmed).unwrap_or("unknown");
                decls.push(StructuredDecl {
                    name: name.to_string(),
                    kind: DeclKind::BroadcastProofFn,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Verus,
                });
            }
            // proof fn (but not broadcast proof fn — already handled)
            else if (trimmed.starts_with("proof fn ") || trimmed.starts_with("pub proof fn "))
                && !trimmed.contains("broadcast")
            {
                let name = extract_fn_name(trimmed).unwrap_or("unknown");
                decls.push(StructuredDecl {
                    name: name.to_string(),
                    kind: DeclKind::ProofFn,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Verus,
                });
            }
            // spec fn
            else if trimmed.starts_with("spec fn ")
                || trimmed.starts_with("pub spec fn ")
                || trimmed.starts_with("pub(crate) spec fn ")
            {
                let name = extract_fn_name(trimmed).unwrap_or("unknown");
                decls.push(StructuredDecl {
                    name: name.to_string(),
                    kind: DeclKind::SpecFn,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Verus,
                });
            }
            // requires(...)
            else if trimmed.starts_with("requires") && trimmed.contains('(') {
                let content = extract_paren_content(trimmed).unwrap_or("").to_string();
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Requires,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Verus,
                });
            }
            // ensures(...)
            else if trimmed.starts_with("ensures") && trimmed.contains('(') {
                let content = extract_paren_content(trimmed).unwrap_or("").to_string();
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Ensures,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Verus,
                });
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// Creusot extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Creusot source files.
///
/// Creusot uses Rust attributes:
/// - `#[ensures(...)]` / `#[requires(...)]` / `#[variant(...)]`
/// - `#[logic]` on functions
pub fn extract_creusot(dir: &Path) -> Vec<StructuredDecl> {
    extract_rust_attr_tool(
        dir,
        SourceSystem::Creusot,
        &[
            ("ensures", DeclKind::Ensures),
            ("requires", DeclKind::Requires),
            ("variant", DeclKind::Variant),
        ],
        &[("logic", DeclKind::LogicAnnotation)],
    )
}

// ---------------------------------------------------------------------------
// Kani extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Kani source files.
///
/// Kani uses:
/// - `#[kani::proof]` — proof harness marker
/// - `#[kani::requires(...)]` / `#[kani::ensures(...)]` — contracts
/// - `kani::assume(...)` / `kani::assert(...)` — inline assumptions/assertions
pub fn extract_kani(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_rs_files(dir, &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();
        let lines: Vec<&str> = text.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // #[kani::proof]
            if trimmed.contains("#[kani::proof]") {
                let fn_name =
                    find_fn_after_attr(&lines, line_idx).unwrap_or_else(|| "unknown".to_string());
                decls.push(StructuredDecl {
                    name: fn_name,
                    kind: DeclKind::ProofHarness,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Kani,
                });
            }
            // #[kani::requires(...)]
            if let Some(content) = extract_attr_content(trimmed, "kani::requires") {
                let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                decls.push(StructuredDecl {
                    name: fn_name,
                    kind: DeclKind::Requires,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Kani,
                });
            }
            // #[kani::ensures(...)]
            if let Some(content) = extract_attr_content(trimmed, "kani::ensures") {
                let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                decls.push(StructuredDecl {
                    name: fn_name,
                    kind: DeclKind::Ensures,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Kani,
                });
            }
            // kani::assume(...)
            if let Some(idx) = trimmed.find("kani::assume(") {
                let content = extract_paren_content(&trimmed[idx..])
                    .unwrap_or("")
                    .to_string();
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Assume,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Kani,
                });
            }
            // kani::assert(...)
            if let Some(idx) = trimmed.find("kani::assert(") {
                let content = extract_paren_content(&trimmed[idx..])
                    .unwrap_or("")
                    .to_string();
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::Assert,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Kani,
                });
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// Prusti extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Prusti source files.
///
/// Prusti uses Rust attributes:
/// - `#[ensures(...)]` / `#[requires(...)]`
/// - `#[trusted]` / `#[pure]`
pub fn extract_prusti(dir: &Path) -> Vec<StructuredDecl> {
    extract_rust_attr_tool(
        dir,
        SourceSystem::Prusti,
        &[
            ("ensures", DeclKind::Ensures),
            ("requires", DeclKind::Requires),
        ],
        &[
            ("trusted", DeclKind::LogicAnnotation),
            ("pure", DeclKind::LogicAnnotation),
        ],
    )
}

// ---------------------------------------------------------------------------
// Aeneas extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Aeneas source files.
///
/// Aeneas uses standard Rust with `#[test]` annotations. Also scans for
/// `.lean` output files.
pub fn extract_aeneas(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut rs_files = Vec::new();
    collect_rs_files(dir, &mut rs_files);

    for path in &rs_files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();
        let lines: Vec<&str> = text.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // #[requires(...)] / #[ensures(...)] — Aeneas may use contract macros
            if let Some(content) = extract_attr_content(trimmed, "requires") {
                let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                decls.push(StructuredDecl {
                    name: fn_name,
                    kind: DeclKind::Requires,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Aeneas,
                });
            }
            if let Some(content) = extract_attr_content(trimmed, "ensures") {
                let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                decls.push(StructuredDecl {
                    name: fn_name,
                    kind: DeclKind::Ensures,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Aeneas,
                });
            }
            // //@ spec comments
            if let Some(rest) = trimmed.strip_prefix("//@") {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::SpecComment,
                    spec_content: rest.trim().to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Aeneas,
                });
            }
            // pub fn / fn declarations
            if (trimmed.starts_with("pub fn ") || trimmed.starts_with("fn "))
                && !trimmed.starts_with("fn main")
            {
                let name = extract_fn_name(trimmed).unwrap_or("unknown");
                decls.push(StructuredDecl {
                    name: name.to_string(),
                    kind: DeclKind::Function,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Aeneas,
                });
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// Hax extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from Hax source files.
///
/// Hax uses:
/// - `#[hax_lib::requires(...)]` / `#[hax_lib::ensures(...)]`
pub fn extract_hax(dir: &Path) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_rs_files(dir, &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();
        let lines: Vec<&str> = text.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            if let Some(content) = extract_attr_content(trimmed, "hax_lib::requires") {
                let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                decls.push(StructuredDecl {
                    name: fn_name,
                    kind: DeclKind::Requires,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Hax,
                });
            }
            if let Some(content) = extract_attr_content(trimmed, "hax_lib::ensures") {
                let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                decls.push(StructuredDecl {
                    name: fn_name,
                    kind: DeclKind::Ensures,
                    spec_content: content,
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Hax,
                });
            }
            // Also detect generic hax_lib:: usage
            if trimmed.contains("hax_lib::")
                && !trimmed.contains("requires")
                && !trimmed.contains("ensures")
            {
                decls.push(StructuredDecl {
                    name: String::new(),
                    kind: DeclKind::LogicAnnotation,
                    spec_content: trimmed.to_string(),
                    source_file: file_str.clone(),
                    source_line: Some(line_num),
                    source_system: SourceSystem::Hax,
                });
            }
        }
    }
    decls
}

// ---------------------------------------------------------------------------
// CreuSAT extractor
// ---------------------------------------------------------------------------

/// Extract structured declarations from CreuSAT source files.
///
/// CreuSAT uses Creusot-style annotations on SAT solver code:
/// - `#[requires(...)]` / `#[ensures(...)]` / `#[invariant(...)]`
pub fn extract_creusat(dir: &Path) -> Vec<StructuredDecl> {
    extract_rust_attr_tool(
        dir,
        SourceSystem::CreuSat,
        &[
            ("ensures", DeclKind::Ensures),
            ("requires", DeclKind::Requires),
            ("invariant", DeclKind::Variant), // loop invariants
        ],
        &[("logic", DeclKind::LogicAnnotation)],
    )
}

// ---------------------------------------------------------------------------
// Shared attribute-based extractor
// ---------------------------------------------------------------------------

/// Generic extractor for Rust tools that use `#[attr_name(...)]` attributes
/// and `#[bare_attr]` annotations.
fn extract_rust_attr_tool(
    dir: &Path,
    source_system: SourceSystem,
    paren_attrs: &[(&str, DeclKind)],
    bare_attrs: &[(&str, DeclKind)],
) -> Vec<StructuredDecl> {
    let mut decls = Vec::new();
    let mut files = Vec::new();
    collect_rs_files(dir, &mut files);

    for path in &files {
        let text = match fs::read_to_string(path) {
            Ok(t) => t,
            Err(_) => continue,
        };
        let file_str = path.to_string_lossy().to_string();
        let lines: Vec<&str> = text.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            let line_num = (line_idx + 1) as u32;

            // Check parenthesized attributes: #[attr_name(content)]
            for &(attr_name, kind) in paren_attrs {
                if let Some(content) = extract_attr_content(trimmed, attr_name) {
                    let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                    decls.push(StructuredDecl {
                        name: fn_name,
                        kind,
                        spec_content: content,
                        source_file: file_str.clone(),
                        source_line: Some(line_num),
                        source_system,
                    });
                }
            }

            // Check bare attributes: #[attr_name]
            for &(attr_name, kind) in bare_attrs {
                let pattern = format!("#[{attr_name}]");
                if trimmed.contains(&pattern) {
                    let fn_name = find_fn_after_attr(&lines, line_idx).unwrap_or_default();
                    decls.push(StructuredDecl {
                        name: fn_name,
                        kind,
                        spec_content: String::new(),
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
// File collection helper
// ---------------------------------------------------------------------------

fn collect_rs_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_rs_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
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
    fn test_extract_paren_content() {
        assert_eq!(extract_paren_content("requires(x > 0)"), Some("x > 0"));
        assert_eq!(
            extract_paren_content("ensures(f(x, y) == z)"),
            Some("f(x, y) == z")
        );
        assert_eq!(extract_paren_content("no_parens"), None);
        assert_eq!(extract_paren_content("nested((a, b))"), Some("(a, b)"));
    }

    #[test]
    fn test_extract_fn_name() {
        assert_eq!(extract_fn_name("fn foo(x: u32) -> bool"), Some("foo"));
        assert_eq!(extract_fn_name("pub fn bar_baz()"), Some("bar_baz"));
        assert_eq!(
            extract_fn_name("proof fn my_proof(x: int)"),
            Some("my_proof")
        );
        assert_eq!(
            extract_fn_name("spec fn spec_func() -> int"),
            Some("spec_func")
        );
        assert_eq!(extract_fn_name("no function here"), None);
    }

    #[test]
    fn test_extract_attr_content() {
        assert_eq!(
            extract_attr_content("#[requires(x > 0)]", "requires"),
            Some("x > 0".to_string())
        );
        assert_eq!(
            extract_attr_content("#[kani::ensures(result == x + 1)]", "kani::ensures"),
            Some("result == x + 1".to_string())
        );
        assert_eq!(
            extract_attr_content("#[hax_lib::requires(n < 100)]", "hax_lib::requires"),
            Some("n < 100".to_string())
        );
        assert_eq!(extract_attr_content("#[pure]", "requires"), None);
    }

    #[test]
    fn test_verus_extraction_from_temp_dir() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("example.rs");
        fs::write(
            &src,
            r#"
proof fn lemma_add_comm(x: int, y: int)
    requires(x >= 0)
    ensures(x + y == y + x)
{
}

spec fn spec_max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub broadcast proof fn lemma_broadcast()
    ensures(true)
{
}
"#,
        )
        .unwrap();

        let decls = extract_verus(dir.path());
        assert!(decls.len() >= 5);

        let proof_fns: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::ProofFn)
            .collect();
        assert_eq!(proof_fns.len(), 1);
        assert_eq!(proof_fns[0].name, "lemma_add_comm");

        let spec_fns: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::SpecFn)
            .collect();
        assert_eq!(spec_fns.len(), 1);
        assert_eq!(spec_fns[0].name, "spec_max");

        let broadcasts: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::BroadcastProofFn)
            .collect();
        assert_eq!(broadcasts.len(), 1);
        assert_eq!(broadcasts[0].name, "lemma_broadcast");

        let requires: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Requires)
            .collect();
        assert!(!requires.is_empty());

        let ensures: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Ensures)
            .collect();
        assert!(!ensures.is_empty());
    }

    #[test]
    fn test_kani_extraction_from_temp_dir() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("test.rs");
        fs::write(
            &src,
            r#"
#[kani::proof]
fn check_add() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    let result = x + 1;
    kani::assert(result > x, "should increase");
}

#[kani::requires(x < u32::MAX)]
#[kani::ensures(|result| *result == x + 1)]
fn increment(x: u32) -> u32 {
    x + 1
}
"#,
        )
        .unwrap();

        let decls = extract_kani(dir.path());
        assert!(!decls.is_empty());

        let harnesses: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::ProofHarness)
            .collect();
        assert_eq!(harnesses.len(), 1);
        assert_eq!(harnesses[0].name, "check_add");

        let assumes: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Assume)
            .collect();
        assert_eq!(assumes.len(), 1);

        let asserts: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Assert)
            .collect();
        assert_eq!(asserts.len(), 1);

        let requires: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Requires)
            .collect();
        assert_eq!(requires.len(), 1);
    }

    #[test]
    fn test_creusot_extraction_from_temp_dir() {
        let dir = tempfile::tempdir().unwrap();
        let src = dir.path().join("creusot_test.rs");
        fs::write(
            &src,
            r#"
#[requires(x > 0)]
#[ensures(result > 0)]
fn positive(x: i32) -> i32 {
    x
}

#[logic]
fn spec_helper() -> bool { true }
"#,
        )
        .unwrap();

        let decls = extract_creusot(dir.path());
        assert!(decls.len() >= 3);

        let requires: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::Requires)
            .collect();
        assert_eq!(requires.len(), 1);
        assert_eq!(requires[0].spec_content, "x > 0");

        let logic: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == DeclKind::LogicAnnotation)
            .collect();
        assert_eq!(logic.len(), 1);
    }
}
