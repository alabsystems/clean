// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SV-COMP benchmarks (.c) enhanced C parser.
//!
//! Extracts function names containing assertions (`assert()`,
//! `__VERIFIER_error()`, `__VERIFIER_assert()`), function declarations,
//! and assertion content rather than just counting lines.

use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Kind of SV-benchmark declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SvDeclKind {
    /// A function definition (extracted from `type name(` patterns).
    Function,
    /// An `assert(...)` call with its assertion content.
    Assert,
    /// A `__VERIFIER_error()` call (reachability check).
    VerifierError,
    /// A `__VERIFIER_assert(...)` call with its content.
    VerifierAssert,
    /// A `__VERIFIER_nondet_*()` nondeterministic input.
    VerifierNondet,
}

/// A single extracted SV-benchmark declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SvDeclaration {
    pub name: String,
    pub kind: SvDeclKind,
    /// Content of the assertion (the argument), or function signature.
    pub content: Option<String>,
    pub source_file: Option<String>,
    /// Enclosing function name (for assertions within a function).
    pub enclosing_function: Option<String>,
}

/// Import statistics for an SV-benchmarks directory.
#[derive(Clone, Debug, Default)]
pub struct SvImportStats {
    pub files_scanned: usize,
    pub files_failed: usize,
    pub functions_found: usize,
    pub asserts_found: usize,
    pub verifier_errors_found: usize,
    pub verifier_asserts_found: usize,
    pub verifier_nondets_found: usize,
}

impl SvImportStats {
    pub fn total_declarations(&self) -> usize {
        self.functions_found
            + self.asserts_found
            + self.verifier_errors_found
            + self.verifier_asserts_found
            + self.verifier_nondets_found
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a single `.c` file into structured SV-benchmark declarations.
pub fn parse_sv_file(text: &str, source_file: Option<&str>) -> Vec<SvDeclaration> {
    let mut decls = Vec::new();
    let src = source_file.map(String::from);
    let mut current_function: Option<String> = None;
    let mut brace_depth = 0i32;

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty()
            || trimmed.starts_with("//")
            || trimmed.starts_with("/*")
            || trimmed.starts_with("*")
            || trimmed.starts_with("#")
        {
            // Track braces even in skipped lines for scope tracking.
            for ch in trimmed.chars() {
                if ch == '{' {
                    brace_depth += 1;
                } else if ch == '}' {
                    brace_depth -= 1;
                    if brace_depth <= 0 {
                        current_function = None;
                        brace_depth = 0;
                    }
                }
            }
            continue;
        }

        // Track brace depth for function scope.
        let open_braces = trimmed.chars().filter(|c| *c == '{').count() as i32;
        let close_braces = trimmed.chars().filter(|c| *c == '}').count() as i32;

        // Detect function definitions: `type name(` at brace depth 0.
        if brace_depth == 0
            && trimmed.contains('(')
            && !trimmed.starts_with("if ")
            && !trimmed.starts_with("while ")
            && !trimmed.starts_with("for ")
            && !trimmed.starts_with("switch ")
            && !trimmed.starts_with("return ")
            && !trimmed.starts_with("typedef ")
        {
            if let Some(func_name) = extract_c_function_name(trimmed) {
                current_function = Some(func_name.clone());
                decls.push(SvDeclaration {
                    name: func_name,
                    kind: SvDeclKind::Function,
                    content: Some(trimmed.to_owned()),
                    source_file: src.clone(),
                    enclosing_function: None,
                });
            }
        }

        // Extract assertions (but not __VERIFIER_assert which is handled separately).
        if let Some(content) = extract_standalone_call_arg(trimmed, "assert(") {
            decls.push(SvDeclaration {
                name: "assert".to_owned(),
                kind: SvDeclKind::Assert,
                content: Some(content),
                source_file: src.clone(),
                enclosing_function: current_function.clone(),
            });
        }
        if trimmed.contains("__VERIFIER_error()") || trimmed.contains("__VERIFIER_error ()") {
            decls.push(SvDeclaration {
                name: "__VERIFIER_error".to_owned(),
                kind: SvDeclKind::VerifierError,
                content: None,
                source_file: src.clone(),
                enclosing_function: current_function.clone(),
            });
        }
        if let Some(content) = extract_call_arg(trimmed, "__VERIFIER_assert(") {
            decls.push(SvDeclaration {
                name: "__VERIFIER_assert".to_owned(),
                kind: SvDeclKind::VerifierAssert,
                content: Some(content),
                source_file: src.clone(),
                enclosing_function: current_function.clone(),
            });
        }
        if trimmed.contains("__VERIFIER_nondet_") {
            // Extract the nondet variant name.
            if let Some(pos) = trimmed.find("__VERIFIER_nondet_") {
                let rest = &trimmed[pos..];
                let name: String = rest
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                decls.push(SvDeclaration {
                    name,
                    kind: SvDeclKind::VerifierNondet,
                    content: None,
                    source_file: src.clone(),
                    enclosing_function: current_function.clone(),
                });
            }
        }

        // Update brace depth.
        brace_depth += open_braces - close_braces;
        if brace_depth <= 0 {
            current_function = None;
            brace_depth = 0;
        }
    }

    decls
}

/// Import all `.c` files in a directory recursively (SV-benchmark style).
pub fn import_sv_dir(dir: &Path) -> Result<(Vec<SvDeclaration>, SvImportStats), std::io::Error> {
    let mut files = Vec::new();
    collect_c_files(dir, &mut files);
    files.sort();

    let mut decls = Vec::new();
    let mut stats = SvImportStats::default();

    for path in &files {
        stats.files_scanned += 1;
        match fs::read_to_string(path) {
            Ok(text) => {
                let file_str = path.to_string_lossy().to_string();
                let file_decls = parse_sv_file(&text, Some(&file_str));
                for d in &file_decls {
                    match d.kind {
                        SvDeclKind::Function => stats.functions_found += 1,
                        SvDeclKind::Assert => stats.asserts_found += 1,
                        SvDeclKind::VerifierError => stats.verifier_errors_found += 1,
                        SvDeclKind::VerifierAssert => stats.verifier_asserts_found += 1,
                        SvDeclKind::VerifierNondet => stats.verifier_nondets_found += 1,
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

/// Extract a C function name from a line like `int main(void) {`.
fn extract_c_function_name(line: &str) -> Option<String> {
    let paren_pos = line.find('(')?;
    let before_paren = line[..paren_pos].trim();
    // The function name is the last identifier before `(`.
    let name: String = before_paren
        .chars()
        .rev()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect::<String>()
        .chars()
        .rev()
        .collect();
    if name.is_empty()
        || name == "if"
        || name == "while"
        || name == "for"
        || name == "switch"
        || name == "return"
        || name == "sizeof"
    {
        None
    } else {
        Some(name)
    }
}

/// Extract the argument of a function call like `assert(x > 0)`.
fn extract_call_arg(line: &str, call_prefix: &str) -> Option<String> {
    let pos = line.find(call_prefix)?;
    let after = &line[pos + call_prefix.len()..];
    // Find matching closing paren (simple: first `)` — works for single-line assertions).
    let end = after.find(')')?;
    let content = after[..end].trim().to_owned();
    Some(content)
}

/// Extract the argument of a standalone function call, ensuring the call name
/// is not preceded by an alphanumeric or underscore character. This prevents
/// matching `assert(` inside `__VERIFIER_assert(`.
fn extract_standalone_call_arg(line: &str, call_prefix: &str) -> Option<String> {
    let mut search_from = 0;
    while let Some(rel_pos) = line[search_from..].find(call_prefix) {
        let pos = search_from + rel_pos;
        // Check that the character before the match is not alphanumeric or underscore.
        if pos > 0 {
            let prev = line.as_bytes()[pos - 1];
            if prev.is_ascii_alphanumeric() || prev == b'_' {
                search_from = pos + 1;
                continue;
            }
        }
        let after = &line[pos + call_prefix.len()..];
        let end = after.find(')')?;
        let content = after[..end].trim().to_owned();
        return Some(content);
    }
    None
}

fn collect_c_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                collect_c_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "c") {
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

    const MOCK_SV: &str = r#"#include <assert.h>
extern int __VERIFIER_nondet_int(void);

int main() {
    int x = __VERIFIER_nondet_int();
    if (x > 0) {
        assert(x > 0);
        __VERIFIER_assert(x >= 1);
    } else {
        __VERIFIER_error();
    }
    return 0;
}
"#;

    #[test]
    fn test_parse_sv_function() {
        let decls = parse_sv_file(MOCK_SV, None);
        let fns: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == SvDeclKind::Function)
            .collect();
        assert!(!fns.is_empty());
        assert!(fns.iter().any(|d| d.name == "main"));
    }

    #[test]
    fn test_parse_sv_assert() {
        let decls = parse_sv_file(MOCK_SV, None);
        let asserts: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == SvDeclKind::Assert)
            .collect();
        assert_eq!(asserts.len(), 1);
        assert_eq!(asserts[0].content.as_deref(), Some("x > 0"));
        assert_eq!(asserts[0].enclosing_function.as_deref(), Some("main"));
    }

    #[test]
    fn test_parse_sv_verifier_assert() {
        let decls = parse_sv_file(MOCK_SV, None);
        let vasserts: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == SvDeclKind::VerifierAssert)
            .collect();
        assert_eq!(vasserts.len(), 1);
        assert_eq!(vasserts[0].content.as_deref(), Some("x >= 1"));
    }

    #[test]
    fn test_parse_sv_verifier_error() {
        let decls = parse_sv_file(MOCK_SV, None);
        let errors: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == SvDeclKind::VerifierError)
            .collect();
        assert_eq!(errors.len(), 1);
    }

    #[test]
    fn test_parse_sv_verifier_nondet() {
        let decls = parse_sv_file(MOCK_SV, None);
        let nondets: Vec<_> = decls
            .iter()
            .filter(|d| d.kind == SvDeclKind::VerifierNondet)
            .collect();
        // Two occurrences: declaration + usage
        assert!(!nondets.is_empty());
    }

    #[test]
    fn test_parse_sv_empty() {
        let decls = parse_sv_file("", None);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_extract_c_function_name() {
        assert_eq!(
            extract_c_function_name("int main(void) {"),
            Some("main".to_owned())
        );
        assert_eq!(
            extract_c_function_name("void foo(int x)"),
            Some("foo".to_owned())
        );
        assert_eq!(
            extract_c_function_name("static int _helper(void)"),
            Some("_helper".to_owned())
        );
        assert_eq!(extract_c_function_name("if (x > 0)"), None);
    }
}
