// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Production-aware Rust lint for direct construction of the `sorry` constant.

use super::sorry_bypass_syntax::{cfg_test_item_ranges, lex_rust_tokens, RustToken};
use super::*;

pub(crate) fn validate_sorry_bypass_lint() -> Result<(), ReplacementError> {
    let repo_root = repo_artifact_path("Cargo.toml")
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    let crates_root = repo_root.join("crates");
    let mut findings = Vec::new();
    for entry in WalkDir::new(&crates_root)
        .into_iter()
        .filter_map(Result::ok)
    {
        if !entry.file_type().is_file()
            || entry.path().extension().and_then(|ext| ext.to_str()) != Some("rs")
        {
            continue;
        }
        let relative_path = entry
            .path()
            .strip_prefix(&repo_root)
            .unwrap_or(entry.path())
            .to_string_lossy()
            .replace('\\', "/");
        if SORRY_BYPASS_ALLOWED_FILES.contains(&relative_path.as_str()) {
            continue;
        }
        let source = fs::read_to_string(entry.path()).map_err(|error| {
            ReplacementError::StaleTrustCoreArtifact {
                message: format!("failed to read {relative_path} for sorry-bypass lint: {error}"),
            }
        })?;
        let source_findings =
            sorry_bypass_lines_in_production(&source).map_err(|message| {
                ReplacementError::StaleTrustCoreArtifact {
                    message: format!(
                        "failed to classify test-only Rust in {relative_path} for sorry-bypass lint: {message}"
                    ),
                }
            })?;
        findings.extend(
            source_findings
                .into_iter()
                .map(|line| format!("{relative_path}:{line}")),
        );
    }
    if findings.is_empty() {
        Ok(())
    } else {
        Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "Rust sorry-bypass lint found direct sorry construction outside allowlist: {}",
                findings.join(", ")
            ),
        })
    }
}

/// Return one-based source lines containing a direct bypass in production code.
///
/// Exact module-root `#[cfg(test)]` items are removed before matching calls.
/// Attributes nested in macro token trees and unsupported or malformed syntax
/// remain visible (or error), so uncertainty fails closed.
pub(crate) fn sorry_bypass_lines_in_production(source: &str) -> Result<Vec<usize>, String> {
    let tokens = lex_rust_tokens(source)?;
    let test_ranges = cfg_test_item_ranges(&tokens);
    let production_tokens: Vec<_> = tokens
        .into_iter()
        .filter(|token| {
            !test_ranges
                .iter()
                .any(|(start, end)| token.start >= *start && token.start < *end)
        })
        .collect();
    let mut lines: Vec<_> = direct_sorry_bypass_offsets(&production_tokens)
        .into_iter()
        .map(|offset| {
            1 + source.as_bytes()[..offset]
                .iter()
                .filter(|byte| **byte == b'\n')
                .count()
        })
        .collect();
    lines.sort_unstable();
    lines.dedup();
    Ok(lines)
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn line_has_sorry_bypass(line: &str) -> bool {
    sorry_bypass_lines_in_production(line).is_ok_and(|lines| !lines.is_empty())
}

fn direct_sorry_bypass_offsets(tokens: &[RustToken<'_>]) -> Vec<usize> {
    let mut offsets = Vec::new();
    for index in 0..tokens.len() {
        if direct_string_constructor(tokens, index, None)
            || direct_string_constructor(tokens, index, Some("const_str"))
            || direct_string_constructor(tokens, index, Some("const_str_levels"))
            || direct_name_constructor(tokens, index)
        {
            offsets.push(tokens[index].start);
        }
    }
    offsets
}

fn direct_string_constructor(
    tokens: &[RustToken<'_>],
    index: usize,
    expr_method: Option<&str>,
) -> bool {
    let string_index = if let Some(method) = expr_method {
        if !token_is_ident(tokens, index, "Expr")
            || !token_is_punct(tokens, index + 1, b':')
            || !token_is_punct(tokens, index + 2, b':')
            || !token_is_ident(tokens, index + 3, method)
            || !token_is_punct(tokens, index + 4, b'(')
        {
            return false;
        }
        index + 5
    } else {
        if !token_is_ident(tokens, index, "mk_const_str")
            || !token_is_punct(tokens, index + 1, b'(')
        {
            return false;
        }
        index + 2
    };
    tokens
        .get(string_index)
        .is_some_and(|token| token.is_sorry_string())
}

fn direct_name_constructor(tokens: &[RustToken<'_>], index: usize) -> bool {
    if !token_is_ident(tokens, index, "Expr")
        || !token_is_punct(tokens, index + 1, b':')
        || !token_is_punct(tokens, index + 2, b':')
        || !token_is_ident(tokens, index + 3, "const_")
        || !token_is_punct(tokens, index + 4, b'(')
    {
        return false;
    }
    let Some(argument_end) = first_argument_end(tokens, index + 4) else {
        return false;
    };
    (index + 5..argument_end).any(|name| {
        token_is_ident(tokens, name, "Name")
            && token_is_punct(tokens, name + 1, b':')
            && token_is_punct(tokens, name + 2, b':')
            && token_is_ident(tokens, name + 3, "from_string")
            && token_is_punct(tokens, name + 4, b'(')
            && tokens
                .get(name + 5)
                .is_some_and(|token| token.is_sorry_string())
    })
}

fn first_argument_end(tokens: &[RustToken<'_>], open: usize) -> Option<usize> {
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(open + 1) {
        if paren_depth == 0
            && bracket_depth == 0
            && brace_depth == 0
            && (token.is_punct(b',') || token.is_punct(b')'))
        {
            return Some(index);
        }
        if token.is_punct(b'(') {
            paren_depth = paren_depth.saturating_add(1);
        } else if token.is_punct(b')') {
            paren_depth = paren_depth.saturating_sub(1);
        } else if token.is_punct(b'[') {
            bracket_depth = bracket_depth.saturating_add(1);
        } else if token.is_punct(b']') {
            bracket_depth = bracket_depth.saturating_sub(1);
        } else if token.is_punct(b'{') {
            brace_depth = brace_depth.saturating_add(1);
        } else if token.is_punct(b'}') {
            brace_depth = brace_depth.saturating_sub(1);
        }
    }
    None
}

fn token_is_ident(tokens: &[RustToken<'_>], index: usize, expected: &str) -> bool {
    tokens
        .get(index)
        .is_some_and(|token| token.is_ident(expected))
}

fn token_is_punct(tokens: &[RustToken<'_>], index: usize, expected: u8) -> bool {
    tokens
        .get(index)
        .is_some_and(|token| token.is_punct(expected))
}
