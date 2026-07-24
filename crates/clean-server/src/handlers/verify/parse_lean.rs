// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean file parser for extracting theorem/lemma declarations and sorry locations.

use super::types::{ExtractedTheorem, SorryLocation};
use clean_elab::tactic::script_runner::comment_strip::strip_block_comments;

const EXPLICIT_HOLE_TOKENS: &[&str] = &["sorry", "admit"];

/// Returns `true` when `tactic` is an explicit hole tactic (`sorry`, `admit`).
///
/// Used by both `composeProof` and `fillSorries` replay paths to keep the
/// tactic-level hole check synchronized with the textual scanner.
pub(crate) fn is_explicit_hole_tactic(tactic: &str) -> bool {
    EXPLICIT_HOLE_TOKENS.contains(&tactic.split_whitespace().next().unwrap_or(""))
}

fn strip_line_comment(line: &str) -> &str {
    match line.find("--") {
        Some(pos) => &line[..pos],
        None => line,
    }
}

fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Check whether `line` contains an explicit hole token at `column`.
///
/// Strips both `/- ... -/` block comments and `-- ...` line comments before
/// scanning, so tokens hidden inside comments are never reported as holes.
pub(crate) fn explicit_hole_token_at(line: &str, column: usize) -> Option<&'static str> {
    let block_stripped = strip_block_comments(line);
    let comment_free = strip_line_comment(&block_stripped);

    for &token in EXPLICIT_HOLE_TOKENS {
        let end = column.checked_add(token.len())?;
        if comment_free.get(column..end) != Some(token) {
            continue;
        }

        let before = if column == 0 {
            None
        } else {
            comment_free[..column].chars().next_back()
        };
        let after = comment_free[end..].chars().next();
        let starts_at_boundary = before.is_none_or(|c| !is_identifier_char(c));
        let ends_at_boundary = after.is_none_or(|c| !is_identifier_char(c));

        if starts_at_boundary && ends_at_boundary {
            return Some(token);
        }
    }

    None
}

fn collect_explicit_holes(line: &str) -> Vec<usize> {
    let comment_free = strip_line_comment(line);
    let mut columns = Vec::new();
    let mut search_start = 0usize;

    while search_start < comment_free.len() {
        let next_match = EXPLICIT_HOLE_TOKENS
            .iter()
            .filter_map(|&token| {
                comment_free[search_start..]
                    .find(token)
                    .map(|offset| (search_start + offset, token))
            })
            .min_by_key(|(column, _)| *column);

        let Some((column, token)) = next_match else {
            break;
        };

        if explicit_hole_token_at(line, column).is_some() {
            columns.push(column);
        }

        search_start = column + token.len();
    }

    columns
}

/// Parse a Lean file to extract theorem/lemma and sorry locations.
///
/// Block comments (`/- ... -/`, including nested) are stripped before scanning
/// so that `sorry`/`admit` tokens inside comments are never reported as holes,
/// and `theorem`/`lemma` keywords inside comments are never detected as
/// declarations.  Line numbers and byte offsets are preserved because
/// [`strip_block_comments`] replaces comment content with spaces, keeping
/// newlines intact.
///
/// Returns `(Option<ExtractedTheorem>, Vec<SorryLocation>)`
pub(crate) fn parse_lean_file(
    content: &str,
) -> Result<(Option<ExtractedTheorem>, Vec<SorryLocation>), String> {
    // Strip block comments across the whole file so multiline `/- ... -/`
    // spanning several lines cannot hide or expose false holes/theorems.
    let stripped = strip_block_comments(content);

    // Find explicit user holes in source text. Trusted tactic usage is tracked
    // semantically via the proof-state trust ledger after tactic execution.
    let mut sorries = Vec::new();
    for (line_idx, line) in stripped.lines().enumerate() {
        for col in collect_explicit_holes(line) {
            sorries.push(SorryLocation {
                line: line_idx + 1,
                col: col + 1,
                context: None, // Will be filled below if in theorem
            });
        }
    }

    let mut theorem: Option<ExtractedTheorem> = None;

    // Find theorem/lemma declaration (simple string-based parsing)
    for (line_idx, line) in stripped.lines().enumerate() {
        let trimmed = line.trim();

        // Skip line comments
        if trimmed.starts_with("--") {
            continue;
        }

        // Look for theorem or lemma keyword
        let keyword = if trimmed.starts_with("theorem ") {
            Some("theorem ")
        } else if trimmed.starts_with("lemma ") {
            Some("lemma ")
        } else {
            None
        };

        if let Some(kw) = keyword {
            // Found a theorem/lemma declaration
            let after_keyword = &trimmed[kw.len()..];

            // Extract name (first word)
            let name_end = after_keyword
                .find(|c: char| !c.is_alphanumeric() && c != '_')
                .unwrap_or(after_keyword.len());
            let name = after_keyword[..name_end].to_string();

            // Find colon and := to extract type signature
            // We need to handle multi-line declarations
            let remaining_content = &stripped[stripped.find(line).unwrap_or(0)..];

            // Find the `:=` that marks end of type signature
            if let Some(assign_pos) = remaining_content.find(":=") {
                let declaration = &remaining_content[..assign_pos];

                // Find colon that separates parameters from type
                // The type starts after the last `:` that isn't inside parens/brackets
                let mut depth: usize = 0;
                let mut type_start = None;
                for (i, c) in declaration.char_indices() {
                    match c {
                        '(' | '[' | '{' => depth += 1,
                        ')' | ']' | '}' => depth = depth.saturating_sub(1),
                        ':' if depth == 0 => type_start = Some(i + 1),
                        _ => {}
                    }
                }

                if let Some(start) = type_start {
                    let type_sig = declaration[start..].trim().to_string();

                    // Extract proof (after `:=`)
                    let proof_start = assign_pos + 2;
                    let proof_text = remaining_content[proof_start..].trim();

                    // Handle `by` keyword
                    let proof = proof_text
                        .strip_prefix("by")
                        .map(|s| s.trim())
                        .unwrap_or(proof_text);

                    // Trim proof to first complete statement
                    let proof_end = proof
                        .find("\ntheorem ")
                        .or_else(|| proof.find("\nlemma "))
                        .or_else(|| proof.find("\ndef "))
                        .or_else(|| proof.find("\nexample "))
                        .or_else(|| proof.find("\n#"))
                        .unwrap_or(proof.len());
                    let original_proof = proof[..proof_end].trim().to_string();

                    // Update sorry contexts
                    for sorry in &mut sorries {
                        sorry.context = Some(name.clone());
                    }

                    theorem = Some(ExtractedTheorem {
                        name,
                        goal: type_sig,
                        line: line_idx + 1,
                        original_proof,
                    });

                    break; // Only extract first theorem for now
                }
            }
        }
    }

    Ok((theorem, sorries))
}
