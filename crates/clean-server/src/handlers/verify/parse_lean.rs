// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean file parser for extracting theorem/lemma declarations and sorry locations.
//!
//! # Where it runs, and its deadline
//!
//! `verifyFile`, `fillSorries` and `composeProof` parse the file a request
//! sends, up to the transport's 10 MiB, so the parse is request work: it runs
//! on the work pool under the request's deadline (`handlers/work.rs`), never
//! on a runtime worker (until R87, 2026-10-17, it ran there).
//! [`parse_lean_file`] asserts that in debug builds.
//!
//! The parse is not linear in the file: the declaration scan searches the
//! rest of the file once per `theorem`/`lemma` line until one parses (the
//! line's first occurrence, then the next `:=`), so a file of many such lines
//! costs their count times its length. It reads the deadline: the clock before
//! each such line (one search is up to a file's length of work, so a poll
//! that reads the clock once every 1,024 would overshoot by 1,024 of them),
//! and the kernel's poll before each line it scans for holes. Past the
//! deadline it stops, and its caller's `run_until` drops what it returned.
//! The hole scan was quadratic in a line's holes as well (it stripped the
//! line's comments again for each candidate, and searched to the line's end
//! for a token the line no longer held); it strips each line once and
//! searches each token once now.

use super::types::{ExtractedTheorem, SorryLocation};
use crate::handlers::work::deadline_passed_now;
use clean_elab::tactic::script_runner::comment_strip::strip_block_comments;
use clean_kernel::tc::poll_deadline;

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
    hole_token_in(strip_line_comment(&block_stripped), column)
}

/// [`explicit_hole_token_at`] on a line whose comments are stripped already
/// (`strip_line_comment(&strip_block_comments(line))`).
fn hole_token_in(comment_free: &str, column: usize) -> Option<&'static str> {
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
    // What `explicit_hole_token_at(line, column)` checks a candidate against,
    // the same for every candidate of the line: stripped once.
    let block_stripped = strip_block_comments(line);
    let checked = strip_line_comment(&block_stripped);
    let mut columns = Vec::new();
    let mut search_start = 0usize;
    // Each token's first occurrence at or after the last search start (`None`:
    // none after it). It stays the first at or after a later start for as long
    // as it is not before that start, so each token's search moves forward
    // only, and the line is searched once per token.
    let mut next: Vec<Option<usize>> = EXPLICIT_HOLE_TOKENS
        .iter()
        .map(|&token| comment_free.find(token))
        .collect();

    while search_start < comment_free.len() {
        for (found, &token) in next.iter_mut().zip(EXPLICIT_HOLE_TOKENS) {
            if found.is_some_and(|column| column < search_start) {
                *found = comment_free[search_start..]
                    .find(token)
                    .map(|offset| search_start + offset);
            }
        }
        let next_match = next
            .iter()
            .zip(EXPLICIT_HOLE_TOKENS)
            .filter_map(|(found, &token)| found.map(|column| (column, token)))
            .min_by_key(|(column, _)| *column);

        let Some((column, token)) = next_match else {
            break;
        };

        if hole_token_in(checked, column).is_some() {
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
/// Returns `(Option<ExtractedTheorem>, Vec<SorryLocation>)`. Under a deadline
/// that passes while it parses, it stops with an error, which its caller's
/// `run_until` drops (the module's notes above).
pub(crate) fn parse_lean_file(
    content: &str,
) -> Result<(Option<ExtractedTheorem>, Vec<SorryLocation>), String> {
    // A request's parse is work for the pool, never for a runtime worker
    // (the module's notes). Tests build with debug assertions, so a request
    // path that brings it back to the runtime fails every test that takes it.
    debug_assert!(
        tokio::runtime::Handle::try_current().is_err(),
        "a request's Lean file was parsed on an async runtime's thread"
    );

    // Strip block comments across the whole file so multiline `/- ... -/`
    // spanning several lines cannot hide or expose false holes/theorems.
    let stripped = strip_block_comments(content);

    let mut sorries = explicit_holes(&stripped)?;
    let theorem = first_declaration(&stripped, &mut sorries)?;
    Ok((theorem, sorries))
}

/// What a parse its deadline interrupted answers (its caller's `run_until`
/// drops it).
const INTERRUPTED: &str = "the parse was interrupted at its deadline";

/// The explicit holes of a file whose block comments are stripped. Polls the
/// deadline before each line.
pub(crate) fn explicit_holes(stripped: &str) -> Result<Vec<SorryLocation>, String> {
    // Find explicit user holes in source text. Trusted tactic usage is tracked
    // semantically via the proof-state trust ledger after tactic execution.
    let mut sorries = Vec::new();
    for (line_idx, line) in stripped.lines().enumerate() {
        if poll_deadline() {
            return Err(INTERRUPTED.to_string());
        }
        for col in collect_explicit_holes(line) {
            sorries.push(SorryLocation {
                line: line_idx + 1,
                col: col + 1,
                context: None, // Will be filled below if in theorem
            });
        }
    }
    Ok(sorries)
}

/// The first `theorem`/`lemma` of a file whose block comments are stripped,
/// naming it as the context of `sorries`. Reads the clock before each such
/// line: each searches the rest of the file.
pub(crate) fn first_declaration(
    stripped: &str,
    sorries: &mut [SorryLocation],
) -> Result<Option<ExtractedTheorem>, String> {
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
            // What follows searches the rest of the file: read the clock.
            if deadline_passed_now() {
                return Err(INTERRUPTED.to_string());
            }
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
                    for sorry in sorries.iter_mut() {
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

    Ok(theorem)
}
