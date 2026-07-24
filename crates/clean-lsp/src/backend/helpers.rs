// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Generic shared helpers for the LSP backend.

use tower_lsp::lsp_types::*;

/// Check if two ranges overlap
pub(crate) fn ranges_overlap(a: Range, b: Range) -> bool {
    // Ranges overlap if one doesn't end before the other starts
    !(a.end.line < b.start.line
        || (a.end.line == b.start.line && a.end.character < b.start.character)
        || b.end.line < a.start.line
        || (b.end.line == a.start.line && b.end.character < a.start.character))
}

/// Extract identifier name from an error message
pub(crate) fn extract_identifier_from_error(message: &str) -> Option<String> {
    // Try to extract quoted identifier like `foo`
    if let Some(start) = message.find('`') {
        if let Some(end) = message[start + 1..].find('`') {
            return Some(message[start + 1..start + 1 + end].to_string());
        }
    }

    // Try to extract identifier after "identifier" or "unknown"
    let patterns = ["unknown identifier ", "identifier ", "not found: "];
    for pattern in patterns {
        if let Some(pos) = message.find(pattern) {
            let start = pos + pattern.len();
            let end = message[start..]
                .find(|c: char| !c.is_alphanumeric() && c != '_' && c != '.')
                .map_or(message.len(), |p| start + p);
            if start < end {
                return Some(message[start..end].to_string());
            }
        }
    }

    None
}

/// Suggest imports for a given identifier
pub(crate) fn suggest_imports_for_identifier(ident: &str) -> Vec<&'static str> {
    // Map common identifiers to their likely imports
    match ident {
        "Nat" | "Int" | "Bool" | "String" | "List" | "Array" | "Option" | "Sum" => vec!["Init"],
        "HashMap" | "HashSet" | "RBMap" | "RBTree" => {
            vec!["Std.Data.HashMap", "Std.Data.HashSet", "Std.Data.RBMap"]
        }
        "Decidable" | "DecidableEq" => vec!["Init.Core"],
        "Monad" | "Functor" | "Applicative" => vec!["Init.Control.Monad"],
        "IO" | "EIO" => vec!["Init.System.IO"],
        "Real" | "Complex" => vec!["Mathlib.Data.Real.Basic", "Mathlib.Data.Complex.Basic"],
        "Group" | "Ring" | "Field" => vec![
            "Mathlib.Algebra.Group.Basic",
            "Mathlib.Algebra.Ring.Basic",
            "Mathlib.Algebra.Field.Basic",
        ],
        _ => {
            // Check for qualified names
            if ident.starts_with("Std.") {
                vec!["Std"]
            } else if ident.starts_with("Mathlib.") {
                vec!["Mathlib"]
            } else {
                vec![]
            }
        }
    }
}

/// Convert byte offset to (line, character) position
pub(crate) fn byte_offset_to_position(text: &str, offset: usize) -> Position {
    let mut line = 0u32;
    let mut col = 0u32;
    for (i, c) in text.char_indices() {
        if i >= offset {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 0;
        } else {
            col += c.len_utf16() as u32;
        }
    }
    Position::new(line, col)
}

/// Keywords that open an indentation-delimited block in Lean 4 surface
/// syntax. When one of these is the final token on a line, the following
/// more-indented lines form a foldable block (`do`/`by`/`where`) or are
/// introduced by a `match ... with` header.
const BLOCK_OPENER_KEYWORDS: &[&str] = &["do", "by", "where", "with"];

/// Declaration-introducing keywords. The body of such a declaration — the run
/// of more-indented lines below its header — is folded as a region. This is
/// deliberately text-driven rather than span-driven: the LSP parser frequently
/// returns a recovery span that covers only the header keyword, so relying on
/// command spans would miss almost every real multi-line body.
const DECL_KEYWORDS: &[&str] = &[
    "def",
    "theorem",
    "lemma",
    "example",
    "instance",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "opaque",
    "axiom",
];

/// Compute the full set of folding ranges for a document.
///
/// Combines several deterministic, elaboration-free sources:
/// 1. One [`FoldingRangeKind::Region`] per `namespace`/`section` … `end`
///    block, matched by a balanced text scan (the parser span only covers the
///    header line, so this cannot be span-driven).
/// 2. One [`FoldingRangeKind::Region`] per multi-line declaration body (the
///    indented run beneath a `def`/`theorem`/`structure`/… header).
/// 3. One [`FoldingRangeKind::Comment`] per multi-line `/- … -/` block
///    comment, preserving the real start column of the opener.
/// 4. One [`FoldingRangeKind::Comment`] per run of two or more consecutive
///    `--` line comments.
/// 5. One [`FoldingRangeKind::Region`] per indentation block introduced by a
///    `do` / `by` / `where` / `match … with` header.
///
/// The result is intentionally allowed to contain overlapping/nested ranges:
/// the LSP protocol permits this and clients render nested folds correctly.
pub(crate) fn compute_folding_ranges(text: &str) -> Vec<FoldingRange> {
    let mut ranges = Vec::new();

    // (1) namespace/section … end blocks.
    ranges.extend(compute_namespace_section_ranges(text));

    // (2) Declaration bodies (indented run under a decl header).
    ranges.extend(compute_indentation_block_ranges(text, |line| {
        first_token(line).is_some_and(|tok| DECL_KEYWORDS.contains(&tok))
    }));

    // (3) Block comments `/- … -/`. Track the real start column of the opener
    // rather than assuming column 0, and only emit multi-line folds.
    let mut block_comment_start: Option<(u32, u32)> = None;
    for (line_num, line) in text.lines().enumerate() {
        let line_num = line_num as u32;
        let trimmed = line.trim_start();
        if block_comment_start.is_none() && trimmed.starts_with("/-") {
            let indent = (line.len() - trimmed.len()) as u32;
            // A `/- … -/` that opens and closes on the same line is not a fold.
            if trimmed.trim_end().ends_with("-/") && trimmed.trim_end().len() > 2 {
                continue;
            }
            block_comment_start = Some((line_num, indent));
        } else if let Some((start_line, start_char)) = block_comment_start {
            if line.trim_end().ends_with("-/") {
                if line_num > start_line {
                    ranges.push(FoldingRange {
                        start_line,
                        start_character: Some(start_char),
                        end_line: line_num,
                        end_character: Some(line.chars().count() as u32),
                        kind: Some(FoldingRangeKind::Comment),
                        collapsed_text: Some("...".to_string()),
                    });
                }
                block_comment_start = None;
            }
        }
    }

    // (4) Runs of consecutive `--` line comments.
    let mut line_comment_start: Option<u32> = None;
    let mut prev_was_comment = false;
    let line_count = text.lines().count() as u32;
    for (line_num, line) in text.lines().enumerate() {
        let line_num = line_num as u32;
        let is_comment = line.trim_start().starts_with("--");
        if is_comment {
            if !prev_was_comment {
                line_comment_start = Some(line_num);
            }
        } else if prev_was_comment {
            if let Some(start) = line_comment_start {
                if line_num > start + 1 {
                    ranges.push(FoldingRange {
                        start_line: start,
                        start_character: Some(0),
                        end_line: line_num - 1,
                        end_character: None,
                        kind: Some(FoldingRangeKind::Comment),
                        collapsed_text: Some("-- ...".to_string()),
                    });
                }
            }
            line_comment_start = None;
        }
        prev_was_comment = is_comment;
    }
    // File that ends inside a comment run.
    if let Some(start) = line_comment_start {
        if line_count > start + 1 {
            ranges.push(FoldingRange {
                start_line: start,
                start_character: Some(0),
                end_line: line_count - 1,
                end_character: None,
                kind: Some(FoldingRangeKind::Comment),
                collapsed_text: Some("-- ...".to_string()),
            });
        }
    }

    // (5) Indentation blocks opened by `do` / `by` / `where` / `match … with`.
    ranges.extend(compute_indentation_block_ranges(
        text,
        ends_with_block_opener,
    ));

    ranges
}

/// The first whitespace-delimited token of a line, or `None` if the line is
/// blank. Used to recognize declaration headers without a full parse.
fn first_token(line: &str) -> Option<&str> {
    line.split_whitespace().next()
}

/// Fold `namespace`/`section` blocks by pairing each opener with its matching
/// `end` via a balanced scan. Lean allows anonymous `section` and `end`, so
/// matching is positional (a stack) rather than name-based.
fn compute_namespace_section_ranges(text: &str) -> Vec<FoldingRange> {
    let mut ranges = Vec::new();
    let mut stack: Vec<(u32, u32)> = Vec::new(); // (start_line, header_char_len)

    for (line_num, line) in text.lines().enumerate() {
        let line_num = line_num as u32;
        match first_token(line) {
            Some("namespace") | Some("section") => {
                stack.push((line_num, line.chars().count() as u32));
            }
            Some("end") => {
                if let Some((start_line, header_char)) = stack.pop() {
                    if line_num > start_line {
                        ranges.push(FoldingRange {
                            start_line,
                            start_character: Some(header_char),
                            end_line: line_num,
                            end_character: Some(line.chars().count() as u32),
                            kind: Some(FoldingRangeKind::Region),
                            collapsed_text: None,
                        });
                    }
                }
            }
            _ => {}
        }
    }

    ranges
}

/// Width of the leading-whitespace indentation of a line, or `None` for a
/// blank line (which never anchors a fold and never closes one).
fn line_indent(line: &str) -> Option<u32> {
    if line.trim().is_empty() {
        return None;
    }
    Some(line.chars().take_while(|c| *c == ' ' || *c == '\t').count() as u32)
}

/// Whether `line` ends (ignoring trailing whitespace and a trailing line
/// comment) with one of the block-opener keywords as a standalone token.
fn ends_with_block_opener(line: &str) -> bool {
    // Drop a trailing `-- …` line comment so `foo do  -- note` still opens.
    let code = match line.find("--") {
        Some(idx) => &line[..idx],
        None => line,
    };
    let code = code.trim_end();
    BLOCK_OPENER_KEYWORDS.iter().any(|kw| {
        code.strip_suffix(kw).is_some_and(|prefix| {
            // The keyword must be a whole token: preceded by start-of-line or
            // a non-identifier character.
            prefix
                .chars()
                .next_back()
                .is_none_or(|c| !c.is_alphanumeric() && c != '_' && c != '.')
        })
    })
}

/// Compute folding ranges for indentation blocks. A block is anchored on a
/// header line accepted by `is_header` and extends across the following run of
/// lines that are strictly more indented than the header.
fn compute_indentation_block_ranges<F>(text: &str, is_header: F) -> Vec<FoldingRange>
where
    F: Fn(&str) -> bool,
{
    let lines: Vec<&str> = text.lines().collect();
    let mut ranges = Vec::new();

    for (idx, line) in lines.iter().enumerate() {
        if !is_header(line) {
            continue;
        }
        let Some(header_indent) = line_indent(line) else {
            continue;
        };

        // Walk forward over the indented body. Blank lines are tolerated
        // inside the block as long as a more-indented line follows; the fold
        // is clamped to the last non-blank body line so trailing blanks are
        // never swallowed into it.
        let mut end_line = idx;
        for (offset, body) in lines.iter().enumerate().skip(idx + 1) {
            match line_indent(body) {
                // Blank line: part of the block only if more body follows, so
                // it does not by itself extend the fold.
                None => {}
                Some(indent) if indent > header_indent => end_line = offset,
                Some(_) => break,
            }
        }

        if end_line > idx {
            let header_char = line.chars().count() as u32;
            ranges.push(FoldingRange {
                start_line: idx as u32,
                start_character: Some(header_char),
                end_line: end_line as u32,
                end_character: Some(lines[end_line].chars().count() as u32),
                kind: Some(FoldingRangeKind::Region),
                collapsed_text: None,
            });
        }
    }

    ranges
}
