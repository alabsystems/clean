// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `textDocument/selectionRange` provider.
//!
//! Builds, for each requested cursor position, a hierarchy of expanding byte
//! ranges from the smallest meaningful syntactic unit out to the whole
//! document. The hierarchy is derived purely from document structure (lexer
//! tokens plus parsed command spans), so it requires neither elaboration nor
//! any network/IO and is fully deterministic.
//!
//! Each level strictly contains its child. From innermost to outermost the
//! candidate levels are:
//! 1. the identifier / word at the cursor;
//! 2. the smallest enclosing balanced bracket pair (`()`, `[]`, `{}`, `⟨⟩`,
//!    `⟪⟫`), including the brackets themselves;
//! 3. the enclosing top-level command / declaration span;
//! 4. the whole document.

use super::CleanBackend;
use crate::document::Document;
use clean_parser::lexer::{Lexer, TokenKind};
use tower_lsp::lsp_types::{Position, Range, SelectionRange};

/// One bracket pair recovered from a balanced token scan, as a byte range
/// `[open_start, close_end)` covering both delimiters and everything between.
type BracketSpan = (usize, usize);

impl CleanBackend {
    /// Compute the selection-range hierarchy for a single position.
    ///
    /// Returns `None` only when the document is unknown; an open document
    /// always yields at least the whole-document range so the client can keep
    /// expanding the selection.
    pub(crate) fn selection_range_at(
        &self,
        uri: &tower_lsp::lsp_types::Url,
        position: Position,
    ) -> Option<SelectionRange> {
        let doc = self.documents.get(uri)?;
        Some(build_selection_range(&doc, position))
    }
}

/// Build the expanding range hierarchy for `position` within `doc`.
///
/// The returned [`SelectionRange`] is the innermost range; its `parent` chain
/// walks outward to the whole-document range. Levels that do not strictly grow
/// the range are skipped so the client never sees a degenerate (zero-width or
/// repeated) step.
fn build_selection_range(doc: &Document, position: Position) -> SelectionRange {
    let text = doc.text();
    let offset = doc.position_to_offset(position).min(text.len());

    // Collect candidate byte ranges, outermost first. We reverse them into the
    // parent chain so the innermost becomes the leaf returned to the client.
    let mut byte_ranges: Vec<(usize, usize)> = Vec::new();

    // (4) Whole document.
    byte_ranges.push((0, text.len()));

    // (3) Enclosing top-level command span.
    if let Some(cmd) = doc.parsed.as_ref().and_then(|parsed| {
        parsed
            .commands
            .iter()
            .filter(|cmd| cmd.start <= offset && offset <= cmd.end && cmd.end > cmd.start)
            .min_by_key(|cmd| cmd.end - cmd.start)
    }) {
        byte_ranges.push((cmd.start, cmd.end));
    }

    // (2) Enclosing bracket pairs, outermost first.
    let mut brackets = enclosing_bracket_spans(&text, offset);
    // `enclosing_bracket_spans` yields innermost-first; reverse to outermost-first
    // so they slot in before the word level.
    brackets.reverse();
    byte_ranges.extend(brackets);

    // (1) The identifier / word at the cursor.
    if let Some((start, end)) = CleanBackend::identifier_span_at(&text, offset) {
        byte_ranges.push((start, end));
    }

    // Deduplicate while preserving order, and enforce strict containment: a
    // child range must lie within its parent. `byte_ranges` is ordered
    // outermost-first; fold inward.
    let mut chain: Vec<(usize, usize)> = Vec::with_capacity(byte_ranges.len());
    for (start, end) in byte_ranges {
        if start >= end && !chain.is_empty() {
            // Skip zero-width inner candidates (the whole-document base may be
            // empty for an empty document, which is fine).
            continue;
        }
        match chain.last() {
            Some(&(p_start, p_end)) => {
                let contained = p_start <= start && end <= p_end;
                let strictly_smaller = (start, end) != (p_start, p_end);
                if contained && strictly_smaller {
                    chain.push((start, end));
                }
            }
            None => chain.push((start, end)),
        }
    }

    // Convert outermost-first byte ranges into a parent-linked chain whose leaf
    // is the innermost range.
    let mut node: Option<SelectionRange> = None;
    for (start, end) in chain {
        let range = Range {
            start: doc.offset_to_position(start),
            end: doc.offset_to_position(end),
        };
        node = Some(SelectionRange {
            range,
            parent: node.map(Box::new),
        });
    }

    node.unwrap_or_else(|| SelectionRange {
        range: Range {
            start: Position::new(0, 0),
            end: doc.offset_to_position(text.len()),
        },
        parent: None,
    })
}

/// Find every balanced bracket pair that encloses `offset`, ordered
/// innermost-first.
///
/// Performs a single left-to-right token scan, maintaining a stack of open
/// delimiters. When a closer matches the top of the stack, the resulting span
/// `[open_start, close_end)` is recorded if it brackets `offset`. Unbalanced or
/// mismatched delimiters are tolerated: a closer with no matching opener is
/// ignored, and openers left on the stack at end-of-input contribute nothing.
fn enclosing_bracket_spans(text: &str, offset: usize) -> Vec<BracketSpan> {
    let tokens = Lexer::tokenize(text);
    let mut stack: Vec<(BracketKind, usize)> = Vec::new();
    let mut spans: Vec<BracketSpan> = Vec::new();

    for token in &tokens {
        if let Some(open) = opener_kind(&token.kind) {
            stack.push((open, token.span.start));
        } else if let Some(close) = closer_kind(&token.kind) {
            // Pop until we find a matching opener; tolerate mismatches by
            // discarding intervening unmatched openers.
            while let Some(&(open, open_start)) = stack.last() {
                stack.pop();
                if open == close {
                    let span = (open_start, token.span.end);
                    if span.0 <= offset && offset <= span.1 {
                        spans.push(span);
                    }
                    break;
                }
            }
        }
    }

    // The scan records pairs as they close, so an outer pair (closing later)
    // appears after an inner pair. Sort innermost-first by width to make the
    // ordering robust regardless of close order.
    spans.sort_by_key(|(start, end)| end - start);
    spans
}

/// The bracket families clean recognizes. Angle and double-angle brackets are
/// kept distinct so `⟨ … ⟩` and `⟪ … ⟫` never cross-match.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BracketKind {
    Paren,
    Brace,
    Bracket,
    Angle,
    DoubleAngle,
}

fn opener_kind(kind: &TokenKind) -> Option<BracketKind> {
    match kind {
        TokenKind::LParen => Some(BracketKind::Paren),
        TokenKind::LBrace => Some(BracketKind::Brace),
        TokenKind::LBracket => Some(BracketKind::Bracket),
        TokenKind::LAngle => Some(BracketKind::Angle),
        TokenKind::LDAngle => Some(BracketKind::DoubleAngle),
        _ => None,
    }
}

fn closer_kind(kind: &TokenKind) -> Option<BracketKind> {
    match kind {
        TokenKind::RParen => Some(BracketKind::Paren),
        TokenKind::RBrace => Some(BracketKind::Brace),
        TokenKind::RBracket => Some(BracketKind::Bracket),
        TokenKind::RAngle => Some(BracketKind::Angle),
        TokenKind::RDAngle => Some(BracketKind::DoubleAngle),
        _ => None,
    }
}
