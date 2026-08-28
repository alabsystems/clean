// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `textDocument/hover` — the type of the thing under the cursor.
//!
//! # What was broken
//!
//! Measured at the wire by an exhaustive grid sweep over a 16-line file
//! (`d33c59dd7`): hover answered non-`null` at **28 of 385** cursor positions,
//! and those 28 were exactly the bytes of the `def` / `theorem` / `structure`
//! KEYWORDS of declarations that elaborated. Every identifier, type, binder
//! and body position answered `null`.
//!
//! The cause is a span, not the hover logic. `clean_parser`'s
//! `grammar/decl/mod.rs` takes `let span = self.current_span();` while sitting
//! on the command keyword, `advance()`s past it, and stores that keyword-only
//! span on the declaration (`decl/def_theorem.rs`, `span: start_span`). It is
//! never widened to the declaration's end, so the enclosing-declaration scan
//! that `get_hover_at` performs could only ever match inside the keyword.
//!
//! # Why the repair is here and not in the parser
//!
//! That span is not hover's private property. `CleanBackend::classify_decl`
//! hands the same `(start, end)` to diagnostic ranges, `documentSymbol`, code
//! lenses, folding ranges and the incremental content hash, and the elaborator
//! threads the same `start_span` into sub-expressions it builds. Widening it in
//! the parser would move every one of those surfaces at once. So the
//! declaration's true extent is reconstructed HERE, from information the
//! server already has: a declaration runs from its keyword to the start of the
//! next top-level command, trimmed of the whitespace between them.
//!
//! # What hover answers now
//!
//! 1. **The identifier under the cursor, resolved to its own type** — a
//!    declaration of this document, or a constant of the import closure the
//!    document elaborated against (`Document::imports_env`). This is the half
//!    that makes hover useful: `double` inside `uses_double` reports
//!    `double : Nat -> Nat`, not `uses_double`'s type.
//! 2. **The enclosing declaration**, over its full extent, when the cursor is
//!    not on a resolvable name.
//!
//! Positions with no type to report still answer `null`, and deliberately so:
//! comments, blank lines, and declarations that failed to elaborate (whose
//! resolvable identifiers still hover through path 1). Local binders resolve
//! to their enclosing declaration rather than to `n : Nat` — term-local hover
//! needs a local context hover does not have, and is a separate brick.

use super::CleanBackend;
use crate::document::{Document, ElaboratedDecl, ElaboratedDocument};
use tower_lsp::lsp_types::*;

impl CleanBackend {
    /// Get hover information at a position.
    pub(crate) fn get_hover_at(&self, uri: &Url, position: Position) -> Option<Hover> {
        let doc = self.documents.get(uri)?;
        let elab = doc.elaborated.as_ref()?;
        let text = doc.text();
        let offset = doc.position_to_offset(position);

        if let Some((start, end, name, type_str)) =
            Self::hover_identifier_at(&doc, elab, &text, offset)
        {
            return Some(Self::hover_signature(&doc, &name, &type_str, start, end));
        }

        let (start, end, decl) = Self::hover_enclosing_declaration(&doc, elab, &text, offset)?;
        Some(Self::hover_signature(
            &doc,
            &decl.name,
            &decl.type_str,
            start,
            end,
        ))
    }

    /// Render a `name : type` signature as the Lean-fenced markdown every
    /// other editor surface (completion detail, inlay tooltips) uses.
    fn hover_signature(
        doc: &Document,
        name: &str,
        type_str: &str,
        start: usize,
        end: usize,
    ) -> Hover {
        Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: format!("```lean\n{name} : {type_str}\n```"),
            }),
            range: Some(Range {
                start: doc.offset_to_position(start),
                end: doc.offset_to_position(end),
            }),
        }
    }

    /// The identifier under the cursor together with its own type, when that
    /// name resolves. Returns `(span start, span end, name, type)`.
    fn hover_identifier_at(
        doc: &Document,
        elab: &ElaboratedDocument,
        text: &str,
        offset: usize,
    ) -> Option<(usize, usize, String, String)> {
        let (bare_start, bare_end) = Self::identifier_span_at(text, offset)?;
        for (start, end) in Self::hover_name_candidates(text, bare_start, bare_end) {
            let name = text.get(start..end)?;
            if let Some(type_str) = Self::hover_type_of_name(doc, elab, name) {
                return Some((start, end, name.to_string(), type_str));
            }
        }
        None
    }

    /// Name spans to try for the identifier at `(bare_start, bare_end)`, most
    /// specific first: the full dotted name the identifier participates in
    /// (`Nat.succ` when the cursor is on either half), then the bare segment.
    ///
    /// Trying both matters because the dotted form is a genuine constant name
    /// in Lean *and* the field-projection syntax `p.x`, where only the bare
    /// segment can resolve.
    fn hover_name_candidates(
        text: &str,
        bare_start: usize,
        bare_end: usize,
    ) -> Vec<(usize, usize)> {
        let mut start = bare_start;
        while let Some(head) = text.get(..start).and_then(|p| p.strip_suffix('.')) {
            let segment: usize = head
                .chars()
                .rev()
                .take_while(|c| Self::is_identifier_continue(*c))
                .map(char::len_utf8)
                .sum();
            if segment == 0 {
                break;
            }
            let segment_start = head.len() - segment;
            // A dotted name's segments each start like an identifier; a
            // decimal literal (`1.5`) must not be glued into a name.
            if !text[segment_start..]
                .chars()
                .next()
                .is_some_and(Self::is_identifier_start)
            {
                break;
            }
            start = segment_start;
        }

        let mut end = bare_end;
        while let Some(tail) = text.get(end..).and_then(|s| s.strip_prefix('.')) {
            if !tail.chars().next().is_some_and(Self::is_identifier_start) {
                break;
            }
            let segment: usize = tail
                .chars()
                .take_while(|c| Self::is_identifier_continue(*c))
                .map(char::len_utf8)
                .sum();
            end += '.'.len_utf8() + segment;
        }

        if (start, end) == (bare_start, bare_end) {
            vec![(bare_start, bare_end)]
        } else {
            vec![(start, end), (bare_start, bare_end)]
        }
    }

    /// The type of `name` as this document sees it: a declaration of the
    /// document itself first, then a constant of the import closure the
    /// document elaborated against.
    ///
    /// The environment lookup is a map read on an already-loaded `Arc` — it
    /// never triggers the (blocking, up-to-a-minute) `.olean` closure load,
    /// which is why the closure is captured at commit time rather than
    /// resolved here.
    fn hover_type_of_name(doc: &Document, elab: &ElaboratedDocument, name: &str) -> Option<String> {
        if let Some(decl) = elab.declarations.iter().find(|decl| decl.name == name) {
            return Some(decl.type_str.clone());
        }

        // A declaration opened inside a `namespace` is recorded under its full
        // name but written under its last segment. Resolve that only when the
        // suffix is unambiguous — two declarations sharing a last segment give
        // no basis for picking one.
        let mut suffix_matches = elab
            .declarations
            .iter()
            .filter(|decl| decl.name.rsplit('.').next() == Some(name));
        if let Some(decl) = suffix_matches.next() {
            if suffix_matches.next().is_none() {
                return Some(decl.type_str.clone());
            }
        }

        let env = doc.imports_env.as_ref()?;
        let info = env.get_const(&clean_kernel::Name::from_string(name))?;
        Some(format!("{}", info.type_))
    }

    /// The elaborated declaration enclosing `offset`, with the extent it
    /// actually occupies in the source.
    fn hover_enclosing_declaration<'a>(
        doc: &Document,
        elab: &'a ElaboratedDocument,
        text: &str,
        offset: usize,
    ) -> Option<(usize, usize, &'a ElaboratedDecl)> {
        let (start, end) = Self::declaration_extent(doc, elab, text, offset)?;
        let decl = elab.declarations.iter().find(|decl| decl.start == start)?;
        Some((start, end, decl))
    }

    /// Byte extent of the top-level unit enclosing `offset`, half-open.
    ///
    /// Reconstructed from the anchors the server already records — the start
    /// of every parsed command and of every elaborated declaration (the
    /// latter so a declaration nested in a `namespace`, which is not itself a
    /// top-level command, still anchors its own extent). A unit runs to the
    /// next anchor, minus the whitespace before it, so blank lines and the
    /// gap between declarations belong to no declaration.
    fn declaration_extent(
        doc: &Document,
        elab: &ElaboratedDocument,
        text: &str,
        offset: usize,
    ) -> Option<(usize, usize)> {
        let mut anchors: Vec<usize> = doc
            .parsed
            .iter()
            .flat_map(|parsed| parsed.commands.iter().map(|command| command.start))
            .chain(elab.declarations.iter().map(|decl| decl.start))
            .collect();
        anchors.sort_unstable();
        anchors.dedup();

        let index = anchors.partition_point(|anchor| *anchor <= offset);
        let start = *anchors.get(index.checked_sub(1)?)?;
        let limit = anchors.get(index).copied().unwrap_or(text.len());
        let end = text.get(..limit)?.trim_end().len();
        (offset < end).then_some((start, end))
    }
}
