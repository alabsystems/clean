// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Whether a doc comment ends immediately before a token (plan item
//! `formats-module-spelling-refusals`).
//!
//! Pinned Lean's whitespace is `--` and `/- … -/` comments only
//! (`Lean.Parser.whitespace`): a declaration doc comment (`/-- … -/`) and a
//! module doc (`/-! … -/`) are tokens. Clean's lexer skips both as trivia and
//! records their spans, and the parser asks here where Lean would have seen
//! one: the file header ends at either kind (`decl::header`), and a
//! declaration doc comment is the first word of a modifier prefix
//! (`decl::module_spelling`).
//!
//! Two questions, because two doc comments can stand between the same two
//! tokens. [`Parser::doc_before`] asks what the command at a token carries,
//! reading the gap in source order as Lean does: a module doc is a command of
//! its own, and a declaration doc comment opens a command that no rule
//! continues with another doc comment, so of `/-- a -/ /-! b -/` Lean stops at
//! the end of the first ([`DocBefore::Stacked`]). [`Parser::doc_met_before`]
//! asks which one Lean's parser meets where no rule takes one (inside a header
//! import, after a modifier prefix's first word): the earliest, since Lean
//! stops there.

use super::super::Parser;
use crate::lexer::{Token, TokenKind};
use crate::surface::{DocComment, Span};

/// The opening atom of a declaration doc comment, which Lean names where one
/// is unexpected.
const DECLARATION_ATOM: &str = "/--";
/// The opening atom of a module doc.
const MODULE_ATOM: &str = "/-!";

/// The doc comments before a token with no token between (only whitespace and
/// plain comments), read in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::grammar) enum DocBefore {
    /// A declaration doc comment (`/-- … -/`) ending at byte `end`.
    Declaration { end: usize },
    /// A module doc (`/-! … -/`), a command of its own in Lean.
    Module,
    /// A declaration doc comment ending at byte `end` with another doc comment
    /// after it before the token, whose opening atom is `next`. The first
    /// opens a command and no rule continues one with a doc comment, so Lean
    /// stops at the end of the first: "unexpected token '<next>'; expected
    /// …", the list after a lone doc comment. Only [`Parser::doc_before`]
    /// returns it.
    Stacked { end: usize, next: &'static str },
}

impl DocBefore {
    /// The token Lean names where this doc comment is unexpected: `'/--'` or
    /// `'/-!'`, its opening atom (for [`DocBefore::Stacked`], the first's).
    pub(in crate::grammar) fn lean_token(self) -> &'static str {
        match self {
            Self::Declaration { .. } | Self::Stacked { .. } => DECLARATION_ATOM,
            Self::Module => MODULE_ATOM,
        }
    }
}

impl Parser {
    /// Lean's position of the end of token `index`: its line and its 0-based
    /// codepoint column plus its width, where Lean reports a token that is
    /// unexpected after it (the start of its trailing whitespace,
    /// `mkErrorMessage`).
    pub(in crate::grammar) fn token_end_position(&self, index: usize) -> Option<(usize, usize)> {
        let token = self.tokens.get(index)?;
        let width = self
            .source
            .get(token.span.start..token.span.end)
            .map_or(0, |text| text.chars().count());
        Some((token.line as usize, token.col as usize + width))
    }

    /// The bytes between the end of token `index - 1` (the file's start for
    /// the first token) and the start of token `index`: where a doc comment
    /// Clean's lexer skipped stands with no token between it and `index`.
    fn doc_gap(&self, index: usize) -> Option<(usize, usize)> {
        let target = self.tokens.get(index)?.span.start;
        let from = index
            .checked_sub(1)
            .and_then(|previous| self.tokens.get(previous))
            .map_or(0, |token| token.span.end);
        Some((from, target))
    }

    /// The doc comments Clean's lexer skipped in the gap before token `index`
    /// ([`Parser::doc_gap`]): the declaration doc comments, then the module
    /// docs, each in source order.
    fn docs_in_gap(&self, index: usize) -> Option<(&[DocComment], &[Span])> {
        let (from, target) = self.doc_gap(index)?;
        // Both lists are in source order and no span overlaps another or a
        // token, so the ones in the gap are a run of each.
        let declarations = self
            .doc_comments
            .get(
                self.doc_comments
                    .partition_point(|doc| doc.span.start < from)
                    ..self
                        .doc_comments
                        .partition_point(|doc| doc.span.end <= target),
            )
            .unwrap_or_default();
        let modules = self
            .module_docs
            .get(
                self.module_docs.partition_point(|span| span.start < from)
                    ..self.module_docs.partition_point(|span| span.end <= target),
            )
            .unwrap_or_default();
        Some((declarations, modules))
    }

    /// Capture an actual documentation prefix with its raw text and source
    /// coordinates. This never validates comments or inspects ordinary strings.
    pub(in crate::grammar) fn documentation_before(&self, index: usize) -> Option<DocComment> {
        let DocBefore::Declaration { end } = self.doc_before(index)? else {
            return None;
        };
        self.doc_comments
            .iter()
            .find(|doc| doc.span.end == end)
            .cloned()
    }

    /// What the command at token `index` carries, reading the doc comments
    /// before it with no token between in source order, as Lean does. A
    /// module doc is a command of its own. The first declaration doc comment
    /// opens the command: it is the command's when nothing follows it before
    /// the token, and otherwise Lean stops at its end
    /// ([`DocBefore::Stacked`]). So the closest one is the command's only
    /// when no declaration doc comment comes before it. Measured on pinned
    /// v4.30.0-rc2:
    ///
    /// - `/-! t -/` / `/-- doc -/ section`: `3:10`, after `/-- doc -/`;
    /// - `/-- a -/ /-! b -/ module`: `1:8: error: unexpected token '/-!';
    ///   expected '#guard_msgs', …` (and `/-- a -/ /-- b -/ module` names
    ///   `'/--'`), never the `1:18` or `1:17` message Lean logs after it;
    /// - `/-! a -/ /-- b -/ /-! c -/ section`: `2:17`, after `/-- b -/`.
    ///
    /// A declaration doc comment the command before takes as its last
    /// argument ([`Parser::doc_is_last_argument`]) is the gap's first, and is
    /// not read here.
    pub(in crate::grammar) fn doc_before(&self, index: usize) -> Option<DocBefore> {
        let (declarations, modules) = self.docs_in_gap(index)?;
        let argument_taken = declarations.first().is_some_and(|first| {
            modules
                .first()
                .is_none_or(|module| first.span.start < module.start)
        }) && self.doc_is_last_argument(index);
        let declarations = declarations
            .get(usize::from(argument_taken)..)
            .unwrap_or_default();
        let Some(doc) = declarations.first() else {
            return modules.last().map(|_| DocBefore::Module);
        };
        let next = [
            declarations
                .get(1)
                .map(|next| (next.span.start, DECLARATION_ATOM)),
            modules
                .iter()
                .find(|module| module.start > doc.span.start)
                .map(|module| (module.start, MODULE_ATOM)),
        ]
        .into_iter()
        .flatten()
        .min_by_key(|(start, _)| *start);
        Some(match next {
            Some((_, next)) => DocBefore::Stacked {
                end: doc.span.end,
                next,
            },
            None => DocBefore::Declaration { end: doc.span.end },
        })
    }

    /// The doc comment Lean's parser meets first after token `index - 1`,
    /// where no rule takes one (inside a header import, after the first word
    /// of a modifier prefix): the EARLIEST one before token `index` with no
    /// token between, if any. Lean stops at it, so a second one is never
    /// reached (measured on pinned v4.30.0-rc2: `module` / `import /-- a -/
    /// /-! b -/ Init` is refused at `2:6` with "unexpected token '/--'", and
    /// with the two swapped with "unexpected token '/-!'"). No command is
    /// before it to take it as an argument.
    pub(in crate::grammar) fn doc_met_before(&self, index: usize) -> Option<DocBefore> {
        let (declarations, modules) = self.docs_in_gap(index)?;
        match (declarations.first(), modules.first()) {
            (Some(doc), Some(module)) if module.start < doc.span.start => Some(DocBefore::Module),
            (Some(doc), _) => Some(DocBefore::Declaration { end: doc.span.end }),
            (None, Some(_)) => Some(DocBefore::Module),
            (None, None) => None,
        }
    }

    /// Whether a declaration doc comment ending before token `index` is the
    /// last argument of the command before it, which then takes it: Batteries'
    /// `library_note <title> docComment` (and the deprecated `library_note2`)
    /// and Mathlib's `#adaptation_note (docComment)?`. Lean starts the next
    /// command after the doc comment, so it is no prefix of that command.
    fn doc_is_last_argument(&self, index: usize) -> bool {
        let back = |count: usize| index.checked_sub(count).and_then(|at| self.tokens.get(at));
        let keyword = |token: Option<&Token>, names: &[&str]| {
            token.is_some_and(|token| {
                !token.ident_escaped
                    && matches!(&token.kind, TokenKind::Ident(name) if names.contains(&name.as_str()))
            })
        };
        // `#adaptation_note` is one token in Lean: `#` glued to the name.
        let adaptation_note = keyword(back(1), &["adaptation_note"])
            && back(2).zip(back(1)).is_some_and(|(hash, name)| {
                matches!(hash.kind, TokenKind::Hash) && hash.span.end == name.span.start
            });
        let library_note = back(1).is_some_and(|title| {
            matches!(title.kind, TokenKind::Ident(_) | TokenKind::StringLit(_))
        }) && keyword(back(2), &["library_note", "library_note2"]);
        adaptation_note || library_note
    }

    /// Whether the command at `self.command_start` carries a modifier prefix
    /// before the current token: a modifier, or a declaration doc comment
    /// (one followed by another doc comment included, which Lean refuses at
    /// its end: `/-- a -/ /-! b -/ section`).
    pub(in crate::grammar) fn has_modifier_prefix(&self) -> bool {
        self.pos > self.command_start
            || matches!(
                self.doc_before(self.command_start),
                Some(DocBefore::Declaration { .. } | DocBefore::Stacked { .. })
            )
    }
}
