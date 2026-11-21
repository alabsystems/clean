// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{IndentContext, Parser};
use crate::lexer::{Token, TokenKind};
use crate::surface::Span;
use crate::{ParseError, SurfaceName};

static EMPTY_EOF: Token = Token {
    kind: TokenKind::Eof,
    span: Span { start: 0, end: 0 },
    ident_escaped: false,
    lean_keyword: false,
    preceded_by_newline: false,
    col: 0,
    line: 1,
};

impl Parser {
    // Token access

    pub(super) fn current(&self) -> &Token {
        self.token_or_eof(self.pos)
    }

    fn token_or_eof(&self, index: usize) -> &Token {
        self.tokens
            .get(index)
            .or_else(|| self.tokens.last())
            .unwrap_or(&EMPTY_EOF)
    }

    pub(super) fn current_kind(&self) -> &TokenKind {
        if !self.mixfix_operand_ends.is_empty() && self.at_mixfix_operand_end(0) {
            return &TokenKind::Eof;
        }
        &self.current().kind
    }

    pub(super) fn current_span(&self) -> Span {
        self.current().span
    }

    /// 1-based line number of the current token.
    pub(super) fn current_line(&self) -> usize {
        self.current().line as usize
    }

    /// The current `Ident` token, spelled `text`, as a NAME: one that is
    /// bound (a binder, pattern variable, `let`, hypothesis or field name) or
    /// declared, or any other identifier Lean's `ident` parser reads.
    ///
    /// A token Lean 4.8.0 scans as a keyword (`Token::lean_keyword`) is
    /// refused: Lean's `ident` never matches a keyword, so `fun (nomatch :
    /// Nat → Nat) => …` and `def nomatch := …` are Lean syntax errors, and
    /// accepting them let the binding capture the keyword (measured
    /// 2026-09-26: `nomatch a + b` computed with the binder).
    pub(super) fn name_token(&self, text: &str) -> Result<SurfaceName, ParseError> {
        if self.current().lean_keyword {
            return Err(self.keyword_as_name_error(text));
        }
        Ok(SurfaceName::component(text, self.current().ident_escaped))
    }

    /// The error for the Lean keyword `text` where a name is required.
    pub(super) fn keyword_as_name_error(&self, text: &str) -> ParseError {
        ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current().col as usize,
            message: format!(
                "expected identifier, got `{text}`, a keyword in Lean 4.8.0 \
                 (a name spelled so is written `«{text}»`)"
            ),
        }
    }

    /// The current `Ident` token, spelled `text`, as a term-position
    /// REFERENCE. A Lean keyword is kept (Clean's recognizers give `nomatch
    /// e` its meaning) but marked, so it resolves to no local and no
    /// constant ([`SurfaceName::into_lean_keyword`]).
    pub(super) fn reference_token(&self, text: &str) -> SurfaceName {
        let name = SurfaceName::component(text, self.current().ident_escaped);
        if self.current().lean_keyword {
            name.into_lean_keyword()
        } else {
            name
        }
    }

    pub(super) fn advance(&mut self) -> &Token {
        if self.pos < self.tokens.len().saturating_sub(1) {
            self.pos += 1;
        }
        // Return reference to token we just passed
        self.token_or_eof(self.pos.saturating_sub(1))
    }

    pub(super) fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(self.current_kind()) == std::mem::discriminant(kind)
            && (matches!(kind, TokenKind::Eof) || !self.longer_notation_atom_at(1, 0))
    }

    pub(super) fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    pub(super) fn expect(&mut self, kind: &TokenKind) -> Result<&Token, ParseError> {
        if self.check(kind) {
            Ok(self.advance())
        } else {
            Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!("expected {:?}, got {:?}", kind, self.current_kind()),
            })
        }
    }

    /// Peek at token kind at offset from current position
    pub(super) fn peek_kind(&self, offset: usize) -> Option<&TokenKind> {
        if !self.mixfix_operand_ends.is_empty() && self.at_mixfix_operand_end(offset) {
            return Some(&TokenKind::Eof);
        }
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    /// The whole token `offset` ahead, when the caller needs more than its
    /// kind — `col` / `preceded_by_newline` for a line-discipline decision.
    pub(super) fn peek_token(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.pos + offset)
    }

    /// True when the `Dot` token at `self.pos` is a *contiguous* qualified-name
    /// separator: the dot immediately follows the previous token (no whitespace
    /// gap) and the following identifier immediately follows the dot. This
    /// distinguishes a qualified name like `Option.none` (written with no
    /// surrounding spaces) from a constructor applied to a leading-dot pattern
    /// argument such as `some .arcRef`, where the space before `.` means
    /// `.arcRef` is a separate argument, not part of the head name.
    ///
    /// Byte-adjacency is read off the lexer spans (`[start, end)` byte ranges):
    /// `prev.end == dot.start` and `dot.end == ident.start` iff no source
    /// characters (spaces/newlines/comments) sit between them.
    pub(super) fn dot_is_contiguous_qualifier(&self) -> bool {
        if !matches!(self.current_kind(), TokenKind::Dot) {
            return false;
        }
        let dot = self.current();
        let prev_adjacent = self
            .pos
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .is_some_and(|prev| prev.span.end == dot.span.start);
        let next_adjacent = self.tokens.get(self.pos + 1).is_some_and(|next| {
            matches!(next.kind, TokenKind::Ident(_)) && dot.span.end == next.span.start
        });
        prev_adjacent && next_adjacent
    }

    /// True when the current token starts exactly where the previous token
    /// ended — no whitespace or comment between them (Lean's
    /// `checkNoWsBefore`). False at the start of input.
    pub(super) fn at_token_glued_to_previous(&self) -> bool {
        self.pos
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .is_some_and(|prev| prev.span.end == self.current().span.start)
    }

    // Indentation stack helpers

    pub(super) fn push_indent_for(&mut self, col: u32, construct: &str) {
        let line = self.current_line();
        let byte = self.current_span().start;
        self.indent_stack.push(col);
        self.indent_context_stack.push(IndentContext {
            construct: construct.to_owned(),
            line,
            column: col,
            byte,
        });
    }

    /// Pop the most recent indentation reference.
    pub(super) fn pop_indent(&mut self) {
        self.indent_stack.pop();
        self.indent_context_stack.pop();
    }

    /// Lean's `withPosition p`: run `parse` with the CURRENT token's column
    /// saved as the position that `checkColGt` / `checkColGe` compare
    /// against, restoring the enclosing position afterwards (on error too).
    /// Lean's `manyIndent` / `sepByIndent` are `withPosition` around their
    /// item loop, so the saved column is the first item's
    /// (`Lean/Parser/Extra.lean:199-204`).
    pub(super) fn with_position<T>(
        &mut self,
        construct: &str,
        parse: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let col = self.current().col;
        self.push_indent_for(col, construct);
        let result = parse(self);
        self.pop_indent();
        result
    }

    /// Lean's `withoutPosition p`: run `parse` with no saved position, so
    /// `checkColGt` / `checkColGe` pass until a nested `withPosition` saves
    /// one again (see [`Parser::position_suppressed_at`]).
    pub(super) fn without_position<T>(&mut self, parse: impl FnOnce(&mut Self) -> T) -> T {
        let saved = self.position_suppressed_at;
        self.position_suppressed_at = Some(self.indent_stack.len());
        let result = parse(self);
        self.position_suppressed_at = saved;
        result
    }

    /// Whether the parse is inside a bracketed term group with no
    /// indentation frame pushed since it opened (Lean's `withoutPosition`;
    /// see [`Parser::position_suppressed_at`]). Column-based stops must not
    /// fire here: the group's closer is the only boundary.
    pub(super) fn position_suppressed(&self) -> bool {
        self.position_suppressed_at == Some(self.indent_stack.len())
    }

    /// Lean's `checkColGt` (`Lean/Parser/Basic.lean`, `checkColGtFn`): the
    /// current token's column is strictly greater than the saved position's,
    /// or no position is saved. Unlike [`Parser::at_dedent`] it does not ask
    /// whether the token begins a line — Lean compares columns only.
    pub(super) fn col_gt_saved_position(&self) -> bool {
        if self.position_suppressed() {
            return true;
        }
        self.indent_stack
            .last()
            .is_none_or(|&saved_col| self.current().col > saved_col)
    }

    /// Current token is on a new line at a column strictly less than the
    /// block's reference column — the block has ended (dedent).
    /// Matches Lean 4: block terminates when a new-line token's column < reference.
    /// Never fires inside a bracketed group that cleared the position
    /// ([`Parser::position_suppressed`]), as Lean's `checkColGe` passes when
    /// no position is saved.
    pub(super) fn at_dedent(&self) -> bool {
        if self.position_suppressed() {
            return false;
        }
        if let Some(&block_col) = self.indent_stack.last() {
            let tok = self.current();
            // Only trigger dedent on new lines — same-line tokens are always part of the block
            tok.preceded_by_newline && tok.col < block_col
        } else {
            false
        }
    }
}
