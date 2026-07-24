// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{IndentContext, Parser};
use crate::lexer::{Token, TokenKind};
use crate::surface::Span;
use crate::ParseError;

impl Parser {
    // Token access

    pub(super) fn current(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .unwrap_or_else(|| self.tokens.last().expect("tokens should have at least EOF"))
    }

    pub(super) fn current_kind(&self) -> &TokenKind {
        &self.current().kind
    }

    pub(super) fn current_span(&self) -> Span {
        self.current().span
    }

    /// 1-based line number of the current token.
    pub(super) fn current_line(&self) -> usize {
        self.current().line as usize
    }

    pub(super) fn advance(&mut self) -> &Token {
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        // Return reference to token we just passed
        &self.tokens[self.pos.saturating_sub(1)]
    }

    pub(super) fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(self.current_kind()) == std::mem::discriminant(kind)
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
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
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

    /// Current token is on a new line at a column strictly less than the
    /// block's reference column — the block has ended (dedent).
    /// Matches Lean 4: block terminates when a new-line token's column < reference.
    pub(super) fn at_dedent(&self) -> bool {
        if let Some(&block_col) = self.indent_stack.last() {
            let tok = self.current();
            // Only trigger dedent on new lines — same-line tokens are always part of the block
            tok.preceded_by_newline && tok.col < block_col
        } else {
            false
        }
    }
}
