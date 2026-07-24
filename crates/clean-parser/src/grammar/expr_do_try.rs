// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Try/catch/finally and refutable let parsing for do-notation.
//!
//! Extracted from expr_do.rs to maintain the 500-line file limit.
//!
//! - `parse_do_try`: Parses `try doSeq [catch ...]* [finally ...]?`
//! - `parse_do_catch_binder`: Parses `catch e [: ExcType] => doSeq`
//! - `parse_do_catch_match`: Parses `catch | pat => doSeq` (desugars to match)
//! - `parse_do_let_else`: Parses `let pat <- action | fallback`
//! - `parse_do_expr_or_bind`: Parses expression statement or bare bind
//! - `is_at_refutable_pattern_start`: Detects constructor patterns
//!
//! Reference: ~/lean4-ref/src/Lean/Parser/Do.lean

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse an expression within a do-element while preserving same-indent
    /// newline boundaries between sibling elements.
    pub(super) fn parse_do_elem_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let saved = self.stop_app_at_newline_outer_indent;
        self.stop_app_at_newline_outer_indent = true;
        let expr = self.expr();
        self.stop_app_at_newline_outer_indent = saved;
        expr
    }

    /// Check if the current position looks like the start of a refutable pattern
    /// (constructor application `.ident` or `Ident.ident`), as opposed to a
    /// simple variable binding.
    pub(super) fn is_at_refutable_pattern_start(&self) -> bool {
        match self.current_kind() {
            // `.some`, `.none`, `.ok`, `.err`, etc.
            TokenKind::Dot => true,
            // Could be `Ctor arg` — check for uppercase first letter
            TokenKind::Ident(s) => s.starts_with(|c: char| c.is_uppercase()) || s.contains('.'),
            _ => false,
        }
    }

    /// Parse a do-block expression, bare bind, or reassignment: `e`, `x <- e`, or `x := e`
    ///
    /// If the expression is an identifier followed by `<-`, this is a bare bind.
    /// If the expression is an identifier followed by `:=`, this is a reassignment
    /// (for mutable variables introduced by `let mut`).
    /// If a parenthesized pattern is followed by `:=`, this is a pattern reassignment.
    /// Otherwise, it's a plain expression statement.
    pub(super) fn parse_do_expr_or_bind(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Save position to try identifier-arrow or identifier-assign pattern
        let saved_pos = self.pos;

        // Try: pattern reassignment `(a, b) := expr`
        // Detect parenthesized tuple pattern followed by `:=`
        if matches!(self.current_kind(), TokenKind::LParen) {
            if let Some(pat_reassign) = self.try_parse_do_pattern_reassign(start_span)? {
                return Ok(pat_reassign);
            }
            // Not a pattern reassign — restore and fall through
            self.pos = saved_pos;
        }

        // Try: `name <- expr` (bare bind without `let`) or `name := expr` (reassignment)
        if let TokenKind::Ident(_) = self.current_kind() {
            let name = self.ident()?;
            if self.eat(&TokenKind::LeftArrow) {
                let val = self.parse_do_elem_expr()?;
                let span = start_span.merge(val.span());
                let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
                return Ok(DoElem::Bind(span, binder, Box::new(val)));
            }
            if self.eat(&TokenKind::ColonEq) {
                // `name := expr` — mutable variable reassignment
                let val = self.parse_do_elem_expr()?;
                let span = start_span.merge(val.span());
                return Ok(DoElem::Reassign(span, name, Box::new(val)));
            }
            // Not a bind or reassign — restore position and parse as expression
            self.pos = saved_pos;
        }

        let expr = self.parse_do_elem_expr()?;
        let span = start_span.merge(expr.span());
        Ok(DoElem::Expr(span, Box::new(expr)))
    }

    /// Try to parse a pattern reassignment: `(a, b) := expr`
    ///
    /// Returns `Some(DoElem::PatternReassign)` if successful, `None` if this
    /// isn't a pattern reassignment (caller should restore position).
    ///
    /// Reference: Lean 4 `doReassign` with `letPatDecl` in `src/Lean/Parser/Do.lean:104-105`
    fn try_parse_do_pattern_reassign(
        &mut self,
        start_span: Span,
    ) -> Result<Option<DoElem>, ParseError> {
        let saved_pos = self.pos;
        // Try parsing a pattern (will consume the `(a, b)` tuple form)
        if let Ok(pat) = self.pattern() {
            if self.eat(&TokenKind::ColonEq) {
                let val = self.parse_do_elem_expr()?;
                let span = start_span.merge(val.span());
                return Ok(Some(DoElem::PatternReassign(span, pat, Box::new(val))));
            }
        }
        // Not a pattern reassignment — restore position
        self.pos = saved_pos;
        Ok(None)
    }

    /// Parse a do-element sequence (used for branches of if/for/match in do blocks).
    ///
    /// Handles both braced `{ ... }` and unbraced (indentation-terminated) sequences.
    pub(super) fn parse_do_seq(&mut self) -> Result<Vec<DoElem>, ParseError> {
        self.parse_do_seq_tracking_semis().map(|(elems, _)| elems)
    }

    /// [`Self::parse_do_seq`], additionally reporting whether any top-level
    /// `;` separator was consumed BETWEEN elements — the do-if branch parser
    /// keys its historical `;`-terminates-the-branch reading on it (B94).
    pub(super) fn parse_do_seq_tracking_semis(
        &mut self,
    ) -> Result<(Vec<DoElem>, bool), ParseError> {
        let braced = self.eat(&TokenKind::LBrace);
        if !braced {
            let first_elem_col = self.current().col;
            self.push_indent_for(first_elem_col, "do sequence");
        }

        let mut semi_joined = false;
        let result = (|| {
            let mut elems = Vec::new();

            loop {
                if braced {
                    if self.eat(&TokenKind::RBrace) {
                        break;
                    }
                } else if self.at_do_seq_end() {
                    break;
                }

                let elem_span = self.current_span();
                let elem = self.parse_do_elem(elem_span)?;
                elems.push(elem);

                let mut ate_semi = false;
                while self.eat(&TokenKind::Semicolon) {
                    ate_semi = true;
                }
                // Only a `;` that actually JOINS two elements counts (a
                // trailing one before the sequence end does not).
                if ate_semi
                    && !(braced && matches!(self.current_kind(), TokenKind::RBrace))
                    && (braced || !self.at_do_seq_end())
                {
                    semi_joined = true;
                }
            }

            if elems.is_empty() {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current().col as usize,
                    message: "empty do sequence in branch".into(),
                });
            }

            Ok(elems)
        })();

        if !braced {
            if let Err(err) = &result {
                self.defer_parser_recovery("do sequence", err);
            }
            self.pop_indent();
        }

        result.map(|elems| (elems, semi_joined))
    }

    /// Check if we're at the end of a nested do-sequence (branch body).
    /// Stops at `else`, `|` (next match arm), `catch`, `finally`,
    /// and standard do-elem-end tokens.
    fn at_do_seq_end(&self) -> bool {
        matches!(
            self.current_kind(),
            TokenKind::Else | TokenKind::Pipe | TokenKind::Eof
        ) || matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "catch" || s == "finally")
            || self.at_do_elem_end()
    }

    /// Parse `try doSeq [catch ...]* [finally ...]?` within a do block.
    ///
    /// Lean 4 grammar:
    ///   `doTry := "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally`
    ///
    /// At least one `catch` or `finally` clause is required.
    ///
    /// Reference: ~/lean4-ref/src/Lean/Parser/Do.lean:201-202
    pub(super) fn parse_do_try(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Set stop_at_catch_finally so the expression parser treats `catch` and
        // `finally` as clause boundaries instead of application arguments.
        // This enables flat forms like `do try pure 1 catch e => pure 0`. (#2969)
        // The flag stays active through catch/finally body parsing too, so
        // multiple catch clauses on one line work correctly.
        let saved_stop = self.stop_at_catch_finally;
        self.stop_at_catch_finally = true;

        // Parse the try body (a do-element sequence)
        let try_body = self.parse_do_seq()?;

        // Parse zero or more catch clauses
        let mut catches = Vec::new();
        while matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "catch") {
            let catch_span = self.current_span();
            self.advance(); // consume `catch`

            // Check for pattern-match catch: `catch | pat => doSeq`
            if self.eat(&TokenKind::Pipe) {
                // Pattern-match form: desugar to `catch __x => match __x with | pat => doSeq`
                let catch_clause = self.parse_do_catch_match(catch_span)?;
                catches.push(catch_clause);
            } else {
                // Binder form: `catch e [: ExcType] => doSeq`
                let catch_clause = self.parse_do_catch_binder(catch_span)?;
                catches.push(catch_clause);
            }
        }

        // Parse optional finally clause
        let finally_body = if matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "finally")
        {
            self.advance(); // consume `finally`
            Some(self.parse_do_seq()?)
        } else {
            None
        };

        // Restore the flag after all try/catch/finally parsing is complete
        self.stop_at_catch_finally = saved_stop;

        // At least one catch or finally is required
        if catches.is_empty() && finally_body.is_none() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "try block requires at least one `catch` or `finally` clause".into(),
            });
        }

        let end_span = finally_body
            .as_ref()
            .and_then(|b: &Vec<DoElem>| b.last())
            .or_else(|| catches.last().and_then(|c| c.body.last()))
            .map_or(start_span, |e: &DoElem| e.span());

        Ok(DoElem::TryCatch(
            start_span.merge(end_span),
            try_body,
            catches,
            finally_body,
        ))
    }

    /// Parse `catch e [: ExcType] => doSeq` — binder form.
    fn parse_do_catch_binder(&mut self, catch_span: Span) -> Result<DoCatchClause, ParseError> {
        // Parse exception binder name (or `_`)
        let binder = match self.current_kind() {
            TokenKind::Ident(_) => self.ident()?,
            TokenKind::Underscore => {
                self.advance();
                "_".to_string()
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!(
                        "expected identifier in catch clause, got {:?}",
                        self.current_kind()
                    ),
                })
            }
        };

        // Optional type annotation: `: ExcType`
        let exc_type = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        self.expect(&TokenKind::FatArrow)?;
        let body = self.parse_do_seq()?;

        let end_span = body.last().map_or(catch_span, |e: &DoElem| e.span());
        Ok(DoCatchClause {
            span: catch_span.merge(end_span),
            binder,
            exc_type,
            body,
        })
    }

    /// Parse `catch | pat1 => doSeq | pat2 => doSeq` — pattern-match form.
    ///
    /// Desugars to `catch __catch_x => match __catch_x with | pat1 => doSeq | pat2 => doSeq`
    /// (matching Lean 4 behavior).
    fn parse_do_catch_match(&mut self, catch_span: Span) -> Result<DoCatchClause, ParseError> {
        // Parse match alternatives (already consumed the first `|`)
        let mut arms = Vec::new();
        loop {
            let arm_span = self.current_span();
            let mut patterns = vec![self.pattern_with_or()?];
            while self.eat(&TokenKind::Comma) {
                patterns.push(self.pattern_with_or()?);
            }
            self.expect(&TokenKind::FatArrow)?;
            let body = self.parse_do_seq()?;
            let end = body.last().map_or(arm_span, |e| e.span());
            arms.push(DoMatchArm {
                span: arm_span.merge(end),
                patterns,
                body,
            });
            if !self.eat(&TokenKind::Pipe) {
                break;
            }
        }

        // Desugar to: catch __catch_x => match __catch_x with | arm1 | arm2 ...
        let fresh_name = "__catch_x".to_string();
        let match_discr = SurfaceExpr::Ident(catch_span, fresh_name.clone());
        let match_elem = DoElem::Match(catch_span, vec![match_discr], arms);

        let body = vec![match_elem];
        let end_span = body.last().map_or(catch_span, |e: &DoElem| e.span());
        Ok(DoCatchClause {
            span: catch_span.merge(end_span),
            binder: fresh_name,
            exc_type: None,
            body,
        })
    }

    /// Parse refutable do-pattern with fallback:
    /// `let pat <- action | fallback` or `let pat := value | fallback`.
    ///
    /// Called when `parse_do_let` detects that the binding target is a pattern
    /// (not a simple identifier) followed by a fallback clause.
    ///
    /// Desugars in elaboration to:
    /// 1. `let __x <- action`
    /// 2. `match __x with | pat => rest | _ => fallback`
    pub(super) fn parse_do_let_else(
        &mut self,
        start_span: Span,
        pat: SurfacePattern,
        action: SurfaceExpr,
    ) -> Result<DoElem, ParseError> {
        let fallback = self.parse_do_seq()?;
        let end_span = fallback.last().map_or(start_span, |e: &DoElem| e.span());
        Ok(DoElem::LetElse(
            start_span.merge(end_span),
            pat,
            Box::new(action),
            fallback,
        ))
    }

    /// Try to parse a refutable pattern let:
    /// `let pat <- action | fallback` or `let pat := value | fallback`
    ///
    /// Returns `Some(DoElem)` if a refutable pattern was successfully parsed,
    /// `None` if the current position doesn't start a refutable pattern.
    /// Restores parser position on failure.
    pub(super) fn try_parse_do_let_refutable(
        &mut self,
        start_span: Span,
    ) -> Result<Option<DoElem>, ParseError> {
        if !self.is_at_refutable_pattern_start() {
            return Ok(None);
        }

        let saved_pos = self.pos;
        if let Ok(pat) = self.pattern() {
            if self.eat(&TokenKind::LeftArrow) {
                let action = self.parse_do_elem_expr()?;
                // Check for `|` fallback
                if self.eat(&TokenKind::Pipe) {
                    return self.parse_do_let_else(start_span, pat, action).map(Some);
                }
                // No `|` — treat as regular bind if pattern is a simple variable
                if let SurfacePattern::Var(name) = pat {
                    let span = start_span.merge(action.span());
                    let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
                    return Ok(Some(DoElem::Bind(span, binder, Box::new(action))));
                }
                // Constructor pattern without fallback — error
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "refutable let pattern requires `| fallback` clause".into(),
                });
            }
            if self.eat(&TokenKind::ColonEq) {
                let value = self.parse_do_elem_expr()?;
                if self.eat(&TokenKind::Pipe) {
                    return self.parse_do_let_else(start_span, pat, value).map(Some);
                }
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "refutable let pattern requires `| fallback` clause".into(),
                });
            }
        }
        // Pattern parsing failed or no `<-` — restore and return None
        self.pos = saved_pos;
        Ok(None)
    }

    /// Parse `unless cond do body` within a do block.
    ///
    /// Desugars in the parser to `if cond then pure () else body`, matching
    /// Lean 4's macro expansion of `unless` (`if cond then pure PUnit.unit else
    /// body`). The "skip" branch (cond true ⇒ do NOT run body) is a *sequenced*
    /// `pure ()`, NOT `return ()`: inside a block with a later `return`, an early
    /// `return ()` is treated as an early return of `Unit`, exiting the whole
    /// block (Unit vs the block's result type).
    ///
    /// Reference: Lean 4 `doUnless` in `src/Lean/Parser/Do.lean`
    pub(super) fn parse_do_unless(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Set forbid_do so that `do` is not consumed as a term prefix (#1815)
        let saved_forbid_do = self.forbid_do;
        self.forbid_do = true;
        let cond = self.expr()?;
        self.forbid_do = saved_forbid_do;
        if !self.eat(&TokenKind::Do) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected `do` in unless expression, got {:?}",
                    self.current_kind()
                ),
            });
        }
        let body = self.parse_do_seq()?;
        let end_span = body.last().map_or(start_span, |e| e.span());
        // Desugar: unless cond do body → if cond then (pure ()) else body.
        // The skip branch must CONTINUE the block (sequenced `pure ()`), never
        // early-return — see the doc comment above.
        let pure_unit = SurfaceExpr::App(
            start_span,
            Box::new(SurfaceExpr::Ident(start_span, "pure".to_string())),
            vec![SurfaceArg::positional(SurfaceExpr::Ident(
                start_span,
                "Unit.unit".to_string(),
            ))],
        );
        let then_branch = vec![DoElem::Expr(start_span, Box::new(pure_unit))];
        Ok(DoElem::If(
            start_span.merge(end_span),
            Box::new(cond),
            then_branch,
            Some(body),
        ))
    }

    /// Parse `when cond do body` within a do block.
    ///
    /// Desugars in the parser to `if cond then body else pure ()`, matching
    /// Lean 4's macro expansion of `when` (`if cond then body else pure
    /// PUnit.unit`) — the mirror of [`Self::parse_do_unless`]. As with `unless`,
    /// the "skip" branch (cond false ⇒ do NOT run body) is a *sequenced*
    /// `pure ()`, NOT `return ()`: inside a block with a later `return`, an early
    /// `return ()` exits the whole block with `Unit`.
    ///
    /// Reference: Lean 4 `doWhen`-style expansion in `src/Lean/Parser/Do.lean`
    pub(super) fn parse_do_when(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Set forbid_do so that `do` is not consumed as a term prefix (#1815)
        let saved_forbid_do = self.forbid_do;
        self.forbid_do = true;
        let cond = self.expr()?;
        self.forbid_do = saved_forbid_do;
        if !self.eat(&TokenKind::Do) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected `do` in when expression, got {:?}",
                    self.current_kind()
                ),
            });
        }
        let body = self.parse_do_seq()?;
        let end_span = body.last().map_or(start_span, |e| e.span());
        // Desugar: when cond do body → if cond then body else (pure ()).
        // The else (skip) branch must CONTINUE the block (sequenced `pure ()`),
        // never early-return — see the doc comment above.
        let pure_unit = SurfaceExpr::App(
            start_span,
            Box::new(SurfaceExpr::Ident(start_span, "pure".to_string())),
            vec![SurfaceArg::positional(SurfaceExpr::Ident(
                start_span,
                "Unit.unit".to_string(),
            ))],
        );
        let else_branch = vec![DoElem::Expr(start_span, Box::new(pure_unit))];
        Ok(DoElem::If(
            start_span.merge(end_span),
            Box::new(cond),
            body,
            Some(else_branch),
        ))
    }

    /// Parse `repeat body` within a do block.
    ///
    /// Reference: Lean 4 `doRepeat` in `src/Lean/Parser/Do.lean`
    pub(super) fn parse_do_repeat(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // `do` keyword is optional
        self.eat(&TokenKind::Do);
        let body = self.parse_do_seq()?;
        let end_span = body.last().map_or(start_span, |e| e.span());
        Ok(DoElem::Repeat(start_span.merge(end_span), body))
    }

    /// Parse `while cond do body` within a do block.
    ///
    /// Reference: Lean 4 `doWhile` in `src/Lean/Parser/Do.lean`
    pub(super) fn parse_do_while(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        // Set forbid_do so that `do` is not consumed as a term prefix (#1815)
        let saved_forbid_do = self.forbid_do;
        self.forbid_do = true;
        let cond = self.expr()?;
        self.forbid_do = saved_forbid_do;
        // Expect `do` keyword
        if !self.eat(&TokenKind::Do) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected `do` in while loop, got {:?}", self.current_kind()),
            });
        }
        let body = self.parse_do_seq()?;
        let end_span = body.last().map_or(start_span, |e| e.span());
        Ok(DoElem::While(
            start_span.merge(end_span),
            Box::new(cond),
            body,
        ))
    }

    /// Parse `dbg_trace msg` within a do block.
    ///
    /// The message is a single expression. The continuation is the rest of
    /// the do block (handled by the sequencing in `elab_do_elems`).
    ///
    /// Reference: Lean 4 `doDbgTrace` in `src/Lean/Parser/Do.lean`
    pub(super) fn parse_do_dbg_trace(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        let msg = self.parse_do_elem_expr()?;
        let end_span = msg.span();
        Ok(DoElem::DbgTrace(start_span.merge(end_span), Box::new(msg)))
    }
}
