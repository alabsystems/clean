// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Termination clauses and their recovery boundaries.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

enum ParsedTerminationHint {
    TerminationBy(TerminationBy),
    DecreasingBy(DecreasingBy),
}

impl Parser {
    /// Parse `termination_by` and `decreasing_by` clauses that follow function definitions
    ///
    /// Lean 4 syntax variants:
    /// - `termination_by args => measure` (well-founded with params)
    /// - `termination_by measure` (well-founded, new syntax)
    /// - `termination_by structural x` (structural recursion on param x) - Lean 4.11.0+
    /// - `termination_by?` (query: show inferred termination)
    /// - `decreasing_by tactic`
    ///
    /// Reference: <https://lean-lang.org/doc/reference/latest/releases/v4.11.0/>
    ///
    /// These clauses are optional and may appear in any order after recursive definitions.
    pub(in crate::grammar) fn parse_termination_hints(&mut self) -> TerminationHints {
        let mut hints = TerminationHints::default();

        loop {
            let construct = match self.current_kind() {
                TokenKind::Ident(name) if name == "termination_by" || name == "termination_by?" => {
                    "termination_by"
                }
                TokenKind::Ident(name) if name == "decreasing_by" => "decreasing_by",
                _ => break,
            };

            let parsed = if construct == "termination_by" {
                self.parse_termination_by_clause(&hints)
                    .map(ParsedTerminationHint::TerminationBy)
            } else {
                self.parse_decreasing_by_clause(&hints)
                    .map(ParsedTerminationHint::DecreasingBy)
            };

            match parsed {
                Ok(ParsedTerminationHint::TerminationBy(hint)) => {
                    hints.termination_by = Some(hint);
                }
                Ok(ParsedTerminationHint::DecreasingBy(hint)) => {
                    hints.decreasing_by = Some(hint);
                }
                Err(err) => {
                    // File parsing is intentionally recovery-capable for IDEs, but
                    // a malformed optional hint must never be represented by a
                    // fabricated `Hole`. Record the exact failed construct, skip
                    // only its malformed tail, and omit the hint. The strict
                    // located file API rejects every recorded recovery.
                    let err = self.termination_hint_recovery_error(err);
                    self.defer_parser_recovery(construct, &err);
                    self.skip_to_termination_hint_boundary();
                    self.flush_pending_parser_recoveries();
                }
            }
        }
        hints
    }

    fn parse_termination_by_clause(
        &mut self,
        hints: &TerminationHints,
    ) -> Result<TerminationBy, ParseError> {
        let start_span = self.current_span();
        let query =
            matches!(self.current_kind(), TokenKind::Ident(name) if name == "termination_by?");
        self.advance();

        // Consume the clause keyword before reporting a duplicate. Recovery
        // must make progress even when the duplicate is immediately followed
        // by another hint or declaration boundary.
        if hints.termination_by.is_some() {
            return Err(self.termination_hint_error("duplicate `termination_by` clause"));
        }

        if query {
            self.ensure_termination_hint_boundary("`termination_by?` takes no arguments")?;
            return Ok(TerminationBy {
                span: start_span,
                kind: TerminationKind::Query,
                params: Vec::new(),
                measure: None,
            });
        }

        if !self.current().ident_escaped
            && matches!(self.current_kind(), TokenKind::Ident(name) if name == "structural")
        {
            self.advance();
            if self.peek_for_legacy_termination_arrow() {
                let mut params = Vec::new();
                while !matches!(self.current_kind(), TokenKind::FatArrow) {
                    let param = match self.current_kind().clone() {
                        TokenKind::Ident(param) => self.name_token(&param)?,
                        TokenKind::Underscore => SurfaceName::from_name(clean_kernel::Name::anon()),
                        _ => return Err(self.termination_hint_error(
                            "expected a parameter name or `_` before `=>` in `termination_by structural`",
                        )),
                    };
                    params.push(param);
                    self.advance();
                }
                // The loop exits only with `=>` as the current token.
                self.advance();
                let measure = self.termination_measure_expr()?;
                self.ensure_termination_hint_boundary(
                    "unexpected token after `termination_by structural` expression",
                )?;
                let param = match &measure {
                    SurfaceExpr::Ident(_, name) => name.clone(),
                    _ => SurfaceName::from_name(clean_kernel::Name::anon()),
                };
                return Ok(TerminationBy {
                    span: Span::new(start_span.start, measure.span().end),
                    kind: TerminationKind::Structural(param),
                    params,
                    measure: Some(Box::new(measure)),
                });
            }
            let (param_name, param_span) = match self.current_kind().clone() {
                TokenKind::Ident(param) => {
                    let param = self.name_token(&param)?;
                    let param_span = self.current_span();
                    self.advance();
                    (param, param_span)
                }
                _ => {
                    return Err(self.termination_hint_error(
                        "`termination_by structural` requires a parameter name",
                    ));
                }
            };
            self.ensure_termination_hint_boundary(
                "unexpected token after `termination_by structural` parameter",
            )?;
            return Ok(TerminationBy {
                span: Span::new(start_span.start, param_span.end),
                kind: TerminationKind::Structural(param_name),
                params: Vec::new(),
                measure: None,
            });
        }

        // Lean supports both the legacy `termination_by x y => measure`
        // spelling and the newer `termination_by measure` spelling.
        let has_arrow = self.peek_for_legacy_termination_arrow();
        let mut params = Vec::new();
        if has_arrow {
            while !matches!(self.current_kind(), TokenKind::FatArrow) {
                match self.current_kind().clone() {
                    TokenKind::Ident(param) => {
                        params.push(self.name_token(&param)?);
                        self.advance();
                    }
                    TokenKind::Underscore => {
                        params.push(SurfaceName::generated_path("_"));
                        self.advance();
                    }
                    _ => {
                        return Err(self.termination_hint_error(
                            "expected a parameter name or `_` before `=>` in `termination_by`",
                        ));
                    }
                }
            }
            if params.is_empty() {
                return Err(self.termination_hint_error(
                    "legacy `termination_by ... => ...` requires at least one parameter",
                ));
            }
            self.expect(&TokenKind::FatArrow)?;
        }

        let measure = self.termination_measure_expr()?;
        self.ensure_termination_hint_boundary(
            "unexpected token after `termination_by` measure expression",
        )?;
        let end_span = measure.span();
        Ok(TerminationBy {
            span: Span::new(start_span.start, end_span.end),
            kind: TerminationKind::WellFounded,
            params,
            measure: Some(Box::new(measure)),
        })
    }

    fn parse_decreasing_by_clause(
        &mut self,
        hints: &TerminationHints,
    ) -> Result<DecreasingBy, ParseError> {
        let start_span = self.current_span();
        self.advance();

        // As above, consume the keyword so duplicate-clause recovery cannot
        // redispatch the same token forever.
        if hints.decreasing_by.is_some() {
            return Err(self.termination_hint_error("duplicate `decreasing_by` clause"));
        }

        let tactic = self.termination_tactic_expr()?;
        self.ensure_termination_hint_boundary(
            "unexpected token after `decreasing_by` tactic body",
        )?;
        let end_span = tactic.span();
        Ok(DecreasingBy {
            span: Span::new(start_span.start, end_span.end),
            tactic: Box::new(tactic),
        })
    }

    /// Parse a termination measure expression (after `=>` or directly after `termination_by`).
    ///
    /// Delegates to the real expression parser. The expression parser naturally stops
    /// at termination hint boundaries (`termination_by`, `decreasing_by`) via the
    /// `is_atom_start()` guard in expr_app.rs, and at declaration keywords.
    fn termination_measure_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        if self.at_termination_hint_end(0) {
            return Err(
                self.termination_hint_error("`termination_by` requires a measure expression")
            );
        }
        self.expr()
    }

    /// Parse a `decreasing_by` tactic block.
    ///
    /// Delegates to the real tactic sequence parser. The tactic parser stops at
    /// termination hint boundaries (`termination_by`, `decreasing_by`) via the
    /// `at_tactic_end()` guard in expr_lambda_let.rs, and at declaration keywords.
    /// The result is wrapped in `SurfaceExpr::ByTactic` to match the `DecreasingBy`
    /// field type.
    fn termination_tactic_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let start_span = self.current_span();

        if self.at_termination_hint_end(0) {
            return Err(
                self.termination_hint_error("`decreasing_by` requires a non-empty tactic body")
            );
        }

        // The first tactic's column bounds the block, exactly as for `by`
        // (`by_body`): a new line at a lesser column ends it. Without it, a
        // `decreasing_by` on a `where` helper swallows the next helper's
        // header as a tactic.
        let first_tac_col = self.current().col;
        self.push_indent_for(first_tac_col, "decreasing_by tactic block");
        let tactics = self.tactic_seq();
        self.pop_indent();
        match tactics {
            Ok(tactics) if !tactics.is_empty() => {
                let end_span = tactics.last().map_or(start_span, |t| t.span());
                Ok(SurfaceExpr::ByTactic(
                    Span::new(start_span.start, end_span.end),
                    tactics,
                ))
            }
            Ok(_) => {
                Err(self.termination_hint_error("`decreasing_by` requires a non-empty tactic body"))
            }
            Err(err) => Err(err),
        }
    }

    fn termination_hint_error(&self, message: impl Into<String>) -> ParseError {
        ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current().col as usize,
            message: message.into(),
        }
    }

    /// Recovery diagnostics have a strict line/column/byte contract even
    /// though legacy `ParseError` sites inconsistently use absolute bytes in
    /// `col`. Re-anchor nested expression/tactic errors to the parser's current
    /// token before recording this hint-local recovery.
    fn termination_hint_recovery_error(&self, err: ParseError) -> ParseError {
        match err {
            ParseError::UnexpectedToken { message, .. } => ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message,
            },
            other => other,
        }
    }

    fn ensure_termination_hint_boundary(&self, message: &str) -> Result<(), ParseError> {
        // A hint on a `where` helper that is not the last one ends where the
        // next helper's header starts.
        if self.at_termination_hint_end(0) || self.at_next_where_def_start() {
            Ok(())
        } else {
            Err(self.termination_hint_error(message))
        }
    }

    /// Skip a malformed hint tail without consuming the next hint/declaration.
    fn skip_to_termination_hint_boundary(&mut self) {
        // Declaration and hint keywords are hard boundaries even after an
        // unmatched opener. Carrying delimiter depth across a failed parse can
        // otherwise swallow the rest of the file (`termination_by ( => ...`
        // followed by `def next`). These keywords cannot legally continue a
        // measure/tactic at any nesting depth, so stopping is unambiguous.
        while !self.at_termination_hint_end(0) {
            self.advance();
        }
    }

    /// Check if we're at the end of a termination hint expression
    pub(in crate::grammar) fn at_termination_hint_end(&self, depth: usize) -> bool {
        if depth > 0 {
            return false;
        }
        // Check for next termination hint or declaration start
        if let TokenKind::Ident(name) = self.current_kind() {
            if name == "termination_by" || name == "termination_by?" || name == "decreasing_by" {
                return true;
            }
        }
        self.is_decl_start()
            || matches!(
                self.current_kind(),
                TokenKind::Where | TokenKind::Eof | TokenKind::End
            )
    }

    /// Determine whether `termination_by` uses the legacy parameter syntax.
    ///
    /// The legacy prefix is narrowly `ident-or-underscore+ =>`. Looking for an
    /// arbitrary top-level `=>` is unsound because valid modern measures may
    /// themselves contain one (`fun x => x`, `match x with | ... => ...`).
    /// Used to distinguish (#1132):
    /// - `termination_by x y => measure` (old syntax with params)
    /// - `termination_by measure` (new syntax without =>)
    fn peek_for_legacy_termination_arrow(&self) -> bool {
        let mut offset = 0usize;
        let mut params = 0usize;
        loop {
            match self.peek_kind(offset) {
                Some(TokenKind::Ident(_)) | Some(TokenKind::Underscore) => {
                    params += 1;
                    offset += 1;
                }
                Some(TokenKind::FatArrow) => return params > 0,
                _ => return false,
            }
        }
    }
}
