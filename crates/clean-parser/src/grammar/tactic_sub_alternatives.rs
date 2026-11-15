// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `|`-alternative tactics of the tactic sub-grammar: `first`, `solve`
//! and the tactic `match`. Lean 4.8 bounds each one's alternatives by the
//! column of its first `|` (`withPosition((colGe "| " …)+)`), so a `|` left
//! of it belongs to an enclosing construct.
//!
//! Split out of `tactic_sub_rw_simp.rs` to keep that file under the
//! 500-line limit of `.claude/rules/rust_excellence.md`; every item here is
//! a method on [`Parser`].

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{Span, SurfaceTactic, TacticMatchArm};
use crate::ParseError;

impl Parser {
    /// Eat the `|` that opens the next alternative of a `first` / `solve`
    /// block whose first `|` sat at column `arm_col`.
    ///
    /// Both are `withPosition((colGe "| " tacticSeq)+)` in Lean 4.8: the
    /// position is the first `|`, and a `|` left of it belongs to an
    /// enclosing construct — the next `| ctor =>` of a surrounding `cases …
    /// with`, as in trust-ir's `TransformCorrectness.lean` (`… <;> first |
    /// … | …` ending a `| some lanes =>` arm right before `| nullPtr =>`).
    fn eat_alternative_pipe(&mut self, arm_col: u32) -> bool {
        if !self.check(&TokenKind::Pipe) || self.current().col < arm_col {
            return false;
        }
        self.advance();
        true
    }

    /// Parse `first | tac1 | tac2 | ...`
    pub(crate) fn parse_tactic_first(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let mut branches = Vec::new();

        // Expect at least one `| tac_seq`
        let arm_col = self.current().col;
        while self.eat_alternative_pipe(arm_col) {
            let tacs = self.tactic_seq_until_pipe()?;
            branches.push(tacs);
        }

        if branches.is_empty() {
            // If no pipe, treat the next tactic as a single branch
            let tac = self.tactic()?;
            branches.push(vec![tac]);
        }

        Ok(SurfaceTactic::First(start, branches))
    }

    /// Parse `solve | tac1 | tac2 | ...`.
    ///
    /// Lean 4.8 (`Init/NotationExtra.lean`): `syntax "solve" withPosition((colGe
    /// "| " tacticSeq)+)` with `macro_rules | `(tactic| solve $[| $ts]*) =>
    /// `(tactic| focus first $[| ($ts); done]*)` — the first alternative that
    /// CLOSES the focused goal wins. Desugared to exactly that expansion, so
    /// `first`, `focus` and `done` keep their own elaboration.
    pub(crate) fn parse_tactic_solve(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let mut branches = Vec::new();
        let arm_col = self.current().col;
        while self.eat_alternative_pipe(arm_col) {
            let mut tacs = self.tactic_seq_until_pipe()?;
            tacs.push(SurfaceTactic::Named {
                span: start,
                name: "done".to_string(),
                args: Vec::new(),
            });
            branches.push(tacs);
        }
        if branches.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected `|` after `solve`, got {:?}", self.current_kind()),
            });
        }
        Ok(SurfaceTactic::Focus(
            start,
            vec![SurfaceTactic::First(start, branches)],
        ))
    }

    /// Parse `match discr1, discr2, ... with | pat => tac_seq | ...` in tactic mode
    ///
    /// Like expression-mode match but arm bodies are tactic sequences.
    /// Reference: Lean 4 `Lean.Parser.Tactic.match` in Tactic.lean
    pub(crate) fn parse_tactic_match(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        // Parse discriminant(s). Lean's `matchDiscr := optional (atomic
        // (binderIdent " : ")) term`: `match hOps : op.inst.operands with`
        // (trust-ir `VectorDialectProps.lean`) binds `hOps : e = pat` per arm.
        // The annotated form is carried for a single discriminant, as the
        // term-mode match does; several annotated discriminants are refused
        // here, loudly, rather than dropping an equation.
        let hyp = self.parse_match_discr_hyp()?;
        let mut discrs = vec![self.parse_tactic_expr()?];
        while self.eat(&TokenKind::Comma) {
            if self.parse_match_discr_hyp()?.is_some() || hyp.is_some() {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "an annotated (`h : e`) discriminant of a tactic `match` is \
                              supported only as its single discriminant"
                        .to_string(),
                });
            }
            discrs.push(self.parse_tactic_expr()?);
        }
        self.expect(&TokenKind::With)?;

        // Parse arms: | pat => tac_seq
        let mut arms = Vec::new();
        let arm_col = self.current().col;
        while self.eat_alternative_pipe(arm_col) {
            let arm_span = self.current_span();
            let pattern = self.pattern_with_or()?;
            self.expect(&TokenKind::FatArrow)?;
            let tactics = self.tactic_seq_until_pipe()?;
            arms.push(TacticMatchArm {
                span: arm_span,
                pattern,
                tactics,
            });
        }

        Ok(SurfaceTactic::Match(start, hyp, discrs, arms))
    }

    /// The `h :` prefix of an annotated match discriminant, if present: an
    /// identifier immediately followed by `:` (no term starts that way).
    fn parse_match_discr_hyp(&mut self) -> Result<Option<crate::SurfaceName>, ParseError> {
        if matches!(self.current_kind(), TokenKind::Ident(_))
            && matches!(self.peek_kind(1), Some(TokenKind::Colon))
        {
            let name = self.expect_ident("match discriminant hypothesis")?;
            self.expect(&TokenKind::Colon)?;
            Ok(Some(name))
        } else {
            Ok(None)
        }
    }
}
