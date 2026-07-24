// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additional tactic sub-parsers for newly wired tactic dispatch entries (#1789).
//!
//! Contains parsers for `simpa` and helper methods used by tactic dispatch.
//! Split from `tactic_sub.rs` to maintain the 500-line file limit.
//!
//! `use`, `exists`, `rotate_left`, `rotate_right` migrated to TacticRegistry
//! (#2430 Phase 3C Wave 2).
//! `by_cases`, `specialize`, `generalize` migrated to TacticRegistry
//! (#2430 Phase 3C Wave 3).

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{Span, SurfaceTactic};
use crate::ParseError;

impl Parser {
    /// Parse `simpa [lemmas]` or `simpa only [lemmas]`
    pub(crate) fn parse_tactic_simpa(
        &mut self,
        span: Span,
        only: bool,
    ) -> Result<SurfaceTactic, ParseError> {
        let lemmas = if self.check(&TokenKind::LBracket) {
            self.advance();
            let mut lemmas = Vec::new();
            if !self.check(&TokenKind::RBracket) {
                lemmas.push(self.expr()?);
                while self.eat(&TokenKind::Comma) {
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                    lemmas.push(self.expr()?);
                }
            }
            self.expect(&TokenKind::RBracket)?;
            lemmas
        } else {
            Vec::new()
        };
        // Optional `using <term>`: `using` is an ordinary identifier token, not a
        // reserved keyword, so we match it by name. The term that follows is a
        // full expression (e.g. `Bool.xor_comm a b`).
        let using_term = if matches!(self.current_kind(), TokenKind::Ident(name) if name == "using")
        {
            self.advance();
            Some(self.expr()?)
        } else {
            None
        };
        Ok(SurfaceTactic::Simpa {
            span,
            only,
            lemmas,
            using_term,
        })
    }

    // =========================================================================
    // Tactic helper methods (split from tactic.rs)
    // =========================================================================

    /// Try to eat an identifier, returning its name if successful
    pub(crate) fn try_eat_ident(&mut self) -> Option<String> {
        match self.current_kind().clone() {
            TokenKind::Ident(name) => {
                // Don't consume keywords that start tactic sub-parsers
                if self.is_tactic_keyword(&name) {
                    return None;
                }
                // Don't consume registered tactic names — they start a new tactic.
                // This ensures `intro rcases h` stops the ident list at `rcases`
                // when `rcases` is in the pattern map.
                if self.tactic_pattern(&name).is_some() {
                    return None;
                }
                self.advance();
                Some(name)
            }
            _ => None,
        }
    }

    /// Expect an identifier, returning its name
    pub(crate) fn expect_ident(&mut self, context: &str) -> Result<String, ParseError> {
        match self.current_kind().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(name)
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected identifier in {}, got {:?}",
                    context,
                    self.current_kind()
                ),
            }),
        }
    }

    /// Parse a list of identifiers (stops at non-ident or tactic keyword)
    pub(crate) fn parse_ident_list(&mut self) -> Vec<String> {
        let mut names = Vec::new();
        while let Some(name) = self.try_eat_ident() {
            names.push(name);
        }
        names
    }

    /// Check if an identifier is a tactic keyword that would start a new tactic
    pub(crate) fn is_tactic_keyword(&self, name: &str) -> bool {
        matches!(
            name,
            "exact"
                | "apply"
                | "refine"
                | "intro"
                | "intros"
                | "assumption"
                | "constructor"
                | "left"
                | "right"
                | "cases"
                | "induction"
                | "rw"
                | "rewrite"
                | "simp"
                | "simp_all"
                | "simp_rw"
                | "simp_only"
                | "omega"
                | "decide"
                | "contradiction"
                | "trivial"
                | "exfalso"
                | "by_contra"
                | "split"
                | "ext"
                | "funext"
                | "subst"
                | "injection"
                | "push_neg"
                | "norm_num"
                | "ring"
                | "linarith"
                | "norm_cast"
                | "unfold"
                | "change"
                | "revert"
                | "clear"
                | "rename_i"
                | "congr"
                | "conv"
                | "dsimp"
                | "aesop"
                | "tauto"
                | "skip"
                | "done"
                | "case"
                | "all_goals"
                | "any_goals"
                | "try"
                | "first"
                | "repeat"
                | "calc"
                | "exact?"
                | "apply?"
                | "at"
                | "symm"
                | "trans"
                | "admit"
                | "native_decide"
                | "use"
                | "exists"
                | "by_cases"
                | "classical"
                | "specialize"
                | "generalize"
                | "rotate_left"
                | "rotate_right"
                | "delta"
                | "simpa"
                | "simpa_only"
        )
    }

    /// Get the span of the previous token
    pub(crate) fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens[self.pos - 1].span
        } else {
            self.current_span()
        }
    }
}
