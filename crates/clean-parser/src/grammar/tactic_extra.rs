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
use crate::surface::{Span, SurfaceName, SurfaceTactic};
use crate::ParseError;

impl Parser {
    /// Parse `simpa [lemmas]` or `simpa only [lemmas]`
    pub(crate) fn parse_tactic_simpa(
        &mut self,
        span: Span,
        mut only: bool,
    ) -> Result<SurfaceTactic, ParseError> {
        // `simpa optConfig (&" only")? ("[" … "]")? ("using" term)?` — the
        // same prefix as `simp` (`parse_tactic_simp`). `only` used to be left
        // unconsumed here, so `· simpa only [H] using hp` parsed `simpa`
        // with no lemmas and then died on an "unknown tactic `only`"
        // (`Prop.forall_iff`'s `<;> simpa only [H]`, measured 2026-09-11).
        self.eat_tactic_config_items();
        if matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "only") {
            self.advance();
            only = true;
        }
        // The lemma list is `simp`'s (`←`/`-` modifiers, `*`); `simpa` has no
        // hypothesis-wildcard channel of its own yet, so `[*]` is recorded as
        // nothing to add (as before, when it did not parse at all).
        let (lemmas, use_hypotheses) = if self.check(&TokenKind::LBracket) {
            self.parse_simp_lemmas()?
        } else {
            (Vec::new(), false)
        };
        // Optional `using <term>`: `using` is an ordinary identifier token, not a
        // reserved keyword, so we match it by name. The term is a tactic-line
        // term: it stops at the next line's bullet or tactic
        // (`parse_tactic_expr`), where a bare `expr()` swallowed the following
        // `· simpa …` line as further arguments (`·` is the cdot-function
        // token) — six of them, in a `by_cases`/bullet proof.
        let using_term = if matches!(self.current_kind(), TokenKind::Ident(name) if name == "using")
        {
            self.advance();
            Some(self.parse_tactic_expr()?)
        } else {
            None
        };
        Ok(SurfaceTactic::Simpa {
            span,
            only,
            lemmas,
            use_hypotheses,
            using_term,
        })
    }

    // =========================================================================
    // Tactic helper methods (split from tactic.rs)
    // =========================================================================

    /// Try to eat an identifier, returning its name if successful. A Lean
    /// keyword is not one (`crate::lexer::Token::lean_keyword`): Lean's
    /// `ident` does not match it, so an identifier list ends there.
    pub(crate) fn try_eat_ident(&mut self) -> Option<SurfaceName> {
        match self.current_kind().clone() {
            TokenKind::Ident(_) if self.current().lean_keyword => None,
            TokenKind::Ident(name) => {
                // Don't consume keywords that start tactic sub-parsers
                if !self.current().ident_escaped && self.is_tactic_keyword(&name) {
                    return None;
                }
                // Don't consume registered tactic names — they start a new tactic.
                // This ensures `intro rcases h` stops the ident list at `rcases`
                // when `rcases` is in the pattern map.
                if !self.current().ident_escaped && self.tactic_pattern(&name).is_some() {
                    return None;
                }
                let name = SurfaceName::component(name, self.current().ident_escaped);
                self.advance();
                Some(name)
            }
            _ => None,
        }
    }

    /// Expect an identifier, returning its name
    pub(crate) fn expect_ident(&mut self, context: &str) -> Result<SurfaceName, ParseError> {
        match self.current_kind().clone() {
            TokenKind::Ident(name) => {
                let name = self.name_token(&name)?;
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
    pub(crate) fn parse_ident_list(&mut self) -> Vec<SurfaceName> {
        let mut names = Vec::new();
        while let Some(name) = self.try_eat_ident() {
            names.push(name);
        }
        names
    }

    /// Read names in an explicit argument list bounded by Lean's `colGt`.
    /// Tactic dispatch names have no special meaning in an argument slot.
    pub(super) fn parse_indented_ident_list(&mut self) -> Result<Vec<SurfaceName>, ParseError> {
        let mut names = Vec::new();
        while self.col_gt_saved_position() && !self.current().lean_keyword {
            let TokenKind::Ident(text) = self.current_kind() else {
                break;
            };
            names.push(self.name_token(text)?);
            self.advance();
        }
        Ok(names)
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
                | "letI"
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
