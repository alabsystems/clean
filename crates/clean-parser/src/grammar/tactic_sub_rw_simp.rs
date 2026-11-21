// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The rewriting, simp and structuring half of the tactic sub-grammar: `rw`,
//! `rwa`, `simp`, `simp_rw`, `case`, `next`, `calc`, the location suffix and
//! the `conv` entries (`first`, `solve` and the tactic `match` are in
//! `tactic_sub_alternatives.rs`).
//!
//! Split out of `tactic_sub.rs` to keep that file under the paragon
//! 1000-line limit; every item here is a method on [`Parser`].

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{
    ConvEnterArg, SimpPhase, Span, SurfaceName, SurfaceRwRule, SurfaceSimpArg, SurfaceTactic,
    SurfaceTacticLocation,
};
use crate::ParseError;

impl Parser {
    /// Parse `rw [rule1, <- rule2, rule3]` optionally followed by `at loc`
    pub(crate) fn parse_tactic_rw(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let rules = self.parse_rw_rules()?;
        let loc = self.parse_tactic_location();
        Ok(SurfaceTactic::Rw(start, rules, loc))
    }

    /// Parse `rewrite [rules] (at loc)?` — Lean's `rewriteSeq`, the rewrite
    /// with NO closing `rfl`. `rw` is Lean's macro over it (`rewrite …; try
    /// (with_reducible rfl)`), so the two are distinct tactic forms: after
    /// `rewrite [h]` a goal `b = b` stays open ("unsolved goals").
    pub(crate) fn parse_tactic_rewrite(
        &mut self,
        start: Span,
    ) -> Result<SurfaceTactic, ParseError> {
        let rules = self.parse_rw_rules()?;
        let loc = self.parse_tactic_location();
        Ok(SurfaceTactic::Rewrite(start, rules, loc))
    }

    /// Keep `rwa` distinct from `rw`: its closing step must remain focused on
    /// the original main goal, and `at h` closes using that rewritten local.
    /// The compound handler implements Lean's `Elab/Tactic/Rwa.lean` sequence.
    pub(crate) fn parse_tactic_rwa(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let rules = self.parse_rw_rules()?;
        let has_at = matches!(self.current_kind(), TokenKind::Ident(ref word) if word == "at");
        let loc = self.parse_tactic_location();
        if has_at && !matches!(&loc, SurfaceTacticLocation::Hyps(names) if names.len() == 1) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected one hypothesis after `rwa … at`".into(),
            });
        }
        Ok(SurfaceTactic::Rwa(start, rules, loc))
    }

    /// Parse `[rule1, <- rule2, rule3]` rewrite rule list
    fn parse_rw_rules(&mut self) -> Result<Vec<SurfaceRwRule>, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut rules = Vec::new();

        if !self.check(&TokenKind::RBracket) {
            loop {
                let rule_span = self.current_span();
                // `←` or its ASCII spelling `<-`.
                let reverse = self.eat(&TokenKind::LeftArrow) || self.eat_ascii_left_arrow();

                let term = self.expr()?;
                rules.push(SurfaceRwRule {
                    span: rule_span.merge(term.span()),
                    reverse,
                    term,
                });

                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(rules)
    }

    /// Parse `simp` with optional `only`, `[lemma1, lemma2]`, and `at loc`
    pub(crate) fn parse_tactic_simp(
        &mut self,
        start: Span,
        mut only: bool,
        all: bool,
    ) -> Result<SurfaceTactic, ParseError> {
        // `simp optConfig (&" only")? ("[" … "]")? (location)?` — the boolean
        // options come BEFORE `only` (191 mathlib4 sites write `simp +x only`,
        // none write `simp only +x`). See `Parser::eat_tactic_config_items`.
        self.eat_tactic_config_items();

        // Check for `simp only`
        if matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "only") {
            self.advance();
            only = true;
        }

        let (lemmas, use_hypotheses) = if self.check(&TokenKind::LBracket) {
            self.parse_simp_lemmas()?
        } else {
            (Vec::new(), false)
        };

        if all && matches!(self.current_kind(), TokenKind::Ident(ref word) if word == "at") {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "simp_all does not take a location".into(),
            });
        }
        let location = self.parse_tactic_location();

        Ok(SurfaceTactic::Simp {
            span: start,
            all,
            only,
            lemmas,
            location,
            use_hypotheses,
        })
    }

    /// Parse `[lemma1, ← lemma2, -lemma3, *]` simp lemma list.
    ///
    /// Returns the parsed [`SurfaceSimpArg`]s plus whether the list contained
    /// Lean's `*` element (`simp [*]`, `simp only [*]`, `simp [foo, *]`). `*`
    /// is not a term — it is the instruction "also use every local hypothesis
    /// as a rewrite rule" — so it is reported separately rather than pushed
    /// into the lemma list.
    ///
    /// Lean's element grammar is `simpLemma := (simpPre <|> simpPost)? "← "?
    /// term` and `simpErase := "-" ident`. Both modifiers used to be eaten
    /// and discarded here, so `simp [← h]` ran `h` FORWARD and `simp [-h]`
    /// ADDED `h` where Lean removes it. They are now recorded on the element.
    pub(super) fn parse_simp_lemmas(&mut self) -> Result<(Vec<SurfaceSimpArg>, bool), ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut lemmas = Vec::new();
        let mut use_hypotheses = false;

        if !self.check(&TokenKind::RBracket) {
            loop {
                let arg_span = self.current_span();
                // `↓` (`simpPre`) / `↑` (`simpPost`): WHEN a rule fires in
                // Lean's two-phase traversal — before or after the subterms
                // are visited — never which equation it is or its direction.
                // The phase is recorded on the element, and the elaborator
                // resolves the rule it marks (a simproc name such as
                // `↓reduceIte`, a theorem, a local) or refuses it by name.
                // `↓` reaches the parser as an unknown-character token and
                // `↑` as the coercion identifier, which in this position Lean
                // never reads as a coercion: `simpPre <|> simpPost` is tried
                // first.
                let phase = self.eat_simp_phase_marker();
                // `←` / `<-` (reverse) and `-` (erase) are Lean's two simp-arg
                // modifiers. `<-` reaches the lexer as `LAngle` + `Minus`, the
                // same spelling `parse_rw_rules` accepts. `simpErase` and `*`
                // are separate alternatives that take no phase marker.
                let reverse = self.eat(&TokenKind::LeftArrow) || self.eat_ascii_left_arrow();
                let erase = phase.is_none() && !reverse && self.eat(&TokenKind::Minus);
                if phase.is_none() && self.eat(&TokenKind::Star) {
                    use_hypotheses = true;
                } else {
                    let term = self.expr()?;
                    lemmas.push(SurfaceSimpArg {
                        span: arg_span.merge(term.span()),
                        phase,
                        reverse,
                        erase,
                        term,
                    });
                }
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok((lemmas, use_hypotheses))
    }

    /// Consume Lean's `simpPre` (`↓`) or `simpPost` (`↑`) marker when the
    /// current token is one; see the caller in [`Self::parse_simp_lemmas`].
    /// The marker must be followed by the rule on the same token boundary
    /// Lean allows (any whitespace); a marker with no rule after it is left
    /// for the term parser to refuse.
    fn eat_simp_phase_marker(&mut self) -> Option<SimpPhase> {
        let phase = match self.current_kind() {
            TokenKind::Error(crate::lexer::LexError::UnexpectedChar('↓')) => SimpPhase::Pre,
            TokenKind::Ident(text) if text == "↑" && !self.current().ident_escaped => {
                SimpPhase::Post
            }
            _ => return None,
        };
        if matches!(
            self.peek_kind(1),
            Some(TokenKind::Comma | TokenKind::RBracket) | None
        ) {
            return None;
        }
        self.advance();
        Some(phase)
    }

    /// Consume the ASCII spelling `<-` of `←` (two tokens: `<` then `-`).
    ///
    /// Returns `false` and consumes nothing when the next two tokens are not
    /// that pair, so it composes with `eat` in a `||` chain.
    fn eat_ascii_left_arrow(&mut self) -> bool {
        if matches!(self.current_kind(), TokenKind::LAngle)
            && matches!(self.peek_kind(1), Some(TokenKind::Minus))
        {
            self.advance();
            self.advance();
            true
        } else {
            false
        }
    }

    /// Parse `simp_rw [rules] (at loc)?`
    pub(crate) fn parse_tactic_simp_rw(
        &mut self,
        start: Span,
    ) -> Result<SurfaceTactic, ParseError> {
        let rules = self.parse_rw_rules()?;
        let loc = self.parse_tactic_location();
        Ok(SurfaceTactic::SimpRw(start, rules, loc))
    }

    /// Parse `case name (binder)* => tac_seq`.
    ///
    /// Lean grammar (`Init.Tactics`): `case caseArg => tacticSeq` where
    /// `caseArg := binderIdent (ppSpace binderIdent)*`. The first `binderIdent`
    /// is the case tag; each subsequent one renames the case's most-recently
    /// introduced inaccessible hypothesis. We accept `_` as a binder
    /// (Lean's anonymous `binderIdent`) and record it literally so the
    /// elaborator can leave that hypothesis unrenamed.
    pub(crate) fn parse_tactic_case(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        // The case tag is a `binderIdent`, so `_` (anonymous) is valid: `case _
        // => …` focuses the first available goal regardless of its tag (the
        // elaborator special-cases the `_` tag). Previously `expect_ident`
        // rejected `_`, so `case _` fell through to parser recovery / synthetic
        // sorry.
        let name = if self.eat(&TokenKind::Underscore) {
            SurfaceName::generated_path("_")
        } else {
            let mut tag = self.expect_ident("case")?;
            // A case tag is one `ident` token in Lean, dotted parts included:
            // `case some.cons hd tl =>` selects the `cons` goal produced under
            // the `some` goal (`cases a <;> cases b`). Clean lexes the parts
            // separately, so re-join them across byte-adjacent dots only.
            while self.dot_is_contiguous_qualifier() {
                self.advance();
                let part = self.expect_ident("case")?;
                tag = tag.append(&part);
            }
            tag
        };
        let mut binders = Vec::new();
        loop {
            match self.current_kind().clone() {
                TokenKind::Ident(binder) => {
                    let binder = self.name_token(&binder)?;
                    self.advance();
                    binders.push(binder);
                }
                TokenKind::Underscore => {
                    self.advance();
                    binders.push(SurfaceName::generated_path("_"));
                }
                _ => break,
            }
        }
        self.expect(&TokenKind::FatArrow)?;
        let tacs = self.indented_tactic_seq()?;
        Ok(SurfaceTactic::Case(start, name, binders, tacs))
    }

    /// Parse `next (binder)* => tac_seq`.
    ///
    /// Lean's `next` focuses the first/next goal (like an anonymous `case _`),
    /// optionally renaming that goal's inaccessible hypotheses to the supplied
    /// binder names. It desugars to `case _ (binder)* => …` — the `_` tag makes
    /// the elaborator focus the first goal.
    pub(crate) fn parse_tactic_next(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let mut binders = Vec::new();
        loop {
            match self.current_kind().clone() {
                TokenKind::Ident(binder) => {
                    let binder = self.name_token(&binder)?;
                    self.advance();
                    binders.push(binder);
                }
                TokenKind::Underscore => {
                    self.advance();
                    binders.push(SurfaceName::generated_path("_"));
                }
                _ => break,
            }
        }
        self.expect(&TokenKind::FatArrow)?;
        let tacs = self.indented_tactic_seq()?;
        Ok(SurfaceTactic::Case(
            start,
            SurfaceName::generated_path("_"),
            binders,
            tacs,
        ))
    }

    /// Parse `calc` steps inside tactic mode
    pub(crate) fn parse_tactic_calc(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let steps = self.calc_steps()?;
        Ok(SurfaceTactic::Calc(start, steps))
    }

    // =========================================================================
    // Location parsing
    // =========================================================================

    /// Parse optional `at h1 h2`, `at h1 h2 ⊢`, or `at *` location specifier.
    pub(super) fn at_tactic_location(&self) -> bool {
        matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "at")
            && !self.current().ident_escaped
    }

    pub(crate) fn parse_tactic_location(&mut self) -> SurfaceTacticLocation {
        if self.at_tactic_location() {
            self.advance();
            if self.eat(&TokenKind::Star) {
                let _ = self.eat(&TokenKind::Turnstile);
                SurfaceTacticLocation::Wildcard
            } else {
                let names = self.parse_location_hyp_list();
                let apply_goal = self.eat(&TokenKind::Turnstile);
                if apply_goal {
                    if names.is_empty() {
                        SurfaceTacticLocation::Goal
                    } else {
                        SurfaceTacticLocation::HypsAndGoal(names)
                    }
                } else if names.is_empty() {
                    SurfaceTacticLocation::Goal
                } else {
                    SurfaceTacticLocation::Hyps(names)
                }
            }
        } else {
            SurfaceTacticLocation::Goal
        }
    }

    /// The hypothesis names of `at h₁ … hₙ`. Lean's `locationHyp` is
    /// `(ppSpace colGt term:max)+`: a name on a later line belongs to the list
    /// only right of the tactic block's column. Contextual spellings such as
    /// `right` are local names in this slot. A new tactic at the block column
    /// ends the list.
    fn parse_location_hyp_list(&mut self) -> Vec<SurfaceName> {
        let mut names = Vec::new();
        loop {
            let tok = self.current();
            if !self.position_suppressed() && tok.preceded_by_newline {
                if let Some(&block_col) = self.indent_stack.last() {
                    if tok.col <= block_col {
                        break;
                    }
                }
            }
            let TokenKind::Ident(name) = &tok.kind else {
                break;
            };
            if tok.lean_keyword {
                break;
            }
            names.push(SurfaceName::component(name.clone(), tok.ident_escaped));
            self.advance();
        }
        names
    }

    // =========================================================================
    // Conv navigation sub-parsers
    // =========================================================================

    /// Parse `arg i` where i is an integer (negative counts from end)
    pub(crate) fn parse_conv_arg(&mut self, span: Span) -> Result<SurfaceTactic, ParseError> {
        let negative = self.eat(&TokenKind::Minus);
        match self.current_kind().clone() {
            TokenKind::NatLit(n) => {
                self.advance();
                // A literal >= 2^63 makes `n as i64` wrap negative and
                // `-(i64::MIN)` overflow (panic in debug, silent wrap in
                // release), and a `BigNat` beyond `u64` has no `i64` at all.
                // Clamp to the i64 range instead: indices this large are not
                // valid conv-arg positions, so saturating keeps in-range inputs
                // exact while making the overflow path safe.
                let magnitude = n
                    .to_u64()
                    .and_then(|v| i64::try_from(v).ok())
                    .unwrap_or(i64::MAX);
                let i = if negative {
                    magnitude.checked_neg().unwrap_or(i64::MIN)
                } else {
                    magnitude
                };
                Ok(SurfaceTactic::ConvArg(span, i))
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected integer after 'arg', got {:?}",
                    self.current_kind()
                ),
            }),
        }
    }

    /// Parse `enter [arg1, arg2, ...]` where each arg is an int or identifier
    pub(crate) fn parse_conv_enter(&mut self, span: Span) -> Result<SurfaceTactic, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut args = Vec::new();
        if !self.check(&TokenKind::RBracket) {
            args.push(self.parse_enter_arg()?);
            while self.eat(&TokenKind::Comma) {
                if self.check(&TokenKind::RBracket) {
                    break;
                }
                args.push(self.parse_enter_arg()?);
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(SurfaceTactic::ConvEnter(span, args))
    }

    /// Parse a single enter argument: numeric index or variable name
    fn parse_enter_arg(&mut self) -> Result<ConvEnterArg, ParseError> {
        let negative = self.eat(&TokenKind::Minus);
        match self.current_kind().clone() {
            TokenKind::NatLit(n) => {
                self.advance();
                // A literal >= 2^63 makes `n as i64` wrap negative and
                // `-(i64::MIN)` overflow (panic in debug, silent wrap in
                // release), and a `BigNat` beyond `u64` has no `i64` at all.
                // Clamp to the i64 range instead: indices this large are not
                // valid conv-enter positions, so saturating keeps in-range
                // inputs exact while making the overflow path safe.
                let magnitude = n
                    .to_u64()
                    .and_then(|v| i64::try_from(v).ok())
                    .unwrap_or(i64::MAX);
                let i = if negative {
                    magnitude.checked_neg().unwrap_or(i64::MIN)
                } else {
                    magnitude
                };
                Ok(ConvEnterArg::Index(i))
            }
            TokenKind::Ident(name) if !negative => {
                let name = self.name_token(&name)?;
                self.advance();
                Ok(ConvEnterArg::Name(name))
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected integer or identifier in enter, got {:?}",
                    self.current_kind()
                ),
            }),
        }
    }
}
