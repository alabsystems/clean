// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic sub-parsers for compound tactic forms.
//!
//! Contains parsers for `let`, `suffices`, `cases`/`induction`, `rw`,
//! `simp`, `case`, `first`, `calc`, and location specifiers. Split from
//! `tactic.rs` for file-size compliance (500 line limit).
//!
//! These are inherent methods on `Parser`, callable from the main tactic
//! dispatch in `tactic.rs`.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{Span, SurfaceExpr, SurfaceInductionAlt, SurfaceTactic};
use crate::ParseError;

impl Parser {
    // =========================================================================
    // Tactic-specific sub-parsers
    // =========================================================================

    /// Parse a tactic-mode `let` binding:
    ///   `let h : T := val`   — named, optionally typed
    ///   `let _ : T := val`   — inaccessible, optionally typed
    ///   `let ⟨a, b⟩ := e`    — anonymous-constructor destructuring
    ///
    /// The destructuring form is desugared to [`SurfaceTactic::Obtain`],
    /// exactly as [`Self::parse_tactic_have`] does for `have ⟨a, b⟩ := e`: the
    /// leading `⟨` disambiguates from the named form, and the remaining parse
    /// (optional `: T` ascription, `:=`, scrutinee) is character-for-character
    /// `obtain`'s, so it routes through the same kernel-checked pattern engine.
    ///
    /// Semantic caveat, carried deliberately: Lean's `let` pattern introduces
    /// LET-BOUND definitions where `obtain` introduces opaque hypotheses. In
    /// practice `obtain ⟨a, b⟩ := p` destructs `p` and substitutes `⟨a, b⟩`
    /// into the goal, so a component projection still reduces (`p.1` ↝ `a` by
    /// iota rather than by zeta) — but the two are not identical, and a proof
    /// that needs `a` to unfold to `p.1` in the OTHER direction can differ.
    pub(crate) fn parse_tactic_let(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        if matches!(self.current_kind(), TokenKind::LAngle) {
            return self.parse_tactic_obtain(start);
        }
        let name = if self.eat(&TokenKind::Underscore) {
            super::tactic::inaccessible_hypothesis()
        } else {
            self.expect_ident("let")?
        };
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.parse_tactic_binding_type()?))
        } else {
            None
        };
        self.expect(&TokenKind::ColonEq)?;
        let val = self.parse_tactic_expr()?;
        Ok(SurfaceTactic::Let(start, name, ty, Box::new(val)))
    }

    /// Parse `suffices h : T by tacs` or `suffices h : T from proof`
    pub(crate) fn parse_tactic_suffices(
        &mut self,
        start: Span,
    ) -> Result<SurfaceTactic, ParseError> {
        // `sufficesDecl := (atomic(group(binderIdent " : ")) <|> hygieneInfo)
        // term showRhs` (`Lean/Parser/Term.lean:216-217`): the binder is taken
        // only when an identifier or `_` is directly followed by `:`, the
        // two-token analogue of that `atomic`. Otherwise the whole argument is
        // the proposition, and the hypothesis is `this` (`Init/Tactics.lean:
        // 871-873`: "If `h :` is omitted, the name `this` is used"; the
        // elaborator supplies it for `None`). Measured before: the first
        // identifier was always taken as the binder, so `suffices cast hU (g
        // s).2 = … by` (Mathlib `Logic/Function/Basic.lean:277`) died "expected
        // Colon, got Ident(hU)", and even `suffices a = 1 by` failed.
        let name = if matches!(self.peek_kind(1), Some(TokenKind::Colon))
            && matches!(
                self.current_kind(),
                TokenKind::Ident(_) | TokenKind::Underscore
            ) {
            // `suffices _ : t` names an INACCESSIBLE hypothesis (`binderIdent`
            // is `ident <|> "_"`); `_` lexes to `Underscore`, not `Ident`.
            let name = if self.eat(&TokenKind::Underscore) {
                super::tactic::inaccessible_hypothesis()
            } else {
                self.expect_ident("suffices")?
            };
            self.expect(&TokenKind::Colon)?;
            Some(name)
        } else {
            // The Lean 3 nameless spelling `suffices : t` is kept (it names the
            // hypothesis `this` as well); Lean 4's anonymous form has no colon.
            let _ = self.eat(&TokenKind::Colon);
            None
        };
        // The type `T` is followed by the justification separator (`by` or
        // `from`). A trailing `by` belongs to `suffices`, not to an application
        // inside `T`, so guard against `by` being read as an application
        // argument while parsing `T` (mirrors the term-level `show_body` /
        // `suffices_body` handling). Without this, `suffices h : p by exact h2`
        // parses `p` as `p (by exact h2)`, swallowing the tactic block and the
        // dedented continuation as application arguments (#1798-style bug).
        let prev_stop_at_by = self.stop_app_at_by;
        self.stop_app_at_by = true;
        let ty_result = self.parse_tactic_expr();
        self.stop_app_at_by = prev_stop_at_by;
        let ty = ty_result?;
        let proof_tacs = if self.eat(&TokenKind::By) {
            self.indented_tactic_seq()?
        } else {
            let _ = self.eat(&TokenKind::From);
            let proof = self.parse_tactic_expr()?;
            vec![SurfaceTactic::Term(proof.span(), Box::new(proof))]
        };
        Ok(SurfaceTactic::Suffices(
            start,
            name,
            Box::new(ty),
            proof_tacs,
        ))
    }

    /// Parse `cases e with | alt => tacs | ...` or `induction e with | alt => tacs | ...`
    pub(crate) fn parse_tactic_cases_induction(
        &mut self,
        start: Span,
        is_cases: bool,
    ) -> Result<SurfaceTactic, ParseError> {
        // While parsing the major premise, stop the application-argument loop at
        // the `using` / `generalizing` clause keywords (see the guard in
        // `app_expr`). `cases` accepts neither clause here, but leaving the guard
        // on for `cases` too is harmless: it only affects a `cases e using …`
        // form, which this function scopes exclusively to `induction` below.
        // `cases h : e` — Lean 4.8's `casesTarget := atomic(ident " : ")? term`
        // (`Init/Tactics.lean`). The `atomic` prefix is an identifier
        // IMMEDIATELY followed by `:`; no term starts that way, so the two-token
        // lookahead is exact. `induction`'s targets are plain `term`s, so the
        // prefix is `cases`-only. Without it the `:` ended the tactic
        // (`at_tactic_end`) and the rest of the proof fell to parser recovery.
        let hyp_name = if is_cases
            && matches!(self.current_kind(), TokenKind::Ident(_))
            && matches!(self.peek_kind(1), Some(TokenKind::Colon))
        {
            let name = self.expect_ident("cases target equation name")?;
            self.expect(&TokenKind::Colon)?;
            Some(name)
        } else {
            None
        };
        let prev_stop = self.stop_app_at_generalizing_using;
        self.stop_app_at_generalizing_using = !is_cases;
        let target_result = self.parse_tactic_expr();
        self.stop_app_at_generalizing_using = prev_stop;
        let target = target_result?;

        // `induction e using r generalizing x with …` — Lean's clause order is
        // `using` then `generalizing`, both optional, both before `with`.
        // `cases` takes neither in this implementation (scoped to induction).
        let (using_recursor, generalizing) = if is_cases {
            (None, Vec::new())
        } else {
            let using_recursor = self.parse_induction_using_clause()?;
            let generalizing = self.parse_induction_generalizing_clause()?;
            (using_recursor, generalizing)
        };

        let alts = if self.eat(&TokenKind::With) {
            self.parse_induction_alts()?
        } else {
            Vec::new()
        };

        if is_cases {
            Ok(SurfaceTactic::Cases(
                start,
                hyp_name,
                Box::new(target),
                alts,
            ))
        } else {
            Ok(SurfaceTactic::Induction {
                span: start,
                target: Box::new(target),
                using_recursor: using_recursor.map(Box::new),
                generalizing,
                alts,
            })
        }
    }

    /// Parse an optional `using <term>` recursor-override clause for `induction`.
    ///
    /// `using` is an ordinary identifier token (not a reserved keyword), matched
    /// by name — mirrors the `simpa … using` clause parser. The recursor is a
    /// full term so qualified names (`Nat.rec`) are captured intact. Returns
    /// `None` when no `using` clause is present.
    fn parse_induction_using_clause(&mut self) -> Result<Option<SurfaceExpr>, ParseError> {
        if matches!(self.current_kind(), TokenKind::Ident(name) if name == "using") {
            self.advance();
            // Keep the generalizing-guard active so `using r generalizing x`
            // stops the recursor term before `generalizing`.
            let prev_stop = self.stop_app_at_generalizing_using;
            self.stop_app_at_generalizing_using = true;
            let term_result = self.parse_tactic_expr();
            self.stop_app_at_generalizing_using = prev_stop;
            Ok(Some(term_result?))
        } else {
            Ok(None)
        }
    }

    /// Collect local names in Lean's indentation-delimited `generalizing` clause.
    /// A tactic spelling such as `right` is a legal local name in this position.
    fn parse_induction_generalizing_clause(
        &mut self,
    ) -> Result<Vec<crate::SurfaceName>, ParseError> {
        if self.current().ident_escaped
            || !matches!(self.current_kind(), TokenKind::Ident(name) if name == "generalizing")
        {
            return Ok(Vec::new());
        }
        self.advance();
        let names = self.parse_indented_ident_list()?;
        if names.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "expected a local variable after generalizing".to_string(),
            });
        }
        Ok(names)
    }

    /// Parse `| name args => tac_seq` alternatives for cases/induction
    ///
    /// Column-sensitive (mirrors `match_body`, Track R / Track KK): the first
    /// arm's `|` column is the reference. A later `|` that begins a new line at
    /// a *smaller* column belongs to an enclosing `cases`/`induction` and must
    /// terminate this alt list — otherwise a nested `cases ... with | ...` in an
    /// arm body greedily swallows the outer construct's subsequent arms
    /// (Basic.lean `Int.land_comm`: the inner `cases b with` ate the outer
    /// `| negSucc m =>` arm, leaving the outer `cases a` with only its first
    /// alternative and producing "Alternative `negSucc` has not been provided").
    /// A same-line `|`, or one indented at least as far as the first arm,
    /// continues this alt list. Matches Lean 4 column-sensitive `matchAlts`.
    fn parse_induction_alts(&mut self) -> Result<Vec<SurfaceInductionAlt>, ParseError> {
        let mut alts = Vec::new();

        // Column of this construct's first arm `|`. Captured before the first
        // `|` is consumed so nested arm bodies can compare against it.
        let arm_col = self.current().col;
        while self.check(&TokenKind::Pipe)
            && !(self.current().preceded_by_newline && self.current().col < arm_col)
        {
            // `inductionAlt := inductionAltLHS+ " => " tacticSeq`: several
            // left-hand sides may share one right-hand side (`| Add | Sub | Mul
            // => simp`, trust-ir `MetaTheorems.lean`). Lean's
            // `expandInductionAlts?` expands such an alternative into one
            // alternative per LHS, each with the same tactics; so does this.
            let mut lhss = vec![self.parse_induction_alt_lhs()?];
            while self.check(&TokenKind::Pipe) {
                lhss.push(self.parse_induction_alt_lhs()?);
            }
            self.expect(&TokenKind::FatArrow)?;
            let tactics = self.tactic_seq_until_pipe()?;
            for (span, explicit, name, args) in lhss {
                alts.push(SurfaceInductionAlt {
                    span,
                    explicit,
                    name,
                    args,
                    tactics: tactics.clone(),
                });
            }
        }

        Ok(alts)
    }

    /// One `inductionAltLHS`: `| (@? ident | _) (ident | _)*`, the `|` included.
    fn parse_induction_alt_lhs(
        &mut self,
    ) -> Result<(Span, bool, crate::SurfaceName, Vec<crate::SurfaceName>), ParseError> {
        self.expect(&TokenKind::Pipe)?;
        let alt_span = self.current_span();
        // Lean 4's `inductionAlt` names the constructor with
        // `(group("@"? ident) <|> hole)` (`Init/Tactics.lean`), so `_` is a
        // legal alternative name meaning "every remaining case". The
        // elaborator already implements it — `builtins_phase3d_intro.rs`
        // looks up `alts.iter().find(|a| a.name == "_")` — but
        // `expect_ident` rejected the `_` token, so the whole `by` block
        // recovered to a synthetic sorry and that branch was dead code
        // (plan brick T5b / RC-Q).
        let explicit = self.eat(&TokenKind::At);
        let name = if !explicit && self.eat(&TokenKind::Underscore) {
            crate::SurfaceName::generated_path("_")
        } else {
            self.expect_ident("case alternative")?
        };
        // Lean's alt arguments are `binderIdent*`, so `_` is a legal
        // ANONYMOUS binder: `| succ k _ => …`. `parse_ident_list` stops at
        // `_`, which then failed `expect(FatArrow)` and recovered the whole
        // block to a synthetic sorry. Record it literally as "_", exactly
        // as `parse_tactic_case`/`parse_ident_list_to_named` already do.
        //
        // Every binder is an `ident`: the `=>` ends the list, so a name that
        // also spells a tactic (`lhs`, `rhs`, `left`, `exact`, …) is still
        // a binder here — Lean's tactic names are non-reserved. `try_eat_ident`
        // stops at those (it serves lists a tactic may follow), which made
        // `| BinOp op ty lhs rhs =>` fail with "expected FatArrow, got
        // Ident(lhs)" (trust-ir `TransformCorrectness.lean`). A Lean
        // keyword is still refused, as `ident` refuses it.
        let mut args = Vec::new();
        loop {
            match self.current_kind().clone() {
                TokenKind::Ident(text) if !self.current().lean_keyword => {
                    let binder = self.name_token(&text)?;
                    self.advance();
                    args.push(binder);
                }
                TokenKind::Underscore => {
                    self.advance();
                    args.push(crate::SurfaceName::generated_path("_"));
                }
                _ => break,
            }
        }
        Ok((alt_span, explicit, name, args))
    }

    /// Parse tactic sequence until we hit `|` or a tactic block terminator.
    ///
    /// Every caller parses the right-hand side of an alternative — an
    /// `inductionAlt` (`cases`/`induction … with`), a `first | …` branch or a
    /// tactic `match` arm — and in Lean 4.8 each of those is a `tacticSeq`
    /// (`Init/Tactics.lean` `inductionAlt`, `first`; `matchRhs`), whose
    /// `sepByIndent` saves the column of its FIRST tactic as the position
    /// (`Lean/Parser/Extra.lean` `sepByIndent` = `withPosition …`). A term
    /// argument then stops at a new line at or left of that column
    /// (`checkColGt` on `argument`), so
    ///
    /// ```text
    /// | some p =>
    ///   obtain ⟨a, b⟩ := p
    ///   cases f a with
    /// ```
    ///
    /// is two tactics. Without the frame the alternative inherited the
    /// enclosing `by` block's column, `cases f a` became two more arguments
    /// of `p`, and the following `with` failed the whole declaration to
    /// parser recovery (trust-ir `TransformCorrectness.lean`,
    /// `MemoryProps.lean`, `PredLatticeProps.lean`). A new line LEFT of the
    /// first tactic ends the alternative.
    ///
    /// Newline-separated siblings must also start at the first tactic's
    /// column (`checkColEq`). A semicolon explicitly separates the next
    /// tactic, so that one separator does not require column equality.
    /// Indented term arguments have already been consumed by `tactic()`.
    pub(super) fn tactic_seq_until_pipe(&mut self) -> Result<Vec<SurfaceTactic>, ParseError> {
        let first_col = self.current().col;
        self.push_indent_for(first_col, "alternative tactic block");
        let result = self.tactic_seq_until_pipe_framed(first_col);
        self.pop_indent();
        result
    }

    fn tactic_seq_until_pipe_framed(
        &mut self,
        first_col: u32,
    ) -> Result<Vec<SurfaceTactic>, ParseError> {
        let mut tactics = Vec::new();
        let mut after_semicolon = false;

        while !self.at_tactic_end(0) && !matches!(self.current_kind(), TokenKind::Pipe) {
            if !tactics.is_empty()
                && !after_semicolon
                && self.current().preceded_by_newline
                && self.current().col != first_col
            {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current().col as usize,
                    message: "alternative tactic siblings must have matching indentation"
                        .to_string(),
                });
            }
            let tac = self.tactic()?;
            tactics.push(self.parse_seq_focus_tail(tac)?);
            after_semicolon = self.eat(&TokenKind::Semicolon);
            while self.eat(&TokenKind::Semicolon) {}
        }

        Ok(tactics)
    }
}
