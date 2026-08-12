// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic sub-parsers for compound tactic forms.
//!
//! Contains parsers for `have`, `let`, `suffices`, `cases`/`induction`, `rw`,
//! `simp`, `case`, `first`, `calc`, and location specifiers. Split from
//! `tactic.rs` for file-size compliance (500 line limit).
//!
//! These are inherent methods on `Parser`, callable from the main tactic
//! dispatch in `tactic.rs`.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{
    ConvEnterArg, Span, SurfaceExpr, SurfaceInductionAlt, SurfaceRwRule, SurfaceTactic,
    SurfaceTacticLocation, TacticMatchArm,
};
use crate::ParseError;

impl Parser {
    // =========================================================================
    // Tactic-specific sub-parsers
    // =========================================================================

    /// Parse the tactic-mode `have` in all of its surface forms:
    ///   `have h : T := proof`   — named, typed
    ///   `have : T := proof`     — anonymous, typed
    ///   `have h := proof`       — named, type inferred from the proof term
    ///   `have ⟨a, b⟩ := e`      — anonymous-constructor destructuring
    ///
    /// The destructuring form is desugared to [`SurfaceTactic::Obtain`] (which
    /// shares `obtain`'s kernel-checked pattern engine). The other forms produce
    /// [`SurfaceTactic::Have`] with an `Option` type annotation: `None` when the
    /// `: T` ascription is omitted, in which case the elaborator infers the type
    /// from the elaborated proof term.
    pub(crate) fn parse_tactic_have(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        // Destructuring `have ⟨pat⟩ (: T)? := e` — desugar to `obtain ⟨pat⟩
        // (: T)? := e`. The leading `⟨` disambiguates from the named forms; the
        // remaining parse (optional ascription, `:=`, scrutinee) is exactly
        // `obtain`'s, so route through the same parser and Obtain machinery.
        if matches!(self.current_kind(), TokenKind::LAngle) {
            return self.parse_tactic_obtain(start);
        }

        // Optional name
        let name = self.try_eat_ident();

        // Optional `: T` ascription. When omitted (`have h := proof`), the type
        // is inferred from the proof term during elaboration.
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.parse_tactic_expr()?))
        } else {
            None
        };

        // The proof can be:
        //   `have h : T by tac_seq`       — `by` directly after type
        //   `have h : T := by tac_seq`    — `:= by` (common Lean 4 form)
        //   `have h : T := proof`         — `:=` followed by a term
        //   `have h : T from proof`       — `from` followed by a term
        //   `have h := proof`             — no ascription; `:=` then a term
        //
        // Both `by` forms go through the indent-aware tactic path.
        // The `:= by` case must be intercepted here rather than falling
        // through to `expr()`, because `expr()` is indent-blind and would
        // greedily consume outer-block tactics as term arguments (#1798).
        let by_proof = if self.eat(&TokenKind::By) {
            true
        } else {
            let _ = self.eat(&TokenKind::ColonEq) || self.eat(&TokenKind::From);
            self.eat(&TokenKind::By)
        };

        let proof_tac = if by_proof {
            let tac_span = self.current_span();
            let tacs = self.indented_tactic_seq()?;
            if tacs.len() == 1 {
                tacs.into_iter()
                    .next()
                    .expect("invariant: tactic_seq returned non-empty")
            } else {
                SurfaceTactic::Paren(tac_span, tacs)
            }
        } else {
            let proof_expr = self.parse_tactic_expr()?;
            SurfaceTactic::Term(proof_expr.span(), Box::new(proof_expr))
        };

        Ok(SurfaceTactic::Have(start, name, ty, Box::new(proof_tac)))
    }

    /// Parse `obtain pat (: T)? := e` in tactic mode.
    ///
    /// The leading keyword (`obtain`) has already been consumed. Parses an
    /// optional destructuring pattern (an anonymous constructor `⟨...⟩` or a
    /// single name), an optional `: T` type ascription, the `:=` separator, and
    /// the RHS scrutinee term. Mirrors [`Self::parse_tactic_have`] so the `:=`
    /// separator is handled directly rather than by the generic expr-list arg
    /// parser (which has no `:=` handling).
    ///
    /// The pattern is captured as its canonical `⟨...⟩` source text so the
    /// elaborator can reuse the recursive-intro pattern engine (`RIntroPattern`)
    /// without the parser depending on `clean-elab` types.
    pub(crate) fn parse_tactic_obtain(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        // Optional pattern: `⟨...⟩` anonymous-constructor pattern, a bare name, or
        // a top-level `|` alternation (`obtain hp | hq := h`, splitting an `Or`).
        // When omitted (`obtain := e` is not valid Lean, but `obtain : T := e`
        // is), default the binder to an anonymous `h` pattern. A `:`/`:=` here
        // means no leading pattern (the `else` arm), so guard against consuming a
        // pattern when the next token starts the type/value clause.
        let pattern = if matches!(
            self.current_kind(),
            TokenKind::LAngle | TokenKind::Underscore | TokenKind::Ident(_) | TokenKind::Rfl
        ) {
            // A full pattern including any top-level `|` alternation, so
            // `obtain hp | hq := h` captures `hp | hq` and the elaborator splits.
            self.parse_rcases_pattern_with_alts()?
        } else {
            "h".to_string()
        };

        // Optional `: T` type ascription.
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.parse_tactic_expr()?))
        } else {
            None
        };

        // Required `:=` separator, then the RHS scrutinee term.
        self.expect(&TokenKind::ColonEq)?;
        let term = self.parse_tactic_expr()?;

        Ok(SurfaceTactic::Obtain {
            span: start.merge(term.span()),
            pattern,
            ty,
            term: Box::new(term),
        })
    }

    /// Parse an anonymous-constructor obtain pattern `⟨p1, p2, ...⟩` into its
    /// canonical `⟨...⟩` source text.
    ///
    /// The current token must be `⟨` (`TokenKind::LAngle`). Recurses on nested
    /// `⟨...⟩` groups so patterns like `⟨⟨a, b⟩, c⟩` round-trip faithfully. Each
    /// field is a full rcases pattern, so an `Or`-alternation `p₁ | p₂` may
    /// appear as a field (e.g. `⟨hp, hq | hr⟩`, destructuring `p ∧ (q ∨ r)`):
    /// the field reader consumes the trailing `| ...` alternatives at the same
    /// bracket level, leaving the enclosing `,`/`⟩` for this loop. The resulting
    /// string is consumed by the elaborator's `RIntroPattern::parse`.
    fn parse_obtain_anon_pattern(&mut self) -> Result<String, ParseError> {
        self.expect(&TokenKind::LAngle)?;
        let mut out = String::from("⟨");
        let mut first = true;
        while !self.check(&TokenKind::RAngle) {
            if !first {
                self.expect(&TokenKind::Comma)?;
                out.push_str(", ");
            }
            first = false;
            // Each field is a full pattern, including a possible `|` alternation
            // (`⟨hp, hq | hr⟩`). `parse_rcases_pattern_with_alts` reads the leaf
            // and any trailing same-level `| ...` alternatives, stopping at the
            // field-separating `,` or the group-closing `⟩`.
            out.push_str(&self.parse_rcases_pattern_with_alts()?);
        }
        self.expect(&TokenKind::RAngle)?;
        out.push('⟩');
        Ok(out)
    }

    /// Parse `rcases <term> with <pattern>` in tactic mode.
    ///
    /// `rcases` destructures an EXISTING hypothesis named by `<term>` according to
    /// the `with`-clause pattern. The scrutinee is parsed as a term; if the `with`
    /// keyword follows, the pattern is parsed via the SAME anonymous-constructor
    /// pattern reader used by `obtain` (`⟨...⟩`, a bare name, or `_`), so nested
    /// patterns like `⟨a, ⟨b, c⟩⟩` round-trip. Parsing stops cleanly at the
    /// pattern's closing `⟩` (or the single ident/`_`), leaving any `;`-sequenced
    /// continuation for the tactic sequencer.
    ///
    /// When no `with`-clause is present, the pattern defaults to a single
    /// wildcard `_`, matching `rcases h` (full recursive case split with
    /// auto-named hypotheses).
    pub(crate) fn parse_tactic_rcases(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let term = self.parse_tactic_expr()?;

        let pattern = if self.eat(&TokenKind::With) {
            self.parse_rcases_with_pattern()?
        } else {
            "_".to_string()
        };

        Ok(SurfaceTactic::RCases {
            span: start.merge(term.span()),
            term: Box::new(term),
            pattern,
        })
    }

    /// Parse the pattern following `rcases ... with` (or a single `rintro`
    /// pattern), INCLUDING a top-level `|` alternation.
    ///
    /// `rcases h with hp | hq` (the canonical disjunction-splitting idiom) parses
    /// the leaf `hp`, then consumes the trailing `| hq` so the captured pattern
    /// text is `hp | hq`, which `RIntroPattern::parse` reads as an `Or`
    /// alternation that the elaborator turns into a real case-split. Without this,
    /// the leaf reader stopped at `hp` and left `| hq` dangling, which the
    /// declaration parser recovered as a raw `Pipe` token. See
    /// [`Self::parse_rcases_pattern_with_alts`].
    fn parse_rcases_with_pattern(&mut self) -> Result<String, ParseError> {
        self.parse_rcases_pattern_with_alts()
    }

    /// Parse one rcases pattern plus any trailing `|`-alternatives at the current
    /// bracket level: `leaf ( | leaf )*`.
    ///
    /// Reads the first leaf via [`Self::parse_rcases_leaf_pattern`], then while the
    /// next token is a `|` (`TokenKind::Pipe`) that is NOT the start of a new
    /// dedented line (so the `·`/`|` of a following focus block or enclosing
    /// `cases`/`induction` alt list is never swallowed), consumes the `|` and the
    /// next leaf, joining them with ` | `. The combined text round-trips through
    /// `RIntroPattern::parse`'s top-level-`|` splitter into an `Or`.
    ///
    /// A `|` that begins a new line is treated as belonging to an enclosing
    /// construct and terminates the alternation — alternation `|`s in the
    /// `rcases`/`obtain`/`rintro` surface sit on the same line as the pattern.
    fn parse_rcases_pattern_with_alts(&mut self) -> Result<String, ParseError> {
        let mut out = self.parse_rcases_leaf_pattern()?;
        while matches!(self.current_kind(), TokenKind::Pipe) && !self.current().preceded_by_newline
        {
            self.advance(); // consume `|`
            out.push_str(" | ");
            out.push_str(&self.parse_rcases_leaf_pattern()?);
        }
        Ok(out)
    }

    /// Parse a single rcases leaf pattern (no top-level `|` alternation).
    ///
    /// Accepts an anonymous-constructor pattern `⟨...⟩` (delegating to
    /// [`Self::parse_obtain_anon_pattern`]), a parenthesized pattern `(...)`
    /// (which may itself contain a `|` alternation, e.g. `rintro (hp | hq)` — the
    /// Lean-required form for an alternation under `rintro`), a wildcard `_`, a
    /// `rfl` equation-substitution leaf, or a bare identifier — the leaf forms
    /// `obtain`/`rcases`/`rintro` accept.
    fn parse_rcases_leaf_pattern(&mut self) -> Result<String, ParseError> {
        if matches!(self.current_kind(), TokenKind::LAngle) {
            self.parse_obtain_anon_pattern()
        } else if self.eat(&TokenKind::LParen) {
            // Parenthesized group: parse the full inner pattern (including any
            // `|` alternation) and return it WITHOUT the parens — the inner text
            // is already a complete pattern that `RIntroPattern::parse` reads. The
            // parens only group an alternation under `rintro` (`rintro (hp | hq)`).
            let inner = self.parse_rcases_pattern_with_alts()?;
            self.expect(&TokenKind::RParen)?;
            Ok(inner)
        } else if self.eat(&TokenKind::Underscore) {
            Ok("_".to_string())
        } else if self.eat(&TokenKind::Rfl) {
            // Top-level `rfl` leaf (e.g. `rintro rfl` or `rcases h with rfl`):
            // `rfl` is a keyword token, not an `Ident`, so accept it explicitly
            // and capture the literal text for `RIntroPattern::parse`.
            Ok("rfl".to_string())
        } else {
            self.expect_ident("rcases pattern")
        }
    }

    /// Parse `rintro pat₁ pat₂ …` in tactic mode.
    ///
    /// The leading keyword (`rintro`) has already been consumed. Parses one or
    /// more space-separated rintro patterns, each captured as its canonical
    /// `⟨...⟩` / name / `_` source text. Patterns are read via the SAME leaf
    /// reader (`parse_rcases_with_pattern`) that `rcases`/`obtain` use, so nested
    /// anonymous-constructor patterns like `⟨a, ⟨b, c⟩⟩` round-trip identically.
    ///
    /// Capturing each pattern as text (rather than letting the generic
    /// expr-list arg parser elaborate `⟨...⟩` as a term-mode anonymous
    /// constructor) is what lets the elaborator route `rintro` through the
    /// kernel-checked `intro` + `destruct_named_hypothesis` engine instead of the
    /// stale-FVar term path.
    ///
    /// Patterns sit on the same source line as `rintro`; parsing stops at the
    /// first newline-preceded token (or `;`/end-of-block) so a `;`-sequenced
    /// continuation or the next line's tactic is never swallowed.
    pub(crate) fn parse_tactic_rintro(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let mut patterns = Vec::new();
        let mut last_span = start;

        // Read leaf patterns greedily while they remain on the rintro line. A
        // bare `rfl` is a valid top-level leaf (`rintro rfl`): it is lexed as the
        // keyword token `TokenKind::Rfl`, so it must be admitted alongside the
        // ident/`_`/`⟨`/`(` starts. A leading `(` opens a parenthesized
        // alternation pattern (`rintro (hp | hq)`).
        while matches!(
            self.current_kind(),
            TokenKind::LAngle
                | TokenKind::LParen
                | TokenKind::Underscore
                | TokenKind::Ident(_)
                | TokenKind::Rfl
        ) && (patterns.is_empty() || !self.current().preceded_by_newline)
        {
            last_span = self.current().span;
            patterns.push(self.parse_rcases_with_pattern()?);
        }

        if patterns.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "rintro: expected at least one pattern".to_string(),
            });
        }

        Ok(SurfaceTactic::RIntro {
            span: start.merge(last_span),
            patterns,
        })
    }

    /// Parse `let h : T := val` in tactic mode
    pub(crate) fn parse_tactic_let(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let name = self.expect_ident("let")?;
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.parse_tactic_expr()?))
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
        let mut name = self.try_eat_ident();
        // `suffices _ : t by tac` — an anonymous (inaccessible) binder. Lean's
        // `binderIdent` is `ident | "_"`, but `_` lexes to `Underscore`, not
        // `Ident`, so `try_eat_ident` leaves it in place and the `Colon` expect
        // below would fail. Consume a stray leading `_` and keep the name
        // unnamed (the same path as the nameless `suffices : t` form).
        if name.is_none() && self.eat(&TokenKind::Underscore) {
            name = None;
        }
        self.expect(&TokenKind::Colon)?;
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
            let generalizing = self.parse_induction_generalizing_clause();
            (using_recursor, generalizing)
        };

        let alts = if self.eat(&TokenKind::With) {
            self.parse_induction_alts()?
        } else {
            Vec::new()
        };

        if is_cases {
            Ok(SurfaceTactic::Cases(start, Box::new(target), alts))
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

    /// Parse an optional `generalizing <ident>+` clause for `induction`.
    ///
    /// The identifiers name hypotheses reverted into the goal before running the
    /// recursor and re-introduced per case. Returns an empty vec when no
    /// `generalizing` clause is present. Stops at the `with` keyword and at any
    /// tactic keyword / non-identifier, per `parse_ident_list`.
    fn parse_induction_generalizing_clause(&mut self) -> Vec<String> {
        if matches!(self.current_kind(), TokenKind::Ident(name) if name == "generalizing") {
            self.advance();
            self.parse_ident_list()
        } else {
            Vec::new()
        }
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
            self.advance(); // consume the `|`
            let alt_span = self.current_span();
            // Lean 4's `inductionAlt` names the constructor with
            // `(group("@"? ident) <|> hole)` (`Init/Tactics.lean`), so `_` is a
            // legal alternative name meaning "every remaining case". The
            // elaborator already implements it — `builtins_phase3d_intro.rs`
            // looks up `alts.iter().find(|a| a.name == "_")` — but
            // `expect_ident` rejected the `_` token, so the whole `by` block
            // recovered to a synthetic sorry and that branch was dead code
            // (plan brick T5b / RC-Q).
            let name = if self.eat(&TokenKind::Underscore) {
                "_".to_string()
            } else {
                self.expect_ident("case alternative")?
            };
            // Lean's alt arguments are `binderIdent*`, so `_` is a legal
            // ANONYMOUS binder: `| succ k _ => …`. `parse_ident_list` stops at
            // `_`, which then failed `expect(FatArrow)` and recovered the whole
            // block to a synthetic sorry. Record it literally as "_", exactly
            // as `parse_tactic_case`/`parse_ident_list_to_named` already do.
            let mut args = Vec::new();
            loop {
                if let Some(n) = self.try_eat_ident() {
                    args.push(n);
                } else if self.eat(&TokenKind::Underscore) {
                    args.push("_".to_string());
                } else {
                    break;
                }
            }
            self.expect(&TokenKind::FatArrow)?;
            let tactics = self.tactic_seq_until_pipe()?;
            alts.push(SurfaceInductionAlt {
                span: alt_span,
                name,
                args,
                tactics,
            });
        }

        Ok(alts)
    }

    /// Parse tactic sequence until we hit `|` or a tactic block terminator
    fn tactic_seq_until_pipe(&mut self) -> Result<Vec<SurfaceTactic>, ParseError> {
        let mut tactics = Vec::new();

        while !self.at_tactic_end(0) && !matches!(self.current_kind(), TokenKind::Pipe) {
            let tac = self.tactic()?;
            tactics.push(tac);
            while self.eat(&TokenKind::Semicolon) {}
        }

        Ok(tactics)
    }

    /// Parse `rw [rule1, <- rule2, rule3]` optionally followed by `at loc`
    pub(crate) fn parse_tactic_rw(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let rules = self.parse_rw_rules()?;
        let loc = self.parse_tactic_location();
        Ok(SurfaceTactic::Rw(start, rules, loc))
    }

    /// Parse `rwa [rules] (at loc)?` — rewrite then close by assumption.
    ///
    /// Lean 4 core defines `rwa` as the macro
    /// `macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>`
    /// `  `(tactic| (rw $rws $(loc)?; assumption))`.
    ///
    /// We mirror that desugaring exactly: the same `[rules] (at loc)?` grammar
    /// as `rw` is parsed, and the result is a parenthesized sequence of the
    /// `rw` rewrite followed by `assumption`. No new tactic semantics are
    /// introduced — both sub-tactics are kernel-checked, so `rwa` inherits
    /// their soundness (`rw` builds an `Eq.mpr`-style proof term; `assumption`
    /// closes via a verified hypothesis reference).
    pub(crate) fn parse_tactic_rwa(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let rules = self.parse_rw_rules()?;
        let loc = self.parse_tactic_location();
        let rw = SurfaceTactic::Rw(start, rules, loc);
        let assumption = SurfaceTactic::Named {
            span: start,
            name: "assumption".to_string(),
            args: vec![],
        };
        Ok(SurfaceTactic::Paren(start, vec![rw, assumption]))
    }

    /// Parse `[rule1, <- rule2, rule3]` rewrite rule list
    fn parse_rw_rules(&mut self) -> Result<Vec<SurfaceRwRule>, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut rules = Vec::new();

        if !self.check(&TokenKind::RBracket) {
            loop {
                let rule_span = self.current_span();
                // Check for <- or <-
                let reverse = self.eat(&TokenKind::LeftArrow)
                    || (matches!(self.current_kind(), TokenKind::LAngle)
                        && matches!(self.peek_kind(1), Some(TokenKind::Minus))
                        && {
                            self.advance();
                            self.advance();
                            true
                        });

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
    ) -> Result<SurfaceTactic, ParseError> {
        // Check for `simp only`
        if matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "only") {
            self.advance();
            only = true;
        }

        let lemmas = if self.check(&TokenKind::LBracket) {
            self.parse_simp_lemmas()?
        } else {
            Vec::new()
        };

        let location = self.parse_tactic_location();

        Ok(SurfaceTactic::Simp {
            span: start,
            only,
            lemmas,
            location,
        })
    }

    /// Parse `[lemma1, lemma2, ...]` simp lemma list
    fn parse_simp_lemmas(&mut self) -> Result<Vec<SurfaceExpr>, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut lemmas = Vec::new();

        if !self.check(&TokenKind::RBracket) {
            loop {
                // Skip `<-`/`-` simp modifiers
                let _ = self.eat(&TokenKind::LeftArrow) || self.eat(&TokenKind::Minus);
                let e = self.expr()?;
                lemmas.push(e);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(lemmas)
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
            "_".to_string()
        } else {
            self.expect_ident("case")?
        };
        let mut binders = Vec::new();
        loop {
            match self.current_kind().clone() {
                TokenKind::Ident(binder) => {
                    self.advance();
                    binders.push(binder);
                }
                TokenKind::Underscore => {
                    self.advance();
                    binders.push("_".to_string());
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
                    self.advance();
                    binders.push(binder);
                }
                TokenKind::Underscore => {
                    self.advance();
                    binders.push("_".to_string());
                }
                _ => break,
            }
        }
        self.expect(&TokenKind::FatArrow)?;
        let tacs = self.indented_tactic_seq()?;
        Ok(SurfaceTactic::Case(start, "_".to_string(), binders, tacs))
    }

    /// Parse `first | tac1 | tac2 | ...`
    pub(crate) fn parse_tactic_first(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let mut branches = Vec::new();

        // Expect at least one `| tac_seq`
        while self.eat(&TokenKind::Pipe) {
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

    /// Parse `calc` steps inside tactic mode
    pub(crate) fn parse_tactic_calc(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let steps = self.calc_steps()?;
        Ok(SurfaceTactic::Calc(start, steps))
    }

    /// Parse `match discr1, discr2, ... with | pat => tac_seq | ...` in tactic mode
    ///
    /// Like expression-mode match but arm bodies are tactic sequences.
    /// Reference: Lean 4 `Lean.Parser.Tactic.match` in Tactic.lean
    pub(crate) fn parse_tactic_match(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        // Parse discriminant(s)
        let mut discrs = vec![self.parse_tactic_expr()?];
        while self.eat(&TokenKind::Comma) {
            discrs.push(self.parse_tactic_expr()?);
        }
        self.expect(&TokenKind::With)?;

        // Parse arms: | pat => tac_seq
        let mut arms = Vec::new();
        while self.eat(&TokenKind::Pipe) {
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

        Ok(SurfaceTactic::Match(start, discrs, arms))
    }

    // =========================================================================
    // Location parsing
    // =========================================================================

    /// Parse optional `at h1 h2`, `at h1 h2 ⊢`, or `at *` location specifier.
    pub(crate) fn parse_tactic_location(&mut self) -> SurfaceTacticLocation {
        if matches!(self.current_kind(), TokenKind::Ident(ref s) if s == "at") {
            self.advance();
            if self.eat(&TokenKind::Star) {
                let _ = self.eat(&TokenKind::Turnstile);
                SurfaceTacticLocation::Wildcard
            } else {
                let names = self.parse_ident_list();
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
