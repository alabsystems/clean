// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic block parser for Lean 4 `by` tactic sequences.
//!
//! Parses tactic syntax into `SurfaceTactic` AST nodes. Called from `by_body`
//! when parsing `by ...` expressions. Tactic keywords that are not lexer
//! keywords (e.g., `exact`, `apply`, `intro`) are lexed as `TokenKind::Ident`
//! and dispatched here by string matching.
//!
//! Compound tactic sub-parsers (have, let, suffices, cases/induction, rw, simp,
//! case, first, calc, location) live in the sibling `tactic_sub` module.
//!
//! Reference: Lean 4 source `src/Init/Tactics.lean`, `src/Lean/Parser/Tactic.lean`

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{Span, SurfaceExpr, SurfaceTactic, SurfaceTacticLocation};
use crate::tactic_patterns::TacticArgPattern;
use crate::ParseError;

/// Convert a parsed tactic location to Named args for registry dispatch.
///
/// `at h1 h2` → `[Ident("h1"), Ident("h2")]`
/// `at h1 h2 ⊢` → `[Ident("h1"), Ident("h2"), Ident("⊢")]`
/// `at *` → `[Ident("*")]`
/// no location → `[]`
fn location_to_args(span: Span, loc: SurfaceTacticLocation) -> Vec<SurfaceExpr> {
    match loc {
        SurfaceTacticLocation::Goal => vec![],
        SurfaceTacticLocation::Hyps(names) => names
            .into_iter()
            .map(|n| SurfaceExpr::Ident(span, n))
            .collect(),
        SurfaceTacticLocation::HypsAndGoal(names) => names
            .into_iter()
            .map(|n| SurfaceExpr::Ident(span, n))
            .chain(std::iter::once(SurfaceExpr::Ident(span, "⊢".to_string())))
            .collect(),
        SurfaceTacticLocation::Wildcard => {
            vec![SurfaceExpr::Ident(span, "*".to_string())]
        }
    }
}

impl Parser {
    /// Parse an expression in tactic context while preserving the outer
    /// tactic block boundary at same-indent newlines.
    ///
    /// This prevents term arguments like `have ... := calc ...` or
    /// `let x := f x` from consuming a following sibling tactic as an
    /// application argument when the sibling starts on the next line.
    pub(super) fn parse_tactic_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let saved = self.stop_app_at_newline_outer_indent;
        self.stop_app_at_newline_outer_indent = true;
        let expr = self.expr();
        self.stop_app_at_newline_outer_indent = saved;
        expr
    }

    /// Parse a tactic term that stops *before* a top-level `=` separator.
    ///
    /// Same newline-stop framing as [`parse_tactic_expr`], but enters the
    /// precedence chain one level below comparison (`bind_expr`), so a trailing
    /// `=` is left for the caller to consume. Used by `generalize (h :)? e = x`,
    /// where the `=` separates the term `e` from the target variable `x` and
    /// must not be absorbed into `e` as an `Eq` application.
    pub(super) fn parse_tactic_term_no_eq(&mut self) -> Result<SurfaceExpr, ParseError> {
        let saved = self.stop_app_at_newline_outer_indent;
        self.stop_app_at_newline_outer_indent = true;
        let expr = self.bind_expr();
        self.stop_app_at_newline_outer_indent = saved;
        expr
    }

    /// Parse a single argument-level term in tactic context.
    ///
    /// Unlike [`parse_tactic_expr`] (which parses a full expression, including
    /// left-associative application like `f x y`), this parses exactly one
    /// atom-level term — the precedence used for an individual application
    /// argument. So `h` parses to `Ident(h)` and `(f x)` parses to the
    /// parenthesized application, but two space-separated atoms are NOT joined
    /// into one application. Used by tactics that take several distinct term
    /// arguments separated by whitespace (e.g. `absurd h hn`).
    pub(super) fn parse_tactic_atom(&mut self) -> Result<SurfaceExpr, ParseError> {
        let saved = self.stop_app_at_newline_outer_indent;
        self.stop_app_at_newline_outer_indent = true;
        let expr = self.atom_expr();
        self.stop_app_at_newline_outer_indent = saved;
        expr
    }

    /// Parse a tactic sequence with an indentation frame.
    ///
    /// Pushes the current token's column as the block reference, parses tactics,
    /// then pops the indent frame. This ensures nested blocks (e.g., `repeat`,
    /// `all_goals`, `have ... by`) terminate correctly when a subsequent token
    /// dedents past this block's first element.
    ///
    /// Use this instead of bare `tactic_seq()` when the caller opens a new
    /// indentation-sensitive sub-block (tactic combinators, `by` proofs, etc.).
    /// Bracket-delimited contexts (`(...)`, `{...}`) don't need this — brackets
    /// already provide explicit boundaries.
    pub(super) fn indented_tactic_seq(&mut self) -> Result<Vec<SurfaceTactic>, ParseError> {
        let first_col = self.current().col;
        self.push_indent_for(first_col, "tactic block");
        let tacs = self.tactic_seq();
        self.pop_indent();
        tacs
    }

    /// Parse a tactic sequence (semicolon- or newline-separated).
    ///
    /// Stops at tactic block terminators (EOF, top-level keywords, unmatched
    /// closing brackets). Returns an empty vec if no tactics are found.
    pub(super) fn tactic_seq(&mut self) -> Result<Vec<SurfaceTactic>, ParseError> {
        let mut tactics = Vec::new();

        while !self.at_tactic_end(0) {
            let mut tac = self.tactic()?;

            // Check for `<;>` sequential focus combinator: `tac1 <;> tac2`
            // applies tac2 to every goal produced by tac1
            while self.eat(&TokenKind::SeqFocusOp) {
                let rhs = self.tactic()?;
                let span = tac.span().merge(rhs.span());
                tac = SurfaceTactic::SeqFocus(span, Box::new(tac), Box::new(rhs));
            }

            tactics.push(tac);

            // Consume optional semicolons between tactics
            while self.eat(&TokenKind::Semicolon) {}
        }

        Ok(tactics)
    }

    /// Parse a single tactic.
    ///
    /// Dispatches on the current token to the appropriate tactic parser.
    pub(super) fn tactic(&mut self) -> Result<SurfaceTactic, ParseError> {
        let span = self.current_span();

        match self.current_kind().clone() {
            // Keywords that are dedicated tokens
            TokenKind::Have => {
                self.advance();
                self.parse_tactic_have(span)
            }
            TokenKind::Show => {
                self.advance();
                let ty = self.parse_tactic_expr()?;
                // Phase 3D.6: keyword-to-Named routing — `show` dispatches via
                // TacticRegistry as a term-arg tactic (#2440).
                Ok(SurfaceTactic::Named {
                    span: span.merge(ty.span()),
                    name: "show".to_string(),
                    args: vec![ty],
                })
            }
            TokenKind::Suffices => {
                self.advance();
                self.parse_tactic_suffices(span)
            }
            TokenKind::Rfl => {
                self.advance();
                // Phase 3D.6: keyword-to-Named routing — `rfl` dispatches via
                // TacticRegistry as a nullary tactic (#2440).
                Ok(SurfaceTactic::Named {
                    span,
                    name: "rfl".to_string(),
                    args: vec![],
                })
            }
            TokenKind::Sorry => {
                self.advance();
                // Phase 3D.6: keyword-to-Named routing — `sorry` dispatches via
                // TacticRegistry as a nullary tactic (#2440).
                Ok(SurfaceTactic::Named {
                    span,
                    name: "sorry".to_string(),
                    args: vec![],
                })
            }
            TokenKind::Let => {
                self.advance();
                self.parse_tactic_let(span)
            }

            // Match tactic: match discr with | pat => tac_seq | ...
            // In tactic mode, arm bodies are tactic sequences, not expressions.
            // Reference: Lean 4 `Lean.Parser.Tactic.match` in Tactic.lean
            TokenKind::Match => {
                self.advance();
                self.parse_tactic_match(span)
            }

            // Parenthesized tactic sequence
            TokenKind::LParen => {
                self.advance();
                let inner = self.tactic_seq()?;
                let end = self.current_span();
                self.expect(&TokenKind::RParen)?;
                Ok(SurfaceTactic::Paren(span.merge(end), inner))
            }

            // Braced tactic sequence: `{ tac1; tac2 }`
            // In Lean 4, this is `tacticSeqBracketed` — uses focusAndDone wrapped
            // in closeUsingOrAdmit: focus on goal 0, run tactics, check closure.
            TokenKind::LBrace => {
                self.advance();
                let inner = self.tactic_seq()?;
                let end = self.current_span();
                self.expect(&TokenKind::RBrace)?;
                Ok(SurfaceTactic::FocusBlock(span.merge(end), inner))
            }

            // Focus dot: `· tac` or `· tac1; tac2`
            // In Lean 4, `·` (cdot) uses closeUsingOrAdmit which wraps
            // focusAndDone: focus on goal 0, run tactics, check closure.
            TokenKind::Cdot => {
                self.advance();
                let inner = self.tactic_seq_until_focus()?;
                Ok(SurfaceTactic::FocusBlock(span, inner))
            }

            // Identifiers: dispatch by tactic name
            TokenKind::Ident(ref name) => {
                let name = name.clone();
                self.parse_ident_tactic(span, &name)
            }

            // If none of the above matched, try parsing as a term-mode tactic
            _ => {
                let expr = self.parse_tactic_expr()?;
                let end = expr.span();
                Ok(SurfaceTactic::Term(span.merge(end), Box::new(expr)))
            }
        }
    }

    /// Dispatch identifier-based tactics (not lexer keywords).
    fn parse_ident_tactic(&mut self, span: Span, name: &str) -> Result<SurfaceTactic, ParseError> {
        match name {
            // 3C.3: ident-list tactics — hardcoded parsing, Named output (#2430 Wave 3)
            "intro" | "ext" | "funext" | "by_contra" => self.parse_ident_list_to_named(span, name),
            // 3C.4: nonempty-ident tactics — hardcoded parsing, Named output (#2430 Wave 3)
            "subst" | "revert" | "clear" | "rename_i" => {
                self.parse_nonempty_ident_to_named(span, name)
            }
            // Conv-mode navigation: with arguments
            "arg" | "enter" => self.parse_compound_ident_tactic(span, name),
            "rw" | "rewrite" | "rwa" | "simp" | "simp_only" | "simp_rw" | "cases" | "induction"
            | "case" | "next" | "first" | "calc" | "unfold" | "push_neg" | "dsimp" | "conv"
            | "all_goals" | "any_goals" | "try" | "repeat" | "focus" | "simpa" | "simpa_only" => {
                self.parse_compound_ident_tactic(span, name)
            }
            // 3C.7: compound-arg tactics — hardcoded parsing, Named output (#2430 Wave 3)
            "by_cases" => {
                self.advance();
                let hyp_name = self.expect_ident("by_cases")?;
                self.expect(&TokenKind::Colon)?;
                let prop = self.parse_tactic_expr()?;
                Ok(SurfaceTactic::Named {
                    span,
                    name: "by_cases".to_string(),
                    args: vec![SurfaceExpr::Ident(span, hyp_name), prop],
                })
            }
            // Lean 4 `wlog h : P` — introduce a WLOG assumption named `h` of type
            // `P`. Mirrors `by_cases`'s `<ident> : <prop>` shape (the `wlog`
            // handler expects exactly `[name, assumption]`). Without this arm the
            // generic expr-list parser stops at `:` and passes fewer than two
            // args, so `wlog h : a ≤ b` failed with MissingArgument. Take the
            // colon arm ONLY for the `<ident> :` shape; otherwise defer to the
            // identical generic path so the legacy space-separated 2-arg form
            // `wlog h Q` (used by existing tests) parses exactly as before.
            "wlog"
                if matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
                    && matches!(self.peek_kind(2), Some(TokenKind::Colon)) =>
            {
                self.advance();
                let hyp_name = self.expect_ident("wlog")?;
                self.expect(&TokenKind::Colon)?;
                let prop = self.parse_tactic_expr()?;
                Ok(SurfaceTactic::Named {
                    span,
                    name: "wlog".to_string(),
                    args: vec![SurfaceExpr::Ident(span, hyp_name), prop],
                })
            }
            "specialize" => {
                self.advance();
                let hyp = self.expect_ident("specialize")?;
                // `specialize h a₁ … aₙ` takes the hypothesis followed by one or
                // more argument terms separated by whitespace. Each argument is
                // parsed at atom precedence (like `absurd h hn`) so that
                // `specialize h 1 2` yields the distinct args `[h, 1, 2]` rather
                // than folding `1 2` into a single application `(1 2)`.
                //
                // The argument list is bounded to the SAME source line: when two
                // tactics sit at the same column on consecutive lines (e.g.
                // `specialize h 0` then `exact h`), `at_tactic_end` returns false
                // (same-column newline is not a dedent), so a bare
                // `!self.at_tactic_end(0)` loop would greedily swallow the next
                // tactic as an extra argument. Stopping at the first
                // newline-preceded token keeps `exact h` as its own tactic — the
                // same idiom `injection … with` uses above.
                let mut args = vec![SurfaceExpr::Ident(span, hyp)];
                if self.at_tactic_end(0) {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: "specialize expects at least one argument term".to_string(),
                    });
                }
                while !self.at_tactic_end(0) && !self.current().preceded_by_newline {
                    args.push(self.parse_tactic_atom()?);
                }
                Ok(SurfaceTactic::Named {
                    span,
                    name: "specialize".to_string(),
                    args,
                })
            }
            // `obtain pat (: T)? := e` — destructure a term (Lean 4 surface form).
            // Dedicated parser mirroring `have` so the `:=` separator and the
            // anonymous-constructor pattern ⟨...⟩ are handled, rather than the
            // generic comma-separated expr-list arg parser.
            "obtain" => {
                self.advance();
                self.parse_tactic_obtain(span)
            }
            // `rcases <term> with <pattern>` — destructure an existing hypothesis.
            // Dedicated parser so the `with`-clause and the anonymous-constructor
            // pattern ⟨...⟩ are handled. Without it the generic expr-list arg
            // parser stops at the `with` keyword, leaving it for `tactic_seq`,
            // which then mis-parses `with ⟨...⟩` as a fresh term-mode tactic and
            // desyncs (decl-level recovery). Reuses obtain's `⟨...⟩` pattern
            // reader so nested patterns round-trip identically.
            "rcases" => {
                self.advance();
                self.parse_tactic_rcases(span)
            }
            // `rintro pat₁ pat₂ …` — recursive intro with destructuring patterns.
            // Dedicated parser so the anonymous-constructor patterns ⟨...⟩ are
            // captured as canonical source text and routed (in the elaborator)
            // through the SAME kernel-checked `intro` + `destruct_named_hypothesis`
            // engine that backs `rcases`/`obtain`. Without it the generic
            // expr-list parser elaborates ⟨...⟩ as a term-mode anonymous
            // constructor against the (Pi) goal, which both fails for ∃/atomic
            // heads and captures stale FVars (the `UnknownFVar` dangling-reference
            // bug).
            "rintro" => {
                self.advance();
                self.parse_tactic_rintro(span)
            }
            // `generalize (h :)? e = x` — abstract the term `e` in the goal as a
            // fresh variable `x`. The optional `h :` prefix names a hypothesis
            // `h : e = x` recording the abstraction (Lean 4 `Lean.Parser.Tactic`
            // `generalize`). Arg shape:
            //   - bare form      `e = x`     → args = [e, Ident(x)]
            //   - hypothesis form `h : e = x` → args = [e, Ident(x), Ident(h)]
            // The elaborator (`builtins_wave3`) routes the 3-arg form through
            // `generalize_eq` (adds the `h : e = x` hypothesis) and the 2-arg form
            // through `generalize` (no hypothesis).
            //
            // The LHS term is parsed at the comparison sub-precedence
            // (`parse_tactic_term_no_eq` → `bind_expr`) so the top-level `=`
            // separator is NOT consumed as part of the term. The old code used
            // `parse_tactic_expr` (full `expr()`), which greedily ate `e = x` as a
            // single `Eq` application; the subsequent `expect(Eq)` then failed and
            // the whole `by` block recovered to a synthetic sorry — `generalize`
            // never reached the elaborator at all.
            "generalize" => {
                self.advance();
                // Optional `h :` hypothesis-name prefix. Disambiguated by a
                // leading `Ident` immediately followed by `:`. A bare term whose
                // head is an identifier (e.g. `generalize n + 0 = m`) is NOT
                // followed by `:`, so it stays in the term branch.
                let hyp_name = if matches!(self.current_kind(), TokenKind::Ident(_))
                    && matches!(self.peek_kind(1), Some(TokenKind::Colon))
                {
                    let name = self.expect_ident("generalize")?;
                    self.expect(&TokenKind::Colon)?;
                    Some(name)
                } else {
                    None
                };
                let term = self.parse_tactic_term_no_eq()?;
                self.expect(&TokenKind::Eq)?;
                let var_name = self.expect_ident("generalize")?;
                let mut args = vec![term, SurfaceExpr::Ident(span, var_name)];
                if let Some(hyp_name) = hyp_name {
                    args.push(SurfaceExpr::Ident(span, hyp_name));
                }
                Ok(SurfaceTactic::Named {
                    span,
                    name: "generalize".to_string(),
                    args,
                })
            }
            // `injection h with h1 h2 …` — the `with`-clause names the resulting
            // hypotheses.  Lean 4 grammar: `injection <term> (with <ident>+)?`.
            // Without a dedicated arm the generic expr-list parser stops at the
            // `with` keyword, leaving it for `tactic_seq`, which then tries to
            // parse `with …` as a fresh tactic (term-mode `expr()` starting at a
            // bare `with`).  That mis-parse greedily swallows the *following*
            // tactic (e.g. `obtain ⟨_, h⟩`) and chokes mid-pattern, triggering
            // decl-level recovery ("parser recovery produced raw declaration").
            // The clean injection elaborator ignores the `with` names (it is
            // registered as a `hyp_arg`), so we consume-and-discard them here.
            "injection" => {
                self.advance();
                let hyp = self.parse_tactic_expr()?;
                if self.eat(&TokenKind::With) {
                    // Consume the result-name idents (discarded; the elaborator
                    // does not use them).  The names sit on the same source line
                    // as `with`; stop at the first newline-preceded token so the
                    // *next* tactic (on its own line) is never swallowed.
                    while matches!(self.current_kind(), TokenKind::Ident(_))
                        && !self.current().preceded_by_newline
                    {
                        self.advance();
                    }
                }
                Ok(SurfaceTactic::Named {
                    span: span.merge(hyp.span()),
                    name: "injection".to_string(),
                    args: vec![hyp],
                })
            }
            // 3C.8: search tactics — Named output (#2430 Wave 3)
            "exact?" | "apply?" => {
                self.advance();
                Ok(SurfaceTactic::Named {
                    span,
                    name: name.to_string(),
                    args: vec![],
                })
            }
            _ => {
                // Unknown identifier: produce Named for registry dispatch.
                // When tactic patterns are available, use pattern-aware argument
                // parsing. Otherwise, fall back to generic expression-list parsing.
                self.advance();
                let args = self.parse_named_tactic_args_for(name)?;
                Ok(SurfaceTactic::Named {
                    span,
                    name: name.to_string(),
                    args,
                })
            }
        }
    }

    /// Parse compound identifier-based tactics that need sub-parsers or arguments.
    fn parse_compound_ident_tactic(
        &mut self,
        span: Span,
        name: &str,
    ) -> Result<SurfaceTactic, ParseError> {
        self.advance();
        match name {
            "arg" => self.parse_conv_arg(span),
            "enter" => self.parse_conv_enter(span),
            "rw" | "rewrite" => self.parse_tactic_rw(span),
            "rwa" => self.parse_tactic_rwa(span),
            "simp" => self.parse_tactic_simp(span, false),
            "simp_only" => self.parse_tactic_simp(span, true),
            "simp_rw" => self.parse_tactic_simp_rw(span),
            "cases" => self.parse_tactic_cases_induction(span, true),
            "induction" => self.parse_tactic_cases_induction(span, false),
            "case" => self.parse_tactic_case(span),
            "next" => self.parse_tactic_next(span),
            "first" => self.parse_tactic_first(span),
            "calc" => self.parse_tactic_calc(span),
            "unfold" => {
                let def_name = self.qualified_ident()?;
                let loc = self.parse_tactic_location();
                let mut args = vec![SurfaceExpr::Ident(span, def_name)];
                args.extend(location_to_args(span, loc));
                Ok(SurfaceTactic::Named {
                    span,
                    name: "unfold".to_string(),
                    args,
                })
            }
            "push_neg" => {
                let loc = self.parse_tactic_location();
                Ok(SurfaceTactic::Named {
                    span,
                    name: "push_neg".to_string(),
                    args: location_to_args(span, loc),
                })
            }
            "dsimp" => {
                let loc = self.parse_tactic_location();
                Ok(SurfaceTactic::Named {
                    span,
                    name: "dsimp".to_string(),
                    args: location_to_args(span, loc),
                })
            }
            "conv" => self.parse_conv_tactic(span),
            "all_goals" => Ok(SurfaceTactic::AllGoals(span, self.indented_tactic_seq()?)),
            "any_goals" => Ok(SurfaceTactic::AnyGoals(span, self.indented_tactic_seq()?)),
            "try" => Ok(SurfaceTactic::Try(span, self.indented_tactic_seq()?)),
            "repeat" => Ok(SurfaceTactic::Repeat(span, self.indented_tactic_seq()?)),
            "focus" => Ok(SurfaceTactic::Focus(span, self.indented_tactic_seq()?)),
            "simpa" => self.parse_tactic_simpa(span, false),
            "simpa_only" => self.parse_tactic_simpa(span, true),
            _ => unreachable!("tactic keyword not in parse dispatch table"),
        }
    }

    /// Parse `conv (at loc)? => tacs`
    fn parse_conv_tactic(&mut self, span: Span) -> Result<SurfaceTactic, ParseError> {
        let loc = self.parse_tactic_location();
        self.expect(&TokenKind::FatArrow)?;
        let tacs = self.indented_tactic_seq()?;
        Ok(SurfaceTactic::Conv(span, loc, tacs))
    }

    /// Parse arguments for a named tactic, using pattern-aware parsing when
    /// a [`TacticArgPattern`] is available for this tactic name.
    ///
    /// Falls back to [`parse_named_tactic_args`] (generic expression list)
    /// when no pattern is registered.
    fn parse_named_tactic_args_for(&mut self, name: &str) -> Result<Vec<SurfaceExpr>, ParseError> {
        match self.tactic_pattern(name).cloned() {
            Some(TacticArgPattern::Nullary) => Ok(Vec::new()),
            Some(TacticArgPattern::TermArg) => {
                if self.at_tactic_end(0) {
                    return Ok(Vec::new());
                }
                Ok(vec![self.parse_tactic_expr()?])
            }
            Some(TacticArgPattern::IdentList) => {
                let mut args = Vec::new();
                while let Some(ident) = self.try_eat_ident() {
                    args.push(SurfaceExpr::Ident(self.prev_span(), ident));
                }
                Ok(args)
            }
            Some(TacticArgPattern::NonemptyIdentList) => {
                let mut args = Vec::new();
                while let Some(ident) = self.try_eat_ident() {
                    args.push(SurfaceExpr::Ident(self.prev_span(), ident));
                }
                if args.is_empty() {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!("expected at least one identifier in {}", name),
                    });
                }
                Ok(args)
            }
            Some(TacticArgPattern::TwoTerms) => {
                // Parse exactly two argument-level terms separated by whitespace,
                // e.g. `absurd h hn` → [h, hn], `absurd (f x) (g y)` → [(f x), (g y)].
                // Each is parsed at atom precedence so the two terms are NOT
                // folded into a single left-associative application.
                let first = self.parse_tactic_atom()?;
                if self.at_tactic_end(0) {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!("{name} expects two term arguments, found one"),
                    });
                }
                let second = self.parse_tactic_atom()?;
                Ok(vec![first, second])
            }
            Some(TacticArgPattern::ExprList) => self.parse_named_tactic_args(),
            None => {
                // Built-in single-term tactics take exactly ONE term argument and
                // must STOP at a top-level comma. The default (patternless) parse
                // path — `parse_file`/`parse_expr` — has no registered pattern, so
                // without this these fall through to the comma-separated
                // `parse_named_tactic_args`: a `by`-block component of a tuple,
                // `(by exact 5, by exact 6)`, then has its `exact` swallow the
                // tuple separator (parsing `5, by exact 6` as a two-element comma
                // list), collapsing the whole tuple into one bogus `by` block.
                // `exact`/`apply`/`refine`/`change` never take a bare comma list in
                // Lean; `use`/`existsi` DO (multiple existential witnesses), so they
                // keep the comma-list fallback below. `at_tactic_end` already treats
                // a top-level comma as a terminator, so stopping here lets the
                // enclosing tuple/paren re-take the comma and build the `Prod.mk`.
                // An anon-ctor argument `exact ⟨a, b⟩` is unaffected: its commas are
                // inside `⟨⟩`, which `parse_tactic_expr` consumes as one term.
                if matches!(name, "exact" | "apply" | "refine" | "change") {
                    if self.at_tactic_end(0) {
                        return Ok(Vec::new());
                    }
                    return Ok(vec![self.parse_tactic_expr()?]);
                }
                // A patternless tactic's arguments sit on the SAME source line; a
                // token on a NEW line is the next tactic in the block, not an
                // argument. Without this, a no-argument tactic (`skip`, `done`,
                // `symm`, …) reaches the greedy comma/expr-list `parse_named_tactic_args`
                // and swallows the following newline-separated tactic — `by skip⏎
                // exact h` parsed `skip` consuming `exact h`, dropping it and
                // leaving the goal unsolved. Mirrors the same-line bound
                // `specialize`/`injection … with` enforce with `preceded_by_newline`.
                if self.current().preceded_by_newline {
                    return Ok(Vec::new());
                }
                self.parse_named_tactic_args()
            }
        }
    }

    /// Parse arguments for a `Named` tactic: comma-separated expressions
    /// until a tactic terminator (`;`, `<;>`, `|`, closing delimiter, dedent, EOF).
    /// Returns empty vec if no arguments follow the tactic name.
    fn parse_named_tactic_args(&mut self) -> Result<Vec<SurfaceExpr>, ParseError> {
        let mut args = Vec::new();
        if self.at_tactic_end(0) {
            return Ok(args);
        }
        args.push(self.parse_tactic_expr()?);
        while self.eat(&TokenKind::Comma) {
            if self.at_tactic_end(0) {
                break;
            }
            args.push(self.parse_tactic_expr()?);
        }
        Ok(args)
    }

    /// Parse ident-list tactics (`intro`, `ext`, `funext`, `by_contra`) → Named.
    /// Uses hardcoded ident-list parsing so it works without tactic patterns.
    fn parse_ident_list_to_named(
        &mut self,
        span: Span,
        name: &str,
    ) -> Result<SurfaceTactic, ParseError> {
        self.advance();
        // Accept both identifiers AND `_` as names. For binder-introducing tactics
        // (`intro`/`ext`/`funext`), `_` is an ANONYMOUS binder name, so `intro _`
        // must yield an `Ident("_")` arg — NOT stop the list and leave the `_` to be
        // mis-parsed as a stray term hole (which mints an unsolved metavar that leaks a
        // meta-encoded FVar into the proof: `intro _; rfl` failed closed with
        // `UnknownFVar`). `_` is read back as the name "_" by `expr_to_hyp_name`.
        let mut args: Vec<SurfaceExpr> = Vec::new();
        loop {
            if let Some(n) = self.try_eat_ident() {
                args.push(SurfaceExpr::Ident(self.prev_span(), n));
            } else if self.eat(&TokenKind::Underscore) {
                args.push(SurfaceExpr::Ident(self.prev_span(), "_".to_string()));
            } else {
                break;
            }
        }
        Ok(SurfaceTactic::Named {
            span,
            name: name.to_string(),
            args,
        })
    }

    /// Parse nonempty-ident-list tactics (`subst`, `revert`, `clear`, `rename_i`) → Named.
    /// Uses hardcoded ident-list parsing so it works without tactic patterns.
    fn parse_nonempty_ident_to_named(
        &mut self,
        span: Span,
        name: &str,
    ) -> Result<SurfaceTactic, ParseError> {
        self.advance();
        let idents = self.parse_ident_list();
        if idents.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected at least one identifier in {name}"),
            });
        }
        let args: Vec<SurfaceExpr> = idents
            .into_iter()
            .map(|n| SurfaceExpr::Ident(self.prev_span(), n))
            .collect();
        Ok(SurfaceTactic::Named {
            span,
            name: name.to_string(),
            args,
        })
    }

    /// Parse tactic sequence until we hit `·`, `|`, or a normal tactic block terminator.
    /// Used for focus-dot parsing: `· tac1; tac2` stops at the next `·`.
    fn tactic_seq_until_focus(&mut self) -> Result<Vec<SurfaceTactic>, ParseError> {
        let mut tactics = Vec::new();

        while !self.at_tactic_end(0)
            && !matches!(self.current_kind(), TokenKind::Cdot | TokenKind::Pipe)
        {
            let tac = self.tactic()?;
            tactics.push(tac);
            while self.eat(&TokenKind::Semicolon) {}
        }

        Ok(tactics)
    }
}
