// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match expression and pattern parsing.
//! Extracted from expr.rs as part of #307.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse match expression: match e with | pat => body | ...
    ///
    /// Also accepts Lean's annotated discriminant `match h : e with …`
    /// (`Lean/Parser/Term.lean:275`: `matchDiscr := optional (atomic
    /// (binderIdent " : ")) >> termParser`): the leading `binderIdent " : "`
    /// names a per-branch equality hypothesis `h : e = <pattern>`
    /// (`Lean/Elab/Match.lean:67`). Supported for a SINGLE discriminant;
    /// clean packs multiple discriminants into one `Prod.mk` scrutinee, which
    /// cannot carry a per-discriminant equation, so `h :` combined with a
    /// multi-discriminant match fails loud here rather than mis-binding.
    pub(super) fn match_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let hyp_name = self.match_discr_hyp_name();
        let mut scrutinees = vec![self.expr()?];
        while self.eat(&TokenKind::Comma) {
            if hyp_name.is_some() || self.match_discr_hyp_name().is_some() {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "match discriminant hypothesis (`match h : e with`) is not \
                              supported with multiple discriminants"
                        .to_string(),
                });
            }
            scrutinees.push(self.expr()?);
        }
        self.expect(&TokenKind::With)?;

        // RIGHT-nested tuple fold — `a, b, c` packs as `Prod.mk a (Prod.mk b c)`
        // — matching the arm-pattern fold below, which right-folds `p1, p2, p3`
        // into `Prod.mk p1 (Prod.mk p2 p3)`. The previous LEFT fold
        // (`Prod.mk (Prod.mk a b) c`) only agreed with the pattern shape for
        // exactly two discriminants; with three or more, field 1 of the
        // scrutinee (`c : Nat`) met the pattern's nested `Prod.mk (p2, p3)`
        // and every ≥3-discriminant match failed loud (brick B05,
        // docs/plans/GAP_SWEEP_2026-07-09.md — 3-discriminant diagonal).
        let scrutinee = scrutinees
            .into_iter()
            .rev()
            .reduce(|acc, expr| {
                let span = expr.span().merge(acc.span());
                SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(span, "Prod.mk".to_string())),
                    vec![SurfaceArg::positional(expr), SurfaceArg::positional(acc)],
                )
            })
            .expect("expected at least one scrutinee");

        // Column of this match's first arm `|`. A later `|` that begins a new
        // line at a *smaller* column belongs to an enclosing match and must
        // terminate this one — otherwise a nested match in an arm body greedily
        // swallows the outer match's subsequent arms (Track R, Basic.lean
        // `Ty.bitWidth`: the `.Vector` arm's inner `match` ate `| .Unit`). A
        // same-line `|`, or one indented at least as far as the first arm,
        // continues this match. Matches Lean 4 column-sensitive `matchAlts`.
        let arm_col = self.current().col;
        let mut arms = Vec::new();
        while self.check(&TokenKind::Pipe)
            && !(self.current().preceded_by_newline && self.current().col < arm_col)
        {
            self.advance(); // consume the `|`
            let mut patterns = vec![self.pattern_with_or()?];
            while self.eat(&TokenKind::Comma) {
                patterns.push(self.pattern_with_or()?);
            }
            self.expect(&TokenKind::FatArrow)?;
            // Parse the arm body under a layout guard pinned at the arm `|`
            // column. Without it, an arm body that *ends in a chained `let`*
            // (`| .SDiv => if … then … else let sl := …; let sr := …; .ok …`)
            // had its trailing implicit-let body parsed by an unguarded
            // `self.expr()` that swallowed the *next* arm's `| .URem` (parsed as
            // absolute-value `|…|` / a stray continuation) — exactly the
            // `semIntBinOp`/`semUnOp`/`semOverflowOp` shape in trust-ir's
            // `Semantics/Arith.lean`. Enabling `stop_app_at_newline_outer_indent`
            // with `arm_col` on the indent stack makes the body's application
            // spine stop at a new-line token (here the next `|`) whose column is
            // `<= arm_col`, ending the arm. (Track EF)
            let saved_stop = self.stop_app_at_newline_outer_indent;
            self.push_indent_for(arm_col, "match arm body");
            self.stop_app_at_newline_outer_indent = true;
            let body_result = self.expr();
            self.stop_app_at_newline_outer_indent = saved_stop;
            self.pop_indent();
            let body = body_result?;
            // Combine multiple patterns into a tuple pattern
            let pattern = if patterns.len() == 1 {
                patterns.pop().expect("patterns is non-empty")
            } else {
                patterns
                    .into_iter()
                    .rev()
                    .reduce(|acc, pat| SurfacePattern::Ctor("Prod.mk".to_string(), vec![pat, acc]))
                    .expect("patterns.len() > 1 in else branch")
            };
            arms.push(SurfaceMatchArm {
                span: pattern.span(),
                pattern,
                body,
            });
        }

        let end_span = arms.last().map_or(start_span, |a| a.body.span());
        Ok(SurfaceExpr::Match(
            start_span.merge(end_span),
            hyp_name,
            Box::new(scrutinee),
            arms,
        ))
    }

    /// Try to consume the annotated-discriminant prefix `h : ` (or `_ : `) of
    /// Lean's `matchDiscr` and return the hypothesis name. Mirrors the
    /// `atomic (binderIdent >> " : ")` in `Lean/Parser/Term.lean:275`: the
    /// prefix is recognized only when a bare identifier (or `_`) is
    /// IMMEDIATELY followed by a single `:` token — otherwise nothing is
    /// consumed and the discriminant parses as an ordinary term (`::`, `.`,
    /// parenthesized ascriptions, applications, … all fall through).
    fn match_discr_hyp_name(&mut self) -> Option<String> {
        let name = match self.current_kind() {
            TokenKind::Ident(name) => name.clone(),
            TokenKind::Underscore => "_".to_string(),
            _ => return None,
        };
        if self.peek_kind(1) != Some(&TokenKind::Colon) {
            return None;
        }
        self.advance(); // consume the binder ident / `_`
        self.advance(); // consume `:`
        Some(name)
    }

    /// Parse a pattern with optional `+ k` suffix for numeral addition patterns
    /// Example: `n + 1` matches `Nat.succ` patterns
    pub(super) fn pattern_with_addition(&mut self) -> Result<SurfacePattern, ParseError> {
        let mut pat = self.pattern()?;

        // Check for `+ k` suffix (numeral addition pattern)
        while self.check(&TokenKind::Plus) {
            self.advance();
            if let TokenKind::NatLit(k) = self.current_kind().clone() {
                // `n + k` successor patterns carry a small offset. A `k` beyond
                // `u64` is not a real successor-pattern offset; reject it loudly
                // rather than truncating to a wrong value.
                let k = k.to_u64().ok_or_else(|| ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!("numeral offset too large in pattern: {k}"),
                })?;
                self.advance();
                pat = SurfacePattern::NumeralAdd(Box::new(pat), k);
            } else {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!(
                        "expected numeral after + in pattern, got {:?}",
                        self.current_kind()
                    ),
                });
            }
        }

        Ok(pat)
    }

    /// Parse a pattern with optional `::` cons operator (right associative)
    /// Example: `x :: xs` matches list cons patterns
    pub(super) fn pattern_with_cons(&mut self) -> Result<SurfacePattern, ParseError> {
        let left = self.pattern_with_addition()?;

        if self.eat(&TokenKind::ColonColon) {
            let right = self.pattern_with_cons()?; // Right associative
            Ok(SurfacePattern::Ctor(
                "List.cons".to_string(),
                vec![left, right],
            ))
        } else {
            Ok(left)
        }
    }

    /// Parse a pattern with optional `|` or-pattern operator
    /// Example: `0 | 1` matches either 0 or 1
    /// Note: This is called at match arm level where `|` can also start a new arm,
    /// so we only consume `|` when followed by pattern-like tokens (not `=>`).
    pub(super) fn pattern_with_or(&mut self) -> Result<SurfacePattern, ParseError> {
        let left = self.pattern_with_cons()?;

        // Check if `|` is followed by something that looks like a pattern
        // (not `=>` which would start a new arm's body or indicate end of patterns)
        if self.check(&TokenKind::Pipe) {
            // Peek ahead to see if this is an or-pattern or a new arm
            let next_is_fat_arrow = self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| matches!(&t.kind, TokenKind::FatArrow));

            if !next_is_fat_arrow {
                self.advance(); // consume `|`
                let right = self.pattern_with_or()?; // Right associative
                return Ok(SurfacePattern::Or(Box::new(left), Box::new(right)));
            }
        }

        Ok(left)
    }

    /// Parse a pattern (simplified)
    pub(super) fn pattern(&mut self) -> Result<SurfacePattern, ParseError> {
        // Check for q-pattern: q(...) or ~q(...)
        // Part of #16: Qq quotation support - Phase 3
        // Part of #23: Qq Phase 4 - ~q syntax support (quote4 convention)
        //
        // Quote4 uses ~q(...) to distinguish pattern matching from construction.
        // We support both syntaxes:
        // - q(...): traditional syntax
        // - ~q(...): quote4 style, more explicit about pattern intent
        if let TokenKind::Ident(name) = self.current_kind() {
            if name == "q" && self.peek_kind(1) == Some(&TokenKind::LParen) {
                self.advance(); // consume 'q'
                self.advance(); // consume '('
                let inner = self.parse_q_body()?; // reuse from Phase 2
                self.expect(&TokenKind::RParen)?;
                return Ok(SurfacePattern::QPattern(Box::new(inner)));
            }
        }

        // Check for ~q(...) pattern (quote4 style)
        if self.check(&TokenKind::Tilde) {
            if let Some(TokenKind::Ident(name)) = self.peek_kind(1) {
                if name == "q" && self.peek_kind(2) == Some(&TokenKind::LParen) {
                    self.advance(); // consume '~'
                    self.advance(); // consume 'q'
                    self.advance(); // consume '('
                    let inner = self.parse_q_body()?;
                    self.expect(&TokenKind::RParen)?;
                    return Ok(SurfacePattern::QPattern(Box::new(inner)));
                }
            }
        }

        match self.current_kind().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                // Handle dotted names like T.t, Option.none, etc.
                //
                // Only merge a `.ident` into the head name when the dot is a
                // *contiguous* qualifier (`Option.none`, no surrounding space).
                // A space before the dot — as in `some .arcRef` — means `.arcRef`
                // is a separate leading-dot constructor *argument*, not part of
                // the head name; the constructor-argument loop below picks it up.
                let mut full_name = name;
                while self.dot_is_contiguous_qualifier() {
                    self.advance(); // consume dot
                    if let TokenKind::Ident(next_name) = self.current_kind().clone() {
                        full_name.push('.');
                        full_name.push_str(&next_name);
                        self.advance(); // consume ident
                    }
                }
                // Check for as-pattern: `n@pat`
                if self.eat(&TokenKind::At) {
                    let inner_pat = self.pattern()?;
                    return Ok(SurfacePattern::As(full_name, Box::new(inner_pat)));
                }
                // Check for constructor arguments
                // Use atomic_pattern to avoid nested constructor application
                // e.g., `MyList.cons head tail` should parse head and tail as
                // separate args, not `head tail` as a nested constructor
                let mut args = Vec::new();
                while self.is_pattern_arg_start() {
                    args.push(self.atomic_pattern()?);
                }
                // Trailing `..` ellipsis: `.Ctor ..` (optionally after explicit
                // patterns, e.g. `.Ctor x ..`). It stands for "every remaining
                // explicit field is a wildcard". Recorded as a trailing
                // `SurfacePattern::Ellipsis`; constructor arity expansion drops it
                // and materializes one `Wildcard` per remaining explicit field.
                if self.eat(&TokenKind::DotDot) {
                    args.push(SurfacePattern::Ellipsis);
                    return Ok(SurfacePattern::Ctor(full_name, args));
                }
                if args.is_empty() {
                    Ok(SurfacePattern::Var(full_name))
                } else {
                    Ok(SurfacePattern::Ctor(full_name, args))
                }
            }
            TokenKind::NatLit(n) => {
                self.advance();
                Ok(SurfacePattern::Lit(SurfaceLit::nat(n)))
            }
            // String-literal patterns: `match op with | "pack_lanes" => …`.
            // The canonical infer-match elaborator compiles literal patterns to
            // a `BEq.beq`/`ite` guard, so `String` is fully supported downstream
            // — only the surface pattern parser was missing the case.
            TokenKind::StringLit(s) => {
                self.advance();
                Ok(SurfacePattern::Lit(SurfaceLit::String(s)))
            }
            // Char-literal patterns: `match c with | 'a' => …`. Same
            // literal-guard lowering as strings.
            TokenKind::CharLit(c) => {
                self.advance();
                Ok(SurfacePattern::Lit(SurfaceLit::Char(c)))
            }
            TokenKind::SyntaxQuote(_) => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "syntax quotation patterns are not supported".to_string(),
            }),
            TokenKind::Rfl => {
                // `rfl` in PATTERN position is Lean's `@[match_pattern] def rfl`
                // (Init/Prelude.lean:352): an alias for the `Eq.refl`
                // constructor, NOT a binder — verified against Lean 4.33.0,
                // where `match (n : Nat) with | rfl => 0` is a type error, so
                // bare-`rfl`-as-variable is not a behavior we can lose (and
                // cannot be one here either: `rfl` lexes as a KEYWORD token,
                // never reaching the `Ident` arm). `Eq.refl` takes zero
                // explicit fields in pattern position (α and a are inductive
                // PARAMETERS), hence the empty argument vector. HEq keeps
                // needing its own `HEq.refl` spelling, exactly as in Lean.
                self.advance();
                Ok(SurfacePattern::Ctor("Eq.refl".to_string(), Vec::new()))
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(SurfacePattern::Wildcard)
            }
            TokenKind::Dot => {
                // Inaccessible pattern `.t` or `.(expr)` - patterns determined by unification
                self.advance();
                // Handle .(expr) - parenthesized inaccessible pattern
                if self.check(&TokenKind::LParen) {
                    self.advance();
                    let expr = self.expr()?;
                    self.expect(&TokenKind::RParen)?;
                    return Ok(SurfacePattern::Inaccessible(Box::new(expr)));
                }
                // A leading dot is DOTTED CONSTRUCTOR NOTATION: `.red` names the
                // constructor `red` of the expected type. It can never introduce a
                // BINDER.
                //
                // Parsing the tail as a plain pattern returns `Var(name)` for the
                // nullary case, because the `Ident` arm cannot see that a dot
                // preceded it. That silently turned a MISSPELLED constructor into a
                // catch-all binder: in
                //
                //     match c with
                //     | .reddd => 1      -- typo; parsed as a binder
                //     | .green => 2      -- dead arm
                //
                // every constructor matched the first arm, so `g Col.green` reduced
                // to `1` and the match still looked exhaustive. A typo changed the
                // program's meaning with no diagnostic. Re-tagging as a nullary
                // constructor makes the name resolve like every other dotted
                // constructor — and an unknown one now fails loudly.
                //
                // Applied-constructor patterns (`.cons h t`) already parse as
                // `Ctor`, so only the nullary case needs re-tagging.
                let inner = self.pattern()?;
                Ok(Self::retag_leading_dot_ctor(inner))
            }
            TokenKind::LParen => {
                self.advance();
                // Handle empty tuple pattern ()
                if self.check(&TokenKind::RParen) {
                    self.advance();
                    return Ok(SurfacePattern::Ctor("Unit.unit".to_string(), vec![]));
                }
                let first = self.pattern_with_cons()?;
                // Check for tuple pattern (p1, p2, ...)
                if self.eat(&TokenKind::Comma) {
                    let mut pats = vec![first];
                    if !self.check(&TokenKind::RParen) {
                        pats.push(self.pattern_with_cons()?);
                        while self.eat(&TokenKind::Comma) {
                            if self.check(&TokenKind::RParen) {
                                break;
                            }
                            pats.push(self.pattern_with_cons()?);
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    // Build nested Prod.mk pattern
                    let result = pats
                        .into_iter()
                        .rev()
                        .reduce(|acc, pat| {
                            SurfacePattern::Ctor("Prod.mk".to_string(), vec![pat, acc])
                        })
                        .expect("tuple pattern must have elements");
                    Ok(result)
                } else {
                    self.expect(&TokenKind::RParen)?;
                    Ok(first)
                }
            }
            TokenKind::LAngle => {
                // Anonymous-constructor pattern: ⟨p1, p2, ...⟩
                // Mirrors the tuple `(p1, p2, ...)` case and the existing
                // `let ⟨a, b⟩ := e` desugaring: build a right-nested `Prod.mk`
                // pattern. The elaborator's pattern-lambda tuple machinery
                // rewrites `Prod.mk` to the inferred tuple constructor
                // (`PProd.mk`, etc.) when the scrutinee is not a `Prod`.
                self.advance();
                // Handle empty anonymous constructor ⟨⟩
                if self.check(&TokenKind::RAngle) {
                    self.advance();
                    return Ok(SurfacePattern::Ctor("Unit.unit".to_string(), vec![]));
                }
                let mut pats = vec![self.pattern_with_cons()?];
                while self.eat(&TokenKind::Comma) {
                    if self.check(&TokenKind::RAngle) {
                        break;
                    }
                    pats.push(self.pattern_with_cons()?);
                }
                self.expect(&TokenKind::RAngle)?;
                let result = pats
                    .into_iter()
                    .rev()
                    .reduce(|acc, pat| SurfacePattern::Ctor("Prod.mk".to_string(), vec![pat, acc]))
                    .expect("anonymous-constructor pattern must have elements");
                Ok(result)
            }
            TokenKind::LBracket => {
                // List pattern: [] or [p1, p2, ...]
                self.advance();
                if self.check(&TokenKind::RBracket) {
                    self.advance();
                    // Empty list pattern: []
                    return Ok(SurfacePattern::Ctor("List.nil".to_string(), vec![]));
                }
                // Non-empty list pattern: [p1, p2, ...]
                let mut pats = vec![self.pattern_with_cons()?];
                while self.eat(&TokenKind::Comma) {
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                    pats.push(self.pattern_with_cons()?);
                }
                self.expect(&TokenKind::RBracket)?;
                // Build List.cons chain: [a, b, c] => List.cons a (List.cons b (List.cons c List.nil))
                let result = pats.into_iter().rev().fold(
                    SurfacePattern::Ctor("List.nil".to_string(), vec![]),
                    |acc, pat| SurfacePattern::Ctor("List.cons".to_string(), vec![pat, acc]),
                );
                Ok(result)
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected pattern, got {:?}", self.current_kind()),
            }),
        }
    }

    pub(super) fn is_pattern_arg_start(&self) -> bool {
        matches!(
            self.current_kind(),
            TokenKind::Ident(_)
                | TokenKind::NatLit(_)
                | TokenKind::StringLit(_)
                | TokenKind::CharLit(_)
                | TokenKind::Underscore
                | TokenKind::Rfl
                | TokenKind::Dot
                | TokenKind::LParen
                | TokenKind::LBracket
        )
    }

    /// Parse an atomic pattern - one that cannot itself take arguments.
    /// Used for constructor arguments to prevent incorrect nesting.
    /// For example, in `MyList.cons head tail`, `head` and `tail` should be
    /// parsed as separate atomic patterns, not `head` with `tail` as its argument.
    /// (#403: Fix multi-field constructor patterns)
    /// Re-tag a pattern parsed after a LEADING DOT as a constructor.
    ///
    /// `.red` is dotted constructor notation; the nullary case would otherwise
    /// arrive as `Var("red")` — a binder — so a typo'd constructor became a
    /// silent catch-all. Only the nullary shape needs it: `.cons h t` already
    /// parses as `Ctor`.
    fn retag_leading_dot_ctor(pat: SurfacePattern) -> SurfacePattern {
        match pat {
            SurfacePattern::Var(name) => SurfacePattern::Ctor(name, Vec::new()),
            other => other,
        }
    }

    pub(super) fn atomic_pattern(&mut self) -> Result<SurfacePattern, ParseError> {
        match self.current_kind().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                // Handle dotted names like T.t, Option.none, etc. Only a
                // *contiguous* dot (no surrounding whitespace) continues the
                // qualified name; a spaced `.foo` is a separate argument.
                let mut full_name = name;
                while self.dot_is_contiguous_qualifier() {
                    self.advance(); // consume dot
                    if let TokenKind::Ident(next_name) = self.current_kind().clone() {
                        full_name.push('.');
                        full_name.push_str(&next_name);
                        self.advance(); // consume ident
                    }
                }
                // Atomic pattern: no arguments collected
                Ok(SurfacePattern::Var(full_name))
            }
            TokenKind::NatLit(n) => {
                self.advance();
                Ok(SurfacePattern::Lit(SurfaceLit::nat(n)))
            }
            TokenKind::StringLit(s) => {
                self.advance();
                Ok(SurfacePattern::Lit(SurfaceLit::String(s)))
            }
            TokenKind::CharLit(c) => {
                self.advance();
                Ok(SurfacePattern::Lit(SurfaceLit::Char(c)))
            }
            TokenKind::Rfl => {
                // `rfl` in PATTERN position is Lean's `@[match_pattern] def rfl`
                // (Init/Prelude.lean:352): an alias for the `Eq.refl`
                // constructor, NOT a binder — verified against Lean 4.33.0,
                // where `match (n : Nat) with | rfl => 0` is a type error, so
                // bare-`rfl`-as-variable is not a behavior we can lose (and
                // cannot be one here either: `rfl` lexes as a KEYWORD token,
                // never reaching the `Ident` arm). `Eq.refl` takes zero
                // explicit fields in pattern position (α and a are inductive
                // PARAMETERS), hence the empty argument vector. HEq keeps
                // needing its own `HEq.refl` spelling, exactly as in Lean.
                self.advance();
                Ok(SurfacePattern::Ctor("Eq.refl".to_string(), Vec::new()))
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(SurfacePattern::Wildcard)
            }
            TokenKind::Dot => {
                self.advance();
                if self.check(&TokenKind::LParen) {
                    self.advance();
                    let expr = self.expr()?;
                    self.expect(&TokenKind::RParen)?;
                    return Ok(SurfacePattern::Inaccessible(Box::new(expr)));
                }
                // A leading dot is DOTTED CONSTRUCTOR NOTATION: `.red` names the
                // constructor `red` of the expected type. It can never introduce a
                // BINDER.
                //
                // Parsing the tail as a plain pattern returns `Var(name)` for the
                // nullary case, because the `Ident` arm cannot see that a dot
                // preceded it. That silently turned a MISSPELLED constructor into a
                // catch-all binder: in
                //
                //     match c with
                //     | .reddd => 1      -- typo; parsed as a binder
                //     | .green => 2      -- dead arm
                //
                // every constructor matched the first arm, so `g Col.green` reduced
                // to `1` and the match still looked exhaustive. A typo changed the
                // program's meaning with no diagnostic. Re-tagging as a nullary
                // constructor makes the name resolve like every other dotted
                // constructor — and an unknown one now fails loudly.
                //
                // Applied-constructor patterns (`.cons h t`) already parse as
                // `Ctor`, so only the nullary case needs re-tagging.
                let inner = self.atomic_pattern()?;
                Ok(Self::retag_leading_dot_ctor(inner))
            }
            TokenKind::LParen => {
                // Parenthesized pattern - can contain full patterns with arguments,
                // OR a tuple pattern `(p1, p2, ...)`. As a constructor *argument*
                // (e.g. `some (lanes, _)`), the parenthesized tuple must be parsed
                // here too; previously only a single parenthesized pattern was
                // accepted, so `(a, b)` hit `expect(RParen)` on the comma and
                // tripped parser recovery. Mirror the top-level `pattern()` LParen
                // handling: build a right-nested `Prod.mk` for the tuple case.
                self.advance(); // consume '('
                if self.check(&TokenKind::RParen) {
                    // () is Unit.unit
                    self.advance();
                    return Ok(SurfacePattern::Ctor("Unit.unit".to_string(), vec![]));
                }
                let first = self.pattern_with_cons()?;
                if self.eat(&TokenKind::Comma) {
                    let mut pats = vec![first];
                    if !self.check(&TokenKind::RParen) {
                        pats.push(self.pattern_with_cons()?);
                        while self.eat(&TokenKind::Comma) {
                            if self.check(&TokenKind::RParen) {
                                break;
                            }
                            pats.push(self.pattern_with_cons()?);
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    let result = pats
                        .into_iter()
                        .rev()
                        .reduce(|acc, pat| {
                            SurfacePattern::Ctor("Prod.mk".to_string(), vec![pat, acc])
                        })
                        .expect("tuple pattern must have elements");
                    Ok(result)
                } else {
                    self.expect(&TokenKind::RParen)?;
                    Ok(first)
                }
            }
            TokenKind::LBracket => {
                // List pattern - delegate to full pattern parser
                self.pattern()
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected pattern argument, got {:?}", self.current_kind()),
            }),
        }
    }
}
