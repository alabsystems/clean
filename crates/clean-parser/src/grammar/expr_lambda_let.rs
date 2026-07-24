// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lambda, let, if, forall, by, calc, and anonymous constructor parsing.
//! Extracted from expr.rs as part of #307.

use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

use super::decl::EquationArmBoundary;
use super::Parser;

impl Parser {
    /// Parse lambda body: x y z => e or (x : T) (y : U) => e
    /// Returns (`lambda_expr`, `is_pattern_matching`) where `is_pattern_matching`
    /// indicates if the lambda used pattern syntax (important for layout)
    pub(super) fn lambda_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Check for pattern-matching lambda: fun | pat => e | pat2 => e2
        //
        // Each arm may carry *several* comma-separated patterns, one per
        // curried parameter: `fun | 0, 0 => 0 | _, _ => 1` is a two-argument
        // function matching on both arguments. This mirrors Lean's `matchAlts`.
        //
        // The desugaring keeps the *single* fresh scrutinee binder `_x` that
        // the elaborator already understands (`try_elab_curried_pattern_lambda`
        // in `clean-elab`), and combines each arm's comma-separated patterns
        // into a right-nested `Prod.mk` tuple pattern. The elaborator reads the
        // curried arity off that tuple pattern, splits `_x` into one eta-local
        // per argument, and rebuilds the tupled scrutinee itself — so the
        // parser must NOT pre-tuple the scrutinee. The single-pattern case
        // (`fun | p => e`) is the arity-1 specialisation and is unchanged
        // (`combine_patterns_as_tuple` returns the lone pattern as-is).
        if self.check(&TokenKind::Pipe) {
            // Parse each arm as a list of comma-separated patterns.
            let mut raw_arms: Vec<(Vec<SurfacePattern>, SurfaceExpr)> = Vec::new();
            while self.eat(&TokenKind::Pipe) {
                let mut patterns = vec![self.pattern_with_cons()?];
                while self.eat(&TokenKind::Comma) {
                    patterns.push(self.pattern_with_cons()?);
                }
                self.expect(&TokenKind::FatArrow)?;
                // Parse body until next | or end of lambda
                let body = self.lambda_arm_body()?;
                raw_arms.push((patterns, body));
            }

            // Arity is the pattern count of the first arm. Lean requires every
            // arm to have the same count; if a later arm disagrees we surface a
            // parse error rather than silently building an ill-typed tuple.
            let arity = raw_arms.first().map_or(1, |(pats, _)| pats.len());

            let mut arms = Vec::with_capacity(raw_arms.len());
            for (patterns, body) in raw_arms {
                if patterns.len() != arity {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!(
                            "match-lambda arm has {} pattern(s) but expected {arity}",
                            patterns.len()
                        ),
                    });
                }
                let pat_span = patterns.first().map_or(start_span, SurfacePattern::span);
                let pattern = Self::combine_patterns_as_tuple(patterns);
                arms.push(SurfaceMatchArm {
                    span: pat_span,
                    pattern,
                    body,
                });
            }

            // Single scrutinee binder `_x`; the elaborator's curried-pattern
            // path peels the tuple arity from the arm patterns.
            let scrutinee = SurfaceExpr::Ident(start_span, "_x".to_string());
            let binder = SurfaceBinder::new("_x".to_string(), None, SurfaceBinderInfo::Explicit);
            let match_expr = SurfaceExpr::Match(start_span, None, Box::new(scrutinee), arms);
            // Return as PatternMatchLambda to signal app_expr to stop
            return Ok(SurfaceExpr::PatternMatchLambda(
                start_span,
                vec![binder],
                Box::new(match_expr),
            ));
        }

        // Destructuring lambda: `fun (a, b) => e`, `fun ⟨a, b⟩ => e`, or a mix
        // like `fun x (a, b) => e`. Lean 4 treats a tuple/anonymous-constructor
        // binder as a *single* parameter that is pattern-matched, so the lambda
        // arity is one per pattern — not one per name inside the pattern.
        //
        // The plain `self.binders()` path flattens `(a, b)` into two separate
        // binders, which silently changes the function's arity. Detect the
        // destructuring case here and desugar to a `PatternMatchLambda` over
        // fresh scrutinee variables, identical to `fun | (a, b) => e`.
        if self.fun_binders_contain_destructuring() {
            return self.destructuring_lambda_body(start_span);
        }

        // Regular lambda: fun x => e
        let binders = self.binders()?;
        self.expect(&TokenKind::FatArrow)?;
        let body = self.expr()?;
        let span = start_span.merge(body.span());
        Ok(SurfaceExpr::Lambda(span, binders, Box::new(body)))
    }

    /// Combine a non-empty list of patterns into a single (possibly tuple)
    /// pattern. A single pattern is returned as-is; several patterns become a
    /// right-nested `Prod.mk` tuple pattern — `[p0, p1, p2]` ⇒
    /// `Prod.mk p0 (Prod.mk p1 p2)`. This is the pattern-side mirror of the
    /// scrutinee tuple built in the match-lambda desugaring, and matches the
    /// combination performed by multi-scrutinee `match` (see `match_body`).
    fn combine_patterns_as_tuple(patterns: Vec<SurfacePattern>) -> SurfacePattern {
        patterns
            .into_iter()
            .rev()
            .reduce(|acc, pat| SurfacePattern::Ctor("Prod.mk".to_string(), vec![pat, acc]))
            // Only reached if `patterns` were empty, which callers never do
            // (each arm parses at least one pattern before the first comma).
            .unwrap_or(SurfacePattern::Wildcard)
    }

    /// Decide whether the upcoming `fun` binder sequence contains at least one
    /// destructuring binder (a tuple `( .. , .. )` or anonymous constructor
    /// `⟨ .. ⟩`) that must be desugared via pattern matching.
    ///
    /// A leading `⟨` is always a destructuring binder. A leading `(` is only a
    /// destructuring binder when it encloses a top-level comma before the
    /// matching `)` — `(x : T)` and `(x)` are ordinary binders and must keep
    /// the fast `self.binders()` path.
    fn fun_binders_contain_destructuring(&self) -> bool {
        let mut offset = 0;
        loop {
            match self.peek_kind(offset) {
                Some(TokenKind::LAngle) => return true,
                Some(TokenKind::LParen) => {
                    if self.paren_group_has_top_level_comma(offset) {
                        return true;
                    }
                    // Skip the balanced `( .. )` group and continue scanning.
                    match self.skip_balanced_group(offset) {
                        Some(next) => offset = next,
                        None => return false,
                    }
                }
                // Any other binder atom (ident, `_`, `{`, `[`) keeps scanning;
                // anything else (`=>`, EOF, ...) ends the binder list.
                Some(TokenKind::Ident(_) | TokenKind::Underscore) => offset += 1,
                _ => return false,
            }
        }
    }

    /// The closing token that balances `opener`, if `opener` is a bracket
    /// opener. Bracket matching is *type-aware*: a `(` is only balanced by a
    /// `)`, never by a `]`, `}`, or `⟩`. Using a single depth counter that
    /// treats every closer as interchangeable miscounts on mixed-bracket
    /// nesting — e.g. the comma inside `Foo {a, b}` would be mistaken for a
    /// paren-level tuple separator. Returns `None` for non-openers.
    fn matching_closer(opener: &TokenKind) -> Option<TokenKind> {
        match opener {
            TokenKind::LParen => Some(TokenKind::RParen),
            TokenKind::LBracket => Some(TokenKind::RBracket),
            TokenKind::LBrace => Some(TokenKind::RBrace),
            TokenKind::LAngle => Some(TokenKind::RAngle),
            _ => None,
        }
    }

    /// Does the `( .. )` group beginning at `peek_kind(open_offset)` look like a
    /// *tuple-destructuring* binder (`(a, b)`) — i.e. it contains a comma at the
    /// group's own nesting depth that is a tuple separator?
    ///
    /// Bracket nesting is tracked with a *type-aware* stack: an opener of
    /// type `T` pushes the closer that balances it, and only that closer pops
    /// it. A closer that does not match the top of the stack ends the scan
    /// (mismatched / malformed nesting) rather than silently corrupting the
    /// depth.
    ///
    /// A depth-1 comma is a tuple separator only when no depth-1 colon has been
    /// seen before it. A typed binder whose type itself contains a top-level
    /// comma — e.g. `(ih : forall (c : Nat), P c)` or `(p : Σ x, Q x)` — has its
    /// binder colon at depth 1 *before* that comma, so it is correctly treated
    /// as an ordinary typed binder, not a tuple. (The inner `forall`/`Σ` comma
    /// belongs to that quantifier, not to the paren group.) Without this guard
    /// the binder is misrouted into the pattern-matching path and fails with
    /// "expected RParen, got Colon".
    fn paren_group_has_top_level_comma(&self, open_offset: usize) -> bool {
        let mut stack: Vec<TokenKind> = Vec::new();
        let mut saw_top_level_colon = false;
        let mut offset = open_offset;
        loop {
            match self.peek_kind(offset) {
                Some(kind) => match Self::matching_closer(kind) {
                    Some(closer) => stack.push(closer),
                    None => {
                        if stack.len() == 1 {
                            match kind {
                                // A depth-1 colon marks this as a typed binder;
                                // any later depth-1 comma belongs to the type
                                // (e.g. a `forall`/`Σ` quantifier), not a tuple.
                                TokenKind::Colon => saw_top_level_colon = true,
                                TokenKind::Comma => return !saw_top_level_colon,
                                _ => {}
                            }
                        }
                        if *kind == TokenKind::Eof {
                            return false;
                        }
                        if Self::is_closer(kind) {
                            match stack.last() {
                                Some(expected) if expected == kind => {
                                    stack.pop();
                                    if stack.is_empty() {
                                        return false;
                                    }
                                }
                                // Mismatched or unbalanced closer: the group
                                // is malformed for our purposes — stop here.
                                _ => return false,
                            }
                        }
                    }
                },
                None => return false,
            }
            offset += 1;
        }
    }

    /// Given an opener at `peek_kind(open_offset)`, return the offset just past
    /// the matching closer, or `None` if the group is unterminated or the
    /// nesting is mismatched. Bracket matching is type-aware (see
    /// [`Self::matching_closer`]).
    fn skip_balanced_group(&self, open_offset: usize) -> Option<usize> {
        let mut stack: Vec<TokenKind> = Vec::new();
        let mut offset = open_offset;
        loop {
            let kind = self.peek_kind(offset)?;
            match Self::matching_closer(kind) {
                Some(closer) => stack.push(closer),
                None => {
                    if *kind == TokenKind::Eof {
                        return None;
                    }
                    if Self::is_closer(kind) {
                        match stack.last() {
                            Some(expected) if expected == kind => {
                                stack.pop();
                                if stack.is_empty() {
                                    return Some(offset + 1);
                                }
                            }
                            // Mismatched / unbalanced closer.
                            _ => return None,
                        }
                    }
                }
            }
            offset += 1;
        }
    }

    /// Is `kind` a bracket closer (`)`, `]`, `}`, or `⟩`)?
    fn is_closer(kind: &TokenKind) -> bool {
        matches!(
            kind,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace | TokenKind::RAngle
        )
    }

    /// Parse a `fun` binder sequence that contains one or more destructuring
    /// binders and desugar it to a `PatternMatchLambda`.
    ///
    /// Each parameter becomes a fresh scrutinee variable; destructuring
    /// parameters are wrapped in a single-arm `match`. Ordinary binders pass
    /// through unchanged. For example:
    ///
    /// - `fun (a, b) => a` ⇒ `fun _x => match _x with | (a, b) => a`
    /// - `fun x (a, b) => a` ⇒ `fun x _x1 => match _x1 with | (a, b) => a`
    fn destructuring_lambda_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Collected lambda binders (fresh names for patterns).
        let mut binders: Vec<SurfaceBinder> = Vec::new();
        // (scrutinee_name, pattern) for each destructuring parameter, in order.
        let mut patterns: Vec<(String, Span, SurfacePattern)> = Vec::new();
        let mut fresh_idx = 0_usize;

        loop {
            match self.current_kind() {
                TokenKind::LAngle => {
                    let span = self.current_span();
                    let pattern = self.pattern()?;
                    let name = self.fresh_destructuring_name(&mut fresh_idx);
                    binders.push(SurfaceBinder::new(
                        name.clone(),
                        None,
                        SurfaceBinderInfo::Explicit,
                    ));
                    patterns.push((name, span, pattern));
                }
                TokenKind::LParen if self.paren_group_has_top_level_comma(0) => {
                    let span = self.current_span();
                    let pattern = self.pattern()?;
                    let name = self.fresh_destructuring_name(&mut fresh_idx);
                    binders.push(SurfaceBinder::new(
                        name.clone(),
                        None,
                        SurfaceBinderInfo::Explicit,
                    ));
                    patterns.push((name, span, pattern));
                }
                TokenKind::LParen => binders.extend(self.explicit_binders()?),
                TokenKind::LBrace => binders.extend(self.implicit_binders()?),
                TokenKind::LBracket => binders.extend(self.instance_binders()?),
                TokenKind::Ident(_) | TokenKind::Underscore => {
                    // Reuse the simple-binder logic by parsing a single binder.
                    binders.push(self.simple_lambda_binder()?);
                }
                _ => break,
            }

            if self.check(&TokenKind::FatArrow) {
                break;
            }
        }

        self.expect(&TokenKind::FatArrow)?;
        let body = self.expr()?;
        let span = start_span.merge(body.span());

        // Wrap the body in nested single-arm matches, innermost (last pattern)
        // first so the textual binder order is preserved.
        let mut result = body;
        for (name, pat_span, pattern) in patterns.into_iter().rev() {
            let scrutinee = SurfaceExpr::Ident(pat_span, name);
            let arm = SurfaceMatchArm {
                span: pat_span,
                pattern,
                body: result,
            };
            result = SurfaceExpr::Match(pat_span, None, Box::new(scrutinee), vec![arm]);
        }

        Ok(SurfaceExpr::PatternMatchLambda(
            span,
            binders,
            Box::new(result),
        ))
    }

    /// Mint a fresh, source-invisible scrutinee name for a destructuring binder.
    fn fresh_destructuring_name(&self, idx: &mut usize) -> String {
        let name = if *idx == 0 {
            "_x".to_string()
        } else {
            format!("_x{idx}")
        };
        *idx += 1;
        name
    }

    /// Parse a single simple `fun` binder: `x` or `x : T` or `_` (with optional
    /// type annotation). Used by the destructuring path for ordinary params.
    fn simple_lambda_binder(&mut self) -> Result<SurfaceBinder, ParseError> {
        let span = self.current_span();
        let name = match self.current_kind() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.advance();
                name
            }
            TokenKind::Underscore => {
                self.advance();
                "_".to_string()
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "expected lambda binder".to_string(),
                })
            }
        };
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.arrow_expr()?))
        } else {
            None
        };
        Ok(SurfaceBinder {
            span,
            name,
            ty,
            default: None,
            info: SurfaceBinderInfo::Explicit,
        })
    }

    /// Parse the body of a lambda arm (until next | or lambda end)
    pub(super) fn lambda_arm_body(&mut self) -> Result<SurfaceExpr, ParseError> {
        // The tricky part: we need to parse an expression but stop at the next |
        // We use a limited expression parser that doesn't consume |
        self.lambda_arm_expr()
    }

    /// Parse an expression for lambda arm body (stops at |)
    /// This is a simplified expression parser that doesn't allow multi-atom applications
    /// to help with layout-free parsing of pattern-matching lambdas
    pub(super) fn lambda_arm_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Parse a simple expression - just an atom with optional projections
        // This is a conservative approach that works for most lambda arm bodies
        // Full applications would need layout information to disambiguate
        let expr = self.atom_expr()?;

        // Allow projections on the result
        let mut result = expr;
        while self.check(&TokenKind::Dot) {
            self.advance(); // consume dot
            match self.current_kind().clone() {
                TokenKind::Ident(field) => {
                    let field_span = self.current_span();
                    self.advance();
                    let span = result.span().merge(field_span);
                    result = SurfaceExpr::Proj(span, Box::new(result), Projection::Named(field));
                }
                TokenKind::NatLit(n) => {
                    let field_span = self.current_span();
                    let index =
                        n.to_u64()
                            .and_then(|v| u32::try_from(v).ok())
                            .ok_or_else(|| ParseError::NumericOverflow {
                                value: n.to_u64().unwrap_or(u64::MAX),
                                max: u64::from(u32::MAX),
                            })?;
                    self.advance();
                    let span = result.span().merge(field_span);
                    result = SurfaceExpr::Proj(span, Box::new(result), Projection::Index(index));
                }
                other => {
                    if let Some(kw_str) = other.as_keyword_str() {
                        let field_span = self.current_span();
                        self.advance();
                        let span = result.span().merge(field_span);
                        result = SurfaceExpr::Proj(
                            span,
                            Box::new(result),
                            Projection::Named(kw_str.to_string()),
                        );
                    } else {
                        break;
                    }
                }
            }
        }

        Ok(result)
    }

    /// Parse forall body: (x : T) (y : U), B
    pub(super) fn forall_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let binders = self.binders()?;

        // Bounded/conditional quantifiers (Mathlib macros):
        //   ∀ x ∈ S, P x   ≡  ∀ x, x ∈ S → P x
        //   ∀ n > 0, P n   ≡  ∀ n, n > 0 → P n
        if let Some(last_binder) = binders.last() {
            if let Some(guard) = self.try_bounded_guard(last_binder)? {
                self.expect(&TokenKind::Comma)?;
                let body = self.expr()?;
                let guard_span = guard.span();
                let body_span = body.span();
                let guarded_body = SurfaceExpr::Arrow(
                    guard_span.merge(body_span),
                    Box::new(guard),
                    Box::new(body),
                );
                let span = start_span.merge(guarded_body.span());
                return Ok(SurfaceExpr::Pi(span, binders, Box::new(guarded_body)));
            }
        }

        // Filter quantifier: ∀ᶠ x in F, body (Mathlib Filter.Eventually)
        // When `in` appears instead of `,`, parse the filter and then the body
        if self.eat(&TokenKind::In) {
            let _filter = self.arrow_expr()?;
            self.expect(&TokenKind::Comma)?;
            let body = self.expr()?;
            let span = start_span.merge(body.span());
            return Ok(SurfaceExpr::Pi(span, binders, Box::new(body)));
        }

        self.expect(&TokenKind::Comma)?;
        let body = self.expr()?;
        let span = start_span.merge(body.span());
        Ok(SurfaceExpr::Pi(span, binders, Box::new(body)))
    }

    /// Parse a bounded/conditional guard after a quantifier binder.
    ///
    /// Examples (Mathlib macros):
    /// - `∀ x ∈ S, ...`
    /// - `∀ n > 0, ...`
    ///
    /// The guard token appears *after* the binder, so we synthesize the left operand
    /// from the binder name.
    pub(super) fn try_bounded_guard(
        &mut self,
        binder: &SurfaceBinder,
    ) -> Result<Option<SurfaceExpr>, ParseError> {
        let left = SurfaceExpr::Ident(binder.span, binder.name.clone());

        let (kind, op) = match self.current_kind() {
            TokenKind::Elem => (TokenKind::Elem, None),
            TokenKind::NotElem => (TokenKind::NotElem, None),
            TokenKind::Lt => (TokenKind::Lt, Some("LT.lt")),
            TokenKind::Le => (TokenKind::Le, Some("LE.le")),
            TokenKind::Gt => (TokenKind::Gt, Some("GT.gt")),
            TokenKind::Ge => (TokenKind::Ge, Some("GE.ge")),
            TokenKind::Eq => (TokenKind::Eq, Some("Eq")),
            TokenKind::Ne => (TokenKind::Ne, Some("Ne")),
            TokenKind::Subset => (TokenKind::Subset, Some("HasSubset.Subset")),
            TokenKind::ProperSubset => (TokenKind::ProperSubset, Some("HasSSubset.SSubset")),
            _ => return Ok(None),
        };

        // Consume the guard operator.
        self.expect(&kind)?;

        let right = self.arrow_expr()?;
        let span = binder.span.merge(right.span());

        // Membership is a special case: `a ∈ b` desugars to `Membership.mem b a`.
        if matches!(kind, TokenKind::Elem | TokenKind::NotElem) {
            let mem_expr = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(
                    binder.span,
                    "Membership.mem".to_string(),
                )),
                vec![SurfaceArg::positional(right), SurfaceArg::positional(left)],
            );

            if matches!(kind, TokenKind::NotElem) {
                return Ok(Some(SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(binder.span, "Not".to_string())),
                    vec![SurfaceArg::positional(mem_expr)],
                )));
            }

            return Ok(Some(mem_expr));
        }

        let op = op.expect("op is Some for non-membership guards");
        Ok(Some(SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(binder.span, op.to_string())),
            vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
        )))
    }

    /// Parse the value of a term-level `let` binding (`let x := <value>`) with
    /// layout-aware termination, matching Lean 4's `Term.let` behavior.
    ///
    /// In Lean 4 the `let` term is `withPosition ("let " letDecl) >> optSemicolon
    /// term`: the value `term` is parsed within the `let` keyword's saved column,
    /// so a following line that dedents to (or below) the `let` keyword's column
    /// begins the *body*, not a continuation of the value. Application arguments
    /// only continue across a newline while they stay strictly more indented than
    /// the `let` keyword (`checkColGt`).
    ///
    /// `let_col` is the 0-based column of the `let`/`letI` keyword that opened
    /// this binding. We push it as the reference column and enable
    /// `stop_app_at_newline_outer_indent` so `app_expr` stops collecting
    /// arguments at a new-line token whose column is `<= let_col`. The body is
    /// then parsed by `let_body_after_value` (when no explicit `in`/`;` follows).
    ///
    /// The indent stack and stop-flag are saved and restored so nested
    /// constructs (do-blocks, tactic blocks) keep their own reference columns.
    pub(super) fn parse_let_value_layout(
        &mut self,
        let_col: u32,
    ) -> Result<SurfaceExpr, ParseError> {
        let saved_stop = self.stop_app_at_newline_outer_indent;
        self.push_indent_for(let_col, "let value");
        self.stop_app_at_newline_outer_indent = true;
        let result = self.expr();
        self.stop_app_at_newline_outer_indent = saved_stop;
        self.pop_indent();
        result
    }

    /// 0-based column of the keyword that opened the current `let` binding.
    ///
    /// `let_body` is entered immediately after the `let`/`letI` keyword token is
    /// consumed, so the token at `pos - 1` is that keyword. Falls back to the
    /// current token's column if there is no preceding token (cannot happen for
    /// a well-formed `let`, but keeps the helper total).
    pub(super) fn let_keyword_col(&self) -> u32 {
        self.pos
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or_else(|| self.current().col, |t| t.col)
    }

    /// Parse let body: x : T := v in e
    /// Also supports:
    /// - Chained let bindings without `in`: let x := 1; let y := 2; x + y
    /// - Recursive let: let rec f (n : Nat) : Nat := ...
    /// - Function let: let f x := x; f 0 (desugars to let f := fun x => x)
    /// - Pattern let: let q($a) := e | fallback in body (Qq Phase 4)
    pub(super) fn let_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let let_col = self.let_keyword_col();
        // Check for pattern let: let q($a) := e | fallback in body
        // Part of #23: Qq Phase 4 - let-pattern support
        if self.is_let_pattern_start() {
            return self.let_pattern_body(start_span);
        }

        // Check for tuple destructuring: let (a, b, c) := e or let ⟨a, b, c⟩ := e
        if matches!(self.current_kind(), TokenKind::LParen | TokenKind::LAngle) {
            return self.let_tuple_body(start_span);
        }

        // Anonymous instance let: `letI : T := v in body` — Part of #8, Part of #2550
        // No name, just a type annotation. Desugar to `let _anon : T := v in body`.
        if self.check(&TokenKind::Colon) {
            self.advance(); // consume :
            let ty = self.expr()?;
            self.expect(&TokenKind::ColonEq)?;
            let val = self.parse_let_value_layout(let_col)?;
            let body = self.let_body_after_value()?;
            let binder =
                SurfaceBinder::new("_anon".to_string(), Some(ty), SurfaceBinderInfo::Explicit);
            let span = start_span.merge(body.span());
            return Ok(SurfaceExpr::Let(
                span,
                binder,
                Box::new(val),
                Box::new(body),
            ));
        }

        // Check for `rec` keyword
        let is_rec = self.eat(&TokenKind::Rec);

        let name = match self.current_kind() {
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
                        "expected identifier in let binding, got {:?}",
                        self.current_kind()
                    ),
                })
            }
        };

        // Parse optional function parameters (for `let f x y := ...` syntax)
        // These come before the optional return type
        let params = self.optional_binders()?;

        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.expr()?)
        } else {
            None
        };

        // B101: equation-style `let rec` — arms instead of `:=`:
        //   let rec go : Nat → List Nat
        //     | 0 => []
        //     | k + 1 => (k + 1) :: go k
        //   go n
        // Mirrors the top-level def equation form (`def_match_body`) and
        // lowers to the exact shape `build_let_rec` (where_desugar_ext)
        // produces for `where` equation helpers, so elaboration routes through
        // the identical `normalize_equation_def` lowering as `:= match`.
        // `:=`-form let recs take the untouched path below.
        if is_rec && self.check(&TokenKind::Pipe) {
            return self.let_rec_equation_body(start_span, let_col, name, params, ty);
        }

        // For a *local function* `let f (x : A) : B := body`, the trailing `: B`
        // is the function's RETURN type, not the type of `f` itself (which is
        // `A → B`). Attaching `B` directly to the `f` binder mis-typed `f` as a
        // non-function (`let wrap (v : Int) : Int := …; wrap 5` then failed with
        // "TooManyArguments"). When params are present, keep the return type as
        // an ascription on the lambda body and let the binder type be inferred
        // from the resulting `fun … => (body : B)`. (Track EF)
        let (binder_ty, ret_ty) = if params.is_empty() {
            (ty, None)
        } else {
            (None, ty)
        };

        self.expect(&TokenKind::ColonEq)?;
        let val_start_pos = self.pos;
        let mut val = self.parse_let_value_layout(let_col)?;

        // If we have parameters, wrap the value in a lambda, first ascribing the
        // declared return type (if any) onto the body.
        // let f x y : T := body  =>  let f := fun x y => (body : T)
        if !params.is_empty() {
            if let Some(rt) = ret_ty.clone() {
                let body_span = val.span();
                val = SurfaceExpr::Ascription(body_span, Box::new(val), Box::new(rt));
            }
            let val_span = val.span();
            val = SurfaceExpr::Lambda(val_span, params.clone(), Box::new(val));
        }

        // In Lean 4, consecutive let bindings can be chained without explicit `in`:
        // let x := 1
        // let y := 2  -- implicit body is the next let
        // x + y       -- final body
        //
        // NOTE: Without layout-sensitive parsing, we cannot reliably detect where
        // the value ends and the body begins for cases like:
        //   let y := 2
        //   x + y
        // Lean 4 uses indentation to know that `x + y` is the body, not `2 x + y`.
        // Our parser will consume `2 x + y` as the value since `x` looks like an argument.
        // For full compatibility, users should use explicit `in` or `;` separators.
        let body = match self.let_body_after_value() {
            Ok(body) => body,
            Err(err) => {
                // Fallback: if parsing the value greedily consumed a newline-starting `( ... )`
                // that was intended as the body, retry parsing the value while preventing
                // application from consuming `(` when it begins after a newline.
                if self.stop_app_at_newline_lparen {
                    return Err(err);
                }

                let saved_pos = self.pos;
                self.pos = val_start_pos;
                let old = self.stop_app_at_newline_lparen;
                self.stop_app_at_newline_lparen = true;
                let mut val_retry = self.expr()?;
                self.stop_app_at_newline_lparen = old;

                if !params.is_empty() {
                    if let Some(rt) = ret_ty.clone() {
                        let body_span = val_retry.span();
                        val_retry =
                            SurfaceExpr::Ascription(body_span, Box::new(val_retry), Box::new(rt));
                    }
                    let val_span = val_retry.span();
                    val_retry = SurfaceExpr::Lambda(val_span, params.clone(), Box::new(val_retry));
                }

                val = val_retry;

                match self.let_body_after_value() {
                    Ok(body) => body,
                    Err(_) => {
                        // Restore position for clearer error reporting (best effort)
                        self.pos = saved_pos;
                        return Err(err);
                    }
                }
            }
        };

        let span = start_span.merge(body.span());
        let binder = SurfaceBinder::new(name, binder_ty, SurfaceBinderInfo::Explicit);

        if is_rec {
            Ok(SurfaceExpr::LetRec(
                span,
                binder,
                Box::new(val),
                Box::new(body),
            ))
        } else {
            Ok(SurfaceExpr::Let(
                span,
                binder,
                Box::new(val),
                Box::new(body),
            ))
        }
    }

    /// Parse the equation-style `let rec` value + body (B101):
    /// `let rec go binders? (: T)? | pat => e | … <let-body>`.
    ///
    /// The arm list is parsed under the same let-value layout gate as a `:=`
    /// value (`parse_let_value_layout`): a line that dedents to (or below) the
    /// `let` keyword's column ends the final arm body and begins the let body.
    ///
    /// Lowering mirrors `build_let_rec` (clean-elab `where_desugar_ext`), the
    /// shape contract with `elab_let_rec`: the declared return type rides
    /// INSIDE the value as an ascription (`(fun _x => match _x with …) : T`,
    /// wrapped in `fun params => …` when binders are present) and the binder
    /// carries the full `params → T` Pi, so the recursive lift routes through
    /// the identical `normalize_equation_def` lowering as `:= match`.
    fn let_rec_equation_body(
        &mut self,
        start_span: Span,
        let_col: u32,
        name: String,
        params: Vec<SurfaceBinder>,
        ret_ty: Option<SurfaceExpr>,
    ) -> Result<SurfaceExpr, ParseError> {
        let saved_stop = self.stop_app_at_newline_outer_indent;
        self.push_indent_for(let_col, "let rec equations");
        self.stop_app_at_newline_outer_indent = true;
        let eq_val = self.def_match_body_bounded(start_span, EquationArmBoundary::LetValue);
        self.stop_app_at_newline_outer_indent = saved_stop;
        self.pop_indent();
        let eq_val = eq_val?;

        let ascribed = match &ret_ty {
            Some(rt) => SurfaceExpr::Ascription(start_span, Box::new(eq_val), Box::new(rt.clone())),
            None => eq_val,
        };
        let val = if params.is_empty() {
            ascribed
        } else {
            let val_span = ascribed.span();
            SurfaceExpr::Lambda(val_span, params.clone(), Box::new(ascribed))
        };
        let binder_ty = ret_ty.map(|rt| {
            if params.is_empty() {
                rt
            } else {
                SurfaceExpr::Pi(start_span, params, Box::new(rt))
            }
        });

        let body = self.let_body_after_value()?;
        let span = start_span.merge(body.span());
        let binder = SurfaceBinder::new(name, binder_ty, SurfaceBinderInfo::Explicit);
        Ok(SurfaceExpr::LetRec(
            span,
            binder,
            Box::new(val),
            Box::new(body),
        ))
    }

    /// Parse let with tuple destructuring: `let (a, b, c) := e` or `let ⟨a, b, c⟩ := e`
    ///
    /// Desugars to nested lets with Prod.fst/Prod.snd projections:
    ///   let _tpl := e in let a := Prod.fst _tpl in let b := Prod.snd _tpl in body
    pub(super) fn let_tuple_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let let_col = self.let_keyword_col();
        let (open, close) = if self.eat(&TokenKind::LParen) {
            (TokenKind::LParen, TokenKind::RParen)
        } else {
            self.expect(&TokenKind::LAngle)?;
            (TokenKind::LAngle, TokenKind::RAngle)
        };
        // The `⟨…⟩` form is a general anonymous-constructor destructure (it works
        // on any single-constructor type); the `(…)` form is a tuple (always a
        // `Prod`). This distinction selects the desugaring below.
        let is_angle = open == TokenKind::LAngle;

        // Collect comma-separated names
        let mut names = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::Ident(_) => names.push(self.ident()?),
                TokenKind::Underscore => {
                    self.advance();
                    names.push("_".to_string());
                }
                _ => break,
            }
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&close)?;

        // Optional type annotation after the pattern
        let ty_annot = if self.eat(&TokenKind::Colon) {
            Some(self.expr()?)
        } else {
            None
        };

        self.expect(&TokenKind::ColonEq)?;
        let val_start_pos = self.pos;
        let mut val = self.parse_let_value_layout(let_col)?;

        // Same retry as let_body: if the value greedily consumed a
        // newline-starting `(...)` that was the body, re-parse with the
        // newline-lparen guard enabled. Part of #8, Part of #2550.
        let body = match self.let_body_after_value() {
            Ok(body) => body,
            Err(err) => {
                if self.stop_app_at_newline_lparen {
                    return Err(err);
                }
                let saved_pos = self.pos;
                self.pos = val_start_pos;
                let old = self.stop_app_at_newline_lparen;
                self.stop_app_at_newline_lparen = true;
                let val_retry = self.expr()?;
                self.stop_app_at_newline_lparen = old;
                val = val_retry;
                match self.let_body_after_value() {
                    Ok(body) => body,
                    Err(_) => {
                        self.pos = saved_pos;
                        return Err(err);
                    }
                }
            }
        };

        if names.is_empty() {
            // Degenerate case: let () := e; body
            return Ok(body);
        }

        if names.len() == 1 {
            // Single name: let (a) := e; body -> let a := e; body
            let span = start_span.merge(body.span());
            let binder = SurfaceBinder::new(
                names
                    .into_iter()
                    .next()
                    .expect("invariant: names.len() == 1 checked above"),
                ty_annot,
                SurfaceBinderInfo::Explicit,
            );
            return Ok(SurfaceExpr::Let(
                span,
                binder,
                Box::new(val),
                Box::new(body),
            ));
        }

        if is_angle {
            // Anonymous-constructor let-destructure `let ⟨a, b, c⟩ := e; body`.
            // The `⟨…⟩` form destructures via the scrutinee's OWN constructor —
            // a `Prod`, a `Sigma`/`Subtype`, or a user `structure` — so desugar
            // it to a single-arm `match`. That routes through the
            // anonymous-constructor pattern remap (which resolves the `Prod.mk`
            // placeholder to the scrutinee's real constructor and flattens the
            // spine), handling every single-constructor scrutinee. The `(a, b)`
            // tuple form below keeps the `Prod.fst`/`Prod.snd` projection
            // desugaring — a genuine tuple is always a `Prod`, and projections
            // reduce without a `casesOn`. Before this, the `⟨…⟩` form also used
            // the `Prod` projections and failed ("expected Prod") on any
            // non-`Prod` structure, even though `match … | ⟨a, b, c⟩ =>` worked.
            let scrut = match ty_annot {
                Some(ty) => SurfaceExpr::Ascription(start_span, Box::new(val), Box::new(ty)),
                None => val,
            };
            let pattern = Self::combine_patterns_as_tuple(
                names.into_iter().map(SurfacePattern::Var).collect(),
            );
            let arm = SurfaceMatchArm {
                span: start_span,
                pattern,
                body,
            };
            return Ok(SurfaceExpr::Match(
                start_span,
                None,
                Box::new(scrut),
                vec![arm],
            ));
        }

        // Build nested lets with Prod projections:
        // let _tpl := val in
        //   let name_0 := Prod.fst _tpl in
        //   let name_1 := Prod.fst (Prod.snd _tpl) in
        //   ...
        //   let name_n := Prod.snd (Prod.snd^(n-1) _tpl) in
        //   body
        let tpl_name = "_tpl".to_string();
        let n = names.len();

        // Build the innermost body first, then wrap outward
        let mut result = body;
        for i in (0..n).rev() {
            let proj = if n == 2 {
                // 2-tuple: just fst/snd
                if i == 0 {
                    "Prod.fst"
                } else {
                    "Prod.snd"
                }
            } else if i == n - 1 {
                "Prod.snd"
            } else {
                "Prod.fst"
            };

            // Build the projection target: _tpl, Prod.snd _tpl, Prod.snd (Prod.snd _tpl), ...
            let mut target = SurfaceExpr::Ident(start_span, tpl_name.clone());
            // For element i, apply (n==2: 0 or 1 snd), for n>2: apply i snds
            let snd_count = if n == 2 { 0 } else { i.min(n - 2) };
            for _ in 0..snd_count {
                target = SurfaceExpr::App(
                    start_span,
                    Box::new(SurfaceExpr::Ident(start_span, "Prod.snd".to_string())),
                    vec![SurfaceArg::positional(target)],
                );
            }

            // Apply the final fst or snd
            let proj_expr = SurfaceExpr::App(
                start_span,
                Box::new(SurfaceExpr::Ident(start_span, proj.to_string())),
                vec![SurfaceArg::positional(target)],
            );

            let binder = SurfaceBinder::new(names[i].clone(), None, SurfaceBinderInfo::Explicit);
            result = SurfaceExpr::Let(start_span, binder, Box::new(proj_expr), Box::new(result));
        }

        // Wrap everything in let _tpl := val in ...
        let tpl_binder = SurfaceBinder::new(tpl_name, None, SurfaceBinderInfo::Explicit);
        Ok(SurfaceExpr::Let(
            start_span,
            tpl_binder,
            Box::new(val),
            Box::new(result),
        ))
    }

    /// Check if current position starts a let-pattern (e.g., `q(...)` or `~q(...)`)
    /// Part of #23: Qq Phase 4 - let-pattern support
    pub(super) fn is_let_pattern_start(&self) -> bool {
        match self.current_kind() {
            // q(...) pattern
            TokenKind::Ident(name) if name == "q" => {
                matches!(self.peek_kind(1), Some(TokenKind::LParen))
            }
            // ~q(...) pattern
            TokenKind::Tilde => {
                if let Some(TokenKind::Ident(name)) = self.peek_kind(1) {
                    name == "q" && matches!(self.peek_kind(2), Some(TokenKind::LParen))
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Parse let-pattern body: q($a) := e | fallback in body
    /// Syntax: `let q($pat) := scrutinee | fallback in body`
    /// Part of #23: Qq Phase 4 - let-pattern support for runtime q-patterns
    pub(super) fn let_pattern_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Parse the pattern (q(...) or ~q(...))
        let pattern = self.pattern()?;

        // Expect :=
        self.expect(&TokenKind::ColonEq)?;

        // Parse scrutinee expression
        let scrutinee = self.expr()?;

        // Expect | for fallback
        self.expect(&TokenKind::Pipe)?;

        // Parse fallback expression
        let fallback = self.expr()?;

        // Expect `in` before body
        self.expect(&TokenKind::In)?;

        // Parse body
        let body = self.expr()?;

        let span = start_span.merge(body.span());
        Ok(SurfaceExpr::LetPattern(
            span,
            pattern,
            Box::new(scrutinee),
            Box::new(fallback),
            Box::new(body),
        ))
    }

    /// Parse if body: c then t else e
    /// Also handles:
    /// - `if let pat := e then t else f` (if-let pattern matching)
    /// - `if h : p then t else e` (decidable if with proof witness)
    pub(super) fn if_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Check for `if let` pattern
        if self.eat(&TokenKind::Let) {
            let pat = self.pattern_with_or()?;
            self.expect(&TokenKind::ColonEq)?;
            let scrutinee = self.expr()?;
            self.expect(&TokenKind::Then)?;
            let then_branch = self.expr()?;
            self.expect(&TokenKind::Else)?;
            let else_branch = self.expr()?;
            let span = start_span.merge(else_branch.span());
            return Ok(SurfaceExpr::IfLet(
                span,
                pat,
                Box::new(scrutinee),
                Box::new(then_branch),
                Box::new(else_branch),
            ));
        }

        // Check for `if h : p` decidable if
        // This is `if ident : expr then ... else ...`
        // We need to look ahead: if we have `ident :` (not `:=`), it's decidable
        if let TokenKind::Ident(name) = self.current_kind() {
            if matches!(self.peek_kind(1), Some(TokenKind::Colon)) {
                // Check it's not ColonEq
                let name = name.clone();
                self.advance(); // consume ident
                self.advance(); // consume :
                let prop = self.expr()?;
                self.expect(&TokenKind::Then)?;
                let then_branch = self.expr()?;
                self.expect(&TokenKind::Else)?;
                let else_branch = self.expr()?;
                let span = start_span.merge(else_branch.span());
                return Ok(SurfaceExpr::IfDecidable(
                    span,
                    name,
                    Box::new(prop),
                    Box::new(then_branch),
                    Box::new(else_branch),
                ));
            }
        }

        // Regular if-then-else
        let cond = self.expr()?;
        self.expect(&TokenKind::Then)?;
        let then_branch = self.expr()?;
        self.expect(&TokenKind::Else)?;
        let else_branch = self.expr()?;
        let span = start_span.merge(else_branch.span());
        Ok(SurfaceExpr::If(
            span,
            Box::new(cond),
            Box::new(then_branch),
            Box::new(else_branch),
        ))
    }

    /// Parse `bif c then t else e` — Lean 4's boolean conditional
    /// (`Init/Prelude.lean`: `macro_rules | \`(bif $c then $t else $e) =>
    /// \`(cond $c $t $e)`). Unlike `if`, `bif` needs no `Decidable` instance —
    /// it eliminates a `Bool` directly — so it desugars to an application of the
    /// `cond` combinator (which the elaborator resolves on demand). The leading
    /// `bif` keyword has already been consumed by the caller.
    pub(super) fn bif_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        let cond = self.expr()?;
        self.expect(&TokenKind::Then)?;
        let then_branch = self.expr()?;
        self.expect(&TokenKind::Else)?;
        let else_branch = self.expr()?;
        let span = start_span.merge(else_branch.span());
        Ok(SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(start_span, "cond".to_string())),
            vec![
                SurfaceArg::positional(cond),
                SurfaceArg::positional(then_branch),
                SurfaceArg::positional(else_branch),
            ],
        ))
    }

    /// Parse by body: tactic proof block.
    ///
    /// Parses the tactic sequence following `by` into a `SurfaceExpr::ByTactic`.
    /// Uses indentation-sensitive parsing: the reference column is the column of
    /// the **first tactic** (not the `by` keyword). Tactics at lesser column
    /// terminate the block, matching Lean 4's `tacticSeqIndentGt` + `sepBy1Indent`.
    pub(super) fn by_body(&mut self, start_span: Span) -> SurfaceExpr {
        // Push the first tactic's column as the reference for this block.
        // Same-line tactics (e.g., `by exact h`) have preceded_by_newline=false,
        // so at_dedent won't trigger — the block terminates normally via other checks.
        let first_tac_col = self.current().col;
        self.push_indent_for(first_tac_col, "by tactic block");

        let result = match self.tactic_seq() {
            Ok(tactics) => {
                let end = if let Some(last) = tactics.last() {
                    last.span()
                } else {
                    start_span
                };
                SurfaceExpr::ByTactic(start_span.merge(end), tactics)
            }
            Err(err) => {
                // On parse error, fall back to skipping tokens (graceful degradation).
                // This ensures we don't break parsing of the rest of the file.
                self.defer_parser_recovery("by tactic block", &err);
                let recovered = self.skip_tactic_block(start_span);
                self.flush_pending_parser_recoveries();
                recovered
            }
        };

        self.pop_indent();
        result
    }

    /// Fallback: skip tokens in a tactic block and return a synthetic sorry node.
    /// Used when tactic parsing fails, to allow the rest of the file to parse.
    fn skip_tactic_block(&mut self, start_span: Span) -> SurfaceExpr {
        let mut depth = 0;
        let mut end_span = start_span;

        while !self.at_tactic_end(depth) {
            match self.current_kind() {
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if depth > 0 {
                        depth -= 1;
                    } else {
                        break;
                    }
                }
                TokenKind::Eof => break,
                _ => {}
            }
            end_span = self.current_span();
            self.advance();
        }

        SurfaceExpr::SyntheticSorry(start_span.merge(end_span))
    }

    /// Check if we're at the end of a tactic block.
    ///
    /// When the indent stack is non-empty, column-based dedent is the primary
    /// termination signal (matching Lean 4's `sepBy1Indent` + `checkColGe`).
    /// Bracket closers and EOF remain unconditional terminators.
    /// Top-level keyword checks remain as fallback when the indent stack is empty.
    pub(super) fn at_tactic_end(&self, depth: usize) -> bool {
        if depth > 0 {
            return false;
        }

        // EOF always terminates
        if matches!(self.current_kind(), TokenKind::Eof) {
            return true;
        }

        // Column-based termination: if we're inside an indented block and the
        // current token is on a new line at lesser column, the block has ended.
        if self.at_dedent() {
            return true;
        }

        // Closing brackets always terminate (regardless of indent context)
        if matches!(
            self.current_kind(),
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace | TokenKind::RAngle
        ) {
            return true;
        }

        // Comma terminates (for tactic sequences inside argument lists)
        if matches!(self.current_kind(), TokenKind::Comma) {
            return true;
        }

        // `else`, `then`, and `where` terminate tactic blocks unconditionally.
        // These keywords are never valid tactic starts. `else`/`then` belong to
        // an enclosing expression-level conditional (#2835); `where` begins a
        // declaration's local-definition clause and, in particular, must stop
        // a preceding `decreasing_by` tactic sequence.
        if matches!(
            self.current_kind(),
            TokenKind::Else | TokenKind::Then | TokenKind::Where
        ) {
            return true;
        }

        // Termination hint keywords terminate tactic sequences (#1132).
        // Without this, `decreasing_by simp_arith` followed by `termination_by n`
        // would cause the tactic parser to consume `termination_by` as a named tactic.
        if let TokenKind::Ident(name) = self.current_kind() {
            if name == "termination_by" || name == "termination_by?" || name == "decreasing_by" {
                return true;
            }
        }

        // Tactic sequence separators and boundaries terminate: these tokens
        // are never part of a tactic's arguments.
        // - `;` and `<;>` separate tactics in a sequence
        // - `|` marks alternative boundaries in cases/induction/match/first
        // Note: `·` (Cdot) is NOT included here because it starts a new
        // FocusBlock tactic, not a separator consumed by tactic_seq.
        if matches!(
            self.current_kind(),
            TokenKind::Semicolon | TokenKind::SeqFocusOp | TokenKind::Pipe
        ) {
            return true;
        }

        // A leading `:` at depth 0 terminates the block. This is the trailing
        // type-ascription colon of the `(by tac : T)` inline-proof idiom
        // (`(by exact h : p)`, `(by simp : P)`): after `expr()` parses the term
        // argument of `exact`/`simp`, the `: T` is left for the enclosing paren's
        // ascription parser (`(e : T)`). No tactic *starts* with `:`, and the
        // colon-consuming tactics (`have h : P`, `show P`, `suffices h : P`,
        // `by_cases h : P`) consume their own colon inside their dedicated
        // parser — so a `:` never appears at the *start* of a fresh tactic. Were
        // it not a terminator, `tactic_seq` would call `tactic()` on the bare
        // `:`, fail to parse it as an expression, and degrade the whole `by`
        // block to a synthetic sorry (losing the proof entirely). #(by-ascription)
        if matches!(self.current_kind(), TokenKind::Colon) {
            return true;
        }

        // Treat hash commands (#check, #eval) as terminators only when they are not array literals
        if matches!(self.current_kind(), TokenKind::Hash)
            && !matches!(self.peek_kind(1), Some(TokenKind::LBracket))
        {
            return true;
        }

        // When inside an indented block, column position is the primary boundary.
        // Don't use keyword fallbacks — they cause greedy consumption of outer-block tactics.
        if !self.indent_stack.is_empty() {
            return false;
        }

        // Fallback: keyword-based termination when indent stack is empty
        // (top-level parsing without column context)
        matches!(
            self.current_kind(),
            TokenKind::Def
                | TokenKind::Theorem
                | TokenKind::Lemma
                | TokenKind::Example
                | TokenKind::Axiom
                | TokenKind::Inductive
                | TokenKind::Structure
                | TokenKind::Class
                | TokenKind::Instance
                | TokenKind::Namespace
                | TokenKind::Section
                | TokenKind::End
                | TokenKind::Import
                | TokenKind::Open
                | TokenKind::Variable
                | TokenKind::Universe
                | TokenKind::Mutual
                | TokenKind::At
                | TokenKind::Private
                | TokenKind::Protected
                | TokenKind::Public
                | TokenKind::Module
                | TokenKind::Partial
                | TokenKind::Unsafe
                | TokenKind::Noncomputable
                | TokenKind::Abbrev
                | TokenKind::Syntax
                | TokenKind::Macro
                | TokenKind::Elab
                | TokenKind::Notation
                | TokenKind::Infixl
                | TokenKind::Infixr
                | TokenKind::Prefix
                | TokenKind::Postfix
                | TokenKind::Scoped
                | TokenKind::SetOption
                | TokenKind::With
                | TokenKind::Pipe
        )
    }

    /// Whether the current token could begin another calc step.
    ///
    /// Returns `false` for hard terminators that end a calc block regardless of
    /// indentation — EOF, closing brackets, `,`, separators (`;`/`<;>`/`|`),
    /// `else`/`then`, hash commands, and top-level command keywords — and `true`
    /// otherwise. Unlike [`Self::at_tactic_end`] this deliberately ignores the
    /// dedent/column check: a subsequent calc step (the first `_ …` line) is
    /// allowed to sit to the LEFT of the first step's column, so column position
    /// alone must not terminate the block before the step-column re-base.
    pub(super) fn calc_step_may_continue(&self) -> bool {
        if matches!(self.current_kind(), TokenKind::Eof) {
            return false;
        }
        if matches!(
            self.current_kind(),
            TokenKind::RParen
                | TokenKind::RBracket
                | TokenKind::RBrace
                | TokenKind::RAngle
                | TokenKind::Comma
                | TokenKind::Semicolon
                | TokenKind::SeqFocusOp
                | TokenKind::Pipe
                | TokenKind::Else
                | TokenKind::Then
        ) {
            return false;
        }
        if matches!(self.current_kind(), TokenKind::Hash)
            && !matches!(self.peek_kind(1), Some(TokenKind::LBracket))
        {
            return false;
        }
        // Top-level command keywords always start a new declaration, never a
        // continuation of the calc block.
        !matches!(
            self.current_kind(),
            TokenKind::Def
                | TokenKind::Theorem
                | TokenKind::Lemma
                | TokenKind::Example
                | TokenKind::Axiom
                | TokenKind::Inductive
                | TokenKind::Structure
                | TokenKind::Class
                | TokenKind::Instance
                | TokenKind::Namespace
                | TokenKind::Section
                | TokenKind::End
                | TokenKind::Import
                | TokenKind::Open
                | TokenKind::Variable
                | TokenKind::Universe
                | TokenKind::Mutual
                | TokenKind::Private
                | TokenKind::Protected
                | TokenKind::Public
                | TokenKind::Module
                | TokenKind::Partial
                | TokenKind::Unsafe
                | TokenKind::Noncomputable
                | TokenKind::Abbrev
                | TokenKind::Syntax
                | TokenKind::Macro
                | TokenKind::Elab
                | TokenKind::Notation
                | TokenKind::Infixl
                | TokenKind::Infixr
                | TokenKind::Prefix
                | TokenKind::Postfix
                | TokenKind::Scoped
                | TokenKind::SetOption
                | TokenKind::With
        )
    }

    /// Parse calc proof steps: `_ rel rhs := proof` sequence.
    ///
    /// A calc block is a sequence of steps, each consisting of:
    /// - A relation expression (e.g., `_ = b`, `_ ≤ c`)
    /// - `:=` followed by a proof term, or `by` followed by a tactic sequence
    ///
    /// The first step may omit `_` and just state the full relation.
    /// Subsequent steps use `_` for the LHS (inherited from the previous RHS).
    pub(super) fn calc_steps(&mut self) -> Result<Vec<SurfaceCalcStep>, ParseError> {
        use crate::surface::{SurfaceCalcJustification, SurfaceCalcStep};

        // Lean 4's grammar (`Init/NotationExtra.lean`):
        //   calcSteps := ppLine withPosition(calcFirstStep)
        //                       withPosition((ppLine linebreak calcStep)*)
        // The FIRST step sets its own reference column; the *subsequent* steps
        // form a separate block whose reference column is the column of the
        // first subsequent step (the first `_ …` line). Subsequent steps need
        // only `colGe` that column — they are NOT constrained to align with the
        // first step. So
        //   calc a ≤ b := h1
        //       _ ≤ c := h2
        // is valid even though `_` sits to the left of `a`. We therefore push
        // the first step's column only while parsing the first step, then re-base
        // the indent to the second step's column for the remaining steps.
        let first_step_col = self.current().col;
        self.push_indent_for(first_step_col, "calc block");

        let mut recorded_recovery = false;
        // Tracks whether we have re-based the indent reference from the first
        // step's column to the subsequent-steps column. Two indents are pushed
        // after a successful re-base ("calc block" + "calc steps"); both must be
        // popped on exit.
        let mut rebased = false;
        let mut parse_one = |p: &mut Self| -> Result<SurfaceCalcStep, ParseError> {
            let step_span = p.current_span();

            // Parse the relation expression (e.g., `a = b` or `_ ≤ c`)
            let rel = p.expr()?;

            // The justification: `:= proof` or `:= by tac_seq`
            let proof = if p.eat(&TokenKind::ColonEq) {
                if p.eat(&TokenKind::By) {
                    let tacs = p.indented_tactic_seq()?;
                    SurfaceCalcJustification::Tactic(tacs)
                } else {
                    // Push the proof term's column as indent reference so that
                    // app_expr stops at the next calc step (which starts at the
                    // steps column, strictly less than the proof column).
                    let proof_col = p.current().col;
                    p.push_indent_for(proof_col, "calc proof term");
                    let proof_term = p.expr();
                    if let Err(err) = &proof_term {
                        p.defer_parser_recovery("calc proof term", err);
                        recorded_recovery = true;
                    }
                    p.pop_indent();
                    SurfaceCalcJustification::Term(proof_term?)
                }
            } else {
                // First step without `:=` — it's just the relation, with an implicit rfl
                SurfaceCalcJustification::Term(SurfaceExpr::Ident(step_span, "rfl".to_string()))
            };

            let end = match &proof {
                SurfaceCalcJustification::Term(e) => e.span(),
                SurfaceCalcJustification::Tactic(tacs) => {
                    tacs.last().map_or(step_span, |t| t.span())
                }
            };

            Ok(SurfaceCalcStep {
                span: step_span.merge(end),
                rel,
                proof,
            })
        };

        let result = (|| {
            let mut steps = Vec::new();

            // Parse the first step under the first-step reference column.
            steps.push(parse_one(self)?);
            while self.eat(&TokenKind::Semicolon) {}

            // Re-base the indent reference to the first *subsequent* step's
            // column, so later steps align with it (Lean's separate
            // `withPosition` for the step repetition) rather than with the first
            // step. Done BEFORE the boundary re-check so a step that sits to the
            // left of the first step (the canonical `_` layout) is still
            // recognized as part of the block. We only re-base when the next
            // token could begin another step — a hard terminator (EOF, closing
            // bracket, top-level command keyword, separator) ends the block
            // regardless of column.
            if self.calc_step_may_continue() {
                let steps_col = self.current().col;
                self.push_indent_for(steps_col, "calc steps");
                rebased = true;
            }

            // Parse remaining steps against the re-based reference column.
            while !self.at_tactic_end(0) {
                steps.push(parse_one(self)?);
                while self.eat(&TokenKind::Semicolon) {}
            }

            Ok(steps)
        })();

        if let Err(err) = &result {
            if !recorded_recovery {
                self.defer_parser_recovery("calc block", err);
            }
        }
        if rebased {
            self.pop_indent();
        }
        self.pop_indent();
        result
    }

    /// Parse anonymous constructor: ⟨e1, e2, ...⟩
    pub(super) fn anon_constructor_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        let mut args = Vec::new();

        if !self.check(&TokenKind::RAngle) {
            args.push(self.expr()?);
            while self.eat(&TokenKind::Comma) {
                // Lean's anonymousCtor allows a trailing comma
                // (`allowTrailingSep`): `⟨1, 2,⟩` ≡ `⟨1, 2⟩`.
                if self.check(&TokenKind::RAngle) {
                    break;
                }
                args.push(self.expr()?);
            }
        }

        self.expect(&TokenKind::RAngle)?;
        let end_span = self.current_span();

        // Create application: anonymousCtor args...
        Ok(SurfaceExpr::App(
            start_span.merge(end_span),
            Box::new(SurfaceExpr::Ident(start_span, "anonymousCtor".to_string())),
            args.into_iter().map(SurfaceArg::positional).collect(),
        ))
    }
}
