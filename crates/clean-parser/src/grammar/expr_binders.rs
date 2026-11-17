// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder, identifier, level expression, and attribute parsing.
//! Extracted from expr.rs as part of #307.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

/// Custom-eliminator attributes whose `local` / `scoped` kinds are lifted to
/// [`Attribute::Local`] / [`Attribute::Scoped`]. Without the lift the
/// fallback arm reads the modifier as the attribute NAME and skips the real
/// one as its argument, so `attribute [local induction_eliminator] e` would
/// register nothing; lifted, the elaborator refuses the unmodeled kind by name.
fn is_lifted_eliminator_attr(name: &str) -> bool {
    matches!(name, "induction_eliminator" | "cases_eliminator")
}

impl Parser {
    /// Parse one or more binders
    pub(super) fn binders(&mut self) -> Result<Vec<SurfaceBinder>, ParseError> {
        // Consumed with `take()`: the barrier applies to THIS binder list only.
        // A nested `binders()` (inside a binder's TYPE, e.g. `(f : ∀ a b, P)`)
        // must see `None`, or a multi-line type annotation would be cut short.
        let barrier = self.binder_run_line_barrier.take();
        let result = self.binders_barriered(barrier);
        self.binder_run_line_barrier = None;
        result
    }

    /// `true` when the cursor sits on the first token of a source line whose
    /// column is at or left of `barrier` — i.e. where the NEXT top-level
    /// command starts, so a bare-name binder run must not continue into it.
    ///
    /// See [`Parser::binder_run_line_barrier`] for why this exists.
    fn at_binder_run_line_barrier(&self, barrier: Option<u32>) -> bool {
        let Some(anchor) = barrier else {
            return false;
        };
        let token = self.current();
        token.preceded_by_newline && token.col <= anchor
    }

    fn binders_barriered(
        &mut self,
        barrier: Option<u32>,
    ) -> Result<Vec<SurfaceBinder>, ParseError> {
        let mut binders = Vec::new();

        loop {
            match self.current_kind() {
                TokenKind::LParen => {
                    binders.extend(self.explicit_binders()?);
                }
                TokenKind::LBrace => {
                    binders.extend(self.implicit_binders()?);
                }
                TokenKind::StrictLBrace => {
                    binders.extend(self.strict_implicit_binders()?);
                }
                TokenKind::LBracket => {
                    binders.extend(self.instance_binders()?);
                }
                TokenKind::Ident(_) | TokenKind::Underscore
                    if self.at_binder_run_line_barrier(barrier) =>
                {
                    // A bare-name run may not START on the next command line.
                    break;
                }
                TokenKind::Ident(_) | TokenKind::Underscore => {
                    // A run of consecutive bare binder names shares a single
                    // trailing type annotation, matching Lean: `∀ a b : Nat, …`,
                    // `∃ x y z : T, …` and `fun a b : T => …` bind EVERY name at
                    // that type — not just the last. (The unparenthesized path
                    // previously attached `: T` only to the final name, leaving
                    // earlier binders' types as holes; an unused binder like `b`
                    // in `∃ a b : Nat, a = a` then stayed an unresolved meta and
                    // was rejected, whereas Lean accepts it.) The parenthesized
                    // `(x y z : T)` form already distributes via `explicit_binders`.
                    // Without a trailing `:` each name is an untyped binder, as
                    // before, so `∃ x ∈ S, …` / `∀ a b, …` are unaffected.
                    let mut run: Vec<(Span, SurfaceName)> = Vec::new();
                    loop {
                        if self.at_binder_run_line_barrier(barrier) {
                            break;
                        }
                        match self.current_kind() {
                            TokenKind::Ident(n) => {
                                run.push((self.current_span(), self.name_token(n)?));
                                self.advance();
                            }
                            TokenKind::Underscore => {
                                run.push((self.current_span(), SurfaceName::generated_path("_")));
                                self.advance();
                            }
                            _ => break,
                        }
                    }

                    // Optional shared type annotation applied to every name in the
                    // run. `arrow_expr` supports function types (`a b : Nat → Bool`).
                    let shared_ty = if self.check(&TokenKind::Colon) {
                        self.advance();
                        // The shared binder type must admit the full connective
                        // ladder: `∀ h : p ∧ q, r h` has a top-level `∧` that
                        // `arrow_expr` (which sits BELOW and/or/iff in the
                        // chain) never reaches — four Logic/Basic decls died in
                        // parse recovery on exactly this. `iff_expr` descends
                        // through or→and→…→arrow, so `a b : Nat → Bool` still
                        // parses, and none of those levels consume the comma
                        // that terminates the quantifier binder.
                        //
                        // `with_term_slot` because Lean parses a binder type
                        // with `termParser` (level 0): the annotation is a full
                        // `term` even when the quantifier itself sits in an
                        // arrow codomain, where `iff_expr` would otherwise leave
                        // the `↔` of `a → ∀ h : p ↔ q, r h` to an enclosing
                        // level that does not exist.
                        Some(self.with_term_slot(Self::iff_expr)?)
                    } else {
                        None
                    };

                    for (span, name) in run {
                        binders.push(SurfaceBinder {
                            span,
                            name,
                            ty: shared_ty.clone().map(Box::new),
                            default: None,
                            info: SurfaceBinderInfo::Explicit,
                        });
                    }
                }
                TokenKind::LAngle => {
                    // Anonymous constructor pattern: ⟨a, b, c⟩
                    // Used in `fun ⟨a, b⟩ =>` and `∑ ⟨i, j⟩ : T, ...`
                    // Treat as comma-separated binder names
                    let span = self.current_span();
                    self.advance(); // consume ⟨
                    let mut names = Vec::new();
                    loop {
                        match self.current_kind() {
                            TokenKind::Ident(name) => {
                                names.push((self.current_span(), self.name_token(name)?));
                                self.advance();
                            }
                            TokenKind::Underscore => {
                                names.push((self.current_span(), SurfaceName::generated_path("_")));
                                self.advance();
                            }
                            _ => break,
                        }
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RAngle)?;
                    if names.is_empty() {
                        binders.push(SurfaceBinder {
                            span,
                            name: SurfaceName::generated_path("_"),
                            ty: None,
                            default: None,
                            info: SurfaceBinderInfo::Explicit,
                        });
                    } else {
                        for (s, name) in names {
                            binders.push(SurfaceBinder {
                                span: s,
                                name,
                                ty: None,
                                default: None,
                                info: SurfaceBinderInfo::Explicit,
                            });
                        }
                    }
                }
                _ => break,
            }
        }

        if binders.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected at least one binder".to_string(),
            });
        }

        Ok(binders)
    }

    /// Parse explicit binders: (x y z : T) or (x y z) without type
    /// Also supports underscore binders: (_ : T)
    pub(super) fn explicit_binders(&mut self) -> Result<Vec<SurfaceBinder>, ParseError> {
        self.expect(&TokenKind::LParen)?;

        let mut names = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::Ident(name) => {
                    names.push((self.current_span(), self.name_token(name)?));
                    self.advance();
                }
                TokenKind::Underscore => {
                    names.push((self.current_span(), SurfaceName::generated_path("_")));
                    self.advance();
                }
                _ => break,
            }
        }

        if names.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected identifier in binder".to_string(),
            });
        }

        // Comma-separated names: (a, b, c) — tuple destructuring pattern
        // Treat as separate binders for parse compatibility
        if self.check(&TokenKind::Comma) && !names.is_empty() {
            while self.eat(&TokenKind::Comma) {
                match self.current_kind() {
                    TokenKind::Ident(name) => {
                        names.push((self.current_span(), self.name_token(name)?));
                        self.advance();
                    }
                    TokenKind::Underscore => {
                        names.push((self.current_span(), SurfaceName::generated_path("_")));
                        self.advance();
                    }
                    _ => break,
                }
            }
            self.expect(&TokenKind::RParen)?;
            return Ok(names
                .into_iter()
                .map(|(s, name)| SurfaceBinder {
                    span: s,
                    name,
                    ty: None,
                    default: None,
                    info: SurfaceBinderInfo::Explicit,
                })
                .collect());
        }

        // Bounded binder: (x ∈ S), (x > 0), (x ≥ 0), (x < n), (x ≤ n), and the
        // other relational forms `try_bounded_guard` recognises. Lean desugars
        // `∀ (x ∈ S), p` to `∀ x, x ∈ S → p` (and `∃ (x ∈ S), p` to
        // `∃ x, x ∈ S ∧ p`), so the guard must be PRESERVED, not discarded.
        // We build the desugared guard proposition here and stash it in
        // `pending_binder_guards`; the enclosing quantifier drains it via
        // `quant_binders` and wraps the body. (Previously the guard tokens were
        // skipped and thrown away, silently dropping the hypothesis and turning
        // `∀ (x ∈ S), p` into the strictly stronger `∀ x, p`.)
        let names = if matches!(
            self.current_kind(),
            TokenKind::Elem
                | TokenKind::NotElem
                | TokenKind::Gt
                | TokenKind::Ge
                | TokenKind::Lt
                | TokenKind::Le
                | TokenKind::Eq
                | TokenKind::Ne
                | TokenKind::Subset
                | TokenKind::ProperSubset
        ) {
            // Only a SINGLE name takes a guard; any other count falls through
            // with `names` unchanged.
            match <[(Span, SurfaceName); 1]>::try_from(names) {
                Ok([(s, name)]) => {
                    let binder = SurfaceBinder {
                        span: s,
                        name,
                        ty: None,
                        default: None,
                        info: SurfaceBinderInfo::Explicit,
                    };
                    // `try_bounded_guard` consumes the operator, parses the right
                    // operand, and returns the desugared guard referencing `binder`.
                    if let Some(guard) = self.try_bounded_guard(&binder)? {
                        self.pending_binder_guards.push(guard);
                    }
                    self.expect(&TokenKind::RParen)?;
                    return Ok(vec![binder]);
                }
                Err(names) => names,
            }
        } else {
            names
        };

        // Type annotation is optional: `(x)` is valid
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        // Default value is optional: `(x := 5)` or `(x : Nat := 5)`
        let default = if self.eat(&TokenKind::ColonEq) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        self.expect(&TokenKind::RParen)?;

        Ok(names
            .into_iter()
            .map(|(s, name)| SurfaceBinder {
                span: s,
                name,
                ty: ty.clone(),
                default: default.clone(),
                info: SurfaceBinderInfo::Explicit,
            })
            .collect())
    }

    /// Parse implicit binders: {x y z : T} or strict implicit: {{x y z : T}}
    /// Also supports underscore binders: {_ : T}
    pub(super) fn implicit_binders(&mut self) -> Result<Vec<SurfaceBinder>, ParseError> {
        self.expect(&TokenKind::LBrace)?;

        // Check for strict implicit: {{...}}
        let is_strict = self.eat(&TokenKind::LBrace);

        let mut names = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::Ident(name) => {
                    names.push((self.current_span(), self.name_token(name)?));
                    self.advance();
                }
                TokenKind::Underscore => {
                    names.push((self.current_span(), SurfaceName::generated_path("_")));
                    self.advance();
                }
                _ => break,
            }
        }

        if names.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected identifier in binder".to_string(),
            });
        }

        // Check for type annotation (colon) or just close brace
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None // Implicit binders without explicit type: {α β}
        };
        self.expect(&TokenKind::RBrace)?;

        // For strict implicit, expect closing }}
        if is_strict {
            self.expect(&TokenKind::RBrace)?;
        }

        let binder_info = if is_strict {
            SurfaceBinderInfo::StrictImplicit
        } else {
            SurfaceBinderInfo::Implicit
        };

        Ok(names
            .into_iter()
            .map(|(s, name)| SurfaceBinder {
                span: s,
                name,
                ty: ty.clone(),
                default: None,
                info: binder_info,
            })
            .collect())
    }

    /// Parse a unicode strict-implicit binder group `⦃x y : T⦄` (Lean
    /// `BinderInfo.strictImplicit`; the ASCII `{{x : T}}` form is handled by
    /// [`Self::implicit_binders`]). The type annotation is optional (untyped
    /// `⦃x⦄` is legal and elaborates to a metavariable type).
    pub(super) fn strict_implicit_binders(&mut self) -> Result<Vec<SurfaceBinder>, ParseError> {
        self.expect(&TokenKind::StrictLBrace)?;
        let mut names = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::Ident(name) => {
                    names.push((self.current_span(), self.name_token(name)?));
                    self.advance();
                }
                TokenKind::Underscore => {
                    names.push((self.current_span(), SurfaceName::generated_path("_")));
                    self.advance();
                }
                _ => break,
            }
        }
        if names.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected identifier in strict-implicit binder `⦃…⦄`".to_string(),
            });
        }
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };
        self.expect(&TokenKind::StrictRBrace)?;
        Ok(names
            .into_iter()
            .map(|(s, name)| SurfaceBinder {
                span: s,
                name,
                ty: ty.clone(),
                default: None,
                info: SurfaceBinderInfo::StrictImplicit,
            })
            .collect())
    }

    /// Parse instance binders: `[x : T]` or anonymous `[T]` or `[Ord A]`
    pub(super) fn instance_binders(&mut self) -> Result<Vec<SurfaceBinder>, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        // Token position right after `[`, to re-parse an ANONYMOUS binder's
        // type with the general expression parser (below).
        let type_start = self.pos;

        let mut names = Vec::new();
        while let TokenKind::Ident(name) = self.current_kind() {
            names.push((self.current_span(), self.name_token(name)?));
            self.advance();
        }

        // Instance binders can be anonymous: [Ord A] or [T]
        // If we see a colon, then names are actual binder names
        // Otherwise, the collected names are the type expression
        let (names, ty) = if names.is_empty() {
            // Nothing collected - expression like [_] or [(A)]?
            let ty_expr = self.expr()?;
            self.expect(&TokenKind::RBracket)?;
            return Ok(vec![SurfaceBinder {
                span: Span::dummy(),
                name: SurfaceName::generated_path("_"),
                ty: Some(Box::new(ty_expr)),
                default: None,
                info: SurfaceBinderInfo::Instance,
            }]);
        } else if self.check(&TokenKind::Colon) {
            // Named binder: [x : T]
            self.expect(&TokenKind::Colon)?;
            let ty = self.expr()?;
            (names, ty)
        } else {
            // Anonymous instance: the whole bracket is the type expression
            // (`[Add α]`, `[OfNat R 0]`, `[Std.Refl r]`). Re-parse it from
            // `type_start` with the general expression parser, so it comes
            // out exactly as `(h : T)` and `: T` produce it. Rebuilding it
            // from the collected identifier TOKENS — the pre-2026-09-11
            // path — lost everything but the first component of a dotted
            // head: the lexer hands `Std.Refl` over as `Std` + `.Refl`, and
            // only `app_expr` folds that into the `Proj` chain the elaborator
            // resolves to the constant, so `[Std.Refl r]` reached the
            // elaborator as `Std` applied to `.Refl` and `r`, and `Std` was
            // auto-bound (`Std.Refl.compl`, `Std.Irrefl.compl`,
            // `rel_imp_eq_of_rel_imp_le` in `Mathlib/Order/Basic.lean`).
            self.pos = type_start;
            let ty_expr = self.expr()?;
            self.expect(&TokenKind::RBracket)?;
            return Ok(vec![SurfaceBinder {
                span: names.first().map_or_else(Span::dummy, |(s, _)| *s),
                name: SurfaceName::generated_path("_"),
                ty: Some(Box::new(ty_expr)),
                default: None,
                info: SurfaceBinderInfo::Instance,
            }]);
        };

        self.expect(&TokenKind::RBracket)?;

        Ok(names
            .into_iter()
            .map(|(s, name)| SurfaceBinder {
                span: s,
                name,
                ty: Some(Box::new(ty.clone())),
                default: None,
                info: SurfaceBinderInfo::Instance,
            })
            .collect())
    }

    /// One identifier token read as Lean's `rawIdent`, which does NOT
    /// consult the token table: a Lean keyword spelling is a name here.
    /// Lean reads an `inductive` constructor this way (`Lean.Parser.Command.
    /// ctor`: `declModifiers true >> rawIdent`), so `inductive T | nomatch`
    /// declares `T.nomatch` (measured with Lean 4.8.0: 133 of the 139
    /// identifier-shaped keywords are accepted there; the other six are
    /// declaration modifiers).
    pub(super) fn raw_ident(&mut self) -> Result<SurfaceName, ParseError> {
        if let TokenKind::Ident(name) = self.current_kind() {
            let name = SurfaceName::component(name, self.current().ident_escaped);
            self.advance();
            return Ok(name);
        }
        self.ident()
    }

    /// Parse one identifier token without flattening its lexical component.
    pub(super) fn ident(&mut self) -> Result<SurfaceName, ParseError> {
        if let TokenKind::Ident(name) = self.current_kind() {
            let name = self.name_token(name)?;
            self.advance();
            Ok(name)
        } else {
            Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected identifier, got {:?}", self.current_kind()),
            })
        }
    }

    /// Check whether the token can serve as a name-list component.
    pub(super) fn is_ident_like(&self) -> bool {
        matches!(self.current_kind(), TokenKind::Ident(_))
            || self.current_kind().as_keyword_str().is_some()
    }

    /// A keyword token is accepted only where the caller's grammar allows it.
    pub(super) fn ident_like(&mut self) -> Result<SurfaceName, ParseError> {
        if matches!(self.current_kind(), TokenKind::Ident(_)) {
            return self.ident();
        }
        if let Some(keyword) = self.current_kind().as_keyword_str() {
            let name = SurfaceName::component(keyword, false);
            self.advance();
            return Ok(name);
        }
        Err(ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current_span().start,
            message: format!(
                "expected identifier or keyword, got {:?}",
                self.current_kind()
            ),
        })
    }

    fn qualified_ident_impl(
        &mut self,
        stop_before_universe_params: bool,
    ) -> Result<SurfaceName, ParseError> {
        let mut name = if matches!(self.current_kind(), TokenKind::Ident(_)) {
            self.ident()?
        } else {
            // Share the keyword-head rule with instance-name lookahead.
            if self.keyword_name_head().is_none() {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!("expected identifier, got {:?}", self.current_kind()),
                });
            }
            self.ident_like()?
        };
        while self.check(&TokenKind::Dot) {
            if stop_before_universe_params && matches!(self.peek_kind(1), Some(TokenKind::LBrace)) {
                break;
            }
            self.advance();
            name = name.append(&self.ident_like()?);
        }
        Ok(name)
    }

    /// The keyword spelling of the current token when it may HEAD a dotted name.
    ///
    /// `Some("Prop")` for the `Prop` of `Prop.instCompl`; `None` for a bare
    /// keyword, so `instance Prop : C` still errors rather than declaring an
    /// instance NAMED `Prop`. Adjacency is byte-level (the same contiguity
    /// idiom as the projection postfix): `Prop .foo` is not a name.
    ///
    /// This is the single definition of that rule. `qualified_ident_impl`
    /// consumes such a head, and callers that must decide whether a name is
    /// even present before committing — `instance_decl_with_mods`, whose other
    /// reading of the same tokens is an ANONYMOUS instance — ask here, so the
    /// look-ahead and the parse cannot disagree.
    pub(super) fn keyword_name_head(&self) -> Option<&'static str> {
        let kw = self.current_kind().as_keyword_str()?;
        let head_end = self.current_span().end;
        let dot_adjacent = matches!(self.peek_kind(1), Some(TokenKind::Dot))
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|d| d.span.start == head_end);
        dot_adjacent.then_some(kw)
    }

    /// Parse a structural qualified identifier.
    pub(super) fn qualified_ident(&mut self) -> Result<SurfaceName, ParseError> {
        self.qualified_ident_impl(false)
    }

    /// Stop before the declaration's explicit universe-parameter suffix.
    pub(super) fn decl_name(&mut self) -> Result<SurfaceName, ParseError> {
        // `protected theorem rfl` (inside `namespace FactorsThrough`,
        // `Logic/Function/Basic.lean:816`): Lean compiles a tactic's leading
        // atom as a NON-reserved symbol, so `rfl` stays an identifier and is
        // an ordinary declaration name. Clean lexes it as a keyword token;
        // accept it here, in declaration-name position only (a dotted
        // `rfl.foo` goes through `keyword_name_head` as before).
        if matches!(self.current_kind(), TokenKind::Rfl) && self.keyword_name_head().is_none() {
            self.advance();
            return Ok(SurfaceName::component("rfl", false));
        }
        self.qualified_ident_impl(true)
    }

    /// A module path has the same structural components as a qualified name.
    pub(super) fn module_path(&mut self) -> Result<SurfaceName, ParseError> {
        self.qualified_ident()
    }

    /// Parse exactly one source name. No error-recovery identifier or trailing
    /// expression can be substituted for an unsupported name.
    pub(crate) fn parse_name(input: &str) -> Result<SurfaceName, ParseError> {
        let mut parser = Self::new(input);
        let name = parser.qualified_ident()?;
        if !matches!(parser.current_kind(), TokenKind::Eof) {
            return Err(ParseError::UnexpectedToken {
                line: parser.current_line(),
                col: parser.current_span().start,
                message: format!("trailing input after name: {:?}", parser.current_kind()),
            });
        }
        Ok(name)
    }

    /// Parse a level expression
    /// Handles: numeric literals, identifiers (params), max, imax, +N suffix, and parenthesized levels
    pub(super) fn level_expr(&mut self) -> Result<LevelExpr, ParseError> {
        let base = self.level_atom()?;

        // Check for +N suffix on the result
        if self.eat(&TokenKind::Plus) {
            if let TokenKind::NatLit(n) = self.current_kind() {
                // Universe offsets are small; a value beyond `u64` (or beyond a
                // sane bound) is not a real level offset. `to_u64` keeps every
                // in-range offset exact and declines the pathological case.
                let n = n.to_u64().unwrap_or(u64::MAX);
                // Enforce Lean's `maxUniverseOffset` (default 32): `Sort (u + n)`
                // with `n > 32` is rejected loudly (`checkUniverseOffset`,
                // `src/Lean/Elab/Level.lean`). Rejecting here — before desugaring
                // `+ n` into `n` nested `Succ` nodes — also stops a huge offset
                // (`u + 9999`) from blowing the downstream macro-expansion depth.
                if n > crate::MAX_UNIVERSE_OFFSET {
                    return Err(ParseError::UniverseOffsetTooLarge {
                        offset: n,
                        max: crate::MAX_UNIVERSE_OFFSET,
                    });
                }
                self.advance();
                let mut result = base;
                for _ in 0..n {
                    result = LevelExpr::Succ(Box::new(result));
                }
                return Ok(result);
            }
        }
        Ok(base)
    }

    /// Parse a level atom (the base of a level expression without +N suffix)
    pub(super) fn level_atom(&mut self) -> Result<LevelExpr, ParseError> {
        match self.current_kind() {
            TokenKind::NatLit(n) => {
                let level = n
                    .to_u64()
                    .and_then(|v| u32::try_from(v).ok())
                    .ok_or_else(|| ParseError::NumericOverflow {
                        value: n.to_u64().unwrap_or(u64::MAX),
                        max: u64::from(u32::MAX),
                    })?;
                self.advance();
                Ok(LevelExpr::Lit(level))
            }
            TokenKind::LParen => {
                // Parenthesized level expression: (max u v), (imax 1 u + 1), etc.
                self.advance();
                let inner = self.level_expr()?;
                self.expect(&TokenKind::RParen)?;
                Ok(inner)
            }
            TokenKind::Dollar => {
                // Level antiquotation: $u (for universe polymorphism in q(...))
                self.advance();
                match self.current_kind() {
                    TokenKind::Ident(name) => {
                        let name = self.name_token(name)?;
                        self.advance();
                        Ok(LevelExpr::Antiquot(name))
                    }
                    _ => Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!(
                            "expected identifier after $ in level antiquotation, got {:?}",
                            self.current_kind()
                        ),
                    }),
                }
            }
            TokenKind::Ident(name) => {
                let name = self.name_token(name)?;
                self.advance();
                // Could be "max" or "imax" special forms. Arguments parse as
                // ATOMS (Lean's level grammar): `max u v + 1` is
                // `(max u v) + 1` — the `+ 1` binds to the WHOLE max via the
                // level_expr caller — not `max u (v + 1)` (which is a
                // different, generally-unequal level; the greedy parse made
                // `PUnit.{max u v + 1}` silently ill-leveled). An offset
                // argument still spells with parens: `max (u + 1) v`.
                if name.is_unescaped_component("max") {
                    let l1 = self.level_atom()?;
                    let l2 = self.level_atom()?;
                    Ok(LevelExpr::Max(Box::new(l1), Box::new(l2)))
                } else if name.is_unescaped_component("imax") {
                    let l1 = self.level_atom()?;
                    let l2 = self.level_atom()?;
                    Ok(LevelExpr::IMax(Box::new(l1), Box::new(l2)))
                } else {
                    Ok(LevelExpr::Param(name))
                }
            }
            TokenKind::Underscore => {
                // Treat universe hole "_" as a level parameter placeholder
                self.advance();
                Ok(LevelExpr::Param(SurfaceName::generated_path("_")))
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected level expression, got {:?}", self.current_kind()),
            }),
        }
    }

    /// Parse attributes: `@[attr1, attr2]` or `@[attr1] @[attr2]`
    ///
    /// Supported attributes:
    /// - `instance N` - set instance priority to N
    /// - `default_instance N` - register in the default-instance table
    ///   (priority `N`, default 1000)
    /// - `aesop phase [priority] [builder]` - aesop rule registration
    pub fn attributes(&mut self) -> Result<Vec<Attribute>, ParseError> {
        let mut attrs = Vec::new();

        while self.eat(&TokenKind::At) {
            self.expect(&TokenKind::LBracket)?;

            // Parse attributes inside brackets, separated by commas
            loop {
                let attr = self.single_attribute()?;
                attrs.push(attr);

                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }

            self.expect(&TokenKind::RBracket)?;
        }

        Ok(attrs)
    }

    /// Parse a single attribute name (and optional argument)
    pub(super) fn single_attribute(&mut self) -> Result<Attribute, ParseError> {
        match self.current_kind().clone() {
            TokenKind::Ident(name) => {
                // `local simp`: Lean's `attrInstance := attrKind attr`. The
                // fallback arm below read `local` as the attribute NAME and
                // skipped `simp` as its argument, so `attribute [local simp]
                // foo` registered nothing and the `simp` it was written for
                // made no progress (Mathlib `Logic/Unique.lean:240`,
                // `attribute [local simp] eq_iff_true_of_subsingleton in`).
                // Only the kinds whose scoping the elaborator models are
                // lifted, plus the custom-eliminator attributes it refuses by
                // name (`is_lifted_eliminator_attr`); see [`Attribute::Local`].
                // `class` is retained too, so its global-only handler can
                // refuse this scope rather than silently dropping the whole use.
                if name == "local"
                    && !self.current().ident_escaped
                    && (matches!(self.peek_kind(1), Some(TokenKind::Ident(next)) if next == "simp" || next == "csimp" || next == "class" || is_lifted_eliminator_attr(next))
                        || matches!(
                            self.peek_kind(1),
                            Some(TokenKind::Instance | TokenKind::Class)
                        ))
                {
                    self.advance();
                    let inner = self.single_attribute()?;
                    return Ok(Attribute::Local(Box::new(inner)));
                }
                self.advance();
                match name.as_str() {
                    // === Type class instance attributes ===
                    "defaultInstance" | "default_instance" => {
                        // Optional priority argument (`@[default_instance 200]`,
                        // numeric or `high`/`default`/`mid`/`low`). Previously
                        // skipped, so `@[default_instance 100]` and
                        // `@[default_instance 200]` were indistinguishable (B99).
                        let priority = self.instance_priority_value();
                        self.skip_attribute_args();
                        Ok(Attribute::DefaultInstance { priority })
                    }

                    // === Simplifier/tactic attributes ===
                    "simp" => {
                        // Parse optional priority: @[simp low] or @[simp high]
                        let priority = self.parse_simp_priority();
                        self.skip_attribute_args();
                        Ok(Attribute::Simp { priority })
                    }
                    "congr" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Congr)
                    }
                    "ext" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Ext)
                    }
                    "refl" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Refl)
                    }
                    "symm" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Symm)
                    }
                    // `@[grind]`, `@[grind =]`, `@[grind ←]`, `@[grind cases]`,
                    // … — Lean's `grind` attribute with its optional
                    // `grindMod` (`Lean/Meta/Tactic/Grind/Attr.lean`). The
                    // modifier decides the DIRECTION the tagged lemma is used
                    // in, so it is read rather than skipped; anything outside
                    // the modeled set is carried verbatim.
                    "grind" => {
                        let kind = self.parse_grind_attr_kind();
                        self.skip_attribute_args();
                        Ok(Attribute::Grind(kind))
                    }

                    // === Reducibility attributes ===
                    "reducible" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Reducible)
                    }
                    "semireducible" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Semireducible)
                    }
                    "irreducible" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Irreducible)
                    }

                    // === Compiler/inlining attributes ===
                    "inline" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Inline)
                    }
                    "always_inline" | "alwaysInline" => {
                        self.skip_attribute_args();
                        Ok(Attribute::AlwaysInline)
                    }
                    "noinline" | "noInline" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Noinline)
                    }
                    "macro_inline" | "macroInline" => {
                        self.skip_attribute_args();
                        Ok(Attribute::MacroInline)
                    }
                    "inline_if_reduce" | "inlineIfReduce" => {
                        self.skip_attribute_args();
                        Ok(Attribute::InlineIfReduce)
                    }
                    "specialize" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Specialize)
                    }
                    "nospecialize" | "noSpecialize" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Nospecialize)
                    }

                    // === FFI/extern attributes ===
                    "extern" => {
                        // @[extern "c_name"]
                        let c_name = self.parse_optional_string_arg();
                        self.skip_attribute_args();
                        Ok(Attribute::Extern(c_name.unwrap_or_default()))
                    }
                    "export" => {
                        // @[export name]
                        let export_name = self.parse_optional_ident_arg();
                        self.skip_attribute_args();
                        Ok(Attribute::Export(export_name.unwrap_or_default()))
                    }
                    "implemented_by" => {
                        // @[implemented_by name]
                        let impl_name = self.qualified_ident()?;
                        self.skip_attribute_args();
                        Ok(Attribute::ImplementedBy(impl_name))
                    }

                    // === Documentation/deprecation ===
                    "deprecated" => {
                        // @[deprecated] or @[deprecated "message"]
                        let msg = self.parse_optional_string_arg();
                        self.skip_attribute_args();
                        Ok(Attribute::Deprecated(msg))
                    }

                    // === Other common attributes ===
                    "expose" | "no_expose" | "defeq" | "backward_defeq" => {
                        if !matches!(self.current_kind(), TokenKind::Comma | TokenKind::RBracket) {
                            return Err(ParseError::UnexpectedToken {
                                line: self.current_line(),
                                col: self.current_span().start,
                                message: format!("attribute [{name}] takes no arguments"),
                            });
                        }
                        Ok(Attribute::Unknown(name))
                    }
                    "csimp" => {
                        if !matches!(self.current_kind(), TokenKind::Comma | TokenKind::RBracket) {
                            return Err(ParseError::UnexpectedToken {
                                line: self.current_line(),
                                col: self.current_span().start,
                                message: "Unexpected attribute argument: This attribute takes no arguments".into(),
                            });
                        }
                        Ok(Attribute::Csimp)
                    }
                    "match_pattern" | "matchPattern" => {
                        self.skip_attribute_args();
                        Ok(Attribute::MatchPattern)
                    }
                    "class" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Class)
                    }
                    "coe" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Coe)
                    }
                    "init" => {
                        self.skip_attribute_args();
                        Ok(Attribute::Init)
                    }

                    // === Aesop ===
                    "aesop" => self.parse_aesop_attribute(),

                    // === Fallback ===
                    _ => {
                        // Consume optional attribute parameters
                        // Attributes can have multi-token arguments like:
                        // @[local command_elab Lean.Parser.Command.end]
                        // @[instance 50]
                        self.skip_attribute_args();
                        Ok(Attribute::Unknown(name))
                    }
                }
            }
            TokenKind::Minus => {
                // Attribute removal syntax: [-attr] or [-instance]
                self.advance();
                // Skip the attribute name (can be identifier or keyword like `instance`)
                if matches!(
                    self.current_kind(),
                    TokenKind::Ident(_) | TokenKind::Instance
                ) {
                    self.advance();
                }
                Ok(Attribute::Unknown("-".to_string()))
            }
            // `scoped instance` (`scoped` is a keyword token): the attribute
            // kind of Lean's `attrInstance := attrKind attr`. Until this arm
            // existed `attribute [scoped instance] c` was a PARSE error, the
            // command became a raw declaration, and the declarations after it
            // were still checked and credited against a state without `c`
            // (Lean 4.8.0 activates it on `open N`; round-25 random battery).
            // Lift the scoped attributes whose activation the elaborator models,
            // and retain `class` for its global-only semantic refusal as well.
            TokenKind::Scoped
                if matches!(
                    self.peek_kind(1),
                    Some(TokenKind::Instance | TokenKind::Class)
                ) || matches!(self.peek_kind(1), Some(TokenKind::Ident(name)) if name == "csimp" || name == "class" || is_lifted_eliminator_attr(name)) =>
            {
                self.advance();
                let inner = self.single_attribute()?;
                Ok(Attribute::Scoped(Box::new(inner)))
            }
            // `class` keyword as attribute name: `attribute [class] Unique`
            // is how Mathlib turns a structure into a class after the fact
            // (Logic/Unique.lean:60). The Attribute::Class variant and its
            // ClassAttrMacro already exist — only this parse arm was missing,
            // so the whole file cascaded ("`Unique` is not a class").
            TokenKind::Class => {
                self.advance();
                Ok(Attribute::Class)
            }
            // Handle `instance` keyword used as attribute name
            TokenKind::Instance => {
                self.advance();
                // Check for optional priority number
                if let TokenKind::NatLit(n) = self.current_kind().clone() {
                    let priority =
                        n.to_u64()
                            .and_then(|v| u32::try_from(v).ok())
                            .ok_or_else(|| ParseError::NumericOverflow {
                                value: n.to_u64().unwrap_or(u64::MAX),
                                max: u64::from(u32::MAX),
                            })?;
                    self.advance();
                    Ok(Attribute::InstancePriority(priority))
                } else if let Some(priority) = self.instance_priority_value() {
                    // The named priorities (`instance high`, `low`, `mid`,
                    // `default` — Lean's `prio` syntax). Only the numeral
                    // was read: `attribute [instance high] c` was a parse
                    // error, the command a raw declaration, and the
                    // declarations after it were credited against a state
                    // without `c` (round-27 extended battery).
                    Ok(Attribute::InstancePriority(priority))
                } else {
                    // Just @[instance] without priority means the Lean default
                    // priority (1000; `low` = 100, `high` = 10000). Was 100,
                    // which tied with `(priority := low)` instances (B99).
                    Ok(Attribute::InstancePriority(1000))
                }
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected attribute name, got {:?}", self.current_kind()),
            }),
        }
    }

    /// Read the optional modifier of an `@[grind …]` attribute.
    ///
    /// Lean's `getAttrKindCore` (`Lean/Meta/Tactic/Grind/Attr.lean`) maps a
    /// `grindMod` syntax node to an `AttrKind`; the absent modifier is
    /// `.infer`. Only the leading token(s) are consumed here — the caller's
    /// `skip_attribute_args` eats any remainder (`gen`, `eager`, a `symbol`
    /// priority), so a longer spelling degrades to the modeled prefix or to
    /// [`GrindAttrKind::Unmodeled`] rather than failing the parse.
    fn parse_grind_attr_kind(&mut self) -> GrindAttrKind {
        match self.current_kind().clone() {
            TokenKind::Eq => {
                self.advance();
                // `=_` / `_=_`: an orientation Clean does not model.
                if self.check(&TokenKind::Underscore) {
                    self.advance();
                    return GrindAttrKind::Unmodeled("=_".to_string());
                }
                GrindAttrKind::EqLhs
            }
            TokenKind::Underscore => {
                self.advance();
                GrindAttrKind::Unmodeled("_=_".to_string())
            }
            TokenKind::LeftArrow => {
                self.advance();
                GrindAttrKind::Backward
            }
            TokenKind::Arrow => {
                self.advance();
                GrindAttrKind::Forward
            }
            TokenKind::Ident(word) => match word.as_str() {
                "cases" => {
                    self.advance();
                    GrindAttrKind::Cases
                }
                "ext" => {
                    self.advance();
                    GrindAttrKind::Ext
                }
                "intro" => {
                    self.advance();
                    GrindAttrKind::Intro
                }
                // `@[grind gen]` is Lean's `.ematch (.default true)`
                // (`Attr.lean`, `getAttrKindCore`), an E-match on the whole
                // term with generalization — NOT the bare attribute's
                // `.infer`, which is a different arm of the same function.
                // Clean has no pattern index, so the two collapse to the same
                // thing here: a name the left-to-right rewriter may use.
                "gen" => {
                    self.advance();
                    GrindAttrKind::Infer
                }
                other => {
                    let recorded = other.to_string();
                    self.advance();
                    GrindAttrKind::Unmodeled(recorded)
                }
            },
            // `@[grind]` with no modifier, or a spelling whose first token is
            // not an identifier (`.`, `<=`, …): Lean's `.infer` is the
            // no-modifier case, and an unrecognized leading token is recorded
            // as unmodeled without consuming it — `skip_attribute_args` will.
            TokenKind::RBracket | TokenKind::Comma => GrindAttrKind::Infer,
            _ => GrindAttrKind::Unmodeled(String::new()),
        }
    }

    /// Parse an optional string argument for attributes like `@[extern "name"]`
    fn parse_optional_string_arg(&mut self) -> Option<String> {
        if let TokenKind::StringLit(s) = self.current_kind().clone() {
            self.advance();
            Some(s)
        } else {
            None
        }
    }

    /// Parse an optional identifier argument for attributes like `@[export name]`
    fn parse_optional_ident_arg(&mut self) -> Option<String> {
        if let TokenKind::Ident(s) = self.current_kind().clone() {
            self.advance();
            Some(s)
        } else {
            None
        }
    }

    /// Parse optional simp priority.
    ///
    /// Supports:
    /// - `@[simp]` - No priority (None)
    /// - `@[simp low]` - Low priority
    /// - `@[simp high]` - High priority
    /// - `@[simp normal]` - Normal priority (explicit default)
    fn parse_simp_priority(&mut self) -> Option<SimpPriority> {
        if let TokenKind::Ident(s) = self.current_kind().clone() {
            match s.as_str() {
                "low" => {
                    self.advance();
                    Some(SimpPriority::Low)
                }
                "high" => {
                    self.advance();
                    Some(SimpPriority::High)
                }
                // Normal is the default - not typically written
                "normal" => {
                    self.advance();
                    Some(SimpPriority::Normal)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Skip attribute arguments until we hit `,` or `]`
    /// Handles multi-token attribute arguments like:
    /// - `@[local command_elab Lean.Parser.Command.end]`
    /// - `@[scoped elab_rules : command]`
    pub(super) fn skip_attribute_args(&mut self) {
        // Track nested brackets to handle things like `@[foo (expr)]`
        let mut bracket_depth = 0;
        let mut paren_depth = 0;

        while !matches!(self.current_kind(), TokenKind::Eof) {
            match self.current_kind() {
                // Stop at comma or closing bracket (at depth 0)
                TokenKind::Comma | TokenKind::RBracket
                    if bracket_depth == 0 && paren_depth == 0 =>
                {
                    break
                }
                // Track nested structures
                TokenKind::LBracket => {
                    bracket_depth += 1;
                    self.advance();
                }
                TokenKind::RBracket => {
                    bracket_depth -= 1;
                    self.advance();
                }
                TokenKind::LParen => {
                    paren_depth += 1;
                    self.advance();
                }
                TokenKind::RParen => {
                    paren_depth -= 1;
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }
    }

    /// Parse an @[aesop ...] attribute
    ///
    /// Syntax:
    /// - `@[aesop safe]` - safe rule with default builder (apply)
    /// - `@[aesop unsafe 30%]` - unsafe rule with 30% priority
    /// - `@[aesop safe apply]` - safe apply rule
    /// - `@[aesop unsafe 30% constructors]` - unsafe constructors rule at 30%
    /// - `@[aesop norm simp]` - normalization simp rule
    /// - `@[aesop safe apply, Measurable]` - safe apply rule in Measurable rule set
    /// - `@[aesop safe, Measurable, Continuous]` - safe rule in multiple rule sets
    pub(super) fn parse_aesop_attribute(&mut self) -> Result<Attribute, ParseError> {
        // Parse phase: safe | unsafe | norm
        let phase = self.parse_aesop_phase()?;

        // For unsafe phase, check for optional priority (N%)
        let priority = if phase == AesopPhase::Unsafe {
            self.parse_aesop_priority()
        } else {
            None
        };

        // Parse optional builder: apply | cases | constructors | etc.
        let builder = self.parse_aesop_builder();

        // Parse optional builder arguments (currently only supported for `cases`)
        let builder_args = self.parse_aesop_builder_args(builder);

        // Parse optional index mode: (index := .target | .hyps | .unindexed)
        let index_mode = self.parse_aesop_index_mode();

        // Parse optional rule set names after comma: , Measurable, Continuous
        let rule_sets = self.parse_aesop_rule_sets();

        Ok(Attribute::Aesop(AesopAttr {
            phase,
            builder,
            builder_args,
            priority,
            rule_sets,
            index_mode,
        }))
    }

    /// Parse optional aesop index mode: (index := .target | .hyps | .unindexed)
    pub(super) fn parse_aesop_index_mode(&mut self) -> AesopIndexMode {
        // Check for '(' followed by 'index'
        if !matches!(self.current_kind(), TokenKind::LParen) {
            return AesopIndexMode::default();
        }

        // Look ahead to check if this is (index := ...)
        let saved_pos = self.pos;
        self.advance(); // Skip '('

        if let TokenKind::Ident(name) = self.current_kind() {
            if name == "index" {
                self.advance(); // Skip 'index'

                // Expect ':='
                if matches!(self.current_kind(), TokenKind::ColonEq) {
                    self.advance(); // Skip ':='

                    // Parse the mode: .target, .hyps, .unindexed (or without dot)
                    let mode = self.parse_index_mode_value();

                    // Expect ')'
                    if matches!(self.current_kind(), TokenKind::RParen) {
                        self.advance(); // Skip ')'
                        return mode;
                    }
                }
            }
        }

        // Not an index mode, restore position
        self.pos = saved_pos;
        AesopIndexMode::default()
    }

    /// Parse index mode value: target | .target | hyps | .hyps | unindexed | .unindexed
    pub(super) fn parse_index_mode_value(&mut self) -> AesopIndexMode {
        // Skip optional leading '.'
        if matches!(self.current_kind(), TokenKind::Dot) {
            self.advance();
        }

        if let TokenKind::Ident(name) = self.current_kind() {
            let mode = match name.as_str() {
                "target" => AesopIndexMode::Target,
                "hyps" => AesopIndexMode::Hyps,
                "unindexed" => AesopIndexMode::Unindexed,
                _ => return AesopIndexMode::default(),
            };
            self.advance();
            return mode;
        }

        AesopIndexMode::default()
    }

    /// Parse aesop phase: safe | unsafe | norm
    ///
    /// Note: `unsafe` is a keyword (TokenKind::Unsafe), so we need to handle
    /// both the identifier case and the keyword case.
    pub(super) fn parse_aesop_phase(&mut self) -> Result<AesopPhase, ParseError> {
        match self.current_kind() {
            // `unsafe` is lexed as a keyword, not an identifier
            TokenKind::Unsafe => {
                self.advance();
                Ok(AesopPhase::Unsafe)
            }
            TokenKind::Ident(name) => {
                let phase = match name.as_str() {
                    "safe" => AesopPhase::Safe,
                    "norm" => AesopPhase::Norm,
                    other => {
                        return Err(ParseError::UnexpectedToken {
                            line: self.current_line(),
                            col: self.current_span().start,
                            message: format!(
                                "expected aesop phase (safe/unsafe/norm), got '{other}'"
                            ),
                        })
                    }
                };
                self.advance();
                Ok(phase)
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected aesop phase (safe/unsafe/norm), got {:?}",
                    self.current_kind()
                ),
            }),
        }
    }

    /// Parse optional aesop priority: N%
    /// Returns None if not present
    pub(super) fn parse_aesop_priority(&mut self) -> Option<u32> {
        if let TokenKind::NatLit(n) = self.current_kind().clone() {
            self.advance();
            let prio = n
                .to_u64()
                .and_then(|v| u32::try_from(v).ok())
                .unwrap_or(100)
                .min(100);
            // Check for % symbol (lexed as Percent or as Ident("%"))
            if matches!(self.current_kind(), TokenKind::Percent) {
                self.advance();
                return Some(prio);
            }
            // Check for bare identifier % (might be lexed differently)
            if let TokenKind::Ident(s) = self.current_kind() {
                if s == "%" {
                    self.advance();
                    return Some(prio);
                }
            }
            // No %, but number was consumed - treat as priority without %
            return Some(prio);
        }
        None
    }

    /// Parse optional aesop builder: apply | cases | constructors | destruct | forward | simp | tactic | unfold
    /// Defaults to Apply if not specified
    pub(super) fn parse_aesop_builder(&mut self) -> AesopBuilder {
        // Stop at comma or bracket end
        if matches!(
            self.current_kind(),
            TokenKind::Comma | TokenKind::RBracket | TokenKind::Eof
        ) {
            return AesopBuilder::Apply; // default
        }

        if let TokenKind::Ident(name) = self.current_kind().clone() {
            let builder = match name.as_str() {
                "apply" => AesopBuilder::Apply,
                "cases" => AesopBuilder::Cases,
                "constructors" => AesopBuilder::Constructors,
                "destruct" => AesopBuilder::Destruct,
                "forward" => AesopBuilder::Forward,
                "simp" => AesopBuilder::Simp,
                "tactic" => AesopBuilder::Tactic,
                "unfold" => AesopBuilder::Unfold,
                _ => return AesopBuilder::Apply, // unknown builder, use default
            };
            self.advance();
            builder
        } else {
            AesopBuilder::Apply // default
        }
    }

    /// Parse optional builder arguments (between builder and `,`/`]`).
    ///
    /// Currently only supported for `cases`, e.g. `@[aesop safe cases Or]`.
    pub(super) fn parse_aesop_builder_args(&mut self, builder: AesopBuilder) -> Vec<String> {
        if builder != AesopBuilder::Cases {
            return Vec::new();
        }

        let mut args = Vec::new();

        while !matches!(
            self.current_kind(),
            TokenKind::Comma | TokenKind::RBracket | TokenKind::Eof
        ) {
            if let TokenKind::Ident(name) = self.current_kind().clone() {
                args.push(name);
                self.advance();
            } else {
                break;
            }
        }

        args
    }

    /// Parse optional aesop rule set names: , Measurable, Continuous
    ///
    /// Rule set names are identifiers following a comma within the attribute.
    /// Multiple rule sets can be specified separated by commas.
    /// Returns empty vec if no rule sets specified.
    pub(super) fn parse_aesop_rule_sets(&mut self) -> Vec<String> {
        let mut rule_sets = Vec::new();

        // Look for comma followed by identifier (rule set name)
        while matches!(self.current_kind(), TokenKind::Comma) {
            self.advance(); // consume comma

            // Next token should be an identifier (rule set name)
            if let TokenKind::Ident(name) = self.current_kind().clone() {
                // Skip known builder names - they're not rule sets
                if !matches!(
                    name.as_str(),
                    "apply"
                        | "cases"
                        | "constructors"
                        | "destruct"
                        | "forward"
                        | "simp"
                        | "tactic"
                        | "unfold"
                ) {
                    rule_sets.push(name);
                    self.advance();
                } else {
                    // It's a builder name, not a rule set - stop parsing rule sets
                    break;
                }
            } else {
                // Not an identifier, stop parsing rule sets
                break;
            }
        }

        rule_sets
    }
}
