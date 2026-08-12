// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder, identifier, level expression, and attribute parsing.
//! Extracted from expr.rs as part of #307.

use super::Parser;
use crate::lexer::{LexError, TokenKind};
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse one or more binders
    pub(super) fn binders(&mut self) -> Result<Vec<SurfaceBinder>, ParseError> {
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
                    let mut run: Vec<(Span, String)> = Vec::new();
                    loop {
                        match self.current_kind() {
                            TokenKind::Ident(n) => {
                                run.push((self.current_span(), n.clone()));
                                self.advance();
                            }
                            TokenKind::Underscore => {
                                run.push((self.current_span(), "_".to_string()));
                                self.advance();
                            }
                            _ => break,
                        }
                    }

                    // Optional shared type annotation applied to every name in the
                    // run. `arrow_expr` supports function types (`a b : Nat → Bool`).
                    let shared_ty = if self.check(&TokenKind::Colon) {
                        self.advance();
                        Some(self.arrow_expr()?)
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
                                names.push((self.current_span(), name.clone()));
                                self.advance();
                            }
                            TokenKind::Underscore => {
                                names.push((self.current_span(), "_".to_string()));
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
                            name: "_".to_string(),
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
                    names.push((self.current_span(), name.clone()));
                    self.advance();
                }
                TokenKind::Underscore => {
                    names.push((self.current_span(), "_".to_string()));
                    self.advance();
                }
                TokenKind::Error(LexError::UnexpectedChar(_)) => {
                    // Error recovery: treat invalid characters as placeholder binder names
                    names.push((self.current_span(), "_invalid_".to_string()));
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
                        names.push((self.current_span(), name.clone()));
                        self.advance();
                    }
                    TokenKind::Underscore => {
                        names.push((self.current_span(), "_".to_string()));
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
        if names.len() == 1
            && matches!(
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
            )
        {
            let (s, name) = names
                .into_iter()
                .next()
                .expect("invariant: names.len() == 1 checked above");
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
                    names.push((self.current_span(), name.clone()));
                    self.advance();
                }
                TokenKind::Underscore => {
                    names.push((self.current_span(), "_".to_string()));
                    self.advance();
                }
                TokenKind::Error(LexError::UnexpectedChar(_)) => {
                    names.push((self.current_span(), "_invalid_".to_string()));
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
                    names.push((self.current_span(), name.clone()));
                    self.advance();
                }
                TokenKind::Underscore => {
                    names.push((self.current_span(), "_".to_string()));
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

        let mut names = Vec::new();
        while let TokenKind::Ident(name) = self.current_kind() {
            names.push((self.current_span(), name.clone()));
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
                name: "_".to_string(),
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
            // Anonymous instance: names are actually the type expression
            // e.g., [Add α] where "Add" and "α" were collected as names
            // Build application: Add α β ...
            let mut result = SurfaceExpr::Ident(names[0].0, names[0].1.clone());
            for (span, name) in names.iter().skip(1) {
                let arg = SurfaceExpr::Ident(*span, name.clone());
                let app_span = result.span().merge(arg.span());
                result = SurfaceExpr::App(
                    app_span,
                    Box::new(result),
                    vec![SurfaceArg::positional(arg)],
                );
            }

            // Parse remaining arguments until closing bracket (e.g., `[OfNat R 0]`)
            while !self.check(&TokenKind::RBracket) {
                let arg = self.atom_expr()?;
                let app_span = result.span().merge(arg.span());
                result = SurfaceExpr::App(
                    app_span,
                    Box::new(result),
                    vec![SurfaceArg::positional(arg)],
                );
            }

            self.expect(&TokenKind::RBracket)?;
            return Ok(vec![SurfaceBinder {
                span: names.first().map_or_else(Span::dummy, |(s, _)| *s),
                name: "_".to_string(),
                ty: Some(Box::new(result)),
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

    /// Parse an identifier
    pub(super) fn ident(&mut self) -> Result<String, ParseError> {
        match self.current_kind() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.advance();
                Ok(name)
            }
            TokenKind::Error(LexError::UnexpectedChar(_)) => {
                // Allow invalid characters to be treated as placeholder identifiers
                // for error recovery in malformed test files
                self.advance();
                Ok("_invalid_".to_string())
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected identifier, got {:?}", self.current_kind()),
            }),
        }
    }

    /// Check if current token can be treated as an identifier in name lists.
    pub(super) fn is_ident_like(&self) -> bool {
        match self.current_kind() {
            TokenKind::Ident(_) => true,
            TokenKind::Error(LexError::UnexpectedChar(_)) => true,
            other => other.as_keyword_str().is_some(),
        }
    }

    /// Parse an identifier or keyword token in name lists.
    pub(super) fn ident_like(&mut self) -> Result<String, ParseError> {
        match self.current_kind() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.advance();
                Ok(name)
            }
            TokenKind::Error(LexError::UnexpectedChar(_)) => {
                self.advance();
                Ok("_invalid_".to_string())
            }
            other => {
                if let Some(kw_str) = other.as_keyword_str() {
                    let name = kw_str.to_string();
                    self.advance();
                    Ok(name)
                } else {
                    Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!(
                            "expected identifier or keyword, got {:?}",
                            self.current_kind()
                        ),
                    })
                }
            }
        }
    }

    fn qualified_ident_impl(
        &mut self,
        stop_before_universe_params: bool,
    ) -> Result<String, ParseError> {
        match self.current_kind() {
            TokenKind::Ident(name) => {
                let mut full_name = name.clone();
                self.advance();
                while self.check(&TokenKind::Dot) {
                    if stop_before_universe_params
                        && matches!(self.peek_kind(1), Some(TokenKind::LBrace))
                    {
                        break;
                    }
                    self.advance();
                    match self.current_kind() {
                        TokenKind::Ident(part) => {
                            full_name.push('.');
                            full_name.push_str(part);
                            self.advance();
                        }
                        other => {
                            if let Some(kw_str) = other.as_keyword_str() {
                                full_name.push('.');
                                full_name.push_str(kw_str);
                                self.advance();
                            } else {
                                return Err(ParseError::UnexpectedToken {
                                    line: self.current_line(),
                                    col: self.current_span().start,
                                    message: format!(
                                        "expected identifier after '.', got {other:?}"
                                    ),
                                });
                            }
                        }
                    }
                }
                Ok(full_name)
            }
            TokenKind::Error(LexError::UnexpectedChar(_)) => {
                // Allow invalid characters to be treated as placeholder identifiers
                // for error recovery in malformed test files
                self.advance();
                Ok("_invalid_".to_string())
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected identifier, got {:?}", self.current_kind()),
            }),
        }
    }

    /// Parse a dotted identifier like `Foo.bar.baz`
    pub(super) fn qualified_ident(&mut self) -> Result<String, ParseError> {
        self.qualified_ident_impl(false)
    }

    /// Parse a declaration name, stopping before an explicit `.{u v}` universe suffix.
    pub(super) fn decl_name(&mut self) -> Result<String, ParseError> {
        self.qualified_ident_impl(true)
    }

    /// Parse a dotted module path into segments
    pub(super) fn module_path(&mut self) -> Result<Vec<String>, ParseError> {
        let mut path = Vec::new();
        let name = self.qualified_ident()?;
        path.extend(name.split('.').map(ToString::to_string));
        Ok(path)
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
                        let name = name.clone();
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
                let name = name.clone();
                self.advance();
                // Could be "max" or "imax" special forms. Arguments parse as
                // ATOMS (Lean's level grammar): `max u v + 1` is
                // `(max u v) + 1` — the `+ 1` binds to the WHOLE max via the
                // level_expr caller — not `max u (v + 1)` (which is a
                // different, generally-unequal level; the greedy parse made
                // `PUnit.{max u v + 1}` silently ill-leveled). An offset
                // argument still spells with parens: `max (u + 1) v`.
                if name == "max" {
                    let l1 = self.level_atom()?;
                    let l2 = self.level_atom()?;
                    Ok(LevelExpr::Max(Box::new(l1), Box::new(l2)))
                } else if name == "imax" {
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
                Ok(LevelExpr::Param("_".to_string()))
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
                    "implemented_by" | "implementedBy" => {
                        // @[implemented_by name]
                        let impl_name = self.parse_optional_ident_arg();
                        self.skip_attribute_args();
                        Ok(Attribute::ImplementedBy(impl_name.unwrap_or_default()))
                    }

                    // === Documentation/deprecation ===
                    "deprecated" => {
                        // @[deprecated] or @[deprecated "message"]
                        let msg = self.parse_optional_string_arg();
                        self.skip_attribute_args();
                        Ok(Attribute::Deprecated(msg))
                    }

                    // === Other common attributes ===
                    "csimp" => {
                        self.skip_attribute_args();
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
