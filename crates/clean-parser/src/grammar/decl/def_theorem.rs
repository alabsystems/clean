// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for def, theorem, axiom, and opaque declarations,
//! including termination hints and def-match-body desugaring.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::DeclModifiers;
use crate::surface::*;
use crate::ParseError;

/// How the equation-arm list of a def-match body is bounded (B101).
///
/// - `Declaration`: top-level `def`/`theorem`/`where` context — after each arm
///   body the parser must sit on a declaration-level boundary token
///   (`|`, `where`, `end`, EOF, or a termination hint).
/// - `LetValue`: term-level equation-style `let rec` context — the enclosing
///   let-value layout gate (dedent to the `let` keyword's column) terminates
///   the final arm body, so the following token starts the let's body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::grammar) enum EquationArmBoundary {
    Declaration,
    LetValue,
}

impl Parser {
    /// Parse a def declaration with explicit modifiers.
    pub(in crate::grammar) fn def_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name_start = self.pos;
        let name = self.decl_name()?;
        self.observe_declaration_name(start_span, name_start, &name);

        // Optional universe params
        let universe_params = self.universe_params()?;

        // Optional binders
        let binders = self.optional_binders()?;

        // Optional type annotation
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        // Definition value can be provided with:
        // - := expr
        // - | pattern => expr (pattern matching)
        // - where | pattern => expr (where clause syntax)
        let val = if self.eat(&TokenKind::ColonEq) {
            self.expr()?
        } else if self.check(&TokenKind::Pipe) {
            // Pattern matching definition
            self.def_match_body(start_span)?
        } else if self.eat(&TokenKind::Where) {
            if self.check(&TokenKind::Pipe) {
                // Where clause: def foo : Nat → Nat where | 0 => 1 | n => n
                self.def_match_body(start_span)?
            } else if self.is_field_assign_start() {
                // Structure-instance sugar: `def x : S where\n  f := v` is a
                // struct literal `{ f := v }` elaborated at the annotated type
                // (Lean `Command.declValStruct`). Same field-assign grammar as
                // an instance `where` body. (B90)
                let assigns = self.parse_where_field_assigns()?;
                SurfaceExpr::StructLit {
                    span: start_span,
                    struct_type: None,
                    base: None,
                    fields: assigns,
                }
            } else {
                // Where clause: def foo : Nat → Nat where | 0 => 1 | n => n
                self.def_match_body(start_span)?
            }
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected := or |, got {:?}", self.current_kind()),
            });
        };

        // Parse optional termination_by and decreasing_by clauses
        let termination = self.parse_termination_hints();

        // Parse optional where clause with local definitions
        let where_decls = self.parse_where_local_defs();

        Ok(SurfaceDecl::Def {
            span: start_span,
            name,
            universe_params,
            binders,
            ty,
            val: Box::new(val),
            attrs,
            termination,
            modifiers,
            where_decls,
        })
    }

    /// Parse a definition body using pattern matching syntax.
    ///
    /// Lean 4: `def f | pat1 => body1 | pat2 => body2` is sugar for
    /// `def f := fun _x => match _x with | pat1 => body1 | pat2 => body2`.
    /// Multi-argument: `def f | p1, p2 => body` uses tuple scrutinees.
    ///
    /// Reference: ~/lean4-ref/src/Lean/Elab/MutualDef.lean (elabFunValues)
    pub(in crate::grammar) fn def_match_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        self.def_match_body_bounded(start_span, EquationArmBoundary::Declaration)
    }

    /// [`Self::def_match_body`] with an explicit arm-list boundary mode.
    ///
    /// `Declaration` is the top-level `def`/`theorem`/`where` behavior
    /// (each arm body must end at a declaration-level boundary token).
    /// `LetValue` is the term-level equation-style `let rec` behavior (B101):
    /// the surrounding let-value layout gate terminates the final arm body at
    /// a dedent, so the token after an arm is the let's continuation body
    /// rather than a declaration boundary.
    pub(in crate::grammar) fn def_match_body_bounded(
        &mut self,
        start_span: Span,
        boundary: EquationArmBoundary,
    ) -> Result<SurfaceExpr, ParseError> {
        if !self.check(&TokenKind::Pipe) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "expected definition equation arm beginning with `|`, got {:?}",
                    self.current_kind()
                ),
            });
        }

        let mut arms = Vec::new();
        let mut arity: Option<usize> = None;
        // The positions of the FIRST equation, kept apart for the one-equation
        // lowering below (the tuple fold loses where the positions end).
        let mut first_positions: Option<Vec<SurfacePattern>> = None;

        let arm_col = self.current().col;
        while self.check(&TokenKind::Pipe)
            && !(boundary == EquationArmBoundary::LetValue
                && self.current().preceded_by_newline
                && self.current().col < arm_col)
        {
            let pipe_col = self.current().col;
            self.advance();
            // Parse comma-separated patterns for this arm
            let mut patterns = vec![self.def_match_pattern()?];
            while self.eat(&TokenKind::Comma) {
                patterns.push(self.def_match_pattern()?);
            }
            if arms.is_empty() {
                first_positions = Some(patterns.clone());
            }

            // Enforce consistent arity across arms
            match arity {
                None => arity = Some(patterns.len()),
                Some(n) if n != patterns.len() => {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current().col as usize,
                        message: format!(
                            "definition equation arity mismatch: expected {n} pattern(s), found {}",
                            patterns.len()
                        ),
                    });
                }
                _ => {}
            }

            self.expect(&TokenKind::FatArrow)?;
            if self.current().preceded_by_newline && self.current().col < pipe_col {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current().col as usize,
                    message: "expected alternative right-hand-side to start in a column \
                              greater than or equal to the corresponding '|'"
                        .to_string(),
                });
            }
            let body = self.def_match_arm_body(boundary)?;
            // Combine multiple patterns into a tuple pattern (a last position
            // that is itself a tuple is kept apart from the spine; see
            // `combine_patterns_as_tuple`).
            let pattern = Self::combine_patterns_as_tuple(patterns);
            arms.push(SurfaceMatchArm {
                span: pattern.span(),
                pattern,
                body,
            });
        }

        debug_assert!(!arms.is_empty(), "leading equation pipe creates an arm");

        // ONE equation over n ≥ 2 positions is Lean's `expandMatchAltsIntoMatch`
        // (`Lean/Elab/Binders.lean`): `fun x₁ … xₙ => match x₁, …, xₙ with |
        // p₁, …, pₙ => body`, the arity taken from the SYNTAX
        // (`getMatchAltsNumPatterns`, `Lean/Elab/BindersUtil.lean:44`). Lower it
        // without the tuple encoding below, which matches the positions as ONE
        // `Prod` value and then has to re-derive the arity from the `Prod.mk`
        // spine:
        //
        // - every position a variable or `_` (`| f, g => body`) matches
        //   nothing, and `match x₁, x₂ with | f, g => body` is `@fun f g =>
        //   body` up to definitional equality, so it lowers to exactly that.
        //   The tuple's motive could not see a codomain that depends on the
        //   positions: `def natDecEq2 : (a b : Nat) → Decidable (a = b) | a, b
        //   => …` was refused by the kernel (`fun (x : Prod Nat Nat) =>
        //   Decidable (fvar#2 = fvar#3)`), and with it every `DecidableEq`
        //   instance written by equations (`decidableEqPFun`, Mathlib
        //   `Logic/Function/Basic.lean:165`).
        // - a LAST position that is itself an anonymous constructor or tuple
        //   lowers to the interleaved fun/match nest of a destructuring `fun`:
        //   one `fun` per position, each refutable one destructured by its own
        //   single-arm `match` before the next is bound, so a codomain that
        //   depends on the positions is rewritten position by position. The
        //   spine re-derivation counted that position's own `Prod.mk` as more
        //   positions: `Unique.subsingleton_unique'` (`∀ h₁ h₂ : Unique α, h₁
        //   = h₂ | ⟨⟨x⟩, h⟩, ⟨⟨y⟩, _⟩ => …`, Mathlib `Logic/Unique.lean`) read
        //   three positions, found two binders, and matched the whole tuple
        //   against the first discriminant ("nested constructor Prod.mk does
        //   not belong to field type Inhabited").
        //
        // Any other single equation keeps the tuple encoding, whose arity it
        // counts correctly and which the recursion lowerings recognize (see
        // `single_equation_lambda`). Arity 1 keeps the match: a single
        // discriminant's motive is generalized over the expected type already.
        // Several equations keep the tuple encoding (a real multi-column
        // match); a last position that is an anonymous constructor there is
        // still over-counted.
        if let ([arm], Some(positions)) = (arms.as_slice(), first_positions.as_deref()) {
            if positions.len() >= 2 {
                if let Some(value) = Self::single_equation_lambda(start_span, positions, &arm.body)
                {
                    return Ok(value);
                }
            }
        }

        // Build anonymous scrutinee variable(s) and the match expression.
        // For arity 1: fun _x => match _x with | arms...
        // For arity N: fun _x => match _x with | (p1, p2) => body | ...
        let scrutinee = SurfaceExpr::Ident(start_span, SurfaceName::pattern_lambda_binder());
        let binder = SurfaceBinder::new_typed(
            SurfaceName::pattern_lambda_binder(),
            None,
            SurfaceBinderInfo::Explicit,
        );
        let match_expr = SurfaceExpr::Match(start_span, None, Box::new(scrutinee), arms);
        Ok(SurfaceExpr::PatternMatchLambda(
            start_span,
            vec![binder],
            Box::new(match_expr),
        ))
    }

    /// Parse a single pattern in a def-match arm.
    /// Uses the full pattern parser with or-pattern and cons support.
    fn def_match_pattern(&mut self) -> Result<SurfacePattern, ParseError> {
        self.pattern_with_or()
    }

    /// The value of a definition given by ONE equation over several
    /// `positions` (see `def_match_body_bounded`), or `None` to keep the
    /// tuple encoding.
    ///
    /// Every lambda is `@fun`, as Lean's expansion writes it
    /// (`expandMatchAltsIntoMatchAux` with `useExplicit`): a position binds
    /// the next binder of the type even when that binder is implicit (`def g
    /// : {n : Nat} → Fin (n+1) → Nat | _, x => …`), with no implicit lambda
    /// inserted in front of it.
    ///
    /// - every position a variable or `_` → `@fun p₁ … pₙ => body`;
    /// - the LAST position an anonymous constructor or tuple (the case the
    ///   tuple encoding cannot count) → the interleaved fun/match nest of a
    ///   destructuring `fun`: one `@fun` per position, each refutable one
    ///   destructured by its own single-arm `match` before the next is bound;
    /// - otherwise `None`: the tuple encoding counts such an equation
    ///   correctly, and it is the shape the recursion lowerings
    ///   (`normalize_equation_def`) recognize.
    ///
    /// A DOTTED name (`Nat.zero`, `Option.none`) is a constructor reference —
    /// a pattern variable is never qualified — so it is refutable, never a
    /// binder. An undotted name is a binder, as in a destructuring `fun`. Lean
    /// would resolve one that names a constructor in scope (`| none, x =>`)
    /// as that constructor; as the only equation that is non-exhaustive unless
    /// the constructor is its type's sole, field-less one, so Clean binding a
    /// variable there instead is the residual difference (the parser cannot
    /// resolve names).
    fn single_equation_lambda(
        start_span: Span,
        positions: &[SurfacePattern],
        body: &SurfaceExpr,
    ) -> Option<SurfaceExpr> {
        let is_binder = |p: &SurfacePattern| match p {
            SurfacePattern::Var(name) => {
                name.component_text().is_some() && !name.is_relative_constructor()
            }
            SurfacePattern::Wildcard => true,
            _ => false,
        };
        let explicit_fun = |binders: Vec<SurfaceBinder>, inner: SurfaceExpr| {
            SurfaceExpr::Explicit(
                start_span,
                Box::new(SurfaceExpr::Lambda(start_span, binders, Box::new(inner))),
            )
        };
        let mut fresh_idx = 0_usize;
        let mut layers = Vec::with_capacity(positions.len());
        for p in positions {
            if is_binder(p) {
                layers.push(Self::pattern_binder_layer(p.clone(), &mut fresh_idx).0);
                continue;
            }
            let name = SurfaceName::unspellable("_dx", fresh_idx as u64);
            fresh_idx += 1;
            layers.push(SurfaceBinder::new_typed(
                name,
                None,
                SurfaceBinderInfo::Explicit,
            ));
        }
        if positions.iter().all(is_binder) {
            return Some(explicit_fun(layers, body.clone()));
        }
        let prod_mk = SurfaceName::generated_path("Prod.mk");
        if !matches!(positions.last(), Some(SurfacePattern::Ctor(name, _)) if *name == prod_mk) {
            return None;
        }
        let mut result = body.clone();
        for (binder, position) in layers.into_iter().zip(positions).rev() {
            let inner = if is_binder(position) {
                result
            } else {
                let span = position.span();
                let arm = SurfaceMatchArm {
                    span,
                    pattern: position.clone(),
                    body: result,
                };
                let scrutinee = SurfaceExpr::Ident(span, binder.name.clone());
                SurfaceExpr::Match(span, None, Box::new(scrutinee), vec![arm])
            };
            result = explicit_fun(vec![binder], inner);
        }
        Some(result)
    }

    /// Parse the body expression of a def-match arm.
    /// Stops at `|`, EOF, declaration starts, and termination hints.
    fn def_match_arm_body(
        &mut self,
        boundary: EquationArmBoundary,
    ) -> Result<SurfaceExpr, ParseError> {
        // Parse a full operator-precedence expression. The `|` arm delimiter is
        // lexed as `TokenKind::Pipe`, which is NOT an operator in the precedence
        // chain (logical-or is `TokenKind::Or` = `∨`/`||`) and cannot start an
        // atom, so `expr()` halts cleanly at the next `| pat =>` arm — while
        // still parsing binary operators and applications in the body
        // (e.g. `| n => n + n`, which the atom-only parser could not handle).
        // Declaration keywords (`def`/`theorem`/…) and termination hints
        // likewise cannot continue or start an expression, so they bound it too.
        // The body after `=>` is mandatory, so a leading `open` here cannot be
        // the `open` COMMAND that ends the declaration: it is Lean's term
        // `open Foo in t` (`Lean.Parser.Term.open`), which `expr()` parses and
        // which refuses an `open` with no `in` (G08: trust-ir's `| op => open
        // Classical in if … then … else …`).
        if self.at_def_match_arm_boundary() && !matches!(self.current_kind(), TokenKind::Open) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "expected definition equation body after `=>`".to_string(),
            });
        }

        let body = self.expr()?;
        // In `LetValue` mode the let-value indent gate has already bounded the
        // arm body: a dedented continuation (the let's own body, e.g. `go n`)
        // legitimately follows the final arm, so any token may appear here.
        // In a `where` block, the next helper's header (a newline-leading
        // ident the where-aware expression parser deliberately stopped at)
        // also legally bounds the final arm body.
        // A line-start `local` or `meta` also bounds it: both are tokens in
        // pinned Lean, so `expr()` halts there and the next command starts
        // (`starts_local_command_at`, `starts_meta_command_at`; Mathlib's
        // `Tactic/Module.lean` `add` and `NormNum/Result.lean` `IsRat.den_nz`
        // are followed by a `meta` line).
        if boundary == EquationArmBoundary::Declaration
            && !(self.at_def_match_arm_boundary()
                || self.at_next_where_def_start()
                || self.starts_local_command_at(0)
                || self.starts_meta_command_at(0))
        {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "unexpected token in definition equation body: {:?}",
                    self.current_kind()
                ),
            });
        }
        Ok(body)
    }

    fn at_def_match_arm_boundary(&self) -> bool {
        // `@foo` is an explicit application atom, not an attribute/declaration
        // start. `TokenKind::At` is also used by the top-level `@[attr]`
        // syntax, so the generic declaration-boundary predicate cannot
        // disambiguate the two without this one-token lookahead. In particular,
        // an equation body may legitimately begin with `@Bool.rec ...`.
        if matches!(self.current_kind(), TokenKind::At)
            && matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
        {
            return false;
        }
        matches!(
            self.current_kind(),
            TokenKind::Pipe | TokenKind::Where | TokenKind::End | TokenKind::Eof
        ) || self.at_termination_hint_end(0)
    }

    /// Inside a `where` block, the last arm body of an equation-form helper is
    /// legally bounded by the NEXT helper's header (a newline-leading ident the
    /// where-aware expression parser deliberately stopped at). Byte-identical
    /// to the stop condition in `expr_app.rs`, so the boundary set only gains
    /// positions where `expr()` already halted.
    pub(super) fn at_next_where_def_start(&self) -> bool {
        self.in_where_block
            && matches!(self.current_kind(), TokenKind::Ident(_))
            && self
                .tokens
                .get(self.pos)
                .is_some_and(|t| t.preceded_by_newline)
            && self.peek_is_where_def_start(0)
    }

    pub(in crate::grammar) fn theorem_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name_start = self.pos;
        let name = self.decl_name()?;
        self.observe_declaration_name(start_span, name_start, &name);
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        self.expect(&TokenKind::Colon)?;
        let ty = self.expr()?;

        // Proof can be provided with:
        // - := expr
        // - | pattern => expr (pattern matching without :=)
        // - where <field assigns> / where | pattern => expr
        let proof = if self.eat(&TokenKind::ColonEq) {
            self.expr()?
        } else if self.check(&TokenKind::Pipe) {
            // Pattern matching theorem: theorem foo : T | p1 => e1 | p2 => e2
            self.def_match_body(start_span)?
        } else if self.eat(&TokenKind::Where) {
            // `theorem`/`lemma` accepts the same three `where` bodies `def`
            // does (`:64-83` in this file) — Lean's `Command.declValStruct` and
            // `Command.whereStructInst` are shared by every `declVal`, not
            // granted to `def` alone. The dominant Mathlib idiom is an `↔`
            // statement proved by `mp`/`mpr` field assignments.
            if self.check(&TokenKind::Pipe) {
                self.def_match_body(start_span)?
            } else if self.is_field_assign_start() {
                // Structure-instance sugar: `theorem t : S where\n  f := v` is
                // a struct literal `{ f := v }` elaborated at the annotated
                // type, exactly as for `def`. A theorem's type is mandatory, so
                // `struct_type: None` always has an expected type to resolve
                // against.
                let assigns = self.parse_where_field_assigns()?;
                SurfaceExpr::StructLit {
                    span: start_span,
                    struct_type: None,
                    base: None,
                    fields: assigns,
                }
            } else {
                self.def_match_body(start_span)?
            }
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected :=, | or where, got {:?}", self.current_kind()),
            });
        };

        // Parse optional termination_by and decreasing_by clauses for recursive theorems
        let termination = self.parse_termination_hints();

        // Parse optional where clause with local definitions
        let where_decls = self.parse_where_local_defs();

        Ok(SurfaceDecl::Theorem {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            proof: Box::new(proof),
            attrs,
            termination,
            modifiers,
            where_decls,
        })
    }

    pub(in crate::grammar) fn axiom_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name_start = self.pos;
        let name = self.decl_name()?;
        self.observe_declaration_name(start_span, name_start, &name);
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        self.expect(&TokenKind::Colon)?;
        let ty = self.expr()?;

        Ok(SurfaceDecl::Axiom {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            attrs,
            modifiers,
        })
    }

    /// Parse opaque declaration with explicit modifiers.
    pub(in crate::grammar) fn opaque_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name_start = self.pos;
        let name = self.decl_name()?;
        self.observe_declaration_name(start_span, name_start, &name);
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        self.expect(&TokenKind::Colon)?;
        let ty = self.expr()?;

        // Optional value: `:= expr`
        let val = if self.eat(&TokenKind::ColonEq) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        Ok(SurfaceDecl::Opaque {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            val,
            attrs,
            modifiers,
        })
    }

    /// Parse optional `where` clause containing local definitions.
    ///
    /// ```text
    /// def foo : Nat := helper 42
    /// where
    ///   helper (n : Nat) : Nat := n + 1
    /// ```
    ///
    /// Returns an empty Vec if no `where` keyword is found.
    ///
    /// Reference: Lean 4 `src/Lean/Elab/MutualDef.lean` (elabWhereDeclsAsLetRec)
    pub(in crate::grammar) fn parse_where_local_defs(&mut self) -> Vec<WhereLocalDef> {
        if !self.eat(&TokenKind::Where) {
            return Vec::new();
        }

        // Enable in_where_block so the expression parser stops at identifiers
        // that start new where-definitions (ident ... :=).
        let saved_in_where = self.in_where_block;
        self.in_where_block = true;

        let mut defs = Vec::new();

        // Parse local definitions until we hit a declaration boundary,
        // termination hint, or EOF. Each definition starts with an identifier.
        while let TokenKind::Ident(_) = self.current_kind() {
            // Stop if this looks like a termination hint or another declaration
            if self.at_termination_hint_end(0) || self.is_decl_start() {
                break;
            }

            match self.parse_single_where_def() {
                Ok(def) => defs.push(def),
                Err(_) => break,
            }
        }

        self.in_where_block = saved_in_where;
        defs
    }

    /// Parse a single local definition inside a `where` block.
    ///
    /// Syntax: `name binders? (: ret_ty)? := body`
    /// or the equation form `name binders? (: ret_ty)? | pat => body | …`
    /// (a helper defined by pattern matching, e.g. `where go : Nat → Nat
    /// | 0 => 0 | k+1 => go k`) — desugared via [`Self::def_match_body`] exactly
    /// like a top-level `def`'s equation body.
    fn parse_single_where_def(&mut self) -> Result<WhereLocalDef, ParseError> {
        let start_span = self.current_span();

        // Parse the name
        let name = self.decl_name()?;

        // Parse optional binders
        let binders = self.optional_binders()?;

        // Parse optional return type annotation
        let ret_ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        // Body: either `:= expr` or the equation form `| pat => body | …`.
        let body = if self.check(&TokenKind::Pipe) {
            self.def_match_body(start_span)?
        } else {
            self.expect(&TokenKind::ColonEq)?;
            self.expr()?
        };

        // A `termination_by` / `decreasing_by` after a helper's body belongs
        // to that helper (Lean `letRecDecl`'s termination suffix).
        let termination = self.parse_termination_hints();

        let end_span = self.current_span();

        Ok(WhereLocalDef {
            span: Span::new(start_span.start, end_span.end),
            name,
            binders,
            ret_ty,
            body,
            termination,
        })
    }
}
