// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for structure declarations, deriving clauses, field types,
//! universe parameters, and optional binders.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::DeclModifiers;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse a structure declaration with explicit modifiers.
    ///
    /// ```text
    /// structure Point where
    ///   x : Nat
    ///   y : Nat
    /// ```
    ///
    /// Or with parameters:
    /// ```text
    /// structure Pair (A : Type) (B : Type) where
    ///   fst : A
    ///   snd : B
    /// ```
    pub(in crate::grammar) fn structure_decl_with_mods(
        &mut self,
        start_span: Span,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        // Optional extends clause: `structure Foo extends Bar, Baz`
        // Parse as a comma-separated list of parent type expressions, mirroring
        // the class parser. `app_expr` handles `Bar α` style applications.
        let mut extends = Vec::new();
        if self.eat(&TokenKind::Extends) {
            extends.push(Box::new(self.app_expr()?));
            while self.eat(&TokenKind::Comma) {
                extends.push(Box::new(self.app_expr()?));
            }
        }

        // Optional explicit result type: `structure Foo : Type 1 where`
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        // Older Lean 4 form: `structure Foo params [extends …] := [ctor ::]
        // (f₁ : T₁) (f₂ : T₂) …` — `:=` introduces the anonymous constructor's
        // parenthesized field binders, equivalent to a `where` field block. A
        // group with multiple names (`(a b : T)`) expands to one field per name.
        if self.eat(&TokenKind::ColonEq) {
            let ctor_name = if matches!(self.current_kind(), TokenKind::Ident(_))
                && matches!(self.peek_kind(1), Some(TokenKind::ColonColon))
            {
                let n = self.ident()?;
                self.expect(&TokenKind::ColonColon)?;
                Some(n)
            } else {
                None
            };

            let fields = self.parse_paren_field_binders()?;

            let deriving = self.parse_deriving_clause()?;
            return Ok(SurfaceDecl::Structure {
                span: start_span,
                name,
                universe_params,
                binders,
                extends,
                ty,
                ctor_name,
                fields,
                deriving,
                modifiers,
            });
        }

        // Handle case where structure has no fields (just extends)
        if !self.check(&TokenKind::Where) {
            return Ok(SurfaceDecl::Structure {
                span: start_span,
                name,
                universe_params,
                binders,
                extends,
                ty,
                ctor_name: None,
                fields: Vec::new(),
                deriving: Vec::new(),
                modifiers,
            });
        }

        self.expect(&TokenKind::Where)?;

        // Optional explicit constructor name: `structure P where make :: …`
        // (Lean `structCtor` = `ident " :: "`). When present, the constructor is
        // named `<Struct>.<make>` rather than the default `<Struct>.mk`. Detected
        // as an identifier immediately followed by `::` (`ColonColon`).
        let ctor_name = if matches!(self.current_kind(), TokenKind::Ident(_))
            && matches!(self.peek_kind(1), Some(TokenKind::ColonColon))
        {
            let n = self.ident()?;
            self.expect(&TokenKind::ColonColon)?;
            Some(n)
        } else {
            None
        };

        // Parse fields. Lean's `structFields` accepts PARENTHESIZED binder
        // groups (`(x y : Nat)`, one field per name, optional group default)
        // interleaved with simple `name : Ty` fields; before this arm the
        // groups fell out of the `where` block entirely and the structure was
        // SILENTLY accepted with zero fields (the junk resurfacing as a raw
        // decl) — the audit's "wrong program silently accepted" shape.
        let mut fields = Vec::new();
        loop {
            if self.check(&TokenKind::LParen) {
                fields.extend(self.parse_paren_field_binders()?);
                continue;
            }
            if !self.is_field_start() {
                break;
            }
            let field_span = self.current_span();
            let field_name = self.ident()?;

            // Bare `name := value` — a field-default OVERRIDE of an inherited
            // field (Lean `structSimpleBinder` with no type ascription):
            // `structure C extends B where x := 10` re-defaults `B`'s `x`.
            // The type is a placeholder hole; the elaborator resolves it from
            // the parent field and rejects non-inherited names loudly. (B90)
            if self.eat(&TokenKind::ColonEq) {
                let default_val = self.field_type_expr()?;
                fields.push(SurfaceField {
                    span: field_span,
                    name: field_name,
                    ty: SurfaceExpr::Hole(field_span),
                    default: Some(default_val),
                    is_default_override: true,
                });
                continue;
            }

            self.expect(&TokenKind::Colon)?;
            let field_ty = self.field_type_expr()?;

            // Optional default value: `field : Type := value`
            let default = if self.eat(&TokenKind::ColonEq) {
                Some(self.field_type_expr()?)
            } else {
                None
            };

            fields.push(SurfaceField {
                span: field_span,
                name: field_name,
                ty: field_ty,
                default,
                is_default_override: false,
            });
        }

        // Parse optional deriving clause: `deriving Repr, BEq`
        let deriving = self.parse_deriving_clause()?;

        Ok(SurfaceDecl::Structure {
            span: start_span,
            name,
            universe_params,
            binders,
            extends,
            ty,
            ctor_name,
            fields,
            deriving,
            modifiers,
        })
    }

    /// Parse a deriving clause: `deriving Class1, Class2, ...`
    pub(in crate::grammar) fn parse_deriving_clause(
        &mut self,
    ) -> Result<Vec<SurfaceName>, ParseError> {
        if !self.eat(&TokenKind::Deriving) {
            return Ok(Vec::new());
        }

        let mut classes = Vec::new();

        // Parse first class name
        classes.push(self.qualified_ident()?);

        // Parse remaining class names separated by commas
        while self.eat(&TokenKind::Comma) {
            classes.push(self.qualified_ident()?);
        }

        Ok(classes)
    }

    /// Parse a run of parenthesized field binders `(name… : type [:= default])*`
    /// — the field spec of the legacy `structure`/`class` `:=` form, and the
    /// parenthesized groups Lean's `structFields` accepts inside a `where`
    /// block (`structure P where (x : Nat) (y : Nat)`). A group with multiple
    /// names (`(a b : T)`) expands to one field per name; a group default
    /// applies to every name in its group. Shared by the structure and class
    /// parsers.
    pub(in crate::grammar) fn parse_paren_field_binders(
        &mut self,
    ) -> Result<Vec<SurfaceField>, ParseError> {
        let mut fields = Vec::new();
        while self.check(&TokenKind::LParen) {
            let group_span = self.current_span();
            self.expect(&TokenKind::LParen)?;
            let mut names = vec![self.ident()?];
            while matches!(self.current_kind(), TokenKind::Ident(_)) {
                names.push(self.ident()?);
            }
            self.expect(&TokenKind::Colon)?;
            let field_ty = self.expr()?;
            // Optional group default: `(x : Nat := 3)`. The closing paren
            // delimits the value, so the full expression grammar applies.
            let default = if self.eat(&TokenKind::ColonEq) {
                Some(self.expr()?)
            } else {
                None
            };
            self.expect(&TokenKind::RParen)?;
            for name in names {
                fields.push(SurfaceField {
                    span: group_span,
                    name,
                    ty: field_ty.clone(),
                    default: default.clone(),
                    is_default_override: false,
                });
            }
        }
        Ok(fields)
    }

    /// Check if the current position looks like a field declaration start.
    /// A field starts with an identifier followed by a colon (`x : Nat`), or
    /// by `:=` for a bare field-default override of an inherited field
    /// (`x := 10` under `structure C extends B where`). (B90)
    pub(in crate::grammar) fn is_field_start(&self) -> bool {
        if !matches!(self.current_kind(), TokenKind::Ident(_)) {
            return false;
        }
        // Check if next token is a colon or `:=`
        self.tokens
            .get(self.pos + 1)
            .is_some_and(|t| matches!(t.kind, TokenKind::Colon | TokenKind::ColonEq))
    }

    /// Parse a field type expression (also used for in-field defaults).
    ///
    /// A structure/class field type is a full type expression — it may use the
    /// entire operator grammar (`=`, `<`, `>`, `≤`, `≠`, `∧`, `∨`, `↔`, `→`,
    /// arithmetic, …), so Subtype-style dependent fields like `h : n = n` and
    /// `property : 0 < val` parse. This mirrors Lean's field telescope in
    /// `src/Lean/Elab/Structure.lean`, where each field's type is elaborated in
    /// a context extended by the prior fields (so field N's type may reference
    /// fields 1..N-1).
    ///
    /// The `in_field_type` flag makes the application/operator spine stop at the
    /// next field (a newline-leading `ident :`) instead of swallowing it as an
    /// argument or an operator's right operand; delimited sub-expressions
    /// (parens, `⟨⟩`, `{}`, …) parse at full generality. This replaces the old
    /// app+arrow-only `field_arrow_expr`/`field_app_expr` sub-grammar, which
    /// could not see any infix operator — a field type of `n = n` parsed as
    /// just `n`, leaving `= n` as an error-recovery raw declaration (brick B11).
    pub(in crate::grammar) fn field_type_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let saved = self.in_field_type;
        self.in_field_type = true;
        let result = self.expr();
        self.in_field_type = saved;
        result
    }

    pub(in crate::grammar) fn universe_params(&mut self) -> Result<Vec<SurfaceName>, ParseError> {
        let mut params = Vec::new();

        // Lean 4 spells declaration universe binders with a DOT ONLY: `def f.{u}`
        // (`declId := ident >> optional (".{" >> sepBy1 ident ", " >> "}")` in
        // `Lean/Parser/Command.lean`). A DOTLESS `{...}` after a declaration name is
        // always an implicit binder group, never a universe list, and the absence of a
        // colon does NOT distinguish the two — Lean auto-binds an untyped implicit.
        //
        // Measured against the pinned `lean` v4.30.0-rc2 with `set_option pp.parens true`:
        //
        //   def f {a} (x : a) : a := x
        //     => def f.{u_1} : {a : (Sort u_1)} → (a → a)   -- `a` is an IMPLICIT BINDER,
        //                                                   -- the universe is auto-bound
        //   def g.{u} (x : Type u) : Type u := x
        //     => def g.{u} : (Type u) → (Type u)            -- `u` is a universe param
        //   structure C {u} (A : Type u) where val : A
        //     => error: Failed to infer type of binder `u`  -- read as an implicit binder
        //                                                   -- and REJECTED, not a universe list
        //
        // Accepting the dotless form here refused every ordinary untyped implicit binder
        // (`def idA {alpha} (x : alpha) : alpha := x`) by routing it into the closed
        // explicit-universe-list check, which then reported a leaked level metavariable.
        // That cost the pinned Mathlib SOURCE slice 326/784 -> 301/775.
        if self.check(&TokenKind::Dot) {
            // Check for .{u v} syntax
            let next_is_lbrace = self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|t| matches!(t.kind, TokenKind::LBrace));
            if next_is_lbrace {
                self.advance(); // consume dot
                self.advance(); // consume lbrace
                                // Lean `declId` universe binders are comma-separated:
                                // `def f.{u, v}` (`Lean/Parser/Command.lean`). Lean itself
                                // REJECTS the space-separated `.{u v}` ("unexpected
                                // identifier; expected '}'", measured on the pinned
                                // v4.30.0-rc2); we accept it as a deliberate superset by
                                // eating an optional comma between names.
                while let TokenKind::Ident(name) = self.current_kind() {
                    params.push(self.name_token(name)?);
                    self.advance();
                    self.eat(&TokenKind::Comma);
                }
                self.expect(&TokenKind::RBrace)?;
            }
        }

        Ok(params)
    }

    pub(in crate::grammar) fn optional_binders(
        &mut self,
    ) -> Result<Vec<SurfaceBinder>, ParseError> {
        let mut binders = Vec::new();

        loop {
            match self.current_kind() {
                TokenKind::LParen => binders.extend(self.explicit_binders()?),
                TokenKind::LBrace => binders.extend(self.implicit_binders()?),
                TokenKind::LBracket => binders.extend(self.instance_binders()?),
                // `⦃x : T⦄` — strict-implicit. The term-position binder loop
                // (expr_binders.rs) has always accepted this; declaration
                // position did not, so `def f ⦃a : Type⦄ ...` fell through to
                // error recovery while the identical term-position spelling
                // parsed. Mathlib uses declaration-position `⦃⦄` widely.
                TokenKind::StrictLBrace => binders.extend(self.strict_implicit_binders()?),
                // Bare identifier binders (without parentheses): `def foo x y := ...`
                TokenKind::Ident(name) => {
                    // First check if current ident immediately precedes := : | where
                    // If so, it's the last binder - consume it then break
                    // Otherwise, consume it and continue looking for more
                    let is_last_binder = matches!(
                        self.peek_kind(1),
                        Some(
                            TokenKind::ColonEq
                                | TokenKind::Colon
                                | TokenKind::Pipe
                                | TokenKind::Where
                        )
                    );
                    let span = self.current_span();
                    let name = self.name_token(name)?;
                    self.advance();
                    binders.push(SurfaceBinder {
                        span,
                        name,
                        ty: None,
                        default: None,
                        info: SurfaceBinderInfo::Explicit,
                    });
                    if is_last_binder {
                        break;
                    }
                }
                _ => break,
            }
        }

        // This parser is used for declaration headers, including local
        // functions subsequently lowered to lambdas. Keep that origin so
        // elaboration can distinguish them from source `fun` binders.
        for binder in &mut binders {
            binder.name = binder.name.clone().with_header_binder_origin(true);
        }
        Ok(binders)
    }

    /// Parse a `codef` declaration (copattern definition into a codata
    /// type): clauses are `name := expr`, one per observation/branch.
    ///
    /// ```text
    /// codef natsFrom (n : Nat) : Stream Nat where
    ///   head := n
    ///   tail := natsFrom (Nat.succ n)
    /// ```
    pub(in crate::grammar) fn codef_decl_with_mods(
        &mut self,
        start_span: Span,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let binders = self.optional_binders()?;
        self.expect(&TokenKind::Colon)?;
        let ty = Box::new(self.expr()?);
        self.expect(&TokenKind::Where)?;

        let mut clauses = Vec::new();
        while matches!(self.current_kind(), TokenKind::Ident(_))
            && matches!(self.peek_kind(1), Some(TokenKind::ColonEq))
        {
            let clause_name = self.ident()?;
            self.expect(&TokenKind::ColonEq)?;
            let value = self.field_type_expr()?;
            clauses.push((clause_name, value));
        }

        Ok(SurfaceDecl::Codef {
            span: start_span,
            name,
            binders,
            ty,
            clauses,
            modifiers,
        })
    }

    /// Parse a `codata` declaration (Rocq-style Type-level codata; M-type
    /// encoded by the elaborator). Two body shapes:
    ///
    /// ```text
    /// codata Stream (A : Type) where       -- RECORD: observation fields
    ///   head : A
    ///   tail : Stream A
    ///
    /// codata ITr (E : Type) (R : Type) where   -- VARIANT: ctor clauses
    ///   | Ret : R → ITr E R
    ///   | Tau : ITr E R → ITr E R
    /// ```
    ///
    /// The record body reuses the structure field grammar (`name : Ty`
    /// only — field defaults are rejected loudly). The variant body reuses
    /// [`Parser::parse_ctor_type`] verbatim, so `| Vis (e : E) (k : Ans e → T) : T`
    /// desugars exactly as it does for `inductive`. `where` is required for
    /// a record body and optional before a `|`-led variant body, matching
    /// `inductive`. `extends` is not part of the codata surface.
    ///
    /// The two bodies never mix: a `|` after fields, or a field after
    /// clauses, is a parse error rather than a half-formed declaration.
    /// See `designs/2026-08-28-variant-codata-surface.md` §2.
    pub(in crate::grammar) fn codata_decl_with_mods(
        &mut self,
        start_span: Span,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        // Optional explicit result sort: `codata Foo : Type where`
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        let had_where = self.eat(&TokenKind::Where);
        let body = if self.check(&TokenKind::Pipe) {
            CodataBody::Variant(self.codata_variant_clauses(&name, &binders)?)
        } else if had_where {
            CodataBody::Record(self.codata_record_fields()?)
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "codata expects `where` followed by observation fields, \
                          or `|`-led constructor clauses"
                    .to_string(),
            });
        };

        let deriving = self.parse_deriving_clause()?;

        Ok(SurfaceDecl::Codata {
            span: start_span,
            name,
            universe_params,
            binders,
            ty,
            body,
            deriving,
            modifiers,
        })
    }

    /// The record body: `name : Ty` observation fields.
    fn codata_record_fields(&mut self) -> Result<Vec<SurfaceField>, ParseError> {
        let mut fields = Vec::new();
        while self.is_field_start() {
            let field_span = self.current_span();
            let field_name = self.ident()?;
            self.expect(&TokenKind::Colon)?;
            let field_ty = self.field_type_expr()?;
            if self.check(&TokenKind::ColonEq) {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "codata fields are observations and cannot carry default values"
                        .to_string(),
                });
            }
            fields.push(SurfaceField {
                span: field_span,
                name: field_name,
                ty: field_ty,
                default: None,
                is_default_override: false,
            });
        }
        if self.check(&TokenKind::Pipe) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "codata: a `|` constructor clause cannot follow observation \
                          fields — a codata body is either a record (fields) or a \
                          variant (clauses), never both"
                    .to_string(),
            });
        }
        Ok(fields)
    }

    /// The variant body: `|`-led constructor clauses, sharing the
    /// `inductive` constructor grammar.
    fn codata_variant_clauses(
        &mut self,
        name: &SurfaceName,
        binders: &[SurfaceBinder],
    ) -> Result<Vec<SurfaceCtor>, ParseError> {
        let mut ctors = Vec::new();
        while self.eat(&TokenKind::Pipe) {
            let ctor_span = self.current_span();
            let ctor_name = self.raw_ident()?;
            let ctor_ty = self.parse_ctor_type(ctor_span, name, binders)?;
            ctors.push(SurfaceCtor {
                span: ctor_span,
                name: ctor_name,
                ty: ctor_ty,
            });
        }
        if self.is_field_start() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "codata: an observation field cannot follow `|` constructor \
                          clauses — a codata body is either a record (fields) or a \
                          variant (clauses), never both"
                    .to_string(),
            });
        }
        Ok(ctors)
    }
}
