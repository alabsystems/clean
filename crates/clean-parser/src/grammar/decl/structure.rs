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

        // Parse fields
        let mut fields = Vec::new();
        while self.is_field_start() {
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
    pub(in crate::grammar) fn parse_deriving_clause(&mut self) -> Result<Vec<String>, ParseError> {
        if !self.eat(&TokenKind::Deriving) {
            return Ok(Vec::new());
        }

        let mut classes = Vec::new();

        // Parse first class name
        classes.push(self.ident()?);

        // Parse remaining class names separated by commas
        while self.eat(&TokenKind::Comma) {
            classes.push(self.ident()?);
        }

        Ok(classes)
    }

    /// Parse a run of parenthesized field binders `(name… : type)*` — the field
    /// spec of the legacy `structure`/`class` `:=` form. A group with multiple
    /// names (`(a b : T)`) expands to one field per name. Shared by the
    /// structure and class parsers.
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
            self.expect(&TokenKind::RParen)?;
            for name in names {
                fields.push(SurfaceField {
                    span: group_span,
                    name,
                    ty: field_ty.clone(),
                    default: None,
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

    pub(in crate::grammar) fn universe_params(&mut self) -> Result<Vec<String>, ParseError> {
        let mut params = Vec::new();

        // Universe params can be:
        // 1. .{u v} - explicit with dot prefix
        // 2. {u v} - identifiers only, no colon (distinguishes from implicit binders {α : Type})

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
                                // `def f.{u, v}` (`Lean/Parser/Command.lean`). Space-separated
                                // (`.{u v}`) is also accepted; tolerate both by eating an
                                // optional comma between names.
                while let TokenKind::Ident(name) = self.current_kind() {
                    params.push(name.clone());
                    self.advance();
                    self.eat(&TokenKind::Comma);
                }
                self.expect(&TokenKind::RBrace)?;
            }
        } else if self.check(&TokenKind::LBrace) {
            // Check for {u v} style - but only if it's NOT followed by a colon
            // (which would make it an implicit binder like {α : Type})
            let saved_pos = self.pos;
            self.advance(); // consume lbrace

            // Collect identifiers (comma-separated or space-separated)
            let mut names = Vec::new();
            while let TokenKind::Ident(name) = self.current_kind() {
                names.push(name.clone());
                self.advance();
                self.eat(&TokenKind::Comma);
            }

            // If we see RBrace (not Colon), these are universe params
            if self.check(&TokenKind::RBrace) && !names.is_empty() {
                self.advance(); // consume rbrace
                params = names;
            } else {
                // Backtrack - this is an implicit binder, not universe params
                self.pos = saved_pos;
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
                    let name = name.clone();
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

        Ok(binders)
    }
}
