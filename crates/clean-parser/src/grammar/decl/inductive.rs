// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for inductive and coinductive type declarations,
//! including constructor type parsing.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::DeclModifiers;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    pub(in crate::grammar) fn inductive_decl_with_mods(
        &mut self,
        start_span: Span,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        // Type annotation is optional in some cases
        let ty = if self.eat(&TokenKind::Colon) {
            self.expr()?
        } else {
            // Default to Type
            SurfaceExpr::Universe(start_span, UniverseExpr::Type)
        };

        // Parse constructors - three syntaxes supported:
        // 1. where-style: `inductive Foo where | ctor1 | ctor2`
        // 2. pipe-style:  `inductive Foo : Type | ctor1 : ... | ctor2 : ...`
        // 3. binder-style: `| ctor (a : A) (b : B) : ReturnType`
        //    (equivalent to `| ctor : (a : A) → (b : B) → ReturnType`)
        let mut ctors = Vec::new();

        // Check for `where` syntax
        if self.eat(&TokenKind::Where) {
            // Parse constructors after where
            while self.eat(&TokenKind::Pipe) || self.is_ctor_start() {
                let ctor_span = self.current_span();
                let ctor_name = self.ident()?;
                let ctor_ty = self.parse_ctor_type(ctor_span, &name, &binders)?;

                ctors.push(SurfaceCtor {
                    span: ctor_span,
                    name: ctor_name,
                    ty: ctor_ty,
                });
            }
        } else {
            // Pipe-style constructors
            while self.eat(&TokenKind::Pipe) {
                let ctor_span = self.current_span();
                let ctor_name = self.ident()?;
                let ctor_ty = self.parse_ctor_type(ctor_span, &name, &binders)?;

                ctors.push(SurfaceCtor {
                    span: ctor_span,
                    name: ctor_name,
                    ty: ctor_ty,
                });
            }
        }

        // Parse optional deriving clause: `deriving Repr, BEq`
        let deriving = self.parse_deriving_clause()?;

        Ok(SurfaceDecl::Inductive {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            ctors,
            deriving,
            modifiers,
        })
    }

    /// Parse coinductive (Lean 4.25+ #191)
    pub(in crate::grammar) fn coinductive_decl_with_mods(
        &mut self,
        start_span: Span,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;
        let ty = if self.eat(&TokenKind::Colon) {
            self.expr()?
        } else {
            SurfaceExpr::Universe(start_span, UniverseExpr::Type)
        };
        let mut ctors = Vec::new();
        if self.eat(&TokenKind::Where) {
            while self.eat(&TokenKind::Pipe) || self.is_ctor_start() {
                let ctor_span = self.current_span();
                let ctor_name = self.ident()?;
                let ctor_ty = self.parse_ctor_type(ctor_span, &name, &binders)?;
                ctors.push(SurfaceCtor {
                    span: ctor_span,
                    name: ctor_name,
                    ty: ctor_ty,
                });
            }
        } else {
            while self.eat(&TokenKind::Pipe) {
                let ctor_span = self.current_span();
                let ctor_name = self.ident()?;
                let ctor_ty = self.parse_ctor_type(ctor_span, &name, &binders)?;
                ctors.push(SurfaceCtor {
                    span: ctor_span,
                    name: ctor_name,
                    ty: ctor_ty,
                });
            }
        }
        let deriving = self.parse_deriving_clause()?;
        Ok(SurfaceDecl::Coinductive {
            span: start_span,
            name,
            universe_params,
            binders,
            ty: Box::new(ty),
            ctors,
            deriving,
            modifiers,
        })
    }

    /// Parse constructor type: optional binders then optional `: type`.
    ///
    /// Lean 4 constructor syntax supports three forms:
    /// 1. `| ctor : A → B → Ind A B`          — full type after colon
    /// 2. `| ctor (a : A) (b : B) : Ind A B`  — binders then return type
    /// 3. `| ctor`                              — defaults to inductive name
    ///
    /// Form 2 is desugared to a Pi/forall wrapping the return type:
    /// `(a : A) → (b : B) → Ind A B`
    ///
    /// Fix for #2001: previously only forms 1 and 3 were handled, so
    /// `| intro (a : A) (b : B) : And A B` was parsed as just `And`,
    /// dropping the binders entirely.
    fn parse_ctor_type(
        &mut self,
        ctor_span: Span,
        ind_name: &str,
        params: &[SurfaceBinder],
    ) -> Result<SurfaceExpr, ParseError> {
        // Default return type when a constructor omits it (`| nothing`): the
        // inductive applied to ALL its parameters by name (`Maybe α`), mirroring
        // the explicit form `| nothing : Maybe α`. The kernel's inductive check
        // (clean-kernel inductive/mod.rs validate_ctor_return_type) requires each
        // parameter to appear as its de-Bruijn-bound variable in the constructor's
        // return type; a bare `Maybe` (no params applied) leaves them absent and
        // `add_inductive` rejects every parametric inductive declared with the
        // shorthand. For a non-parametric inductive `params` is empty and this is
        // exactly the previous bare-name default.
        let default_return = || {
            let head = SurfaceExpr::Ident(ctor_span, ind_name.to_string());
            if params.is_empty() {
                head
            } else {
                let args = params
                    .iter()
                    .map(|b| SurfaceArg::positional(SurfaceExpr::Ident(ctor_span, b.name.clone())))
                    .collect();
                SurfaceExpr::App(ctor_span, Box::new(head), args)
            }
        };

        let has_binders = matches!(
            self.current_kind(),
            TokenKind::LParen
                | TokenKind::LBrace
                | TokenKind::LBracket
                | TokenKind::Ident(_)
                | TokenKind::Underscore
        );

        if has_binders {
            let binders = self.optional_binders()?;
            let return_ty = if self.eat(&TokenKind::Colon) {
                self.expr()?
            } else {
                default_return()
            };
            if binders.is_empty() {
                Ok(return_ty)
            } else {
                Ok(SurfaceExpr::Pi(ctor_span, binders, Box::new(return_ty)))
            }
        } else if self.eat(&TokenKind::Colon) {
            self.expr()
        } else {
            Ok(default_return())
        }
    }

    /// Check if current token starts a constructor definition
    pub(in crate::grammar) fn is_ctor_start(&self) -> bool {
        matches!(self.current_kind(), TokenKind::Ident(_))
    }
}
