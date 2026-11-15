// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The ASCII existential `exists x, p`.
//!
//! Lean 4.8 declares it beside `∃` (`Init/NotationExtra.lean`):
//!
//! ```text
//! macro "exists" xs:explicitBinders ", " b:term : term =>
//!   expandExplicitBinders ``Exists xs b
//! syntax unbracketedExplicitBinders := (ppSpace binderIdent)+ (" : " term)?
//! syntax bracketedExplicitBinders   := "(" withoutPosition((binderIdent ppSpace)+ ": " term) ")"
//! syntax explicitBinders := (ppSpace bracketedExplicitBinders)+ <|> unbracketedExplicitBinders
//! ```
//!
//! So `exists` takes ONLY explicit binders — no `{x}` / `[inst]` brackets,
//! no binder predicate (`exists x > 0, p` is a syntax error, unlike `∃ x >
//! 0, p`), and a bracketed group always carries its type. This parser
//! accepts exactly that, and the result is the `Exists (fun x => …)` chain
//! `∃` produces. Before it, `exists` was read as an unknown identifier and a
//! statement such as trust-ir's `(exists result, Sem.run … = .ok result) ∨
//! …` failed the whole declaration to parser recovery.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{
    Span, SurfaceArg, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, SurfaceName,
};
use crate::ParseError;

impl Parser {
    /// The term after the `exists` keyword: `explicitBinders ", " term`.
    pub(super) fn exists_keyword_body(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceExpr, ParseError> {
        let binders = self.lean_explicit_binders()?;
        self.expect(&TokenKind::Comma)?;
        let mut result = self.expr()?;
        for binder in binders.into_iter().rev() {
            let span = start_span.merge(result.span());
            result = SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, SurfaceName::global_path("Exists"))),
                vec![SurfaceArg::positional(SurfaceExpr::Lambda(
                    span,
                    vec![binder],
                    Box::new(result),
                ))],
            );
        }
        Ok(result)
    }

    /// Lean's `explicitBinders`: one or more `(x y : T)` groups, or one
    /// unbracketed run `x y (: T)?`. The two forms do not mix.
    fn lean_explicit_binders(&mut self) -> Result<Vec<SurfaceBinder>, ParseError> {
        let mut binders = Vec::new();
        if self.check(&TokenKind::LParen) {
            while self.eat(&TokenKind::LParen) {
                let names = self.binder_ident_run()?;
                self.expect(&TokenKind::Colon)?;
                // `withoutPosition`: the type may continue on any column.
                let saved = self.position_suppressed_at;
                self.position_suppressed_at = Some(self.indent_stack.len());
                let ty = self.expr();
                self.position_suppressed_at = saved;
                let ty = ty?;
                self.expect(&TokenKind::RParen)?;
                Self::push_explicit(&mut binders, names, Some(&ty));
            }
        } else {
            let names = self.binder_ident_run()?;
            let ty = if self.eat(&TokenKind::Colon) {
                // A full `term`, which stops at the `,` that ends the binders.
                Some(self.with_term_slot(Self::iff_expr)?)
            } else {
                None
            };
            Self::push_explicit(&mut binders, names, ty.as_ref());
        }
        Ok(binders)
    }

    /// `binderIdent+` — identifiers (never a Lean keyword) or `_`.
    fn binder_ident_run(&mut self) -> Result<Vec<(Span, SurfaceName)>, ParseError> {
        let mut names = Vec::new();
        loop {
            match self.current_kind().clone() {
                TokenKind::Ident(text) => {
                    names.push((self.current_span(), self.name_token(&text)?));
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
                message: format!(
                    "expected a binder name after `exists`, got {:?}",
                    self.current_kind()
                ),
            });
        }
        Ok(names)
    }

    fn push_explicit(
        binders: &mut Vec<SurfaceBinder>,
        names: Vec<(Span, SurfaceName)>,
        ty: Option<&SurfaceExpr>,
    ) {
        for (span, name) in names {
            binders.push(SurfaceBinder {
                span,
                name,
                ty: ty.cloned().map(Box::new),
                default: None,
                info: SurfaceBinderInfo::Explicit,
            });
        }
    }
}
