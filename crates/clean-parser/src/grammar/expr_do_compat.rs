// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compatibility do-notation forms that are small parser extensions over the
//! core do-block grammar.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    fn wrap_do_function_return_type(
        &self,
        params: &[SurfaceBinder],
        ret_ty: SurfaceExpr,
    ) -> SurfaceExpr {
        if params.is_empty() {
            return ret_ty;
        }

        let start_span = params.first().map_or(ret_ty.span(), |binder| binder.span);
        SurfaceExpr::Pi(
            start_span.merge(ret_ty.span()),
            params.to_vec(),
            Box::new(ret_ty),
        )
    }

    /// Parse the binder part of a regular do-let declaration.
    pub(super) fn parse_do_let_binder(&mut self) -> Result<SurfaceBinder, ParseError> {
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
                        "expected identifier in do let binding, got {:?}",
                        self.current_kind()
                    ),
                })
            }
        };

        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.expr()?)
        } else {
            None
        };

        Ok(SurfaceBinder::new(name, ty, SurfaceBinderInfo::Explicit))
    }

    /// Parse `have h : P := proof` inside a do-block.
    ///
    /// This is a pure local declaration, so it lowers onto `DoElem::Let`.
    pub(super) fn parse_do_have(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        let (name, params) = if matches!(
            self.current_kind(),
            TokenKind::Ident(_) | TokenKind::Underscore
        ) {
            let name = match self.current_kind() {
                TokenKind::Ident(_) => self.ident()?,
                TokenKind::Underscore => {
                    self.advance();
                    "_".to_string()
                }
                _ => unreachable!("guarded by matches!"),
            };
            (name, self.optional_binders()?)
        } else {
            ("_h".to_string(), Vec::new())
        };
        let mut ty = if self.eat(&TokenKind::Colon) {
            Some(self.expr()?)
        } else {
            None
        };
        self.expect(&TokenKind::ColonEq)?;
        let mut val = self.parse_do_elem_expr()?;
        if !params.is_empty() {
            if let Some(ret_ty) = ty.take() {
                ty = Some(self.wrap_do_function_return_type(&params, ret_ty));
            }
            let val_span = val.span();
            val = SurfaceExpr::Lambda(val_span, params, Box::new(val));
        }
        let span = start_span.merge(val.span());
        let binder = SurfaceBinder::new(name, ty, SurfaceBinderInfo::Explicit);
        Ok(DoElem::Let(span, binder, Box::new(val)))
    }

    /// Parse `let rec f args := body [and g args := body]*` inside a do-block.
    ///
    /// Supports mutual recursion via `and` clauses (Lean 4 `doLetRec`).
    pub(super) fn parse_do_let_rec(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        let mut decls = vec![self.parse_single_let_rec_decl()?];

        // Parse additional `and` clauses for mutual recursion
        while matches!(self.current_kind(), TokenKind::Ident(name) if name == "and") {
            self.advance(); // consume `and`
            decls.push(self.parse_single_let_rec_decl()?);
        }

        let end_span = decls
            .last()
            .map(|(_, val)| val.span())
            .unwrap_or(start_span);
        Ok(DoElem::LetRec(start_span.merge(end_span), decls))
    }

    /// Parse a single recursive declaration: `f args := body`.
    fn parse_single_let_rec_decl(
        &mut self,
    ) -> Result<(SurfaceBinder, Box<SurfaceExpr>), ParseError> {
        let name = match self.current_kind() {
            TokenKind::Ident(_) => self.ident()?,
            _ => {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!(
                        "expected identifier in `let rec` declaration, got {:?}",
                        self.current_kind()
                    ),
                })
            }
        };

        let params = self.optional_binders()?;
        let mut ty = if self.eat(&TokenKind::Colon) {
            Some(self.expr()?)
        } else {
            None
        };

        self.expect(&TokenKind::ColonEq)?;
        let mut val = self.parse_do_elem_expr()?;
        if !params.is_empty() {
            if let Some(ret_ty) = ty.take() {
                ty = Some(self.wrap_do_function_return_type(&params, ret_ty));
            }
            let val_span = val.span();
            val = SurfaceExpr::Lambda(val_span, params, Box::new(val));
        }

        let binder = SurfaceBinder::new(name, ty, SurfaceBinderInfo::Explicit);
        Ok((binder, Box::new(val)))
    }

    /// Parse `assert! cond` / `debug_assert! cond` inside a do-block.
    ///
    /// These are sequenced actions, so the parser lowers them to ordinary
    /// expression statements that call the named assertion helper.
    pub(super) fn parse_do_assert(
        &mut self,
        start_span: Span,
        name: &str,
    ) -> Result<DoElem, ParseError> {
        let cond = self.parse_do_elem_expr()?;
        let span = start_span.merge(cond.span());
        let expr = SurfaceExpr::App(
            span,
            Box::new(SurfaceExpr::Ident(start_span, name.to_string())),
            vec![SurfaceArg::positional(cond)],
        );
        Ok(DoElem::Expr(span, Box::new(expr)))
    }

    /// Parse `match_expr discr with | pat => doSeq | _ => doSeq`.
    ///
    /// The current parser reuses the existing do-match representation.
    pub(super) fn parse_do_match_expr(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        self.consume_optional_match_expr_meta_false()?;

        let discr = self.expr()?;
        self.expect(&TokenKind::With)?;

        let mut arms = Vec::new();
        while self.eat(&TokenKind::Pipe) {
            let arm_span = self.current_span();
            let pattern = self.pattern_with_or()?;
            self.expect(&TokenKind::FatArrow)?;
            let body = self.parse_do_seq()?;
            let end = body.last().map_or(arm_span, |e| e.span());
            arms.push(DoMatchArm {
                span: arm_span.merge(end),
                patterns: vec![pattern],
                body,
            });
        }

        if arms.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected at least one `match_expr` arm".into(),
            });
        }

        let end_span = arms
            .last()
            .and_then(|arm| arm.body.last())
            .map_or(discr.span(), |elem| elem.span());
        Ok(DoElem::Match(start_span.merge(end_span), vec![discr], arms))
    }

    /// Parse `let_expr pat := discr | fallback` or `let_expr pat <- discr | fallback`.
    pub(super) fn parse_do_let_expr(&mut self, start_span: Span) -> Result<DoElem, ParseError> {
        let pat = self.pattern_with_or()?;
        let kind = if self.eat(&TokenKind::ColonEq) {
            DoLetExprKind::Pure
        } else if self.eat(&TokenKind::LeftArrow) {
            DoLetExprKind::Bind
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected `:=` or `←`/`<-` after `let_expr` pattern, got {:?}",
                    self.current_kind()
                ),
            });
        };

        let discr = self.parse_do_elem_expr()?;
        self.expect(&TokenKind::Pipe)?;
        let fallback = self.parse_do_seq()?;
        let end_span = fallback.last().map_or(discr.span(), |elem| elem.span());
        Ok(DoElem::LetExpr(
            start_span.merge(end_span),
            pat,
            Box::new(discr),
            kind,
            fallback,
        ))
    }

    fn consume_optional_match_expr_meta_false(&mut self) -> Result<(), ParseError> {
        let looks_like_meta_false = matches!(self.current_kind(), TokenKind::LParen)
            && matches!(self.peek_kind(1), Some(TokenKind::Ident(name)) if name == "meta")
            && matches!(self.peek_kind(2), Some(TokenKind::ColonEq))
            && matches!(self.peek_kind(3), Some(TokenKind::Ident(name)) if name == "false")
            && matches!(self.peek_kind(4), Some(TokenKind::RParen));

        if !looks_like_meta_false {
            return Ok(());
        }

        self.expect(&TokenKind::LParen)?;
        let meta_name = self.ident()?;
        if meta_name != "meta" {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected `meta`, got `{meta_name}`"),
            });
        }
        self.expect(&TokenKind::ColonEq)?;
        let false_name = self.ident()?;
        if false_name != "false" {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected `false`, got `{false_name}`"),
            });
        }
        self.expect(&TokenKind::RParen)?;
        Ok(())
    }
}
