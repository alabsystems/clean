// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tactic `have` uses Lean's declaration value grammar (`:= term` or equations).

use super::decl::EquationArmBoundary;
use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{Span, SurfaceExpr, SurfaceTactic};
use crate::ParseError;

impl Parser {
    pub(crate) fn parse_tactic_have(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        let have_col = self
            .pos
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or_else(|| self.current().col, |t| t.col);
        if matches!(self.current_kind(), TokenKind::LAngle) {
            return self.parse_tactic_obtain(start);
        }

        // An explicit `_` is inaccessible; an omitted binder names `this`.
        let name = if self.eat(&TokenKind::Underscore) {
            Some(super::tactic::inaccessible_hypothesis())
        } else if matches!(self.current_kind(), TokenKind::Ident(_)) {
            Some(self.expect_ident("have")?)
        } else {
            None
        };
        let params = self.optional_binders()?;
        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.parse_tactic_expr()?)
        } else {
            None
        };

        let value = if self.check(&TokenKind::Pipe) {
            // A dedent ends this local value, leaving the continuation tactic
            // (or an enclosing case's pipe) to its own reader.
            let saved_stop = self.stop_app_at_newline_outer_indent;
            self.push_indent_for(have_col, "have equations");
            self.stop_app_at_newline_outer_indent = true;
            let value = self.def_match_body_bounded(start, EquationArmBoundary::LetValue);
            self.stop_app_at_newline_outer_indent = saved_stop;
            self.pop_indent();
            value?
        } else if self.eat(&TokenKind::ColonEq) {
            let by_span = self.current_span();
            if self.eat(&TokenKind::By) {
                let tacs = self.indented_tactic_seq()?;
                if params.is_empty() && ty.is_some() {
                    // Preserve the typed sub-proof path and its local closing
                    // rules. Inferred `by` values below use term elaboration
                    // with no expected type, just like any other inferred RHS.
                    let proof = match <[SurfaceTactic; 1]>::try_from(tacs) {
                        Ok([tac]) => tac,
                        Err(tacs) => SurfaceTactic::Paren(by_span, tacs),
                    };
                    return Ok(SurfaceTactic::Have(
                        start,
                        name,
                        ty.map(Box::new),
                        Box::new(proof),
                    ));
                }
                SurfaceExpr::ByTactic(by_span.merge(self.prev_span()), tacs)
            } else {
                self.parse_tactic_expr()?
            }
        } else {
            // Report the entire declaration-value choice. Neither bare `by`
            // nor `from` belongs to Lean's letDeclVal grammar.
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "expected ':=' or '|' in have declaration".to_string(),
            });
        };

        // Local declaration binders are function arguments; the annotation is
        // the return type, rather than the type of the resulting function.
        let (ty, value) = if params.is_empty() {
            (ty, value)
        } else {
            (
                ty.map(|ty| SurfaceExpr::Pi(start, params.clone(), Box::new(ty))),
                SurfaceExpr::Lambda(start, params, Box::new(value)),
            )
        };
        let proof = SurfaceTactic::Term(value.span(), Box::new(value));
        Ok(SurfaceTactic::Have(
            start,
            name,
            ty.map(Box::new),
            Box::new(proof),
        ))
    }
}
