// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tactic `have` and `letI` use Lean's declaration value grammar (`:= term` or equations).

use super::decl::EquationArmBoundary;
use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{Span, SurfaceExpr, SurfaceName, SurfaceTactic};
use crate::ParseError;

#[derive(Clone, Copy, PartialEq, Eq)]
enum LocalDeclaration {
    Have,
    LetI,
}

impl Parser {
    pub(crate) fn parse_tactic_have(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        self.tactic_local_declaration(start, LocalDeclaration::Have)
    }

    pub(crate) fn parse_tactic_let_i(&mut self, start: Span) -> Result<SurfaceTactic, ParseError> {
        self.tactic_local_declaration(start, LocalDeclaration::LetI)
    }

    fn tactic_local_declaration(
        &mut self,
        start: Span,
        kind: LocalDeclaration,
    ) -> Result<SurfaceTactic, ParseError> {
        let keyword = match kind {
            LocalDeclaration::Have => "have",
            LocalDeclaration::LetI => "letI",
        };
        let decl_col = self
            .pos
            .checked_sub(1)
            .and_then(|i| self.tokens.get(i))
            .map_or_else(|| self.current().col, |t| t.col);
        if kind == LocalDeclaration::Have && self.check(&TokenKind::LAngle) {
            return self.parse_tactic_obtain(start);
        }

        // An explicit `_` is inaccessible; an omitted binder names `this`.
        let name = if self.eat(&TokenKind::Underscore) {
            Some(super::tactic::inaccessible_hypothesis())
        } else if matches!(self.current_kind(), TokenKind::Ident(_)) {
            Some(self.expect_ident(keyword)?)
        } else {
            None
        };
        // Lean's letId excludes an adjacent '[' (the array update pattern).
        // Its parenthesized-pattern alternative also precedes a nameless
        // letIdDecl: a lone '(x)' is a pattern but '(x : T)' is a binder.
        let adjacent_bracket = name.is_some()
            && self.check(&TokenKind::LBracket)
            && self.prev_span().end == self.current_span().start;
        let starts_with_paren = name.is_none() && self.check(&TokenKind::LParen);
        let params_start = self.pos;
        let params = self.optional_binders_with_tuple_patterns(kind == LocalDeclaration::Have)?;
        let lone_paren_pattern = starts_with_paren
            && self.tokens[params_start + 1..self.pos - 1]
                .iter()
                .all(|t| matches!(t.kind, TokenKind::Ident(_) | TokenKind::Underscore));
        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.parse_tactic_binding_type()?)
        } else {
            None
        };

        if kind == LocalDeclaration::LetI
            && (adjacent_bracket || (lone_paren_pattern && self.check(&TokenKind::ColonEq)))
        {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: "letI cannot inline a pattern declaration".to_string(),
            });
        }
        let value = if self.check(&TokenKind::Pipe) {
            // A dedent ends this local value, leaving the continuation tactic
            // (or an enclosing case's pipe) to its own reader.
            let saved_stop = self.stop_app_at_newline_outer_indent;
            self.push_indent_for(decl_col, "local declaration equations");
            self.stop_app_at_newline_outer_indent = true;
            let value = self.def_match_body_bounded(start, EquationArmBoundary::LetValue);
            self.stop_app_at_newline_outer_indent = saved_stop;
            self.pop_indent();
            value?
        } else if self.eat(&TokenKind::ColonEq) {
            let by_span = self.current_span();
            if self.eat(&TokenKind::By) {
                let tacs = self.indented_tactic_seq()?;
                if kind == LocalDeclaration::Have && params.is_empty() && ty.is_some() {
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
                message: format!("expected ':=' or '|' in {keyword} declaration"),
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
        let ty = ty.map(Box::new);
        Ok(match kind {
            LocalDeclaration::Have => {
                let proof = SurfaceTactic::Term(value.span(), Box::new(value));
                SurfaceTactic::Have(start, name, ty, Box::new(proof))
            }
            LocalDeclaration::LetI => SurfaceTactic::LetI(
                start,
                name.unwrap_or_else(|| SurfaceName::component("this", false)),
                ty,
                Box::new(value),
            ),
        })
    }
}
