// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multiplicative-precedence parsing, including Lean 4's non-associative raw `\`.

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::{SurfaceArg, SurfaceExpr};
use crate::ParseError;

impl Parser {
    /// Multiplicative expressions: `*`, `/`, `%`, `∩`, and non-associative `\`.
    ///
    /// Operands descend through [`Self::smul_expr`] (`•` prec 73) → `subst_expr`
    /// (`▸` prec 75) → [`Self::neg_expr`] (Lean prefix `-`, `prefix:75`) rather
    /// than straight into `pow_expr`, so `•`/`▸`/unary-minus all bind TIGHTER
    /// than `*` (70): `-3 * 2` = `(-3) * 2`, `2 * -3` = `2 * (-3)`, `a * b • c` =
    /// `a * (b • c)` (matches Lean v4.30). See [`Self::smul_expr`].
    pub(super) fn mul_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.smul_expr()?;
        let mut saw_prec_70_operator = false;

        loop {
            // A registered multi-token custom symbol may begin with a builtin
            // multiplicative token (`**` lexes as `Star, Star`). If the custom
            // layer left it for an outer precedence context, consuming the
            // first token here would split the authoritative symbol and turn a
            // valid left-associative chain into recovery syntax.
            if self.starts_custom_infix_or_postfix_at(0) {
                break;
            }
            let span = left.span();
            if self.eat(&TokenKind::Star) {
                let right = self.with_custom_min_prec(71, Self::smul_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HMul.hMul".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                saw_prec_70_operator = true;
            } else if self.eat(&TokenKind::Slash) {
                let right = self.with_custom_min_prec(71, Self::smul_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HDiv.hDiv".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                saw_prec_70_operator = true;
            } else if self.eat(&TokenKind::Percent) {
                let right = self.with_custom_min_prec(71, Self::smul_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HMod.hMod".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                saw_prec_70_operator = true;
            } else if self.eat(&TokenKind::Inter) {
                let right = self.with_custom_min_prec(71, Self::smul_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "Inter.inter".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                saw_prec_70_operator = true;
            } else if self.check(&TokenKind::SDiff) {
                let op_span = self.current_span();
                if saw_prec_70_operator {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: op_span.start,
                        message:
                            "non-associative `\\` requires parentheses after precedence-70 operators"
                                .to_string(),
                    });
                }
                self.advance();
                let right = self.with_custom_min_prec(71, Self::smul_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "SDiff.sdiff".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                saw_prec_70_operator = true;
            } else {
                break;
            }
        }

        Ok(left)
    }
}
