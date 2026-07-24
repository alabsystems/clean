// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compatibility lowering for parser-only do-notation forms.

use super::*;
use clean_parser::{DoLetExprKind, SurfaceBinderInfo};

impl<'a> ElabCtx<'a> {
    /// Lower recursive do-binding(s) onto nested `SurfaceExpr::LetRec`.
    ///
    /// For a single declaration, produces one `let rec f := v in do rest`.
    /// For mutual declarations (`and`), nests them: `let rec f := v in let rec g := w in do rest`.
    /// Note: nested `let rec` is an approximation — Lean 4 uses a single mutual block.
    /// True mutual visibility requires `SurfaceExpr` multi-binding support (future work).
    pub(super) fn elab_do_let_rec_elem(
        &mut self,
        decls: &[(SurfaceBinder, Box<SurfaceExpr>)],
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        // decls is always non-empty (parser requires at least one declaration)
        let first_val_span = decls[0].1.span();
        let body = SurfaceExpr::Do(
            rest.last()
                .map_or(first_val_span, |elem| first_val_span.merge(elem.span())),
            rest.to_vec(),
        );

        // Build inside-out: innermost let rec wraps the body, outer ones wrap that
        let mut result = body;
        for (binder, val) in decls.iter().rev() {
            result = SurfaceExpr::LetRec(
                val.span().merge(result.span()),
                binder.clone(),
                Box::new(val.as_ref().clone()),
                Box::new(result),
            );
        }
        self.elaborate(&result)
    }

    /// Lower `let_expr` to the existing do-match / do-bind infrastructure.
    pub(super) fn elab_do_let_expr_elem(
        &mut self,
        pat: &SurfacePattern,
        discr: &SurfaceExpr,
        kind: DoLetExprKind,
        fallback: &[DoElem],
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let span = discr.span();
        let success_body = if rest.is_empty() {
            vec![DoElem::Return(
                span,
                Box::new(SurfaceExpr::Ident(span, "Unit.unit".to_string())),
            )]
        } else {
            rest.to_vec()
        };
        let success_arm = DoMatchArm {
            span,
            patterns: vec![pat.clone()],
            body: success_body,
        };
        let fallback_arm = DoMatchArm {
            span,
            patterns: vec![SurfacePattern::Wildcard],
            body: fallback.to_vec(),
        };

        match kind {
            DoLetExprKind::Pure => {
                let match_elem =
                    DoElem::Match(span, vec![discr.clone()], vec![success_arm, fallback_arm]);
                self.elab_do_elems(&[match_elem])
            }
            DoLetExprKind::Bind => {
                let fresh = "__let_expr_x".to_string();
                let binder = SurfaceBinder::new(&fresh, None, SurfaceBinderInfo::Explicit);
                let bind_elem = DoElem::Bind(span, binder, Box::new(discr.clone()));
                let match_elem = DoElem::Match(
                    span,
                    vec![SurfaceExpr::Ident(span, fresh)],
                    vec![success_arm, fallback_arm],
                );
                self.elab_do_elems(&[bind_elem, match_elem])
            }
        }
    }
}
