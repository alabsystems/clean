// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The template walk over `do` elements (see the parent module doc).

use super::*;

impl Walker<'_> {
    // ------------------------------------------------------------------
    // `do` blocks: a binder scopes over the REST of its sequence.
    // ------------------------------------------------------------------
    pub(super) fn do_seq(&mut self, elems: &[DoElem]) -> Walked<Vec<DoElem>> {
        let depth = self.env.len();
        let out = elems
            .iter()
            .map(|elem| self.do_elem(elem))
            .collect::<Walked<Vec<_>>>()?;
        self.env.truncate(depth);
        Ok(out)
    }

    pub(super) fn opt_do_seq(
        &mut self,
        elems: Option<&Vec<DoElem>>,
    ) -> Walked<Option<Vec<DoElem>>> {
        elems.map(|elems| self.do_seq(elems)).transpose()
    }

    #[allow(clippy::too_many_lines)] // one arm per do-element kind, by design
    pub(super) fn do_elem(&mut self, elem: &DoElem) -> Walked<DoElem> {
        Ok(match elem {
            // `let x ← e` / `let x := e` / `let mut x := e`: `x` scopes over
            // the rest of the sequence, not over `e`.
            DoElem::Bind(span, binder, value) => {
                let value = self.boxed(value)?;
                DoElem::Bind(*span, self.binder(binder)?, value)
            }
            DoElem::Let(span, binder, value) => {
                let value = self.boxed(value)?;
                DoElem::Let(*span, self.binder(binder)?, value)
            }
            DoElem::Have(span, binder, value) => {
                let value = self.boxed(value)?;
                DoElem::Have(*span, self.binder(binder)?, value)
            }
            DoElem::LetMut(span, binder, value) => {
                let value = self.boxed(value)?;
                DoElem::LetMut(*span, self.binder(binder)?, value)
            }
            // `let rec f := v and g := w`: every name is in scope in every
            // value and in the rest.
            DoElem::LetRec(span, decls) => {
                let binders = decls
                    .iter()
                    .map(|(binder, _)| self.binder(binder))
                    .collect::<Walked<Vec<_>>>()?;
                let decls = binders
                    .into_iter()
                    .zip(decls)
                    .map(|(binder, (_, value))| Ok((binder, self.boxed(value)?)))
                    .collect::<Walked<Vec<_>>>()?;
                DoElem::LetRec(*span, decls)
            }
            DoElem::Return(span, value) => DoElem::Return(*span, self.boxed(value)?),
            DoElem::Expr(span, value) => DoElem::Expr(*span, self.boxed(value)?),
            DoElem::DbgTrace(span, value) => DoElem::DbgTrace(*span, self.boxed(value)?),
            DoElem::If(span, cond, then_seq, else_seq) => DoElem::If(
                *span,
                self.boxed(cond)?,
                self.do_seq(then_seq)?,
                self.opt_do_seq(else_seq.as_ref())?,
            ),
            DoElem::IfLet(span, pattern, scrutinee, then_seq, else_seq) => {
                let scrutinee = self.boxed(scrutinee)?;
                let depth = self.env.len();
                let pattern = self.pattern_in_scope(pattern)?;
                let then_seq = self.do_seq(then_seq)?;
                self.env.truncate(depth);
                let else_seq = self.opt_do_seq(else_seq.as_ref())?;
                DoElem::IfLet(*span, pattern, scrutinee, then_seq, else_seq)
            }
            DoElem::IfDecidable(span, hyp, cond, then_seq, else_seq) => {
                let cond = self.boxed(cond)?;
                let depth = self.env.len();
                let hyp = self.bind(hyp)?;
                let then_seq = self.do_seq(then_seq)?;
                let else_seq = self.opt_do_seq(else_seq.as_ref())?;
                self.env.truncate(depth);
                DoElem::IfDecidable(*span, hyp, cond, then_seq, else_seq)
            }
            DoElem::For(span, binder, collection, body) => {
                let collection = self.boxed(collection)?;
                let depth = self.env.len();
                let binder = self.binder(binder)?;
                let body = self.do_seq(body)?;
                self.env.truncate(depth);
                DoElem::For(*span, binder, collection, body)
            }
            DoElem::Match(span, discriminants, arms) => {
                let discriminants = discriminants
                    .iter()
                    .map(|d| self.expr(d))
                    .collect::<Walked<Vec<_>>>()?;
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let depth = self.env.len();
                        let patterns = self.patterns_in_scope(&arm.patterns)?;
                        let body = self.do_seq(&arm.body)?;
                        self.env.truncate(depth);
                        Ok(DoMatchArm {
                            span: arm.span,
                            patterns,
                            body,
                        })
                    })
                    .collect::<Walked<Vec<_>>>()?;
                DoElem::Match(*span, discriminants, arms)
            }
            DoElem::TryCatch(span, body, catches, finally) => {
                let body = self.do_seq(body)?;
                let catches = catches
                    .iter()
                    .map(|clause| {
                        let exc_type = clause
                            .exc_type
                            .as_deref()
                            .map(|ty| self.boxed(ty))
                            .transpose()?;
                        let depth = self.env.len();
                        let binder = self.bind(&clause.binder)?;
                        let body = self.do_seq(&clause.body)?;
                        self.env.truncate(depth);
                        Ok(DoCatchClause {
                            span: clause.span,
                            binder,
                            exc_type,
                            body,
                        })
                    })
                    .collect::<Walked<Vec<_>>>()?;
                let finally = self.opt_do_seq(finally.as_ref())?;
                DoElem::TryCatch(*span, body, catches, finally)
            }
            // `let p ← e | alt`: `p`'s variables scope over the REST of the
            // sequence, never over `alt`.
            DoElem::LetElse(span, pattern, value, fallback) => {
                let value = self.boxed(value)?;
                let fallback = self.do_seq(fallback)?;
                let pattern = self.pattern_in_scope(pattern)?;
                DoElem::LetElse(*span, pattern, value, fallback)
            }
            DoElem::LetExpr(span, pattern, value, kind, fallback) => {
                let value = self.boxed(value)?;
                let fallback = self.do_seq(fallback)?;
                let pattern = self.pattern_in_scope(pattern)?;
                DoElem::LetExpr(*span, pattern, value, *kind, fallback)
            }
            DoElem::Repeat(span, body) => DoElem::Repeat(*span, self.do_seq(body)?),
            DoElem::While(span, cond, body) => {
                DoElem::While(*span, self.boxed(cond)?, self.do_seq(body)?)
            }
            DoElem::Break(span) => DoElem::Break(*span),
            DoElem::Continue(span) => DoElem::Continue(*span),
            // `x := e` / `(a, b) := e` name mutable variables in scope.
            DoElem::Reassign(span, name, value) => {
                DoElem::Reassign(*span, self.reference_name(name)?, self.boxed(value)?)
            }
            DoElem::PatternReassign(span, pattern, value) => {
                DoElem::PatternReassign(*span, self.pattern_refs(pattern)?, self.boxed(value)?)
            }
        })
    }
}
