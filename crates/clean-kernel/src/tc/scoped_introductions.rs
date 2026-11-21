// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared strict introductions in one scoped certification declaration.

use super::{declaration_budget_used, TypeChecker, TypeError};
use crate::env::ScopedDeclarationWork;
use crate::expr::{BinderData, Expr, ExprKind};
use crate::mode::CleanMode;
use crate::work_meter::{charge, Walk};
use crate::{Level, Name};

#[derive(Clone, Copy)]
enum Introduction<'a> {
    Pi(BinderData, &'a Expr),
    Let(&'a Name, &'a Expr, &'a Expr),
}

impl TypeChecker<'_> {
    /// Check the actual type and value before the scope owner installs either.
    /// Each exact Pi/Lam domain and exact LET annotation and RHS is a premise
    /// of both judgments. Give both bodies the same fresh local and use the
    /// ordinary strict value checker at the first differing introduction.
    /// Its conversion lifts through each Pi by congruence and through each
    /// checked LET by the ordinary zeta rule. A successful result also
    /// reports whether the annotation satisfies ordinary LET sort formation.
    pub(crate) fn check_scoped_definition(
        &self,
        expected: &Expr,
        value: &Expr,
        work: &mut ScopedDeclarationWork,
    ) -> Result<bool, TypeError> {
        let outer = self.ctx_len();
        let result = (|| {
            let (expected, value, locals, formed) = self.scoped_definition_type(expected, value)?;
            work.after_type = declaration_budget_used();
            let checked = if locals.is_empty() {
                self.check_type(value, &expected)
            } else {
                self.open_scoped_introduction(value, &locals)
                    .and_then(|value| self.check_type(&value, &expected))
                    .and_then(|()| self.metered_scoped_operation(|| ()))
            };
            work.after_value = Some(declaration_budget_used());
            checked.map(|()| formed)
        })();
        self.ctx_truncate_to(outer);
        if work.after_value.is_none() {
            work.after_type = declaration_budget_used();
        }
        result
    }

    /// This route uses the ordinary non-cumulative product and zeta rules.
    /// A matched Pi ensures that the original outer LET/Pi type would infer
    /// a Sort. Other type forms retain the original infer_sort entry point,
    /// including its special handling of inferred Pi and SProp.
    fn scoped_definition_type<'value>(
        &self,
        expected: &Expr,
        value: &'value Expr,
    ) -> Result<(Expr, &'value Expr, Vec<Expr>, bool), TypeError> {
        let mut remaining_type = expected;
        let mut remaining_value = value;
        let mut introductions = Vec::new();
        let mut has_pi = false;

        // Both modes use the same Pi/Lam/LET formation rules here.
        // All premises and residual conversion still run in the live mode,
        // including its elimination restrictions and proof irrelevance.
        if matches!(self.mode(), CleanMode::Constructive | CleanMode::Classical) && !self.cumulative
        {
            while matches!(
                (remaining_type.kind(), remaining_value.kind()),
                (ExprKind::Pi(..), ExprKind::Lam(..)) | (ExprKind::Let(..), ExprKind::Let(..))
            ) {
                let common = self.metered_scoped_operation(|| {
                    match (remaining_type.kind(), remaining_value.kind()) {
                        (ExprKind::Pi(tb, td, t), ExprKind::Lam(vb, vd, v))
                            if tb == vb && td == vd =>
                        {
                            Some((Introduction::Pi(*tb, td), t.as_ref(), v.as_ref()))
                        }
                        (ExprKind::Let(tn, td, tr, t, tf), ExprKind::Let(vn, vd, vr, v, vf))
                            if tn == vn && tf == vf && td == vd && tr == vr =>
                        {
                            Some((Introduction::Let(tn, td, tr), t.as_ref(), v.as_ref()))
                        }
                        _ => None,
                    }
                })?;
                let Some((introduction, next_type, next_value)) = common else {
                    break;
                };
                has_pi |= matches!(introduction, Introduction::Pi(..));
                introductions.push(introduction);
                remaining_type = next_type;
                remaining_value = next_value;
            }
        }

        if !has_pi {
            let (_, formed) = self.infer_sort_with_formation(expected)?;
            return Ok((expected.clone(), value, Vec::new(), formed));
        }

        let outer = self.ctx_len();
        let mut locals = Vec::with_capacity(introductions.len());
        let mut domains = Vec::new();
        for introduction in introductions {
            let id = match introduction {
                Introduction::Pi(binder, domain) => {
                    let domain = self.open_scoped_introduction(domain, &locals)?;
                    domains.push(self.strict_scoped_sort(&domain)?);
                    self.ctx_push(Name::anon(), domain, binder)
                }
                Introduction::Let(name, domain, rhs) => {
                    let domain = self.open_scoped_introduction(domain, &locals)?;
                    let _sort = self.strict_scoped_sort(&domain)?;
                    let rhs = self.open_scoped_introduction(rhs, &locals)?;
                    self.check_type(&rhs, &domain)?;
                    self.ctx_push_let(name.clone(), domain, rhs)
                }
            };
            locals.push(Expr::fvar(id));
        }
        let opened_type = self.open_scoped_introduction(remaining_type, &locals)?;
        let inferred = self.infer_type_full(&opened_type)?;
        let ExprKind::Sort(level) = inferred.kind() else {
            // The ordinary Pi rule pops its binder before reducing the
            // inferred codomain type. In particular a recursor can reduce
            // using a live proof local that will be unavailable after pop.
            // Keep that ordinary judgment for every residual needing WHNF.
            self.ctx_truncate_to(outer);
            let (_, formed) = self.infer_sort_with_formation(expected)?;
            return Ok((expected.clone(), value, Vec::new(), formed));
        };
        // A syntactic Sort cannot mention an expression local. LET levels
        // therefore survive zeta, and Pi levels combine using ordinary imax.
        let _sort = self.metered_scoped_operation(|| {
            domains
                .into_iter()
                .rev()
                .fold(level.clone(), |body, domain| self.level_imax(domain, body))
        })?;
        Ok((opened_type, remaining_value, locals, true))
    }

    fn open_scoped_introduction(&self, term: &Expr, locals: &[Expr]) -> Result<Expr, TypeError> {
        self.metered_scoped_operation(|| {
            charge(Walk::Fold, locals.len() as u64);
            let arguments: Vec<_> = locals.iter().rev().cloned().collect();
            term.instantiate_rev(&arguments)
        })
    }

    fn strict_scoped_sort(&self, term: &Expr) -> Result<Level, TypeError> {
        let inferred = self.infer_type_full(term)?;
        let previous = self.infer_only.replace(false);
        let sort = self.whnf(&inferred);
        self.infer_only.set(previous);
        match sort.kind() {
            ExprKind::Sort(level) => Ok(level.clone()),
            _ => Err(TypeError::ExpectedSort {
                ty: Box::new(inferred),
                location: self.expr_loc_snapshot(),
            }),
        }
    }
}

#[cfg(test)]
#[path = "scoped_introductions_tests.rs"]
mod tests;
