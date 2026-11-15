// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Context-independent FAST type-only memo entries for closed applicative data.
//!
//! This is a structural prerequisite, not a declaration/proof certificate.
//! Unknown/lazy environment records or callback ownership retain exact-prefix
//! inference. An independent App requires both children already admitted in the
//! same checking mode; eviction merely prevents admission. No binder, extension
//! or inference-only argument is granted a missing derivation by this route.
use super::{infer_arc_memo::InferArcMemoKey, TypeChecker};
use crate::{Expr, ExprKind};
use std::sync::Arc;

fn screened(expr: &Expr) -> bool {
    crate::work_meter::charge(crate::work_meter::Walk::Probe, 1);
    closed(expr)
}

fn closed(expr: &Expr) -> bool {
    !expr.has_fvar_quick()
        && !expr.has_loose_bvars_quick()
        && !expr.has_expr_mvar_quick()
        && !expr.has_level_mvar_quick()
}

impl TypeChecker<'_> {
    fn independent_environment(&self) -> bool {
        if let Some(known) = self.independent_infer_environment.get() {
            return known;
        }
        let env = self.env;
        // Native callbacks require installation custody from the existing
        // builtin owner; names, addresses and serialized data confer none.
        // Visit each screened inventory completely, so work charges do not
        // depend on randomized map iteration when a record refuses.
        let known = !env.has_constant_source()
            && env.has_only_owned_native_reducers()
            && env
                .constants()
                .map(|c| screened(&c.type_) & c.value.as_ref().is_none_or(screened))
                .fold(true, |known, current| known & current)
            && env
                .inductives()
                .map(|i| screened(&i.type_))
                .fold(true, |a, b| a & b)
            && env
                .constructors()
                .map(|c| screened(&c.type_))
                .fold(true, |a, b| a & b)
            && env
                .quotients()
                .map(|q| screened(&q.type_))
                .fold(true, |a, b| a & b)
            && env
                .recursors()
                .map(|r| {
                    screened(&r.type_)
                        & r.rules
                            .iter()
                            .map(|rule| screened(&rule.rhs))
                            .fold(true, |a, b| a & b)
                })
                .fold(true, |a, b| a & b);
        self.independent_infer_environment.set(Some(known));
        known
    }

    pub(super) fn independent_infer_key(&self, arc: &Arc<Expr>) -> Option<InferArcMemoKey> {
        // Preserve the established empty-context namespace and its genuine
        // type-only -> certificate promotion. Independent entries serve only
        // the repeated nonempty binder prefixes this optimization addresses.
        if self.ctx.borrow().is_empty()
            || !closed(arc)
            || self.level_eq_override.is_some()
            || !self.independent_environment()
        {
            return None;
        }
        match arc.kind() {
            ExprKind::Const(..) | ExprKind::Sort(..) | ExprKind::Lit(..) | ExprKind::App(..) => {
                Some(InferArcMemoKey::independent(arc, self.infer_only.get()))
            }
            _ => None,
        }
    }

    pub(super) fn independent_infer_admissible(&self, arc: &Arc<Expr>, ty: &Expr) -> bool {
        if !closed(ty) {
            return false;
        }
        match arc.kind() {
            ExprKind::Const(..) | ExprKind::Sort(..) | ExprKind::Lit(..) => true,
            ExprKind::App(f, a) => {
                let memo = self.infer_arc_memo.borrow();
                let mode = self.infer_only.get();
                memo.get(&InferArcMemoKey::independent(f, mode)).is_some()
                    && memo.get(&InferArcMemoKey::independent(a, mode)).is_some()
            }
            _ => false,
        }
    }
}

#[cfg(test)]
#[path = "infer_closed_data_tests.rs"]
mod tests;
