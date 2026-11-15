// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's `isDefEqArgs` postponement of implicit arguments
//! (`Lean/Meta/ExprDefEq.lean:301-359`), narrowed to the one shape the
//! App/App rule otherwise refuses.
//!
//! Lean unifies the arguments of two applications of the same function in two
//! passes: explicit arguments first, then the implicit ones it postponed. The
//! historical rule here pairs the function parts first, so every EARLIER
//! argument is met before a later one, implicit or not. That order loses
//! exactly when an implicit argument is a flex application that is not a
//! Miller pattern and a later argument would have assigned its head:
//!
//! ```text
//! @HEq (?motive ?b ?h) (@Eq.rec ?α ?a ?motive ?x ?b ?h) ?β ?y
//!   =?= @HEq (C b) (@Eq.rec α a (fun b _ => C b) x b e) β y
//! ```
//!
//! met `?motive ?b ?h =?= C b` first, which only decomposes first-order
//! (`?motive ?b =?= C`, "cannot unify a free variable with an application"),
//! where the `Eq.rec` pair assigns `?motive := fun b _ => C b` and the type
//! argument then holds by β (`Mathlib/Logic/Basic.lean :: rec_heq_of_heq`,
//! `eqRec_heq_iff_heq.mpr h`, measured 2026-09-12 and again 2026-09-20).
//!
//! Only that shape is re-ordered, and only after the historical order has
//! failed in a speculative scope: every constraint the historical order
//! solves keeps the solution it had. SOUNDNESS: argument-wise congruence of
//! two applications of the same constant is a sound def-eq rule in any
//! order, a failed attempt is rolled back, and every assignment is re-checked
//! by the kernel in the finished term.

use clean_kernel::{BinderInfo, Expr, ExprKind};

use super::{Unifier, UnifyResult};

impl<'a> Unifier<'a> {
    /// `left` and `right` are applications. When both are spines of the same
    /// constant with the same number of arguments, and a NON-explicit
    /// argument pair that is not the last holds a stuck flex application
    /// ([`Self::is_stuck_flex_app`]): try the historical order first, and on
    /// failure unify the other argument pairs first and the stuck implicit
    /// ones last, instantiated with what the others assigned.
    ///
    /// `None` when the constraint does not have that shape; the caller then
    /// runs the historical rule alone.
    pub(super) fn try_unify_spine_postponing_stuck_implicits(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Option<UnifyResult> {
        let (left_head, right_head) = (left.get_app_fn(), right.get_app_fn());
        let (ExprKind::Const(left_name, _), ExprKind::Const(right_name, _)) =
            (left_head.kind(), right_head.kind())
        else {
            return None;
        };
        if left_name != right_name {
            return None;
        }
        let left_args = left.get_app_args();
        let right_args = right.get_app_args();
        if left_args.len() < 2 || left_args.len() != right_args.len() {
            return None;
        }
        // The cheap test first: nearly every spine has no stuck argument, and
        // the last pair is met last in either order.
        let last = left_args.len() - 1;
        let stuck: Vec<usize> = (0..last)
            .filter(|&i| {
                self.is_stuck_flex_app(left_args[i]) || self.is_stuck_flex_app(right_args[i])
            })
            .collect();
        if stuck.is_empty() {
            return None;
        }
        let infos = self.const_head_binder_infos(left_head, left_args.len())?;
        let postponed: Vec<usize> = stuck
            .into_iter()
            .filter(|&i| {
                infos
                    .get(i)
                    .is_some_and(|info| *info != BinderInfo::Default)
            })
            .collect();
        if postponed.is_empty() {
            return None;
        }
        let (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) = (left.kind(), right.kind()) else {
            return None;
        };

        // The historical order, kept whenever it succeeds.
        self.metas.push_scope();
        let in_order = self.unify_app_app_in_order((left, right), (f1, a1), (f2, a2));
        if matches!(in_order, UnifyResult::Success) {
            self.metas.commit();
            return Some(in_order);
        }
        self.metas.pop_scope();

        // Lean's order for the postponed pairs: everything else first.
        self.metas.push_scope();
        let mut result = self.unify_core(left_head, right_head);
        for i in (0..left_args.len()).filter(|i| !postponed.contains(i)) {
            if !matches!(result, UnifyResult::Success) {
                break;
            }
            result = self.unify_app_args(left_args[i], right_args[i]);
        }
        for &i in &postponed {
            if !matches!(result, UnifyResult::Success) {
                break;
            }
            let l = self.metas.instantiate(left_args[i]);
            let r = self.metas.instantiate(right_args[i]);
            result = self.unify_app_args(&l, &r);
        }
        if matches!(result, UnifyResult::Success) {
            self.metas.commit();
            Some(result)
        } else {
            self.metas.pop_scope();
            // Report the refusal the historical order gave.
            Some(in_order)
        }
    }

    /// Binder kinds of the first `limit` binders of a constant head's type,
    /// read as written (no reduction). Shorter than `limit` when the declared
    /// telescope is; the arguments beyond it count as explicit, as Lean's
    /// `isDefEqArgs` treats arguments beyond `paramInfo`. `None` without a
    /// type checker or when the head does not type.
    fn const_head_binder_infos(&self, head: &Expr, limit: usize) -> Option<Vec<BinderInfo>> {
        let tc_cache = self.tc_cache.borrow();
        let tc = tc_cache.as_ref()?;
        let mut ty = tc.infer_type(head).ok()?;
        let mut infos = Vec::with_capacity(limit);
        while infos.len() < limit {
            let ExprKind::Pi(bi, _, body) = ty.kind() else {
                break;
            };
            infos.push(bi.info);
            let next = body.as_ref().clone();
            ty = next;
        }
        Some(infos)
    }
}
