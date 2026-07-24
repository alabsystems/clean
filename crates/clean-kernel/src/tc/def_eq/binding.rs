// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

impl<'env> TypeChecker<'env> {
    /// Compare two binding expressions by iteratively processing consecutive
    /// same-kind binders.
    pub(in crate::tc::def_eq) fn is_def_eq_binding(&self, a: &Expr, b: &Expr) -> bool {
        let save_len = self.ctx_len();
        let binder_disc = std::mem::discriminant(a.kind());
        let mut a = a.clone();
        let mut b = b.clone();

        loop {
            let (ty1, body1) = match a.kind() {
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    (ty.as_ref(), body.as_ref())
                }
                _ => unreachable!("is_def_eq_binding: lhs is not Lam/Pi"),
            };
            let (bi2, ty2, body2) = match b.kind() {
                ExprKind::Lam(bi, ty, body) | ExprKind::Pi(bi, ty, body) => {
                    (*bi, ty.as_ref(), body.as_ref())
                }
                _ => unreachable!("is_def_eq_binding: rhs is not Lam/Pi"),
            };

            // Syntactic pre-check: skip full def_eq comparison when domains
            // are structurally identical. This is a pure optimization — structurally
            // equal types are always definitionally equal. Avoids expensive WHNF
            // and cache overhead for the common case of identical binder domains
            // (e.g., `(n : Nat) → ...` vs `(n : Nat) → ...`).
            // Part of #3230.
            if ty1 != ty2 && !self.is_def_eq_impl(ty1, ty2) {
                self.ctx_truncate_to(save_len);
                return false;
            }

            if !body1.has_loose_bvars() && !body2.has_loose_bvars() {
                let result = self.is_def_eq_impl(body1, body2);
                self.ctx_truncate_to(save_len);
                return result;
            }

            let local_id = self.ctx_push(Name::anon(), ty2.clone(), bi2);
            let a_next = self.open_bvar(body1, local_id);
            let b_next = self.open_bvar(body2, local_id);
            if std::mem::discriminant(a_next.kind()) == binder_disc
                && std::mem::discriminant(b_next.kind()) == binder_disc
            {
                a = a_next;
                b = b_next;
                continue;
            }

            let result = self.is_def_eq_impl(&a_next, &b_next);
            self.ctx_truncate_to(save_len);
            return result;
        }
    }
}
