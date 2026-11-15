// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Recognize ordinary constructor-headed weak-head normal forms.

use super::reduction::names;
use super::TypeChecker;
use crate::expr::{Expr, ExprKind};

// Recognition is optional. Long or malformed application spines use the
// original path. Cache hits precede this scan; each visited node on a miss is
// charged to the existing work meter.
const MAX_CONSTRUCTOR_SPINE: usize = 8;

impl TypeChecker<'_> {
    /// A registered constructor with no reduction rule needs neither a cache
    /// entry nor a reduction step. Its fields are deliberately not normalized.
    ///
    /// The current environment supplies constructor identity: spelling a
    /// definition `List.cons` does not make its application a normal form.
    /// Native hooks and Nat's literal/constructor extension retain their
    /// existing reduction path. Cubical modes also retain the complete path
    /// through their additional head-reduction rules.
    pub(super) fn constructor_is_already_whnf(&self, expr: &Expr) -> bool {
        if self.mode.has_cubical_layer() {
            return false;
        }
        let mut head = expr;
        for _ in 0..MAX_CONSTRUCTOR_SPINE {
            crate::work_meter::charge(crate::work_meter::Walk::Fold, 1);
            if let ExprKind::App(function, _) = head.kind() {
                head = function;
            } else {
                return self.constructor_head_is_normal(head);
            }
        }
        false
    }

    fn constructor_head_is_normal(&self, head: &Expr) -> bool {
        let ExprKind::Const(name, _) = head.kind() else {
            return false;
        };
        self.env
            .get_constructor(name)
            .is_some_and(|constructor| constructor.inductive_name != *names::NAT)
            && self
                .env
                .get_const(name)
                .is_some_and(|declaration| declaration.value.is_none())
            && self.env.get_native_reducer(name).is_none()
    }
}
