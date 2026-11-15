// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Share the existing WHNF of a definition's first type application.

use super::TypeChecker;
use crate::env::ConstantKind;
use crate::expr::{Expr, ExprKind};
use crate::work_meter::{charge, Walk};

impl TypeChecker<'_> {
    /// A repeated `f A x ...` can reuse `whnf(f A)` when it exposes a lambda.
    /// The declared sort argument is only a scheduling hint: both operations
    /// still use ordinary WHNF and capture-avoiding beta substitution. No type
    /// equality, definition body, or native reduction is accepted from the hint.
    /// Called only after the full application's native/Nat reductions declined.
    pub(super) fn reduce_type_argument_prefix(&self, expression: &Expr) -> Option<Expr> {
        if self.mode.has_cubical_layer() {
            return None;
        }
        let mut head = expression;
        let mut first_application = None;
        let mut reversed: smallvec::SmallVec<[&Expr; 8]> = smallvec::SmallVec::new();
        // Keep classification bounded, including on an uncached hostile spine.
        for _ in 0..8 {
            charge(Walk::Fold, 1);
            match &head.kind {
                ExprKind::App(function, argument) => {
                    first_application = Some(head);
                    reversed.push(argument);
                    head = function;
                }
                ExprKind::Const(name, _) => {
                    if reversed.len() < 2 || self.reducibility_gate_blocks(name) {
                        return None;
                    }
                    let info = self.env.get_const(name)?;
                    if info.kind == ConstantKind::Opaque
                        || info.value.is_none()
                        || self.env.get_native_reducer(name).is_some()
                    {
                        return None;
                    }
                    let ExprKind::Pi(_, domain, _) = &info.type_.kind else {
                        return None;
                    };
                    if !matches!(domain.kind(), ExprKind::Sort(_)) {
                        return None;
                    }
                    let prefix = self.whnf_impl(first_application?);
                    if !prefix.is_lam()
                        || self.heartbeat_exhausted()
                        || self.level_sharing_recorded()
                    {
                        return None;
                    }
                    let remaining: smallvec::SmallVec<[&Expr; 8]> = reversed[..reversed.len() - 1]
                        .iter()
                        .rev()
                        .copied()
                        .collect();
                    let reduced = super::beta::apply_lambdas(&prefix, &remaining);
                    if reduced == *expression || self.native_nat_grind_recursor_stuck(&reduced) {
                        return None;
                    }
                    return Some(reduced);
                }
                _ => return None,
            }
        }
        None
    }
}
