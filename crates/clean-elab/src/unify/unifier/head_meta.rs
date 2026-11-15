// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The unifier's WHNF sees an ASSIGNED metavariable at the head of a term.
//!
//! Lean's `whnfCore` reads a metavariable's assignment where it stands at the
//! head of an application or under a projection (`?f a`, `?x.1`) and reduces
//! through it. Clean's [`Unifier::try_whnf`] is the kernel's `whnf`, which
//! treats every elaborator metavariable as an opaque free variable, assigned
//! or not. Within ONE unification a metavariable assigned by an earlier
//! argument therefore stayed opaque in the later ones: unifying `?x < ?y ↔
//! ?x.1 < ?y.1 ∧ …` against `(a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ …` assigned `?x
//! := (a₁, b₁)` in the left operand, and then `?x.1 =?= a₁` in the right one
//! could not reduce `?x.1`. Every structural probe over it failed and was
//! retried through the WHNF fallback, the failures spent the probe budget
//! (`app_heads.rs`, 64; measured 470 on `Mathlib/Order/Basic.lean`'s
//! `Prod.mk_lt_mk` shape), and past the budget the lossy fallback unfolded
//! `LT.lt (?α × ?β) …` away and left `?β` unassigned ("Type mismatch …
//! got ?x < ?y ↔ …", integ/r5 2026-10-16; inherited from origin/main's
//! 99d4246fb, which made the probes run before WHNF).

use clean_kernel::{Expr, ExprKind};

use super::{MetaState, Unifier};

impl Unifier<'_> {
    /// `e` with its metavariables instantiated when its spine head — through
    /// applications, projections and annotations — is an ASSIGNED
    /// metavariable; `None` otherwise (nothing for the head to read).
    pub(super) fn instantiate_assigned_head(&self, e: &Expr) -> Option<Expr> {
        let mut cur = e;
        loop {
            match cur.kind() {
                ExprKind::App(f, _) => cur = f,
                ExprKind::Proj(_, _, s) => cur = s,
                ExprKind::MData(_, inner) => cur = inner,
                ExprKind::FVar(id) => {
                    let assigned = MetaState::from_fvar(*id)
                        .and_then(|meta| self.metas.get(meta))
                        .is_some_and(|var| var.assignment.is_some());
                    return assigned.then(|| self.metas.instantiate(e));
                }
                _ => return None,
            }
        }
    }
}

#[cfg(test)]
#[path = "head_meta_tests.rs"]
mod tests;
