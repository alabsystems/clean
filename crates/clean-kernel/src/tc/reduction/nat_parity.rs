// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed parity recovery through an independently rechecked source equation.
//! No new arithmetic primitive: the result uses admitted shift/add/sub folds.

use super::{names, nat::CLOSED_FOLD_GRIND_STUCK_THRESHOLD};
use crate::expr::{BinderInfo, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;
use std::cell::Cell;
use std::sync::LazyLock;

static PARITY_HEAD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.div2Par"));

thread_local! {
    // Includes every nested checker created by the certification auditor.
    static CHECKING_RECONSTRUCTION: Cell<bool> = const { Cell::new(false) };
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn nat() -> Expr {
    c("Nat")
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn eq(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), a, b],
    )
}
fn trans(a: Expr, b: Expr, z: Expr, h: Expr, k: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), a, b, z, h, k],
    )
}

/// The complete proof checked in tests/half_shift_source.lean, constructed
/// against the actual declarations rather than trusting a theorem's name.
fn reconstruction() -> (Expr, Expr) {
    let n = Expr::bvar(0);
    let half = app("Nat.div2", [n.clone()]);
    let parity = app("Nat.div2Par", [n.clone()]);
    let doubled = app("Nat.add", [half.clone(), half]);
    let joined = app("Nat.add", [doubled.clone(), parity.clone()]);
    let commuted = app("Nat.add", [parity.clone(), doubled.clone()]);
    let h = trans(
        n.clone(),
        joined,
        commuted.clone(),
        app("Nat.div2_rejoin", [n.clone()]),
        app("Nat.add_comm", [doubled.clone(), parity.clone()]),
    );
    let rhs = app("Nat.sub", [n.clone(), doubled.clone()]);
    let middle = app("Nat.sub", [commuted.clone(), doubled.clone()]);
    let function = Expr::lam(
        BinderInfo::Default,
        nat(),
        app("Nat.sub", [Expr::bvar(0), doubled.lift(1)]),
    );
    let congr = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()); 2],
        ),
        [nat(), nat(), n, commuted, function, h],
    );
    let subtract = app("Nat.add_sub_cancel", [parity.clone(), doubled]);
    let equality = trans(rhs.clone(), middle, parity.clone(), congr, subtract);
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), rhs.clone(), parity.clone(), equality],
    );
    (
        Expr::pi(BinderInfo::Default, nat(), eq(parity, rhs)),
        Expr::lam(BinderInfo::Default, nat(), proof),
    )
}

/// Bound all nested audit checkers by the original caller's remaining fuel.
/// The old ambient allowance is restored after subtracting exactly audit work;
/// the caller's own account is charged too, without billing ambient work twice.
struct AuditScope<'a, 'env> {
    tc: &'a TypeChecker<'env>,
    ambient: (u64, u64),
    allowance: u64,
}
impl Drop for AuditScope<'_, '_> {
    fn drop(&mut self) {
        let used = self
            .allowance
            .saturating_sub(crate::tc::declaration_budget_remaining());
        let remaining = if self.ambient.0 == 0 {
            self.ambient.1
        } else {
            self.ambient.1.saturating_sub(used)
        };
        crate::tc::restore_declaration_budget_state(self.ambient.0, remaining);
        if self.tc.heartbeat_limit() != 0 {
            self.tc.heartbeat_counter.set(
                self.tc
                    .heartbeat_counter
                    .get()
                    .saturating_sub(used.min(u64::from(u32::MAX)) as u32),
            );
        }
        CHECKING_RECONSTRUCTION.with(|checking| checking.set(false));
    }
}

impl<'env> TypeChecker<'env> {
    fn certify_parity_equation(&self, goal: &Expr, proof: &Expr) -> bool {
        if CHECKING_RECONSTRUCTION.with(Cell::get) || self.heartbeat_exhausted() {
            return false;
        }
        // The equation certifies a reduction only when its equality is the
        // checked inductive that the kernel uses for propositional equality.
        if self.env.check_equality_premise().is_err() {
            return false;
        }
        let ambient = crate::tc::declaration_budget_state();
        let own = if self.heartbeat_limit() == 0 {
            u64::MAX
        } else {
            u64::from(self.heartbeat_counter.get())
        };
        let allowance = own.min(if ambient.0 == 0 { u64::MAX } else { ambient.1 });
        if allowance == 0 {
            return false;
        }
        CHECKING_RECONSTRUCTION.with(|checking| checking.set(true));
        let _scope = AuditScope {
            tc: self,
            ambient,
            allowance,
        };
        crate::tc::restore_declaration_budget_state(allowance, allowance);
        let audit = self.env.audit_certification(goal, proof);
        // This equation licenses a computational shortcut. Its checked
        // reconstruction from the admitted arithmetic definitions needs no axiom.
        audit.is_certified()
            && audit.foundations.is_empty()
            && !crate::tc::declaration_budget_exhausted()
    }

    pub(in crate::tc) fn reduce_certified_parity(&self, e: &Expr) -> Option<Expr> {
        if CHECKING_RECONSTRUCTION.with(Cell::get)
            || self.kernel_theory() != self.env.kernel_theory()
        {
            return None;
        }
        let ExprKind::App(function, input) = e.kind() else {
            return None;
        };
        let ExprKind::Const(name, levels) = function.kind() else {
            return None;
        };
        if *name != *PARITY_HEAD
            || !levels.is_empty()
            || input.has_fvar_quick()
            || input.has_loose_bvars_quick()
            || input.has_expr_mvar_quick()
            || input.has_level_mvar_quick()
            || ![&names::NAT_SHIFT_RIGHT, &names::NAT_ADD, &names::NAT_SUB]
                .into_iter()
                .all(|head| self.hardwired_fold_admitted(head))
        {
            return None;
        }
        let number = self.get_nat_bignat_whnf_pub(input)?;
        // Avoid certification setup for the ordinary small folds. Once a large
        // call checks the equation, its smaller recursive calls reuse it.
        if !self.parity_reconstruction_verified.get() {
            if number
                .to_u64()
                .is_some_and(|n| n < CLOSED_FOLD_GRIND_STUCK_THRESHOLD)
            {
                return None;
            }
            let (goal, proof) = reconstruction();
            if !self.certify_parity_equation(&goal, &proof) {
                return None;
            }
            self.parity_reconstruction_verified.set(true);
        }
        let input = Expr::from_kind(ExprKind::Lit(Literal::Nat(number)));
        // The parity proof refers to the actual halving definition. Reuse its
        // separately checked universal identity before accepting a shift value.
        let half = self.reduce_unary_shift_alias(&app("Nat.div2", [input.clone()]))?;
        self.reduce_nat(&app(
            "Nat.sub",
            [input, app("Nat.add", [half.clone(), half])],
        ))
    }
}

#[cfg(test)]
#[path = "nat_parity_tests.rs"]
mod tests;
