// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B3 (3/n): the strict-false reflection brick.
//!
//! # Why this module exists
//!
//! The dyadic-floor UPPER bound `Rat.dyadicNum_sq_lt_succ`
//! (`x · 4^n < (ofNat (k_n + 1))²`, the other side of the squeeze) discharges
//! its FALSE digit branch from `Rat.ble lhs rhs = false`. On main there is
//! `Rat.le_of_ble_eq_true` (the `true` reflection) but NO companion turning a
//! `ble = false` into the strict reverse `Rat.lt rhs lhs`. This module supplies
//! exactly that brick, axiom-free:
//!
//! ```text
//!   Rat.lt_of_ble_eq_false : ∀ a b : Rat, Eq Bool (Rat.ble a b) false → Rat.lt b a
//! ```
//!
//! # Proof (no new axioms; routes only through the constructive order surface)
//!
//! Let `heq : ble a b = false`.
//!
//! 1. `not_le_ab : ¬ (a ≤ b)` — assume `hab : a ≤ b`. Then
//!    `Rat.ble_eq_true_of_le a b hab : ble a b = true`. Compose with `heq` to get
//!    `Eq Bool true false` (`Eq.symm` + `Eq.trans` at universe 1, since
//!    `Bool : Sort 1`), then `@Bool.noConfusion.{0} False true false _ : False`.
//! 2. `tot : Or (b ≤ a) (a ≤ b)` — `Rat.le_total b a`.
//! 3. `hba : b ≤ a` — `@Or.rec` on `tot`: left branch is `b ≤ a` directly; the
//!    right branch `a ≤ b` contradicts `not_le_ab`, closed by `@False.elim`.
//! 4. `Rat.lt b a` — `Iff.mpr (Rat.lt_iff_le_not_le b a) (And.intro hba not_le_ab)`
//!    (the `lt ↔ le ∧ ¬le` engine; `Rat.lt_iff_le_not_le` is now Constructive
//!    since `Int.lt_iff_le_not_le` was upgraded from Axiom to Theorem).
//!
//! All inputs are kernel-checked Constructive theorems / constructors with empty
//! admitted-axiom closure, so `Rat.lt_of_ble_eq_false` is too. NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the strict-false reflection.
pub(crate) struct StrictConsts {
    rat: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    rat_ble: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    bool_false: Expr,
    false_ty: Expr,
    not_c: Expr,
    and_c: Expr,
    or_c: Expr,
    and_intro: Expr,
    or_rec: Expr,
    iff_mpr: Expr,
    false_elim: Expr,
    bool_no_confusion: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    rat_ble_eq_true_of_le: Expr,
    rat_le_total: Expr,
    rat_lt_iff_le_not_le: Expr,
}

impl StrictConsts {
    pub(crate) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_ble: k("Rat.ble"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            false_ty: k("False"),
            not_c: k("Not"),
            and_c: k("And"),
            or_c: k("Or"),
            and_intro: k("And.intro"),
            or_rec: k("Or.rec"),
            iff_mpr: k("Iff.mpr"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]),
            bool_no_confusion: Expr::const_(Name::from_string("Bool.noConfusion"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
            rat_ble_eq_true_of_le: k("Rat.ble_eq_true_of_le"),
            rat_le_total: k("Rat.le_total"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
        }
    }

    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_ble.clone(), [a, b])
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn or(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.or_c.clone(), [p, q])
    }
    /// `Eq.symm.{1} Bool x y h : Eq Bool y x`.
    fn symm_bool(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.bool_ty.clone(), x, y, h])
    }
    /// `Eq.trans.{1} Bool x y z hxy hyz : Eq Bool x z`.
    fn trans_bool(&self, x: Expr, y: Expr, z: Expr, hxy: Expr, hyz: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.bool_ty.clone(), x, y, z, hxy, hyz],
        )
    }
    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), x, y])
    }
}

impl Environment {
    /// Register `Rat.lt_of_ble_eq_false`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_strict(&mut self) -> Result<(), EnvError> {
        self.init_bool()?; // Bool, Bool.noConfusion
        self.init_eq()?; // Eq, Eq.symm, Eq.trans
        self.init_or()?; // Or, Or.rec
        self.init_and()?; // And, And.intro
        self.init_iff()?; // Iff, Iff.mpr
        self.init_true_false()?; // False, False.elim
        self.register_rat_minmax_proofs()?; // Rat.ble, Rat.ble_eq_true_of_le
        self.init_rat_linear_order()?; // Rat.le_total, Rat.lt_iff_le_not_le

        let c = StrictConsts::new();
        self.register_rat_lt_of_ble_eq_false(&c)
    }

    fn register_rat_lt_of_ble_eq_false(&mut self, c: &StrictConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_of_ble_eq_false");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let heq_ty = c.eq_bool(c.ble(a.clone(), bv.clone()), c.bool_false.clone());
            let (heq_id, _heq) = b.fresh_local(heq_ty.clone());
            let concl = c.lt(bv.clone(), a.clone());
            let e = b.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let heq_ty = c.eq_bool(c.ble(a.clone(), bv.clone()), c.bool_false.clone());
            let (heq_id, heq) = b.fresh_local(heq_ty.clone());

            let le_ab = c.le(a.clone(), bv.clone());
            let le_ba = c.le(bv.clone(), a.clone());
            let not_le_ab = c.not_(le_ab.clone());

            // not_le_ab_proof : (a ≤ b) → False.
            let not_le_ab_proof = {
                let mut nb = EnvDeclBuilder::child_of(&b);
                let (hab_id, hab) = nb.fresh_local(le_ab.clone());
                // ble_eq_true_of_le a b hab : ble a b = true
                let ble_true = Expr::apps(
                    c.rat_ble_eq_true_of_le.clone(),
                    [a.clone(), bv.clone(), hab],
                );
                let ble_ab = c.ble(a.clone(), bv.clone());
                // symm : true = ble a b
                let symm = c.symm_bool(ble_ab.clone(), c.bool_true.clone(), ble_true);
                // trans : true = false   (true = ble a b ; ble a b = false)
                let true_eq_false = c.trans_bool(
                    c.bool_true.clone(),
                    ble_ab,
                    c.bool_false.clone(),
                    symm,
                    heq.clone(),
                );
                // @Bool.noConfusion.{0} False true false (true = false) : False
                let false_proof = Expr::apps(
                    c.bool_no_confusion.clone(),
                    [
                        c.false_ty.clone(),
                        c.bool_true.clone(),
                        c.bool_false.clone(),
                        true_eq_false,
                    ],
                );
                let lam = nb.mk_lam(hab_id, BinderInfo::Default, le_ab.clone(), false_proof);
                nb.finish_child(lam)
            };

            // tot : Or (b ≤ a) (a ≤ b)  := Rat.le_total b a
            let tot = Expr::apps(c.rat_le_total.clone(), [bv.clone(), a.clone()]);

            // Or.rec to extract `b ≤ a`:
            //   motive : fun (_ : Or (b≤a)(a≤b)) => Rat.le b a
            let or_motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let or_ty = c.or(le_ba.clone(), le_ab.clone());
                let (z_id, _z) = mb.fresh_local(or_ty.clone());
                mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, or_ty, le_ba.clone()))
            };
            // left : (b ≤ a) → b ≤ a := id
            let left = {
                let mut lb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = lb.fresh_local(le_ba.clone());
                lb.finish_child(lb.mk_lam(h_id, BinderInfo::Default, le_ba.clone(), h))
            };
            // right : (a ≤ b) → b ≤ a := fun h => False.elim (b≤a) (not_le_ab h)
            let right = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = rb.fresh_local(le_ab.clone());
                let false_val = Expr::app(not_le_ab_proof.clone(), h);
                // @False.elim.{0} (Rat.le b a) false_val : Rat.le b a
                let body = Expr::apps(c.false_elim.clone(), [le_ba.clone(), false_val]);
                rb.finish_child(rb.mk_lam(h_id, BinderInfo::Default, le_ab.clone(), body))
            };
            // @Or.rec (b≤a) (a≤b) motive left right tot : b ≤ a
            let hba = Expr::apps(
                c.or_rec.clone(),
                [le_ba.clone(), le_ab.clone(), or_motive, left, right, tot],
            );

            // And.intro (b≤a) (¬a≤b) hba not_le_ab : And (b≤a) (¬a≤b)
            let conj = Expr::apps(
                c.and_intro.clone(),
                [le_ba.clone(), not_le_ab.clone(), hba, not_le_ab_proof],
            );

            // lt_iff : Iff (lt b a) (And (le b a) (¬ le a b))
            let lt_ba = c.lt(bv.clone(), a.clone());
            let and_ty = c.and(le_ba, not_le_ab);
            let iff_e = Expr::apps(c.rat_lt_iff_le_not_le.clone(), [bv.clone(), a.clone()]);
            // Iff.mpr (lt b a) (And ...) iff_e conj : lt b a
            let body = Expr::apps(c.iff_mpr.clone(), [lt_ba, and_ty, iff_e, conj]);

            let e = b.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_strict()
            .expect("init_algebra_nnreal_sqrt_strict");
        env.init_algebra_nnreal_sqrt_strict().expect("idempotent");
        env
    }

    #[test]
    fn test_lt_of_ble_eq_false_kernel_checks() {
        let env = env();
        let nm = Name::from_string("Rat.lt_of_ble_eq_false");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.lt_of_ble_eq_false must kernel-check");
    }

    #[test]
    fn test_lt_of_ble_eq_false_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.lt_of_ble_eq_false");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
