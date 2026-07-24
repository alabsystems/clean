// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Component A, Step (1): the combined STRICT product
//! monotonicity lemma over nonneg `Rat`.
//!
//! # Why this module exists
//!
//! `NNReal.mul`'s multiplicative `Quot.lift` respect proof reduces (via
//! `NNReal.IsCauchy_mul`) to the nonneg, two-sided-strict product estimate
//!
//! ```text
//! 0 ≤ a, a < b, 0 ≤ c, c < d  ⟹  a·c < b·d
//! ```
//!
//! Only the ONE-sided strict `Rat.mul_lt_mul_of_pos_left` and the non-strict
//! `Rat.mul_le_mul_of_nonneg_left/right` exist on main. This module composes
//! them into the BOTH-factors lemma:
//!
//! - `Rat.mul_lt_mul : ∀ a b c d, Rat.le 0 a → Rat.lt a b → Rat.le 0 c →
//!       Rat.lt c d → Rat.lt (a·c) (b·d)`
//!
//! # Proof shape (no subtraction, nonneg-friendly)
//!
//! 1. `c ≤ d`  from `c < d`  (the `And.left ∘ Iff.mp Rat.lt_iff_le_not_le`
//!    bridge — inlined, no standalone `Rat.le_of_lt` on main).
//! 2. `step1 : a·c ≤ a·d`  from `Rat.mul_le_mul_of_nonneg_left a c d (c≤d)(0≤a)`.
//! 3. `0 < d`  from `Rat.lt_of_le_of_lt 0 c d (0≤c)(c<d)`.
//! 4. `Rat.mul_lt_mul_of_pos_left d a b (a<b)(0<d) : d·a < d·b`, then commute
//!    both endpoints via `Rat.mul_comm` (two `Eq.subst`s) to `step2 : a·d < b·d`.
//! 5. `Rat.lt_of_le_of_lt (a·c)(a·d)(b·d) step1 step2 : a·c < b·d`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `Rat.mul_lt_mul`.
pub(crate) struct MulStrictConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul: Expr,
    rat_mul_comm: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_mul_le_left: Expr,
    rat_mul_lt_pos_left: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
    eq_subst: Expr,
}

impl MulStrictConsts {
    pub(crate) fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul: k("Rat.mul"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_mul_lt_pos_left: k("Rat.mul_lt_mul_of_pos_left"),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![lvl1]),
        }
    }

    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.rat_zero.clone(), a)
    }
    /// `Rat.mul_comm a b : Eq Rat (a·b) (b·a)`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : a < c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.mul_lt_mul_of_pos_left a b c (b<c)(0<a) : a·b < a·c`.
    fn mul_lt_pos_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.rat_mul_lt_pos_left.clone(), [a, b, cc, hbc, ha])
    }
    /// From `hlt : Rat.lt a b`, extract `Rat.le a b` via
    /// `And.left (Iff.mp (Rat.lt_iff_le_not_le a b) hlt)`.
    fn le_of_lt(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.le(a.clone(), b.clone());
        let not_le_ba = Expr::app(self.not_c.clone(), self.le(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le_ba.clone()]);
        let lt_ab = self.lt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le_ba, mp])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
}

impl Environment {
    /// Register `Rat.mul_lt_mul`. Idempotent.
    ///
    /// Depends on `Rat.mul_le_mul_of_nonneg_left` (B1 toolkit),
    /// `Rat.mul_lt_mul_of_pos_left` (B1b), `Rat.lt_of_le_of_lt` +
    /// `Rat.lt_iff_le_not_le` (B1c/B1b), and `Rat.mul_comm`.
    pub fn init_algebra_rat_mul_strict(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left
        self.init_boolean_analysis_order_toolkit_b1b()?; // mul_lt_mul_of_pos_left, lt_iff
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.init_iff()?; // Iff.mp
        self.init_and()?; // And, And.left

        let c = MulStrictConsts::new();
        self.register_rat_mul_lt_mul(&c)
    }

    /// `Rat.mul_lt_mul : ∀ a b c d, Rat.le 0 a → Rat.lt a b → Rat.le 0 c →
    ///     Rat.lt c d → Rat.lt (a·c) (b·d)`.
    fn register_rat_mul_lt_mul(&mut self, c: &MulStrictConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_lt_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let (dv_id, dv) = b.fresh_local(c.rat.clone());
            let h0a = c.nonneg(a.clone());
            let (h0a_id, _) = b.fresh_local(h0a.clone());
            let hab = c.lt(a.clone(), bv.clone());
            let (hab_id, _) = b.fresh_local(hab.clone());
            let h0c = c.nonneg(cv.clone());
            let (h0c_id, _) = b.fresh_local(h0c.clone());
            let hcd = c.lt(cv.clone(), dv.clone());
            let (hcd_id, _) = b.fresh_local(hcd.clone());
            let concl = c.lt(c.mul(a.clone(), cv.clone()), c.mul(bv.clone(), dv.clone()));
            let e = b.mk_pi(hcd_id, BinderInfo::Default, hcd, concl);
            let e = b.mk_pi(h0c_id, BinderInfo::Default, h0c, e);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab, e);
            let e = b.mk_pi(h0a_id, BinderInfo::Default, h0a, e);
            let e = b.mk_pi(dv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_mul_lt_mul_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the proof term for `Rat.mul_lt_mul`.
fn build_mul_lt_mul_proof(c: &MulStrictConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let (dv_id, dv) = b.fresh_local(c.rat.clone());
    let h0a_ty = c.nonneg(a.clone());
    let (h0a_id, h0a) = b.fresh_local(h0a_ty.clone());
    let hab_ty = c.lt(a.clone(), bv.clone());
    let (hab_id, hab) = b.fresh_local(hab_ty.clone());
    let h0c_ty = c.nonneg(cv.clone());
    let (h0c_id, h0c) = b.fresh_local(h0c_ty.clone());
    let hcd_ty = c.lt(cv.clone(), dv.clone());
    let (hcd_id, hcd) = b.fresh_local(hcd_ty.clone());

    let ac = c.mul(a.clone(), cv.clone());
    let ad = c.mul(a.clone(), dv.clone());
    let bd = c.mul(bv.clone(), dv.clone());

    // 1. c ≤ d.
    let hcd_le = c.le_of_lt(cv.clone(), dv.clone(), hcd.clone());
    // 2. step1 : a·c ≤ a·d.
    let step1 = c.mul_le_left(a.clone(), cv.clone(), dv.clone(), hcd_le, h0a);
    // 3. 0 < d  via lt_of_le_of_lt 0 c d (0≤c)(c<d).
    let h0d = c.lt_of_le_of_lt(c.rat_zero.clone(), cv.clone(), dv.clone(), h0c, hcd);
    // 4. mul_lt_pos_left d a b (a<b)(0<d) : d·a < d·b.
    let da_lt_db = c.mul_lt_pos_left(dv.clone(), a.clone(), bv.clone(), hab, h0d);
    let da = c.mul(dv.clone(), a.clone());
    let db = c.mul(dv.clone(), bv.clone());
    // commute LHS: d·a = a·d  (Rat.mul_comm d a).
    let comm_da = c.mul_comm(dv.clone(), a.clone());
    // motiveL t := Rat.lt t (d·b)
    let motive_l = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.lt(t, db.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // s1 : a·d < d·b.
    let s1 = c.subst(motive_l, da.clone(), ad.clone(), comm_da, da_lt_db);
    // commute RHS: d·b = b·d  (Rat.mul_comm d b).
    let comm_db = c.mul_comm(dv.clone(), bv.clone());
    // motiveR t := Rat.lt (a·d) t
    let motive_r = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.lt(ad.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // step2 : a·d < b·d.
    let step2 = c.subst(motive_r, db.clone(), bd.clone(), comm_db, s1);

    // 5. lt_of_le_of_lt (a·c)(a·d)(b·d) step1 step2 : a·c < b·d.
    let proof = c.lt_of_le_of_lt(ac, ad, bd, step1, step2);

    let e = b.mk_lam(hcd_id, BinderInfo::Default, hcd_ty, proof);
    let e = b.mk_lam(h0c_id, BinderInfo::Default, h0c_ty, e);
    let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, e);
    let e = b.mk_lam(h0a_id, BinderInfo::Default, h0a_ty, e);
    let e = b.mk_lam(dv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_mul_strict()
            .expect("init_algebra_rat_mul_strict");
        env.init_algebra_rat_mul_strict().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_mul_lt_mul_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("Rat.mul_lt_mul");
        let info = env.get_const(&nm).expect("Rat.mul_lt_mul registered");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.mul_lt_mul must kernel-check");
    }

    #[test]
    fn test_rat_mul_lt_mul_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.mul_lt_mul");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
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
