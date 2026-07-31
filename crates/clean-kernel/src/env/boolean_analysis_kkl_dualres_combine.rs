// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3 residual, component **M-Hölder**, the
//! ABSTRACT quadratic combiner.
//!
//! The support-restricted double Cauchy–Schwarz (the M-Hölder content) produces,
//! at the concrete cube instance, the two scalar inequalities
//!
//! ```text
//!   l²  ≤  (4·W)·cnt        (CS-1, after the support mask collapses the count)
//!   W²  ≤  f4·cnt           (CS-2)
//! ```
//!
//! and the §9.6 `h_holder4` target `l⁴ ≤ f4·(16·cnt³)` follows by PURE rational
//! algebra: `l⁴ = (l²)² ≤ ((4W)cnt)² = 16·W²·cnt² ≤ 16·(f4·cnt)·cnt² = f4·(16·cnt³)`.
//! This module isolates that algebra as a standalone, axiom-free lemma over FREE
//! rationals so the cube-level assembly (`deriv_holder_fourth_support`) need only
//! supply the two inequalities and the nonnegativities — keeping all the ring
//! juggling away from the giant `subsetSum` terms.
//!
//! ```text
//! BoolAnalysis.holder_quad_combine :
//!   ∀ (l2 w cnt f4 : Rat),
//!     0 ≤ l2 → 0 ≤ w → 0 ≤ cnt → 0 ≤ f4 →
//!     l2 ≤ (4·w)·cnt →                                   -- h1 (CS-1 shadow)
//!     w·w ≤ f4·cnt →                                     -- h2 (CS-2 shadow)
//!     (l2·l2) ≤ f4·((16·cnt)·(cnt·cnt))
//! ```
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! With `K := (4·w)·cnt`:
//! 1. `sqA : l2·l2 ≤ K·K` — square `h1` (`mul_le_*_of_nonneg` + `le_trans`,
//!    using `0 ≤ l2` and `0 ≤ K = mul_nonneg`).
//! 2. `eqK : K·K = (16·(w·w))·(cnt·cnt)` — `Rat.mul_mul_mul_comm` twice
//!    (`(K)·(K) = ((4w)(4w))·(cnt²)`, then `(4w)(4w) = (4·4)·(w·w) = 16·(w·w)`
//!    via `congrArg` on the GROUND `4·4 = 16`); transport into `sqA` by `Eq.subst`.
//! 3. `sqC : l2·l2 ≤ (16·(f4·cnt))·(cnt·cnt)` — bound `16·(w·w) ≤ 16·(f4·cnt)`
//!    from `h2` (`mul_le_..._left`, `0 ≤ 16`) then right-multiply by `cnt·cnt ≥ 0`
//!    (`sq_nonneg`) and `le_trans`.
//! 4. `eqF : (16·(f4·cnt))·(cnt·cnt) = f4·((16·cnt)·(cnt·cnt))` — a 5-atom
//!    commutative regroup (`mul_comm`/`mul_assoc`/`congrArg`); transport `sqC` by
//!    `Eq.subst` to land the goal.
//!
//! Every leaf (`Rat.mul_nonneg`, `Rat.sq_nonneg`, `Rat.mul_le_mul_of_nonneg_*`,
//! `Rat.le_trans`, `Rat.mul_mul_mul_comm`, `Rat.mul_assoc`, `Rat.mul_comm`,
//! `Rat.le_of_ble_eq_true`, `congrArg`, `Eq.subst/trans/refl`) is `Constructive`
//! with empty admitted-axiom closure, so the combiner is too.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the abstract quadratic combiner.
pub(super) struct CombineConsts {
    o: OrderConsts,
    nat_succ: Expr,
    nat_zero: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    mul_le_left: Expr,
    mul_le_right: Expr,
    le_trans: Expr,
    mmmc: Expr,
    mul_assoc: Expr,
    mul_comm: Expr,
    congr_arg: Expr,
    le_of_ble: Expr,
    bool_true: Expr,
    bool_ty: Expr,
    rat_ble: Expr,
    eq_refl_u1: Expr,
}

impl CombineConsts {
    pub(super) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            o: OrderConsts::new(),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            le_trans: k("Rat.le_trans"),
            mmmc: k("Rat.mul_mul_mul_comm"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            le_of_ble: k("Rat.le_of_ble_eq_true"),
            bool_true: k("Bool.true"),
            bool_ty: k("Bool"),
            rat_ble: k("Rat.ble"),
            eq_refl_u1: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
        }
    }

    pub(super) fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    pub(super) fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    /// `Eq.refl.{1}` const atom (for the ground `4·4 = 16` refl).
    pub(super) fn eq_refl_u1(&self) -> Expr {
        self.eq_refl_u1.clone()
    }
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    pub(super) fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }
    #[cfg(test)]
    pub(super) fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_eq(a, b)
    }
    /// `Rat.mk (Int.ofNat v) 1`.
    pub(super) fn lit(&self, v: u64) -> Expr {
        let mut nk = self.nat_zero.clone();
        for _ in 0..v {
            nk = Expr::app(self.nat_succ.clone(), nk);
        }
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), nk), one_nat],
        )
    }
    pub(super) fn sq_nonneg(&self, t: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), t)
    }
    pub(super) fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    pub(super) fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, h, h0])
    }
    pub(super) fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h, h0])
    }
    pub(super) fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h1, h2])
    }
    pub(super) fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mmmc.clone(), [a, b, cc, d])
    }
    pub(super) fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    pub(super) fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `congrArg @Rat @Rat a₁ a₂ f h : f a₁ = f a₂`.
    pub(super) fn congr_arg(&self, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat(), self.rat(), a1, a2, f, h],
        )
    }
    /// `fun (z : Rat) => z·right` as a congr-motive.
    pub(super) fn lam_mul_right(&self, parent: &EnvDeclBuilder, right: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat());
        let body = self.mul(z, right.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat(), body))
    }
    /// `fun (z : Rat) => left·z` as a congr-motive.
    pub(super) fn lam_mul_left(&self, parent: &EnvDeclBuilder, left: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat());
        let body = self.mul(left.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat(), body))
    }
    /// `fun (z : Rat) => le_concl(z)` substitution motive `l2·l2 ≤ z`.
    pub(super) fn lam_le_rhs(&self, parent: &EnvDeclBuilder, lhs: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat());
        let body = self.le(lhs.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat(), body))
    }
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.o.symm(a, b, h)
    }
    pub(super) fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.o.trans(a, b, cc, h1, h2)
    }
    pub(super) fn subst(&self, motive: Expr, a: Expr, b: Expr, h: Expr, hm: Expr) -> Expr {
        self.o.subst(motive, a, b, h, hm)
    }
    /// `0 ≤ (v : Rat)` via the boolean-order reflection `Rat.le_of_ble_eq_true 0 v rfl`.
    pub(super) fn nonneg_lit(&self, v: u64) -> Expr {
        let lit = self.lit(v);
        let ble = Expr::apps(self.rat_ble.clone(), [self.zero(), lit.clone()]);
        let _ = ble;
        let refl = Expr::apps(
            self.eq_refl_u1.clone(),
            [self.bool_ty.clone(), self.bool_true.clone()],
        );
        Expr::apps(self.le_of_ble.clone(), [self.zero(), lit, refl])
    }
}

impl Environment {
    /// Register `BoolAnalysis.holder_quad_combine` — the abstract rational
    /// quadratic combiner of the support-restricted double Cauchy–Schwarz.
    /// Kernel-checked, `ProofQuality::Constructive`, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_holder_quad_combine(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.holder_quad_combine");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?; // sq_nonneg, mul_le_mul_*
        self.register_rat_order_proofs()?; // le_trans, mul_nonneg
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true
        self.register_rat_mul_mul_mul_comm_theorem()?; // mmmc
        self.register_rat_mul_assoc_proof()?; // mul_assoc
        self.register_rat_mul_comm_proof()?; // mul_comm

        let c = CombineConsts::new();
        let (ty, value) = build_combine(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `BoolAnalysis.holder_quad_combine`.
fn build_combine(c: &CombineConsts) -> (Expr, Expr) {
    // RHS `f4·((16·cnt)·(cnt·cnt))`.
    let target_rhs = |f4: &Expr, cnt: &Expr| -> Expr {
        c.mul(
            f4.clone(),
            c.mul(
                c.mul(c.lit(16), cnt.clone()),
                c.mul(cnt.clone(), cnt.clone()),
            ),
        )
    };
    // K := (4·w)·cnt.
    let kk = |w: &Expr, cnt: &Expr| -> Expr { c.mul(c.mul(c.lit(4), w.clone()), cnt.clone()) };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (l2_id, l2) = b.fresh_local(c.rat());
        let (w_id, w) = b.fresh_local(c.rat());
        let (cnt_id, cnt) = b.fresh_local(c.rat());
        let (f4_id, f4) = b.fresh_local(c.rat());

        let hl2_ty = c.le(c.zero(), l2.clone());
        let hw_ty = c.le(c.zero(), w.clone());
        let hcnt_ty = c.le(c.zero(), cnt.clone());
        let hf4_ty = c.le(c.zero(), f4.clone());
        let h1_ty = c.le(l2.clone(), kk(&w, &cnt));
        let h2_ty = c.le(c.mul(w.clone(), w.clone()), c.mul(f4.clone(), cnt.clone()));
        let concl = c.le(c.mul(l2.clone(), l2.clone()), target_rhs(&f4, &cnt));

        let (h2_id, _) = b.fresh_local(h2_ty.clone());
        let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
        let (h1_id, _) = b.fresh_local(h1_ty.clone());
        let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
        let (hf4_id, _) = b.fresh_local(hf4_ty.clone());
        let e = b.mk_pi(hf4_id, BinderInfo::Default, hf4_ty, e);
        let (hcnt_id, _) = b.fresh_local(hcnt_ty.clone());
        let e = b.mk_pi(hcnt_id, BinderInfo::Default, hcnt_ty, e);
        let (hw_id, _) = b.fresh_local(hw_ty.clone());
        let e = b.mk_pi(hw_id, BinderInfo::Default, hw_ty, e);
        let (hl2_id, _) = b.fresh_local(hl2_ty.clone());
        let e = b.mk_pi(hl2_id, BinderInfo::Default, hl2_ty, e);
        let e = b.mk_pi(f4_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(w_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(l2_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (l2_id, l2) = b.fresh_local(c.rat());
        let (w_id, w) = b.fresh_local(c.rat());
        let (cnt_id, cnt) = b.fresh_local(c.rat());
        let (f4_id, f4) = b.fresh_local(c.rat());

        let hl2_ty = c.le(c.zero(), l2.clone());
        let hw_ty = c.le(c.zero(), w.clone());
        let hcnt_ty = c.le(c.zero(), cnt.clone());
        let hf4_ty = c.le(c.zero(), f4.clone());
        let h1_ty = c.le(l2.clone(), kk(&w, &cnt));
        let h2_ty = c.le(c.mul(w.clone(), w.clone()), c.mul(f4.clone(), cnt.clone()));

        let (hl2_id, h_l2) = b.fresh_local(hl2_ty.clone());
        let (hw_id, h_w) = b.fresh_local(hw_ty.clone());
        let (hcnt_id, h_cnt) = b.fresh_local(hcnt_ty.clone());
        let (hf4_id, _h_f4) = b.fresh_local(hf4_ty.clone());
        let (h1_id, h1) = b.fresh_local(h1_ty.clone());
        let (h2_id, h2) = b.fresh_local(h2_ty.clone());

        let proof = super::boolean_analysis_kkl_dualres_combine_proof::build_combine_proof(
            c,
            &b,
            &l2,
            &w,
            &cnt,
            &f4,
            h_l2,
            h_w,
            h_cnt,
            h1,
            h2,
            &kk,
            &target_rhs,
        );

        let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, proof);
        let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
        let e = b.mk_lam(hf4_id, BinderInfo::Default, hf4_ty, e);
        let e = b.mk_lam(hcnt_id, BinderInfo::Default, hcnt_ty, e);
        let e = b.mk_lam(hw_id, BinderInfo::Default, hw_ty, e);
        let e = b.mk_lam(hl2_id, BinderInfo::Default, hl2_ty, e);
        let e = b.mk_lam(f4_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(w_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(l2_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    pub(super) fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_holder_quad_combine()
            .expect("register_holder_quad_combine");
        env
    }

    #[test]
    pub(super) fn test_combine_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.holder_quad_combine");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty (foundational-only), got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    pub(super) fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_holder_quad_combine().expect("first");
        env.register_holder_quad_combine().expect("idempotent");
    }

    /// THE TARGET-REFUTATION GATE. The combiner is a TRUE implication
    /// (`l⁴ = (l²)² ≤ ((4W)cnt)² = 16W²cnt² ≤ 16(f4 cnt)cnt² = f4·16cnt³`), so
    /// `refute_conjecture` must NOT manufacture a counterexample.
    #[test]
    pub(super) fn test_combine_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.holder_quad_combine"))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the quadratic combiner is a TRUE implication; must NOT refute"
        );
    }
}
