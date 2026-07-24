// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — **RUNG 4b** (`rung4-sqrtbound`): the perfect-square sqrt UPPER
//! bound `√(δ·δ) ≤ ofRat δ`.
//!
//! To reflect the analytic aggregate (`Σ W_norm ≤ 4·√ε·I[f]`, in `NNReal`) back
//! into the `Rat` `Var`/`I[f]` ledger we instantiate `ε := δ·δ` (a perfect
//! square) and need `NNReal.sqrtRat (δ·δ) ≤ NNReal.ofRat δ`. THIS lands that
//! one-sided bound.
//!
//! ## What this registers (constructive, EMPTY admitted-axiom closure)
//!
//! ```text
//! NNReal.sqrtRat_sq_le_ofRat :
//!   ∀ (d : Rat) (hd : Rat.le Rat.zero d)
//!     (hdd0 : Rat.le Rat.zero (Rat.mul d d))
//!     (hdd1 : Rat.lt (Rat.mul d d) Rat.one),
//!     NNReal.le (NNReal.sqrtRat (Rat.mul d d)) (NNReal.ofRat d hd)
//! ```
//!
//! Proof, by `NNReal.le_of_sq_le_sq (sqrtRat (d·d)) (ofRat d hd) hsq`, where
//! `hsq : NNReal.le (mul (sqrtRat (d·d))(sqrtRat (d·d))) (mul (ofRat d hd)(ofRat d hd))`
//! is `Eq.subst` of `NNReal.le.refl` along the EQUALITY of the two squares:
//! - `s1 : mul (sqrtRat (d·d))(sqrtRat (d·d)) = ofRat (d·d) hdd0`
//!     (`NNReal.sqrtRat_mul_self (d·d) hdd0 hdd1`),
//! - `s2 : mul (ofRat d hd)(ofRat d hd) = ofRat (Rat.mul d d) hdd0`
//!     (`NNReal.ofRat_mul d d hd hd hdd0` — the SAME `hdd0` proof field, so the
//!      two RHS are byte-identical `ofRat (d·d) hdd0`),
//!
//! so `eq : mul (ofRat d)(ofRat d) = mul (sqrtRat (d·d))(sqrtRat (d·d))`
//! (`Eq.trans s2 (Eq.symm s1)`), and
//! `Eq.subst (fun t => NNReal.le t (mul (ofRat d)(ofRat d)))
//! eq (NNReal.le.refl (mul (ofRat d)(ofRat d)))` is the desired `hsq`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct SqrtBoundConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    nnreal: Expr,
    nnreal_le: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt: Expr,
    u1: Level,
}

impl SqrtBoundConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            nnreal: k("NNReal"),
            nnreal_le: k("NNReal.le"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt: k("NNReal.sqrtRat"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nonneg(&self, x: Expr) -> Expr {
        self.rle(self.rat_zero.clone(), x)
    }
    fn nn_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }
    fn nn_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a, b])
    }
    fn of_rat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x, h])
    }
    fn sqrt(&self, x: Expr) -> Expr {
        Expr::app(self.nnreal_sqrt.clone(), x)
    }
    fn eq_symm_nn(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.nnreal.clone(), a, b, h],
        )
    }
    fn eq_trans_nn(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.nnreal.clone(), a, b, cc, h1, h2],
        )
    }
    fn eq_subst_nn(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.nnreal.clone(), motive, a, b, h_eq, h],
        )
    }
}

fn sqrtbound_type(c: &SqrtBoundConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let hd_ty = c.nonneg(d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let dd = c.rmul(d.clone(), d.clone());
    let hdd0_ty = c.nonneg(dd.clone());
    let (hdd0_id, _hdd0) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.rlt(dd.clone(), c.rat_one.clone());
    let (hdd1_id, _hdd1) = b.fresh_local(hdd1_ty.clone());

    let lhs = c.sqrt(dd.clone());
    let rhs = c.of_rat(d.clone(), hd.clone());
    let concl = c.nn_le(lhs, rhs);

    let e = b.mk_pi(hdd1_id, BinderInfo::Default, hdd1_ty, concl);
    let e = b.mk_pi(hdd0_id, BinderInfo::Default, hdd0_ty, e);
    let e = b.mk_pi(hd_id, BinderInfo::Default, hd_ty, e);
    b.finish(b.mk_pi(d_id, BinderInfo::Default, c.rat.clone(), e))
}

fn sqrtbound_value(c: &SqrtBoundConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let hd_ty = c.nonneg(d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let dd = c.rmul(d.clone(), d.clone());
    let hdd0_ty = c.nonneg(dd.clone());
    let (hdd0_id, hdd0) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.rlt(dd.clone(), c.rat_one.clone());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());

    let s = c.sqrt(dd.clone()); // sqrtRat (d·d)
    let z = c.of_rat(d.clone(), hd.clone()); // ofRat d hd
    let s_sq = c.nn_mul(s.clone(), s.clone()); // s·s
    let z_sq = c.nn_mul(z.clone(), z.clone()); // z·z
    let of_dd = c.of_rat(dd.clone(), hdd0.clone()); // ofRat (d·d) hdd0

    // s1 : s·s = ofRat (d·d) hdd0   (sqrtRat_mul_self (d·d) hdd0 hdd1).
    let sqrt_mul_self = Expr::const_(Name::from_string("NNReal.sqrtRat_mul_self"), vec![]);
    let s1 = Expr::apps(sqrt_mul_self, [dd.clone(), hdd0.clone(), hdd1.clone()]);

    // s2 : z·z = ofRat (d·d) hdd0   (ofRat_mul d d hd hd hdd0).
    let ofrat_mul = Expr::const_(Name::from_string("NNReal.ofRat_mul"), vec![]);
    let s2 = Expr::apps(
        ofrat_mul,
        [d.clone(), d.clone(), hd.clone(), hd.clone(), hdd0.clone()],
    );

    // eq : z·z = s·s   (trans s2 (symm s1) : z·z = ofRat(d·d) = s·s).
    let s1_symm = c.eq_symm_nn(s_sq.clone(), of_dd.clone(), s1);
    let eq = c.eq_trans_nn(z_sq.clone(), of_dd.clone(), s_sq.clone(), s2, s1_symm);

    // hsq : NNReal.le (s·s)(z·z)
    //   Eq.subst (fun t => NNReal.le t (z·z)) eq (NNReal.le.refl (z·z)).
    //   (refl : le (z·z)(z·z); transport LHS z·z ↦ s·s along eq.)
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.nnreal.clone());
        let body = c.nn_le(t, z_sq.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let refl_zz = Expr::apps(
        Expr::const_(Name::from_string("NNReal.le.refl"), vec![]),
        [z_sq.clone()],
    );
    let hsq = c.eq_subst_nn(motive, z_sq.clone(), s_sq.clone(), eq, refl_zz);

    // proof : NNReal.le s z   (le_of_sq_le_sq s z hsq).
    let le_of_sq = Expr::const_(Name::from_string("NNReal.le_of_sq_le_sq"), vec![]);
    let proof = Expr::apps(le_of_sq, [s.clone(), z.clone(), hsq]);

    let e = b.mk_lam(hdd1_id, BinderInfo::Default, hdd1_ty, proof);
    let e = b.mk_lam(hdd0_id, BinderInfo::Default, hdd0_ty, e);
    let e = b.mk_lam(hd_id, BinderInfo::Default, hd_ty, e);
    b.finish(b.mk_lam(d_id, BinderInfo::Default, c.rat.clone(), e))
}

impl Environment {
    /// Register `NNReal.sqrtRat_sq_le_ofRat` — **RUNG 4b**: `√(δ·δ) ≤ ofRat δ`.
    /// See module docs. Kernel-checked, `Constructive`, empty admitted-axiom
    /// closure. Idempotent; no axiom added/removed.
    pub fn register_kkl_sqrtrat_sq_le_ofrat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtRat_sq_le_ofRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.le.refl, NNReal.ofRat
        self.init_algebra_nnreal_sqrt_identity()?; // NNReal.sqrtRat_mul_self
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.ofRat_mul
        self.init_algebra_nnreal_reverse_square_sq()?; // NNReal.le_of_sq_le_sq

        let c = SqrtBoundConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: sqrtbound_type(&c),
            value: sqrtbound_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_sqrtrat_sq_le_ofrat_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_sqrtrat_sq_le_ofrat()
            .expect("register_kkl_sqrtrat_sq_le_ofrat");
        let nm = Name::from_string("NNReal.sqrtRat_sq_le_ofRat");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("sqrt bound proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_sqrtbound_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_sqrtrat_sq_le_ofrat().expect("first");
        env.register_kkl_sqrtrat_sq_le_ofrat().expect("idempotent");
    }
}
