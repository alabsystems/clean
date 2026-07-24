// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the LOWER half of the cube squeeze (Rung 3 part A).
//!
//! # Why this module exists
//!
//! The cube keystone `NNReal.cbrt x ^ 3 = ofRat x` lifts (after the carrier
//! defeqs) to a two-sided ε-squeeze between the pointwise-CUBED dyadic sequence
//! `n ↦ a_n·a_n·a_n` and the constant `n ↦ x`, where
//! `a_n := Rat.cbrtDyadicApprox x n = ofNat(k_n)·inv(2^n)`.
//!
//! This module lands the LOWER half (`a_n³ ≤ x`) and its scale bridges, mirroring
//! the sqrt layer's `algebra_nnreal_sqrt_squeeze` (lower + bridges). The 8^n vs
//! 4^n / cube vs square difference is the genuinely-new content:
//!
//! - **`Rat.ofNat_two_pow_cube_eq_pow8 : ∀ n, ((ofNat 2^n)·(ofNat 2^n))·(ofNat 2^n)
//!   = cbrtDyadicPow8 n`** (`Nat.rec`; the cube analogue of `ofNat_two_pow_sq_eq_pow4`).
//! - **`Rat.zero_lt_cbrtDyadicPow8 : ∀ n, 0 < 8^n`**.
//! - **`Rat.inv_two_pow_cube_eq_inv_pow8 : ∀ n,
//!   (inv(2^n)·inv(2^n))·inv(2^n) = inv(8^n)`** (two `mul_inv` + transport).
//! - **`Rat.cbrtDyadicApprox_cube_eq : ∀ x n,
//!   a_n·a_n·a_n = ((ofNat k_n·ofNat k_n)·ofNat k_n)·inv(8^n)`** (cube `mmmc` regroup).
//! - **`Rat.cbrtDyadicApprox_cube_le : ∀ x, 0≤x → ∀ n, a_n·a_n·a_n ≤ x`** (divide the
//!   landed `cbrtDyadicNum_cube_le` by `8^n > 0`, cancel `8^n·inv`).
//! - **`Rat.cbrtDyadicApprox_le_one : ∀ x, 0≤x → x<1 → ∀ n, a_n ≤ 1`** (cube floor:
//!   `a_n³ ≤ x < 1`, then `le_of_cube_le` … here via the LANDED `le_of_sq_le_sq`
//!   applied to `a_n·a_n ≤ 1` which follows from `a_n³ ≤ 1` and `a_n ≤ a_n³ + …`?
//!   No — simpler: `a_n³ ≤ x < 1`; since `a_n ≥ 0`, `a_n ≤ 1` follows from the
//!   cube-monotone reverse, but we route through the SQUARE: `a_n·a_n ≤ 1` would
//!   need `a_n³ ≥ a_n²` which fails for `a_n<1`. We instead prove `a_n ≤ 1`
//!   directly from `a_n³ < 1` by `le_of_cube_lt_one` — see the proof note).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure for every theorem. NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the cube squeeze (lower half).
pub(crate) struct CbrtSqueezeConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_cbrt_num: Expr,
    rat_cbrt_pow8: Expr,
    rat_cbrt_approx: Expr,
    rat_mul_one: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_mul_inv: Expr,
    rat_mul_inv_cancel: Expr,
    rat_ofnat_mul: Expr,
    rat_mul_pos: Expr,
    rat_mul_le_right: Expr,
    rat_mul_lt_pos_left: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_ne_zero_of_pos: Expr,
    rat_inv_pos: Expr,
    rat_zero_lt_two_pow: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    // rung 2 / rung 3 order + cube bricks
    rat_add: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_lt_of_lt_of_le: Expr,
    rat_le_trans: Expr,
    rat_le_refl: Expr,
    rat_add_le_add: Expr,
    rat_mul_le_left: Expr,
    rat_zero_lt_one: Expr,
    rat_inv_two_pow_le_one: Expr,
    rat_one_mul: Expr,
    rat_right_distrib: Expr,
    rat_add_natcast_one: Expr,
    rat_add_assoc: Expr,
    // Eq toolkit (Rat is Sort 1)
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    eq_trans1: Expr,
    congr_arg11: Expr,
    nat_rec_prop: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

impl CbrtSqueezeConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let l0 = Level::zero();
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_cbrt_num: k("Rat.cbrtDyadicNum"),
            rat_cbrt_pow8: k("Rat.cbrtDyadicPow8"),
            rat_cbrt_approx: k("Rat.cbrtDyadicApprox"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_mul_inv: k("Rat.mul_inv"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_mul_pos: k("Rat.mul_pos"),
            rat_mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_mul_lt_pos_left: k("Rat.mul_lt_mul_of_pos_left"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            rat_inv_pos: k("Rat.inv_pos"),
            rat_zero_lt_two_pow: k("Rat.zero_lt_ofNat_two_pow"),
            rat_zero_lt_inv_two_pow: k("Rat.zero_lt_inv_two_pow"),
            rat_add: k("Rat.add"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            rat_le_trans: k("Rat.le_trans"),
            rat_le_refl: k("Rat.le_refl"),
            rat_add_le_add: k("Rat.add_le_add"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_inv_two_pow_le_one: k("Rat.inv_two_pow_le_one"),
            rat_one_mul: k("Rat.one_mul"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_add_natcast_one: k("Rat.add_natCast_one"),
            rat_add_assoc: k("Rat.add_assoc"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0]),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn cnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_cbrt_num.clone(), [x.clone(), n])
    }
    fn pow8(&self, n: Expr) -> Expr {
        Expr::app(self.rat_cbrt_pow8.clone(), n)
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_cbrt_approx.clone(), [x.clone(), n])
    }
    fn two_pow(&self, n: Expr) -> Expr {
        self.ofnat(self.npow2(n))
    }
    fn inv_two_pow(&self, n: Expr) -> Expr {
        self.inv(self.two_pow(n))
    }
    /// `(a·a)·a`.
    fn cube(&self, a: Expr) -> Expr {
        let sq = self.mul(a.clone(), a.clone());
        self.mul(sq, a)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn mul_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, c])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    fn mmmc(&self, a: Expr, b: Expr, c: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mul_mul_mul_comm.clone(), [a, b, c, d])
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_mul.clone(), [m, n])
    }
    fn mul_inv(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv.clone(), [a, b, ha, hb])
    }
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_pos.clone(), [a, b, ha, hb])
    }
    fn mul_le_right(&self, a: Expr, b: Expr, c: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_right.clone(), [a, b, c, h, h0])
    }
    fn mul_le_left(&self, a: Expr, b: Expr, c: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, c, h, h0])
    }
    /// `Rat.mul_lt_mul_of_pos_left a b c (b<c)(0<a) : a·b < a·c`.
    fn mul_lt_left(&self, a: Expr, b: Expr, c: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_lt_pos_left.clone(), [a, b, c, h, h0])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    fn right_distrib(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_right_distrib.clone(), [a, b, c])
    }
    fn add_natcast_one(&self, k: Expr) -> Expr {
        Expr::app(self.rat_add_natcast_one.clone(), k)
    }
    fn add_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_add_assoc.clone(), [a, b, c])
    }
    fn add_le_add(&self, a: Expr, b: Expr, c: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, c, d, h1, h2])
    }
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, c, h1, h2])
    }
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, c, h1, h2])
    }
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, c, h1, h2])
    }
    fn inv_two_pow_le_one(&self, n: Expr) -> Expr {
        Expr::app(self.rat_inv_two_pow_le_one.clone(), n)
    }
    /// `a ≤ b` from `a < b` (generic): `lt_iff_le_not_le` + `And.left`.
    fn le_of_lt_generic(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.le(a.clone(), b.clone());
        let not_le = Expr::app(self.not_c.clone(), self.le(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le.clone()]);
        let lt_ab = self.lt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le, mp])
    }
    /// `0 ≤ 1` via `le_of_lt_generic 0 1 Rat.zero_lt_one`.
    fn zero_le_one(&self) -> Expr {
        self.le_of_lt_generic(
            self.rat_zero.clone(),
            self.rat_one.clone(),
            self.rat_zero_lt_one.clone(),
        )
    }
    /// `0 ≤ a` from `0 < a` (lt_iff_le_not_le + And.left).
    fn le_of_lt(&self, a: Expr, hlt: Expr) -> Expr {
        let le0a = self.le(self.rat_zero.clone(), a.clone());
        let not_le = Expr::app(
            self.not_c.clone(),
            self.le(a.clone(), self.rat_zero.clone()),
        );
        let and_ty = Expr::apps(self.and_c.clone(), [le0a.clone(), not_le.clone()]);
        let lt0a = self.lt(self.rat_zero.clone(), a.clone());
        let iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [self.rat_zero.clone(), a],
        );
        let mp = Expr::apps(self.iff_mp.clone(), [lt0a, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le0a, not_le, mp])
    }
    fn zero_lt_two_pow(&self, n: Expr) -> Expr {
        Expr::app(self.rat_zero_lt_two_pow.clone(), n)
    }
    fn zero_lt_inv_two_pow(&self, n: Expr) -> Expr {
        Expr::app(self.rat_zero_lt_inv_two_pow.clone(), n)
    }
    fn two_pow_ne_zero(&self, n: Expr) -> Expr {
        let b = self.two_pow(n.clone());
        Expr::apps(
            self.rat_ne_zero_of_pos.clone(),
            [b, self.zero_lt_two_pow(n)],
        )
    }
    /// `0 ≤ inv(8^n)` from `0 < 8^n` (the LANDED `zero_lt_cbrtDyadicPow8`).
    fn zero_le_inv_pow8(&self, n: &Expr) -> Expr {
        let pow8 = self.pow8(n.clone());
        let h_pos = Expr::app(
            Expr::const_(Name::from_string("Rat.zero_lt_cbrtDyadicPow8"), vec![]),
            n.clone(),
        );
        let inv_pos = Expr::apps(self.rat_inv_pos.clone(), [pow8.clone(), h_pos]);
        self.le_of_lt(self.inv(pow8), inv_pos)
    }
    fn pow8_ne_zero(&self, n: &Expr) -> Expr {
        let pow8 = self.pow8(n.clone());
        let h_pos = Expr::app(
            Expr::const_(Name::from_string("Rat.zero_lt_cbrtDyadicPow8"), vec![]),
            n.clone(),
        );
        Expr::apps(self.rat_ne_zero_of_pos.clone(), [pow8, h_pos])
    }
}

mod bridges;
mod lower;
mod upper;

impl Environment {
    /// Register the cube-squeeze lower half + bridges. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_cbrt_squeeze(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_nat()?;
        self.init_algebra_nnreal_cbrt_seq()?; // a_n, k_n, cbrtDyadicNum
        self.init_algebra_nnreal_cbrt_invariant()?; // cbrtDyadicNum_cube_le
        self.init_algebra_nnreal_cbrt_upper()?; // cbrtDyadicNum_cube_lt_succ
        self.init_algebra_rat_inv_dyadic_step()?; // inv positivity
        self.init_algebra_rat_inv_dyadic()?; // ne_zero_of_pos, inv_pos
        self.register_rat_ofnat_mul()?;
        self.init_algebra_rat_inv_mul()?; // mul_inv
        self.register_rat_order_proofs()?; // mul_pos, mul_nonneg, lt_iff_le_not_le
        self.init_rat_linear_order()?; // le_trans, le_refl
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_{left,right}
        self.init_boolean_analysis_order_toolkit_b1b()?; // mul_lt_mul_of_pos_left
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt, lt_of_lt_of_le
        self.register_rat_add_le_add()?; // add_le_add
        self.register_rat_pow_nat()?;
        self.init_rat_field_inst()?; // mul_inv_cancel, one_mul, right_distrib
                                     // rung 2 / rung 3 additions:
        self.init_algebra_rat_cube_identity()?; // add_cube, le_of_cube_le_cube
        self.init_algebra_nnreal_sqrt_squeeze()?; // Rat.inv_two_pow_le_one
        self.register_fin_sum_const_one_theorems()?; // add_natCast_one

        let c = CbrtSqueezeConsts::new();
        self.register_ofnat_two_pow_cube_eq_pow8(&c)?;
        self.register_zero_lt_cbrt_dyadic_pow8(&c)?;
        self.register_inv_two_pow_cube_eq_inv_pow8(&c)?;
        self.register_cbrt_dyadic_approx_cube_eq(&c)?;
        self.register_cbrt_dyadic_approx_cube_le(&c)?;
        self.register_cbrt_dyadic_approx_le_one(&c)?;
        self.register_x_lt_cbrt_dyadic_approx_cube_add(&c)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "Rat.ofNat_two_pow_cube_eq_pow8",
        "Rat.zero_lt_cbrtDyadicPow8",
        "Rat.inv_two_pow_cube_eq_inv_pow8",
        "Rat.cbrtDyadicApprox_cube_eq",
        "Rat.cbrtDyadicApprox_cube_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_squeeze()
            .expect("init_algebra_nnreal_cbrt_squeeze");
        env.init_algebra_nnreal_cbrt_squeeze().expect("idempotent");
        env
    }

    #[test]
    fn test_cbrt_squeeze_lower_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_cbrt_squeeze_lower_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
