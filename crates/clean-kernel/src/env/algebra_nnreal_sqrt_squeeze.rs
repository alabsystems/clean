// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the two-sided SQUEEZE on the squared dyadic
//! approximation (Stage B3, sqrt run #5, rung 7).
//!
//! # Why this module exists
//!
//! The keystone `NNReal.sqrtRat x · NNReal.sqrtRat x = NNReal.ofRat x` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.6 rung 8b) lifts, after
//! the `NNReal.mul`/`Quot.lift` defeq + the `NNRat.val`/`Subtype` defeqs, to the
//! single dist-free `Equiv` between the pointwise-squared dyadic sequence
//! `n ↦ a_n · a_n` and the constant sequence `n ↦ x`, where
//! `a_n := Rat.dyadicApprox x n = ofNat(k_n) · inv(ofNat 2^n)`.
//!
//! That `Equiv` is exactly the two-sided ε-squeeze proved HERE at the pure
//! `Rat` level (so the identity module only has to transport these facts and
//! discharge `Quot.sound`). The four rungs:
//!
//! - **7a** `Rat.ofNat_two_pow_sq_eq_pow4 : ∀ n, ofNat(2^n)·ofNat(2^n) = 4^n`
//!   (`Nat.rec`); `Rat.zero_lt_dyadicPow4 : ∀ n, 0 < 4^n` (`mul_pos` transport);
//!   `Rat.inv_two_pow_sq_eq_inv_pow4 : ∀ n, inv(2^n)·inv(2^n) = inv(4^n)`
//!   (`mul_inv` + transport); and the SQUARE rewrite
//!   `Rat.dyadicApprox_sq_eq : ∀ x n, a_n·a_n = (ofNat k_n · ofNat k_n)·inv(4^n)`.
//! - **7a-lower** `Rat.dyadicApprox_sq_le : ∀ x, 0≤x → ∀ n, a_n·a_n ≤ x`
//!   (multiply the landed `dyadicNum_sq_le` by `inv(4^n) ≥ 0`, cancel `4^n·inv`).
//! - **7b** `Rat.dyadicApprox_le_one : ∀ x, 0≤x → x<1 → ∀ n, a_n ≤ 1`
//!   (`a_n·a_n ≤ x < 1 = 1·1`, then the landed `Rat.le_of_sq_le_sq`).
//! - **7b-upper** `Rat.x_lt_dyadicApprox_sq_add_three_inv :
//!     ∀ x, 0≤x → x<1 → ∀ n, x < a_n·a_n + (inv(2^n)+inv(2^n)+inv(2^n))`
//!   (divide the landed `dyadicNum_sq_lt_succ` by `4^n`, then EXPAND the square
//!   `(k_n+1)²·inv(4^n) = (a_n + inv(2^n))²` and bound the cross + tail terms by
//!   `a_n ≤ 1`, `inv(2^n) ≤ 1`).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure for every theorem. The two `Nat.rec` bridges are universe-1 `Eq`s
//! over `Rat`. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use crate::env::{EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the squeeze rung.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) struct SqueezeConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_pow4: Expr,
    rat_dyadic_approx: Expr,
    // arithmetic bricks
    rat_mul_one: Expr,
    rat_one_mul: Expr,
    rat_right_distrib: Expr,
    rat_add_natcast_one: Expr,
    rat_mul_lt_pos_left: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_mul_inv: Expr,
    rat_mul_inv_cancel: Expr,
    rat_ofnat_mul: Expr,
    rat_add_sq: Expr,
    // order bricks
    rat_mul_pos: Expr,
    #[cfg(test)]
    rat_mul_nonneg: Expr,
    rat_mul_le_left: Expr,
    rat_mul_le_right: Expr,
    rat_le_of_sq_le_sq: Expr,
    #[cfg(test)]
    rat_le_trans: Expr,
    rat_le_refl: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_lt_of_lt_of_le: Expr,
    rat_add_le_add: Expr,
    #[cfg(test)]
    rat_add_le_add_right: Expr,
    rat_lt_iff_le_not_le: Expr,
    // positivity of two-pow + its ne-zero bridge
    rat_zero_lt_two_pow: Expr,
    rat_ne_zero_of_pos: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    // Eq toolkit (Rat is Sort 1)
    eq1: Expr,
    #[cfg(test)]
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    eq_trans1: Expr,
    congr_arg11: Expr,
    nat_rec_prop: Expr,
    // logic
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl SqueezeConsts {
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
            rat_add: k("Rat.add"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_dyadic_pow4: k("Rat.dyadicPow4"),
            rat_dyadic_approx: k("Rat.dyadicApprox"),
            rat_mul_one: k("Rat.mul_one"),
            rat_one_mul: k("Rat.one_mul"),
            rat_right_distrib: k("Rat.right_distrib"),
            rat_add_natcast_one: k("Rat.add_natCast_one"),
            rat_mul_lt_pos_left: k("Rat.mul_lt_mul_of_pos_left"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_mul_inv: k("Rat.mul_inv"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_add_sq: k("Rat.add_sq"),
            rat_mul_pos: k("Rat.mul_pos"),
            #[cfg(test)]
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_le_of_sq_le_sq: k("Rat.le_of_sq_le_sq"),
            #[cfg(test)]
            rat_le_trans: k("Rat.le_trans"),
            rat_le_refl: k("Rat.le_refl"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            rat_add_le_add: k("Rat.add_le_add"),
            #[cfg(test)]
            rat_add_le_add_right: k("Rat.add_le_add_right"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_zero_lt_two_pow: k("Rat.zero_lt_ofNat_two_pow"),
            rat_ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            rat_zero_lt_inv_two_pow: k("Rat.zero_lt_inv_two_pow"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            #[cfg(test)]
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

    // ── small constructors ──
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
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
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
    fn dnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_num.clone(), [x.clone(), n])
    }
    fn pow4(&self, n: Expr) -> Expr {
        Expr::app(self.rat_dyadic_pow4.clone(), n)
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    /// `ofNat(2^n)`.
    fn two_pow(&self, n: Expr) -> Expr {
        self.ofnat(self.npow2(n))
    }
    /// `inv(ofNat 2^n)`.
    fn inv_two_pow(&self, n: Expr) -> Expr {
        self.inv(self.two_pow(n))
    }
    /// `@Eq Rat a b`.
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    /// `@Eq.refl Rat a`.
    #[cfg(test)]
    fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    /// `@Eq.symm Rat a b h : b = a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@Eq.trans Rat a b c h1 h2 : a = c`.
    fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }
    /// `@congrArg Rat Rat a b f h : f a = f b` for `f : Rat → Rat`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b` (motive : Rat → Prop).
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, c])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, c: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mul_mul_mul_comm.clone(), [a, b, c, d])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    /// `Rat.right_distrib a b c : (a+b)·c = a·c + b·c`.
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_right_distrib.clone(), [a, b, cc])
    }
    /// `Rat.add_natCast_one k : ofNat k + 1 = ofNat(succ k)` for `k : Nat`.
    fn add_natcast_one(&self, k: Expr) -> Expr {
        Expr::app(self.rat_add_natcast_one.clone(), k)
    }
    /// `Rat.mul_lt_mul_of_pos_left a b c (b<c)(0<a) : a·b < a·c`.
    fn mul_lt_pos_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_lt_pos_left.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.ofNat_mul m n : ofNat(m·n) = ofNat m · ofNat n`.
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_mul.clone(), [m, n])
    }
    /// `Rat.mul_inv a b ha hb : inv(a·b) = inv a · inv b`.
    fn mul_inv(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_inv_cancel a h : a·inv a = 1`.
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.add_sq a b : (a+b)·(a+b) = (a·a + (1+1)·(a·b)) + b·b`.
    fn add_sq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add_sq.clone(), [a, b])
    }
    /// `Rat.mul_pos a b (0<a)(0<b) : 0 < a·b`.
    fn mul_pos(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_pos.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_nonneg a b (0≤a)(0≤b) : 0 ≤ a·b`.
    #[cfg(test)]
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (b≤c)(0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_right.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (b≤c)(0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.le_of_sq_le_sq a b (0≤a)(0≤b)(a·a≤b·b) : a ≤ b`.
    fn le_of_sq_le_sq(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, hsq: Expr) -> Expr {
        Expr::apps(self.rat_le_of_sq_le_sq.clone(), [a, b, ha, hb, hsq])
    }
    /// `Rat.le_trans a b c (a≤b)(b≤c) : a ≤ c`.
    #[cfg(test)]
    fn le_trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, c, h1, h2])
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : a < c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, c, h1, h2])
    }
    /// `Rat.lt_of_lt_of_le a b c (a<b)(b≤c) : a < c`.
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, c, h1, h2])
    }
    /// `Rat.add_le_add a b c d (a≤b)(c≤d) : (a+c) ≤ (b+d)`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add.clone(), [a, b, cc, d, h1, h2])
    }
    /// `Rat.add_le_add_right a b c (a≤b) : (a+c) ≤ (b+c)`.
    #[cfg(test)]
    fn add_le_add_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_le_add_right.clone(), [a, b, cc, h])
    }
    /// `a ≤ b` from `a < b`, via `lt_iff_le_not_le` + `And.left`.
    fn le_of_lt_generic(&self, a: Expr, b: Expr, hlt: Expr) -> Expr {
        let le_ab = self.le(a.clone(), b.clone());
        let not_le = Expr::app(self.not_c.clone(), self.le(b.clone(), a.clone()));
        let and_ty = Expr::apps(self.and_c.clone(), [le_ab.clone(), not_le.clone()]);
        let lt_ab = self.lt(a.clone(), b.clone());
        let iff = Expr::apps(self.rat_lt_iff_le_not_le.clone(), [a, b]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt_ab, and_ty, iff, hlt]);
        Expr::apps(self.and_left.clone(), [le_ab, not_le, mp])
    }
    /// `0 ≤ a` from `0 < a`.
    fn le_of_lt(&self, a: Expr, hlt: Expr) -> Expr {
        self.le_of_lt_generic(self.rat_zero.clone(), a, hlt)
    }
    /// `0 ≤ 1` via `le_of_lt_generic 0 1 Rat.zero_lt_one`.
    fn zero_le_one(&self) -> Expr {
        let zlo = Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]);
        self.le_of_lt_generic(self.rat_zero.clone(), self.rat_one.clone(), zlo)
    }
    /// `0 < ofNat(2^n)`.
    fn zero_lt_two_pow(&self, n: Expr) -> Expr {
        Expr::app(self.rat_zero_lt_two_pow.clone(), n)
    }
    /// `0 < inv(ofNat 2^n)`.
    fn zero_lt_inv_two_pow(&self, n: Expr) -> Expr {
        Expr::app(self.rat_zero_lt_inv_two_pow.clone(), n)
    }
    /// `Rat.inv_two_pow_le_one n : inv(ofNat 2^n) ≤ 1`.
    fn inv_two_pow_le_one(&self, n: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.inv_two_pow_le_one"), vec![]),
            n,
        )
    }
    /// `(b = 0 → False)` for `b := ofNat(2^n)` from positivity.
    fn two_pow_ne_zero(&self, n: Expr) -> Expr {
        let b = self.two_pow(n.clone());
        Expr::apps(
            self.rat_ne_zero_of_pos.clone(),
            [b, self.zero_lt_two_pow(n)],
        )
    }
}

mod bridges;
mod lower;
mod upper;

impl Environment {
    /// Register the squeeze rung (7a / 7a-lower / 7b / 7b-upper). Idempotent;
    /// every theorem axiom-free.
    pub fn init_algebra_nnreal_sqrt_squeeze(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_nat()?;
        // a_n, k_n, 4^n.
        self.init_algebra_nnreal_sqrt_seq()?;
        // dyadicNum_sq_le.
        self.init_algebra_nnreal_sqrt_invariant()?;
        // dyadicNum_sq_lt_succ.
        self.init_algebra_nnreal_sqrt_upper()?;
        // inv positivity + the ne_zero bridge.
        self.init_algebra_rat_inv_dyadic_step()?;
        self.init_algebra_rat_inv_dyadic()?; // ne_zero_of_pos, inv_pos
                                             // ofNat_mul, mul_inv, mmmc, inv_le_inv_of_le, one_le_ofNat_two_pow.
        self.register_rat_ofnat_mul()?;
        self.init_algebra_rat_inv_mul()?;
        self.init_algebra_nnreal_sqrt_cauchy()?; // inv_le_inv_of_le, inv_two_pow_le_of_le
        self.init_algebra_rat_archimedean()?; // one_le_ofNat_two_pow
                                              // mul/order toolkit.
        self.register_rat_order_proofs()?; // mul_nonneg, mul_one, mul_pos, lt_iff_le_not_le
        self.init_rat_linear_order()?; // le_trans, le_refl, le_total
        self.register_rat_mul_comm_proof()?; // mul_comm
        self.register_rat_mul_assoc_proof()?; // mul_assoc
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_{left,right}
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt, lt_of_lt_of_le
        self.init_boolean_analysis_order_toolkit_b1d()?; // le_of_sq_le_sq
        self.register_rat_add_le_add()?; // add_le_add
        self.register_rat_add_le_add_right()?;
        self.init_boolean_analysis_ring_identities()?; // add_sq
        self.register_rat_pow_nat()?; // powNat (for dyadicPow4 defeq backers)
        self.init_rat_field_inst()?; // right_distrib, one_mul (field instances)
        self.register_fin_sum_const_one_theorems()?; // add_natCast_one
        self.init_algebra_rat_mul_strict()?; // mul_lt_mul_of_pos_left

        let c = SqueezeConsts::new();
        self.register_ofnat_two_pow_sq_eq_pow4(&c)?;
        self.register_zero_lt_dyadic_pow4(&c)?;
        self.register_inv_two_pow_sq_eq_inv_pow4(&c)?;
        self.register_inv_two_pow_le_one(&c)?;
        self.register_dyadic_approx_sq_eq(&c)?;
        self.register_dyadic_approx_sq_le(&c)?;
        self.register_dyadic_approx_le_one(&c)?;
        self.register_x_lt_dyadic_approx_sq_add(&c)?;
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
        "Rat.ofNat_two_pow_sq_eq_pow4",
        "Rat.zero_lt_dyadicPow4",
        "Rat.inv_two_pow_sq_eq_inv_pow4",
        "Rat.inv_two_pow_le_one",
        "Rat.dyadicApprox_sq_eq",
        "Rat.dyadicApprox_sq_le",
        "Rat.dyadicApprox_le_one",
        "Rat.x_lt_dyadicApprox_sq_add_three_inv",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_squeeze()
            .expect("init_algebra_nnreal_sqrt_squeeze");
        env.init_algebra_nnreal_sqrt_squeeze().expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_squeeze_present_and_kernel_check() {
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
    fn test_sqrt_squeeze_constructive_empty_closure() {
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
