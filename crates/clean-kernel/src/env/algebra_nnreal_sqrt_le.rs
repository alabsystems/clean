// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage C (Component A, rung 2): `NNReal.sqrtRat`
//! MONOTONE in the radicand.
//!
//! # Why this module exists
//!
//! The half-power charge `x^{3/2} ≤ ε^{1/2}·x` closes cleanly through
//! `sqrtRat x ≤ sqrtRat ε` (designs §9.3/§9.4). This rung lifts the pointwise
//! dyadic-floor monotonicity (`Rat.dyadicNum_mono`, rung 1) to the carrier
//! order `NNReal.le`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.dyadicApprox_mono : ∀ x y, 0≤x → x≤y → ∀ n,
//!       Rat.le (Rat.dyadicApprox x n) (Rat.dyadicApprox y n)`.
//!   `a_n(x) = ofNat(k_n(x))·inv(2^n)`; `k_n(x) ≤ k_n(y)` (rung 1) lifts to
//!   `ofNat(k_n(x)) ≤ ofNat(k_n(y))` (`Rat.ofNat_le_ofNat_of_le`), times the
//!   shared NONNEG factor `inv(2^n) ≥ 0` (`Rat.zero_lt_inv_two_pow` → `≤`), via
//!   `Rat.mul_le_mul_of_nonneg_right`.
//!
//! - `NNReal.sqrtRat_le_sqrtRat : ∀ x y, 0≤x → x≤y → x<1 →
//!       NNReal.le (NNReal.sqrtRat x) (NNReal.sqrtRat y)`.
//!   `NNReal.le (mk(sqrtSeq x))(mk(sqrtSeq y))` ι-reduces (two `Quot.lift`
//!   steps) to `NNReal.CauSeq.le (sqrtSeq x)(sqrtSeq y)`, whose leaf at `(ε, n)`
//!   is (by the `NNRat.val`/`Subtype`/`CauSeq.mk` defeqs) `a_n(x) < a_n(y) + ε`.
//!   EVENTUAL domination is IMMEDIATE from the pointwise `≤`: witness `N := 0`,
//!   and at every `n`, `a_n(x) ≤ a_n(y) < a_n(y) + ε` (`dyadicApprox_mono` +
//!   `x < x+ε`) closes by `Rat.lt_of_le_of_lt`.
//!   The `x < 1` hypothesis is kept to match the half-power-consumer API; the
//!   domination argument does not consume it.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the sqrt-monotone rung.
pub(crate) struct SqrtLeConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    #[cfg(test)]
    rat_mul: Expr,
    rat_add: Expr,
    rat_inv: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_approx: Expr,
    rat_dyadic_num_mono: Expr,
    rat_ofnat_le_ofnat: Expr,
    rat_mul_le_right: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    rat_lt_iff: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_one: Expr,
    and_c: Expr,
    and_left: Expr,
    iff_mp: Expr,
    not_c: Expr,
    // carrier.
    nnreal_le: Expr,
    nnreal_sqrt: Expr,
    // logic.
    exists_intro: Expr,
    // Eq.{1} over Rat (transport).
    eq_subst1: Expr,
}

impl SqrtLeConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_le: k("Nat.le"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            #[cfg(test)]
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            rat_inv: k("Rat.inv"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_dyadic_approx: k("Rat.dyadicApprox"),
            rat_dyadic_num_mono: k("Rat.dyadicNum_mono"),
            rat_ofnat_le_ofnat: k("Rat.ofNat_le_ofNat_of_le"),
            rat_mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_zero_lt_inv_two_pow: k("Rat.zero_lt_inv_two_pow"),
            rat_lt_iff: k("Rat.lt_iff_le_not_le"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_one: k("Rat.one"),
            and_c: k("And"),
            and_left: k("And.left"),
            iff_mp: k("Iff.mp"),
            not_c: k("Not"),
            nnreal_le: k("NNReal.le"),
            nnreal_sqrt: k("NNReal.sqrtRat"),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
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
    #[cfg(test)]
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn dnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_num.clone(), [x.clone(), n])
    }
    /// `Rat.dyadicApprox x n` (= `ofNat(dyadicNum x n) · inv(ofNat 2^n)`).
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    /// The dyadic denominator `inv(ofNat 2^n)`.
    fn den(&self, n: Expr) -> Expr {
        self.inv(self.ofnat(self.npow2(n)))
    }
    /// `Rat.dyadicNum_mono x y h0 hxy n : Nat.le (dyadicNum x n)(dyadicNum y n)`.
    fn dnum_mono(&self, x: &Expr, y: &Expr, h0: &Expr, hxy: &Expr, n: Expr) -> Expr {
        Expr::apps(
            self.rat_dyadic_num_mono.clone(),
            [x.clone(), y.clone(), h0.clone(), hxy.clone(), n],
        )
    }
    /// `Rat.ofNat_le_ofNat_of_le k m h : Rat.le (ofNat k)(ofNat m)`.
    fn ofnat_le(&self, k: Expr, m: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_le_ofnat.clone(), [k, m, h])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c hbc h0 : Rat.le (b·a)(c·a)`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_right.clone(), [a, b, cc, hbc, h0])
    }
    /// `0 ≤ inv(2^n)` from `Rat.zero_lt_inv_two_pow n` via the lt→le idiom.
    fn zero_le_den(&self, n: Expr) -> Expr {
        let den = self.den(n.clone());
        let hpos = Expr::app(self.rat_zero_lt_inv_two_pow.clone(), n);
        let le0d = self.rle(self.rat_zero.clone(), den.clone());
        let not_led0 = Expr::app(
            self.not_c.clone(),
            self.rle(den.clone(), self.rat_zero.clone()),
        );
        let lt0d = self.rlt(self.rat_zero.clone(), den.clone());
        let and_e = Expr::apps(self.and_c.clone(), [le0d.clone(), not_led0.clone()]);
        let iff_e = Expr::apps(self.rat_lt_iff.clone(), [self.rat_zero.clone(), den]);
        let mp = Expr::apps(self.iff_mp.clone(), [lt0d, and_e, iff_e, hpos]);
        Expr::apps(self.and_left.clone(), [le0d, not_led0, mp])
    }
    /// `Rat.lt_of_le_of_lt a b c hab hbc : a < c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)` from `h : a<b`.
    fn add_lt_add_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_add_lt_add_left.clone(), [a, b, cc, h])
    }
    /// `Rat.add_zero a : Eq Rat (a+0) a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a)
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `t < t + ε` from `0 < ε` (`add_lt_add_left 0 ε t` + `add_zero` transport).
    fn t_lt_t_add_eps(&self, parent: &EnvDeclBuilder, t: &Expr, eps: &Expr, hpos: Expr) -> Expr {
        let h = self.add_lt_add_left(self.rat_zero.clone(), eps.clone(), t.clone(), hpos);
        let t_zero = self.radd(t.clone(), self.rat_zero.clone());
        let t_eps = self.radd(t.clone(), eps.clone());
        let e_az = self.add_zero(t.clone());
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = d.fresh_local(self.rat.clone());
            let body = self.rlt(s, t_eps.clone());
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, t_zero, t.clone(), e_az, h)
    }
}

impl Environment {
    /// Register `Rat.dyadicApprox_mono` + `NNReal.sqrtRat_le_sqrtRat`.
    /// Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_le(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_dyadic_mono()?; // Rat.dyadicNum_mono
        self.init_algebra_nnreal_sqrt_seq()?; // Rat.dyadicApprox, Rat.zero_le_dyadicApprox
        self.init_algebra_nnreal_sqrt_def()?; // NNReal.sqrtRat
        self.init_algebra_nnreal_le()?; // NNReal.le
        self.init_exists()?; // Exists.intro
        self.init_eq()?;
        self.register_rat_ofnat_le_ofnat_of_le()?; // Rat.ofNat_le_ofNat_of_le
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right
        self.init_algebra_rat_inv_dyadic_step()?; // Rat.zero_lt_inv_two_pow
        self.init_rat_linear_order()?; // Rat.lt_iff_le_not_le
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_rat_field_inst()?; // Rat.add_zero
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt

        let c = SqrtLeConsts::new();
        self.register_dyadic_approx_mono_radicand(&c)?;
        self.register_sqrt_rat_le_sqrt_rat(&c)
    }

    /// `Rat.dyadicApprox_mono : ∀ x y, 0≤x → x≤y → ∀ n,
    ///   Rat.le (dyadicApprox x n)(dyadicApprox y n)`.
    fn register_dyadic_approx_mono_radicand(&mut self, c: &SqrtLeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_mono_radicand");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let hxy_ty = c.rle(x.clone(), y.clone());
            let (hxy_id, _hxy) = b.fresh_local(hxy_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let body = c.rle(c.approx(&x, n.clone()), c.approx(&y, n.clone()));
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_pi(hxy_id, BinderInfo::Default, hxy_ty, inner);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let hxy_ty = c.rle(x.clone(), y.clone());
            let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let kx = c.dnum(&x, n.clone());
            let ky = c.dnum(&y, n.clone());
            let ofkx = c.ofnat(kx.clone());
            let ofky = c.ofnat(ky.clone());
            let den = c.den(n.clone());
            // hk : Nat.le kx ky.
            let hk = c.dnum_mono(&x, &y, &h0, &hxy, n.clone());
            // hofnat : Rat.le (ofNat kx)(ofNat ky).
            let hofnat = c.ofnat_le(kx.clone(), ky.clone(), hk);
            // hden : 0 ≤ inv(2^n).
            let hden = c.zero_le_den(n.clone());
            // mul_le_mul_of_nonneg_right den (ofNat kx)(ofNat ky) hofnat hden :
            //   Rat.le (ofNat kx · den)(ofNat ky · den) ≡ Rat.le (approx x n)(approx y n).
            let body = c.mul_le_right(den, ofkx, ofky, hofnat, hden);

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(hxy_id, BinderInfo::Default, hxy_ty, e);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.sqrtRat_le_sqrtRat : ∀ x y, 0≤x → x≤y → x<1 →
    ///   NNReal.le (NNReal.sqrtRat x)(NNReal.sqrtRat y)`.
    fn register_sqrt_rat_le_sqrt_rat(&mut self, c: &SqrtLeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtRat_le_sqrtRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let approx_mono = Expr::const_(Name::from_string("Rat.dyadicApprox_mono_radicand"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let hxy_ty = c.rle(x.clone(), y.clone());
            let (hxy_id, _hxy) = b.fresh_local(hxy_ty.clone());
            let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let sx = Expr::app(c.nnreal_sqrt.clone(), x.clone());
            let sy = Expr::app(c.nnreal_sqrt.clone(), y.clone());
            let concl = Expr::apps(c.nnreal_le.clone(), [sx, sy]);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
            let e = b.mk_pi(hxy_id, BinderInfo::Default, hxy_ty, e);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let hxy_ty = c.rle(x.clone(), y.clone());
            let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());
            let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());

            // Body : NNReal.CauSeq.le (sqrtSeq x)(sqrtSeq y), defeq the goal.
            //   fun ε hpos => Exists.intro Nat pred Nat.zero witness.
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.rlt(c.rat_zero.clone(), eps.clone());
            let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

            // pred N := ∀ n, N≤n → a_n(x) < a_n(y) + ε.
            let pred = |parent: &EnvDeclBuilder| -> Expr {
                let mut pn = EnvDeclBuilder::child_of(parent);
                let (cap_id, cap) = pn.fresh_local(c.nat.clone());
                let inner = {
                    let mut pi = EnvDeclBuilder::child_of(&pn);
                    let (n_id, n) = pi.fresh_local(c.nat.clone());
                    let hle_ty = c.nat_le(cap.clone(), n.clone());
                    let (hle_id, _hle) = pi.fresh_local(hle_ty.clone());
                    let ax = c.approx(&x, n.clone());
                    let ay = c.approx(&y, n.clone());
                    let concl = c.rlt(ax, c.radd(ay, eps.clone()));
                    let e = pi.mk_pi(hle_id, BinderInfo::Default, hle_ty, concl);
                    let e = pi.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
                    pi.finish_child(e)
                };
                pn.finish_child(pn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // witness : ∀ n, 0≤n → a_n(x) < a_n(y) + ε.
            let witness = {
                let mut wb = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = wb.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(c.nat_zero.clone(), n.clone());
                let (hle_id, _hle) = wb.fresh_local(hle_ty.clone());
                let ax = c.approx(&x, n.clone());
                let ay = c.approx(&y, n.clone());
                let ay_eps = c.radd(ay.clone(), eps.clone());
                // h_mono : a_n(x) ≤ a_n(y).
                let h_mono = Expr::apps(
                    approx_mono.clone(),
                    [x.clone(), y.clone(), h0.clone(), hxy.clone(), n.clone()],
                );
                // h_ay_lt : a_n(y) < a_n(y) + ε.
                let h_ay_lt = c.t_lt_t_add_eps(&wb, &ay, &eps, hpos.clone());
                // body : a_n(x) < a_n(y) + ε := lt_of_le_of_lt a_n(x) a_n(y) (a_n(y)+ε) h_mono h_ay_lt.
                let body = c.lt_of_le_of_lt(ax, ay, ay_eps, h_mono, h_ay_lt);
                let e = wb.mk_lam(hle_id, BinderInfo::Default, hle_ty, body);
                let e = wb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
                wb.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), pred(&b), c.nat_zero.clone(), witness],
            );
            let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_lam(hxy_id, BinderInfo::Default, hxy_ty, e);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
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

    const THEOREMS: &[&str] = &[
        "Rat.dyadicApprox_mono_radicand",
        "NNReal.sqrtRat_le_sqrtRat",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_le()
            .expect("init_algebra_nnreal_sqrt_le");
        env.init_algebra_nnreal_sqrt_le().expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_le_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_sqrt_le_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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
