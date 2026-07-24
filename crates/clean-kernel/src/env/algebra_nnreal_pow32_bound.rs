// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage C (Component A, rung 4): THE per-coordinate
//! HALF-POWER bound `x^{3/2} ≤ ε^{1/2}·x`.
//!
//! # Why this module exists
//!
//! The `n`-free KKL charge `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]` is assembled from
//! the per-coordinate half-power bound (designs §9.4 target 2):
//!
//! ```text
//!   NNReal.pow32_le_sqrt_eps_mul :
//!     0≤x → x≤ε → ε<1 →
//!       NNReal.le (NNReal.pow32 x h0)
//!                 (NNReal.mul (NNReal.sqrtRat ε)(NNReal.ofRat x h0))
//! ```
//!
//! i.e. `x·√x ≤ √ε·x` (since `pow32 x = ofRat x · √x`).
//!
//! # Proof (DIRECT at the Cauchy carrier — no general `NNReal.mul_le_mul_left`)
//!
//! `NNReal.pow32 x h0 ≡ NNReal.mul (ofRat x h0)(sqrtRat x)`, and both factors are
//! `NNReal.mk = Quot.mk`, so `NNReal.le (pow32 x h0)(mul (sqrtRat ε)(ofRat x h0))`
//! ι-reduces (four `Quot.lift` steps) to
//!
//! ```text
//!   NNReal.CauSeq.le (CauSeq.mul (const(ofRat x))(sqrtSeq x))
//!                    (CauSeq.mul (sqrtSeq ε)(const(ofRat x))).
//! ```
//!
//! Its leaf at `(δ, n)` is (via `NNRat.val_mul` + the `val(NNRat.ofRat·) ≡ x`
//! and `val(dyadicApproxNN · n) ≡ a_n(·)` Subtype defeqs)
//! `x·a_n(x) < a_n(ε)·x + δ`. EVENTUAL domination is IMMEDIATE (witness `N := 0`)
//! from the POINTWISE radicand-monotonicity:
//!   - `a_n(x) ≤ a_n(ε)` (`Rat.dyadicApprox_mono_radicand x ε h0 hxe n`),
//!   - scaled by `x ≥ 0` (`Rat.mul_le_mul_of_nonneg_left`): `x·a_n(x) ≤ x·a_n(ε)`,
//!   - `x·a_n(ε) = a_n(ε)·x` (`Rat.mul_comm`), so `x·a_n(x) ≤ a_n(ε)·x`,
//!   - `< a_n(ε)·x + δ` (`x < x+δ`), closed by `Rat.lt_of_le_of_lt`.
//!
//! The `val_mul` transports move the proof's `x·a_n(x)` / `a_n(ε)·x` endpoints
//! onto the `val(NNRat.mul …)` leaf forms.
//!
//! The `ε<1` hypothesis is carried to match the half-power-consumer API; the
//! domination argument does not consume it (the pointwise mono needs only
//! `0≤x` and `x≤ε`). NO general `NNReal.mul_le_mul_left` / boundedness / δ-choice
//! is invoked — the constant left factor `ofRat x` makes the carrier inequality
//! pointwise.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the half-power bound.
pub(crate) struct Pow32BoundConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_dyadic_approx: Expr,
    rat_dyadic_approx_mono: Expr,
    rat_mul_le_left: Expr,
    rat_mul_comm: Expr,
    rat_lt_of_le_of_lt: Expr,
    rat_add_lt_add_left: Expr,
    rat_add_zero: Expr,
    nat_le: Expr,
    // carrier.
    nnrat: Expr,
    nnrat_val: Expr,
    nnrat_mul: Expr,
    nnrat_of_rat: Expr,
    nnrat_val_mul: Expr,
    nnreal_le: Expr,
    nnreal_pow32: Expr,
    nnreal_mul: Expr,
    nnreal_sqrt: Expr,
    nnreal_of_rat: Expr,
    dyadic_approxnn: Expr,
    causeq_seq: Expr,
    // logic.
    exists_intro: Expr,
    eq_subst1: Expr,
    eq_symm1: Expr,
}

impl Pow32BoundConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            rat_dyadic_approx: k("Rat.dyadicApprox"),
            rat_dyadic_approx_mono: k("Rat.dyadicApprox_mono_radicand"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_lt_of_le_of_lt: k("Rat.lt_of_le_of_lt"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            rat_add_zero: k("Rat.add_zero"),
            nat_le: k("Nat.le"),
            nnrat: k("NNRat"),
            nnrat_val: k("NNRat.val"),
            nnrat_mul: k("NNRat.mul"),
            nnrat_of_rat: k("NNRat.ofRat"),
            nnrat_val_mul: k("NNRat.val_mul"),
            nnreal_le: k("NNReal.le"),
            nnreal_pow32: k("NNReal.pow32"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_sqrt: k("NNReal.sqrtRat"),
            nnreal_of_rat: k("NNReal.ofRat"),
            dyadic_approxnn: k("Rat.dyadicApproxNN"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
        }
    }

    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn radd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Rat.dyadicApprox x n`.
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    /// `NNRat.ofRat x h : NNRat`.
    fn nn_of_rat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnrat_of_rat.clone(), [x.clone(), h.clone()])
    }
    /// `Rat.dyadicApproxNN x n : NNRat` (= `seq (sqrtSeq x) n` defeq).
    fn approxnn(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.dyadic_approxnn.clone(), [x.clone(), n])
    }
    /// `NNRat.val q : Rat`.
    fn val(&self, q: Expr) -> Expr {
        Expr::app(self.nnrat_val.clone(), q)
    }
    /// `NNRat.mul p q : NNRat`.
    fn nnmul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_mul.clone(), [p, q])
    }
    /// `NNRat.val_mul p q : Eq Rat (val (NNRat.mul p q)) (val p · val q)`.
    fn val_mul(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.nnrat_val_mul.clone(), [p, q])
    }
    /// `Rat.dyadicApprox_mono_radicand x y h0 hxy n : Rat.le (approx x n)(approx y n)`.
    fn approx_mono(&self, x: &Expr, y: &Expr, h0: &Expr, hxy: &Expr, n: Expr) -> Expr {
        Expr::apps(
            self.rat_dyadic_approx_mono.clone(),
            [x.clone(), y.clone(), h0.clone(), hxy.clone(), n],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c hbc h0 : Rat.le (a·b)(a·c)`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, hbc, h0])
    }
    /// `Rat.mul_comm a b : Eq Rat (a·b)(b·a)`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.lt_of_le_of_lt a b c hab hbc : a < c`.
    fn lt_of_le_of_lt(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_le_of_lt.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.add_lt_add_left a b c h : (c+a) < (c+b)`.
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
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    /// `t < t + δ` (`add_lt_add_left 0 δ t` + `add_zero` transport).
    fn t_lt_t_add(&self, parent: &EnvDeclBuilder, t: &Expr, eps: &Expr, hpos: Expr) -> Expr {
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
    /// Register `NNReal.pow32_le_sqrt_eps_mul`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_pow32_bound(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_pow32()?; // NNReal.pow32 (+ ofRat, sqrtRat, mul)
        self.init_algebra_nnreal_sqrt_le()?; // Rat.dyadicApprox_mono_radicand
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.CauSeq.le
        self.init_algebra_nnreal_nnrat()?; // NNRat.val_mul
        self.init_exists()?;
        self.init_eq()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_rat_field_inst()?; // Rat.add_zero

        let c = Pow32BoundConsts::new();
        self.register_pow32_le_sqrt_eps_mul(&c)
    }

    /// `NNReal.pow32_le_sqrt_eps_mul`.
    fn register_pow32_le_sqrt_eps_mul(&mut self, c: &Pow32BoundConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.pow32_le_sqrt_eps_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let hxe_ty = c.rle(x.clone(), eps.clone());
            let (hxe_id, _hxe) = b.fresh_local(hxe_ty.clone());
            let he1_ty = c.rlt(eps.clone(), c.rat_one.clone());
            let (he1_id, _he1) = b.fresh_local(he1_ty.clone());

            let pow32 = Expr::apps(c.nnreal_pow32.clone(), [x.clone(), h0.clone()]);
            let sqrt_eps = Expr::app(c.nnreal_sqrt.clone(), eps.clone());
            let of_x = Expr::apps(c.nnreal_of_rat.clone(), [x.clone(), h0.clone()]);
            let rhs = Expr::apps(c.nnreal_mul.clone(), [sqrt_eps, of_x]);
            let concl = Expr::apps(c.nnreal_le.clone(), [pow32, rhs]);

            let e = b.mk_pi(he1_id, BinderInfo::Default, he1_ty, concl);
            let e = b.mk_pi(hxe_id, BinderInfo::Default, hxe_ty, e);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let hxe_ty = c.rle(x.clone(), eps.clone());
            let (hxe_id, hxe) = b.fresh_local(hxe_ty.clone());
            let he1_ty = c.rlt(eps.clone(), c.rat_one.clone());
            let (he1_id, _he1) = b.fresh_local(he1_ty.clone());

            // Body : NNReal.CauSeq.le (mul (const(ofRat x))(sqrtSeq x))
            //                         (mul (sqrtSeq ε)(const(ofRat x))), defeq goal.
            //   fun δ hpos => Exists.intro Nat pred Nat.zero witness.
            let (del_id, del) = b.fresh_local(c.rat.clone());
            let hpos_ty = c.rlt(c.rat_zero.clone(), del.clone());
            let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

            // The leaf seq-value endpoints (the EXACT defeq forms of the CauSeq.le
            // conclusion at index n).
            //   vL n := val(NNRat.mul (ofRat x h0)(approxNN x n)).
            //   vR n := val(NNRat.mul (approxNN ε n)(ofRat x h0)).
            let vl = |n: &Expr| -> Expr {
                c.val(c.nnmul(c.nn_of_rat(&x, &h0), c.approxnn(&x, n.clone())))
            };
            let vr = |n: &Expr| -> Expr {
                c.val(c.nnmul(c.approxnn(&eps, n.clone()), c.nn_of_rat(&x, &h0)))
            };

            // pred N := ∀ n, N≤n → vL n < vR n + δ.
            let pred = |parent: &EnvDeclBuilder| -> Expr {
                let mut pn = EnvDeclBuilder::child_of(parent);
                let (cap_id, cap) = pn.fresh_local(c.nat.clone());
                let inner = {
                    let mut pi = EnvDeclBuilder::child_of(&pn);
                    let (n_id, n) = pi.fresh_local(c.nat.clone());
                    let hle_ty = c.nat_le(cap.clone(), n.clone());
                    let (hle_id, _hle) = pi.fresh_local(hle_ty.clone());
                    let concl = c.rlt(vl(&n), c.radd(vr(&n), del.clone()));
                    let e = pi.mk_pi(hle_id, BinderInfo::Default, hle_ty, concl);
                    let e = pi.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
                    pi.finish_child(e)
                };
                pn.finish_child(pn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            // witness : ∀ n, 0≤n → vL n < vR n + δ.
            let witness = {
                let mut wb = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = wb.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(c.nat_zero.clone(), n.clone());
                let (hle_id, _hle) = wb.fresh_local(hle_ty.clone());

                let ax = c.approx(&x, n.clone()); // a_n(x)
                let ae = c.approx(&eps, n.clone()); // a_n(ε)
                let x_ax = c.rmul(x.clone(), ax.clone()); // x·a_n(x)
                let x_ae = c.rmul(x.clone(), ae.clone()); // x·a_n(ε)
                let ae_x = c.rmul(ae.clone(), x.clone()); // a_n(ε)·x

                // h_mono : a_n(x) ≤ a_n(ε).
                let h_mono = c.approx_mono(&x, &eps, &h0, &hxe, n.clone());
                // h_scaled : x·a_n(x) ≤ x·a_n(ε).
                let h_scaled = c.mul_le_left(x.clone(), ax.clone(), ae.clone(), h_mono, h0.clone());
                // transport RHS x·a_n(ε) → a_n(ε)·x along mul_comm x a_n(ε).
                let h_comm = c.mul_comm(x.clone(), ae.clone()); // x·a_n(ε) = a_n(ε)·x
                let motive_le = {
                    let mut d = EnvDeclBuilder::child_of(&wb);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.rle(x_ax.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                // h_le : x·a_n(x) ≤ a_n(ε)·x.
                let h_le = c.subst(motive_le, x_ae.clone(), ae_x.clone(), h_comm, h_scaled);
                // h_lt : a_n(ε)·x < a_n(ε)·x + δ.
                let h_lt = c.t_lt_t_add(&wb, &ae_x, &del, hpos.clone());
                // core : x·a_n(x) < a_n(ε)·x + δ.
                let ae_x_del = c.radd(ae_x.clone(), del.clone());
                let core =
                    c.lt_of_le_of_lt(x_ax.clone(), ae_x.clone(), ae_x_del.clone(), h_le, h_lt);

                // Transport endpoints to the val(NNRat.mul …) leaf forms.
                //   eq_l : x·a_n(x) = vL n   (symm val_mul; RHS defeq x·a_n(x)).
                let p_l = c.nn_of_rat(&x, &h0);
                let q_l = c.approxnn(&x, n.clone());
                let vl_n = vl(&n);
                let eq_l = c.eq_symm(vl_n.clone(), x_ax.clone(), c.val_mul(p_l, q_l));
                //   eq_r : a_n(ε)·x = vR n.
                let p_r = c.approxnn(&eps, n.clone());
                let q_r = c.nn_of_rat(&x, &h0);
                let vr_n = vr(&n);
                let eq_r = c.eq_symm(vr_n.clone(), ae_x.clone(), c.val_mul(p_r, q_r));

                // step1: rewrite RHS summand a_n(ε)·x → vR n.
                let motive_rhs = {
                    let mut d = EnvDeclBuilder::child_of(&wb);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.rlt(x_ax.clone(), c.radd(t, del.clone()));
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let step1 = c.subst(motive_rhs, ae_x.clone(), vr_n.clone(), eq_r, core);
                // step2: rewrite LHS x·a_n(x) → vL n.
                let motive_lhs = {
                    let mut d = EnvDeclBuilder::child_of(&wb);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.rlt(t, c.radd(vr_n.clone(), del.clone()));
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let body = c.subst(motive_lhs, x_ax.clone(), vl_n.clone(), eq_l, step1);

                let e = wb.mk_lam(hle_id, BinderInfo::Default, hle_ty, body);
                let e = wb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
                wb.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), pred(&b), c.nat_zero.clone(), witness],
            );
            let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
            let e = b.mk_lam(del_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(he1_id, BinderInfo::Default, he1_ty, e);
            let e = b.mk_lam(hxe_id, BinderInfo::Default, hxe_ty, e);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            // Drop the now-unused seq const handle to keep clippy quiet.
            let _ = &c.causeq_seq;
            let _ = &c.nnrat;
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
        env.init_algebra_nnreal_pow32_bound()
            .expect("init_algebra_nnreal_pow32_bound");
        env.init_algebra_nnreal_pow32_bound().expect("idempotent");
        env
    }

    #[test]
    fn test_pow32_bound_kernel_checks() {
        let env = env();
        let nm = Name::from_string("NNReal.pow32_le_sqrt_eps_mul");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.pow32_le_sqrt_eps_mul must kernel-check: {e:?}"));
    }

    #[test]
    fn test_pow32_bound_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.pow32_le_sqrt_eps_mul");
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
