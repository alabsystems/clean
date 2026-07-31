// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the GENERAL (scale-parameterized) square root on ALL
//! nonneg `Rat`, axiom-free.
//!
//! # Why this module exists (the [0,1)-faithfulness unblock for sqrt)
//!
//! The landed `NNReal.sqrtRat` is faithful ONLY on `[0,1)` — its dyadic floor
//! seeds `k_0 = 0`, so `sqrtRat(x)·sqrtRat(x) ≠ x` for `x ≥ 1` (the carrier
//! saturates below 1). The `(4/3, 4)` tensorization cross-term needs a square
//! root that squares back for an ARBITRARY nonneg argument (e.g. `√(NG·NH)` for a
//! product of finSums, which is `≥ 1` in general), not just on `[0,1)`.
//!
//! THE UNBLOCK: stay inside the faithful range by SCALING. For any `x ≥ 0` the
//! archimedean `Rat.exists_pow_gt` guarantees a `k : Nat` with `4^k > x`, hence
//! the reduced argument `r := x · 4^{-k} ∈ [0,1)`. With `s := 2^k` (so `s² = 4^k`)
//! the square root of `x` is `s · sqrtRat(r)`, and
//!
//! ```text
//!   (s · √r)² = s² · (√r)² = 4^k · r = 4^k · (x · 4^{-k}) = x.
//! ```
//!
//! `√r·√r = ofRat r` is the GENUINE landed `NNReal.sqrtRat_mul_self` (`r ∈ [0,1)`,
//! faithful, a real `Quot.sound`), so the reduction to `[0,1)` is the real
//! content — NOT a refl.
//!
//! This is the EXACT two-square analog of `NNReal.cbrtGen`
//! (`algebra_nnreal_cbrt_gen.rs`): there the abstract scale `s` and reduced arg
//! `r ∈ [0,1)` give `(s · cbrt r)³ = ofRat (((s·s)·s)·r)`; here we square instead
//! of cube, so `(s · √r)² = ofRat ((s·s)·r)`.
//!
//! # The k-dependence (honest)
//!
//! The keystone `NNReal.sqrtGen_sq` is stated over an ABSTRACT scale `s` and
//! reduced arg `r ∈ [0,1)`: `(s · √r)² = ofRat ((s·s)·r)`. The caller picks
//! `s = 2^k` and `r = x·4^{-k}` for whichever valid `k` the archimedean witness
//! supplies; the square identity then reads `ofRat ((s·s)·r) = ofRat (4^k·r) =
//! ofRat x`, the last equality by the reconstruction equation `x = (s·s)·r`.
//! Because the identity is keyed on the equation `x = (s·s)·r` rather than on
//! `k`, well-definedness across different valid `k` is automatic: ANY valid `k`
//! gives the SAME `ofRat x`. The `x`-facing corollary `NNReal.sqrtGen_sq_at`
//! makes this explicit — given any `s, r` with `x = (s·s)·r`, `0 ≤ s`,
//! `r ∈ [0,1)`, `(s·√r)² = ofRat x`. NO `Nat.rec` least-`k` construction is
//! needed (and none is built); the abstract-scale statement subsumes it.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.sqrtGen : (s r : Rat) → (hs : 0 ≤ s) → NNReal`
//!     `:= NNReal.mul (NNReal.ofRat s hs) (NNReal.sqrtRat r)`.
//!   Reducible `Definition`. The scaled square root `s · √r`.
//!
//! - `NNReal.sqrtGen_sq : ∀ (s r : Rat)(hs:0≤s)(hr:0≤r)(hr1:r<1),`
//!     `NNReal.mul (sqrtGen s r hs)(sqrtGen s r hs) = NNReal.ofRat ((s·s)·r) h`.
//!   The keystone (general, axiom-free).
//!
//! - `NNReal.sqrtGen_sq_at : ∀ (x s r : Rat)(hx:0≤x)(hs:0≤s)(hr:0≤r)(hr1:r<1)`
//!     `(heq : x = (s·s)·r),`
//!     `NNReal.mul (sqrtGen s r hs)(sqrtGen s r hs) = NNReal.ofRat x hx`.
//!   The `x`-facing corollary: `(√-of-x)² = x`.
//!
//! `Declaration::Theorem`/`Definition`, `ProofQuality::Constructive`, empty
//! admitted-axiom closure (foundational only). NO `sorry` / `add_decl_unchecked`
//! / `add_decl_structural`. FORBIDDEN here: `NNReal.sqrtRat` applied to a `≥ 1`
//! argument inside a `sq`-style claim (we ONLY ever square `√r` for `r ∈ [0,1)`).
//! FORBIDDEN: any `Real`/`Real.sqrt`/`Rat.dist` import — this IS the constructive
//! sqrt.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the general scaled sqrt.
/// Mirrors `CbrtGenConsts`, with the abstract scale `s` in the `A`-role and the
/// reduced arg `r` in the `C`-role — but SQUARING (`(A·C)·(A·C)`) rather than
/// cubing.
struct SqrtGenConsts {
    nnreal: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul_nonneg: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt: Expr,
    nnreal_sqrt_gen: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_mmm_comm: Expr,
    nnreal_sqrt_mul_self: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
}

impl SqrtGenConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt: k("NNReal.sqrtRat"),
            nnreal_sqrt_gen: k("NNReal.sqrtGen"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_mmm_comm: k("NNReal.mul_mul_mul_comm"),
            nnreal_sqrt_mul_self: k("NNReal.sqrtRat_mul_self"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
        }
    }

    // ── Rat ──────────────────────────────────────────────────────────────────
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn rat_mul_nonneg(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_nonneg.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone()],
        )
    }

    // ── NNReal ───────────────────────────────────────────────────────────────
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    fn sqrt(&self, r: &Expr) -> Expr {
        Expr::app(self.nnreal_sqrt.clone(), r.clone())
    }
    /// `NNReal.sqrtGen s r hs`.
    fn sqrt_gen(&self, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_sqrt_gen.clone(),
            [s.clone(), r.clone(), hs.clone()],
        )
    }

    // ── Eq.{1} plumbing ──────────────────────────────────────────────────────
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn refl_nn(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a.clone()])
    }
    fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                hab,
                hbc,
            ],
        )
    }
    #[cfg(test)]
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }

    /// `NNReal.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn nn_mmm(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mmm_comm.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `NNReal.ofRat_mul a b ha hb hab : mul (ofRat a ha)(ofRat b hb) = ofRat (a·b) hab`.
    fn nn_ofrat_mul(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_mul.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
    /// `NNReal.sqrtRat_mul_self r hr0 hr1 : mul (sqrtRat r)(sqrtRat r) = ofRat r hr0`.
    fn sqrt_mul_self(&self, r: &Expr, hr0: &Expr, hr1: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_sqrt_mul_self.clone(),
            [r.clone(), hr0.clone(), hr1.clone()],
        )
    }
}

impl Environment {
    /// Register `NNReal.sqrtGen`, `NNReal.sqrtGen_sq`, and
    /// `NNReal.sqrtGen_sq_at`. Reuses the landed `NNReal.sqrtRat_mul_self`,
    /// `NNReal.mul_mul_mul_comm`, `NNReal.ofRat_mul`, `Rat.mul_nonneg`.
    /// Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_sqrt_gen(&mut self) -> Result<(), EnvError> {
        // sqrtRat + the keystone identity (pulls NNReal, ofRat, sqrtRat, mul).
        self.init_algebra_nnreal_sqrt_identity()?; // NNReal.sqrtRat_mul_self
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul
        self.init_algebra_nnreal_reverse_square_algebra()?; // ofRat_mul, mul_comm, mul_assoc
        self.init_algebra_nnreal_pow43_cubed()?; // NNReal.mul_mul_mul_comm + Rat.mul_nonneg
        self.init_eq()?;

        let c = SqrtGenConsts::new();
        self.register_sqrt_gen_def(&c)?;
        self.register_sqrt_gen_sq(&c)?;
        self.register_sqrt_gen_sq_at(&c)?;
        Ok(())
    }

    /// `NNReal.sqrtGen : (s r : Rat) → (hs : 0 ≤ s) → NNReal`
    ///   `:= fun s r hs => NNReal.mul (NNReal.ofRat s hs) (NNReal.sqrtRat r)`.
    fn register_sqrt_gen_def(&mut self, c: &SqrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtGen");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (r_id, _r) = b.fresh_local(c.rat.clone());
            let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
            let (hs_id, _hs) = b.fresh_local(hs_ty.clone());
            let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, c.nnreal.clone());
            let e = b.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
            let (hs_id, hs) = b.fresh_local(hs_ty.clone());
            let body = c.nnmul(&c.ofrat(&s, &hs), &c.sqrt(&r));
            let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, body);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.sqrtGen_sq`.
    fn register_sqrt_gen_sq(&mut self, c: &SqrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtGen_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut bd = EnvDeclBuilder::new();
            let (s_id, s) = bd.fresh_local(c.rat.clone());
            let (r_id, r) = bd.fresh_local(c.rat.clone());
            let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
            let (hs_id, hs) = bd.fresh_local(hs_ty.clone());
            let hr_ty = c.rle(c.rat_zero.clone(), r.clone());
            let (hr_id, hr) = bd.fresh_local(hr_ty.clone());
            let hr1_ty = c.rlt(r.clone(), c.rat_one.clone());
            let (hr1_id, _hr1) = bd.fresh_local(hr1_ty.clone());
            let pw = c.sqrt_gen(&s, &r, &hs);
            let lhs = c.nnmul(&pw, &pw);
            let (ssr, hssr) = ss_r_and_proof(c, &s, &r, &hs, &hr);
            let rhs = c.ofrat(&ssr, &hssr);
            let concl = c.eq_nn(&lhs, &rhs);
            let e = bd.mk_pi(hr1_id, BinderInfo::Default, hr1_ty, concl);
            let e = bd.mk_pi(hr_id, BinderInfo::Default, hr_ty, e);
            let e = bd.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
            let e = bd.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
            bd.finish(bd.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_sqrt_gen_sq_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.sqrtGen_sq_at` — the `x`-facing corollary: with the reconstruction
    /// equation `x = (s·s)·r`, the scaled square root squares to `ofRat x`. This
    /// is "general sqrt on all nonneg x": for any `x ≥ 0`, pick `s = 2^k,
    /// r = x·4^{-k}` (k from `Rat.exists_pow_gt`), then `(s·s)·r = 4^k·(x·4^{-k})
    /// = x`.
    fn register_sqrt_gen_sq_at(&mut self, c: &SqrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sqrtGen_sq_at");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut bd = EnvDeclBuilder::new();
            let (x_id, x) = bd.fresh_local(c.rat.clone());
            let (s_id, s) = bd.fresh_local(c.rat.clone());
            let (r_id, r) = bd.fresh_local(c.rat.clone());
            let hx_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (hx_id, hx) = bd.fresh_local(hx_ty.clone());
            let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
            let (hs_id, hs) = bd.fresh_local(hs_ty.clone());
            let hr_ty = c.rle(c.rat_zero.clone(), r.clone());
            let (hr_id, _hr) = bd.fresh_local(hr_ty.clone());
            let hr1_ty = c.rlt(r.clone(), c.rat_one.clone());
            let (hr1_id, _hr1) = bd.fresh_local(hr1_ty.clone());
            let ssr = ss_r(c, &s, &r);
            let heq_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), ssr.clone()]);
            let (heq_id, _heq) = bd.fresh_local(heq_ty.clone());
            let pw = c.sqrt_gen(&s, &r, &hs);
            let lhs = c.nnmul(&pw, &pw);
            let rhs = c.ofrat(&x, &hx);
            let concl = c.eq_nn(&lhs, &rhs);
            let e = bd.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
            let e = bd.mk_pi(hr1_id, BinderInfo::Default, hr1_ty, e);
            let e = bd.mk_pi(hr_id, BinderInfo::Default, hr_ty, e);
            let e = bd.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
            let e = bd.mk_pi(hx_id, BinderInfo::Default, hx_ty, e);
            let e = bd.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = bd.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e);
            bd.finish(bd.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_sqrt_gen_sq_at_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `(s·s)·r` (left-nested) — pure expression form.
fn ss_r(c: &SqrtGenConsts, s: &Expr, r: &Expr) -> Expr {
    let ss = c.rmul(s.clone(), s.clone());
    c.rmul(ss, r.clone())
}

/// `(s·s)·r` (left-nested) and `h : 0 ≤ (s·s)·r` from `0≤s`, `0≤r`.
fn ss_r_and_proof(c: &SqrtGenConsts, s: &Expr, r: &Expr, hs: &Expr, hr: &Expr) -> (Expr, Expr) {
    let ss = c.rmul(s.clone(), s.clone());
    let ssr = c.rmul(ss.clone(), r.clone());
    let h_ss = c.rat_mul_nonneg(s, s, hs, hs);
    let h_ssr = c.rat_mul_nonneg(&ss, r, &h_ss, hr);
    (ssr, h_ssr)
}

/// `a·p = a·q` from `h : p = q` (congruence in the right factor).
fn congr_mul_right(
    c: &SqrtGenConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    p: &Expr,
    q: &Expr,
    h_pq: Expr,
) -> Expr {
    let ap = c.nnmul(a, p);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&ap, &c.nnmul(a, &t));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&ap))
}

/// `p·a = q·a` from `h : p = q` (congruence in the left factor).
fn congr_mul_left(
    c: &SqrtGenConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    a: &Expr,
    h_pq: Expr,
) -> Expr {
    let pa = c.nnmul(p, a);
    let motive = {
        let mut mm = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mm.fresh_local(c.nnreal.clone());
        let body = c.eq_nn(&pa, &c.nnmul(&t, a));
        mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst_nn(motive, p, q, h_pq, c.refl_nn(&pa))
}

/// The full `sqrtGen_sq` proof term.
///
/// `A := ofRat s hs`, `C := √r := sqrtRat r`, `pw := sqrtGen s r hs`
/// (reducible-defeq `mul A C`). The square `(A·C)·(A·C)` regroups (one
/// `mul_mul_mul_comm`) to `(A·A)·(C·C)`, then:
///   * C-square `C·C = ofRat r`   (`NNReal.sqrtRat_mul_self r hr hr1`),
///   * A-square `A·A = ofRat (s·s)` (`NNReal.ofRat_mul s s hs hs`),
///   * combine `(A·A)·(C·C) = ofRat (s·s)·ofRat r = ofRat ((s·s)·r)`.
fn build_sqrt_gen_sq_value(c: &SqrtGenConsts) -> Expr {
    let mut bd = EnvDeclBuilder::new();
    let (s_id, s) = bd.fresh_local(c.rat.clone());
    let (r_id, r) = bd.fresh_local(c.rat.clone());
    let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
    let (hs_id, hs) = bd.fresh_local(hs_ty.clone());
    let hr_ty = c.rle(c.rat_zero.clone(), r.clone());
    let (hr_id, hr) = bd.fresh_local(hr_ty.clone());
    let hr1_ty = c.rlt(r.clone(), c.rat_one.clone());
    let (hr1_id, hr1) = bd.fresh_local(hr1_ty.clone());

    let body = build_sqrt_gen_sq_core(c, &bd, &s, &r, &hs, &hr, &hr1);

    let e = bd.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, body);
    let e = bd.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
    let e = bd.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
    let e = bd.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
    bd.finish(bd.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e))
}

/// The shared square core: a proof of
/// `mul pw pw = ofRat ((s·s)·r) h` where `pw := sqrtGen s r hs`.
/// Reused by both `sqrtGen_sq` and (via a final value-congruence)
/// `sqrtGen_sq_at`.
fn build_sqrt_gen_sq_core(
    c: &SqrtGenConsts,
    bd: &EnvDeclBuilder,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
    hr: &Expr,
    hr1: &Expr,
) -> Expr {
    // A := ofRat s hs ; C := √r ; pw := sqrtGen s r hs (defeq mul A C).
    let a = c.ofrat(s, hs);
    let sqrt = c.sqrt(r);

    let ac = c.nnmul(&a, &sqrt); // A·C  (defeq pw)
    let pw = c.sqrt_gen(s, r, hs);
    let lhs = c.nnmul(&pw, &pw);

    // ── Regroup (A·C)·(A·C) → (A·A)·(C·C)  [mul_mul_mul_comm A C A C] ──
    let aa = c.nnmul(&a, &a);
    let cc_ = c.nnmul(&sqrt, &sqrt);
    let _acac = c.nnmul(&ac, &ac); // (A·C)·(A·C) = lhs once pw≡A·C.
    let aacc = c.nnmul(&aa, &cc_); // (A·A)·(C·C)
    let step_regroup = c.nn_mmm(&a, &sqrt, &a, &sqrt); // acac = aacc

    // ── C-square : C·C = ofRat r hr   (NNReal.sqrtRat_mul_self r hr hr1). ──
    let cc_eq_ofr = c.sqrt_mul_self(r, hr, hr1);
    let of_r = c.ofrat(r, hr);

    // ── A-square : A·A = ofRat (s·s) h. ──
    let ss = c.rmul(s.clone(), s.clone());
    let h_ss = c.rat_mul_nonneg(s, s, hs, hs);
    let of_ss = c.ofrat(&ss, &h_ss);
    let aa_eq_ofss = c.nn_ofrat_mul(s, s, hs, hs, &h_ss); // A·A = ofRat(s·s)

    // ── Combine: (A·A)·(C·C) = ofRat(s·s)·ofRat r = ofRat((s·s)·r). ──
    // aacc = (A·A)·(C·C)
    //      →[congr right by cc_eq_ofr]  (A·A)·ofRat r
    //      →[congr left  by aa_eq_ofss] ofRat(s·s)·ofRat r
    //      →[ofRat_mul (s·s) r]         ofRat((s·s)·r)
    let aa_ofr = c.nnmul(&aa, &of_r); // (A·A)·ofRat r
    let cc_to_ofr = congr_mul_right(c, bd, &aa, &cc_, &of_r, cc_eq_ofr); // aacc = aa·ofRat r
    let ofss_ofr = c.nnmul(&of_ss, &of_r); // ofRat(s·s)·ofRat r
    let aa_ofr_to_ofss_ofr = congr_mul_left(c, bd, &aa, &of_ss, &of_r, aa_eq_ofss);

    let ssr = c.rmul(ss.clone(), r.clone());
    let h_ssr = c.rat_mul_nonneg(&ss, r, &h_ss, hr);
    let of_ssr = c.ofrat(&ssr, &h_ssr);
    let ofss_ofr_eq = c.nn_ofrat_mul(&ss, r, &h_ss, hr, &h_ssr); // ofRat(s·s)·ofRat r = ofRat((s·s)·r)

    let comb1 = c.trans_nn(&aacc, &aa_ofr, &ofss_ofr, cc_to_ofr, aa_ofr_to_ofss_ofr);
    let comb = c.trans_nn(&aacc, &ofss_ofr, &of_ssr, comb1, ofss_ofr_eq);

    // FULL: lhs = acac = aacc (step_regroup) = ofRat((s·s)·r) (comb).
    c.trans_nn(&lhs, &aacc, &of_ssr, step_regroup, comb)
}

/// The full `sqrtGen_sq_at` proof term: the square core followed by an
/// `ofRat`-value congruence transporting `ofRat ((s·s)·r) = ofRat x` using the
/// reconstruction equation `heq : x = (s·s)·r` (its `symm`).
fn build_sqrt_gen_sq_at_value(c: &SqrtGenConsts) -> Expr {
    let mut bd = EnvDeclBuilder::new();
    let (x_id, x) = bd.fresh_local(c.rat.clone());
    let (s_id, s) = bd.fresh_local(c.rat.clone());
    let (r_id, r) = bd.fresh_local(c.rat.clone());
    let hx_ty = c.rle(c.rat_zero.clone(), x.clone());
    let (hx_id, hx) = bd.fresh_local(hx_ty.clone());
    let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
    let (hs_id, hs) = bd.fresh_local(hs_ty.clone());
    let hr_ty = c.rle(c.rat_zero.clone(), r.clone());
    let (hr_id, hr) = bd.fresh_local(hr_ty.clone());
    let hr1_ty = c.rlt(r.clone(), c.rat_one.clone());
    let (hr1_id, hr1) = bd.fresh_local(hr1_ty.clone());
    let (ssr, h_ssr) = ss_r_and_proof(c, &s, &r, &hs, &hr);
    let heq_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), ssr.clone()]);
    let (heq_id, heq) = bd.fresh_local(heq_ty.clone());

    // core : mul pw pw = ofRat ((s·s)·r) h_ssr.
    let pw = c.sqrt_gen(&s, &r, &hs);
    let lhs = c.nnmul(&pw, &pw);
    let core = build_sqrt_gen_sq_core(c, &bd, &s, &r, &hs, &hr, &hr1);
    let of_ssr = c.ofrat(&ssr, &h_ssr);

    // value-congr : ofRat ((s·s)·r) h_ssr = ofRat x hx, transporting the VALUE
    // `(s·s)·r → x` via Eq.subst over a Π-motive (nonneg arg is a Prop,
    // proof-irrelevant). Needs `(s·s)·r = x` i.e. `symm heq` (heq : x = (s·s)·r).
    let heq_symm = Expr::apps(
        c.eq_symm1.clone(),
        [c.rat.clone(), x.clone(), ssr.clone(), heq.clone()],
    );
    let val_congr = ofrat_value_congr(c, &bd, &ssr, &x, &h_ssr, &hx, heq_symm);
    let of_x = c.ofrat(&x, &hx);

    // FULL: lhs =[core] ofRat(ssr) =[val_congr] ofRat x.
    let full = c.trans_nn(&lhs, &of_ssr, &of_x, core, val_congr);

    let e = bd.mk_lam(heq_id, BinderInfo::Default, heq_ty, full);
    let e = bd.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, e);
    let e = bd.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
    let e = bd.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
    let e = bd.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
    let e = bd.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
    let e = bd.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
    bd.finish(bd.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
}

/// `ofRat a ha = ofRat b hb` from `h_eq : a = b`. The nonneg argument is a
/// `Prop`, so proof-irrelevant; transport the VALUE via `Eq.subst` over
/// `fun z => Π (hz : 0≤z), ofRat a ha = ofRat z hz`. (Mirrors the cbrt_gen
/// `ofrat_value_congr`.)
fn ofrat_value_congr(
    c: &SqrtGenConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    ha: &Expr,
    hb: &Expr,
    h_eq: Expr,
) -> Expr {
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = {
            let mut di = EnvDeclBuilder::child_of(&d);
            let hz_ty = c.rle(c.rat_zero.clone(), z.clone());
            let (hz_id, hz) = di.fresh_local(hz_ty.clone());
            let body = c.eq_nn(&c.ofrat(a, ha), &c.ofrat(&z, &hz));
            di.finish_child(di.mk_pi(hz_id, BinderInfo::Default, hz_ty, body))
        };
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), inner))
    };
    let base = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let ha_ty = c.rle(c.rat_zero.clone(), a.clone());
        let (hz_id, _hz) = d.fresh_local(ha_ty.clone());
        let body = c.refl_nn(&c.ofrat(a, ha));
        d.finish_child(d.mk_lam(hz_id, BinderInfo::Default, ha_ty, body))
    };
    let transported = Expr::apps(
        c.eq_subst1.clone(),
        [c.rat.clone(), motive, a.clone(), b.clone(), h_eq, base],
    );
    Expr::apps(transported, [hb.clone()])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.sqrtGen_sq", "NNReal.sqrtGen_sq_at"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_gen()
            .expect("init_algebra_nnreal_sqrt_gen");
        env.init_algebra_nnreal_sqrt_gen().expect("idempotent");
        env
    }

    #[test]
    fn test_sqrt_gen_def_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.sqrtGen");
        let info = env.get_const(&nm).expect("NNReal.sqrtGen registered");
        assert_eq!(info.kind, ConstantKind::Definition, "must be Definition");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.sqrtGen must kernel-check");
    }

    #[test]
    fn test_sqrt_gen_sq_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_sqrt_gen_sq_constructive_empty_closure() {
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
