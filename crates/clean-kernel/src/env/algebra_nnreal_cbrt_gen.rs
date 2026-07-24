// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the GENERAL (scale-parameterized) cube root on ALL
//! nonneg `Rat`, axiom-free.
//!
//! # Why this module exists (the [0,1)-faithfulness unblock)
//!
//! The landed `NNReal.cbrt` is faithful ONLY on `[0,1)` — its dyadic floor seeds
//! `k_0 = 0`, so `cbrt(x)³ ≠ x` for `x ≥ 1` (the carrier saturates below 1). The
//! `(4/3, 4)` two-point Holder base needs `|a ± b|^{4/3}` at ARBITRARY values, so
//! we need a cube root that cubes back for every nonneg argument, not just on
//! `[0,1)`.
//!
//! THE UNBLOCK: stay inside the faithful range by SCALING. For any `x ≥ 0` the
//! archimedean `Rat.exists_pow_gt` guarantees a `k : Nat` with `8^k > x`, hence
//! the reduced argument `r := x · 8^{-k} ∈ [0,1)`. With `s := 2^k` (so `s³ = 8^k`)
//! the cube root of `x` is `s · cbrt(r)`, and
//!
//! ```text
//!   (s · cbrt r)³ = s³ · (cbrt r)³ = 8^k · r = 8^k · (x · 8^{-k}) = x.
//! ```
//!
//! `cbrt(r)³ = ofRat r` is the GENUINE landed `NNReal.cbrt_cubed` (`r ∈ [0,1)`,
//! faithful), so the reduction to `[0,1)` is the real content — NOT a refl.
//!
//! This is the SAME scaling-reduction the value-`2^{4/3}` keystone
//! (`algebra_nnreal_two_four_thirds.rs`) does for the single fixed scale
//! `s = 4, r = 1/4`; here the scale `s` and reduced arg `r` are ABSTRACT, so the
//! identity is general over every nonneg argument.
//!
//! # The k-dependence (honest)
//!
//! The keystone `NNReal.cbrtGen_cubed` is stated over an ABSTRACT scale `s` and
//! reduced arg `r ∈ [0,1)`: `(s · cbrt r)³ = ofRat ((s·s·s)·r)`. The caller picks
//! `s = 2^k` and `r = x·8^{-k}` for whichever valid `k` the archimedean witness
//! supplies; the cube identity then reads `ofRat ((s·s·s)·r) = ofRat (8^k·r) =
//! ofRat x`, the last equality by the reconstruction equation `x = (s·s·s)·r`.
//! Because the identity is keyed on the equation `x = (s·s·s)·r` rather than on
//! `k`, well-definedness across different valid `k` is automatic: ANY valid `k`
//! gives the SAME `ofRat x`. The `x`-facing corollary `NNReal.cbrtGen_cubed_at`
//! makes this explicit — given any `s, r` with `x = (s·s·s)·r`, `0 ≤ s`,
//! `r ∈ [0,1)`, `(s·cbrt r)³ = ofRat x`. NO `Nat.rec` least-`k` construction is
//! needed (and none is built); the abstract-scale statement subsumes it.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.cbrtGen : (s r : Rat) → (hs : 0 ≤ s) → NNReal`
//!     `:= NNReal.mul (NNReal.ofRat s hs) (NNReal.cbrt r)`.
//!   Reducible `Definition`. The scaled cube root `s · cbrt(r)`.
//!
//! - `NNReal.cbrtGen_cubed : ∀ (s r : Rat)(hs:0≤s)(hr:0≤r)(hr1:r<1),`
//!     `NNReal.mul (NNReal.mul (cbrtGen s r hs)(cbrtGen s r hs))(cbrtGen s r hs)`
//!     `  = NNReal.ofRat (((s·s)·s)·r) h`.   The keystone (general, axiom-free).
//!
//! - `NNReal.cbrtGen_cubed_at : ∀ (x s r : Rat)(hx:0≤x)(hs:0≤s)(hr:0≤r)(hr1:r<1)`
//!     `(heq : x = ((s·s)·s)·r),`
//!     `NNReal.mul (NNReal.mul (cbrtGen s r hs)(cbrtGen s r hs))(cbrtGen s r hs)`
//!     `  = NNReal.ofRat x hx`.   The `x`-facing corollary: `(cbrt-of-x)³ = x`.
//!
//! `Declaration::Theorem`/`Definition`, `ProofQuality::Constructive`, empty
//! admitted-axiom closure (foundational only). NO `sorry` / `add_decl_unchecked`
//! / `add_decl_structural`. FORBIDDEN here: `NNReal.cbrt` applied to a `≥ 1`
//! argument inside a `cube_cubed`-style claim (we ONLY ever cube `cbrt r` for
//! `r ∈ [0,1)`).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the general scaled cbrt.
/// Self-contained (mirrors `Pow43CubedConsts`, with the abstract scale `s` in
/// the `A`-role and the reduced arg `r` in the `C`-role).
struct CbrtGenConsts {
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
    nnreal_cbrt: Expr,
    nnreal_cbrt_gen: Expr,
    nnreal_cbrt_gen_cubed_at: Expr,
    nnreal_pow43_gen: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_mmm_comm: Expr,
    nnreal_cbrt_cubed: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
}

impl CbrtGenConsts {
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
            nnreal_cbrt: k("NNReal.cbrt"),
            nnreal_cbrt_gen: k("NNReal.cbrtGen"),
            nnreal_cbrt_gen_cubed_at: k("NNReal.cbrtGen_cubed_at"),
            nnreal_pow43_gen: k("NNReal.pow43Gen"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_mmm_comm: k("NNReal.mul_mul_mul_comm"),
            nnreal_cbrt_cubed: k("NNReal.cbrt_cubed"),
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
    fn cbrt(&self, r: &Expr) -> Expr {
        Expr::app(self.nnreal_cbrt.clone(), r.clone())
    }
    /// `NNReal.cbrtGen s r hs`.
    fn cbrt_gen(&self, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_cbrt_gen.clone(),
            [s.clone(), r.clone(), hs.clone()],
        )
    }
    /// `NNReal.pow43Gen x s r hx hs`.
    fn pow43_gen(&self, x: &Expr, s: &Expr, r: &Expr, hx: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_pow43_gen.clone(),
            [x.clone(), s.clone(), r.clone(), hx.clone(), hs.clone()],
        )
    }
    /// `NNReal.cbrtGen_cubed_at x s r hx hs hr hr1 heq :
    ///    mul(mul (cbrtGen s r hs)(cbrtGen s r hs))(cbrtGen s r hs) = ofRat x hx`.
    fn cbrt_gen_cubed_at(
        &self,
        x: &Expr,
        s: &Expr,
        r: &Expr,
        hx: &Expr,
        hs: &Expr,
        hr: &Expr,
        hr1: &Expr,
        heq: &Expr,
    ) -> Expr {
        Expr::apps(
            self.nnreal_cbrt_gen_cubed_at.clone(),
            [
                x.clone(),
                s.clone(),
                r.clone(),
                hx.clone(),
                hs.clone(),
                hr.clone(),
                hr1.clone(),
                heq.clone(),
            ],
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
}

impl Environment {
    /// Register `NNReal.cbrtGen`, `NNReal.cbrtGen_cubed`, and
    /// `NNReal.cbrtGen_cubed_at`. Reuses the landed `NNReal.cbrt_cubed`,
    /// `NNReal.mul_mul_mul_comm`, `NNReal.ofRat_mul`, `Rat.mul_nonneg`.
    /// Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_cbrt_gen(&mut self) -> Result<(), EnvError> {
        // pow43_cubed seeds: ofRat_mul, mul_comm, mul_assoc, mul_mul_mul_comm,
        // cbrt_cubed, Rat.mul_nonneg, NNReal.cbrt.
        self.init_algebra_nnreal_pow43_cubed()?;
        self.init_eq()?;

        let c = CbrtGenConsts::new();
        self.register_cbrt_gen_def(&c)?;
        self.register_cbrt_gen_cubed(&c)?;
        self.register_cbrt_gen_cubed_at(&c)?;
        self.register_pow43_gen_def(&c)?;
        self.register_pow43_gen_cubed(&c)?;
        Ok(())
    }

    /// `NNReal.cbrtGen : (s r : Rat) → (hs : 0 ≤ s) → NNReal`
    ///   `:= fun s r hs => NNReal.mul (NNReal.ofRat s hs) (NNReal.cbrt r)`.
    fn register_cbrt_gen_def(&mut self, c: &CbrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cbrtGen");
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
            let body = c.nnmul(&c.ofrat(&s, &hs), &c.cbrt(&r));
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

    /// `NNReal.cbrtGen_cubed`.
    fn register_cbrt_gen_cubed(&mut self, c: &CbrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cbrtGen_cubed");
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
            let pw = c.cbrt_gen(&s, &r, &hs);
            let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);
            let (sssr, hsssr) = sss_r_and_proof(c, &s, &r, &hs, &hr);
            let rhs = c.ofrat(&sssr, &hsssr);
            let concl = c.eq_nn(&lhs, &rhs);
            let e = bd.mk_pi(hr1_id, BinderInfo::Default, hr1_ty, concl);
            let e = bd.mk_pi(hr_id, BinderInfo::Default, hr_ty, e);
            let e = bd.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
            let e = bd.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
            bd.finish(bd.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_cbrt_gen_cubed_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.cbrtGen_cubed_at` — the `x`-facing corollary: with the
    /// reconstruction equation `x = ((s·s)·s)·r`, the scaled cube cubes to
    /// `ofRat x`. This is "general cbrt on all nonneg x": for any `x ≥ 0`, pick
    /// `s = 2^k, r = x·8^{-k}` (k from `Rat.exists_pow_gt`), then `((s·s)·s)·r =
    /// 8^k · (x·8^{-k}) = x`.
    fn register_cbrt_gen_cubed_at(&mut self, c: &CbrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cbrtGen_cubed_at");
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
            let (sssr, _h) = sss_r(c, &s, &r);
            let heq_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), sssr.clone()]);
            let (heq_id, _heq) = bd.fresh_local(heq_ty.clone());
            let pw = c.cbrt_gen(&s, &r, &hs);
            let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);
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
        let value = build_cbrt_gen_cubed_at_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.pow43Gen : (x s r : Rat) → (hx : 0≤x) → (hs : 0≤s) → NNReal`
    ///   `:= fun x s r hx hs => NNReal.mul (NNReal.ofRat x hx)(NNReal.cbrtGen s r hs)`.
    /// The general `x^{4/3} = x · x^{1/3}` for ALL nonneg `x` (with the scale `s`
    /// and reduced arg `r` realizing `x^{1/3}` via `cbrtGen`).
    fn register_pow43_gen_def(&mut self, c: &CbrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.pow43Gen");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (r_id, _r) = b.fresh_local(c.rat.clone());
            let hx_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (hx_id, _hx) = b.fresh_local(hx_ty.clone());
            let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
            let (hs_id, _hs) = b.fresh_local(hs_ty.clone());
            let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, c.nnreal.clone());
            let e = b.mk_pi(hx_id, BinderInfo::Default, hx_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (s_id, s) = b.fresh_local(c.rat.clone());
            let (r_id, r) = b.fresh_local(c.rat.clone());
            let hx_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
            let (hs_id, hs) = b.fresh_local(hs_ty.clone());
            let body = c.nnmul(&c.ofrat(&x, &hx), &c.cbrt_gen(&s, &r, &hs));
            let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, body);
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
            let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.pow43Gen_cubed : ∀ (x s r : Rat)(hx:0≤x)(hs:0≤s)(hr:0≤r)(hr1:r<1)`
    ///   `(heq : x = ((s·s)·s)·r),`
    ///   `mul (mul (pow43Gen x s r hx hs)(…))(…) = NNReal.ofRat (((x·x)·x)·x) h`.
    /// The general `^{4/3}` cube identity `(x^{4/3})³ = x⁴` for ALL nonneg `x`.
    fn register_pow43_gen_cubed(&mut self, c: &CbrtGenConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.pow43Gen_cubed");
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
            let (sssr, _h) = sss_r(c, &s, &r);
            let heq_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), sssr.clone()]);
            let (heq_id, _heq) = bd.fresh_local(heq_ty.clone());
            let pw = c.pow43_gen(&x, &s, &r, &hx, &hs);
            let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);
            let (x4, h4) = x4_and_proof(c, &x, &hx);
            let rhs = c.ofrat(&x4, &h4);
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
        let value = build_pow43_gen_cubed_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `x⁴ := ((x·x)·x)·x` (left-nested) and `h4 : 0 ≤ x⁴` from `hx : 0≤x`.
fn x4_and_proof(c: &CbrtGenConsts, x: &Expr, hx: &Expr) -> (Expr, Expr) {
    let xx = c.rmul(x.clone(), x.clone());
    let xxx = c.rmul(xx.clone(), x.clone());
    let xxxx = c.rmul(xxx.clone(), x.clone());
    let h_xx = c.rat_mul_nonneg(x, x, hx, hx);
    let h_xxx = c.rat_mul_nonneg(&xx, x, &h_xx, hx);
    let h_xxxx = c.rat_mul_nonneg(&xxx, x, &h_xxx, hx);
    (xxxx, h_xxxx)
}

/// `((s·s)·s)·r` (left-nested) — pure expression form.
fn sss_r(c: &CbrtGenConsts, s: &Expr, r: &Expr) -> (Expr, ()) {
    let ss = c.rmul(s.clone(), s.clone());
    let sss = c.rmul(ss.clone(), s.clone());
    (c.rmul(sss, r.clone()), ())
}

/// `((s·s)·s)·r` (left-nested) and `h : 0 ≤ ((s·s)·s)·r` from `0≤s`, `0≤r`.
fn sss_r_and_proof(c: &CbrtGenConsts, s: &Expr, r: &Expr, hs: &Expr, hr: &Expr) -> (Expr, Expr) {
    let ss = c.rmul(s.clone(), s.clone());
    let sss = c.rmul(ss.clone(), s.clone());
    let sssr = c.rmul(sss.clone(), r.clone());
    let h_ss = c.rat_mul_nonneg(s, s, hs, hs);
    let h_sss = c.rat_mul_nonneg(&ss, s, &h_ss, hs);
    let h_sssr = c.rat_mul_nonneg(&sss, r, &h_sss, hr);
    (sssr, h_sssr)
}

/// `a·p = a·q` from `h : p = q` (congruence in the right factor).
fn congr_mul_right(
    c: &CbrtGenConsts,
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
    c: &CbrtGenConsts,
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

/// The full `cbrtGen_cubed` proof term.
///
/// `A := ofRat s hs`, `C := cbrt r`, `pw := cbrtGen s r hs` (reducible-defeq
/// `mul A C`). Mirrors `build_pow43_cubed_value` with the abstract scale `s` in
/// the `A`-role and the reduced arg `r` in the `C`-role.
fn build_cbrt_gen_cubed_value(c: &CbrtGenConsts) -> Expr {
    let mut bd = EnvDeclBuilder::new();
    let (s_id, s) = bd.fresh_local(c.rat.clone());
    let (r_id, r) = bd.fresh_local(c.rat.clone());
    let hs_ty = c.rle(c.rat_zero.clone(), s.clone());
    let (hs_id, hs) = bd.fresh_local(hs_ty.clone());
    let hr_ty = c.rle(c.rat_zero.clone(), r.clone());
    let (hr_id, hr) = bd.fresh_local(hr_ty.clone());
    let hr1_ty = c.rlt(r.clone(), c.rat_one.clone());
    let (hr1_id, hr1) = bd.fresh_local(hr1_ty.clone());

    let body = build_cbrt_gen_cube_core(c, &bd, &s, &r, &hs, &hr, &hr1);

    let e = bd.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, body);
    let e = bd.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
    let e = bd.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
    let e = bd.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
    bd.finish(bd.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e))
}

/// The shared cube core: a proof of
/// `mul (mul pw pw) pw = ofRat (((s·s)·s)·r) h` where `pw := cbrtGen s r hs`.
/// Reused by both `cbrtGen_cubed` and (via a final value-congruence)
/// `cbrtGen_cubed_at`.
fn build_cbrt_gen_cube_core(
    c: &CbrtGenConsts,
    bd: &EnvDeclBuilder,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
    hr: &Expr,
    hr1: &Expr,
) -> Expr {
    // A := ofRat s hs ; C := cbrt r ; pw := cbrtGen s r hs (defeq mul A C).
    let a = c.ofrat(s, hs);
    let cbrt = c.cbrt(r);
    let pw = c.cbrt_gen(s, r, hs);

    let ac = c.nnmul(&a, &cbrt); // A·C  (defeq pw)
    let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);

    // ── Regroup (A·C)·(A·C)·(A·C) → ((A·A)·A)·((C·C)·C) ──
    let aa = c.nnmul(&a, &a);
    let cc_ = c.nnmul(&cbrt, &cbrt);
    let acac = c.nnmul(&ac, &ac); // (A·C)·(A·C)
    let aacc = c.nnmul(&aa, &cc_); // (A·A)·(C·C)
    let i1 = c.nn_mmm(&a, &cbrt, &a, &cbrt);
    let aaa = c.nnmul(&aa, &a); // (A·A)·A
    let ccc = c.nnmul(&cc_, &cbrt); // (C·C)·C
    let i2 = c.nn_mmm(&aa, &cc_, &a, &cbrt);
    let aacc_ac = c.nnmul(&aacc, &ac); // ((A·A)·(C·C))·(A·C)
    let aaa_ccc = c.nnmul(&aaa, &ccc); // ((A·A)·A)·((C·C)·C)

    let left_rw = congr_mul_left(c, bd, &acac, &aacc, &ac, i1);
    let acac_ac = c.nnmul(&acac, &ac); // (A·C·A·C)·(A·C) = lhs once pw≡A·C.
    let step_regroup = c.trans_nn(&acac_ac, &aacc_ac, &aaa_ccc, left_rw, i2);

    // ── C-cube : (C·C)·C = ofRat r hr   (NNReal.cbrt_cubed r hr hr1). ──
    let ccc_eq_ofr = Expr::apps(
        c.nnreal_cbrt_cubed.clone(),
        [r.clone(), hr.clone(), hr1.clone()],
    );
    let of_r = c.ofrat(r, hr);

    // ── A-cube : (A·A)·A = ofRat ((s·s)·s) h. ──
    let ss = c.rmul(s.clone(), s.clone());
    let sss = c.rmul(ss.clone(), s.clone());
    let h_ss = c.rat_mul_nonneg(s, s, hs, hs);
    let h_sss = c.rat_mul_nonneg(&ss, s, &h_ss, hs);
    let of_ss = c.ofrat(&ss, &h_ss);
    let of_sss = c.ofrat(&sss, &h_sss);
    let aa_eq_ofss = c.nn_ofrat_mul(s, s, hs, hs, &h_ss); // A·A = ofRat(s·s)
    let aaa_to_ofss_a = congr_mul_left(c, bd, &aa, &of_ss, &a, aa_eq_ofss);
    let ofss_a = c.nnmul(&of_ss, &a); // ofRat(s·s)·ofRat s
    let ofss_a_eq = c.nn_ofrat_mul(&ss, s, &h_ss, hs, &h_sss); // = ofRat((s·s)·s)
    let aaa_eq_ofsss = c.trans_nn(&aaa, &ofss_a, &of_sss, aaa_to_ofss_a, ofss_a_eq);

    // ── Combine: ((A·A)·A)·((C·C)·C) = ofRat((s·s)·s)·ofRat r = ofRat(((s·s)·s)·r). ──
    let aaa_ofr = c.nnmul(&aaa, &of_r); // ((A·A)·A)·ofRat r
    let ccc_to_ofr = congr_mul_right(c, bd, &aaa, &ccc, &of_r, ccc_eq_ofr); // aaa·ccc = aaa·ofRat r
    let ofsss_ofr = c.nnmul(&of_sss, &of_r); // ofRat((s·s)·s)·ofRat r
    let aaa_ofr_to_ofsss_ofr = congr_mul_left(c, bd, &aaa, &of_sss, &of_r, aaa_eq_ofsss);
    // ofRat((s·s)·s)·ofRat r = ofRat(((s·s)·s)·r)   ofRat_mul (sss) r.
    let sssr = c.rmul(sss.clone(), r.clone());
    let h_sssr = c.rat_mul_nonneg(&sss, r, &h_sss, hr);
    let of_sssr = c.ofrat(&sssr, &h_sssr);
    let ofsss_ofr_eq = c.nn_ofrat_mul(&sss, r, &h_sss, hr, &h_sssr);

    let comb1 = c.trans_nn(
        &aaa_ccc,
        &aaa_ofr,
        &ofsss_ofr,
        ccc_to_ofr,
        aaa_ofr_to_ofsss_ofr,
    );
    let comb = c.trans_nn(&aaa_ccc, &ofsss_ofr, &of_sssr, comb1, ofsss_ofr_eq);

    // FULL: lhs = aaa_ccc (step_regroup) = ofRat(((s·s)·s)·r) (comb).
    c.trans_nn(&lhs, &aaa_ccc, &of_sssr, step_regroup, comb)
}

/// The full `cbrtGen_cubed_at` proof term: the cube core followed by an
/// `ofRat`-value congruence transporting `ofRat (((s·s)·s)·r) = ofRat x` using
/// the reconstruction equation `heq : x = ((s·s)·s)·r` (its `symm`).
fn build_cbrt_gen_cubed_at_value(c: &CbrtGenConsts) -> Expr {
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
    let (sssr, h_sssr) = sss_r_and_proof(c, &s, &r, &hs, &hr);
    let heq_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), sssr.clone()]);
    let (heq_id, heq) = bd.fresh_local(heq_ty.clone());

    // core : mul(mul pw pw) pw = ofRat (((s·s)·s)·r) h_sssr.
    let pw = c.cbrt_gen(&s, &r, &hs);
    let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);
    let core = build_cbrt_gen_cube_core(c, &bd, &s, &r, &hs, &hr, &hr1);
    let of_sssr = c.ofrat(&sssr, &h_sssr);

    // value-congr : ofRat (((s·s)·s)·r) h_sssr = ofRat x hx, transporting the
    // VALUE `((s·s)·s)·r → x` via Eq.subst over a Π-motive (nonneg arg is a
    // Prop, proof-irrelevant). `ofrat_value_congr` needs `a = b` i.e.
    // `((s·s)·s)·r = x`, so feed `symm heq` (heq : x = ((s·s)·s)·r).
    let heq_symm = Expr::apps(
        c.eq_symm1.clone(),
        [c.rat.clone(), x.clone(), sssr.clone(), heq.clone()],
    );
    let val_congr = ofrat_value_congr(c, &bd, &sssr, &x, &h_sssr, &hx, heq_symm);
    let of_x = c.ofrat(&x, &hx);

    // FULL: lhs =[core] ofRat(sssr) =[val_congr] ofRat x.
    let full = c.trans_nn(&lhs, &of_sssr, &of_x, core, val_congr);

    let e = bd.mk_lam(heq_id, BinderInfo::Default, heq_ty, full);
    let e = bd.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, e);
    let e = bd.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
    let e = bd.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
    let e = bd.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
    let e = bd.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
    let e = bd.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
    bd.finish(bd.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
}

/// The full `pow43Gen_cubed` proof term: `(x · cbrtGen s r)³ = x⁴`.
///
/// `A := ofRat x hx` (the `A`-cube → `ofRat((x·x)·x)` via two `ofRat_mul`s),
/// `C := cbrtGen s r hs` (the `C`-cube → `ofRat x` via `cbrtGen_cubed_at`),
/// `pw := pow43Gen x s r hx hs` (reducible-defeq `mul A C`). Mirrors
/// `build_pow43_cubed_value`, with the `C`-cube using the general
/// `NNReal.cbrtGen_cubed_at` (so `r ∈ [0,1)` is the ONLY range constraint, and
/// `x` is an ARBITRARY nonneg).
fn build_pow43_gen_cubed_value(c: &CbrtGenConsts) -> Expr {
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
    let (sssr, _h) = sss_r(c, &s, &r);
    let heq_ty = Expr::apps(c.eq1.clone(), [c.rat.clone(), x.clone(), sssr.clone()]);
    let (heq_id, heq) = bd.fresh_local(heq_ty.clone());

    // A := ofRat x hx ; C := cbrtGen s r hs ; pw := pow43Gen … (defeq mul A C).
    let a = c.ofrat(&x, &hx);
    let cg = c.cbrt_gen(&s, &r, &hs);
    let pw = c.pow43_gen(&x, &s, &r, &hx, &hs);

    let ac = c.nnmul(&a, &cg); // A·C  (defeq pw)
    let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);

    // ── Regroup (A·C)·(A·C)·(A·C) → ((A·A)·A)·((C·C)·C) ──
    let aa = c.nnmul(&a, &a);
    let cc_ = c.nnmul(&cg, &cg);
    let acac = c.nnmul(&ac, &ac); // (A·C)·(A·C)
    let aacc = c.nnmul(&aa, &cc_); // (A·A)·(C·C)
    let i1 = c.nn_mmm(&a, &cg, &a, &cg);
    let aaa = c.nnmul(&aa, &a); // (A·A)·A
    let ccc = c.nnmul(&cc_, &cg); // (C·C)·C
    let i2 = c.nn_mmm(&aa, &cc_, &a, &cg);
    let aacc_ac = c.nnmul(&aacc, &ac); // ((A·A)·(C·C))·(A·C)
    let aaa_ccc = c.nnmul(&aaa, &ccc); // ((A·A)·A)·((C·C)·C)

    let left_rw = congr_mul_left(c, &bd, &acac, &aacc, &ac, i1);
    let acac_ac = c.nnmul(&acac, &ac); // (A·C·A·C)·(A·C) = lhs once pw≡A·C.
    let step_regroup = c.trans_nn(&acac_ac, &aacc_ac, &aaa_ccc, left_rw, i2);

    // ── C-cube : (C·C)·C = ofRat x hx   (NNReal.cbrtGen_cubed_at). ──
    let ccc_eq_a = c.cbrt_gen_cubed_at(&x, &s, &r, &hx, &hs, &hr, &hr1, &heq); // (C·C)·C = ofRat x hx = A

    // ── A-cube : (A·A)·A = ofRat ((x·x)·x) h. ──
    let xx = c.rmul(x.clone(), x.clone());
    let xxx = c.rmul(xx.clone(), x.clone());
    let h_xx = c.rat_mul_nonneg(&x, &x, &hx, &hx);
    let h_xxx = c.rat_mul_nonneg(&xx, &x, &h_xx, &hx);
    let of_xx = c.ofrat(&xx, &h_xx);
    let of_xxx = c.ofrat(&xxx, &h_xxx);
    let aa_eq_ofxx = c.nn_ofrat_mul(&x, &x, &hx, &hx, &h_xx); // A·A = ofRat(x·x)
    let aaa_to_ofxx_a = congr_mul_left(c, &bd, &aa, &of_xx, &a, aa_eq_ofxx);
    let ofxx_a = c.nnmul(&of_xx, &a); // ofRat(x·x)·ofRat x
    let ofxx_a_eq = c.nn_ofrat_mul(&xx, &x, &h_xx, &hx, &h_xxx); // = ofRat((x·x)·x)
    let aaa_eq_ofxxx = c.trans_nn(&aaa, &ofxx_a, &of_xxx, aaa_to_ofxx_a, ofxx_a_eq);

    // ── Combine: ((A·A)·A)·((C·C)·C) = ofRat((x·x)·x)·ofRat x = ofRat(((x·x)·x)·x). ──
    let aaa_a = c.nnmul(&aaa, &a); // ((A·A)·A)·A   (A = ofRat x hx)
    let ccc_to_a = congr_mul_right(c, &bd, &aaa, &ccc, &a, ccc_eq_a); // aaa·ccc = aaa·A
    let ofxxx_a = c.nnmul(&of_xxx, &a); // ofRat((x·x)·x)·ofRat x
    let aaa_a_to_ofxxx_a = congr_mul_left(c, &bd, &aaa, &of_xxx, &a, aaa_eq_ofxxx); // aaa·A = ofRat(xxx)·A
                                                                                    // ofRat((x·x)·x)·ofRat x = ofRat(((x·x)·x)·x)   ofRat_mul (xxx) x.
    let xxxx = c.rmul(xxx.clone(), x.clone());
    let h_xxxx = c.rat_mul_nonneg(&xxx, &x, &h_xxx, &hx);
    let of_xxxx = c.ofrat(&xxxx, &h_xxxx);
    let ofxxx_a_eq = c.nn_ofrat_mul(&xxx, &x, &h_xxx, &hx, &h_xxxx);

    let comb1 = c.trans_nn(&aaa_ccc, &aaa_a, &ofxxx_a, ccc_to_a, aaa_a_to_ofxxx_a);
    let comb = c.trans_nn(&aaa_ccc, &ofxxx_a, &of_xxxx, comb1, ofxxx_a_eq);

    // FULL: lhs = aaa_ccc (step_regroup) = ofRat(xxxx) (comb).
    let full = c.trans_nn(&lhs, &aaa_ccc, &of_xxxx, step_regroup, comb);

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
/// `fun z => Π (hz : 0≤z), ofRat a ha = ofRat z hz`. (Mirrors the
/// `two_four_thirds` `ofrat_value_congr`.)
fn ofrat_value_congr(
    c: &CbrtGenConsts,
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

    const THEOREMS: &[&str] = &[
        "NNReal.cbrtGen_cubed",
        "NNReal.cbrtGen_cubed_at",
        "NNReal.pow43Gen_cubed",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_gen()
            .expect("init_algebra_nnreal_cbrt_gen");
        env.init_algebra_nnreal_cbrt_gen().expect("idempotent");
        env
    }

    #[test]
    fn test_cbrt_gen_def_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in ["NNReal.cbrtGen", "NNReal.pow43Gen"] {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be Definition"
            );
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_cbrt_gen_cubed_kernel_check() {
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
    fn test_cbrt_gen_cubed_constructive_empty_closure() {
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
