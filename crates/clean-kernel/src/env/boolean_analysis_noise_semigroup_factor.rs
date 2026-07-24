// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Noise-operator semigroup campaign — the **per-coordinate noise convolution**
//! (rung 1 of #1, the Bool-level wrapper over the scalar ring engine).
//!
//! ```text
//!   BoolAnalysis.noiseFactor_conv :
//!     ∀ (ρ : Rat) (x y : Bool),
//!       w(ρ,x,false)·w(ρ,false,y) + w(ρ,x,true)·w(ρ,true,y) = (1+1)·w(ρ·ρ, x, y)
//! ```
//!
//! where `w(ρ,a,b) := 1 + ρ·(pm a · pm b)` is the single-coordinate noise kernel
//! (the `prod_int_rho` integrand of `noiseDensityW_eq_prod`). The two-term
//! `z:Bool` sum convolves the kernel over the lone intermediate coordinate; the
//! `rho` squares and the leading `(1+1)=2` is the per-coordinate `|Bool|` factor
//! (the seed of the `2^n` un-normalization the full cube semigroup carries). The
//! ring work is done by `BoolAnalysis.noise_conv_scalar`
//! (`boolean_analysis_noise_semigroup.rs`); this file supplies the `pm`-sign
//! bridges (`pm_not`, `pm_mul_self`, `mul_neg`, derived `neg_mul`,
//! `mul_mul_mul_comm`) that align the Bool-level factors. Kernel-checked,
//! `Constructive`, EMPTY domain-axiom closure. No axiom added or removed.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_noise_semigroup::ConvConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// ===========================================================================
// noiseFactor_conv — the per-coordinate noise convolution (STEP 1).
//
//   ∀ (ρ : Rat) (x y : Bool),
//     w(ρ,x,false)·w(ρ,false,y) + w(ρ,x,true)·w(ρ,true,y)
//       = (1+1)·w(ρ·ρ, x, y)
//
// where `w(ρ,a,b) := 1 + ρ·(pm a · pm b)` is the single-coordinate noise kernel
// (the `prod_int_rho` integrand of `noiseDensityW_eq_prod`). The two-term
// `z:Bool` sum convolves the kernel over the lone intermediate coordinate; the
// `rho` squares (`ρ·ρ`) and the leading `(1+1)=2` is the per-coordinate
// `|Bool|` factor. The scalar engine `noise_conv_scalar` does the ring work;
// the `pm`-sign bridges (`pm_not`, `pm_mul_self`, `mul_neg`/`neg_mul`,
// `mul_mul_mul_comm`) align the Bool-level factors.
// ===========================================================================

impl Environment {
    /// Register `BoolAnalysis.noiseFactor_conv` — the per-coordinate noise
    /// convolution `Σ_{z:Bool} w(ρ,x,z)·w(ρ,z,y) = 2·w(ρ², x, y)`. Kernel-checked,
    /// `Constructive`, EMPTY domain-axiom closure. Idempotent.
    pub(crate) fn register_noise_factor_conv(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseFactor_conv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_field_inst()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.neg_mul_neg
        self.register_noise_conv_scalar()?;
        // `pm`, `pm_not`, `pm_mul_self`, `Rat.neg_mul`, `Rat.mul_neg`,
        // `Rat.mul_mul_mul_comm` come with the boolean-analysis foundations.
        self.init_boolean_analysis()?;
        self.register_pm_not()?;
        self.register_pm_mul_self_theorem()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ConvConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_factor_conv_type(&c),
            value: build_factor_conv_value(&c),
        })
    }
}

fn build_factor_conv_type(c: &ConvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (x_id, x) = b.fresh_local(c.bool_.clone());
    let (y_id, y) = b.fresh_local(c.bool_.clone());

    let lhs = factor_conv_lhs(c, &rho, &x, &y);
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let rhs = c.mul(c.add(c.one(), c.one()), c.factor(&rho_sq, &x, &y));
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(y_id, BinderInfo::Default, c.bool_.clone(), concl);
    let ty = b.mk_pi(x_id, BinderInfo::Default, c.bool_.clone(), ty);
    let ty = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), ty);
    b.finish(ty)
}

/// `w(ρ,x,false)·w(ρ,false,y) + w(ρ,x,true)·w(ρ,true,y)`.
fn factor_conv_lhs(c: &ConvConsts, rho: &Expr, x: &Expr, y: &Expr) -> Expr {
    let zf = c.mul(c.factor(rho, x, &c.bfalse), c.factor(rho, &c.bfalse, y));
    let zt = c.mul(c.factor(rho, x, &c.btrue), c.factor(rho, &c.btrue, y));
    c.add(zf, zt)
}

fn build_factor_conv_value(c: &ConvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (x_id, x) = b.fresh_local(c.bool_.clone());
    let (y_id, y) = b.fresh_local(c.bool_.clone());

    let bf = c.bfalse.clone();
    let bt = c.btrue.clone();

    // Scalar instantiation args: a := ρ·(pm x · pm false), b := ρ·(pm false · pm y).
    let pm_x = c.pm(&x);
    let pm_y = c.pm(&y);
    let pm_bf = c.pm(&bf);
    let xb = c.mul(pm_x.clone(), pm_bf.clone()); // pm x · pm false
    let by = c.mul(pm_bf.clone(), pm_y.clone()); // pm false · pm y
    let sa = c.mul(rho.clone(), xb.clone()); // a
    let sb = c.mul(rho.clone(), by.clone()); // b

    // The z=false product `w(ρ,x,false)·w(ρ,false,y)` IS `(1+a)·(1+b)` by def.
    // The z=true product `w(ρ,x,true)·w(ρ,true,y)` must be rewritten to
    // `(1+(−a))·(1+(−b))`.
    let one_p_a = c.add(c.one(), sa.clone());
    let one_p_b = c.add(c.one(), sb.clone());
    let one_p_na = c.add(c.one(), c.neg(sa.clone()));
    let one_p_nb = c.add(c.one(), c.neg(sb.clone()));

    let lhs = factor_conv_lhs(c, &rho, &x, &y);

    // ── z=true factor rewrites ───────────────────────────────────────────────
    // wt_x : w(ρ,x,true) = 1 + (−a)
    let wt_x = prove_factor_true_x(c, &b, &rho, &x);
    // wt_y : w(ρ,true,y) = 1 + (−b)
    let wt_y = prove_factor_true_y(c, &b, &rho, &y);

    // lhs = (1+a)(1+b) + [(1+(−a))(1+(−b))]
    // step: rewrite the z=true product factor-by-factor.
    let wf_x = c.factor(&rho, &x, &bt); // w(ρ,x,true)
    let wf_y = c.factor(&rho, &bt, &y); // w(ρ,true,y)
    let zt_orig = c.mul(wf_x.clone(), wf_y.clone());
    // congr-left wt_x : wf_x·wf_y = (1+(−a))·wf_y
    let m_zt_l = c.mul_left_motive(&b, &wf_y);
    let zt_c1 = c.congr(wf_x.clone(), one_p_na.clone(), m_zt_l, wt_x);
    let zt_mid = c.mul(one_p_na.clone(), wf_y.clone());
    // congr-right wt_y : (1+(−a))·wf_y = (1+(−a))·(1+(−b))
    let m_zt_r = c.mul_right_motive(&b, &one_p_na);
    let zt_c2 = c.congr(wf_y.clone(), one_p_nb.clone(), m_zt_r, wt_y);
    let zt_target = c.mul(one_p_na.clone(), one_p_nb.clone());
    let zt_eq = c.trans(zt_orig.clone(), zt_mid, zt_target.clone(), zt_c1, zt_c2);

    // lift to the full LHS sum: congr-right (zt_orig → zt_target) under (zf + ·)
    let zf = c.mul(one_p_a.clone(), one_p_b.clone()); // = w(ρ,x,false)·w(ρ,false,y) by def
    let m_sum_r = c.add_right_motive(&b, &zf);
    let lhs_c = c.congr(zt_orig.clone(), zt_target.clone(), m_sum_r, zt_eq);
    let lhs_rw = c.add(zf.clone(), zt_target.clone());

    // ── scalar instance ─────────────────────────────────────────────────────
    // noise_conv_scalar a b : (1+a)(1+b) + (1+(−a))(1+(−b)) = (1+1)·(1 + a·b)
    let scalar = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noise_conv_scalar"), vec![]),
        [sa.clone(), sb.clone()],
    );
    let ab = c.mul(sa.clone(), sb.clone());
    let scalar_rhs = c.mul(c.add(c.one(), c.one()), c.add(c.one(), ab.clone()));

    // ── RHS bridge: (1+1)·(1 + a·b) = (1+1)·(1 + (ρρ)(pm x·pm y)) = (1+1)·w(ρρ,x,y)
    let ab_bridge = prove_ab_eq(c, &b, &rho, &x, &y); // a·b = (ρρ)(pm x · pm y)
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let pmxy = c.mul(pm_x.clone(), pm_y.clone());
    let rrxy = c.mul(rho_sq.clone(), pmxy.clone());
    // motive: fun z => (1+1)·(1 + z)
    let m_rhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = c.add(c.one(), z);
        let body = c.mul(c.add(c.one(), c.one()), inner);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rhs_c = c.congr(ab.clone(), rrxy.clone(), m_rhs, ab_bridge);
    // target RHS = (1+1)·(1 + (ρρ)(pm x·pm y)) = (1+1)·w(ρρ,x,y)  [def-eq]
    let rhs_target = c.mul(c.add(c.one(), c.one()), c.factor(&rho_sq, &x, &y));

    // ── assemble: lhs = lhs_rw = scalar_rhs = rhs_target ─────────────────────
    let t1 = c.trans(
        lhs.clone(),
        lhs_rw.clone(),
        scalar_rhs.clone(),
        lhs_c,
        scalar,
    );
    let proof = c.trans(lhs, scalar_rhs, rhs_target, t1, rhs_c);

    let val = b.mk_lam(y_id, BinderInfo::Default, c.bool_.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, c.bool_.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

/// `w(ρ,x,true) = 1 + (−(ρ·(pm x · pm false)))`.
///   w(ρ,x,true) = 1 + ρ·(pm x · pm true)
///   pm true = pm (¬false) = Rat.neg (pm false)         [pm_not false, ¬false ≡ true]
///   ⇒ pm x · pm true = pm x · (−(pm false)) = −(pm x · pm false)   [mul_neg]
///   ⇒ ρ·(pm x · pm true) = ρ·(−(pm x·pm false)) = −(ρ·(pm x·pm false))  [mul_neg]
fn prove_factor_true_x(c: &ConvConsts, parent: &EnvDeclBuilder, rho: &Expr, x: &Expr) -> Expr {
    let bf = c.bfalse.clone();
    let pm_x = c.pm(x);
    let pm_bf = c.pm(&bf);
    let pm_bt = c.pm(&c.btrue); // pm true
    let xb_false = c.mul(pm_x.clone(), pm_bf.clone()); // pm x · pm false
    let xb_true = c.mul(pm_x.clone(), pm_bt.clone()); // pm x · pm true

    // w(ρ,x,true) = 1 + ρ·(pm x · pm true)  ; target = 1 + (−(ρ·(pm x·pm false)))
    let w_true = c.factor(rho, x, &c.btrue);
    let target = c.add(c.one(), c.neg(c.mul(rho.clone(), xb_false.clone())));

    // We prove the inner `ρ·(pm x · pm true) = −(ρ·(pm x·pm false))` then congr
    // under `1 + ·`.
    // h1 : pm true = Rat.neg (pm false)    [pm_not false : pm (¬false) = Rat.neg(pm false); ¬false ≡ true def-eq]
    let pm_not_false = c.h_pm_not(&bf);
    let neg_pm_bf = c.neg(pm_bf.clone());
    // congr-right (pm x · ·) : pm x · pm true = pm x · (−(pm false))
    let m_pmx = c.mul_right_motive(parent, &pm_x);
    let step_a = c.congr(pm_bt.clone(), neg_pm_bf.clone(), m_pmx, pm_not_false);
    let xb_negbf = c.mul(pm_x.clone(), neg_pm_bf.clone()); // pm x · (−(pm false))
                                                           // mul_neg (pm x) (pm false) : pm x · (−(pm false)) = −(pm x · pm false)
    let mn = c.h_mul_neg(&pm_x, &pm_bf);
    let neg_xb_false = c.neg(xb_false.clone());
    // chain: pm x·pm true = pm x·(−pm false) = −(pm x·pm false)
    let inner_pm = c.trans(
        xb_true.clone(),
        xb_negbf.clone(),
        neg_xb_false.clone(),
        step_a,
        mn,
    );
    // congr-right (ρ·) : ρ·(pm x·pm true) = ρ·(−(pm x·pm false))
    let m_rho = c.mul_right_motive(parent, rho);
    let step_b = c.congr(xb_true.clone(), neg_xb_false.clone(), m_rho, inner_pm);
    let rho_negxb = c.mul(rho.clone(), neg_xb_false.clone()); // ρ·(−(pm x·pm false))
                                                              // mul_neg ρ (pm x·pm false) : ρ·(−(pm x·pm false)) = −(ρ·(pm x·pm false))
    let mn2 = c.h_mul_neg(rho, &xb_false);
    let rho_xb_false = c.mul(rho.clone(), xb_false.clone());
    let neg_rho_xb = c.neg(rho_xb_false.clone());
    let inner = c.trans(
        c.mul(rho.clone(), xb_true.clone()),
        rho_negxb,
        neg_rho_xb.clone(),
        step_b,
        mn2,
    );
    // congr under `1 + ·`
    // cong : (1 + ρ·(pm x·pm true)) = (1 + (−(ρ·(pm x·pm false))))
    // which is exactly  w(ρ,x,true) = target  (def-eq on the LHS).
    let _ = (&w_true, &target);
    let m_one = c.add_right_motive(parent, &c.one());
    c.congr(
        c.mul(rho.clone(), xb_true.clone()),
        neg_rho_xb,
        m_one,
        inner,
    )
}

/// `w(ρ,true,y) = 1 + (−(ρ·(pm false · pm y)))`.
///   symmetric to `prove_factor_true_x` but the `pm true` sits on the LEFT of the
///   inner product, so we use `neg_mul` instead of `mul_neg`.
fn prove_factor_true_y(c: &ConvConsts, parent: &EnvDeclBuilder, rho: &Expr, y: &Expr) -> Expr {
    let bf = c.bfalse.clone();
    let pm_y = c.pm(y);
    let pm_bf = c.pm(&bf);
    let pm_bt = c.pm(&c.btrue);
    let by_false = c.mul(pm_bf.clone(), pm_y.clone()); // pm false · pm y
    let by_true = c.mul(pm_bt.clone(), pm_y.clone()); // pm true · pm y

    // h: pm true = Rat.neg(pm false)
    let pm_not_false = c.h_pm_not(&bf);
    let neg_pm_bf = c.neg(pm_bf.clone());
    // congr-left (· · pm y) : pm true · pm y = (−(pm false)) · pm y
    let m_pmy = c.mul_left_motive(parent, &pm_y);
    let step_a = c.congr(pm_bt.clone(), neg_pm_bf.clone(), m_pmy, pm_not_false);
    let negbf_y = c.mul(neg_pm_bf.clone(), pm_y.clone());
    // (−(pm false))·pm y = −(pm false·pm y)   [derived: mul_comm ∘ mul_neg ∘ congr]
    let nm = prove_neg_mul(c, parent, &pm_bf, &pm_y);
    let neg_by_false = c.neg(by_false.clone());
    let inner_pm = c.trans(by_true.clone(), negbf_y, neg_by_false.clone(), step_a, nm);
    // congr-right (ρ·)
    let m_rho = c.mul_right_motive(parent, rho);
    let step_b = c.congr(by_true.clone(), neg_by_false.clone(), m_rho, inner_pm);
    let rho_negby = c.mul(rho.clone(), neg_by_false.clone());
    let mn2 = c.h_mul_neg(rho, &by_false);
    let rho_by_false = c.mul(rho.clone(), by_false.clone());
    let neg_rho_by = c.neg(rho_by_false.clone());
    let inner = c.trans(
        c.mul(rho.clone(), by_true.clone()),
        rho_negby,
        neg_rho_by.clone(),
        step_b,
        mn2,
    );
    let m_one = c.add_right_motive(parent, &c.one());
    c.congr(
        c.mul(rho.clone(), by_true.clone()),
        neg_rho_by,
        m_one,
        inner,
    )
}

/// `a·b = (ρ·ρ)·(pm x · pm y)` where `a = ρ·(pm x·pm false)`, `b = ρ·(pm false·pm y)`.
///   a·b = (ρ·(pm x·pm false))·(ρ·(pm false·pm y))
///     →[mmmc ρ (pm x·pm false) ρ (pm false·pm y)]  (ρ·ρ)·((pm x·pm false)·(pm false·pm y))
///     →[inner collapse]                            (ρ·ρ)·(pm x·pm y)
///   inner: (pm x·pm false)·(pm false·pm y)
///     →[congr-right mul_comm (pm false)(pm y)]  (pm x·pm false)·(pm y·pm false)
///     →[mmmc (pm x)(pm false)(pm y)(pm false)]   (pm x·pm y)·(pm false·pm false)
///     →[congr-right pm_mul_self false]           (pm x·pm y)·1
///     →[mul_one (pm x·pm y)]                      (pm x·pm y)
fn prove_ab_eq(c: &ConvConsts, parent: &EnvDeclBuilder, rho: &Expr, x: &Expr, y: &Expr) -> Expr {
    let bf = c.bfalse.clone();
    let pm_x = c.pm(x);
    let pm_y = c.pm(y);
    let pm_bf = c.pm(&bf);
    let xb = c.mul(pm_x.clone(), pm_bf.clone()); // pm x · pm false
    let by = c.mul(pm_bf.clone(), pm_y.clone()); // pm false · pm y
    let sa = c.mul(rho.clone(), xb.clone());
    let sb = c.mul(rho.clone(), by.clone());
    let ab = c.mul(sa.clone(), sb.clone());

    // step1 mmmc ρ xb ρ by : (ρ·xb)·(ρ·by) = (ρ·ρ)·(xb·by)
    let s1 = c.h_mmmc(rho, &xb, rho, &by);
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let xb_by = c.mul(xb.clone(), by.clone());
    let after1 = c.mul(rho_sq.clone(), xb_by.clone());

    // inner collapse: xb·by = (pm x·pm false)·(pm false·pm y) → (pm x·pm y)
    let inner = prove_inner_collapse(c, parent, x, y);
    let pmxy = c.mul(pm_x.clone(), pm_y.clone());
    // congr-right (ρ·ρ)·· : (ρ·ρ)·(xb·by) = (ρ·ρ)·(pm x·pm y)
    let m = c.mul_right_motive(parent, &rho_sq);
    let s2 = c.congr(xb_by.clone(), pmxy.clone(), m, inner);
    let after2 = c.mul(rho_sq.clone(), pmxy.clone());

    c.trans(ab, after1, after2, s1, s2)
}

/// `(−a)·b = −(a·b)` derived from `mul_comm` + `mul_neg` (Rat.neg_mul is not a
/// registered standalone lemma in this build).
///   (−a)·b
///     →[mul_comm (−a) b]   b·(−a)
///     →[mul_neg b a]        −(b·a)
///     →[congr-neg mul_comm b a]   −(a·b)
fn prove_neg_mul(c: &ConvConsts, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
    let neg_a = c.neg(a.clone());
    let from = c.mul(neg_a.clone(), b.clone()); // (−a)·b
                                                // step1 mul_comm (−a) b : (−a)·b = b·(−a)
    let s1 = c.h_mul_comm(&neg_a, b);
    let b_na = c.mul(b.clone(), neg_a.clone());
    // step2 mul_neg b a : b·(−a) = −(b·a)
    let s2 = c.h_mul_neg(b, a);
    let ba = c.mul(b.clone(), a.clone());
    let neg_ba = c.neg(ba.clone());
    // step3 congr (Rat.neg ·) (mul_comm b a) : −(b·a) = −(a·b)
    let comm = c.h_mul_comm(b, a);
    let m_neg = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.neg(z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let ab = c.mul(a.clone(), b.clone());
    let neg_ab = c.neg(ab.clone());
    let s3 = c.congr(ba.clone(), ab.clone(), m_neg, comm);

    let t1 = c.trans(from.clone(), b_na, neg_ba.clone(), s1, s2);
    c.trans(from, neg_ba, neg_ab, t1, s3)
}

/// `(pm x·pm false)·(pm false·pm y) = pm x·pm y`.
fn prove_inner_collapse(c: &ConvConsts, parent: &EnvDeclBuilder, x: &Expr, y: &Expr) -> Expr {
    let bf = c.bfalse.clone();
    let pm_x = c.pm(x);
    let pm_y = c.pm(y);
    let pm_bf = c.pm(&bf);
    let xb = c.mul(pm_x.clone(), pm_bf.clone());
    let by = c.mul(pm_bf.clone(), pm_y.clone());
    let from = c.mul(xb.clone(), by.clone());

    // step1: congr-right mul_comm (pm false)(pm y) : by = pm y·pm false, under (xb · ·)
    let comm = c.h_mul_comm(&pm_bf, &pm_y);
    let yb = c.mul(pm_y.clone(), pm_bf.clone());
    let m1 = c.mul_right_motive(parent, &xb);
    let s1 = c.congr(by.clone(), yb.clone(), m1, comm);
    let after1 = c.mul(xb.clone(), yb.clone()); // (pm x·pm false)·(pm y·pm false)

    // step2: mmmc (pm x)(pm false)(pm y)(pm false) : (pm x·pm false)·(pm y·pm false) = (pm x·pm y)·(pm false·pm false)
    let s2 = c.h_mmmc(&pm_x, &pm_bf, &pm_y, &pm_bf);
    let pmxy = c.mul(pm_x.clone(), pm_y.clone());
    let bf_sq = c.mul(pm_bf.clone(), pm_bf.clone());
    let after2 = c.mul(pmxy.clone(), bf_sq.clone());

    // step3: congr-right pm_mul_self false : bf_sq = 1, under (pm x·pm y)··
    let pms = c.h_pm_mul_self(&bf);
    let m3 = c.mul_right_motive(parent, &pmxy);
    let s3 = c.congr(bf_sq.clone(), c.one(), m3, pms);
    let after3 = c.mul(pmxy.clone(), c.one());

    // step4: mul_one (pm x·pm y) : (pm x·pm y)·1 = pm x·pm y
    let s4 = c.h_mul_one(&pmxy);

    let t1 = c.trans(from.clone(), after1.clone(), after2.clone(), s1, s2);
    let t2 = c.trans(from.clone(), after2.clone(), after3.clone(), t1, s3);
    c.trans(from, after3, pmxy, t2, s4)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_noise_factor_conv_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_factor_conv()
            .expect("register_noise_factor_conv");
        env.register_noise_factor_conv().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.noiseFactor_conv");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("noiseFactor_conv proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
