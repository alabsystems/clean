// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3,4)` campaign — `BoolAnalysis.finSum_two_point_close`: the
//! ALGEBRAIC discharge of the `(4/3,4)` dual-HC tensorization residual `H_CLOSE`
//! (design `2026-06-20-hc43-dual-tensorization-cross-term.md` §11), proved
//! ROOT-FREE from the correct single-cube two-point base + the finSum cube
//! collapse + the norm-split identity.
//!
//! # What this resolves (the §11 sqrt-free route)
//!
//! `H_CLOSE` (the §11 residual) is, after the genuine S1 LHS-reshape:
//!
//! ```text
//!   Σ_k (ofRat(pow4 lo_k) + ofRat(pow4 hi_k))  ≤  ofRat(4^{m+1}) · norm43_cubed(m+1)
//! ```
//!
//! `norm43_cubed(m+1) = (norm43_{m+1})³ = (Σ_k W_k)³` is the CUBE of a SINGLE
//! finSum (NOT the ℓ³-separated `(‖·‖₃)³`). So the discharge does NOT need the
//! `NNReal.cube_minkowski` MERGE (which is the ℓ³-SEPARATED `U³ ≤ S²·T` tool) — it
//! needs the ROOT-FREE finSum cube COLLAPSE `Σ_k W_k³ ≤ (Σ_k W_k)³`
//! (`NNReal.finSum_cube_le_cube_sum`, landed). This theorem is the abstract
//! algebraic skeleton of that discharge, over abstract per-coordinate legs so it
//! is reusable and free of the noiseFn/norm43 surface:
//!
//! ```text
//!   BoolAnalysis.finSum_two_point_close :
//!     ∀ (n : Nat) (Lo Hi W : Fin n → NNReal) (c4 cN Ncubed : NNReal)
//!       (h_split : Ncubed = ((Σ W)·(Σ W))·(Σ W))                    -- (D) norm-split
//!       (h_tp    : ∀ k, NNReal.le (Lo k + Hi k) (c4 · ((W k · W k)· W k)))  -- (A) two-point
//!       (h_const : NNReal.le c4 cN),                                -- (C) constant
//!       NNReal.le (NNReal.finSum n (fun k => Lo k + Hi k))
//!                 (NNReal.mul cN Ncubed)
//! ```
//!
//! Instantiating at `n := 2^m`, `Lo k := ofRat(pow4 lo_k)`, `Hi k :=
//! ofRat(pow4 hi_k)`, `W k :=` the two `norm43_{m+1}` half-contributions summed,
//! `c4 := ofRat 4`, `cN := ofRat(4^{m+1})`, `Ncubed := norm43_cubed(m+1)`, this IS
//! `H_CLOSE` — discharged conditional on the THREE honest minor premises (A) the
//! correct single-cube two-point base (the parallel campaign's leaf), (D) the
//! norm-split identity `norm43_{m+1} = Σ_k W_k` (an NNReal `2^{m+1}=2^m+2^m`
//! reindex, the structural residual), and (C) the trivial constant `4 ≤ 4^{m+1}`.
//!
//! # Proof (axiom-free, root-free)
//!
//! ```text
//!   Σ(Lo+Hi) ≤[finSum_le h_tp]      Σ(fun k => c4·W_k³)
//!            =[finSum_smul]          c4·Σ(W³)
//!            ≤[mul_le_mul · collapse] c4·(ΣW)³
//!            ≤[mul_le_mul h_const]   cN·(ΣW)³
//!            =[h_split (symm), subst] cN·Ncubed.
//! ```
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Declaration::Axiom`.

use super::algebra_nnreal_finsum::NNFinSumConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `finSum_two_point_close`.
struct TwoPointCloseConsts {
    base: NNFinSumConsts,
    l1: Level,
    nnreal_mul: Expr,
    nnreal_le: Expr,
    nnreal_le_refl: Expr,
    nnreal_le_trans: Expr,
    nnreal_mul_le_mul: Expr,
    nnreal_finsum_le: Expr,
    nnreal_finsum_smul: Expr,
    nnreal_finsum_cube: Expr,
}

impl TwoPointCloseConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            base: NNFinSumConsts::new(),
            l1: Level::succ(Level::zero()),
            nnreal_mul: k("NNReal.mul"),
            nnreal_le: k("NNReal.le"),
            nnreal_le_refl: k("NNReal.le.refl"),
            nnreal_le_trans: k("NNReal.le.trans"),
            nnreal_mul_le_mul: k("NNReal.mul_le_mul"),
            nnreal_finsum_le: k("NNReal.finSum_le"),
            nnreal_finsum_smul: k("NNReal.finSum_smul"),
            nnreal_finsum_cube: k("NNReal.finSum_cube_le_cube_sum"),
        }
    }

    fn nat(&self) -> Expr {
        self.base.nat.clone()
    }
    fn nnreal(&self) -> Expr {
        self.base.nnreal.clone()
    }
    fn fin(&self, n: &Expr) -> Expr {
        Expr::app(self.base.fin.clone(), n.clone())
    }
    fn fin_to_nnreal(&self, n: &Expr) -> Expr {
        self.base.fin_to_nnreal(n.clone())
    }
    fn sum(&self, n: &Expr, f: &Expr) -> Expr {
        self.base.sum(n.clone(), f.clone())
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        self.base.add(a.clone(), b.clone())
    }
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn cube(&self, a: &Expr) -> Expr {
        self.mul(&self.mul(a, a), a)
    }
    fn le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    fn le_refl(&self, a: &Expr) -> Expr {
        Expr::app(self.nnreal_le_refl.clone(), a.clone())
    }
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn mul_le_mul(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_le_mul.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.finSum_le n f g h`.
    fn finsum_le(&self, n: &Expr, f: &Expr, g: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_finsum_le.clone(),
            [n.clone(), f.clone(), g.clone(), h],
        )
    }
    /// `NNReal.finSum_smul n c f : finSum n (fun i => c·(f i)) = c·(finSum n f)`.
    fn finsum_smul(&self, n: &Expr, c: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_finsum_smul.clone(),
            [n.clone(), c.clone(), f.clone()],
        )
    }
    /// `NNReal.finSum_cube_le_cube_sum n W : finSum n (cube∘W) ≤ (finSum n W)³`.
    fn finsum_cube(&self, n: &Expr, w: &Expr) -> Expr {
        Expr::apps(self.nnreal_finsum_cube.clone(), [n.clone(), w.clone()])
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.nnreal(), a.clone(), b.clone()],
        )
    }
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.nnreal(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.subst NNReal motive a b h_eq h : motive b` (motive lands in Prop).
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.nnreal(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }

    /// `fun (k : Fin n) => Lo k + Hi k` — the LHS per-coordinate summand.
    fn lo_plus_hi_fn(&self, parent: &EnvDeclBuilder, n: &Expr, lo: &Expr, hi: &Expr) -> Expr {
        let fin_n = self.fin(n);
        let mut b = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = b.fresh_local(fin_n.clone());
        let body = self.add(&Expr::app(lo.clone(), k.clone()), &Expr::app(hi.clone(), k));
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (k : Fin n) => c4 · ((W k · W k)· W k)` — the bound per-coordinate
    /// summand (the `scaled c4 (cube∘W)` shape `finSum_smul` consumes).
    fn scaled_cube_fn(&self, parent: &EnvDeclBuilder, n: &Expr, c4: &Expr, w: &Expr) -> Expr {
        let fin_n = self.fin(n);
        let mut b = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = b.fresh_local(fin_n.clone());
        let wk = Expr::app(w.clone(), k.clone());
        let body = self.mul(c4, &self.cube(&wk));
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (k : Fin n) => ((W k · W k)· W k)` — the bare `cube∘W` summand.
    fn cube_fn(&self, parent: &EnvDeclBuilder, n: &Expr, w: &Expr) -> Expr {
        let fin_n = self.fin(n);
        let mut b = EnvDeclBuilder::child_of(parent);
        let (k_id, k) = b.fresh_local(fin_n.clone());
        let wk = Expr::app(w.clone(), k.clone());
        let body = self.cube(&wk);
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin_n, body))
    }
}

impl Environment {
    /// Register `BoolAnalysis.finSum_two_point_close`. Idempotent;
    /// foundational-only closure.
    pub fn init_boolean_analysis_hc43_two_point_close(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_finsum()?; // NNReal.finSum
        self.init_algebra_nnreal_le()?; // NNReal.le.refl / le.trans
        self.init_algebra_nnreal_cube_mono()?; // NNReal.mul_le_mul
        self.init_algebra_nnreal_finsum_le()?; // NNReal.finSum_le
        self.init_algebra_nnreal_finsum_smul()?; // NNReal.finSum_smul
        self.init_algebra_nnreal_finsum_cube()?; // NNReal.finSum_cube_le_cube_sum
        self.init_eq()?;

        let name = Name::from_string("BoolAnalysis.finSum_two_point_close");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = TwoPointCloseConsts::new();
        let (ty, value) = build_two_point_close(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ n Lo Hi W c4 cN Ncubed, h_split → h_tp → h_const → <close>`.
fn build_two_point_close_type(c: &TwoPointCloseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let fn_ty = c.fin_to_nnreal(&n);
    let (lo_id, lo) = b.fresh_local(fn_ty.clone());
    let (hi_id, hi) = b.fresh_local(fn_ty.clone());
    let (w_id, w) = b.fresh_local(fn_ty.clone());
    let (c4_id, c4) = b.fresh_local(c.nnreal());
    let (cn_id, cn) = b.fresh_local(c.nnreal());
    let (nc_id, nc) = b.fresh_local(c.nnreal());

    let sum_w = c.sum(&n, &w);
    let cube_sum_w = c.cube(&sum_w);

    // h_split : Ncubed = (Σ W)³.
    let h_split_ty = c.eq_nn(&nc, &cube_sum_w);
    let (hs_id, _hs) = b.fresh_local(h_split_ty.clone());

    // h_tp : ∀ k, (Lo k + Hi k) ≤ c4·(W k)³.
    let h_tp_ty = forall_two_point_ty(c, &b, &n, &lo, &hi, &w, &c4);
    let (htp_id, _htp) = b.fresh_local(h_tp_ty.clone());

    // h_const : c4 ≤ cN.
    let h_const_ty = c.le(&c4, &cn);
    let (hc_id, _hc) = b.fresh_local(h_const_ty.clone());

    // conclusion : Σ(Lo+Hi) ≤ cN·Ncubed.
    let lhs = c.sum(&n, &c.lo_plus_hi_fn(&b, &n, &lo, &hi));
    let rhs = c.mul(&cn, &nc);
    let concl = c.le(&lhs, &rhs);

    let e = b.mk_pi(hc_id, BinderInfo::Default, h_const_ty, concl);
    let e = b.mk_pi(htp_id, BinderInfo::Default, h_tp_ty, e);
    let e = b.mk_pi(hs_id, BinderInfo::Default, h_split_ty, e);
    let e = b.mk_pi(nc_id, BinderInfo::Default, c.nnreal(), e);
    let e = b.mk_pi(cn_id, BinderInfo::Default, c.nnreal(), e);
    let e = b.mk_pi(c4_id, BinderInfo::Default, c.nnreal(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(hi_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(lo_id, BinderInfo::Default, fn_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat(), e))
}

/// `∀ (k : Fin n), NNReal.le (Lo k + Hi k) (c4 · ((W k · W k)· W k))`.
fn forall_two_point_ty(
    c: &TwoPointCloseConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    lo: &Expr,
    hi: &Expr,
    w: &Expr,
    c4: &Expr,
) -> Expr {
    let fin_n = c.fin(n);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin_n.clone());
    let lhs = c.add(
        &Expr::app(lo.clone(), k.clone()),
        &Expr::app(hi.clone(), k.clone()),
    );
    let wk = Expr::app(w.clone(), k.clone());
    let rhs = c.mul(c4, &c.cube(&wk));
    let body = c.le(&lhs, &rhs);
    b.finish_child(b.mk_pi(k_id, BinderInfo::Default, fin_n, body))
}

/// The proof term.
fn build_two_point_close_value(c: &TwoPointCloseConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat());
    let fn_ty = c.fin_to_nnreal(&n);
    let (lo_id, lo) = b.fresh_local(fn_ty.clone());
    let (hi_id, hi) = b.fresh_local(fn_ty.clone());
    let (w_id, w) = b.fresh_local(fn_ty.clone());
    let (c4_id, c4) = b.fresh_local(c.nnreal());
    let (cn_id, cn) = b.fresh_local(c.nnreal());
    let (nc_id, nc) = b.fresh_local(c.nnreal());
    let h_split_ty = {
        let sum_w = c.sum(&n, &w);
        c.eq_nn(&nc, &c.cube(&sum_w))
    };
    let (hs_id, hs) = b.fresh_local(h_split_ty.clone());
    let h_tp_ty = forall_two_point_ty(c, &b, &n, &lo, &hi, &w, &c4);
    let (htp_id, htp) = b.fresh_local(h_tp_ty.clone());
    let h_const_ty = c.le(&c4, &cn);
    let (hc_id, hconst) = b.fresh_local(h_const_ty.clone());

    // Named summand functions.
    let lo_hi = c.lo_plus_hi_fn(&b, &n, &lo, &hi); // fun k => Lo k + Hi k
    let scaled_cube = c.scaled_cube_fn(&b, &n, &c4, &w); // fun k => c4·(W k)³
    let cube_w = c.cube_fn(&b, &n, &w); // fun k => (W k)³

    let sum_lo_hi = c.sum(&n, &lo_hi);
    let sum_scaled = c.sum(&n, &scaled_cube);
    let sum_cube = c.sum(&n, &cube_w);
    let sum_w = c.sum(&n, &w);
    let cube_sum_w = c.cube(&sum_w);

    // (1) finSum_le : Σ(Lo+Hi) ≤ Σ(c4·W³).  pointwise proof = htp.
    let step1 = c.finsum_le(&n, &lo_hi, &scaled_cube, htp.clone());

    // (2) finSum_smul n c4 (cube∘W) : Σ(c4·W³) = c4·(Σ W³).
    let smul = c.finsum_smul(&n, &c4, &cube_w);
    let c4_sum_cube = c.mul(&c4, &sum_cube);

    // (3) collapse : Σ W³ ≤ (Σ W)³.
    let collapse = c.finsum_cube(&n, &w);
    // mul_le_mul c4 c4 (Σ W³)((Σ W)³)(le.refl c4)(collapse) : c4·(Σ W³) ≤ c4·(Σ W)³.
    let c4_cube_sum_w = c.mul(&c4, &cube_sum_w);
    let step3 = c.mul_le_mul(&c4, &c4, &sum_cube, &cube_sum_w, c.le_refl(&c4), collapse);

    // (4) mul_le_mul c4 cN ((Σ W)³)((Σ W)³) h_const (le.refl) : c4·(Σ W)³ ≤ cN·(Σ W)³.
    let cn_cube_sum_w = c.mul(&cn, &cube_sum_w);
    let step4 = c.mul_le_mul(
        &c4,
        &cn,
        &cube_sum_w,
        &cube_sum_w,
        hconst,
        c.le_refl(&cube_sum_w),
    );

    // Chain the inequalities.
    //  a : Σ(Lo+Hi) ≤ c4·(Σ W³)    -- step1 with RHS rewritten by smul (subst).
    // Rewrite Σ(c4·W³) → c4·(Σ W³) in step1's RHS via subst along smul.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nnreal());
        let body = c.le(&sum_lo_hi, &t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nnreal(), body))
    };
    // step1 : le sum_lo_hi sum_scaled ;  smul : sum_scaled = c4·(Σ W³).
    let a = c.subst_nn(motive_a, &sum_scaled, &c4_sum_cube, smul, step1);

    // b : Σ(Lo+Hi) ≤ c4·(Σ W)³   via le.trans a step3.
    let bproof = c.le_trans(&sum_lo_hi, &c4_sum_cube, &c4_cube_sum_w, a, step3);

    // d : Σ(Lo+Hi) ≤ cN·(Σ W)³   via le.trans b step4.
    let dproof = c.le_trans(&sum_lo_hi, &c4_cube_sum_w, &cn_cube_sum_w, bproof, step4);

    // e : Σ(Lo+Hi) ≤ cN·Ncubed   via subst the RHS (Σ W)³ → Ncubed along symm h_split.
    //   h_split : Ncubed = (Σ W)³, so symm : (Σ W)³ = Ncubed.
    let motive_e = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nnreal());
        let body = c.le(&sum_lo_hi, &c.mul(&cn, &t));
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nnreal(), body))
    };
    let proof = c.subst_nn(
        motive_e,
        &cube_sum_w,
        &nc,
        c.symm_nn(&nc, &cube_sum_w, hs),
        dproof,
    );

    let e = b.mk_lam(hc_id, BinderInfo::Default, h_const_ty, proof);
    let e = b.mk_lam(htp_id, BinderInfo::Default, h_tp_ty, e);
    let e = b.mk_lam(hs_id, BinderInfo::Default, h_split_ty, e);
    let e = b.mk_lam(nc_id, BinderInfo::Default, c.nnreal(), e);
    let e = b.mk_lam(cn_id, BinderInfo::Default, c.nnreal(), e);
    let e = b.mk_lam(c4_id, BinderInfo::Default, c.nnreal(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(hi_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(lo_id, BinderInfo::Default, fn_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat(), e))
}

fn build_two_point_close(c: &TwoPointCloseConsts) -> (Expr, Expr) {
    (
        build_two_point_close_type(c),
        build_two_point_close_value(c),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_two_point_close()
            .expect("init_boolean_analysis_hc43_two_point_close");
        env.init_boolean_analysis_hc43_two_point_close()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_finsum_two_point_close_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("BoolAnalysis.finSum_two_point_close");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_).unwrap_or_else(|e| {
            panic!("BoolAnalysis.finSum_two_point_close must kernel-check: {e:?}")
        });
    }

    #[test]
    fn test_finsum_two_point_close_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.finSum_two_point_close");
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
