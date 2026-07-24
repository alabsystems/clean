// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3, 4)` campaign — `hc43_core_step`: the induction STEP
//! `motive m → motive (m+1)` of the `(4/3,4)`-hypercontractivity operator bound,
//! the dual of the `(2,4)` `hc24_core_step` S1–S8 chain.
//!
//! The step is built CONDITIONAL on two explicit leaf hypotheses (NOT axioms):
//!
//! - **`h_cm` (cube-Minkowski / MERGE)** — the landed `NNReal.cube_minkowski_merge`
//!   shape, taken universally as a hypothesis so the fold of the two IH cube
//!   objects into one cube-of-sum may thread its cross term;
//! - **`h_tp` (two-point base)** — the per-coordinate dual-HC two-point bound
//!   (`h_tp_ty` from `hc43_core_concl`), the parallel campaign's leaf (A), taken
//!   universally so the step's S2 consumes it under the sum.
//!
//! ```text
//! BoolAnalysis.hc43_core_step :
//!   ∀ (ρ : Rat), Rat.le (3·(ρ·ρ)) 1 →
//!     H_CM → H_TP →
//!       ∀ (m : Nat), motive m → motive (m+1)
//! ```
//!
//! where `motive` is `hc43_core`'s witness-bundle predicate. This discharges the
//! LAST structural hypothesis of the M2 `(4/3,4)` core (`hc43_core`'s `h_step`):
//! once `h_cm` and `h_tp` are landed leaves, `hc43_core_step h_cm h_tp` IS the
//! `h_step` that `hc43_core` consumes.
//!
//! ## Chain (dual of `hc24_core_step` S1–S8)
//!
//! - **S1 (LHS split)** `finSumPow2SuccSplit` on `fun jx => pow4(noiseFn ρ (m+1)
//!   F jx)` + `noiseFn_succ_low/_high` rewrite the split halves to `pow4(G+ρH)` /
//!   `pow4(G−ρH)`; `finSum_ofRat` lifts the Rat sum equality to NNReal.
//! - **S2 (two-point)** `h_tp` applied per coordinate `k`, lifted by
//!   `NNReal.finSum_le`, bounds `LHS(m+1) ≤ Σ_k 4·(A_k³ + B_k³)` with
//!   `A_k := contribution(gPart …)`, `B_k := contribution(liftH …)`.
//! - **cross / fold** the cube super-additivity (`finSum_cube_split`/`cube_superadd`)
//!   collapses `Σ A_k³ ≤ (Σ A_k)³`, `Σ B_k³ ≤ (Σ B_k)³`, and the cube-Minkowski
//!   `h_cm` merges the two corners.
//! - **close** `norm43_card_succ` relates `Σ A`, `Σ B` to `norm43_{m+1}` and the
//!   `4^{m+1}` scalar is reassembled.
//!
//! See `designs/2026-06-20-hc43-dual-tensorization-cross-term.md` §11.

use super::boolean_analysis_hc43_core_base::{
    forall_lhs_nonneg_ty, forall_r_lt_one_ty, forall_r_nonneg_ty, forall_recon_ty,
    forall_scale_nonneg_ty, h_tp_ty, hc43_core_concl, hyp_contract_ty, Hc43Consts,
};
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

include!("boolean_analysis_hc43_core_step_consts.rs");
include!("boolean_analysis_hc43_core_step_leaves.rs");
include!("boolean_analysis_hc43_core_step_build.rs");
include!("boolean_analysis_hc43_core_step_v2.rs");

impl Environment {
    /// Register `BoolAnalysis.hc43_core_step` — the `m → m+1` induction step of
    /// the `(4/3,4)`-hypercontractivity operator bound, conditional on the
    /// explicit leaf hypotheses `h_cm` (cube-Minkowski) and `h_tp` (two-point
    /// base). Idempotent; axiom-free (the only leaves are landed Constructive
    /// theorems + the two explicit minor premises — no axiom in the closure).
    pub fn init_boolean_analysis_hc43_core_step(&mut self) -> Result<(), EnvError> {
        // Statement + base deps (motive surface, norm43, pow43Gen, noiseFn …).
        self.init_boolean_analysis_hc43_core_base()?;
        // Step-only landed bricks.
        self.register_finsum_cube_split()?; // BoolAnalysis.finSum_cube_split
        self.init_algebra_nnreal_cube_superadd()?; // NNReal.cube_superadd
        self.init_algebra_nnreal_le()?; // NNReal.le.trans / le.refl
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add
        self.init_algebra_nnreal_cube_mono()?; // NNReal.mul_le_mul
        self.init_algebra_nnreal_finsum_le()?; // NNReal.finSum_le
        self.init_algebra_nnreal_finsum_add()?; // NNReal.finSum_congr / finSum_add
        self.init_algebra_nnreal_finsum_ofrat()?; // NNReal.finSum_ofRat
        self.register_fin_sum_pow2_succ_split()?; // BoolAnalysis.finSumPow2SuccSplit
        self.register_noise_fn_succ()?; // noiseFn_succ_low / _high
        self.register_noise_fn_add()?; // BoolAnalysis.noiseFn_add (L7)

        let name = Name::from_string("BoolAnalysis.hc43_core_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Hc43StepConsts::new();
        let (type_, value) = build_hc43_step(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc43_core_step_leaf_types_are_props() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_core_base()
            .expect("base deps");
        env.register_finsum_cube_split().expect("cube split");
        env.init_algebra_nnreal_cube_superadd().expect("superadd");
        env.register_noise_fn_succ().expect("noise succ");
        env.register_noise_fn_add().expect("noise add");
        env.register_fin_sum_pow2_succ_split().ok();
        env.init_algebra_nnreal_finsum_le().ok();
        env.init_algebra_nnreal_finsum_add().ok();
        env.init_algebra_nnreal_finsum_ofrat().ok();
        env.init_algebra_nnreal_le().ok();
        env.init_algebra_nnreal_le_add().ok();
        env.init_algebra_nnreal_cube_mono().ok();
        let c = super::Hc43StepConsts::new();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let cm = super::h_cm_ty(&c);
        let _ = tc
            .infer_type(&cm)
            .expect("h_cm_ty must be a well-formed type");
        let full = super::build_hc43_step_ty(&c);
        let _ = tc
            .infer_type(&full)
            .expect("build_hc43_step_ty must be a well-formed type");
        let value = super::build_hc43_step_value(&c);
        tc.check_type(&value, &full)
            .expect("hc43_core_step value must check against its declared type");
    }

    #[test]
    fn test_hc43_core_step_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_core_step()
            .expect("init_boolean_analysis_hc43_core_step");
        env.init_boolean_analysis_hc43_core_step()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc43_core_step");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc43_core_step proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }

    /// `hc43_core_step_v2` closes `motive m → motive (m+1)` from the TWO-POINT
    /// BASE (A) ALONE: no `H_CM`, no opaque `H_CLOSE`. Its type is
    /// `∀ ρ, (3ρ²≤1) → H_TP_A → ∀ m, motive m → motive (m+1)` — exactly ONE leaf
    /// (the genuine two-point base, an explicit hypothesis) beyond the contraction
    /// `3ρ²≤1`. Kernel-checked, Constructive, empty axiom closure (the internal
    /// `H_CLOSE` discharge routes through the PROVEN (C) `four_le_four_pow_succ`,
    /// (D) `norm43_cubed_succ_split`, and `finSum_two_point_close` — no axiom).
    #[test]
    fn test_hc43_core_step_v2_closes_from_two_point_base_alone() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_core_step_v2()
            .expect("init_boolean_analysis_hc43_core_step_v2");
        env.init_boolean_analysis_hc43_core_step_v2()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc43_core_step_v2");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc43_core_step_v2 proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }

    /// TARGET 4 — `hc43_core` reduces to the SINGLE leaf (A): we build
    /// `fun ρ n hcontract h_tp_a => hc43_core ρ n hcontract
    ///    (hc43_core_step_v2 ρ hcontract h_tp_a)` and `check_type` it against
    /// `∀ ρ n, (3ρ²≤1) → H_TP_A → motive n`. A successful kernel `check_type`
    /// certifies that the M2 `(4/3,4)` tensorization (`hc43_core`'s `Nat.rec`),
    /// instantiated with the v2 step, needs ONLY the two-point base (A) — no
    /// `H_CM`, no `H_CLOSE`. We do NOT alter the registered `hc43_core` proof.
    #[test]
    fn test_hc43_core_from_two_point_base_alone() {
        use super::super::decl_builder::EnvDeclBuilder;
        use super::{build_hc43_step_v2_ty, step_v2_htp_universal_ty, Hc43StepConsts};
        use crate::expr::{BinderInfo, Expr};

        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_core_step_v2()
            .expect("step_v2");
        env.init_boolean_analysis_hc43_core().expect("hc43_core");

        let c = Hc43StepConsts::new();
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat());
        let (n_id, n) = b.fresh_local(c.nat());
        let hcon_ty = super::super::boolean_analysis_hc43_core_base::hyp_contract_ty(&c.o, &rho);
        let (hcon_id, hcon) = b.fresh_local(hcon_ty.clone());
        let htp_ty = step_v2_htp_universal_ty(&c, &b, &rho);
        let (htp_id, htp) = b.fresh_local(htp_ty.clone());

        // motive n (byte-for-byte hc43_core's motive_body == step_motive_body).
        let mot_n = super::step_motive_body(&c, &b, &rho, &n);

        // step := hc43_core_step_v2 ρ hcontract h_tp_a : ∀ m, motive m → motive (m+1).
        let step = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hc43_core_step_v2"), vec![]),
            [rho.clone(), hcon.clone(), htp.clone()],
        );
        // core := hc43_core ρ n hcontract step : motive n.
        let core = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hc43_core"), vec![]),
            [rho.clone(), n.clone(), hcon.clone(), step],
        );

        // term : ∀ ρ n hcontract h_tp_a, motive n.
        let term = {
            let e = b.mk_lam(htp_id, BinderInfo::Default, htp_ty.clone(), core);
            let e = b.mk_lam(hcon_id, BinderInfo::Default, hcon_ty.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat(), e);
            b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e))
        };
        let term_ty = {
            let mut tb = EnvDeclBuilder::new();
            let (rho2_id, rho2) = tb.fresh_local(c.rat());
            let (n2_id, n2) = tb.fresh_local(c.nat());
            let hcon2_ty =
                super::super::boolean_analysis_hc43_core_base::hyp_contract_ty(&c.o, &rho2);
            let (hcon2_id, _hcon2) = tb.fresh_local(hcon2_ty.clone());
            let htp2_ty = step_v2_htp_universal_ty(&c, &tb, &rho2);
            let (htp2_id, _htp2) = tb.fresh_local(htp2_ty.clone());
            let mot_n2 = super::step_motive_body(&c, &tb, &rho2, &n2);
            let e = tb.mk_pi(htp2_id, BinderInfo::Default, htp2_ty, mot_n2);
            let e = tb.mk_pi(hcon2_id, BinderInfo::Default, hcon2_ty, e);
            let e = tb.mk_pi(n2_id, BinderInfo::Default, c.nat(), e);
            tb.finish(tb.mk_pi(rho2_id, BinderInfo::Default, c.rat(), e))
        };

        // Sanity: the v2 step's full declared type is well-formed (smoke).
        let _ = build_hc43_step_v2_ty(&c);
        let _ = mot_n;

        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&term, &term_ty).expect(
            "hc43_core ∘ hc43_core_step_v2 must inhabit ∀ρ n, (3ρ²≤1) → H_TP_A → motive n \
             (M2 tensorization closes from the two-point base (A) alone)",
        );
    }

    /// LINKAGE: the §11 residual `H_CLOSE` IS discharged by the landed
    /// `BoolAnalysis.finSum_two_point_close` instance (root-free, via the
    /// `NNReal.finSum_cube_le_cube_sum` collapse). We construct the discharge term
    /// `fun (W)(h_split)(h_tp)(h_const) => finSum_two_point_close (2^m) Lo Hi W c4
    /// cN Ncubed h_split h_tp h_const` at concrete free binders and CHECK it has
    /// the function type ending in the EXACT `H_CLOSE` conclusion
    /// `nnle(split_summand_finsum, ofRat(4^{m+1})·norm43_cubed(m+1))`. A successful
    /// kernel `check_type` certifies the defeq linkage — the abstract algebraic
    /// skeleton lands on the genuine `H_CLOSE` shape, so the step needs only the
    /// three honest premises {two-point base (A), norm-split (D), constant (C)} in
    /// place of the opaque `H_CLOSE` leaf.
    #[test]
    fn test_h_close_discharged_by_two_point_close() {
        use super::super::boolean_analysis_hc43_core_base::forall_scale_nonneg_ty;
        use super::super::decl_builder::EnvDeclBuilder;
        use super::{
            forall_hi_nonneg_ty, forall_lo_nonneg_ty, split_summand_finsum, Hc43StepConsts,
        };
        use crate::expr::{BinderInfo, Expr};

        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_core_step()
            .expect("step deps");
        env.init_boolean_analysis_hc43_two_point_close()
            .expect("two_point_close");

        let c = Hc43StepConsts::new();
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat());
        let (m_id, m) = b.fresh_local(c.nat());
        let sm = c.succ(&m);
        let p2m = c.pow2(&m);
        let fin = c.fin_of(&p2m);
        let fn_ty = c.f_type(&sm);
        let (f_id, f) = b.fresh_local(fn_ty.clone());
        let (s_id, s) = b.fresh_local(fn_ty.clone());
        let (r_id, r) = b.fresh_local(fn_ty.clone());
        let hs_ty = forall_scale_nonneg_ty(&c.o, &b, &sm, &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());
        let hlo_ty = forall_lo_nonneg_ty(&c, &b, &rho, &m, &f);
        let (hlo_id, hlo) = b.fresh_local(hlo_ty.clone());
        let hhi_ty = forall_hi_nonneg_ty(&c, &b, &rho, &m, &f);
        let (hhi_id, hhi) = b.fresh_local(hhi_ty.clone());
        let h4n_ty = c.rle(&c.rat_zero(), &c.pow4n(&sm));
        let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

        // H_CLOSE LHS / RHS (byte-for-byte the leaves.rs `h_close_ty` body).
        let lhs = split_summand_finsum(&c, &b, &rho, &m, &f, &hlo, &hhi);
        let cn = c.ofrat(&c.pow4n(&sm), &h4n); // ofRat(4^{m+1})
        let ncubed = c.norm43_cubed_app(&sm, &f, &s, &r, &hs);
        let rhs = c.nnmul(&cn, &ncubed);
        let h_close_concl = c.nnle(&lhs, &rhs);

        // The two LHS leg functions Lo, Hi (the split_summand_finsum summand split).
        let leg_fn = |b: &EnvDeclBuilder, hnn: &Expr, low: bool| {
            let g_part = c.g_part_of(&m, &f);
            let lift_h = c.lift_h_of(&m, &f);
            let mut d = EnvDeclBuilder::child_of(b);
            let (k_id, k) = d.fresh_local(fin.clone());
            let g = c.noise_fn(&rho, &m, &g_part, &k);
            let hh = c.noise_fn(&rho, &m, &lift_h, &k);
            let rho_h = c.rmul(&rho, &hh);
            let leg = if low {
                c.rat_add(&g, &rho_h)
            } else {
                c.rat_sub(&g, &rho_h)
            };
            let body = c.ofrat(&c.pow4(&leg), &Expr::app(hnn.clone(), k.clone()));
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, fin.clone(), body))
        };
        let lo_fn = leg_fn(&b, &hlo, true);
        let hi_fn = leg_fn(&b, &hhi, false);

        // c4 := ofRat 4 (≥0) — the per-coordinate two-point constant.
        let four_nonneg = {
            // 0 ≤ 4 via Rat: use the same nonneg shape h4n carries at m+1? simplest:
            // reuse a fresh hypothesis-free nonneg — but 0 ≤ 4 is `Rat`-derivable.
            // We take it as a local of the right type to keep the test structural.
            c.rle(&c.rat_zero(), &c.four_rat())
        };
        let (h4_id, h4) = b.fresh_local(four_nonneg.clone());
        let c4 = c.ofrat(&c.four_rat(), &h4);

        // The three honest premises as FREE locals (typed exactly as
        // finSum_two_point_close demands at this instance).
        let nn_fn_ty = Expr::pi(BinderInfo::Default, fin.clone(), c.nnreal());
        let (w_id, w) = b.fresh_local(nn_fn_ty.clone());
        let sum_w = c.finsum(&p2m, &w);
        let cube_sum_w = c.nncube(&sum_w);
        let h_split_ty = c.eq_nn(&ncubed, &cube_sum_w);
        let (hsp_id, h_split) = b.fresh_local(h_split_ty.clone());
        let h_tp_ty = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(fin.clone());
            let lo_k = Expr::app(lo_fn.clone(), k.clone());
            let hi_k = Expr::app(hi_fn.clone(), k.clone());
            let wk = Expr::app(w.clone(), k.clone());
            let body = c.nnle(&c.nnadd(&lo_k, &hi_k), &c.nnmul(&c4, &c.nncube(&wk)));
            d.finish_child(d.mk_pi(k_id, BinderInfo::Default, fin.clone(), body))
        };
        let (htp_id, h_tp) = b.fresh_local(h_tp_ty.clone());
        let h_const_ty = c.nnle(&c4, &cn);
        let (hco_id, h_const) = b.fresh_local(h_const_ty.clone());

        // The discharge term: finSum_two_point_close (2^m) Lo Hi W c4 cN Ncubed
        //   h_split h_tp h_const  :  nnle(finSum (2^m)(λk. Lo k + Hi k))(cN·Ncubed).
        let discharge = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.finSum_two_point_close"),
                vec![],
            ),
            [
                p2m.clone(),
                lo_fn.clone(),
                hi_fn.clone(),
                w.clone(),
                c4.clone(),
                cn.clone(),
                ncubed.clone(),
                h_split.clone(),
                h_tp.clone(),
                h_const.clone(),
            ],
        );

        // The EXACT H_CLOSE conclusion (byte-for-byte the leaves.rs `h_close_ty`
        // body) is the target the discharge must inhabit.
        let body_ty = c.nnle(&lhs, &rhs);
        assert_eq!(
            body_ty, h_close_concl,
            "the checked conclusion must be byte-for-byte H_CLOSE"
        );

        // Abstract the FULL telescope so both the term and its type are closed:
        //   type  : ∀ ρ m F s r hs hlo hhi h4n h4 W h_split h_tp h_const, H_CLOSE
        //   term  : fun (same binders) => <finSum_two_point_close instance>.
        // A successful `check_type` certifies the instance's type is defeq to
        // `H_CLOSE` under every binder.
        let close_ty = {
            let e = b.mk_pi(
                hco_id,
                BinderInfo::Default,
                h_const_ty.clone(),
                body_ty.clone(),
            );
            let e = b.mk_pi(htp_id, BinderInfo::Default, h_tp_ty.clone(), e);
            let e = b.mk_pi(hsp_id, BinderInfo::Default, h_split_ty.clone(), e);
            let e = b.mk_pi(w_id, BinderInfo::Default, nn_fn_ty.clone(), e);
            let e = b.mk_pi(h4_id, BinderInfo::Default, four_nonneg.clone(), e);
            let e = b.mk_pi(h4n_id, BinderInfo::Default, h4n_ty.clone(), e);
            let e = b.mk_pi(hhi_id, BinderInfo::Default, hhi_ty.clone(), e);
            let e = b.mk_pi(hlo_id, BinderInfo::Default, hlo_ty.clone(), e);
            let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty.clone(), e);
            let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat(), e);
            b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e)
        };
        let close_term = {
            let e = b.mk_lam(hco_id, BinderInfo::Default, h_const_ty.clone(), discharge);
            let e = b.mk_lam(htp_id, BinderInfo::Default, h_tp_ty.clone(), e);
            let e = b.mk_lam(hsp_id, BinderInfo::Default, h_split_ty.clone(), e);
            let e = b.mk_lam(w_id, BinderInfo::Default, nn_fn_ty.clone(), e);
            let e = b.mk_lam(h4_id, BinderInfo::Default, four_nonneg.clone(), e);
            let e = b.mk_lam(h4n_id, BinderInfo::Default, h4n_ty.clone(), e);
            let e = b.mk_lam(hhi_id, BinderInfo::Default, hhi_ty.clone(), e);
            let e = b.mk_lam(hlo_id, BinderInfo::Default, hlo_ty.clone(), e);
            let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty.clone(), e);
            let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat(), e);
            b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e))
        };
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&close_term, &close_ty).expect(
            "finSum_two_point_close instance must inhabit the H_CLOSE conclusion (defeq linkage)",
        );
    }
}
