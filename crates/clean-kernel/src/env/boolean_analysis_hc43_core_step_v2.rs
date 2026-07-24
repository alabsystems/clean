// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// `BoolAnalysis.hc43_core_step_v2` — the §11.1 induction STEP closing
// `motive m → motive (m+1)` from the TWO-POINT BASE (A) ALONE (no opaque
// `H_CLOSE`, no `H_CM` cube-Minkowski). The residual `H_CLOSE` is discharged
// INTERNALLY by `BoolAnalysis.finSum_two_point_close` instantiated with the now
// PROVEN premises (D) `BoolAnalysis.norm43_cubed_succ_split` and (C)
// `BoolAnalysis.four_le_four_pow_succ`, leaving only the genuine two-point base
// (A) as an explicit hypothesis (the parallel campaign's leaf). `include!`d into
// `boolean_analysis_hc43_core_step.rs`.
//
// Type:
//   ∀ (ρ : Rat), Rat.le (3·(ρ·ρ)) 1 → H_TP_A → ∀ (m : Nat), motive m → motive (m+1)
//
// where H_TP_A (the (A) leaf) is the per-coordinate SINGLE-CUBE two-point bound
//   ∀ m (F s r : HCPoint (m+1) → Rat)(hs : ∀ x, 0 ≤ s x)
//     (hlo : ∀ k, 0 ≤ pow4 (G k + ρ·H k))(hhi : ∀ k, 0 ≤ pow4 (G k − ρ·H k)),
//     ∀ k : Fin (2^m),
//       NNReal.le (ofRat(pow4 lo_k) (hlo k) + ofRat(pow4 hi_k) (hhi k))
//                 (NNReal.mul (ofRat 4 _) (W_k · W_k · W_k))
//   with W := `norm43_merged_w` (the EXACT `W` premise (D) pins). This is the
//   genuine leaf (A) — NOT built/faked here; it is the parallel campaign's lane.

/// `fun (k : Fin (2^m)) => NNReal.ofRat (pow4 (G k + ρ·H k)) (hlo k)` (low) /
/// `… (G k − ρ·H k) (hhi k)` (high) — the two legs `split_summand_finsum` adds.
/// Byte-for-byte the legs the §11.1 linkage `leg_fn` pins.
fn step_v2_leg_fn(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    m: &Expr,
    f: &Expr,
    hnn: &Expr,
    low: bool,
) -> Expr {
    let p2m = c.pow2(m);
    let fin = c.fin_of(&p2m);
    let g_part = c.g_part_of(m, f);
    let lift_h = c.lift_h_of(m, f);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = d.fresh_local(fin.clone());
    let g = c.noise_fn(rho, m, &g_part, &k);
    let hh = c.noise_fn(rho, m, &lift_h, &k);
    let rho_h = c.rmul(rho, &hh);
    let leg = if low {
        c.rat_add(&g, &rho_h)
    } else {
        c.rat_sub(&g, &rho_h)
    };
    let body = c.ofrat(&c.pow4(&leg), &Expr::app(hnn.clone(), k.clone()));
    d.finish_child(d.mk_lam(k_id, BinderInfo::Default, fin, body))
}

/// The per-coordinate (A) body at fixed `(ρ, m, F, s, r, hs, hlo, hhi)`:
/// `∀ k : Fin (2^m), nnle(lo_fn k + hi_fn k)(ofRat 4 · (W k)³)`. This is exactly
/// what `finSum_two_point_close`'s `h_tp` premise demands at the `H_CLOSE`
/// instance — and exactly the `H_TP_A` universal body.
#[allow(clippy::too_many_arguments)]
fn step_v2_htp_body(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    m: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
    hlo: &Expr,
    hhi: &Expr,
) -> Expr {
    let p2m = c.pow2(m);
    let fin = c.fin_of(&p2m);
    let lo_fn = step_v2_leg_fn(c, parent, rho, m, f, hlo, true);
    let hi_fn = step_v2_leg_fn(c, parent, rho, m, f, hhi, false);
    let w = super::boolean_analysis_hc43_norm_split::norm43_merged_w(parent, m, f, s, r, hs);
    let h4 = super::boolean_analysis_hc43_four_le_pow::four_rat_zero_le();
    let c4 = c.ofrat(&c.four_rat(), &h4);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = d.fresh_local(fin.clone());
    let lo_k = Expr::app(lo_fn.clone(), k.clone());
    let hi_k = Expr::app(hi_fn.clone(), k.clone());
    let wk = Expr::app(w.clone(), k.clone());
    let body = c.nnle(&c.nnadd(&lo_k, &hi_k), &c.nnmul(&c4, &c.nncube(&wk)));
    d.finish_child(d.mk_pi(k_id, BinderInfo::Default, fin, body))
}

/// `H_TP_A` — the (A) leaf, universally quantified over `(m, F, s, r, hs, hlo,
/// hhi)`. `F s r : HCPoint (m+1) → Rat`; `hlo`/`hhi` the pow4-nonneg witnesses.
fn step_v2_htp_universal_ty(c: &Hc43StepConsts, parent: &EnvDeclBuilder, rho: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = b.fresh_local(c.nat());
    let sm = c.succ(&m);
    let fn_ty = c.f_type(&sm);
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let (s_id, s) = b.fresh_local(fn_ty.clone());
    let (r_id, r) = b.fresh_local(fn_ty.clone());
    let hs_ty = forall_scale_nonneg_ty(&c.o, &b, &sm, &s);
    let (hs_id, hs) = b.fresh_local(hs_ty.clone());
    let hlo_ty = forall_lo_nonneg_ty(c, &b, rho, &m, &f);
    let (hlo_id, hlo) = b.fresh_local(hlo_ty.clone());
    let hhi_ty = forall_hi_nonneg_ty(c, &b, rho, &m, &f);
    let (hhi_id, hhi) = b.fresh_local(hhi_ty.clone());

    let body = step_v2_htp_body(c, &b, rho, &m, &f, &s, &r, &hs, &hlo, &hhi);

    let e = b.mk_pi(hhi_id, BinderInfo::Default, hhi_ty, body);
    let e = b.mk_pi(hlo_id, BinderInfo::Default, hlo_ty, e);
    let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
    let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
    b.finish_child(b.mk_pi(m_id, BinderInfo::Default, c.nat(), e))
}

/// Build the `motive (m+1)` conclusion body for v2: S1 reshape, then the
/// INTERNAL `finSum_two_point_close` discharge from {(D), (A)=h_tp_a, (C)}.
fn build_step_concl_v2(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    ctx: &StepCtx,
    h_tp_a: &Expr,
) -> Expr {
    let sm = c.succ(&ctx.m);
    let p2m = c.pow2(&ctx.m);

    let lhs_nn = {
        let summand = lhs_nn_summand(c, parent, ctx);
        c.finsum(&c.pow2(&sm), &summand)
    };
    let cn = c.ofrat(&c.pow4n(&sm), &ctx.h4n);
    let ncubed = c.norm43_cubed_app(&sm, &ctx.f, &ctx.s, &ctx.r, &ctx.hs);
    let rhs = c.nnmul(&cn, &ncubed);

    // pow4-nonneg witnesses (same as the v1 body).
    let hlo = build_lo_nonneg(c, parent, ctx);
    let hhi = build_hi_nonneg(c, parent, ctx);

    // S1 : lhs_nn = split_summand_finsum.
    let split_fs = split_summand_finsum(c, parent, &ctx.rho, &ctx.m, &ctx.f, &hlo, &hhi);
    let s1 = build_s1(c, parent, ctx, &lhs_nn, &split_fs, &hlo, &hhi);

    // ── construct H_CLOSE internally via finSum_two_point_close ──
    let lo_fn = step_v2_leg_fn(c, parent, &ctx.rho, &ctx.m, &ctx.f, &hlo, true);
    let hi_fn = step_v2_leg_fn(c, parent, &ctx.rho, &ctx.m, &ctx.f, &hhi, false);
    let w = super::boolean_analysis_hc43_norm_split::norm43_merged_w(
        parent, &ctx.m, &ctx.f, &ctx.s, &ctx.r, &ctx.hs,
    );
    let h4 = super::boolean_analysis_hc43_four_le_pow::four_rat_zero_le();
    let c4 = c.ofrat(&c.four_rat(), &h4);

    // (D) h_split : Ncubed = (Σ W)³   =  norm43_cubed_succ_split m F s r hs.
    let h_split = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.norm43_cubed_succ_split"),
            vec![],
        ),
        [
            ctx.m.clone(),
            ctx.f.clone(),
            ctx.s.clone(),
            ctx.r.clone(),
            ctx.hs.clone(),
        ],
    );

    // (C) h_const : c4 ≤ cN   =  four_le_four_pow_succ m h4 h4n.
    let h_const = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.four_le_four_pow_succ"),
            vec![],
        ),
        [ctx.m.clone(), h4.clone(), ctx.h4n.clone()],
    );

    // (A) h_tp : ∀ k, (lo_fn k + hi_fn k) ≤ c4·(W k)³  =  h_tp_a m F s r hs hlo hhi.
    let h_tp = Expr::apps(
        h_tp_a.clone(),
        [
            ctx.m.clone(),
            ctx.f.clone(),
            ctx.s.clone(),
            ctx.r.clone(),
            ctx.hs.clone(),
            hlo.clone(),
            hhi.clone(),
        ],
    );

    // discharge : Σ_k (lo_fn k + hi_fn k) ≤ cN·Ncubed  =  split_fs ≤ rhs.
    let close = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.finSum_two_point_close"),
            vec![],
        ),
        [
            p2m.clone(),
            lo_fn,
            hi_fn,
            w,
            c4,
            cn,
            ncubed,
            h_split,
            h_tp,
            h_const,
        ],
    );

    // subst along (S1 : lhs_nn = split_fs) : lhs_nn ≤ rhs.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(c.nnreal());
        let body = c.nnle(&w, &rhs);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal(), body))
    };
    c.subst_nn_prop(
        motive,
        &split_fs,
        &lhs_nn,
        c.symm_nn(&lhs_nn, &split_fs, s1),
        close,
    )
}

/// Full `hc43_core_step_v2` TYPE:
/// `∀ ρ, (3ρ²≤1) → H_TP_A → ∀ m, motive m → motive (m+1)`.
fn build_hc43_step_v2_ty(c: &Hc43StepConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let h_ty = hyp_contract_ty(&c.o, &rho);
    let (h_id, _h) = b.fresh_local(h_ty.clone());
    let htp_ty = step_v2_htp_universal_ty(c, &b, &rho);
    let (htp_id, _htp) = b.fresh_local(htp_ty.clone());

    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = d.fresh_local(c.nat());
        let mot_m = step_motive_body(c, &d, &rho, &m);
        let sm = c.succ(&m);
        let mot_sm = step_motive_body(c, &d, &rho, &sm);
        let arrow = {
            let mut e2 = EnvDeclBuilder::child_of(&d);
            let (ih_id, _ih) = e2.fresh_local(mot_m.clone());
            e2.finish_child(e2.mk_pi(ih_id, BinderInfo::Default, mot_m.clone(), mot_sm))
        };
        d.finish_child(d.mk_pi(m_id, BinderInfo::Default, c.nat(), arrow))
    };

    let e = b.mk_pi(htp_id, BinderInfo::Default, htp_ty, step);
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
    b.finish(b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e))
}

/// Full `hc43_core_step_v2` VALUE.
fn build_hc43_step_v2_value(c: &Hc43StepConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let h_ty = hyp_contract_ty(&c.o, &rho);
    let (h_id, h) = b.fresh_local(h_ty.clone());
    let htp_ty = step_v2_htp_universal_ty(c, &b, &rho);
    let (htp_id, h_tp_a) = b.fresh_local(htp_ty.clone());
    let (m_id, m) = b.fresh_local(c.nat());
    let mot_m = step_motive_body(c, &b, &rho, &m);
    let (ih_id, ih) = b.fresh_local(mot_m.clone());

    let sm = c.succ(&m);
    let fn_ty = c.f_type(&sm);
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let (s_id, s) = b.fresh_local(fn_ty.clone());
    let (r_id, r) = b.fresh_local(fn_ty.clone());
    let hs_ty = forall_scale_nonneg_ty(&c.o, &b, &sm, &s);
    let (hs_id, hs) = b.fresh_local(hs_ty.clone());
    let hr_ty = forall_r_nonneg_ty(&c.o, &b, &sm, &r);
    let (hr_id, hr) = b.fresh_local(hr_ty.clone());
    let hr1_ty = forall_r_lt_one_ty(&c.o, &b, &sm, &r);
    let (hr1_id, hr1) = b.fresh_local(hr1_ty.clone());
    let hrecon_ty = forall_recon_ty(&c.o, &b, &sm, &f, &s, &r);
    let (hrecon_id, hrecon) = b.fresh_local(hrecon_ty.clone());
    let hnn_ty = forall_lhs_nonneg_ty(&c.o, &b, &rho, &sm, &f);
    let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
    let h4n_ty = c.rle(&c.rat_zero(), &c.pow4n(&sm));
    let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

    let ctx = StepCtx {
        rho: rho.clone(),
        h: h.clone(),
        h_cm: h.clone(),      // unused in v2 (no cube-Minkowski) — placeholder.
        h_tp: h_tp_a.clone(), // unused via ctx (threaded explicitly below).
        h_close: h.clone(),   // unused in v2 (constructed internally) — placeholder.
        m: m.clone(),
        ih: ih.clone(),
        f: f.clone(),
        s: s.clone(),
        r: r.clone(),
        hs: hs.clone(),
        hr: hr.clone(),
        hr1: hr1.clone(),
        hrecon: hrecon.clone(),
        hnn: hnn.clone(),
        h4n: h4n.clone(),
    };

    let body = build_step_concl_v2(c, &b, &ctx, &h_tp_a);

    // Re-abstract the motive (m+1) telescope.
    let e = b.mk_lam(h4n_id, BinderInfo::Default, h4n_ty, body);
    let e = b.mk_lam(hnn_id, BinderInfo::Default, hnn_ty, e);
    let e = b.mk_lam(hrecon_id, BinderInfo::Default, hrecon_ty, e);
    let e = b.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, e);
    let e = b.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
    let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
    let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
    let e = b.mk_lam(ih_id, BinderInfo::Default, mot_m, e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat(), e);
    let e = b.mk_lam(htp_id, BinderInfo::Default, htp_ty, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, e);
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e))
}

fn build_hc43_step_v2(c: &Hc43StepConsts) -> (Expr, Expr) {
    (build_hc43_step_v2_ty(c), build_hc43_step_v2_value(c))
}

impl Environment {
    /// Register `BoolAnalysis.hc43_core_step_v2` — the §11.1 step closing
    /// `motive m → motive (m+1)` from the TWO-POINT BASE (A) ALONE (`H_TP_A`),
    /// discharging `H_CLOSE` internally from the PROVEN (D) `norm43_cubed_succ_split`
    /// and (C) `four_le_four_pow_succ`. No `H_CM`, no opaque `H_CLOSE`. Idempotent;
    /// axiom-free (closure = S1 leaves + finSum_two_point_close + (C) + (D) + the
    /// explicit (A) premise — no axiom).
    pub fn init_boolean_analysis_hc43_core_step_v2(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_hc43_core_step()?; // S1 bricks + statement deps
        self.init_boolean_analysis_hc43_two_point_close()?; // finSum_two_point_close
        self.init_boolean_analysis_hc43_norm_split()?; // (D) norm43_cubed_succ_split
        self.init_boolean_analysis_hc43_four_le_pow()?; // (C) four_le_four_pow_succ

        let name = Name::from_string("BoolAnalysis.hc43_core_step_v2");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Hc43StepConsts::new();
        let (type_, value) = build_hc43_step_v2(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}
