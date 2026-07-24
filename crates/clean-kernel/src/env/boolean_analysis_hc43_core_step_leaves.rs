// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Type builders for `hc43_core_step`: the `motive` predicate (mirroring
// `boolean_analysis_hc43_core_motive.rs`), and the two explicit leaf-hypothesis
// types `H_CM` (cube-Minkowski / MERGE) and `H_TP` (two-point base). `include!`d
// into `boolean_analysis_hc43_core_step.rs`. No new globals.

/// `motive m` — the per-level induction predicate, byte-for-byte the one
/// `hc43_core`'s `Nat.rec` consumes (so `hc43_core_step` is the exact `h_step`).
///
/// `motive m := ∀ (F s r : HCPoint m → Rat)(hs)(hr)(hr1)(hrecon)(hnn)(h4n),
///   <hc43_core_concl ρ m F s r hs hnn h4n>`.
pub(super) fn step_motive_body(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    m: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fn_ty = c.f_type(m);
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let (s_id, s) = b.fresh_local(fn_ty.clone());
    let (r_id, r) = b.fresh_local(fn_ty.clone());
    let hs_ty = forall_scale_nonneg_ty(&c.o, &b, m, &s);
    let (hs_id, hs) = b.fresh_local(hs_ty.clone());
    let hr_ty = forall_r_nonneg_ty(&c.o, &b, m, &r);
    let (hr_id, _hr) = b.fresh_local(hr_ty.clone());
    let hr1_ty = forall_r_lt_one_ty(&c.o, &b, m, &r);
    let (hr1_id, _hr1) = b.fresh_local(hr1_ty.clone());
    let hrecon_ty = forall_recon_ty(&c.o, &b, m, &f, &s, &r);
    let (hrecon_id, _hrecon) = b.fresh_local(hrecon_ty.clone());
    let hnn_ty = forall_lhs_nonneg_ty(&c.o, &b, rho, m, &f);
    let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
    let h4n_ty = c.o.rle(&c.o.rat_zero, &c.pow4n(m));
    let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

    let concl = hc43_core_concl(&c.o, &b, rho, m, &f, &s, &r, &hs, &hnn, &h4n);

    let e = b.mk_pi(h4n_id, BinderInfo::Default, h4n_ty, concl);
    let e = b.mk_pi(hnn_id, BinderInfo::Default, hnn_ty, e);
    let e = b.mk_pi(hrecon_id, BinderInfo::Default, hrecon_ty, e);
    let e = b.mk_pi(hr1_id, BinderInfo::Default, hr1_ty, e);
    let e = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, e);
    let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
    let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
    b.finish_child(e)
}

/// `H_CM` — the cube-Minkowski / MERGE leaf, universally quantified (the landed
/// `NNReal.cube_minkowski_merge` shape):
///
/// ```text
///   ∀ (U₁ S₁ T₁ U₂ S₂ T₂ : NNReal),
///     U₁³ ≤ S₁²·T₁ → U₂³ ≤ S₂²·T₂ →
///     3·(U₁²U₂) ≤ 2·(S₁S₂T₁) + S₁²T₂ →     -- (Split A)
///     3·(U₁U₂²) ≤ 2·(S₁S₂T₂) + S₂²T₁ →     -- (Split B)
///       (U₁+U₂)³ ≤ (S₁+S₂)²·(T₁+T₂)
/// ```
///
/// Identical to `cube_minkowski_merge`'s own type; taken as a hypothesis so the
/// step threads it (with its split premises) at the fold.
pub(super) fn h_cm_ty(c: &Hc43StepConsts) -> Expr {
    let nn = c.nnreal();
    let cube = |t: &Expr| c.nncube(t);
    let sq_t = |s: &Expr, t: &Expr| c.nnmul(&c.nnmul(s, s), t);
    let three = |t: &Expr| c.nnadd(&c.nnadd(t, t), t);
    let two_plus = |p: &Expr, q: &Expr| c.nnadd(&c.nnadd(p, p), q);

    let mut b = EnvDeclBuilder::new();
    let (u1_id, u1) = b.fresh_local(nn.clone());
    let (s1_id, s1) = b.fresh_local(nn.clone());
    let (t1_id, t1) = b.fresh_local(nn.clone());
    let (u2_id, u2) = b.fresh_local(nn.clone());
    let (s2_id, s2) = b.fresh_local(nn.clone());
    let (t2_id, t2) = b.fresh_local(nn.clone());

    let h1_ty = c.nnle(&cube(&u1), &sq_t(&s1, &t1));
    let (h1_id, _) = b.fresh_local(h1_ty.clone());
    let h2_ty = c.nnle(&cube(&u2), &sq_t(&s2, &t2));
    let (h2_id, _) = b.fresh_local(h2_ty.clone());

    let u1sq_u2 = c.nnmul(&c.nnmul(&u1, &u1), &u2);
    let u1_u2sq = c.nnmul(&c.nnmul(&u1, &u2), &u2);
    let p_term = c.nnmul(&c.nnmul(&s1, &s2), &t1);
    let q_term = c.nnmul(&c.nnmul(&s1, &s1), &t2);
    let pp_term = c.nnmul(&c.nnmul(&s1, &s2), &t2);
    let qp_term = c.nnmul(&c.nnmul(&s2, &s2), &t1);

    let ha_ty = c.nnle(&three(&u1sq_u2), &two_plus(&p_term, &q_term));
    let (ha_id, _) = b.fresh_local(ha_ty.clone());
    let hb_ty = c.nnle(&three(&u1_u2sq), &two_plus(&pp_term, &qp_term));
    let (hb_id, _) = b.fresh_local(hb_ty.clone());

    let us = c.nnadd(&u1, &u2);
    let lhs = c.nnmul(&c.nnmul(&us, &us), &us);
    let ss = c.nnadd(&s1, &s2);
    let tt = c.nnadd(&t1, &t2);
    let rhs = c.nnmul(&c.nnmul(&ss, &ss), &tt);
    let concl = c.nnle(&lhs, &rhs);

    let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
    let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_pi(t2_id, BinderInfo::Default, nn.clone(), e);
    let e = b.mk_pi(s2_id, BinderInfo::Default, nn.clone(), e);
    let e = b.mk_pi(u2_id, BinderInfo::Default, nn.clone(), e);
    let e = b.mk_pi(t1_id, BinderInfo::Default, nn.clone(), e);
    let e = b.mk_pi(s1_id, BinderInfo::Default, nn.clone(), e);
    let e = b.mk_pi(u1_id, BinderInfo::Default, nn.clone(), e);
    b.finish(e)
}

/// `H_TP` — the two-point base leaf, universally quantified, with the
/// per-coordinate body byte-for-byte `h_tp_ty`. Note the level mismatch the
/// `gPart`/`liftH` fold forces: `F : HCPoint (m+1) → Rat` (the cube split lives
/// one level up), while the per-point witnesses `s r : HCPoint m → Rat` live at
/// the lower level (the `contribution` point `x := decode m k : HCPoint m`):
///
/// ```text
///   ∀ (m : Nat)(F : HCPoint (m+1) → Rat)(s r : HCPoint m → Rat)
///     (hs : ∀ x : HCPoint m, 0 ≤ s x), <h_tp_ty ρ m F s r hs>
/// ```
pub(super) fn h_tp_universal_ty(c: &Hc43StepConsts, parent: &EnvDeclBuilder, rho: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = b.fresh_local(c.nat());
    let sm = c.succ(&m);
    let f_ty = c.f_type(&sm); // HCPoint (m+1) → Rat
    let sr_ty = c.f_type(&m); // HCPoint m → Rat
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (s_id, s) = b.fresh_local(sr_ty.clone());
    let (r_id, r) = b.fresh_local(sr_ty.clone());
    let hs_ty = forall_scale_nonneg_ty(&c.o, &b, &m, &s);
    let (hs_id, hs) = b.fresh_local(hs_ty.clone());

    let body = h_tp_ty(&c.o, &b, rho, &m, &f, &s, &r, &hs);

    let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, body);
    let e = b.mk_pi(r_id, BinderInfo::Default, sr_ty.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, sr_ty, e);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish_child(b.mk_pi(m_id, BinderInfo::Default, c.nat(), e))
}

/// `fun (k : Fin (2^m)) => NNReal.ofRat (pow4 (lo k)) (hlo k) + NNReal.ofRat (pow4
/// (hi k)) (hhi k)` — the NNReal split-summand (S1's output). `lo k = G k + ρ·H k`
/// (the `noiseFn_succ_low` RHS), `hi k = G k − ρ·H k` (`_high`). The per-point
/// nonneg witnesses are supplied by `hlo`/`hhi` (∀-quantified pow4-nonneg). This
/// is the EXACT finSum that S1 proves `LHS(m+1)` equals (after the `finSum_ofRat`
/// lift), and the LHS of the residual `H_CLOSE`.
pub(super) fn split_summand_finsum(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    m: &Expr,
    f: &Expr,
    hlo: &Expr,
    hhi: &Expr,
) -> Expr {
    let p2m = c.pow2(m);
    let fin = c.fin_of(&p2m);
    let g_part = c.g_part_of(m, f);
    let lift_h = c.lift_h_of(m, f);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let g = c.noise_fn(rho, m, &g_part, &k);
    let hh = c.noise_fn(rho, m, &lift_h, &k);
    let rho_h = c.rmul(rho, &hh);
    let lo = c.rat_add(&g, &rho_h);
    let hi = c.rat_sub(&g, &rho_h);
    let body = c.nnadd(
        &c.ofrat(&c.pow4(&lo), &Expr::app(hlo.clone(), k.clone())),
        &c.ofrat(&c.pow4(&hi), &Expr::app(hhi.clone(), k.clone())),
    );
    let summand = b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body));
    c.finsum(&p2m, &summand)
}

/// `∀ k : Fin (2^m), 0 ≤ pow4 (G k + ρ·H k)` — the LOW per-point nonneg hyp.
pub(super) fn forall_lo_nonneg_ty(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    m: &Expr,
    f: &Expr,
) -> Expr {
    let fin = c.fin_of(&c.pow2(m));
    let g_part = c.g_part_of(m, f);
    let lift_h = c.lift_h_of(m, f);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let g = c.noise_fn(rho, m, &g_part, &k);
    let hh = c.noise_fn(rho, m, &lift_h, &k);
    let lo = c.rat_add(&g, &c.rmul(rho, &hh));
    let body = c.rle(&c.rat_zero(), &c.pow4(&lo));
    b.finish_child(b.mk_pi(k_id, BinderInfo::Default, fin, body))
}

/// `∀ k : Fin (2^m), 0 ≤ pow4 (G k − ρ·H k)` — the HIGH per-point nonneg hyp.
pub(super) fn forall_hi_nonneg_ty(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    m: &Expr,
    f: &Expr,
) -> Expr {
    let fin = c.fin_of(&c.pow2(m));
    let g_part = c.g_part_of(m, f);
    let lift_h = c.lift_h_of(m, f);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let g = c.noise_fn(rho, m, &g_part, &k);
    let hh = c.noise_fn(rho, m, &lift_h, &k);
    let hi = c.rat_sub(&g, &c.rmul(rho, &hh));
    let body = c.rle(&c.rat_zero(), &c.pow4(&hi));
    b.finish_child(b.mk_pi(k_id, BinderInfo::Default, fin, body))
}

/// `H_CLOSE` — the residual two-point bound + cube-fold + `4^{m+1}` scalar close,
/// the §11 cross-term wall, universally quantified. After S1 the LHS `LHS(m+1)`
/// equals `Σ_k (ofRat(pow4 lo) + ofRat(pow4 hi))` (the split-summand finSum);
/// closing to the motive RHS `ofRat(4^{m+1})·norm43_cubed_{m+1}` needs exactly
/// this inequality, which `h_cm`/`h_tp` as stated do NOT compose to (S2 gives
/// `Σ 4·(A³+B³)`, whose collapse `4·(NG³+NH³)` is NOT `≤ 4^{m+1}·NF1³` without the
/// irrational cross-term). Carried as an EXPLICIT minor premise (NOT an axiom):
///
/// ```text
///   ∀ (m : Nat)(F s r : HCPoint (m+1) → Rat)(hs : ∀ x, 0 ≤ s x)
///     (hlo : ∀ k, 0 ≤ pow4 (G k + ρ·H k))(hhi : ∀ k, 0 ≤ pow4 (G k − ρ·H k))
///     (h4n : 0 ≤ 4^{m+1}),
///       NNReal.le
///         (NNReal.finSum (2^m) (fun k => ofRat(pow4 lo) + ofRat(pow4 hi)))
///         (NNReal.mul (ofRat (4^{m+1}) h4n) (norm43_cubed (m+1) F s r hs))
/// ```
///
/// stated over the SAME `s,r,hs` witnesses the motive RHS uses, so the close is a
/// single inequality the eventual CH3 tower (§11 rungs 2–5: `h_tp`'s two-point,
/// the cube-Minkowski `h_cm`, `norm43_card_succ`, the AM-GM rung) discharges.
pub(super) fn h_close_ty(c: &Hc43StepConsts, parent: &EnvDeclBuilder, rho: &Expr) -> Expr {
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
    let h4n_ty = c.rle(&c.rat_zero(), &c.pow4n(&sm));
    let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

    let lhs = split_summand_finsum(c, &b, rho, &m, &f, &hlo, &hhi);
    let rhs = c.nnmul(
        &c.ofrat(&c.pow4n(&sm), &h4n),
        &c.norm43_cubed_app(&sm, &f, &s, &r, &hs),
    );
    let concl = c.nnle(&lhs, &rhs);

    let e = b.mk_pi(h4n_id, BinderInfo::Default, h4n_ty, concl);
    let e = b.mk_pi(hhi_id, BinderInfo::Default, hhi_ty, e);
    let e = b.mk_pi(hlo_id, BinderInfo::Default, hlo_ty, e);
    let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
    let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
    b.finish_child(b.mk_pi(m_id, BinderInfo::Default, c.nat(), e))
}

/// The full `hc43_core_step` TYPE:
/// `∀ ρ, (3ρ²≤1) → H_CM → H_TP → H_CLOSE → ∀ m, motive m → motive (m+1)`.
pub(super) fn build_hc43_step_ty(c: &Hc43StepConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let h_ty = hyp_contract_ty(&c.o, &rho);
    let (h_id, _h) = b.fresh_local(h_ty.clone());
    let hcm_ty = h_cm_ty(c);
    let (hcm_id, _hcm) = b.fresh_local(hcm_ty.clone());
    let htp_ty = h_tp_universal_ty(c, &b, &rho);
    let (htp_id, _htp) = b.fresh_local(htp_ty.clone());
    let hclose_ty = h_close_ty(c, &b, &rho);
    let (hclose_id, _hclose) = b.fresh_local(hclose_ty.clone());

    // ∀ m, motive m → motive (m+1).
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

    let e = b.mk_pi(hclose_id, BinderInfo::Default, hclose_ty, step);
    let e = b.mk_pi(htp_id, BinderInfo::Default, htp_ty, e);
    let e = b.mk_pi(hcm_id, BinderInfo::Default, hcm_ty, e);
    let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
    b.finish(b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e))
}
