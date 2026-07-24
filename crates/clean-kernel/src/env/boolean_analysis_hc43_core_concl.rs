// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_hc43_core_base.rs` — the shared `hc43_core`
// conclusion (the NNReal `LE` goal) + the witness-bundle telescope, reused by the
// base case, the step, and the `Nat.rec` assembly so the targets agree
// byte-for-byte. No new globals.

/// `∀ x : HCPoint n, 0 ≤ s x` — the bundled per-point scale-nonneg hyp (matches
/// `norm43`'s `forall_scale_nonneg_ty`).
pub(super) fn forall_scale_nonneg_ty(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    s: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = d.fresh_local(hcp.clone());
    let body = c.rle(&c.rat_zero, &Expr::app(s.clone(), x));
    d.finish_child(d.mk_pi(x_id, BinderInfo::Default, hcp, body))
}

/// `∀ x : HCPoint n, 0 ≤ r x`.
pub(super) fn forall_r_nonneg_ty(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    r: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = d.fresh_local(hcp.clone());
    let body = c.rle(&c.rat_zero, &Expr::app(r.clone(), x));
    d.finish_child(d.mk_pi(x_id, BinderInfo::Default, hcp, body))
}

/// `∀ x : HCPoint n, r x < 1`.
pub(super) fn forall_r_lt_one_ty(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    r: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = d.fresh_local(hcp.clone());
    let body = c.rlt(&Expr::app(r.clone(), x), &c.rat_one);
    d.finish_child(d.mk_pi(x_id, BinderInfo::Default, hcp, body))
}

/// `∀ x : HCPoint n, |F x| = ((s x · s x)· s x)· r x` — the reconstruction
/// witness `pow43Gen_cubed` consumes (the `heq` slot, per point).
pub(super) fn forall_recon_ty(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = d.fresh_local(hcp.clone());
    let fx = Expr::app(f.clone(), x.clone());
    let sx = Expr::app(s.clone(), x.clone());
    let rx = Expr::app(r.clone(), x.clone());
    let ss = c.rmul(&sx, &sx);
    let sss = c.rmul(&ss, &sx);
    let sssr = c.rmul(&sss, &rx);
    let body = c.eq_rat(&c.abs(&fx), &sssr);
    d.finish_child(d.mk_pi(x_id, BinderInfo::Default, hcp, body))
}

/// `∀ jx : Fin (2^n), 0 ≤ pow4 (noiseFn ρ n F jx)` — the LHS per-point nonneg
/// witness (genuine: `pow4 x = (x·x)·(x·x)` is always ≥ 0; carried as an honest
/// hypothesis rather than re-deriving square-nonneg per point — NOT an axiom).
pub(super) fn forall_lhs_nonneg_ty(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
) -> Expr {
    let fin = c.fin_of(&c.pow2(n));
    let mut d = EnvDeclBuilder::child_of(parent);
    let (jx_id, jx) = d.fresh_local(fin.clone());
    let body = c.rle(&c.rat_zero, &c.pow4(&c.noise_fn(rho, n, f, &jx)));
    d.finish_child(d.mk_pi(jx_id, BinderInfo::Default, fin, body))
}

/// The LHS summand `fun jx : Fin (2^n) => NNReal.ofRat (pow4 (noiseFn ρ n F jx))
/// (hnn jx)`.
pub(super) fn lhs_summand(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
    hnn: &Expr,
) -> Expr {
    let fin = c.fin_of(&c.pow2(n));
    let mut d = EnvDeclBuilder::child_of(parent);
    let (jx_id, jx) = d.fresh_local(fin.clone());
    let body = c.ofrat(
        &c.pow4(&c.noise_fn(rho, n, f, &jx)),
        &Expr::app(hnn.clone(), jx.clone()),
    );
    d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, fin, body))
}

/// The `hc43_core` conclusion (the NNReal `LE` goal) at a concrete `n`, for FREE
/// `ρ, F, s, r, hs, hnn, h4n`. Reused by base / step / assembly.
///
/// `NNReal.le (NNReal.finSum (2^n) lhs_summand)
///            (NNReal.mul (NNReal.ofRat (powNat 4 n) h4n) (norm43_cubed n F s r hs))`.
#[allow(clippy::too_many_arguments)]
pub(super) fn hc43_core_concl(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
    hnn: &Expr,
    h4n: &Expr,
) -> Expr {
    let p2n = c.pow2(n);
    let summand = lhs_summand(c, parent, rho, n, f, hnn);
    let lhs = c.finsum(&p2n, &summand);
    let scal = c.ofrat(&c.pow4n(n), h4n);
    let rhs = c.nnmul(&scal, &c.norm43_cubed_app(n, f, s, r, hs));
    c.nnle(&lhs, &rhs)
}

/// `3·(ρ·ρ) ≤ 1` (the hc-bounds-shaped contraction hypothesis).
pub(super) fn hyp_contract_ty(c: &Hc43Consts, rho: &Expr) -> Expr {
    let three = c.o.three();
    let rho_sq = c.rmul(rho, rho);
    c.rle(&c.rmul(&three, &rho_sq), &c.rat_one)
}

/// The two-point base hypothesis `h_tp` (the parallel campaign's leaf (A)), in
/// its POINTWISE per-coordinate form over the n-level legs `gPart`/`liftH`.
///
/// At the cube point `x' := hcDecode n k` the two operator legs are
///   `G := noiseFn ρ n (gPart n F) k`,  `H := noiseFn ρ n (liftH n F) k`,
/// and the genuine `n=1` dual-HC two-point inequality (design §0/§1, refute-clean)
/// is the EVEN-PAIR moment bound, lifted to NNReal. We state it CONCRETELY (no new
/// constant — an honest universally-quantified inequality):
///
/// ```text
///   h_tp : ∀ (k : Fin (2^n)),
///     NNReal.le
///       (NNReal.add (NNReal.ofRat (pow4 (G + ρ·H)) _)
///                   (NNReal.ofRat (pow4 (G − ρ·H)) _))
///       (NNReal.mul (NNReal.ofRat 4 _)
///         (NNReal.add (cube (contribution (gPart n F) … (decode n k)))
///                     (cube (contribution (liftH n F) … (decode n k)))))
/// ```
///
/// where `G+ρ·H := noiseFn ρ (n+1) F (castP (castAdd k))` (the LOW split) and
/// `G−ρ·H := noiseFn ρ (n+1) F (castP (addNat k))` (the HIGH split) by
/// `noiseFn_succ_low/high`, `cube t := (t·t)·t`, and `contribution g … x :=
/// pow43Gen |g x| (s x)(r x) …` is the `4/3`-norm per-point contribution. This is
/// the EXACT NNReal pointwise leaf the step's S2 consumes (lifted under the sum by
/// `NNReal.finSum_le`); it is an explicit hypothesis, NOT an axiom. The base does
/// NOT consume it (at `n=0` it is threaded only to match the telescope).
///
/// NB: the LHS per-point nonneg proofs are supplied by `hnn`-style square-nonneg
/// witnesses bundled into `hsplit_nn` (carried alongside, see report); to keep the
/// telescope a single `Prop` we wrap the whole pointwise statement as the body of
/// a `∀ k`. The witnesses for the two `ofRat` LHS legs reuse `hsplit_lo`/`hsplit_hi`
/// supplied per-coordinate.
#[allow(clippy::too_many_arguments)]
pub(super) fn h_tp_ty(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
) -> Expr {
    let p2n = c.pow2(n);
    let fin = c.fin_of(&p2n);
    let g_part = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.gPart"), vec![]),
        [n.clone(), f.clone()],
    );
    let lift_h = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.liftH"), vec![]),
        [n.clone(), f.clone()],
    );
    let cube = |t: &Expr| c.nnmul(&c.nnmul(t, t), t);

    let mut d = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = d.fresh_local(fin.clone());
    let x = c.decode(n, &k);
    // legs G, H at coordinate k.
    let gg = c.noise_fn(rho, n, &g_part, &k);
    let hh = c.noise_fn(rho, n, &lift_h, &k);
    let rho_h = c.rmul(rho, &hh);
    let lo = c.rat_add(&gg, &rho_h); // G + ρ·H
    let hi = c.rat_sub(&gg, &rho_h); // G − ρ·H
    let pow4_lo = c.pow4(&lo);
    let pow4_hi = c.pow4(&hi);
    let h_lo = c.rle(&c.rat_zero, &pow4_lo);
    let h_hi = c.rle(&c.rat_zero, &pow4_hi);
    // LHS NNReal: ofRat(pow4 lo) + ofRat(pow4 hi)   (nonneg witnesses opaque-bound below).
    let (hlo_id, hlo) = d.fresh_local(h_lo.clone());
    let (hhi_id, hhi) = d.fresh_local(h_hi.clone());
    let lhs_nn = c.nnadd(&c.ofrat(&pow4_lo, &hlo), &c.ofrat(&pow4_hi, &hhi));
    // RHS NNReal: ofRat 4 · (cube(contribution gPart) + cube(contribution liftH)).
    let h4 = c.rle(&c.rat_zero, &c.four_rat());
    let (h4_id, h4v) = d.fresh_local(h4.clone());
    let contrib_g = c.contribution(&g_part, s, r, hs, &x);
    let contrib_h = c.contribution(&lift_h, s, r, hs, &x);
    let rhs_nn = c.nnmul(
        &c.ofrat(&c.four_rat(), &h4v),
        &c.nnadd(&cube(&contrib_g), &cube(&contrib_h)),
    );
    let ineq = c.nnle(&lhs_nn, &rhs_nn);
    // ∀ h4 hlo hhi, ineq  (the per-point nonneg/scale witnesses are bound INSIDE the
    // per-coordinate Prop so the whole thing is a single closed Prop).
    let body = d.mk_pi(h4_id, BinderInfo::Default, h4, ineq);
    let body = d.mk_pi(hhi_id, BinderInfo::Default, h_hi, body);
    let body = d.mk_pi(hlo_id, BinderInfo::Default, h_lo, body);
    d.finish_child(d.mk_pi(k_id, BinderInfo::Default, fin, body))
}
