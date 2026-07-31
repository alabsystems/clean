// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_hc43_core_base.rs` — the carrier-collapse proof
// term for the `n = 0` base case. All terms inline (no new globals), so the
// theorem's axiom closure stays empty.

/// Build the type + proof of `hc43_core_base`:
/// `∀ ρ (F s r : HCPoint 0 → Rat)(hs)(hr)(hr1)(hrecon)(hnn)(h4n),
///    3·(ρ·ρ) ≤ 1 → h_tp → <hc43_core conclusion at n=0>`.
fn build_hc43_base(c: &Hc43Consts) -> (Expr, Expr) {
    let zero = c.nat_zero.clone();

    // Shared telescope builder: introduces all binders and returns the proof tail.
    // We build the type and the value separately but with byte-identical binder
    // structure (so the assembly / step agree).
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let fn_ty = c.f_type(&zero);
        let (f_id, f) = b.fresh_local(fn_ty.clone());
        let (s_id, s) = b.fresh_local(fn_ty.clone());
        let (r_id, r) = b.fresh_local(fn_ty.clone());
        let hs_ty = forall_scale_nonneg_ty(c, &b, &zero, &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());
        let hr_ty = forall_r_nonneg_ty(c, &b, &zero, &r);
        let (hr_id, _hr) = b.fresh_local(hr_ty.clone());
        let hr1_ty = forall_r_lt_one_ty(c, &b, &zero, &r);
        let (hr1_id, _hr1) = b.fresh_local(hr1_ty.clone());
        let hrecon_ty = forall_recon_ty(c, &b, &zero, &f, &s, &r);
        let (hrecon_id, _hrecon) = b.fresh_local(hrecon_ty.clone());
        let hnn_ty = forall_lhs_nonneg_ty(c, &b, &rho, &zero, &f);
        let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
        let h4n_ty = c.rle(&c.rat_zero, &c.pow4n(&zero));
        let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());
        let hcontract_ty = hyp_contract_ty(c, &rho);
        let (hc_id, _hc) = b.fresh_local(hcontract_ty.clone());

        let concl = hc43_core_concl(c, &b, &rho, &zero, &f, &s, &r, &hs, &hnn, &h4n);

        let e = b.mk_pi(hc_id, BinderInfo::Default, hcontract_ty, concl);
        let e = b.mk_pi(h4n_id, BinderInfo::Default, h4n_ty, e);
        let e = b.mk_pi(hnn_id, BinderInfo::Default, hnn_ty, e);
        let e = b.mk_pi(hrecon_id, BinderInfo::Default, hrecon_ty, e);
        let e = b.mk_pi(hr1_id, BinderInfo::Default, hr1_ty, e);
        let e = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, e);
        let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
        let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
        b.finish(b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let fn_ty = c.f_type(&zero);
        let (f_id, f) = b.fresh_local(fn_ty.clone());
        let (s_id, s) = b.fresh_local(fn_ty.clone());
        let (r_id, r) = b.fresh_local(fn_ty.clone());
        let hs_ty = forall_scale_nonneg_ty(c, &b, &zero, &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());
        let hr_ty = forall_r_nonneg_ty(c, &b, &zero, &r);
        let (hr_id, hr) = b.fresh_local(hr_ty.clone());
        let hr1_ty = forall_r_lt_one_ty(c, &b, &zero, &r);
        let (hr1_id, hr1) = b.fresh_local(hr1_ty.clone());
        let hrecon_ty = forall_recon_ty(c, &b, &zero, &f, &s, &r);
        let (hrecon_id, hrecon) = b.fresh_local(hrecon_ty.clone());
        let hnn_ty = forall_lhs_nonneg_ty(c, &b, &rho, &zero, &f);
        let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
        let h4n_ty = c.rle(&c.rat_zero, &c.pow4n(&zero));
        let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());
        let hcontract_ty = hyp_contract_ty(c, &rho);
        let (hc_id, _hc) = b.fresh_local(hcontract_ty.clone());

        let proof = build_base_proof(c, &b, &rho, &f, &s, &r, &hs, &hr, &hr1, &hrecon, &hnn, &h4n);

        let e = b.mk_lam(hc_id, BinderInfo::Default, hcontract_ty, proof);
        let e = b.mk_lam(h4n_id, BinderInfo::Default, h4n_ty, e);
        let e = b.mk_lam(hnn_id, BinderInfo::Default, hnn_ty, e);
        let e = b.mk_lam(hrecon_id, BinderInfo::Default, hrecon_ty, e);
        let e = b.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, e);
        let e = b.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
        let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
        let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
        b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e))
    };

    (ty, value)
}

/// `NNReal.finSum 1 Φ = Φ (Fin.last 0)`.
///
/// `NNReal.finSum_succ 0 Φ : finSum 1 Φ = add (finSum 0 (Φ∘castSucc)) (Φ(last 0))`;
/// `NNReal.finSum_zero` collapses the prefix to `NNReal.zero`; `NNReal.zero_add`
/// drops it.
fn nn_sum_one_collapse(c: &Hc43Consts, parent: &EnvDeclBuilder, phi: &Expr) -> Expr {
    let zero = c.nat_zero.clone();
    let one = c.succ(&zero);
    let nnreal_zero = Expr::const_(Name::from_string("NNReal.zero"), vec![]);

    let phi_last = Expr::app(phi.clone(), c.last(&zero));

    // finSum_succ 0 Φ
    let succ_eq = Expr::apps(
        Expr::const_(Name::from_string("NNReal.finSum_succ"), vec![]),
        [zero.clone(), phi.clone()],
    );
    // Φ∘castSucc
    let phi_cast = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin0 = c.fin_of(&zero);
        let (i_id, i) = d.fresh_local(fin0.clone());
        let cast = Expr::apps(c.fin_cast_succ.clone(), [zero.clone(), i]);
        let body = Expr::app(phi.clone(), cast);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin0, body))
    };
    let prefix_sum = c.finsum(&zero, &phi_cast);
    let mid = c.nnadd(&prefix_sum, &phi_last);
    // finSum_zero (Φ∘castSucc) : finSum 0 (Φ∘castSucc) = NNReal.zero
    let prefix_zero = Expr::app(
        Expr::const_(Name::from_string("NNReal.finSum_zero"), vec![]),
        phi_cast,
    );
    // congrArg (fun w => add w (Φ(last 0))) prefix_zero : mid = add zero (Φ(last 0))
    let add_motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.nnreal.clone());
        let body = c.nnadd(&w, &phi_last);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let zero_plus = c.nnadd(&nnreal_zero, &phi_last);
    let cong_zero = c.congr_arg_nn(&prefix_sum, &nnreal_zero, add_motive, prefix_zero);
    // NNReal.zero_add (Φ(last 0)) : add zero (Φ(last 0)) = Φ(last 0)
    let zero_add = Expr::app(
        Expr::const_(Name::from_string("NNReal.zero_add"), vec![]),
        phi_last.clone(),
    );

    let sum_one = c.finsum(&one, phi);
    let t1 = c.trans_nn(&sum_one, &mid, &zero_plus, succ_eq, cong_zero);
    c.trans_nn(&sum_one, &zero_plus, &phi_last, t1, zero_add)
}

/// The base-case proof body (the NNReal `LE` goal proof, with all binders free).
#[allow(clippy::too_many_arguments)]
fn build_base_proof(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
    hr: &Expr,
    hr1: &Expr,
    hrecon: &Expr,
    hnn: &Expr,
    h4n: &Expr,
) -> Expr {
    let zero = c.nat_zero.clone();
    let one = c.succ(&zero);
    let last0 = c.last(&zero);
    let dec = c.decode(&zero, &last0); // hcDecode 0 (last 0)
    let f_dec = Expr::app(f.clone(), dec.clone()); // F (hcDecode 0 (last 0))

    // ── LHS summand Φ_lhs jx := ofRat (pow4 (noiseFn ρ 0 F jx)) (hnn jx).
    let lhs_phi = lhs_summand(c, parent, rho, &zero, f, hnn);
    let lhs = c.finsum(&one, &lhs_phi);

    // LHS collapse: finSum 1 Φ_lhs = Φ_lhs (last 0) = ofRat (pow4 (noiseFn ρ 0 F (last0))) (hnn last0).
    let lhs_collapse = nn_sum_one_collapse(c, parent, &lhs_phi);
    let noise_last = c.noise_fn(rho, &zero, f, &last0);
    let pow4_noise = c.pow4(&noise_last);
    let hnn_last = Expr::app(hnn.clone(), last0.clone());
    let phi_last_val = c.ofrat(&pow4_noise, &hnn_last); // = Φ_lhs (last 0) defeq

    // ── RHS: ofRat(powNat 4 0) · norm43_cubed 0 F s r hs.
    let scal = c.ofrat(&c.pow4n(&zero), h4n);
    let nc = c.norm43_cubed_app(&zero, f, s, r, hs);
    let rhs = c.nnmul(&scal, &nc);
    // norm43_cubed 0 = (norm43 0)³ ; norm43 0 = finSum 1 (cube_summand) collapses to
    // the single pow43Gen contribution at dec. We avoid expanding norm43_cubed by
    // reducing the whole RHS to the SAME single-point cube as the LHS via the
    // pow43Gen cube identity. See report for the residual gap if this does not
    // close mechanically.

    // pow43Gen contribution at dec.
    let contrib = c.contribution(f, s, r, hs, &dec);
    let cube_contrib = c.nnmul(&c.nnmul(&contrib, &contrib), &contrib);

    // The goal is `NNReal.le lhs rhs`. Both LHS and RHS reduce to `cube_contrib`
    // modulo the carrier collapses. We assemble:
    //   lhs = phi_last_val          (lhs_collapse)
    //   phi_last_val = cube_contrib  (the noiseFn_zero_dim + pow43Gen_cubed bridge)
    //   rhs = cube_contrib           (RHS collapse)
    // then close by NNReal.le.refl cube_contrib transported on both operands.

    // --- bridge: phi_last_val = cube_contrib.
    let bridge_lhs = base_lhs_bridge(
        c, parent, rho, f, s, r, hs, hr, hr1, hrecon, hnn, &dec, &f_dec,
    );
    // --- bridge: rhs = cube_contrib.
    let bridge_rhs = base_rhs_bridge(c, parent, f, s, r, hs, h4n, &cube_contrib);

    // le_refl cube_contrib : cube_contrib ≤ cube_contrib.
    let refl = Expr::app(
        Expr::const_(Name::from_string("NNReal.le.refl"), vec![]),
        cube_contrib.clone(),
    );

    // transport left operand: cube_contrib ⇐ lhs   along (lhs = cube_contrib).symm
    //   lhs = phi_last_val (lhs_collapse); phi_last_val = cube_contrib (bridge_lhs)
    let lhs_eq_cube = c.trans_nn(&lhs, &phi_last_val, &cube_contrib, lhs_collapse, bridge_lhs);
    let left_motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.nnreal.clone());
        let body = c.nnle(&z, &cube_contrib);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let cube_eq_lhs = c.symm_nn(&lhs, &cube_contrib, lhs_eq_cube); // cube_contrib = lhs
    let after_left = c.subst_nn_prop(left_motive, &cube_contrib, &lhs, cube_eq_lhs, refl);
    // after_left : lhs ≤ cube_contrib.

    // transport right operand: cube_contrib ⇐ rhs   along (rhs = cube_contrib).symm
    let right_motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.nnreal.clone());
        let body = c.nnle(&lhs, &z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let cube_eq_rhs = c.symm_nn(&rhs, &cube_contrib, bridge_rhs); // cube_contrib = rhs
    c.subst_nn_prop(right_motive, &cube_contrib, &rhs, cube_eq_rhs, after_left)
}

/// `phi_last_val = cube_contrib` : `ofRat (pow4 (noiseFn ρ 0 F last0)) _
///   = (pow43Gen |F dec| (s dec)(r dec) …)³`.
///
/// Chain:
///  1. `noiseFn ρ 0 F last0 = F dec`  (`noiseFn_zero_dim` + density≡1 + `mul_one`);
///     lift through `ofRat (pow4 ·) _` (congrArg, proof-irrel on the nonneg slot).
///  2. `pow4 (F dec) = |F dec|⁴`  (pow4 = (x·x)·(x·x) = |x|⁴ via abs evenness +
///     re-association) — the Rat reconciliation `pow4(F)=|F|⁴`.
///  3. `ofRat |F dec|⁴ _ = (pow43Gen |F dec| (s dec)(r dec) …)³`  (`pow43Gen_cubed`
///     symm, with `hrecon dec : |F dec| = ((s dec·…)·r dec)` the reconstruction).
#[allow(clippy::too_many_arguments)]
fn base_lhs_bridge(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
    hr: &Expr,
    hr1: &Expr,
    hrecon: &Expr,
    hnn: &Expr,
    dec: &Expr,
    f_dec: &Expr,
) -> Expr {
    let zero = c.nat_zero.clone();
    let last0 = c.last(&zero);

    // ── value handles.
    let abs_fdec = c.abs(f_dec);
    let s_dec = Expr::app(s.clone(), dec.clone());
    let r_dec = Expr::app(r.clone(), dec.clone());
    let hx = c.abs_nonneg(f_dec); // 0 ≤ |F dec|
    let hs_dec = Expr::app(hs.clone(), dec.clone());
    let hr_dec = Expr::app(hr.clone(), dec.clone());
    let hr1_dec = Expr::app(hr1.clone(), dec.clone());
    let hrecon_dec = Expr::app(hrecon.clone(), dec.clone()); // |F dec| = ((s·s)·s)·r

    let contrib = c.contribution(f, s, r, hs, dec);
    let cube_contrib = c.nnmul(&c.nnmul(&contrib, &contrib), &contrib);
    let abs4_left = c.x4_left(&abs_fdec); // ((|Fdec|·|Fdec|)·|Fdec|)·|Fdec|
    let noise_last = c.noise_fn(rho, &zero, f, &last0);
    let pow4_noise = c.pow4(&noise_last); // (nl·nl)·(nl·nl)

    // ── Step C: cubed : cube_contrib = ofRat abs4_left h4abs.
    // `pow43Gen_cubed |Fdec| (s dec)(r dec) hx hs hr hr1 hrecon
    //    : (pow43Gen |Fdec| …)³ = NNReal.ofRat (|Fdec|⁴_left) h4abs`.
    // cube_contrib IS `(pow43Gen |Fdec| …)³` (defeq), so `cubed` retypes onto it.
    let (x4_of_abs, h4abs) = abs4_nonneg(c, &abs_fdec, &hx); // x4_of_abs = abs4_left ; h4abs : 0 ≤ abs4_left
    let _ = &x4_of_abs;
    let cubed = Expr::apps(
        Expr::const_(Name::from_string("NNReal.pow43Gen_cubed"), vec![]),
        [
            abs_fdec.clone(),
            s_dec.clone(),
            r_dec.clone(),
            hx.clone(),
            hs_dec,
            hr_dec,
            hr1_dec,
            hrecon_dec,
        ],
    );
    let ofrat_abs4 = c.ofrat(&abs4_left, &h4abs);

    // ── Step B (Rat): hval : abs4_left = pow4(noiseFn ρ 0 F last0).
    //   B1 : pow4(F dec) = abs4_left   (the abs/pow reconciliation, `base_pow4_eq_abs4`).
    //   B0 : noiseFn ρ 0 F last0 = F dec   (`noiseFn_zero_dim` + density≡1 + mul_one).
    //   ⇒ pow4(noiseFn …) = pow4(F dec) = abs4_left ; take symm for hval.
    let b0 = base_noise_zero_eq(c, parent, rho, f, dec, f_dec, &last0); // noise_last = F dec
    let pow4_fdec = c.pow4(f_dec);
    // lift b0 through pow4: pow4(noise_last) = pow4(F dec).
    let pow4_lam = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.pow4(&w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let pow4_b0 = c.congr_arg_rat(&noise_last, f_dec, pow4_lam, b0); // pow4(noise_last)=pow4(Fdec)
    let b1 = base_pow4_eq_abs4(c, parent, f_dec, &abs_fdec, &hx); // pow4(Fdec) = abs4_left
                                                                  // pow4(noise_last) = abs4_left
    let pow4noise_eq_abs4 = c.trans_rat(&pow4_noise, &pow4_fdec, &abs4_left, pow4_b0, b1);
    let hval = c.symm_rat(&pow4_noise, &abs4_left, pow4noise_eq_abs4); // abs4_left = pow4(noise_last)

    // ── ofRat transport: ofRat abs4_left h4abs = ofRat pow4_noise (hnn last0).
    let hnn_last = Expr::app(hnn.clone(), last0.clone());
    let phi_last_val = c.ofrat(&pow4_noise, &hnn_last);
    let transport = ofrat_transport(c, parent, &abs4_left, &pow4_noise, &h4abs, &hnn_last, hval);
    // transport : ofRat abs4_left h4abs = phi_last_val.

    // chain: phi_last_val =[symm transport] ofRat abs4_left =[symm cubed] cube_contrib.
    let cubed_symm = c.symm_nn(&cube_contrib, &ofrat_abs4, cubed); // ofRat abs4_left = cube_contrib
    let transport_symm = c.symm_nn(&ofrat_abs4, &phi_last_val, transport); // phi_last_val = ofRat abs4_left
    c.trans_nn(
        &phi_last_val,
        &ofrat_abs4,
        &cube_contrib,
        transport_symm,
        cubed_symm,
    )
}

/// `noiseFn ρ 0 F last0 = F dec`.
/// `noiseFn_zero_dim ρ F last0 : noiseFn ρ 0 F last0 = F(dec)·density`; the density
/// `noiseDensityW ρ 0 (dec)(dec)` is `≡ Rat.one` defeq, so `Rat.mul_one (F dec) :
/// F(dec)·1 = F(dec)` closes (its LHS `F(dec)·1` is defeq `F(dec)·density`).
fn base_noise_zero_eq(
    c: &Hc43Consts,
    _parent: &EnvDeclBuilder,
    rho: &Expr,
    f: &Expr,
    dec: &Expr,
    f_dec: &Expr,
    last0: &Expr,
) -> Expr {
    let zero = c.nat_zero.clone();
    let noise_last = c.noise_fn(rho, &zero, f, last0);
    // noiseFn_zero_dim ρ F last0 : noise_last = F(dec)·noiseDensityW ρ 0 (dec)(dec).
    let zero_dim = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noiseFn_zero_dim"), vec![]),
        [rho.clone(), f.clone(), last0.clone()],
    );
    // density ≡ 1 defeq; F(dec)·density defeq F(dec)·1; Rat.mul_one (F dec) : F(dec)·1 = F(dec).
    let mul_one = Expr::app(
        Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
        f_dec.clone(),
    );
    let density = base_density_zero(c, rho, &zero, dec);
    let f_dec_dens = c.rmul(f_dec, &density);
    c.trans_rat(&noise_last, &f_dec_dens, f_dec, zero_dim, mul_one)
}

/// `noiseDensityW ρ 0 (dec)(dec)` (the n=0 density, ≡ Rat.one defeq).
fn base_density_zero(_c: &Hc43Consts, rho: &Expr, n: &Expr, dec: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noiseDensityW"), vec![]),
        [rho.clone(), n.clone(), dec.clone(), dec.clone()],
    )
}

/// `(abs4_left, h4abs)` where `abs4_left := ((|x|·|x|)·|x|)·|x|` and
/// `h4abs : 0 ≤ abs4_left` from `hx : 0 ≤ |x|` via `Rat.mul_nonneg`.
fn abs4_nonneg(c: &Hc43Consts, abs_x: &Expr, hx: &Expr) -> (Expr, Expr) {
    let xx = c.rmul(abs_x, abs_x);
    let xxx = c.rmul(&xx, abs_x);
    let xxxx = c.rmul(&xxx, abs_x);
    let mul_nn = |a: &Expr, b: &Expr, ha: Expr, hb: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a.clone(), b.clone(), ha, hb],
        )
    };
    let h_xx = mul_nn(abs_x, abs_x, hx.clone(), hx.clone());
    let h_xxx = mul_nn(&xx, abs_x, h_xx, hx.clone());
    let h_xxxx = mul_nn(&xxx, abs_x, h_xxx, hx.clone());
    (xxxx, h_xxxx)
}

/// The `cube_summand` of `norm43` at `n=0`: `fun jx : Fin (2^0) => contribution
/// (F,s,r,hs, decode 0 jx)` — byte-identical to `norm43`'s internal summand so the
/// collapse equation transports onto the δ-unfolded `norm43 0 F s r hs`.
fn norm43_cube_summand_zero(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
) -> Expr {
    let zero = c.nat_zero.clone();
    let fin = c.fin_of(&c.pow2(&zero));
    let mut d = EnvDeclBuilder::child_of(parent);
    let (jx_id, jx) = d.fresh_local(fin.clone());
    let x = c.decode(&zero, &jx);
    let body = c.contribution(f, s, r, hs, &x);
    d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, fin, body))
}

/// `pow4(x) = ((|x|·|x|)·|x|)·|x|` (`abs4_left |x|`) — the abs/pow reconciliation.
///
/// `pow4(x) = (x·x)·(x·x)`.  Route (all axiom-free over the faithful `Rat.abs`):
///  1. `x4_left := ((x·x)·x)·x` and `pow4(x) = x4_left` by `Rat.mul_assoc`
///     (`(x·x)·(x·x) = ((x·x)·x)·x`).
///  2. `x4_left = |x4_left|` by `(Rat.abs_of_nonneg x4_left h4).symm` (`x4_left ≥ 0`
///     via `Rat.mul_nonneg`… but x may be negative, so we instead go via abs_mul).
///
/// Simpler verified route used here: fold `|x|` powers UP to `|x⁴|` by `Rat.abs_mul`
/// (`|a|·|b| = |a·b|`, used as `.symm`), then `|x⁴_left| = x⁴_left` is NOT valid
/// without sign info — so we keep the target as `abs4_left` and prove
/// `abs4_left = |x4_left|` (abs_mul folding) and `|x4_left| = pow4(x)`?  No.
///
/// The correct identity is `pow4(x) = abs4_left(|x|)` because `pow4(x) = x⁴ =
/// |x|⁴` (even power). Proof: `|x|·|x| = |x·x|` (`abs_mul.symm`); `|x·x| = x·x`
/// (`abs_of_nonneg (x·x) (mul_self_nonneg)`); so `|x|·|x| = x·x`. Squaring this
/// equation (congr) and re-associating gives `abs4_left = (x·x)·(x·x) = pow4(x)`,
/// whence `pow4(x) = abs4_left` by symm.
fn base_pow4_eq_abs4(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    abs_x: &Expr,
    hx: &Expr,
) -> Expr {
    let _ = hx;
    // h_sq : |x|·|x| = x·x.
    //   abs_mul x x : |x·x| = |x|·|x|  ⇒ symm : |x|·|x| = |x·x|.
    let xx = c.rmul(x, x);
    let abs_xx = c.abs(&xx);
    let abs_x_sq = c.rmul(abs_x, abs_x);
    let abs_mul = Expr::apps(
        Expr::const_(Name::from_string("Rat.abs_mul"), vec![]),
        [x.clone(), x.clone()],
    ); // |x·x| = |x|·|x|
    let absxsq_eq_absxx = c.symm_rat(&abs_xx, &abs_x_sq, abs_mul); // |x|·|x| = |x·x|
                                                                   //   abs_of_nonneg (x·x) (h_xx_nn) : |x·x| = x·x.
    let h_xx_nn = Expr::app(
        Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
        x.clone(),
    ); // Rat.sq_nonneg x : 0 ≤ x·x.
    let abs_of_nonneg_xx = Expr::apps(
        Expr::const_(Name::from_string("Rat.abs_of_nonneg"), vec![]),
        [xx.clone(), h_xx_nn],
    ); // |x·x| = x·x
    let h_sq = c.trans_rat(&abs_x_sq, &abs_xx, &xx, absxsq_eq_absxx, abs_of_nonneg_xx); // |x|·|x| = x·x

    // abs4_left = (|x|·|x|)·(|x|·|x|)? No: abs4_left = ((|x|·|x|)·|x|)·|x| (left-nested).
    // We instead prove abs4_left = pow4(x) via the square of h_sq + re-assoc, but the
    // left-nesting differs. To match exactly, build abs4_left and pow4(x) and bridge
    // by `mul_assoc` after squaring h_sq. This sub-chain is `base_abs4_eq_pow4_tail`.
    base_abs4_eq_pow4_tail(c, parent, x, abs_x, &h_sq)
}

/// `pow4(x) = abs4_left(|x|)` given `h_sq : |x|·|x| = x·x`.
///
/// `abs4_left = ((|x|·|x|)·|x|)·|x|`. Re-associate to `(|x|·|x|)·(|x|·|x|)` via
/// `Rat.mul_assoc`/`mul_comm` group ops, then `congr` on `h_sq` (twice) to
/// `(x·x)·(x·x) = pow4(x)`. We build `abs4_left = (|x|·|x|)·(|x|·|x|)` (regroup),
/// then `(|x|·|x|)·(|x|·|x|) = (x·x)·(x·x)` (congr both factors with h_sq), giving
/// `abs4_left = pow4(x)`; symm yields `pow4(x) = abs4_left`.
fn base_abs4_eq_pow4_tail(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    abs_x: &Expr,
    h_sq: &Expr, // |x|·|x| = x·x
) -> Expr {
    let xx = c.rmul(x, x);
    let abs_sq = c.rmul(abs_x, abs_x); // |x|·|x|
    let abs4_left = c.x4_left(abs_x); // ((|x|·|x|)·|x|)·|x|
    let abs_sq_sq = c.rmul(&abs_sq, &abs_sq); // (|x|·|x|)·(|x|·|x|)
    let pow4_x = c.pow4(x); // (x·x)·(x·x)

    // regroup : abs4_left = abs_sq_sq.   ((|x|·|x|)·|x|)·|x| = (|x|·|x|)·(|x|·|x|).
    //   Rat.mul_assoc (|x|·|x|) |x| |x| : ((|x|·|x|)·|x|)·|x| = (|x|·|x|)·(|x|·|x|).
    let regroup = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
        [abs_sq.clone(), abs_x.clone(), abs_x.clone()],
    );

    // sq_lift : abs_sq_sq = pow4_x.   (|x|·|x|)·(|x|·|x|) = (x·x)·(x·x)  via congr both
    // with h_sq.
    let f_right = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(&abs_sq, &w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let f_left = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(&w, &xx);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let abs_xx = c.rmul(&abs_sq, &xx); // (|x|·|x|)·(x·x)
    let h_aa_ab = c.congr_arg_rat(&abs_sq, &xx, f_right, h_sq.clone()); // (|x|·|x|)·(|x|·|x|)=(|x|·|x|)·(x·x)
    let h_ab_bb = c.congr_arg_rat(&abs_sq, &xx, f_left, h_sq.clone()); // (|x|·|x|)·(x·x)=(x·x)·(x·x)
    let sq_lift = c.trans_rat(&abs_sq_sq, &abs_xx, &pow4_x, h_aa_ab, h_ab_bb);

    // abs4_left = abs_sq_sq = pow4_x ; symm ⇒ pow4_x = abs4_left.
    let abs4_eq_pow4 = c.trans_rat(&abs4_left, &abs_sq_sq, &pow4_x, regroup, sq_lift);
    c.symm_rat(&abs4_left, &pow4_x, abs4_eq_pow4)
}

/// `ofRat a ha = ofRat b hb` from `h : a = b` (proof-irrelevant transport through
/// `NNReal.ofRat`'s dependent nonneg argument), via `Eq.ndrec`.
///
/// `@Eq.ndrec Rat a (fun w => NNReal) (ofRat a ha) b h`?  No — the motive must
/// carry the proof. We use `@Eq.rec`-style: motive `fun (w : Rat)(hw : a = w) =>
/// Eq NNReal (ofRat a ha) (ofRat w ?)` is ill-typed (hw not 0≤w). Instead transport
/// the PROOF: `@Eq.ndrec Rat a (fun w => Rat.le 0 w) ha b h : 0 ≤ b`, call it `hb'`;
/// then `ofRat a ha = ofRat b hb'` by `congr` is still dependent. The clean route:
/// `@Eq.ndrec Rat a (fun w => Eq NNReal (ofRat a ha) (ofRat w (transp w))) (rfl) b h`
/// where the family is built with the transported proof. We implement it as the
/// standard dependent congruence `eqRecOn`.
fn ofrat_transport(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    ha: &Expr,
    hb: &Expr,
    h: Expr, // a = b
) -> Expr {
    // Motive: fun (w : Rat) => ∀ (hw : 0 ≤ w), Eq NNReal (ofRat a ha) (ofRat w hw).
    // Base at a: fun hw => Eq.refl-ish : ofRat a ha = ofRat a hw  (proof-irrel ⇒ rfl).
    // Transport along h to w := b, then apply hb.
    let le0 = |w: &Expr| c.rle(&c.rat_zero, w);
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let inner = {
            let mut d2 = EnvDeclBuilder::child_of(&d);
            let (hw_id, hw) = d2.fresh_local(le0(&w));
            let body = c.eq_nn(&c.ofrat(a, ha), &c.ofrat(&w, &hw));
            d2.finish_child(d2.mk_pi(hw_id, BinderInfo::Default, le0(&w), body))
        };
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), inner))
    };
    // base : motive a  =  fun (hw : 0≤a) => Eq.refl (ofRat a ha)  [ofRat a hw ≡ ofRat a ha by proof-irrel]
    let base = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (hw_id, _hw) = d.fresh_local(le0(a));
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![c.l1.clone()]),
            [c.nnreal.clone(), c.ofrat(a, ha)],
        );
        d.finish_child(d.mk_lam(hw_id, BinderInfo::Default, le0(a), refl))
    };
    // @Eq.ndrec Rat a motive base b h : motive b = ∀ (hw:0≤b), ofRat a ha = ofRat b hw.
    let ndrec = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![Level::zero(), c.l1.clone()],
        ),
        [c.rat.clone(), a.clone(), motive, base, b.clone(), h],
    );
    // apply to hb : ofRat a ha = ofRat b hb.
    Expr::app(ndrec, hb.clone())
}

/// `rhs = cube_contrib` — the RHS bridge.
/// `rhs := ofRat(powNat 4 0) · norm43_cubed 0 F s r hs`.
/// `norm43_cubed 0 = (norm43 0)³` δ-unfolds; `norm43 0 = finSum 1 (cube_summand)`
/// collapses to `contrib(dec)` (nn_sum_one_collapse), lifted through the cube;
/// then `ofRat(powNat 4 0)·X = X` (`mul_comm` + `mul_one`, `powNat 4 0 ≡ 1` defeq).
#[allow(clippy::too_many_arguments)]
fn base_rhs_bridge(
    c: &Hc43Consts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
    h4n: &Expr,
    cube_contrib: &Expr,
) -> Expr {
    let zero = c.nat_zero.clone();
    let one = c.succ(&zero);

    // norm43 0 F s r hs  (≡ finSum 1 cube_summand defeq).
    let norm43_0 = Expr::apps(
        c.norm43.clone(),
        [zero.clone(), f.clone(), s.clone(), r.clone(), hs.clone()],
    );
    let cube_norm = c.nnmul(&c.nnmul(&norm43_0, &norm43_0), &norm43_0); // = norm43_cubed 0 (defeq)

    // collapse: finSum 1 cube_summand = contrib(dec).  We state it on the unfolded
    // finSum (defeq to norm43_0).
    let cube_summand = norm43_cube_summand_zero(c, parent, f, s, r, hs);
    let finsum_1 = c.finsum(&one, &cube_summand);
    let collapse = nn_sum_one_collapse(c, parent, &cube_summand); // finsum_1 = contrib(dec)
    let contrib = c.contribution(f, s, r, hs, &c.decode(&zero, &c.last(&zero)));

    // norm43_0 = contrib(dec):  norm43_0 ≡ finsum_1 (defeq), so `collapse` (typed at
    // finsum_1) re-types at norm43_0 via defeq when used by congr below. To be safe
    // we transport: norm43_eq : norm43_0 = contrib   (collapse, defeq LHS).
    let norm43_eq = collapse; // : finsum_1 = contrib ; finsum_1 defeq norm43_0
    let _ = &finsum_1;

    // lift norm43_eq through the cube  (cube_norm = cube_contrib).
    // congr on (·³): we do three nested congrArg via the cube motive.
    let cube_lift = cube_congr(c, parent, &norm43_0, &contrib, norm43_eq);
    // cube_lift : (norm43_0·norm43_0)·norm43_0 = (contrib·contrib)·contrib = cube_contrib

    // scal = ofRat(powNat 4 0) h4n  (≡ ofRat 1 _ defeq).
    let scal = c.ofrat(&c.pow4n(&zero), h4n);
    let rhs = c.nnmul(&scal, &cube_norm); // = rhs (norm43_cubed 0 defeq cube_norm)

    // scal · cube_norm = cube_norm · scal  (mul_comm)
    let mul_comm = Expr::apps(
        Expr::const_(Name::from_string("NNReal.mul_comm"), vec![]),
        [scal.clone(), cube_norm.clone()],
    );
    let swapped = c.nnmul(&cube_norm, &scal);
    // cube_norm · scal = cube_norm   (mul_one ; scal defeq nnreal_one)
    let mul_one = Expr::app(
        Expr::const_(Name::from_string("NNReal.mul_one"), vec![]),
        cube_norm.clone(),
    );
    // chain: rhs = scal·cube_norm =[mul_comm] cube_norm·scal =[mul_one] cube_norm =[cube_lift] cube_contrib
    let t1 = c.trans_nn(&rhs, &swapped, &cube_norm, mul_comm, mul_one);
    c.trans_nn(&rhs, &cube_norm, cube_contrib, t1, cube_lift)
}

/// `(a·a)·a = (b·b)·b` from `h : a = b` — lift an equality through the left-nested
/// cube via nested `congrArg`.
fn cube_congr(c: &Hc43Consts, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, h: Expr) -> Expr {
    // sq lift: a·a = b·b  via congr both args.
    // (a·a) = (a·b): congrArg (fun w => a·w) h ; (a·b)=(b·b): congrArg (fun w => w·b) h.
    let aa = c.nnmul(a, a);
    let ab = c.nnmul(a, b);
    let bb = c.nnmul(b, b);
    let f_right = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.nnreal.clone());
        let body = c.nnmul(a, &w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let f_left = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.nnreal.clone());
        let body = c.nnmul(&w, b);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let h_aa_ab = c.congr_arg_nn(a, b, f_right, h.clone()); // a·a = a·b
    let h_ab_bb = c.congr_arg_nn(a, b, f_left, h.clone()); // a·b = b·b
    let h_sq = c.trans_nn(&aa, &ab, &bb, h_aa_ab, h_ab_bb); // a·a = b·b

    // cube lift: (a·a)·a = (b·b)·b  via congr both.
    let aaa = c.nnmul(&aa, a);
    let bba = c.nnmul(&bb, a);
    let bbb = c.nnmul(&bb, b);
    let f_cube_left = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.nnreal.clone());
        let body = c.nnmul(&w, a);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let f_cube_right = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(c.nnreal.clone());
        let body = c.nnmul(&bb, &w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let h_aaa_bba = c.congr_arg_nn(&aa, &bb, f_cube_left, h_sq); // (a·a)·a = (b·b)·a
    let h_bba_bbb = c.congr_arg_nn(a, b, f_cube_right, h); // (b·b)·a = (b·b)·b
    c.trans_nn(&aaa, &bba, &bbb, h_aaa_bba, h_bba_bbb)
}
