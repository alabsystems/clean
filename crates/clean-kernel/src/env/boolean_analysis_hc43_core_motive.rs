// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_hc43_core.rs` — the `Nat.rec` motive (witness
// bundle quantified INSIDE) + the conditional assembly. No new globals.

/// `motive m := ∀ (F s r : HCPoint m → Rat)(hs)(hr)(hr1)(hrecon)(hnn)(h4n),
///   <hc43_core_concl ρ m F s r hs hnn h4n>` — the per-level induction predicate
/// with the witness bundle quantified inside (so the step instantiates at
/// `gPart`/`liftH`). Returns the Π-telescope body at the free `m` over `parent`.
fn motive_body(c: &Hc43Consts, parent: &EnvDeclBuilder, rho: &Expr, m: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fn_ty = c.f_type(m);
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let (s_id, s) = b.fresh_local(fn_ty.clone());
    let (r_id, r) = b.fresh_local(fn_ty.clone());
    let hs_ty = forall_scale_nonneg_ty(c, &b, m, &s);
    let (hs_id, hs) = b.fresh_local(hs_ty.clone());
    let hr_ty = forall_r_nonneg_ty(c, &b, m, &r);
    let (hr_id, _hr) = b.fresh_local(hr_ty.clone());
    let hr1_ty = forall_r_lt_one_ty(c, &b, m, &r);
    let (hr1_id, _hr1) = b.fresh_local(hr1_ty.clone());
    let hrecon_ty = forall_recon_ty(c, &b, m, &f, &s, &r);
    let (hrecon_id, _hrecon) = b.fresh_local(hrecon_ty.clone());
    let hnn_ty = forall_lhs_nonneg_ty(c, &b, rho, m, &f);
    let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
    let h4n_ty = c.rle(&c.rat_zero, &c.pow4n(m));
    let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

    let concl = hc43_core_concl(c, &b, rho, m, &f, &s, &r, &hs, &hnn, &h4n);

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

/// `fun (m : Nat) => motive_body m` — the `Nat.rec` motive lambda.
fn motive_lam(c: &Hc43Consts, parent: &EnvDeclBuilder, rho: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let body = motive_body(c, &b, rho, &m);
    b.finish_child(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
}

/// `STEP_TYPE ρ := ∀ (m : Nat), motive m → motive (m+1)` — the explicit induction
/// step hypothesis (the §11 cross-term tower, supplied as a minor premise).
fn step_ty(c: &Hc43Consts, parent: &EnvDeclBuilder, rho: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let mot_m = motive_body(c, &b, rho, &m);
    let sm = c.succ(&m);
    let mot_sm = motive_body(c, &b, rho, &sm);
    let arrow = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (ih_id, _ih) = d.fresh_local(mot_m.clone());
        d.finish_child(d.mk_pi(ih_id, BinderInfo::Default, mot_m.clone(), mot_sm))
    };
    b.finish_child(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), arrow))
}

/// Build the type + proof of `BoolAnalysis.hc43_core`.
fn build_hc43_core(c: &Hc43Consts) -> (Expr, Expr) {
    let nat = c.nat.clone();

    // ── Type: ∀ ρ n, (3·ρ²≤1) → (h_step : STEP_TYPE) → motive n.
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (n_id, n) = b.fresh_local(nat.clone());
        let h_ty = hyp_contract_ty(c, &rho);
        let (h_id, _h) = b.fresh_local(h_ty.clone());
        let hstep_ty = step_ty(c, &b, &rho);
        let (hstep_id, _hstep) = b.fresh_local(hstep_ty.clone());
        let mot_n = motive_body(c, &b, &rho, &n);

        let e = b.mk_pi(hstep_id, BinderInfo::Default, hstep_ty, mot_n);
        let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), e))
    };

    // ── Proof: fun ρ n h h_step => Nat.rec motive base h_step n.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat.clone());
        let (n_id, n) = b.fresh_local(nat.clone());
        let h_ty = hyp_contract_ty(c, &rho);
        let (h_id, h) = b.fresh_local(h_ty.clone());
        let hstep_ty = step_ty(c, &b, &rho);
        let (hstep_id, hstep) = b.fresh_local(hstep_ty.clone());

        let base = build_base_minor(c, &b, &rho, &h);
        let mtv = motive_lam(c, &b, &rho);
        let zero = c.nat_zero.clone();
        let _ = zero;

        // @Nat.rec.{0} motive base h_step n : motive n.
        let rec = Expr::apps(
            Expr::const_(
                Name::from_string("Nat.rec"),
                vec![crate::level::Level::zero()],
            ),
            [mtv, base, hstep.clone(), n.clone()],
        );

        let e = b.mk_lam(hstep_id, BinderInfo::Default, hstep_ty, rec);
        let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
        b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), e))
    };

    (ty, value)
}

/// The base minor premise `motive 0`:
/// `fun F s r hs hr hr1 hrecon hnn h4n => hc43_core_base ρ F s r hs hr hr1 hrecon
///   hnn h4n h` (feeding the captured contraction `h` to the base's hcontract
/// slot). Reshapes `hc43_core_base`'s telescope into the motive's witness-bundle
/// shape at `m = 0`.
fn build_base_minor(c: &Hc43Consts, parent: &EnvDeclBuilder, rho: &Expr, h: &Expr) -> Expr {
    let zero = c.nat_zero.clone();
    let base_const = Expr::const_(Name::from_string("BoolAnalysis.hc43_core_base"), vec![]);

    let mut b = EnvDeclBuilder::child_of(parent);
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
    let hnn_ty = forall_lhs_nonneg_ty(c, &b, rho, &zero, &f);
    let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
    let h4n_ty = c.rle(&c.rat_zero, &c.pow4n(&zero));
    let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

    // hc43_core_base ρ F s r hs hr hr1 hrecon hnn h4n h : concl 0 F s r hs hnn h4n.
    let body = Expr::apps(
        base_const,
        [
            rho.clone(),
            f.clone(),
            s.clone(),
            r.clone(),
            hs.clone(),
            hr.clone(),
            hr1.clone(),
            hrecon.clone(),
            hnn.clone(),
            h4n.clone(),
            h.clone(),
        ],
    );

    let e = b.mk_lam(h4n_id, BinderInfo::Default, h4n_ty, body);
    let e = b.mk_lam(hnn_id, BinderInfo::Default, hnn_ty, e);
    let e = b.mk_lam(hrecon_id, BinderInfo::Default, hrecon_ty, e);
    let e = b.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, e);
    let e = b.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
    let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
    let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
    b.finish_child(e)
}
