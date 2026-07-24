// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_applyt_coeff_eigen_chain.rs — legD (the
// diagonal collapse over the spectral index T) and the top-level `eigen_value`.

impl CoeffConsts {
    /// `fun x => (Σ_T ρ^{|T|}·(χ_T x·χ_T y))·χ_S(x)` — the eigen `x`-integrand
    /// with `noiseDensityW` δ-unfolded (def-eq to `eigen_x_fn`). The proof chain
    /// runs over this explicit form; it checks against `eigen_type` (folded `W`)
    /// by reducibility of `noiseDensityW`.
    fn m0_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr, y: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let w_sum = self.ssum(n, self.w_summand_fn(&xb, rho, n, &x, y));
        let body = self.mul(w_sum, self.chi_(n, s, &x));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

/// legD (diagonal collapse over the spectral index `T`, at the decoded `jS`):
///   `Σ_T (ρ^{|T|}·χ_T y)·(Σ_x χ_T x·χ_S x) = (ρ^{|S|}·χ_S y)·2^n`,  `S = hcDecode jS`.
///
/// `subsetSum n (m3_t_fn)` δ-unfolds to `Fin.sum P (fun jT => f jT)` with
/// `f jT = (ρ^{|hcDec jT|}·χ_{hcDec jT} y)·(Σ_x χ_{hcDec jT} x·χ_S x)`.
///   • off-diagonal `jT ≠ jS`: `Σ_x χ_{hcDec jT} x·χ_{hcDec jS} x = 0`
///     (`chi_offdiag_subsetSum_zero n jT jS`), so `f jT = coeff·0 = 0`
///     (`Rat.mul_zero`);
///   • `Fin.sum_diag_collapse P jS f` lands `f jS = (ρ^{|S|}·χ_S y)·(Σ_x χ_S x·χ_S x)`;
///   • `chi_diag_subsetSum_cube n S : Σ_x χ_S x·χ_S x = 2^n`, lifted by
///     `congrArg ((ρ^{|S|}·χ_S y)·)`.
fn eigen_leg_d_js(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    js: &Expr,
    y: &Expr,
) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let s = c.hc_decode(n, js); // S = hcDecode n jS
    let hcp = c.hcpoint_of(n);

    // coeff_S := ρ^{|S|}·χ_S y.
    let coeff_s = c.mul(c.pow(rho, &c.set_size(n, &s)), c.chi_(n, &s, y));

    // f : Fin P → Rat := fun jT => (ρ^{|hcDec jT|}·χ_{hcDec jT} y)·(Σ_x χ_{hcDec jT} x·χ_S x).
    let f = {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let (jt_id, jt) = tb.fresh_local(fin_p.clone());
        let t = c.hc_decode(n, &jt);
        let coeff_t = c.mul(c.pow(rho, &c.set_size(n, &t)), c.chi_(n, &t, y));
        let chi_chi = c.ssum(n, c.chi_chi_fn(&tb, n, &t, &s));
        let body = c.mul(coeff_t, chi_chi);
        tb.finish_child(tb.mk_lam(jt_id, BinderInfo::Default, fin_p.clone(), body))
    };

    // hyp H : ∀ jT, (Eq (Fin P) jT jS → False) → f jT = 0.
    let hyp = {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let (jt_id, jt) = tb.fresh_local(fin_p.clone());
        let ne_ty = Expr::pi(
            BinderInfo::Default,
            c.eq_fin_pow(n, &jt, js),
            c.false_c.clone(),
        );
        let (ne_id, ne) = tb.fresh_local(ne_ty.clone());
        let t = c.hc_decode(n, &jt);
        let coeff_t = c.mul(c.pow(rho, &c.set_size(n, &t)), c.chi_(n, &t, y));
        let chi_chi = c.ssum(n, c.chi_chi_fn(&tb, n, &t, &s)); // Σ_x χ_{hcDec jT} x·χ_S x

        // off : Σ_x χ_{hcDec jT} x·χ_{hcDec jS} x = 0   (chi_offdiag_subsetSum_zero n jT jS ne).
        let off = Expr::apps(
            c.chi_offdiag.clone(),
            [n.clone(), jt.clone(), js.clone(), ne.clone()],
        );
        // mul_zero coeff_t : coeff_t·0 = 0.
        let mz = Expr::app(c.rat_mul_zero.clone(), coeff_t.clone());
        // congrArg (coeff_t·) off : coeff_t·(Σ_x …) = coeff_t·0.
        let cg = c.mul_left_congr(&tb, &coeff_t, chi_chi.clone(), c.rat_zero.clone(), off);
        // f jT = coeff_t·(Σ_x …) = coeff_t·0 = 0.
        let lhs = c.mul(coeff_t.clone(), chi_chi);
        let midd = c.mul(coeff_t, c.rat_zero.clone());
        let proof = c.trans(lhs, midd, c.rat_zero.clone(), cg, mz);
        let lam = tb.mk_lam(ne_id, BinderInfo::Default, ne_ty, proof);
        tb.finish_child(tb.mk_lam(jt_id, BinderInfo::Default, fin_p.clone(), lam))
    };

    // collapse : Fin.sum P f = f jS   (f jS = coeff_S·(Σ_x χ_S x·χ_S x)).
    let collapse = Expr::apps(
        c.fin_sum_diag_collapse.clone(),
        [pp.clone(), js.clone(), f, hyp],
    );

    // f jS = coeff_S·(Σ_x χ_S x·χ_S x). Rewrite Σ_x χ_S x·χ_S x → 2^n via chi_diag.
    let chi_diag_sum = c.ssum(n, c.chi_chi_fn(parent, n, &s, &s)); // Σ_x χ_S x·χ_S x
    let fjs = c.mul(coeff_s.clone(), chi_diag_sum.clone());
    let diag = Expr::apps(c.chi_diag.clone(), [n.clone(), s.clone()]); // : Σ_x χ_S x·χ_S x = 2^n
    let cube = c.cube(n);
    let leg_cube = c.mul_left_congr(parent, &coeff_s, chi_diag_sum, cube.clone(), diag);
    let target = c.mul(coeff_s, cube); // coeff_S·2^n = (ρ^{|S|}·χ_S y)·2^n

    // Σ_T(…) = f jS = coeff_S·2^n.   (The `Fin.sum P (decoded m3)` is def-eq to
    // `subsetSum n (m3_t_fn)`; both sides bridge through hcDecode.)
    let _ = hcp;
    let y_sum = c.fsum(pp, build_m3_tsum_dec(c, parent, rho, n, js, y));
    c.trans(y_sum, fjs, target, collapse, leg_cube)
}

/// `Fin.sum P f` body rebuilt to match `m3_t_fn` after the `subsetSum`-unfold at
/// the decoded spectral index `jT` (so legD's LHS is def-eq to `subsetSum n m3`).
fn build_m3_tsum_dec(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    js: &Expr,
    y: &Expr,
) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let s = c.hc_decode(n, js);
    let mut tb = EnvDeclBuilder::child_of(parent);
    let (jt_id, jt) = tb.fresh_local(fin_p.clone());
    let t = c.hc_decode(n, &jt);
    let coeff_t = c.mul(c.pow(rho, &c.set_size(n, &t)), c.chi_(n, &t, y));
    let chi_chi = c.ssum(n, c.chi_chi_fn(&tb, n, &t, &s));
    let body = c.mul(coeff_t, chi_chi);
    tb.finish_child(tb.mk_lam(jt_id, BinderInfo::Default, fin_p, body))
}

/// Final regroup `(ρ^{|S|}·χ_S y)·2^n = (2^n·ρ^{|S|})·χ_S y`.
/// `p := ρ^{|S|}`, `q := χ_S y`, `cc := 2^n`:
///   (p·q)·cc =[assoc]        p·(q·cc)
///            =[congr·comm]   p·(cc·q)
///            =[symm assoc]   (p·cc)·q
///            =[right·comm]   (cc·p)·q.
fn eigen_final_regroup(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    cc: &Expr,
) -> Expr {
    let lhs = c.mul(c.mul(p.clone(), q.clone()), cc.clone()); // (p·q)·cc
    let p_q_cc = c.mul(p.clone(), c.mul(q.clone(), cc.clone())); // p·(q·cc)
    let p_cc_q_inner = c.mul(p.clone(), c.mul(cc.clone(), q.clone())); // p·(cc·q)
    let pc_q = c.mul(c.mul(p.clone(), cc.clone()), q.clone()); // (p·cc)·q
    let rhs = c.mul(c.mul(cc.clone(), p.clone()), q.clone()); // (cc·p)·q

    // s1 : (p·q)·cc = p·(q·cc)   (mul_assoc p q cc).
    let s1 = c.mul_assoc(p, q, cc);
    // s2 : p·(q·cc) = p·(cc·q)   (congrArg (p·) (mul_comm q cc)).
    let s2 = c.mul_left_congr(
        parent,
        p,
        c.mul(q.clone(), cc.clone()),
        c.mul(cc.clone(), q.clone()),
        c.mul_comm(q, cc),
    );
    // s3 : p·(cc·q) = (p·cc)·q   (Eq.symm (mul_assoc p cc q)).
    let assoc2 = c.mul_assoc(p, cc, q); // (p·cc)·q = p·(cc·q)
    let s3 = c.symm(pc_q.clone(), p_cc_q_inner.clone(), assoc2);
    // s4 : (p·cc)·q = (cc·p)·q   (congrArg (·q) (mul_comm p cc)).
    let s4 = c.mul_right_congr(
        parent,
        q,
        c.mul(p.clone(), cc.clone()),
        c.mul(cc.clone(), p.clone()),
        c.mul_comm(p, cc),
    );

    let t1 = c.trans(lhs.clone(), p_q_cc, p_cc_q_inner.clone(), s1, s2);
    let t2 = c.trans(lhs.clone(), p_cc_q_inner, pc_q.clone(), t1, s3);
    c.trans(lhs, pc_q, rhs, t2, s4)
}

fn eigen_value(c: &CoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (js_id, js) = b.fresh_local(fin_p.clone());
    let hcp = c.hcpoint_of(&n);
    let (y_id, y) = b.fresh_local(hcp.clone());
    let s = c.hc_decode(&n, &js);

    // endpoint expressions (over the δ-unfolded W).
    let e0 = c.ssum(&n, c.m0_x_fn(&b, &rho, &n, &s, &y));
    let m1 = c.ssum(&n, c.m1_x_fn(&b, &rho, &n, &s, &y));
    let m2 = c.ssum(&n, c.m2_t_fn(&b, &rho, &n, &s, &y));
    let m3 = c.ssum(&n, c.m3_t_fn(&b, &rho, &n, &s, &y));

    let p = c.pow(&rho, &c.set_size(&n, &s)); // ρ^{|S|}
    let q = c.chi_(&n, &s, &y); // χ_S y
    let cube = c.cube(&n);
    let coeff_s = c.mul(p.clone(), q.clone()); // ρ^{|S|}·χ_S y
    let m4 = c.mul(coeff_s, cube.clone()); // (ρ^{|S|}·χ_S y)·2^n
    let rhs = c.mul(c.mul(cube.clone(), p.clone()), q.clone()); // (2^n·ρ^{|S|})·χ_S y

    // legA : e0 = m1   (subsetSum_congr over x of eigen_leg_a_x).
    let leg_a = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let pf = eigen_leg_a_x(c, &xb, &rho, &n, &s, &y, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ssum_congr(
            &n,
            &c.m0_x_fn(&b, &rho, &n, &s, &y),
            &c.m1_x_fn(&b, &rho, &n, &s, &y),
            h,
        )
    };

    // legB : m1 = m2   (subsetSum_swap n F).  F x T = χ_S(x)·(ρ^{|T|}·(χ_T x·χ_T y)).
    let leg_b = {
        let big_f = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let inner = {
                let mut tb = EnvDeclBuilder::child_of(&xb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let w = c.mul(
                    c.pow(&rho, &c.set_size(&n, &t)),
                    c.mul(c.chi_(&n, &t, &x), c.chi_(&n, &t, &y)),
                );
                let body = c.mul(c.chi_(&n, &s, &x), w);
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
            };
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), inner))
        };
        Expr::apps(c.subset_sum_swap.clone(), [n.clone(), big_f])
    };

    // legC : m2 = m3   (subsetSum_congr over T of eigen_leg_c_t).
    let leg_c = {
        let h = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let pf = eigen_leg_c_t(c, &tb, &rho, &n, &s, &y, &t);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ssum_congr(
            &n,
            &c.m2_t_fn(&b, &rho, &n, &s, &y),
            &c.m3_t_fn(&b, &rho, &n, &s, &y),
            h,
        )
    };

    // legD : m3 = m4   ((ρ^{|S|}·χ_S y)·2^n via the diagonal collapse over T).
    let leg_d = eigen_leg_d_js(c, &b, &rho, &n, &js, &y);

    // legE : m4 = rhs   ((ρ^{|S|}·χ_S y)·2^n = (2^n·ρ^{|S|})·χ_S y).
    let leg_e = eigen_final_regroup(c, &b, &p, &q, &cube);

    // Assemble: e0 = m1 = m2 = m3 = m4 = rhs.
    let t1 = c.trans(e0.clone(), m1.clone(), m2.clone(), leg_a, leg_b);
    let t2 = c.trans(e0.clone(), m2.clone(), m3.clone(), t1, leg_c);
    let t3 = c.trans(e0.clone(), m3.clone(), m4.clone(), t2, leg_d);
    let proof = c.trans(e0, m4, rhs, t3, leg_e);

    let val = b.mk_lam(y_id, BinderInfo::Default, hcp, proof);
    let val = b.mk_lam(js_id, BinderInfo::Default, fin_p, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}
