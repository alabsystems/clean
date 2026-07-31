// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// STEP-2 holder-instantiation term builders (`build_step2`,
// `build_step2_value`, `lam_jx`, `forall_jx`). `include!`d into
// `boolean_analysis_kkl_dualhc_step2.rs` — shares its `Step2Consts` and imports.
// Split out to keep each file under the 500-line convention. (Regular `//`
// comments: inner doc `//!` is not allowed at an `include!` site.)

/// Build a `fun (jx : Fin (2^n)) => body(jx)` summand lambda over the cube index.
/// The per-point closure receives the CHILD builder so any nested binders chain
/// from it (disjoint FVarIds) — same discipline as `HolderConsts::lam_fn`.
fn lam_jx<F: Fn(&EnvDeclBuilder, &Expr) -> Expr>(
    c: &Step2Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    body: F,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let fin_pow = c.fin_of(&c.pow2(n));
    let (j_id, j) = d.fresh_local(fin_pow.clone());
    let b = body(&d, &j);
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_pow, b))
}

/// Build a `∀ (jx : Fin (2^n)), P(jx)` proof (`fun jx => proof`) or its type.
fn forall_jx<F: Fn(&EnvDeclBuilder, &Expr) -> Expr>(
    c: &Step2Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    as_pi: bool,
    body: F,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let fin_pow = c.fin_of(&c.pow2(n));
    let (j_id, j) = d.fresh_local(fin_pow.clone());
    let b = body(&d, &j);
    let e = if as_pi {
        d.mk_pi(j_id, BinderInfo::Default, fin_pow, b)
    } else {
        d.mk_lam(j_id, BinderInfo::Default, fin_pow, b)
    };
    d.finish_child(e)
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_step2_holder_inst`.
fn build_step2(c: &Step2Consts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let w_ty = c.hcpoint_to_rat(&n);
    let (w_id, w) = b.fresh_local(w_ty.clone());

    let half = c.half();
    let n_pow = c.pow2(&n);

    // The instantiation integrands over the cube index jx : Fin (2^n).
    //   e   jx := (D_i f (hcDecode n jx)) · half
    //   chi jx := (g·g)·(half·half),  g := D_i f (hcDecode n jx)
    //   w   jx := w (hcDecode n jx)
    let g_at = |jx: &Expr| {
        let x = c.decode(&n, jx);
        c.deriv(&n, &f, &x, &i)
    };
    let e_fn = lam_jx(c, &b, &n, |_d, jx| c.mul(g_at(jx), half.clone()));
    let chi_fn = lam_jx(c, &b, &n, |_d, jx| {
        let g = g_at(jx);
        c.mul(c.mul(g.clone(), g), c.mul(half.clone(), half.clone()))
    });
    let w_fn = lam_jx(c, &b, &n, |_d, jx| Expr::app(w.clone(), c.decode(&n, jx)));

    // m := Fin.sum (2^n) chi_fn  — the support measure.
    let m = c.fin_sum(&n_pow, chi_fn.clone());

    // The conclusion in the FOLDED subsetSum form (def-eq to R2's Fin.sum form).
    //   subsetSum n (fun x => (D_i f x · half)·(w x))
    //   subsetSum n (fun x => pow4 (w x))
    //   m := subsetSum n (fun x => (D_i f x · D_i f x)·(half·half))
    let m_folded = c.ssum(&n, {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let g = c.deriv(&n, &f, &x, &i);
        let body = c.mul(c.mul(g.clone(), g), c.mul(half.clone(), half.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    });
    let p_folded = c.ssum(&n, {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let g = c.deriv(&n, &f, &x, &i);
        let body = c.mul(c.mul(g, half.clone()), Expr::app(w.clone(), x.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    });
    let sumw4_folded = c.ssum(&n, {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = c.pow4(Expr::app(w.clone(), x.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    });
    let m_sq = c.mul(m_folded.clone(), m_folded.clone());
    let m_cube = c.mul(m_folded.clone(), m_sq);
    let concl = c.le(c.pow4(p_folded), c.mul(m_cube, sumw4_folded));

    let tail = if for_value {
        build_step2_value(
            c, &b, &n, &f, &i, &w, &half, &n_pow, &e_fn, &w_fn, &chi_fn, &m,
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, w_id, w_ty, tail);
    let e = bind(&b, i_id, c.fin_of(&n), e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term: `holder (2^n) e w chi m H1 H2 H3 H4 H5 H6`.
/// The result type is R2's conclusion in the UNFOLDED `Fin.sum` form, which is
/// def-eq to the stated (folded `subsetSum`) conclusion — the kernel discharges
/// the fold by δ-reducing `subsetSum`.
fn build_step2_value(
    c: &Step2Consts,
    b: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    i: &Expr,
    _w: &Expr,
    half: &Expr,
    n_pow: &Expr,
    e_fn: &Expr,
    w_fn: &Expr,
    chi_fn: &Expr,
    m: &Expr,
) -> Expr {
    // g (jx) := D_i f (hcDecode n jx);  (a,b) the Bool args.
    let g_at = |jx: &Expr| {
        let x = c.decode(n, jx);
        c.deriv(n, f, &x, i)
    };
    let args_at = |jx: &Expr| {
        let x = c.decode(n, jx);
        c.deriv_args(n, f, &x, i)
    };

    // H1 : ∀ jx, chi jx = (e jx)·(e jx)  := half_deriv_chi_eq_sq g.
    let h1 = forall_jx(c, b, n, false, |_d, jx| {
        Expr::app(c.half_chi_eq_sq.clone(), g_at(jx))
    });
    // H2 : ∀ jx, (e jx)·(chi jx) = e jx
    //    := half_deriv_e_chi_eq_e g (deriv_cube_eq_four_deriv a b).
    let h2 = forall_jx(c, b, n, false, |_d, jx| {
        let g = g_at(jx);
        let (a, bb) = args_at(jx);
        let hcube = Expr::apps(c.deriv_cube.clone(), [a, bb]);
        Expr::apps(c.half_e_chi_eq_e.clone(), [g, hcube])
    });
    // H3 : ∀ jx, (chi jx)·(chi jx) = chi jx
    //    := half_deriv_chi_sq_eq_chi g (disagree_sq_self_eq_four_mul a b).
    let h3 = forall_jx(c, b, n, false, |_d, jx| {
        let g = g_at(jx);
        let (a, bb) = args_at(jx);
        let hsq = Expr::apps(c.disagree_sq_self.clone(), [a, bb]);
        Expr::apps(c.half_chi_sq_eq_chi.clone(), [g, hsq])
    });
    // H4 : ∀ jx, chi jx ≤ 1
    //    := half_deriv_chi_le_one g (disagree_sq_le_four a b).
    let h4 = forall_jx(c, b, n, false, |_d, jx| {
        let g = g_at(jx);
        let (a, bb) = args_at(jx);
        let hle = Expr::apps(c.disagree_sq_le_four.clone(), [a, bb]);
        Expr::apps(c.half_chi_le_one.clone(), [g, hle])
    });
    // H5 : 0 ≤ m  := Fin.sum_nonneg (2^n) chi_fn (fun jx => 0 ≤ chi jx).
    //   chi jx = (g·g)·(half·half), so 0 ≤ chi jx
    //          := mul_nonneg (g·g) (half·half) (sq_nonneg g) (sq_nonneg half).
    let h5_proof = forall_jx(c, b, n, false, |_d, jx| {
        let g = g_at(jx);
        let gg = c.mul(g.clone(), g.clone());
        let hh = c.mul(half.clone(), half.clone());
        c.mul_nonneg(gg, hh, c.sq_nonneg(g), c.sq_nonneg(half.clone()))
    });
    let h5 = c.sum_nonneg(n_pow, chi_fn.clone(), h5_proof);
    // H6 : m = Fin.sum (2^n) chi  := Eq.refl (m is THAT sum).
    let h6 = c.eq_refl(m.clone());

    c.holder(
        n_pow,
        e_fn.clone(),
        w_fn.clone(),
        chi_fn.clone(),
        m.clone(),
        h1,
        h2,
        h3,
        h4,
        h5,
        h6,
    )
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_step2_m_eq_disagree_mass`.
fn build_m_eq_mass(c: &Step2Consts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let half = c.half();

    // chi_fn := fun x => (D_i f x · D_i f x)·(half·half)
    let chi_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let g = c.deriv(&n, &f, &x, &i);
        let body = c.mul(c.mul(g.clone(), g), c.mul(half.clone(), half.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    };
    // ind_fn := fun x => ind(disagree x)  (= Influence's summand)
    let ind_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = c.ind_of(c.disagree(&n, &f, &x, &i));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    };
    let lhs = c.ssum(&n, chi_fn.clone());
    let rhs = c.ssum(&n, ind_fn.clone());

    let tail = if for_value {
        // pointwise : ∀ x, (g·g)·(h·h) = ind(disagree x).
        let per_x = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = d.fresh_local(hcp.clone());
            let (a, bb) = c.deriv_args(&n, &f, &x, &i);
            let g = c.deriv(&n, &f, &x, &i);
            let gg = c.mul(g.clone(), g.clone());
            let hh = c.mul(half.clone(), half.clone());
            let ind = c.ind_of(c.disagree(&n, &f, &x, &i));
            let four = c.four();
            let four_ind = c.mul(four.clone(), ind.clone());
            let ind_four = c.mul(ind.clone(), four.clone());

            // s1 : (g·g)·(h·h) = (4·ind)·(h·h)   [congr (·(h·h)) (symm bridge)]
            let bridge = c.bridge(a, bb); // 4·ind = g·g
            let gg_eq_4ind = c.symm(four_ind.clone(), gg.clone(), bridge); // g·g = 4·ind
            let f1 = c.lam_rat(&d, |t| c.mul(t, hh.clone()));
            let s1 = c.congr_arg(gg.clone(), four_ind.clone(), f1, gg_eq_4ind);
            // s2 : (4·ind)·(h·h) = (ind·4)·(h·h)   [congr (·(h·h)) (mul_comm 4 ind)]
            let f2 = c.lam_rat(&d, |t| c.mul(t, hh.clone()));
            let s2 = c.congr_arg(
                four_ind.clone(),
                ind_four.clone(),
                f2,
                c.mul_comm(four.clone(), ind.clone()),
            );
            // s3 : (ind·4)·(h·h) = ind·(4·(h·h))   [mul_assoc ind 4 (h·h)]
            let s3 = c.mul_assoc(ind.clone(), four.clone(), hh.clone());
            // s4 : ind·(4·(h·h)) = ind·1   [congr (ind·) four_half_sq_eq_one]
            let four_hh = c.mul(four.clone(), hh.clone());
            let one = c.order.rat_one.clone();
            let f4 = c.lam_rat(&d, |t| c.mul(ind.clone(), t));
            let s4 = c.congr_arg(
                four_hh.clone(),
                one.clone(),
                f4,
                c.four_half_sq_eq_one.clone(),
            );
            // s5 : ind·1 = ind   [mul_one ind]
            let s5 = c.mul_one(ind.clone());

            // chain s1..s5.
            let gg_hh = c.mul(gg.clone(), hh.clone());
            let fourind_hh = c.mul(four_ind.clone(), hh.clone());
            let indfour_hh = c.mul(ind_four.clone(), hh.clone());
            let ind_fourhh = c.mul(ind.clone(), four_hh.clone());
            let ind_one = c.mul(ind.clone(), one.clone());
            let v12 = c.trans(
                gg_hh.clone(),
                fourind_hh.clone(),
                indfour_hh.clone(),
                s1,
                s2,
            );
            let v123 = c.trans(
                gg_hh.clone(),
                indfour_hh.clone(),
                ind_fourhh.clone(),
                v12,
                s3,
            );
            let v1234 = c.trans(gg_hh.clone(), ind_fourhh.clone(), ind_one.clone(), v123, s4);
            let pf = c.trans(gg_hh, ind_one, ind.clone(), v1234, s5);
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, pf))
        };
        c.ssum_congr(&n, chi_fn.clone(), ind_fn.clone(), per_x)
    } else {
        c.eq(lhs, rhs)
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, i_id, c.fin_of(&n), tail);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}
