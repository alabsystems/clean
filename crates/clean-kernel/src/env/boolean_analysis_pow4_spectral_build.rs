// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_pow4_spectral.rs — the type + proof builders for
// `Fin.sum_pow4`.

/// The `Fin.sum_pow4` conclusion type
/// `∀ (n : Nat) (f : Fin n → Rat),
///    (Σf·Σf)·(Σf·Σf) = Σ_{j1}Σ_{j3}Σ_{j2}Σ_{j4} (f j1·f j2)·(f j3·f j4)`.
#[cfg(test)]
fn build_sum_pow4_type(c: &Pow4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.fin_to_rat(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    let s = c.sum(&n, f.clone());
    let lhs = c.mul(c.mul(s.clone(), s.clone()), c.mul(s.clone(), s));
    let rhs = build_quad_rhs(c, &b, &n, &f);
    let concl = c.eq_rat(lhs, rhs);

    let ty = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

/// `Σ_{j1} (fun j1 => Σ_{j3} (fun j3 => Σ_{j2} (fun j2 => Σ_{j4} (fun j4 =>
///   (f j1·f j2)·(f j3·f j4)))))` — the final quadruple-sum RHS, in the
/// `j1,j3,j2,j4` order that the three `Fin.sum_mul_sum` applications produce.
#[cfg(test)]
fn build_quad_rhs(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    c.sum(n, build_quad_j1_fn(c, parent, n, f))
}

/// `fun (j1 : Fin n) => Σ_{j3} Σ_{j2} Σ_{j4} (f j1·f j2)·(f j3·f j4)` — the outer
/// RHS integrand.
#[cfg(test)]
fn build_quad_j1_fn(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut j1b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j1_id, j1) = j1b.fresh_local(fin_n.clone());
    let fj1 = Expr::app(f.clone(), j1);
    let inner = build_quad_j3(c, &j1b, n, &fj1, f);
    j1b.finish_child(j1b.mk_lam(j1_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// `fun (j3 : Fin n) => Σ_{j2} Σ_{j4} (f j1·f j2)·(f j3·f j4)` at fixed `fj1 := f j1`.
#[cfg(test)]
fn build_quad_j3(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, fj1: &Expr, f: &Expr) -> Expr {
    let mut j3b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
    let fj3 = Expr::app(f.clone(), j3);
    let inner = build_quad_j2(c, &j3b, n, fj1, &fj3, f);
    j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// `fun (j2 : Fin n) => Σ_{j4} (f j1·f j2)·(f j3·f j4)` at fixed `fj1,fj3`.
#[cfg(test)]
fn build_quad_j2(
    c: &Pow4Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    fj1: &Expr,
    fj3: &Expr,
    f: &Expr,
) -> Expr {
    let mut j2b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j2_id, j2) = j2b.fresh_local(fin_n.clone());
    let left = c.mul(fj1.clone(), Expr::app(f.clone(), j2));
    let inner = c.quartic_inner_fn(&j2b, n, &left, fj3, f);
    j2b.finish_child(j2b.mk_lam(j2_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// Proof of `Fin.sum_pow4`.
#[cfg(test)]
fn build_sum_pow4_value(c: &Pow4Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.fin_to_rat(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());

    let s = c.sum(&n, f.clone());
    let ss = c.mul(s.clone(), s.clone());

    // h := fun j1 => Fin.sum n (fun j2 => f j1·f j2); D := Fin.sum n h.
    let h = c.h_fn(&b, &n, &f);
    let d = c.sum(&n, h.clone());

    // dms : S·S = D    (Fin.sum_mul_sum n n f f)
    let dms = c.sum_mul_sum(&n, &f, &f);

    // ── Step A : pow4(S) = D·D, lifting dms through both factors of (S·S)·(S·S).
    // legA1 : (S·S)·(S·S) = D·(S·S)   via congrArg (fun z => z·(S·S)) dms
    let left_fn = {
        let mut lb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = lb.fresh_local(c.rat.clone());
        let body = c.mul(z, ss.clone());
        lb.finish_child(lb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let leg_a1 = c.congr(ss.clone(), d.clone(), left_fn, dms.clone());
    let d_ss = c.mul(d.clone(), ss.clone());
    // legA2 : D·(S·S) = D·D    via congrArg (fun z => D·z) dms
    let right_fn = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = rb.fresh_local(c.rat.clone());
        let body = c.mul(d.clone(), z);
        rb.finish_child(rb.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let leg_a2 = c.congr(ss.clone(), d.clone(), right_fn, dms);
    let dd = c.mul(d.clone(), d.clone());
    let pow4_s = c.mul(ss.clone(), ss.clone());
    // legA : pow4(S) = D·D
    let leg_a = c.trans(pow4_s.clone(), d_ss.clone(), dd.clone(), leg_a1, leg_a2);

    // ── Step B : D·D = Σ_{j1} (Σ_{j3} h j1·h j3)   (Fin.sum_mul_sum n n h h)
    let leg_b = c.sum_mul_sum(&n, &h, &h);
    // e_mid := Fin.sum n (fun j1 => Fin.sum n (fun j3 => h j1·h j3))
    let e_mid = build_hh_double(c, &b, &n, &h);

    // ── Step C : e_mid = RHS   (Fin.sum_congr over j1 of Fin.sum_congr over j3 of
    //    the per-(j1,j3) sum_mul_sum expansion).
    let leg_c = build_leg_c(c, &b, &n, &f, &h);
    let rhs = build_quad_rhs(c, &b, &n, &f);

    // Assemble: pow4(S) = D·D = e_mid = RHS.
    let t1 = c.trans(pow4_s.clone(), dd.clone(), e_mid.clone(), leg_a, leg_b);
    let proof = c.trans(pow4_s, e_mid, rhs, t1, leg_c);

    let val = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

/// `Fin.sum n (fun j1 => Fin.sum n (fun j3 => Rat.mul (h j1) (h j3)))` — the
/// `Fin.sum_mul_sum n n h h` RHS (`D·D` expanded).
#[cfg(test)]
fn build_hh_double(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, h: &Expr) -> Expr {
    c.sum(n, build_hh_double_fn(c, parent, n, h))
}

/// `fun (j1 : Fin n) => Fin.sum n (fun j3 => Rat.mul (h j1) (h j3))` — the
/// `D·D` outer integrand.
#[cfg(test)]
fn build_hh_double_fn(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, h: &Expr) -> Expr {
    let mut j1b = EnvDeclBuilder::child_of(parent);
    let fin_n = c.fin_of(n);
    let (j1_id, j1) = j1b.fresh_local(fin_n.clone());
    let hj1 = Expr::app(h.clone(), j1);
    let inner = {
        let mut j3b = EnvDeclBuilder::child_of(&j1b);
        let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
        let body = c.mul(hj1.clone(), Expr::app(h.clone(), j3));
        j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), body))
    };
    j1b.finish_child(j1b.mk_lam(j1_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
}

/// Leg C proof : `Fin.sum n (fun j1 => Σ_{j3} h j1·h j3) = build_quad_rhs`.
/// `Fin.sum_congr` over `j1` of (`Fin.sum_congr` over `j3` of the per-(j1,j3)
/// `Fin.sum_mul_sum` expansion `h j1·h j3 = Σ_{j2}Σ_{j4} (f j1·f j2)·(f j3·f j4)`).
#[cfg(test)]
fn build_leg_c(c: &Pow4Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, h: &Expr) -> Expr {
    let fin_n = c.fin_of(n);

    // before_j1 : fun j1 => Σ_{j3} h j1·h j3   (the e_mid integrand)
    let before_j1 = build_hh_double_fn(c, parent, n, h);
    // after_j1 : fun j1 => Σ_{j3} Σ_{j2} Σ_{j4} (f j1·f j2)·(f j3·f j4)
    let after_j1 = build_quad_j1_fn(c, parent, n, f);
    // H_j1 : fun j1 => (Σ_{j3} h j1·h j3 = Σ_{j3} Σ_{j2} Σ_{j4} ...)
    //   = Fin.sum_congr over j3 of the per-(j1,j3) sum_mul_sum.
    let h_j1 = {
        let mut j1b = EnvDeclBuilder::child_of(parent);
        let (j1_id, j1) = j1b.fresh_local(fin_n.clone());
        let fj1 = Expr::app(f.clone(), j1.clone());
        let hj1 = Expr::app(h.clone(), j1);

        // before_j3 : fun j3 => h j1·h j3
        let before_j3 = {
            let mut j3b = EnvDeclBuilder::child_of(&j1b);
            let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
            let body = c.mul(hj1.clone(), Expr::app(h.clone(), j3));
            j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), body))
        };
        // after_j3 : fun j3 => Σ_{j2} Σ_{j4} (f j1·f j2)·(f j3·f j4)
        let after_j3 = {
            let mut j3b = EnvDeclBuilder::child_of(&j1b);
            let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
            let fj3 = Expr::app(f.clone(), j3);
            let inner = build_quad_j2(c, &j3b, n, &fj1, &fj3, f);
            j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), c.sum(n, inner)))
        };
        // H_j3 : fun j3 => (h j1·h j3 = Σ_{j2} Σ_{j4} ...) = Fin.sum_mul_sum n n (pj1)(pj3)
        let h_j3 = {
            let mut j3b = EnvDeclBuilder::child_of(&j1b);
            let (j3_id, j3) = j3b.fresh_local(fin_n.clone());
            let fj3 = Expr::app(f.clone(), j3);
            // pj1 := fun j2 => f j1·f j2  (= h j1 body); pj3 := fun j4 => f j3·f j4 (= h j3 body)
            let pj1 = c.pair_fn(&j3b, n, &fj1, f);
            let pj3 = c.pair_fn(&j3b, n, &fj3, f);
            // Fin.sum_mul_sum n n pj1 pj3 : (Σ pj1)·(Σ pj3) = Σ_{j2} Σ_{j4} pj1 j2·pj3 j4.
            // (Σ pj1) ≡ h j1, (Σ pj3) ≡ h j3 (def-eq), and pj1 j2·pj3 j4 ≡
            // (f j1·f j2)·(f j3·f j4) — exactly the quartic_inner integrand.
            let body = c.sum_mul_sum(n, &pj1, &pj3);
            j3b.finish_child(j3b.mk_lam(j3_id, BinderInfo::Default, fin_n.clone(), body))
        };
        let cong = c.sum_congr(n, &before_j3, &after_j3, h_j3);
        j1b.finish_child(j1b.mk_lam(j1_id, BinderInfo::Default, fin_n.clone(), cong))
    };
    c.sum_congr(n, &before_j1, &after_j1, h_j1)
}
