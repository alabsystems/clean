// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL UNCONDITIONAL dichotomy — main type + proof assembly. `include!`d into
// `boolean_analysis_kkl_maxinf_uncond_build.rs`.

/// Build the type (`for_value=false`) / proof (`for_value=true`) of
/// `BoolAnalysis.kkl_exists_max_influence_uncond`. The binder structure is
/// shared so the Pi type and the lambda value agree byte-for-byte.
fn build_uncond(c: &UncondConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());

    let kcast = c.natcast(&c.succ(&k)); // K := natCast(k+1)
    let nn = c.natcast(&n); // Nn := natCast n
    let p = c.p_of(&k); // P := K·9^k
    let q = c.q_of(&k); // Q := P+1
    let qq = c.mul(q.clone(), q.clone()); // QQ := Q·Q
    let two_nn = c.add(nn.clone(), nn.clone()); // 2n := Nn+Nn
    let var = c.variance_of(&n, &f);

    // hpos : Nat.lt 0 n  (≡ Nat.le (succ 0) n).
    let hpos_ty = c.pos_nat(&n);
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    // hthr : (k+1)·QQ ≤ Nn+Nn.
    let hthr_ty = c.rat_le(c.mul(kcast.clone(), qq.clone()), two_nn.clone());
    let (hthr_id, hthr) = b.fresh_local(hthr_ty.clone());
    // h0 : ∀ i, 0 ≤ Inf_i.
    let h0_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.rat_le(c.rat_zero.clone(), c.influence_of(&n, &f, &i));
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());

    // ∃ i, K·Var ≤ Nn·Inf_i + Nn·Inf_i.
    let concl = exists_concl(c, &b, &n, &f, &kcast, &nn, &var);

    let body = if for_value {
        build_uncond_body(
            c, &b, &n, &k, &f, &kcast, &nn, &p, &q, &qq, &two_nn, &concl, &hpos, &hthr, &h0,
        )
    } else {
        concl
    };

    // Wrap h0, then hthr, then hpos, then f, k, n.
    let e = if for_value {
        b.mk_lam(h0_id, BinderInfo::Default, h0_ty, body)
    } else {
        b.mk_pi(h0_id, BinderInfo::Default, h0_ty, body)
    };
    let e = if for_value {
        b.mk_lam(hthr_id, BinderInfo::Default, hthr_ty, e)
    } else {
        b.mk_pi(hthr_id, BinderInfo::Default, hthr_ty, e)
    };
    let e = if for_value {
        b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, e)
    } else {
        b.mk_pi(hpos_id, BinderInfo::Default, hpos_ty, e)
    };
    let e = if for_value {
        b.mk_lam(f_id, BinderInfo::Default, bf_ty, e)
    } else {
        b.mk_pi(f_id, BinderInfo::Default, bf_ty, e)
    };
    let e = if for_value {
        b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e)
    } else {
        b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e)
    };
    let e = if for_value {
        b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e)
    } else {
        b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e)
    };
    b.finish(e)
}

/// `∃ (i : Fin n), K·Var ≤ Nn·Inf_i + Nn·Inf_i` — matches the conditional
/// theorem's conclusion exactly. Built as a child of `parent` because the body
/// references the outer locals `n, f, kcast, nn, var`.
fn exists_concl(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    kcast: &Expr,
    nn: &Expr,
    var: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let pred = uncond_pred(c, parent, n, f, kcast, nn, var);
    Expr::apps(
        Expr::const_(Name::from_string("Exists"), vec![c.u1.clone()]),
        [fin_n, pred],
    )
}

/// `fun (i : Fin n) => K·Var ≤ Nn·Inf_i + Nn·Inf_i` — the existential predicate.
fn uncond_pred(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    kcast: &Expr,
    nn: &Expr,
    var: &Expr,
) -> Expr {
    let fin_n = c.fin_of(n);
    let mut d = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = d.fresh_local(fin_n.clone());
    let g_i = c.mul(nn.clone(), c.influence_of(n, f, &i));
    let body = c.rat_le(c.mul(kcast.clone(), var.clone()), c.add(g_i.clone(), g_i));
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
}

include!("boolean_analysis_kkl_maxinf_uncond_body.rs");
