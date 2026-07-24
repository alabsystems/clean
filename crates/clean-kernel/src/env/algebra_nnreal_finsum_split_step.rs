// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// `NNReal.finSum_split_add` — type + `Nat.rec.{0}` (induction on `b`, `a` fixed)
// proof. Byte-for-byte the structure of the landed Rat `Fin.sum_split_add`
// (`nn_verify_fin_sum_split_proof.rs`), lifted to `NNReal`. `include!`d into
// `algebra_nnreal_finsum_split.rs`.

/// Theorem type: `∀ (a b : Nat) (h : Fin (a+b) → NNReal), <concl_body>`.
fn build_split_type(c: &C) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let (bb_id, bb) = b.fresh_local(c.nat.clone());
    let h_ty = c.fin_to_nnreal(&c.add_nat_(&a, &bb));
    let (h_id, h) = b.fresh_local(h_ty.clone());
    let concl = concl_body(c, &b, &a, &bb, &h);
    let r = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    let r = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), r))
}

/// Motive for `Nat.rec` (induction on `b`), `a` captured:
/// `fun (b : Nat) => ∀ (h : Fin (a+b) → NNReal), <concl_body a b h>`.
fn build_split_motive(c: &C, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (b_id, bb) = mb.fresh_local(c.nat.clone());
    let h_ty = c.fin_to_nnreal(&c.add_nat_(a, &bb));
    let (h_id, h) = mb.fresh_local(h_ty.clone());
    let concl = concl_body(c, &mb, a, &bb, &h);
    let pi = mb.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
    mb.finish_child(mb.mk_lam(b_id, BinderInfo::Default, c.nat.clone(), pi))
}

/// Base case `M 0`, `a` captured: `fun (h : Fin (a+0) → NNReal) => proof`.
fn build_split_base(c: &C, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
    let mut bb = EnvDeclBuilder::child_of(parent);
    let h_ty = c.fin_to_nnreal(&c.add_nat_(a, &c.nat_zero));
    let (h_id, h) = bb.fresh_local(h_ty.clone());

    // low := fun (i : Fin a) => h (castAdd a 0 i)
    let low = {
        let h = h.clone();
        let a = a.clone();
        let zero = c.nat_zero.clone();
        lam_fin(c, &bb, &a.clone(), move |_b, i| {
            Expr::app(h.clone(), c.cast_add(&a, &zero, &i))
        })
    };
    let s_low = c.sum(a, &low);
    let s_h = c.sum(a, &h); // ≡ finSum (a+0) h since a+0 ≡ a.

    // e1 : finSum a h = finSum a low   (finSum_congr, pw i : h i = h (castAdd a 0 i)).
    let pw = {
        let a2 = a.clone();
        reindex_pw(
            c,
            &bb,
            a,
            a, // big = a (castAdd a 0 i : Fin (a+0) ≡ Fin a)
            &h,
            |_c, x| x,
            move |cc, x| cc.cast_add(&a2, &cc.nat_zero.clone(), &x),
        )
    };
    let e1 = c.sum_congr(a, &h, &low, pw);

    // e2 : add s_low zero = s_low  (NNReal.add_zero s_low); symm.
    let e2 = Expr::app(c.nnreal_add_zero.clone(), s_low.clone());
    let s_low_plus_zero = c.nadd(&s_low, &c.base.nnreal_zero.clone());
    let e2s = c.symm(&s_low_plus_zero, &s_low, e2);

    // proof : finSum a h = add s_low zero  =  trans e1 e2s.
    let proof = c.trans(&s_h, &s_low, &s_low_plus_zero, e1, e2s);
    bb.finish_child(bb.mk_lam(h_id, BinderInfo::Default, h_ty, proof))
}

/// Step `fun (b' : Nat) (ih : M b') (h : Fin (a+succ b') → NNReal) => proof`.
#[allow(clippy::too_many_lines)]
fn build_split_step(c: &C, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (bp_id, bp) = sb.fresh_local(c.nat.clone()); // b'
    let m = c.add_nat_(a, &bp); // m := a + b'
    let ih_ty = {
        let h_ty = c.fin_to_nnreal(&m);
        let (h_id, h) = sb.fresh_local(h_ty.clone());
        let concl = concl_body(c, &sb, a, &bp, &h);
        sb.mk_pi(h_id, BinderInfo::Default, h_ty, concl)
    };
    let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

    let sbp = c.succ(&bp); // succ b'
    let a_sbp = c.add_nat_(a, &sbp); // a + succ b' ≡ succ m
    let h_ty = c.fin_to_nnreal(&a_sbp);
    let (h_id, h) = sb.fresh_local(h_ty.clone());

    // h_cs : Fin m → NNReal := fun x => h (castSucc m x)  (the IH summand).
    let h_cs = {
        let h = h.clone();
        let m = m.clone();
        lam_fin(c, &sb, &m.clone(), move |_b, x| {
            Expr::app(h.clone(), c.cast_succ(&m, &x))
        })
    };

    // ── LHS expansion: finSum (succ m) h = add (finSum m h_cs) (h (last m)). ──
    let h_last_m = Expr::app(h.clone(), c.last(&m));
    let s_m_hcs = c.sum(&m, &h_cs);
    let lhs = c.sum(&c.succ(&m), &h);
    let step_l = Expr::apps(c.nnreal_finsum_succ.clone(), [m.clone(), h.clone()]);
    let lvl0 = c.nadd(&s_m_hcs, &h_last_m);

    // ── IH at h_cs: finSum m h_cs = add P0 Q0. ──
    let p0_fn = {
        let h_cs = h_cs.clone();
        let a = a.clone();
        let bp = bp.clone();
        lam_fin(c, &sb, &a.clone(), move |_b, i| {
            Expr::app(h_cs.clone(), c.cast_add(&a, &bp, &i))
        })
    };
    let q0_fn = {
        let h_cs = h_cs.clone();
        let a = a.clone();
        let bp = bp.clone();
        lam_fin(c, &sb, &bp.clone(), move |_b, j| {
            Expr::app(h_cs.clone(), c.add_nat_idx(&a, &bp, &j))
        })
    };
    let p0 = c.sum(a, &p0_fn);
    let q0 = c.sum(&bp, &q0_fn);
    let ih_app = Expr::app(ih.clone(), h_cs.clone());
    let ih_rhs = c.nadd(&p0, &q0);

    // step_ih : lvl0 = add ih_rhs (h (last m))  (congr left via ih_app).
    let add_right_lastm = {
        let last = h_last_m.clone();
        let mut bld = EnvDeclBuilder::child_of(&sb);
        let (x_id, x) = bld.fresh_local(c.nnreal());
        let body = c.nadd(&x, &last);
        bld.finish_child(bld.mk_lam(x_id, BinderInfo::Default, c.nnreal(), body))
    };
    let lvl1 = c.nadd(&ih_rhs, &h_last_m);
    let step_ih = c.congr_nn_fn(&s_m_hcs, &ih_rhs, add_right_lastm, ih_app);

    // ── target RHS pieces. ──
    let p_fn = {
        let h = h.clone();
        let a = a.clone();
        let sbp = sbp.clone();
        lam_fin(c, &sb, &a.clone(), move |_b, i| {
            Expr::app(h.clone(), c.cast_add(&a, &sbp, &i))
        })
    };
    let p = c.sum(a, &p_fn);
    let high_fn = {
        let h = h.clone();
        let a = a.clone();
        let sbp = sbp.clone();
        lam_fin(c, &sb, &sbp.clone(), move |_b, j| {
            Expr::app(h.clone(), c.add_nat_idx(&a, &sbp, &j))
        })
    };
    let s_high = c.sum(&sbp, &high_fn);
    let step_r = Expr::apps(c.nnreal_finsum_succ.clone(), [bp.clone(), high_fn.clone()]);
    let q_fn = {
        let high_fn = high_fn.clone();
        let bp = bp.clone();
        lam_fin(c, &sb, &bp.clone(), move |_b, j| {
            Expr::app(high_fn.clone(), c.cast_succ(&bp, &j))
        })
    };
    let q = c.sum(&bp, &q_fn);
    let rr = Expr::app(high_fn.clone(), c.last(&bp));
    let q_plus_r = c.nadd(&q, &rr);

    // ── C1 : P0 = P. ──
    let big = a_sbp.clone();
    let c1_pw = {
        let a2 = a.clone();
        let bp2 = bp.clone();
        let m2 = m.clone();
        let a4 = a.clone();
        let sbp2 = sbp.clone();
        reindex_pw(
            c,
            &sb,
            a,
            &big,
            &h,
            move |cc, i| cc.cast_succ(&m2, &cc.cast_add(&a2, &bp2, &i)),
            move |cc, i| cc.cast_add(&a4, &sbp2, &i),
        )
    };
    let c1 = c.sum_congr(a, &p0_fn, &p_fn, c1_pw);

    // ── C2 : Q0 = Q. ──
    let c2_pw = {
        let a2 = a.clone();
        let bp2 = bp.clone();
        let m2 = m.clone();
        let a3 = a.clone();
        let bp3 = bp.clone();
        let sbp3 = sbp.clone();
        reindex_pw(
            c,
            &sb,
            &bp,
            &big,
            &h,
            move |cc, j| cc.cast_succ(&m2, &cc.add_nat_idx(&a2, &bp2, &j)),
            move |cc, j| cc.add_nat_idx(&a3, &sbp3, &cc.cast_succ(&bp3, &j)),
        )
    };
    let c2 = c.sum_congr(&bp, &q0_fn, &q_fn, c2_pw);

    // ── C3 : r0 = r (last terms). ──
    let last_m = c.last(&m);
    let an_last = c.add_nat_idx(a, &sbp, &c.last(&bp));
    let c3 = {
        let refl = Expr::apps(c.eq_refl_nat.clone(), [c.nat.clone(), c.val(&big, &last_m)]);
        let eqf = Expr::apps(
            c.fin_eq_of_val.clone(),
            [big.clone(), last_m.clone(), an_last.clone(), refl],
        );
        Expr::apps(
            c.congr_arg_fn.clone(),
            [
                c.fin_n(&big),
                c.nnreal(),
                last_m.clone(),
                an_last.clone(),
                h.clone(),
                eqf,
            ],
        )
    };

    // ── assemble: rewrite lvl1 = add (add P0 Q0) r0 into add (add P Q) r, reassoc. ──
    let add_pq_right_q0 = mk_add_right(c, &sb, &q0);
    let add_pq_left_p = mk_add_left(c, &sb, &p);
    let a1 = c.congr_nn_fn(&p0, &p, add_pq_right_q0, c1);
    let a2v = c.congr_nn_fn(&q0, &q, add_pq_left_p, c2);
    let pq0 = c.nadd(&p0, &q0);
    let pq = c.nadd(&p, &q);
    let s1 = c.trans(&pq0, &c.nadd(&p, &q0), &pq, a1, a2v);

    let add_r0 = mk_add_right(c, &sb, &h_last_m);
    let s2 = c.congr_nn_fn(&pq0, &pq, add_r0, s1);

    let add_pq_left = mk_add_left(c, &sb, &pq);
    let s3 = c.congr_nn_fn(&h_last_m, &rr, add_pq_left, c3);

    let s4 = Expr::apps(
        c.nnreal_add_assoc.clone(),
        [p.clone(), q.clone(), rr.clone()],
    );

    let step_r_sym = c.symm(&s_high, &q_plus_r, step_r);
    let s5 = c.congr_nn_fn(&q_plus_r, &s_high, mk_add_left(c, &sb, &p), step_r_sym);

    // ── chain. ──
    let t1 = c.nadd(&pq, &h_last_m);
    let t2 = c.nadd(&pq, &rr);
    let t3 = c.nadd(&p, &q_plus_r);
    let target_rhs = c.nadd(&p, &s_high);

    let chain = c.trans(&lhs, &lvl0, &lvl1, step_l, step_ih);
    let chain = c.trans(&lhs, &lvl1, &t1, chain, s2);
    let chain = c.trans(&lhs, &t1, &t2, chain, s3);
    let chain = c.trans(&lhs, &t2, &t3, chain, s4);
    let proof = c.trans(&lhs, &t3, &target_rhs, chain, s5);

    let lam = sb.mk_lam(h_id, BinderInfo::Default, h_ty, proof);
    let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, lam);
    sb.finish_child(sb.mk_lam(bp_id, BinderInfo::Default, c.nat.clone(), lam))
}

/// `fun (w : NNReal) => NNReal.add w r`, fresh per call.
fn mk_add_right(c: &C, parent: &EnvDeclBuilder, r: &Expr) -> Expr {
    let r = r.clone();
    let mut bld = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = bld.fresh_local(c.nnreal());
    let body = c.nadd(&x, &r);
    bld.finish_child(bld.mk_lam(x_id, BinderInfo::Default, c.nnreal(), body))
}

/// `fun (w : NNReal) => NNReal.add l w`, fresh per call.
fn mk_add_left(c: &C, parent: &EnvDeclBuilder, l: &Expr) -> Expr {
    let l = l.clone();
    let mut bld = EnvDeclBuilder::child_of(parent);
    let (x_id, x) = bld.fresh_local(c.nnreal());
    let body = c.nadd(&l, &x);
    bld.finish_child(bld.mk_lam(x_id, BinderInfo::Default, c.nnreal(), body))
}

fn build_split_value(c: &C) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nat.clone());
    let motive = build_split_motive(c, &b, &a);
    let base = build_split_base(c, &b, &a);
    let step = build_split_step(c, &b, &a);
    let (b_id, bb) = b.fresh_local(c.nat.clone());
    let rec_app = Expr::apps(c.nat_rec0.clone(), [motive, base, step, bb]);
    let lam = b.mk_lam(b_id, BinderInfo::Default, c.nat.clone(), rec_app);
    b.finish(b.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam))
}
