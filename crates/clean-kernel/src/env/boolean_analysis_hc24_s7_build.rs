// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Proof-term builder for `BoolAnalysis.hc24S7` (S7 parallelogram-summed).
//
// `include!`d into `boolean_analysis_hc24_s7.rs`; shares its `use`s and the
// `S7Consts` plumbing.

/// `fun (x' : Fin (2^n)) => sq (body (hcDecode n x'))` where `body` maps the
/// decoded point to a Rat (used for gSq / hSq leaves).
fn sq_decode_fn(
    c: &S7Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    make: &dyn Fn(&Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (x_id, x) = b.fresh_local(c.fin_of(&p2n));
    let dec = c.decode(n, &x);
    let body = c.sq(&make(&dec));
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (jx : Fin (2^(n+1))) => sq (F (hcDecode (n+1) jx))`.
fn fsq_fn(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let sn = c.succ(n);
    let p2sn = c.pow2(&sn);
    let (jx_id, jx) = b.fresh_local(c.fin_of(&p2sn));
    let dec = c.decode(&sn, &jx);
    let body = c.sq(&Expr::app(f.clone(), dec));
    b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&p2sn), body))
}

/// `fun (x' : Fin (2^n)) => (1+1)·sq (F (extend* n (hcDecode n x')))`.
fn two_extsq_fn(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, low: bool) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (x_id, x) = b.fresh_local(c.fin_of(&p2n));
    let dec = c.decode(n, &x);
    let ext = if low {
        c.ext_f(n, &dec)
    } else {
        c.ext_t(n, &dec)
    };
    let body = c.mul(c.two(), c.sq(&Expr::app(f.clone(), ext)));
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (x' : Fin (2^n)) => sq (F (extend* n (hcDecode n x')))`  (mSq / cSq).
fn extsq_fn(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, low: bool) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (x_id, x) = b.fresh_local(c.fin_of(&p2n));
    let dec = c.decode(n, &x);
    let ext = if low {
        c.ext_f(n, &dec)
    } else {
        c.ext_t(n, &dec)
    };
    let body = c.sq(&Expr::app(f.clone(), ext));
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (x' : Fin (2^n)) => gSq x' + hSq x'`  (pointwise sum of the two legs).
fn gh_sum_fn(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (x_id, x) = b.fresh_local(c.fin_of(&p2n));
    let dec = c.decode(n, &x);
    let gsq = c.sq(&c.g_part_at(n, f, &dec));
    let hsq = c.sq(&c.lift_h_at(n, f, &dec));
    let body = c.add(gsq, hsq);
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (x' : Fin (2^n)) => (1+1)·mSq x' + (1+1)·cSq x'`  (parallelogram RHS).
fn two_mc_sum_fn(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (x_id, x) = b.fresh_local(c.fin_of(&p2n));
    let dec = c.decode(n, &x);
    let msq = c.sq(&Expr::app(f.clone(), c.ext_f(n, &dec)));
    let csq = c.sq(&Expr::app(f.clone(), c.ext_t(n, &dec)));
    let body = c.add(c.mul(c.two(), msq), c.mul(c.two(), csq));
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (x' : Fin (2^n)) => Fsq (castP (idx (2^n) (2^n) x'))`  — one
/// `finSumPow2SuccSplit` half-summand, with `Fsq` applied to the reindexed
/// point. Built to be byte-identical to the split's LOW/HIGH summand.
fn split_half_fn(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, low: bool) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (x_id, x) = b.fresh_local(c.fin_of(&p2n));
    let idx = if low {
        c.cast_add.clone()
    } else {
        c.add_nat.clone()
    };
    let mapped = Expr::apps(idx, [p2n.clone(), p2n.clone(), x.clone()]);
    let casted = cast_p_s7(c, &b, n, &mapped);
    let fsq = fsq_fn(c, &b, n, f);
    let body = Expr::app(fsq, casted);
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `castP n M := @Eq.ndrec Nat (2^n+2^n) (fun m => Fin m) M (2^(n+1))
///   (Eq.symm (Nat.pow_two_succ n))` — byte-for-byte the transport used in
/// `finSumPow2SuccSplit` and the decode↔extend bridges.
fn cast_p_s7(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, mapped: &Expr) -> Expr {
    let nat = c.o.nat.clone();
    let p2n = c.pow2(n);
    let sum_pow = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [p2n.clone(), p2n.clone()],
    );
    let sn = c.succ(n);
    let p2sn = c.pow2(&sn);
    let e_fwd = Expr::app(
        Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
        n.clone(),
    );
    let e = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![c.l1.clone()]),
        [nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
    );
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = mb.fresh_local(nat.clone());
        let body = c.fin_of(&m);
        mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
    };
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![c.l1.clone(), c.l1.clone()],
        ),
        [nat, sum_pow, motive, mapped.clone(), p2sn, e],
    )
}

/// Build the type + proof of `BoolAnalysis.hc24S7`.
fn build_s7(c: &S7Consts) -> (Expr, Expr) {
    let make_g = |n: &Expr, f: &Expr| -> Box<dyn Fn(&Expr) -> Expr> {
        let c2 = S7Consts::new();
        let n = n.clone();
        let f = f.clone();
        Box::new(move |dec: &Expr| c2.g_part_at(&n, &f, dec))
    };
    let make_h = |n: &Expr, f: &Expr| -> Box<dyn Fn(&Expr) -> Expr> {
        let c2 = S7Consts::new();
        let n = n.clone();
        let f = f.clone();
        Box::new(move |dec: &Expr| c2.lift_h_at(&n, &f, dec))
    };

    // ── Type: ∀ n F, SG + SH = (1+1)·SF'.
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.o.nat.clone());
        let sn = c.succ(&n);
        let f_ty = c.o.f_type(&sn);
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let p2n = c.pow2(&n);
        let sn2 = c.succ(&n);
        let p2sn = c.pow2(&sn2);

        let sg = c.sum(&p2n, sq_decode_fn(c, &b, &n, &*make_g(&n, &f)));
        let sh = c.sum(&p2n, sq_decode_fn(c, &b, &n, &*make_h(&n, &f)));
        let sf = c.sum(&p2sn, fsq_fn(c, &b, &n, &f));
        let lhs = c.add(sg, sh);
        let rhs = c.mul(c.two(), sf);
        let body = c.eq_rat(lhs, rhs);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, body);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.o.nat.clone(), e);
        b.finish(e)
    };

    // ── Proof.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.o.nat.clone());
        let sn = c.succ(&n);
        let f_ty = c.o.f_type(&sn);
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let p2n = c.pow2(&n);
        let p2sn = c.pow2(&c.succ(&n));

        // Leaf functions.
        let gsq = sq_decode_fn(c, &b, &n, &*make_g(&n, &f));
        let hsq = sq_decode_fn(c, &b, &n, &*make_h(&n, &f));
        let msq = extsq_fn(c, &b, &n, &f, true);
        let csq = extsq_fn(c, &b, &n, &f, false);
        let fsq = fsq_fn(c, &b, &n, &f);
        let gh_sum = gh_sum_fn(c, &b, &n, &f);
        let two_mc = two_mc_sum_fn(c, &b, &n, &f);
        let two_m = two_extsq_fn(c, &b, &n, &f, true);
        let two_c = two_extsq_fn(c, &b, &n, &f, false);
        let low_half = split_half_fn(c, &b, &n, &f, true);
        let high_half = split_half_fn(c, &b, &n, &f, false);

        // Sums.
        let sg = c.sum(&p2n, gsq.clone());
        let sh = c.sum(&p2n, hsq.clone());
        let sm = c.sum(&p2n, msq.clone());
        let sc = c.sum(&p2n, csq.clone());
        let sf = c.sum(&p2sn, fsq.clone());
        let sum_ghsum = c.sum(&p2n, gh_sum.clone());
        let sum_two_mc = c.sum(&p2n, two_mc.clone());
        let sum_two_m = c.sum(&p2n, two_m.clone());
        let sum_two_c = c.sum(&p2n, two_c.clone());
        let sum_low = c.sum(&p2n, low_half.clone());
        let sum_high = c.sum(&p2n, high_half.clone());

        let two = c.two();
        let lhs = c.add(sg.clone(), sh.clone()); // SG + SH

        // step1 : SG + SH = Σ(gSq + hSq)   [symm (Fin.sum_add n gSq hSq)]
        let h_sum_add = c.sum_add(&p2n, &gsq, &hsq);
        let step1 = c.symm(sum_ghsum.clone(), lhs.clone(), h_sum_add);

        // step2 : Σ(gSq + hSq) = Σ((1+1)mSq + (1+1)cSq)   [sum_congr + parallelogram]
        let pw2 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = d.fresh_local(c.fin_of(&p2n));
            let dec = c.decode(&n, &x);
            let m = Expr::app(f.clone(), c.ext_f(&n, &dec));
            let cc = Expr::app(f.clone(), c.ext_t(&n, &dec));
            let body = c.parallelogram(&m, &cc); // type defeq to gh_sum x = two_mc x
            d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), body))
        };
        let step2 = c.sum_congr(&p2n, &gh_sum, &two_mc, pw2);

        // step3 : Σ((1+1)mSq + (1+1)cSq) = Σ((1+1)mSq) + Σ((1+1)cSq)   [Fin.sum_add]
        let step3 = c.sum_add(&p2n, &two_m, &two_c);

        // step4a : Σ((1+1)mSq) = (1+1)·SM   [Fin.sum_smul n (1+1) mSq]
        let step4a = c.sum_smul(&p2n, &two, &msq);
        // step4b : Σ((1+1)cSq) = (1+1)·SC
        let step4b = c.sum_smul(&p2n, &two, &csq);

        // Combine step4a/b into  Σ((1+1)mSq) + Σ((1+1)cSq) = (1+1)SM + (1+1)SC.
        let two_sm = c.mul(two.clone(), sm.clone());
        let two_sc = c.mul(two.clone(), sc.clone());
        let add_c = c.o.rat_add.clone();
        // congr left:  sum_two_m + sum_two_c = (1+1)SM + sum_two_c
        let h4l = congr_left_s7(
            c,
            &b,
            &add_c,
            sum_two_m.clone(),
            two_sm.clone(),
            sum_two_c.clone(),
            step4a,
        );
        let mid_4l = c.add(two_sm.clone(), sum_two_c.clone());
        // congr right: (1+1)SM + sum_two_c = (1+1)SM + (1+1)SC
        let h4r = congr_right_s7(
            c,
            &b,
            &add_c,
            sum_two_c.clone(),
            two_sc.clone(),
            two_sm.clone(),
            step4b,
        );
        let rhs_44 = c.add(two_sm.clone(), two_sc.clone());
        let step4 = c.trans(
            c.add(sum_two_m.clone(), sum_two_c.clone()),
            mid_4l,
            rhs_44.clone(),
            h4l,
            h4r,
        );

        // Chain so far:  SG+SH = sum_ghsum = sum_two_mc = (sum_two_m + sum_two_c) = (1+1)SM+(1+1)SC.
        let c12 = c.trans(
            lhs.clone(),
            sum_ghsum.clone(),
            sum_two_mc.clone(),
            step1,
            step2,
        );
        let c123 = c.trans(
            lhs.clone(),
            sum_two_mc.clone(),
            c.add(sum_two_m.clone(), sum_two_c.clone()),
            c12,
            step3,
        );
        let lhs_eq_4 = c.trans(
            lhs.clone(),
            c.add(sum_two_m.clone(), sum_two_c.clone()),
            rhs_44.clone(),
            c123,
            step4,
        );

        // ── SF' = SM + SC   (steps 5).
        // split : SF' = Σ low + Σ high   [finSumPow2SuccSplit n Fsq]
        let split = c.pow2_split(&n, &fsq);
        // low-congr : Σ low = SM    [sum_congr n low_half mSq <bridge-lifted>]
        let low_pw = bridge_pw(c, &b, &n, &f, true);
        let low_eq = c.sum_congr(&p2n, &low_half, &msq, low_pw);
        // high-congr : Σ high = SC
        let high_pw = bridge_pw(c, &b, &n, &f, false);
        let high_eq = c.sum_congr(&p2n, &high_half, &csq, high_pw);
        // SF' = Σ low + Σ high = SM + Σ high = SM + SC
        let split_rhs = c.add(sum_low.clone(), sum_high.clone());
        let hlc = congr_left_s7(
            c,
            &b,
            &add_c,
            sum_low.clone(),
            sm.clone(),
            sum_high.clone(),
            low_eq,
        );
        let mid_sf = c.add(sm.clone(), sum_high.clone());
        let hrc = congr_right_s7(
            c,
            &b,
            &add_c,
            sum_high.clone(),
            sc.clone(),
            sm.clone(),
            high_eq,
        );
        let sm_sc = c.add(sm.clone(), sc.clone());
        let split_eq_smsc = c.trans(split_rhs.clone(), mid_sf, sm_sc.clone(), hlc, hrc);
        // SF' = SM + SC
        let sf_eq_smsc = c.trans(
            sf.clone(),
            split_rhs.clone(),
            sm_sc.clone(),
            split,
            split_eq_smsc,
        );

        // ── close: (1+1)SM + (1+1)SC = (1+1)(SM+SC) = (1+1)SF'.
        // dist : (1+1)(SM+SC) = (1+1)SM + (1+1)SC
        let dist = c.ldist(&two, &sm, &sc);
        let two_smsc = c.mul(two.clone(), sm_sc.clone());
        // (1+1)SM+(1+1)SC = (1+1)(SM+SC)  [symm dist]
        let rhs44_eq_two_smsc = c.symm(two_smsc.clone(), rhs_44.clone(), dist);
        // (1+1)(SM+SC) = (1+1)SF'   [cong_right (1+1)·_ of symm(sf_eq_smsc)]
        let mul_c = c.o.rat_mul.clone();
        let smsc_eq_sf = c.symm(sf.clone(), sm_sc.clone(), sf_eq_smsc);
        let two_sf = c.mul(two.clone(), sf.clone());
        let two_smsc_eq_two_sf = congr_right_s7(
            c,
            &b,
            &mul_c,
            sm_sc.clone(),
            sf.clone(),
            two.clone(),
            smsc_eq_sf,
        );

        // rhs_44 = (1+1)(SM+SC) = (1+1)SF'
        let rhs44_eq_two_sf = c.trans(
            rhs_44.clone(),
            two_smsc.clone(),
            two_sf.clone(),
            rhs44_eq_two_smsc,
            two_smsc_eq_two_sf,
        );

        // Final: SG+SH = rhs_44 = (1+1)SF'.
        let proof = c.trans(
            lhs.clone(),
            rhs_44.clone(),
            two_sf.clone(),
            lhs_eq_4,
            rhs44_eq_two_sf,
        );

        let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.o.nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

/// `(x `op` fixed) = (y `op` fixed)` from `h : x = y` over `Rat`.
fn congr_left_s7(
    c: &S7Consts,
    parent: &EnvDeclBuilder,
    op: &Expr,
    x: Expr,
    y: Expr,
    fixed: Expr,
    h: Expr,
) -> Expr {
    let f = {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(c.rat());
        let body = Expr::apps(op.clone(), [w, fixed]);
        ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
    };
    c.congr_arg(x, y, f, h)
}

/// `(fixed `op` x) = (fixed `op` y)` from `h : x = y` over `Rat`.
fn congr_right_s7(
    c: &S7Consts,
    parent: &EnvDeclBuilder,
    op: &Expr,
    x: Expr,
    y: Expr,
    fixed: Expr,
    h: Expr,
) -> Expr {
    let f = {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = ch.fresh_local(c.rat());
        let body = Expr::apps(op.clone(), [fixed, w]);
        ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
    };
    c.congr_arg(x, y, f, h)
}

/// The pointwise hypothesis for the LOW/HIGH `Fin.sum_congr` fold:
/// `fun (x' : Fin (2^n)) => <proof : split_half x' = extSq x'>`, where the proof
/// lifts the decode↔extend bridge through `fun p => sq (F p)`.
///
/// `split_half x'` β-reduces to `sq (F (hcDecode (n+1) (castP (idx x'))))`, the
/// bridge rewrites the inner point to `extend* n (hcDecode n x')`, and the
/// `congrArg (fun p => sq (F p))` lift gives `= sq (F (extend* …)) = extSq x'`.
fn bridge_pw(c: &S7Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, low: bool) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let sn = c.succ(n);
    let (x_id, x) = b.fresh_local(c.fin_of(&p2n));

    // The inner decoded points.
    let idx = if low {
        c.cast_add.clone()
    } else {
        c.add_nat.clone()
    };
    let mapped = Expr::apps(idx, [p2n.clone(), p2n.clone(), x.clone()]);
    let casted = cast_p_s7(c, &b, n, &mapped);
    let from_pt = c.decode(&sn, &casted); // hcDecode (n+1) (castP (idx x'))
    let dec_n = c.decode(n, &x);
    let to_pt = if low {
        c.ext_f(n, &dec_n)
    } else {
        c.ext_t(n, &dec_n)
    }; // extend* n (dec x')

    // h_bridge : from_pt = to_pt.
    let h_bridge = c.bridge(low, n, &x);

    // lift through `fun (p : HCPoint (n+1)) => sq (F p)`.
    let lift_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = d.fresh_local(c.o.hcpoint_of(&sn));
        let body = c.sq(&Expr::app(f.clone(), p));
        d.finish_child(d.mk_lam(p_id, BinderInfo::Default, c.o.hcpoint_of(&sn), body))
    };
    // congrArg : sq(F from_pt) = sq(F to_pt)  — type defeq to split_half x' = extSq x'.
    let proof = c.congr_arg_pt(&sn, from_pt, to_pt, lift_fn, h_bridge);
    b.finish_child(b.mk_lam(x_id, BinderInfo::Default, c.fin_of(&p2n), proof))
}
