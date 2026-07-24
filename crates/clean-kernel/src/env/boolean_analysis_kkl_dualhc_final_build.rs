// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// FINAL term builders (`build_cube_reassoc`, `build_final`). `include!`d into
// `boolean_analysis_kkl_dualhc_final.rs` — shares its `FinalConsts` and imports.
// (Regular `//` comments: inner doc `//!` is not allowed at an `include!` site.)

/// `(two·two)·two = eight` proof leaf, where `two := Rat.mk (Int.ofNat 2) 1`,
/// `eight := Rat.mk (Int.ofNat 8) 1` — built so the `eight` (`powNat 8`'s base)
/// matches `Rat.ofNat 8` def-eq. Returns `eight = (two·two)·two`.
fn eight_eq_two_cube(c: &FinalConsts, parent: &EnvDeclBuilder) -> Expr {
    // ofNat literals; the powNat bases (Rat.mk (ofNat k) 1) are def-eq to these.
    let two = c.ofnat(c.nat_lit(2));
    let four = c.ofnat(c.nat_lit(4));
    let eight = c.ofnat(c.nat_lit(8));
    // ofnat_mul 4 2 : ofNat(Nat.mul 4 2) = ofNat 4 · ofNat 2  ;  LHS ≡ ofNat 8.
    let h84 = c.ofnat_mul(c.nat_lit(4), c.nat_lit(2)); // 8 = four·two (defeq LHS)
    let four_two = c.mul(four.clone(), two.clone());
    // ofnat_mul 2 2 : ofNat(Nat.mul 2 2) = ofNat 2·ofNat 2 ; LHS ≡ ofNat 4.
    let h42 = c.ofnat_mul(c.nat_lit(2), c.nat_lit(2)); // 4 = two·two (defeq LHS)
    let two_two = c.mul(two.clone(), two.clone());
    // congrArg (·two) h42 : four·two = (two·two)·two.
    let f = c.lam_rat(parent, |t| c.mul(t, two.clone()));
    let cg = c.congr_arg(four.clone(), two_two.clone(), f, h42);
    let two_two_two = c.mul(two_two.clone(), two.clone());
    // trans : 8 = four·two = (two·two)·two.
    c.trans(eight, four_two, two_two_two, h84, cg)
}

/// Build the type/value of `dualhc_pow8_eq_two_pow_cube`.
fn build_cube_reassoc(c: &FinalConsts, for_value: bool) -> Expr {
    // goal n : powNat 8 n = ((powNat 2 n · powNat 2 n) · powNat 2 n).
    let goal = |n: &Expr| {
        let p2 = c.pow_lit(2, n);
        c.eq(
            c.pow_lit(8, n),
            c.mul(c.mul(p2.clone(), p2.clone()), p2.clone()),
        )
    };
    if !for_value {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)));
    }

    let mut b = EnvDeclBuilder::new();

    // motive := fun n => goal n.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = m.fresh_local(c.nat.clone());
        m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)))
    };

    // BASE n=0: goal 0 ≡ (1 = (1·1)·1). h:(1·1)·1=1 via mul_one twice; symm.
    let base = {
        let one = c.one();
        let one_one = c.mul(one.clone(), one.clone());
        let oo_o = c.mul(one_one.clone(), one.clone());
        let h1 = c.mul_one(one_one.clone()); // (1·1)·1 = 1·1
        let h2 = c.mul_one(one.clone()); // 1·1 = 1
        let h = c.trans(oo_o.clone(), one_one.clone(), one.clone(), h1, h2); // (1·1)·1 = 1
        c.symm(oo_o, one.clone(), h) // 1 = (1·1)·1
    };

    // STEP: fun (n)(ih : goal n) => goal (n+1).
    let step = {
        let mut s = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = s.fresh_local(c.nat.clone());
        let ih_ty = goal(&n);
        let (ih_id, ih) = s.fresh_local(ih_ty.clone());

        let two = c.ofnat(c.nat_lit(2)); // ofNat 2 ≡ powNat-2 base
        let eight = c.ofnat(c.nat_lit(8)); // ofNat 8 ≡ powNat-8 base
        let p2 = c.pow_lit(2, &n); // powNat 2 n
        let p8 = c.pow_lit(8, &n); // powNat 8 n
        let p2p2 = c.mul(p2.clone(), p2.clone());
        let p2cube = c.mul(p2p2.clone(), p2.clone()); // (p2·p2)·p2  (= RHS of ih)

        // succ : powNat 8 (n+1) = 8·p8.
        let succ8 = c.pownat_succ(eight.clone(), n.clone());
        // succ : powNat 2 (n+1) = 2·p2.
        let succ2 = c.pownat_succ(two.clone(), n.clone());
        let p2_succ = c.pow_lit(2, &c.succ(n.clone())); // powNat 2 (n+1)
        let two_p2 = c.mul(two.clone(), p2.clone()); // 2·p2

        // GOAL succ LHS = powNat 8 (n+1) ; RHS = ((p2'·p2')·p2'), p2' := powNat 2 (n+1).
        // Strategy: prove  8·p8 = ((2·p2)·(2·p2))·(2·p2)  [call it CORE], then
        // transport endpoints by succ8 (LHS) and succ2 (RHS factors).

        // CORE chain (right-to-left assembled, but I build left = 8·p8 to right):
        //   8·p8 = 8·((p2·p2)·p2)                       [congr (8·_) ih]
        //        = ((2·2)·2)·((p2·p2)·p2)               [congr (·((p2·p2)·p2)) (eight = (2·2)·2)]
        //        = ((2·2)·(p2·p2))·(2·p2)               [mmmc (2·2) 2 (p2·p2) p2]  ... need shape match
        //        = ((2·p2)·(2·p2))·(2·p2)               [congr (·(2·p2)) (mmmc 2 p2 2 p2 symm)]
        // Let me build it forward.
        let h_eight = eight_eq_two_cube(c, &s); // eight = (2·2)·2
        let two_two = c.mul(two.clone(), two.clone());
        let two_two_two = c.mul(two_two.clone(), two.clone()); // (2·2)·2

        // c1 : 8·p8 = 8·((p2·p2)·p2)   [congr (8·_) ih]
        let f1 = c.lam_rat(&s, |t| c.mul(eight.clone(), t));
        let c1 = c.congr_arg(p8.clone(), p2cube.clone(), f1, ih.clone());
        let eight_p2cube = c.mul(eight.clone(), p2cube.clone()); // 8·((p2·p2)·p2)
                                                                 // c2 : 8·((p2·p2)·p2) = ((2·2)·2)·((p2·p2)·p2)  [congr (·((p2·p2)·p2)) h_eight]
        let f2 = c.lam_rat(&s, |t| c.mul(t, p2cube.clone()));
        let c2 = c.congr_arg(eight.clone(), two_two_two.clone(), f2, h_eight);
        let ttt_p2cube = c.mul(two_two_two.clone(), p2cube.clone()); // ((2·2)·2)·((p2·p2)·p2)

        // Now regroup ((2·2)·2)·((p2·p2)·p2) into ((2·p2)·(2·p2))·(2·p2).
        // mmmc (2·2) 2 (p2·p2) p2 : ((2·2)·2)·((p2·p2)·p2) = ((2·2)·(p2·p2))·(2·p2).
        let c3 = c.mmmc(two_two.clone(), two.clone(), p2p2.clone(), p2.clone());
        let tt_p2p2 = c.mul(two_two.clone(), p2p2.clone()); // (2·2)·(p2·p2)
        let tt_p2p2_two_p2 = c.mul(tt_p2p2.clone(), two_p2.clone()); // ((2·2)·(p2·p2))·(2·p2)
                                                                     // (2·2)·(p2·p2) = (2·p2)·(2·p2)   [symm (mmmc 2 p2 2 p2)]
        let mmmc_2p2 = c.mmmc(two.clone(), p2.clone(), two.clone(), p2.clone()); // (2·p2)·(2·p2) = (2·2)·(p2·p2)
        let twop2_twop2 = c.mul(two_p2.clone(), two_p2.clone()); // (2·p2)·(2·p2)
        let h_tt = c.symm(twop2_twop2.clone(), tt_p2p2.clone(), mmmc_2p2); // (2·2)·(p2·p2) = (2·p2)·(2·p2)
                                                                           // congr (·(2·p2)) h_tt : ((2·2)·(p2·p2))·(2·p2) = ((2·p2)·(2·p2))·(2·p2)
        let f4 = c.lam_rat(&s, |t| c.mul(t, two_p2.clone()));
        let c4 = c.congr_arg(tt_p2p2.clone(), twop2_twop2.clone(), f4, h_tt);
        let core_rhs = c.mul(twop2_twop2.clone(), two_p2.clone()); // ((2·p2)·(2·p2))·(2·p2)

        // assemble CORE: 8·p8 = ... = ((2·p2)·(2·p2))·(2·p2).
        let k1 = c.trans(
            c.mul(eight.clone(), p8.clone()),
            eight_p2cube.clone(),
            ttt_p2cube.clone(),
            c1,
            c2,
        );
        let k2 = c.trans(
            c.mul(eight.clone(), p8.clone()),
            ttt_p2cube.clone(),
            tt_p2p2_two_p2.clone(),
            k1,
            c3,
        );
        let core = c.trans(
            c.mul(eight.clone(), p8.clone()),
            tt_p2p2_two_p2.clone(),
            core_rhs.clone(),
            k2,
            c4,
        );
        // core : 8·p8 = ((2·p2)·(2·p2))·(2·p2).

        // Transport LHS endpoint: succ8 : powNat 8 (n+1) = 8·p8 ;  trans → goal LHS.
        // chain1 : powNat 8 (n+1) = ((2·p2)·(2·p2))·(2·p2).
        let pow8_succ = c.pow_lit(8, &c.succ(n.clone()));
        let chain1 = c.trans(
            pow8_succ.clone(),
            c.mul(eight.clone(), p8.clone()),
            core_rhs.clone(),
            succ8,
            core,
        );

        // Transport RHS: replace each (2·p2) by p2' via succ2 (symm). Use Eq.subst
        // with motive (fun t => powNat 8 (n+1) = ((t·t)·t)), at a := 2·p2, b := p2'.
        // succ2 : p2' = 2·p2 ; symm : 2·p2 = p2'.
        let succ2_sym = c.symm(p2_succ.clone(), two_p2.clone(), succ2); // 2·p2 = p2'
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&s);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.eq(
                pow8_succ.clone(),
                c.mul(c.mul(t.clone(), t.clone()), t.clone()),
            );
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        // chain1 : motive (2·p2) (since core_rhs = ((2·p2)·(2·p2))·(2·p2)).
        let goal_succ = c.subst(motive, two_p2.clone(), p2_succ.clone(), succ2_sym, chain1);

        let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, goal_succ);
        s.finish_child(s.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let (n_id, n) = b.fresh_local(c.nat.clone());
    let rec = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec))
}

/// Build the type/value of `dualhc_final_le`.
fn build_final(c: &FinalConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let (r_id, r) = b.fresh_local(c.rat());

    let half = c.half();
    let four = c.four();
    let g = c.deriv_lam(&b, &n, &f, &i);
    let tg = c.op(&n, &g);

    // W := subsetSum n (fun y => (tg y)·(tg y)).
    let w = c.ssum(&n, {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = c.mul(tgy.clone(), tgy);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp, body))
    });
    let ww = c.mul(w.clone(), w.clone());

    // m := subsetSum n (fun x => (g x·g x)·(half·half)).
    let m = c.ssum(&n, {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let gx = Expr::app(g.clone(), x.clone());
        let body = c.mul(c.mul(gx.clone(), gx), c.mul(half.clone(), half.clone()));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    });
    let m_cube = c.mul(m.clone(), c.mul(m.clone(), m.clone())); // m·(m·m)
    let p2 = c.pow_lit(2, &n); // powNat 2 n
    let p8 = c.pow_lit(8, &n); // powNat 8 n
    let x_val = c.mul(m.clone(), p2.clone()); // X := m·2^n

    // IsRpow32 X r → W ≤ 4·r.
    let hyp = c.is_rpow32_of(&x_val, &r);
    let concl = c.le(w.clone(), c.mul(four.clone(), r.clone()));
    let (hyp_id, hyp_v) = b.fresh_local(hyp.clone());

    let tail = if for_value {
        // step4 n f i : W·W ≤ (4·4)·(m_cube·8^n).
        let step4 = Expr::apps(c.step4.clone(), [n.clone(), f.clone(), i.clone()]);
        let sixteen = c.mul(four.clone(), four.clone());
        let mc_p8 = c.mul(m_cube.clone(), p8.clone()); // m_cube·8^n
                                                       // We must rewrite (4·4)·(m_cube·8^n) into (4·4)·((X·X)·X), X := m·2^n.
                                                       // KEY identity: m_cube·8^n = (X·X)·X.
                                                       //   8^n = (p2·p2)·p2  [cube_reassoc]
                                                       //   m_cube·8^n = (m·(m·m))·((p2·p2)·p2)
                                                       //              = (X·X)·X  via mmmc/mul_assoc regroup (X = m·p2).
                                                       // Build:  e8 : m_cube·8^n = m_cube·((p2·p2)·p2)  [congr (m_cube·_) cube_reassoc]
        let cube_reassoc = Expr::app(c.pow8_cube.clone(), n.clone()); // 8^n = (p2·p2)·p2
        let p2cube = c.mul(c.mul(p2.clone(), p2.clone()), p2.clone()); // (p2·p2)·p2
        let f8 = c.lam_rat(&b, |t| c.mul(m_cube.clone(), t));
        let e8 = c.congr_arg(p8.clone(), p2cube.clone(), f8, cube_reassoc); // m_cube·8^n = m_cube·((p2·p2)·p2)
        let mc_p2cube = c.mul(m_cube.clone(), p2cube.clone()); // m_cube·((p2·p2)·p2)

        // Now prove m_cube·((p2·p2)·p2) = (X·X)·X  with X = m·p2.
        //   m_cube = m·(m·m).  Regroup (m·(m·m))·((p2·p2)·p2).
        //   = (m·(m·m))·((p2·p2)·p2)
        //   First reassoc m_cube to (m·m)·m : mul_assoc m m m gives (m·m)·m = m·(m·m);
        //   we keep m_cube = m·(m·m) and pair carefully. Use:
        //   mmmc (m·m) m (p2·p2) p2 : ((m·m)·m)·((p2·p2)·p2) = ((m·m)·(p2·p2))·(m·p2)
        //   but m_cube = m·(m·m), not (m·m)·m. Bridge via mul_comm? Instead set up
        //   the whole thing as ((m·p2)·(m·p2))·(m·p2) and prove EQ to m_cube·8^n
        //   directly via a single mmmc-based chain on X·X·X.
        //   Easiest: prove (X·X)·X = m_cube·((p2·p2)·p2) and symm.
        //     X·X = (m·p2)·(m·p2) = (m·m)·(p2·p2)  [mmmc m p2 m p2]
        //     (X·X)·X = ((m·m)·(p2·p2))·(m·p2)
        //             = ((m·m)·m)·((p2·p2)·p2)      [mmmc (m·m) (p2·p2) m p2]
        //     ((m·m)·m) = m·(m·m) = m_cube           [mul_assoc m m m]
        //     so (X·X)·X = (m·(m·m))·((p2·p2)·p2) = m_cube·((p2·p2)·p2).
        let x = x_val.clone();
        let xx = c.mul(x.clone(), x.clone()); // X·X
        let xxx = c.mul(xx.clone(), x.clone()); // (X·X)·X
        let mm = c.mul(m.clone(), m.clone());
        let mm_p2p2 = c.mul(mm.clone(), c.mul(p2.clone(), p2.clone())); // (m·m)·(p2·p2)
                                                                        // s1 : X·X = (m·m)·(p2·p2)   [mmmc m p2 m p2]
        let s1 = c.mmmc(m.clone(), p2.clone(), m.clone(), p2.clone());
        // congr (·X) s1 : (X·X)·X = ((m·m)·(p2·p2))·X    (X = m·p2)
        let f_x = c.lam_rat(&b, |t| c.mul(t, x.clone()));
        let s1c = c.congr_arg(xx.clone(), mm_p2p2.clone(), f_x, s1); // (X·X)·X = ((m·m)·(p2·p2))·(m·p2)
        let mmp2p2_x = c.mul(mm_p2p2.clone(), x.clone()); // ((m·m)·(p2·p2))·(m·p2)
                                                          // s2 : ((m·m)·(p2·p2))·(m·p2) = ((m·m)·m)·((p2·p2)·p2)  [mmmc (m·m) (p2·p2) m p2]
        let s2 = c.mmmc(
            mm.clone(),
            c.mul(p2.clone(), p2.clone()),
            m.clone(),
            p2.clone(),
        );
        let mmm = c.mul(mm.clone(), m.clone()); // (m·m)·m
        let mmm_p2cube = c.mul(mmm.clone(), p2cube.clone()); // ((m·m)·m)·((p2·p2)·p2)
                                                             // s3 : ((m·m)·m) = m·(m·m) = m_cube   [mul_assoc m m m]
        let s3 = c.mul_assoc(m.clone(), m.clone(), m.clone()); // (m·m)·m = m·(m·m)
                                                               // congr (·((p2·p2)·p2)) s3 : ((m·m)·m)·((p2·p2)·p2) = m_cube·((p2·p2)·p2)
        let f_cube = c.lam_rat(&b, |t| c.mul(t, p2cube.clone()));
        let s3c = c.congr_arg(mmm.clone(), m_cube.clone(), f_cube, s3);
        // chain : (X·X)·X = m_cube·((p2·p2)·p2).
        let t1 = c.trans(xxx.clone(), mmp2p2_x.clone(), mmm_p2cube.clone(), s1c, s2);
        let xxx_eq_mcp2cube = c.trans(xxx.clone(), mmm_p2cube.clone(), mc_p2cube.clone(), t1, s3c);
        // m_cube·8^n = (X·X)·X : symm e8 gives m_cube·((p2·p2)·p2) = m_cube·8^n;
        //   then symm xxx_eq → m_cube·((p2·p2)·p2) = (X·X)·X reversed... assemble:
        //   m_cube·8^n = m_cube·((p2·p2)·p2)  [e8]
        //              = (X·X)·X               [symm xxx_eq_mcp2cube]
        let mcp2cube_eq_xxx = c.symm(xxx.clone(), mc_p2cube.clone(), xxx_eq_mcp2cube); // m_cube·((p2·p2)·p2) = (X·X)·X
        let mcp8_eq_xxx = c.trans(
            mc_p8.clone(),
            mc_p2cube.clone(),
            xxx.clone(),
            e8,
            mcp2cube_eq_xxx,
        ); // m_cube·8^n = (X·X)·X

        // Transport step4 `W·W ≤ (4·4)·(m_cube·8^n)` along (m_cube·8^n = (X·X)·X):
        //   motive t := W·W ≤ (4·4)·t.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(ww.clone(), c.mul(sixteen.clone(), t));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let sq_le = c.subst(motive, mc_p8.clone(), xxx.clone(), mcp8_eq_xxx, step4);
        // sq_le : W·W ≤ (4·4)·((X·X)·X) — the descent's hypothesis shape.

        // 0 ≤ W := Fin.sum_nonneg over (Tg)² ≥ 0 (decoded Fin summand).
        let w_per = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(c.fin_pow(&n));
            let decode = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
                [n.clone(), j.clone()],
            );
            let tgy = Expr::app(tg.clone(), decode);
            let body = c.sq_nonneg(tgy);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        let w_decoded_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(c.fin_pow(&n));
            let decode = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
                [n.clone(), j.clone()],
            );
            let tgy = Expr::app(tg.clone(), decode);
            let body = c.mul(tgy.clone(), tgy);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        let w_nonneg = c.fin_sum_nonneg(&c.pow2_nat(&n), w_decoded_fn, w_per); // 0 ≤ W

        // descent W X r (0≤W) (IsRpow32 X r) (W² ≤ 16·X³) : W ≤ 4·r.
        Expr::apps(
            c.descent.clone(),
            [w.clone(), x_val.clone(), r.clone(), w_nonneg, hyp_v, sq_le],
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
    let e = bind(&b, hyp_id, hyp, tail);
    let e = bind(&b, r_id, c.rat(), e);
    let e = bind(&b, i_id, c.fin_of(&n), e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}
