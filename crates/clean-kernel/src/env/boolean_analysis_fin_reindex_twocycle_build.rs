// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for `Rat.add_swap_outer` + `Fin.sum_reindex_twocycle_step`.
// `include!`d into `boolean_analysis_fin_reindex_twocycle_step.rs`; shares its
// `TwoCycleConsts` + imports.

// ===========================================================================
// Rat.add_swap_outer : ∀ a w b, (a + w) + b = (b + w) + a
//   chain: (a+w)+b = a+(w+b) = a+(b+w) = (a+b)+w = (b+a)+w = b+(a+w) = b+(w+a)
//          = (b+w)+a.
// ===========================================================================
fn add_swap_outer_type(c: &TwoCycleConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (bb_id, bb) = b.fresh_local(c.rat.clone());
    let lhs = c.add(c.add(a.clone(), w.clone()), bb.clone());
    let rhs = c.add(c.add(bb.clone(), w.clone()), a.clone());
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(bb_id, BinderInfo::Default, c.rat.clone(), concl);
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e))
}

fn add_swap_outer_value(c: &TwoCycleConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (bb_id, bb) = b.fresh_local(c.rat.clone());

    let assoc = Expr::const_(Name::from_string("Rat.add_assoc"), vec![]);
    let comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
    let rat_to_rat = Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone());

    // terms
    let aw = c.add(a.clone(), w.clone());
    let wb = c.add(w.clone(), bb.clone());
    let bw = c.add(bb.clone(), w.clone());
    let ab = c.add(a.clone(), bb.clone());
    let ba = c.add(bb.clone(), a.clone());
    let wa = c.add(w.clone(), a.clone());
    let aw_b = c.add(aw.clone(), bb.clone()); // (a+w)+b   [start]
    let a_wb = c.add(a.clone(), wb.clone()); // a+(w+b)
    let a_bw = c.add(a.clone(), bw.clone()); // a+(b+w)
    let ab_w = c.add(ab.clone(), w.clone()); // (a+b)+w
    let ba_w = c.add(ba.clone(), w.clone()); // (b+a)+w
    let b_aw = c.add(bb.clone(), aw.clone()); // b+(a+w)
    let b_wa = c.add(bb.clone(), wa.clone()); // b+(w+a)
    let bw_a = c.add(bw.clone(), a.clone()); // (b+w)+a   [goal]

    // s1 : (a+w)+b = a+(w+b)   [add_assoc a w b]
    let s1 = Expr::apps(assoc.clone(), [a.clone(), w.clone(), bb.clone()]);
    // s2 : a+(w+b) = a+(b+w)   [congrArg (a+·) (add_comm w b)]
    let comm_wb = Expr::apps(comm.clone(), [w.clone(), bb.clone()]);
    let add_a = Expr::app(c.rat_add.clone(), a.clone());
    let s2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            wb.clone(),
            bw.clone(),
            add_a,
            comm_wb,
        ],
    );
    // s3 : a+(b+w) = (a+b)+w   [(add_assoc a b w).symm]
    let assoc_abw = Expr::apps(assoc.clone(), [a.clone(), bb.clone(), w.clone()]);
    let s3 = Expr::apps(
        c.eq_symm.clone(),
        [c.rat.clone(), ab_w.clone(), a_bw.clone(), assoc_abw],
    );
    // s4 : (a+b)+w = (b+a)+w   [congrArg (·+w) (add_comm a b)]
    let comm_ab = Expr::apps(comm.clone(), [a.clone(), bb.clone()]);
    let add_flip_w = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = d.fresh_local(c.rat.clone());
        let body = c.add(x.clone(), w.clone());
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s4 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            ab.clone(),
            ba.clone(),
            add_flip_w,
            comm_ab,
        ],
    );
    // s5 : (b+a)+w = b+(a+w)   [add_assoc b a w]
    let s5 = Expr::apps(assoc.clone(), [bb.clone(), a.clone(), w.clone()]);
    // s6 : b+(a+w) = b+(w+a)   [congrArg (b+·) (add_comm a w)]
    let comm_aw = Expr::apps(comm.clone(), [a.clone(), w.clone()]);
    let add_b = Expr::app(c.rat_add.clone(), bb.clone());
    let s6 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            aw.clone(),
            wa.clone(),
            add_b,
            comm_aw,
        ],
    );
    // s7 : b+(w+a) = (b+w)+a   [(add_assoc b w a).symm]
    let assoc_bwa = Expr::apps(assoc.clone(), [bb.clone(), w.clone(), a.clone()]);
    let s7 = Expr::apps(
        c.eq_symm.clone(),
        [c.rat.clone(), bw_a.clone(), b_wa.clone(), assoc_bwa],
    );
    let _ = &rat_to_rat;

    // chain s1..s7
    let t = |l: Expr, m: Expr, r: Expr, p1: Expr, p2: Expr| -> Expr {
        Expr::apps(c.eq_trans.clone(), [c.rat.clone(), l, m, r, p1, p2])
    };
    let c12 = t(aw_b.clone(), a_wb.clone(), a_bw.clone(), s1, s2);
    let c123 = t(aw_b.clone(), a_bw.clone(), ab_w.clone(), c12, s3);
    let c1234 = t(aw_b.clone(), ab_w.clone(), ba_w.clone(), c123, s4);
    let c12345 = t(aw_b.clone(), ba_w.clone(), b_aw.clone(), c1234, s5);
    let c123456 = t(aw_b.clone(), b_aw.clone(), b_wa.clone(), c12345, s6);
    let proof = t(aw_b, b_wa, bw_a, c123456, s7);

    let e = b.mk_lam(bb_id, BinderInfo::Default, c.rat.clone(), proof);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e))
}

include!("boolean_analysis_fin_reindex_twocycle_build2.rs");
