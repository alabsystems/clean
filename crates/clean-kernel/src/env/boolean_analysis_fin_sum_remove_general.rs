// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The general `Fin.sum_remove` proof body (the `Nat.rec` / `Fin.lastCases`
// assembly: `last` minor = `Fin.sum_remove_last`, `castSucc p'` minor = the
// interior reindex using coherences A/B + IH + `Rat.add_assoc`).
//
// `include!`d into `boolean_analysis_fin_sum_remove.rs` to keep each file under
// the 500-line convention; it shares that module's `RemoveConsts` + imports.

// ===========================================================================
// Fin.sum_remove : (k)(p : Fin (k+1))(F : Fin (k+1) → Rat) →
//   Fin.sum (k+1) F = Rat.add (F p) (Fin.sum k (fun j => F (skipNth k p j)))
//
// Value: fun k => @Nat.rec.{0} M base step k, where M k ≡ ∀ p F, <goal>.
// ===========================================================================
fn sum_remove_type(c: &RemoveConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let body = c.motive_body(&b, &k); // ∀ p F, <goal at k>
    b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), body))
}

/// The `last`-minor of the `Fin.lastCases` at level `lvl` (`p = last lvl`):
/// the goal is exactly `Fin.sum_remove_last lvl F`.  Returns a proof term of
/// `Fin.sum (lvl+1) F = Rat.add (F (last lvl)) (Fin.sum lvl (F∘skipNth lvl (last lvl)))`.
fn last_minor(_c: &RemoveConsts, lvl: &Expr, f: &Expr) -> Expr {
    let srl = Expr::const_(Name::from_string("Fin.sum_remove_last"), vec![]);
    Expr::apps(srl, [lvl.clone(), f.clone()])
}

/// The `castSucc`-minor at level `m+1` of the step (`p = castSucc (m+1) p'`).
/// `ih : M m`, `f : Fin (m+2) → Rat`, `p' : Fin (m+1)`.  Proves
///   Fin.sum (m+2) F = Rat.add (F (castSucc p')) (Fin.sum (m+1) (F∘skipNth (m+1)(castSucc p'))).
fn interior_minor(
    c: &RemoveConsts,
    parent: &EnvDeclBuilder,
    m: &Expr,
    ih: &Expr,
    f: &Expr,
    pprime: &Expr,
) -> Expr {
    let m1 = c.succ(m);
    let m2 = c.succ(&m1);
    let fin_m = c.fin_of(m);
    let fin_m1 = c.fin_of(&m1);

    let cs_p = c.cast_succ(&m1, pprime); // castSucc (m+1) p' : Fin (m+2)
    let last_m1 = c.last(&m1); // last (m+1) : Fin (m+2)
    let t = Expr::app(f.clone(), last_m1.clone()); // F (last (m+1))

    // G := fun j : Fin (m+1) => F (castSucc (m+1) j)   (= F ∘ castSucc)
    let g = {
        let mut rb = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = rb.fresh_local(fin_m1.clone());
        let body = Expr::app(f.clone(), c.cast_succ(&m1, &j));
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_m1.clone(), body))
    };
    // Q := Fin.sum m (fun j => G (skipNth m p' j))
    let q_fn = {
        let mut rb = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = rb.fresh_local(fin_m.clone());
        let body = Expr::app(g.clone(), c.skip(m, pprime, &j));
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body))
    };
    let q = c.sum(m, &q_fn);
    let p_term = Expr::app(g.clone(), pprime.clone()); // G p' (≡ F (castSucc p'))
    let sum_g = c.sum(&m1, &g);

    // s1 : Fin.sum (m+2) F = Rat.add (Fin.sum (m+1) G) (F (last (m+1)))   [Fin.sum_succ (m+1) F]
    let lhs_total = c.sum(&m2, f);
    let mid_a = c.add(sum_g.clone(), t.clone());
    let s1 = Expr::apps(c.fin_sum_succ.clone(), [m1.clone(), f.clone()]);

    // ih_app : Fin.sum (m+1) G = Rat.add (G p') (Q)    [ih p' G]
    let ih_app = Expr::apps(ih.clone(), [pprime.clone(), g.clone()]);
    // s2 : Rat.add (Fin.sum (m+1) G) t = Rat.add (Rat.add (G p') Q) t
    //   := congrArg (fun X => Rat.add X t) ih_app  — built as congr of (Rat.add · t)
    //   Use congrArg with f := fun X => Rat.add X t.
    let add_flip_t = {
        let mut rb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = rb.fresh_local(c.rat.clone());
        let body = c.add(x.clone(), t.clone());
        rb.finish_child(rb.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let pq = c.add(p_term.clone(), q.clone());
    let mid_b = c.add(pq.clone(), t.clone());
    let s2 = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            sum_g.clone(),
            pq.clone(),
            add_flip_t,
            ih_app,
        ],
    );
    // s3 : Rat.add (Rat.add (G p') Q) t = Rat.add (G p') (Rat.add Q t)   [add_assoc]
    let qt = c.add(q.clone(), t.clone());
    let mid_c = c.add(p_term.clone(), qt.clone());
    let s3 = Expr::apps(
        c.rat_add_assoc.clone(),
        [p_term.clone(), q.clone(), t.clone()],
    );

    // ── RHS side: Fin.sum (m+1) (F∘skipNth (m+1) (castSucc p')) = Rat.add Q t ──
    // skip-fn := fun jx : Fin (m+1) => F (skipNth (m+1) (castSucc p') jx)
    let skip_fn = {
        let mut rb = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = rb.fresh_local(fin_m1.clone());
        let body = Expr::app(f.clone(), c.skip(&m1, &cs_p, &jx));
        rb.finish_child(rb.mk_lam(jx_id, BinderInfo::Default, fin_m1.clone(), body))
    };
    let sum_skip = c.sum(&m1, &skip_fn);
    // r1 : Fin.sum (m+1) skip_fn = Rat.add (Fin.sum m (skip_fn∘castSucc m)) (skip_fn (last m))
    //   [Fin.sum_succ m skip_fn]
    let skip_prefix = {
        // fun j : Fin m => skip_fn (castSucc m j) ≡ F (skipNth (m+1)(castSucc p')(castSucc m j))
        let mut rb = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = rb.fresh_local(fin_m.clone());
        let inner = c.skip(&m1, &cs_p, &c.cast_succ(m, &j));
        let body = Expr::app(f.clone(), inner);
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body))
    };
    let skip_top = Expr::app(f.clone(), c.skip(&m1, &cs_p, &c.last(m))); // skip_fn (last m)
    let r1_mid = c.add(c.sum(m, &skip_prefix), skip_top.clone());
    let r1 = Expr::apps(c.fin_sum_succ.clone(), [m.clone(), skip_fn.clone()]);

    // leg_top : skip_top = t    via congrArg F (coh_A m p')
    //   coh_A m p' : skipNth (m+1)(castSucc p')(last m) = last (m+1)
    let coh_a = Expr::apps(c.coh_a.clone(), [m.clone(), pprime.clone()]);
    let skipped_top = c.skip(&m1, &cs_p, &c.last(m));
    let leg_top = Expr::apps(
        c.congr_arg.clone(),
        [
            c.fin_of(&m2),
            c.rat.clone(),
            skipped_top.clone(),
            last_m1.clone(),
            f.clone(),
            coh_a,
        ],
    );
    // leg_prefix : Fin.sum m skip_prefix = Q    via Fin.sum_congr
    //   pw j : skip_prefix j = q_fn j
    //     skip_prefix j ≡ F (skipNth (m+1)(castSucc p')(castSucc j))
    //     q_fn j        ≡ G (skipNth m p' j) ≡ F (castSucc (m+1) (skipNth m p' j))
    //     coh_B m p' j  : skipNth (m+1)(castSucc p')(castSucc j) = castSucc (m+1)(skipNth m p' j)
    //     pw j := congrArg F (coh_B m p' j)
    let pw = {
        let mut rb = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = rb.fresh_local(fin_m.clone());
        let lhs_pt = c.skip(&m1, &cs_p, &c.cast_succ(m, &j));
        let rhs_pt = c.cast_succ(&m1, &c.skip(m, pprime, &j));
        let coh_b = Expr::apps(c.coh_b.clone(), [m.clone(), pprime.clone(), j.clone()]);
        let body = Expr::apps(
            c.congr_arg.clone(),
            [
                c.fin_of(&m2),
                c.rat.clone(),
                lhs_pt,
                rhs_pt,
                f.clone(),
                coh_b,
            ],
        );
        rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_m.clone(), body))
    };
    let leg_prefix = Expr::apps(
        c.fin_sum_congr.clone(),
        [m.clone(), skip_prefix.clone(), q_fn.clone(), pw],
    );
    // r2 : Rat.add (Fin.sum m skip_prefix) (skip_top) = Rat.add Q t
    //   := congr (congrArg Rat.add leg_prefix) leg_top
    let congr_c = Expr::const_(
        Name::from_string("congr"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let sum_prefix = c.sum(m, &skip_prefix);
    let congr_add = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone()),
            sum_prefix.clone(),
            q.clone(),
            c.rat_add.clone(),
            leg_prefix,
        ],
    );
    let r2 = Expr::apps(
        congr_c,
        [
            c.rat.clone(),
            c.rat.clone(),
            Expr::app(c.rat_add.clone(), sum_prefix.clone()),
            Expr::app(c.rat_add.clone(), q.clone()),
            skip_top.clone(),
            t.clone(),
            congr_add,
            leg_top,
        ],
    );
    // sum_skip = r1_mid (r1), r1_mid = qt (r2)  ⇒  sum_skip = qt
    let r_chain = Expr::apps(
        c.eq_trans.clone(),
        [
            c.rat.clone(),
            sum_skip.clone(),
            r1_mid.clone(),
            qt.clone(),
            r1,
            r2,
        ],
    );
    // goal_rhs : Rat.add (F (castSucc p')) (Fin.sum (m+1) skip_fn) = Rat.add (G p') (Rat.add Q t)
    //   F (castSucc p') ≡ G p' (defeq), so use congrArg (Rat.add (G p')) r_chain.
    //   (G p' is defeq to F (castSucc p'); we present the LHS spelled as F (castSucc p') in the
    //    final conclusion, the kernel folds them.)
    let f_cs_p = Expr::app(f.clone(), cs_p.clone()); // F (castSucc p') (the goal's spelling)
    let goal_rhs_lhs = c.add(f_cs_p.clone(), sum_skip.clone()); // goal RHS as stated
    let _goal_rhs_rhs = c.add(p_term.clone(), qt.clone()); // = mid_c
                                                           // congrArg (Rat.add (F (castSucc p'))) r_chain : add (F cs p') sum_skip = add (F cs p') qt
    let add_fcsp = Expr::app(c.rat_add.clone(), f_cs_p.clone());
    let r_lift = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            sum_skip.clone(),
            qt.clone(),
            add_fcsp,
            r_chain,
        ],
    );
    // r_lift : add (F cs p') sum_skip = add (F cs p') qt
    // mid_c ≡ add (G p') qt ≡ add (F cs p') qt (defeq), so r_lift : goal_rhs_lhs = mid_c.

    // Now assemble: lhs_total = mid_a (s1) = mid_b (s2) = mid_c (s3) = goal_rhs_lhs (r_lift.symm)
    let chain_ab = Expr::apps(
        c.eq_trans.clone(),
        [
            c.rat.clone(),
            lhs_total.clone(),
            mid_a.clone(),
            mid_b.clone(),
            s1,
            s2,
        ],
    );
    let chain_abc = Expr::apps(
        c.eq_trans.clone(),
        [
            c.rat.clone(),
            lhs_total.clone(),
            mid_b.clone(),
            mid_c.clone(),
            chain_ab,
            s3,
        ],
    );
    // r_lift.symm : mid_c = goal_rhs_lhs   (mid_c ≡ add (F cs p') qt = r_lift's RHS spelled add (G p') qt — defeq)
    let r_lift_sym = Expr::apps(
        c.eq_symm.clone(),
        [c.rat.clone(), goal_rhs_lhs.clone(), mid_c.clone(), r_lift],
    );
    // final : lhs_total = goal_rhs_lhs
    Expr::apps(
        c.eq_trans.clone(),
        [
            c.rat.clone(),
            lhs_total,
            mid_c,
            goal_rhs_lhs,
            chain_abc,
            r_lift_sym,
        ],
    )
}

fn sum_remove_value(c: &RemoveConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());

    // motive M : Nat → Prop := fun m => ∀ p F, <goal at m>
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = d.fresh_local(c.nat.clone());
        let body = c.motive_body(&d, &m);
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // lcMotive at level lvl, for fixed F : Fin (lvl+1) → Rat :
    //   fun (q : Fin (lvl+1)) => Fin.sum (lvl+1) F
    //         = Rat.add (F q) (Fin.sum lvl (fun j => F (skipNth lvl q j)))
    let lc_motive = |c: &RemoveConsts, parent: &EnvDeclBuilder, lvl: &Expr, f: &Expr| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let l1 = c.succ(lvl);
        let fin_l1 = c.fin_of(&l1);
        let fin_l = c.fin_of(lvl);
        let (q_id, q) = d.fresh_local(fin_l1.clone());
        let skip_fn = {
            let mut rb = EnvDeclBuilder::child_of(&d);
            let (j_id, j) = rb.fresh_local(fin_l.clone());
            let body = Expr::app(f.clone(), c.skip(lvl, &q, &j));
            rb.finish_child(rb.mk_lam(j_id, BinderInfo::Default, fin_l.clone(), body))
        };
        let lhs = c.sum(&l1, f);
        let rhs = c.add(Expr::app(f.clone(), q.clone()), c.sum(lvl, &skip_fn));
        let concl = c.eq_rat(lhs, rhs);
        d.finish_child(d.mk_lam(q_id, BinderInfo::Default, fin_l1, concl))
    };

    // ── base : M 0 = ∀ (p : Fin 1)(F) => goal ──
    //   fun p F => @Fin.lastCases 0 (lcMotive 0 F) (last_minor 0 F) castMinor0 p
    //   castMinor0 : (i : Fin 0) → lcMotive 0 F (castSucc 0 i)  — vacuous via False.elim.
    let base = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let zero = c.nat_zero.clone();
        let one = c.succ(&zero);
        let fin1 = c.fin_of(&one);
        let f_ty = c.fin_to_rat(&one);
        let (p_id, p) = d.fresh_local(fin1.clone());
        let (f_id, f) = d.fresh_local(f_ty.clone());

        let lcm = lc_motive(c, &d, &zero, &f);
        let last_min = last_minor(c, &zero, &f);
        // castMinor0 : (i : Fin 0) → lcMotive 0 F (castSucc 0 i)
        let cast_min = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let fin0 = c.fin_of(&zero);
            let (i_id, i) = e.fresh_local(fin0.clone());
            // goal := lcMotive 0 F (castSucc 0 i)
            let cs_i = c.cast_succ(&zero, &i);
            let goal = Expr::app(lcm.clone(), cs_i);
            // False.elim goal (Nat.not_succ_le_zero (val 0 i) (Fin.isLt 0 i))
            let val0 = c.val(&zero, &i);
            let islt = Expr::apps(c.fin_islt.clone(), [zero.clone(), i.clone()]);
            let false_pf = Expr::apps(c.nat_not_succ_le_zero.clone(), [val0, islt]);
            let body = Expr::apps(c.false_elim.clone(), [goal, false_pf]);
            e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin0, body))
        };
        // @Fin.lastCases.{1} 0 lcm last_min cast_min p
        let lc = Expr::apps(
            c.fin_last_cases.clone(),
            [zero.clone(), lcm, last_min, cast_min, p.clone()],
        );
        let r = d.mk_lam(f_id, BinderInfo::Default, f_ty, lc);
        d.finish_child(d.mk_lam(p_id, BinderInfo::Default, fin1, r))
    };

    // ── step : (m : Nat) → M m → M (m+1) ──
    //   fun m ih p F => @Fin.lastCases (m+1) (lcMotive (m+1) F)
    //                     (last_minor (m+1) F) (castMinor) p
    //   castMinor : (p' : Fin (m+1)) → lcMotive (m+1) F (castSucc (m+1) p')
    //             := fun p' => interior_minor c m ih F p'
    let step = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = d.fresh_local(c.nat.clone());
        let mbody = c.motive_body(&d, &m); // M m
        let (ih_id, ih) = d.fresh_local(mbody.clone());
        let m1 = c.succ(&m);
        let m2 = c.succ(&m1);
        let fin_m2 = c.fin_of(&m2);
        let fin_m1 = c.fin_of(&m1);
        let f_ty = c.fin_to_rat(&m2);
        let (p_id, p) = d.fresh_local(fin_m2.clone());
        let (f_id, f) = d.fresh_local(f_ty.clone());

        let lcm = lc_motive(c, &d, &m1, &f);
        let last_min = last_minor(c, &m1, &f);
        let cast_min = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (pp_id, pp) = e.fresh_local(fin_m1.clone());
            let body = interior_minor(c, &e, &m, &ih, &f, &pp);
            e.finish_child(e.mk_lam(pp_id, BinderInfo::Default, fin_m1.clone(), body))
        };
        let lc = Expr::apps(
            c.fin_last_cases.clone(),
            [m1.clone(), lcm, last_min, cast_min, p.clone()],
        );
        let r = d.mk_lam(f_id, BinderInfo::Default, f_ty, lc);
        let r = d.mk_lam(p_id, BinderInfo::Default, fin_m2, r);
        let r = d.mk_lam(ih_id, BinderInfo::Default, mbody, r);
        d.finish_child(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), r))
    };

    // @Nat.rec.{0} M base step k : M k
    let rec_app = Expr::apps(c.nat_rec1.clone(), [motive, base, step, k.clone()]);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), rec_app))
}
