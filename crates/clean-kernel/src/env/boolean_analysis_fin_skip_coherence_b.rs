// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Coherence (B) `Fin.skipNth_castSucc_castSucc` proof body — the prefix
// reindex coherence for the interior case of `Fin.sum_remove`.
//
// `include!`d into `boolean_analysis_fin_skip_coherence.rs` to keep each file
// under the 500-line convention; it shares that module's `CohConsts` + imports.

// ===========================================================================
// (B) Fin.skipNth_castSucc_castSucc
//   (m)(p' : Fin (m+1))(j : Fin m) →
//     skipNth (m+1) (castSucc (m+1) p') (castSucc m j)
//       = castSucc (m+1) (skipNth m p' j)
// ===========================================================================
fn coh_b_type(c: &CohConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let m1 = c.succ(&m);
    let m2 = c.succ(&m1);
    let fin_m1 = c.fin_of(&m1);
    let fin_m = c.fin_of(&m);
    let (p_id, p) = b.fresh_local(fin_m1.clone());
    let (j_id, j) = b.fresh_local(fin_m.clone());
    let cs_p = c.cast_succ(&m1, &p);
    let cs_j = c.cast_succ(&m, &j);
    let lhs = c.skip(&m1, &cs_p, &cs_j); // Fin (m+2)
    let skip_pj = c.skip(&m, &p, &j); // Fin (m+1)
    let rhs = c.cast_succ(&m1, &skip_pj); // Fin (m+2)
    let concl = c.eq_fin(&m2, lhs, rhs);
    let e = b.mk_pi(j_id, BinderInfo::Default, fin_m, concl);
    let e = b.mk_pi(p_id, BinderInfo::Default, fin_m1, e);
    b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
}

fn coh_b_value(c: &CohConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let m1 = c.succ(&m);
    let m2 = c.succ(&m1);
    let fin_m1 = c.fin_of(&m1);
    let fin_m = c.fin_of(&m);
    let fin_m2_ty = c.fin_of(&m2);
    let (p_id, p) = b.fresh_local(fin_m1.clone());
    let (j_id, j) = b.fresh_local(fin_m.clone());

    let cs_p = c.cast_succ(&m1, &p);
    let cs_j = c.cast_succ(&m, &j);
    let val_j = c.val(&m, &j);
    let val_p = c.val(&m1, &p);
    let prop = c.lt(&val_j, &val_p); // Nat.lt (val j) (val p')

    let lhs = c.skip(&m1, &cs_p, &cs_j); // skipNth (m+1) (castSucc p') (castSucc j)
    let skip_pj = c.skip(&m, &p, &j); // skipNth m p' j
    let rhs = c.cast_succ(&m1, &skip_pj); // castSucc (m+1) (skipNth m p' j)
    let goal = c.eq_fin(&m2, lhs.clone(), rhs.clone());

    // motive : Decidable prop → Prop := fun _ => goal
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let dec_prop = Expr::app(c.decidable.clone(), prop.clone());
        let (d_id, _d) = d.fresh_local(dec_prop.clone());
        d.finish_child(d.mk_lam(d_id, BinderInfo::Default, dec_prop, goal.clone()))
    };

    // helper: castSucc(m+1) of an arg : Fin (m+1) → Fin (m+2), as a function term
    //   used as `congrArg`'s `f`.
    let cast_m1_fn = Expr::app(c.fin_cast_succ.clone(), m1.clone());

    // ── TRUE minor: fun (ht : prop) => goal-proof ──
    //   e_lhs : lhs = castSucc (m+1) (castSucc m j)   [skipNth_lt (m+1) (castSucc p') (castSucc j) ht]
    //   e_rhs : rhs = castSucc (m+1) (castSucc m j)   [congrArg (castSucc (m+1)) (skipNth_lt m p' j ht)]
    //   proof := e_lhs.trans e_rhs.symm
    let is_true_min = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (ht_id, ht) = d.fresh_local(prop.clone());
        let cs_cs_j = c.cast_succ(&m1, &cs_j); // castSucc (m+1) (castSucc m j)
                                               // e_lhs : lhs = castSucc (m+1) (castSucc m j)
        let e_lhs = Expr::apps(
            c.skip_nth_lt.clone(),
            [m1.clone(), cs_p.clone(), cs_j.clone(), ht.clone()],
        );
        // inner : skipNth m p' j = castSucc m j
        let inner = Expr::apps(
            c.skip_nth_lt.clone(),
            [m.clone(), p.clone(), j.clone(), ht.clone()],
        );
        // e_rhs : castSucc (m+1) (skipNth m p' j) = castSucc (m+1) (castSucc m j)
        let e_rhs = Expr::apps(
            c.congr_arg.clone(),
            [
                fin_m1.clone(),
                fin_m2_ty.clone(),
                skip_pj.clone(),
                cs_j.clone(),
                cast_m1_fn.clone(),
                inner,
            ],
        );
        // e_rhs_sym : castSucc (m+1) (castSucc m j) = rhs
        let e_rhs_sym = Expr::apps(
            c.eq_symm.clone(),
            [fin_m2_ty.clone(), rhs.clone(), cs_cs_j.clone(), e_rhs],
        );
        // proof : lhs = rhs := e_lhs.trans e_rhs_sym
        let proof = Expr::apps(
            c.eq_trans.clone(),
            [
                fin_m2_ty.clone(),
                lhs.clone(),
                cs_cs_j.clone(),
                rhs.clone(),
                e_lhs,
                e_rhs_sym,
            ],
        );
        d.finish_child(d.mk_lam(ht_id, BinderInfo::Default, prop.clone(), proof))
    };

    // ── FALSE minor: fun (hf : prop → False) => goal-proof ──
    //   e_lhs : lhs = skip_shift (m+1) (castSucc j)      [skipNth_ge (m+1) (castSucc p') (castSucc j) hf]
    //   inner : skipNth m p' j = skip_shift m j          [skipNth_ge m p' j hf]
    //   e_rhs : rhs = castSucc (m+1) (skip_shift m j)     [congrArg (castSucc (m+1)) inner]
    //   e_mid : skip_shift (m+1) (castSucc j) = castSucc (m+1) (skip_shift m j)
    //              [Fin.eq_of_val_eq (m+2) _ _ (Eq.refl Nat (succ (val j)))]
    //   proof := e_lhs.trans (e_mid.trans e_rhs.symm)
    let is_false_min = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let not_p = Expr::pi(BinderInfo::Default, prop.clone(), false_c);
        let (hf_id, hf) = d.fresh_local(not_p.clone());

        let shift_cs_j = c.skip_shift(&m1, &cs_j); // skip_shift (m+1) (castSucc j) : Fin (m+2), val ≡ succ (val j)
        let shift_m_j = c.skip_shift(&m, &j); // skip_shift m j : Fin (m+1), val ≡ succ (val j)
        let cs_shift = c.cast_succ(&m1, &shift_m_j); // castSucc (m+1) (skip_shift m j) : Fin (m+2)

        // e_lhs : lhs = skip_shift (m+1) (castSucc j)
        let e_lhs = Expr::apps(
            c.skip_nth_ge.clone(),
            [m1.clone(), cs_p.clone(), cs_j.clone(), hf.clone()],
        );
        // inner : skipNth m p' j = skip_shift m j
        let inner = Expr::apps(
            c.skip_nth_ge.clone(),
            [m.clone(), p.clone(), j.clone(), hf.clone()],
        );
        // e_rhs : castSucc (m+1) (skipNth m p' j) = castSucc (m+1) (skip_shift m j)
        let e_rhs = Expr::apps(
            c.congr_arg.clone(),
            [
                fin_m1.clone(),
                fin_m2_ty.clone(),
                skip_pj.clone(),
                shift_m_j.clone(),
                cast_m1_fn.clone(),
                inner,
            ],
        );
        // e_rhs_sym : castSucc (m+1) (skip_shift m j) = rhs
        let e_rhs_sym = Expr::apps(
            c.eq_symm.clone(),
            [fin_m2_ty.clone(), rhs.clone(), cs_shift.clone(), e_rhs],
        );
        // e_mid : skip_shift (m+1) (castSucc j) = castSucc (m+1) (skip_shift m j)
        //   both val ≡ succ (val j); Fin.eq_of_val_eq with Eq.refl Nat (succ (val j))
        let hval = Expr::apps(c.eq_refl_nat.clone(), [c.nat_c.clone(), c.succ(&val_j)]);
        let e_mid = Expr::apps(
            c.fin_eq_of_val.clone(),
            [m2.clone(), shift_cs_j.clone(), cs_shift.clone(), hval],
        );
        // e_mid_then : skip_shift (m+1) (castSucc j) = rhs   := e_mid.trans e_rhs_sym
        let e_mid_then = Expr::apps(
            c.eq_trans.clone(),
            [
                fin_m2_ty.clone(),
                shift_cs_j.clone(),
                cs_shift.clone(),
                rhs.clone(),
                e_mid,
                e_rhs_sym,
            ],
        );
        // proof : lhs = rhs := e_lhs.trans e_mid_then
        let proof = Expr::apps(
            c.eq_trans.clone(),
            [
                fin_m2_ty.clone(),
                lhs.clone(),
                shift_cs_j.clone(),
                rhs.clone(),
                e_lhs,
                e_mid_then,
            ],
        );
        d.finish_child(d.mk_lam(hf_id, BinderInfo::Default, not_p, proof))
    };

    // discriminant := Nat.decLt (val j) (val p') : Decidable prop
    let discr = Expr::apps(c.nat_dec_lt.clone(), [val_j.clone(), val_p.clone()]);
    // @Decidable.rec.{0} prop motive isFalse isTrue discr : goal
    let rec_app = Expr::apps(
        c.decidable_rec0.clone(),
        [prop.clone(), motive, is_false_min, is_true_min, discr],
    );

    let e = b.mk_lam(j_id, BinderInfo::Default, fin_m, rec_app);
    let e = b.mk_lam(p_id, BinderInfo::Default, fin_m1, e);
    b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
}
