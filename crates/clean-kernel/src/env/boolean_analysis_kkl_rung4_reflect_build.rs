// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL finish — RUNG 4 reflection type/proof builders. `include!`d into
// `boolean_analysis_kkl_rung4_reflect.rs` so it shares `ReflectConsts` and
// keeps the registration module under the 500-line convention. (Regular `//`
// comments only — inner doc `//!` is not allowed at an `include!` site.)

fn forall_pos_lt_add_type(c: &ReflectConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let hyp = forall_pos_lt_add_hyp(c, &b, &a, &bv);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.le(a.clone(), bv.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e))
}

/// `∀ (e : Rat), Rat.lt 0 e → Rat.lt a (Rat.add b e)`.
fn forall_pos_lt_add_hyp(c: &ReflectConsts, parent: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (e_id, e) = b.fresh_local(c.rat.clone());
    let hpos = c.lt(c.rat_zero.clone(), e.clone());
    let (hp_id, _) = b.fresh_local(hpos.clone());
    let concl = c.lt(a.clone(), c.add(bv.clone(), e.clone()));
    let inner = b.mk_pi(hp_id, BinderInfo::Default, hpos, concl);
    b.finish_child(b.mk_pi(e_id, BinderInfo::Default, c.rat.clone(), inner))
}

fn forall_pos_lt_add_value(c: &ReflectConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let hyp = forall_pos_lt_add_hyp(c, &b, &a, &bv);
    let (h_id, h) = b.fresh_local(hyp.clone());

    let a_le_b = c.le(a.clone(), bv.clone());

    // em (a ≤ b) : Or (a≤b)(¬(a≤b)).
    let em = Expr::const_(Name::from_string("Classical.em"), vec![]);
    let h_em = Expr::app(em, a_le_b.clone());
    let not_a_le_b = c.not_(a_le_b.clone());

    // YES: λ (h0 : a ≤ b) => h0.
    let yes = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (h0_id, h0) = ch.fresh_local(a_le_b.clone());
        ch.finish_child(ch.mk_lam(h0_id, BinderInfo::Default, a_le_b.clone(), h0))
    };

    // NO: λ (hnab : ¬(a ≤ b)) => <contradiction yields a ≤ b>.
    let no = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hnab_id, hnab) = ch.fresh_local(not_a_le_b.clone());

        // le_total a b : Or (a≤b)(b≤a). Left disjunct refuted by hnab → b ≤ a.
        let le_total = Expr::const_(Name::from_string("Rat.le_total"), vec![]);
        let h_total = Expr::apps(le_total, [a.clone(), bv.clone()]);
        let b_le_a = c.le(bv.clone(), a.clone());
        // tot_left : a≤b → b≤a   (False.elim after hnab refutes a≤b).
        let tot_left = {
            let mut e = EnvDeclBuilder::child_of(&ch);
            let (hab_id, hab) = e.fresh_local(a_le_b.clone());
            let h_false = Expr::app(hnab.clone(), hab); // : False
            let body = c.false_elim(b_le_a.clone(), h_false);
            e.finish_child(e.mk_lam(hab_id, BinderInfo::Default, a_le_b.clone(), body))
        };
        // tot_right : b≤a → b≤a   (identity).
        let tot_right = {
            let mut e = EnvDeclBuilder::child_of(&ch);
            let (hba_id, hba) = e.fresh_local(b_le_a.clone());
            e.finish_child(e.mk_lam(hba_id, BinderInfo::Default, b_le_a.clone(), hba))
        };
        let hba: Expr = c.or_elim(
            &ch,
            a_le_b.clone(),
            b_le_a.clone(),
            b_le_a.clone(),
            h_total,
            tot_left,
            tot_right,
        );

        // hba_lt : b < a   via lt_iff.mpr ⟨b≤a, ¬(a≤b)⟩.
        let not_pi_a_le_b = c.not_pi(&ch, a_le_b.clone());
        let and_ba = c.and_intro(b_le_a.clone(), not_pi_a_le_b.clone(), hba, hnab.clone());
        let hba_lt = c.iff_mpr(
            c.lt(bv.clone(), a.clone()),
            c.and_(b_le_a.clone(), not_pi_a_le_b.clone()),
            c.lt_iff(bv.clone(), a.clone()),
            and_ba,
        );

        // h_pos : 0 < a − b   (sub_pos_of_lt b a hba_lt).
        let amb = c.sub(a.clone(), bv.clone());
        let sub_pos = Expr::const_(Name::from_string("Rat.sub_pos_of_lt"), vec![]);
        let h_pos = Expr::apps(sub_pos, [bv.clone(), a.clone(), hba_lt]);

        // h_inst : a < b + (a − b)   (apply the hypothesis at e := a−b).
        let h_inst = Expr::apps(h.clone(), [amb.clone(), h_pos]);

        // eq1 : b + (a − b) = (a − b) + b   (add_comm b (a−b)).
        let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
        let b_plus_amb = c.add(bv.clone(), amb.clone());
        let amb_plus_b = c.add(amb.clone(), bv.clone());
        let eq1 = Expr::apps(add_comm, [bv.clone(), amb.clone()]);
        // eq2 : (a − b) + b = a   (sub_add_cancel b a : (a−b)+b = a).
        let sub_add_cancel = Expr::const_(Name::from_string("Rat.sub_add_cancel"), vec![]);
        let eq2 = Expr::apps(sub_add_cancel, [bv.clone(), a.clone()]);
        // eq : b + (a − b) = a.
        let eq = c.eq_trans_rat(b_plus_amb.clone(), amb_plus_b.clone(), a.clone(), eq1, eq2);

        // a < a   via Eq.subst (motive t => a < t) eq h_inst.
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&ch);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.lt(a.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let a_lt_a = c.eq_subst_rat(motive, b_plus_amb, a.clone(), eq, h_inst);

        // lt_iff.mp (a<a) : (a≤a) ∧ ¬(a≤a) → False.
        let le_aa = c.le(a.clone(), a.clone());
        let not_pi_le_aa = c.not_pi(&ch, le_aa.clone());
        let rhs_aa = c.and_(le_aa.clone(), not_pi_le_aa.clone());
        let mp = c.iff_mp(
            c.lt(a.clone(), a.clone()),
            rhs_aa,
            c.lt_iff(a.clone(), a.clone()),
            a_lt_a,
        );
        let h_le_aa = c.and_left(le_aa.clone(), not_pi_le_aa.clone(), mp.clone());
        let h_not_le_aa = c.and_right(le_aa.clone(), not_pi_le_aa.clone(), mp);
        let h_false = Expr::app(h_not_le_aa, h_le_aa); // : False

        let body = c.false_elim(a_le_b.clone(), h_false);
        ch.finish_child(ch.mk_lam(hnab_id, BinderInfo::Default, not_a_le_b.clone(), body))
    };

    let body = c.or_elim(&b, a_le_b.clone(), not_a_le_b, a_le_b, h_em, yes, no);

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e))
}

// ─────────────── NNReal.ofRat_le_ofRat_rev ──────────────────────────────────

fn reflect_type(c: &ReflectConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let ha_ty = c.nonneg(a.clone());
    let (ha_id, ha) = b.fresh_local(ha_ty.clone());
    let hb_ty = c.nonneg(bv.clone());
    let (hb_id, hb) = b.fresh_local(hb_ty.clone());
    let oa = c.of_rat(a.clone(), ha.clone());
    let ob = c.of_rat(bv.clone(), hb.clone());
    let hyp = c.nn_le(oa, ob);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.le(a.clone(), bv.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, e);
    let e = b.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e))
}

fn reflect_value(c: &ReflectConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let ha_ty = c.nonneg(a.clone());
    let (ha_id, ha) = b.fresh_local(ha_ty.clone());
    let hb_ty = c.nonneg(bv.clone());
    let (hb_id, hb) = b.fresh_local(hb_ty.clone());
    let oa = c.of_rat(a.clone(), ha.clone());
    let ob = c.of_rat(bv.clone(), hb.clone());
    let hyp = c.nn_le(oa, ob);
    let (h_id, h) = b.fresh_local(hyp.clone());

    // Build the `∀ e>0, a < b+e` term, then feed to le_of_forall_pos_lt_add.
    //   H : NNReal.le (ofRat a)(ofRat b)  is def-eq to
    //       ∀ e, 0<e → ∃ N, ∀ n, N≤n → vseq(const a) n < vseq(const b) n + e.
    //   For each e he: Exists.elim (H e he) over `a < b+e`.
    let forall_pos = {
        let mut eb = EnvDeclBuilder::child_of(&b);
        let (e_id, e) = eb.fresh_local(c.rat.clone());
        let hpos = c.lt(c.rat_zero.clone(), e.clone());
        let (hp_id, hp) = eb.fresh_local(hpos.clone());

        // H e hp : ∃ N, ∀ n, N≤n → a < b+e  (def-eq through the const/lift ι-rules).
        let h_exists = Expr::apps(h.clone(), [e.clone(), hp.clone()]);

        // The goal of the Exists.elim and the predicate it eliminates are spelled
        // over the def-eq `a < b + e` form. The existential's binder is `N : Nat`
        // and its body `∀ n, N≤n → a < b+e`; we re-express that body abstractly.
        let goal = c.lt(a.clone(), c.add(bv.clone(), e.clone()));

        // pred : Nat → Prop  := fun N => ∀ n, Nat.le N n → a < b+e.
        // (This is the existential's predicate after the const-seq ι-reduction;
        //  vseq(const ·) n ≡ a/b so the body is `a < b+e` independent of n/N.)
        let pred = {
            let mut pb = EnvDeclBuilder::child_of(&eb);
            let (n_id, _n) = pb.fresh_local(c.nat.clone());
            // ∀ m, Nat.le N m → a < b+e.
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&pb);
                let (m_id, m) = ib.fresh_local(c.nat.clone());
                let nat_le = Expr::apps(
                    Expr::const_(Name::from_string("Nat.le"), vec![]),
                    [_n.clone(), m.clone()],
                );
                let (hle_id, _hle) = ib.fresh_local(nat_le.clone());
                let body = goal.clone();
                let e2 = ib.mk_pi(hle_id, BinderInfo::Default, nat_le, body);
                ib.finish_child(ib.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e2))
            };
            pb.finish_child(pb.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner))
        };

        // motive (Exists.elim target) is `goal` (non-dependent).
        // λ (N : Nat) (hN : ∀ m, N≤m → a<b+e) => hN N (Nat.le_refl N).
        let elim_fn = {
            let mut fb = EnvDeclBuilder::child_of(&eb);
            let (cap_id, cap) = fb.fresh_local(c.nat.clone());
            let cap_pred = {
                // ∀ m, Nat.le cap m → a < b+e.
                let mut ib = EnvDeclBuilder::child_of(&fb);
                let (m_id, m) = ib.fresh_local(c.nat.clone());
                let nat_le = Expr::apps(
                    Expr::const_(Name::from_string("Nat.le"), vec![]),
                    [cap.clone(), m.clone()],
                );
                let (hle_id, _hle) = ib.fresh_local(nat_le.clone());
                let e2 = ib.mk_pi(hle_id, BinderInfo::Default, nat_le, goal.clone());
                ib.finish_child(ib.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e2))
            };
            let (hn_id, hn) = fb.fresh_local(cap_pred.clone());
            let le_refl = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_refl"), vec![]),
                [cap.clone()],
            );
            // hN cap (Nat.le_refl cap) : a < b+e.
            let applied = Expr::apps(hn, [cap.clone(), le_refl]);
            let e2 = fb.mk_lam(hn_id, BinderInfo::Default, cap_pred, applied);
            fb.finish_child(fb.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e2))
        };

        // Exists.elim.{1} Nat pred goal h_exists elim_fn : goal.
        let exists_elim = Expr::const_(Name::from_string("Exists.elim"), vec![c.u1.clone()]);
        let elimmed = Expr::apps(
            exists_elim,
            [c.nat.clone(), pred, goal.clone(), h_exists, elim_fn],
        );

        let e2 = eb.mk_lam(hp_id, BinderInfo::Default, hpos, elimmed);
        eb.finish_child(eb.mk_lam(e_id, BinderInfo::Default, c.rat.clone(), e2))
    };

    // Rat.le_of_forall_pos_lt_add a b forall_pos : a ≤ b.
    let arch = Expr::const_(Name::from_string("Rat.le_of_forall_pos_lt_add"), vec![]);
    let proof = Expr::apps(arch, [a.clone(), bv.clone(), forall_pos]);

    let _ = (&c.prop, &c.nnreal); // doc parity (carrier handles referenced)
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, proof);
    let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, e);
    let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e))
}
