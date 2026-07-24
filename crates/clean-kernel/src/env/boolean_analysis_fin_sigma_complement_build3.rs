// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for the σ'' complement bundle, part 3: the on-`p` reduction
// (`eq_self_of_val_eq` + `fix_p`), the off-`p` preservation (`ne_p`), and the
// involutivity proof.  `include!`d (transitively) into the module owning
// `SigmaComplementConsts`.  Keeps each file under the 500-line convention.

// These two extra deliverables are NOT in the registered bundle's public list
// but are registered alongside it (helpers): `Fin.sigmaComplement_eq_self` and
// `Fin.sigmaComplement_ne_p`.  They are used by `fix_p` and `involutive`.

// ===========================================================================
// Fin.sigmaComplement_eq_self :
//   (k)(σ)(hinv)(p)(hcase)(j : Fin k)(heq : val j = val p) → @Eq (Fin k) (σ'' j) j
//
// In the isTrue branch (which `heq` selects) σ'' j ι-reduces to `j`.  Dispatch
// via Decidable.rec.{0}; isTrue → Eq.refl j; isFalse → vacuous (hne heq).
// ===========================================================================
fn eq_self_type(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let heq_ty = c.eq_nat(val_j, val_p);
    let (heq_id, _heq) = pre.b.fresh_local(heq_ty.clone());
    let spp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &j);
    let concl = c.eq_fin(&pre.k, spp, j.clone());
    let body = pre.b.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
    let body = pre
        .b
        .mk_pi(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, true)
}

fn eq_self_value(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let prop = c.eq_nat(val_j.clone(), val_p.clone());
    let (heq_id, heq) = pre.b.fresh_local(prop.clone());

    // motive : (dd : Decidable prop) → Prop := fun dd => complement_rec_at dd = j
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let dec_prop = Expr::app(c.decidable.clone(), prop.clone());
        let (dd_id, dd) = d.fresh_local(dec_prop.clone());
        let rec_dd = complement_rec_at(c, &pre, &d, &j, dd);
        let goal_dd = c.eq_fin(&pre.k, rec_dd, j.clone());
        d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_prop, goal_dd))
    };

    // isFalse minor: fun (hne : ¬prop) => False.elim (hne heq)
    //   (goal here is `Fin.mk k v hlt = j`, but the outer `heq : val j = val p`
    //    contradicts the discriminant — discharge vacuously.)
    let not_p = Expr::pi(BinderInfo::Default, prop.clone(), c.false_c.clone());
    let is_false_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (hne_id, hne) = d.fresh_local(not_p.clone());
        let spp_branch = complement_ne_branch_value(c, &pre, &d, &j, &hne);
        let goal_false = c.eq_fin(&pre.k, spp_branch, j.clone());
        let false_pf = Expr::app(hne.clone(), heq.clone());
        let false_elim0 = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
        let body = Expr::apps(false_elim0, [goal_false, false_pf]);
        d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_p.clone(), body))
    };

    // isTrue minor: fun (heq2 : prop) => Eq.refl (Fin k) j  (σ'' j ι-reduces to j)
    let is_true_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (heq2_id, _heq2) = d.fresh_local(prop.clone());
        let eq_refl_fin = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        let body = Expr::apps(eq_refl_fin, [pre.fin_k.clone(), j.clone()]);
        d.finish_child(d.mk_lam(heq2_id, BinderInfo::Default, prop.clone(), body))
    };

    let discr = Expr::apps(c.nat_deceq.clone(), [val_j.clone(), val_p.clone()]);
    let rec_app = Expr::apps(
        c.decidable_rec0.clone(),
        [prop.clone(), motive, is_false_min, is_true_min, discr],
    );
    let body = pre.b.mk_lam(heq_id, BinderInfo::Default, prop, rec_app);
    let body = pre
        .b
        .mk_lam(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, false)
}

// ===========================================================================
// Fin.sigmaComplement_fix_p : (k)(σ)(hinv)(p)(hcase) → @Eq (Fin k) (σ'' p) p
//   := Fin.sigmaComplement_eq_self k σ hinv p hcase p (Eq.refl Nat (val p)).
// ===========================================================================
fn fix_p_type(c: &SigmaComplementConsts) -> Expr {
    let pre = make_cprefix(c);
    let spp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &pre.p);
    let concl = c.eq_fin(&pre.k, spp, pre.p.clone());
    close_cprefix(&pre, concl, true)
}

fn fix_p_value(c: &SigmaComplementConsts) -> Expr {
    let pre = make_cprefix(c);
    let val_p = c.val(&pre.k, &pre.p);
    let refl_vp = Expr::apps(c.eq_refl_nat.clone(), [c.nat.clone(), val_p]);
    let body = Expr::apps(
        Expr::const_(Name::from_string("Fin.sigmaComplement_eq_self"), vec![]),
        [
            pre.k.clone(),
            pre.sigma.clone(),
            pre.hinv.clone(),
            pre.p.clone(),
            pre.hcase.clone(),
            pre.p.clone(),
            refl_vp,
        ],
    );
    close_cprefix(&pre, body, false)
}

// ===========================================================================
// Fin.sigmaComplement_ne_p :
//   (k)(σ)(hinv)(p)(hcase)(j : Fin k)(hne : val j = val p → False)
//     → @Eq Nat (val (σ'' j)) (val p) → False
//
// In the `≠` branch σ'' j ≡ Fin.mk k v hlt (v = val (σ (castSucc j))), so
// val (σ'' j) ≡ v.  If v = val p then val (σ (castSucc j)) = val (castSucc p), so
// (Fin.eq_of_val_eq) σ (castSucc j) = castSucc p = σ (last) [hcase.symm]; apply σ
// (hinv) ⇒ castSucc j = last, contradicting castSucc_ne_last.
// ===========================================================================
fn ne_p_type(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let not_p = Expr::pi(
        BinderInfo::Default,
        c.eq_nat(val_j, val_p.clone()),
        c.false_c.clone(),
    );
    let (hne_id, _hne) = pre.b.fresh_local(not_p.clone());
    let spp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &j);
    let val_spp = c.val(&pre.k, &spp);
    let e_ty = c.eq_nat(val_spp, val_p);
    let (e_id, _e) = pre.b.fresh_local(e_ty.clone());
    let body = pre
        .b
        .mk_pi(e_id, BinderInfo::Default, e_ty, c.false_c.clone());
    let body = pre.b.mk_pi(hne_id, BinderInfo::Default, not_p, body);
    let body = pre
        .b
        .mk_pi(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, true)
}

fn ne_p_value(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let succ_k = c.succ(&pre.k);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let prop = c.eq_nat(val_j.clone(), val_p.clone());
    let not_p = Expr::pi(BinderInfo::Default, prop.clone(), c.false_c.clone());
    let (hne_id, hne) = pre.b.fresh_local(not_p.clone());

    let cs_j = c.cast_succ(&pre.k, &j);
    let sig_cs = Expr::app(pre.sigma.clone(), cs_j.clone()); // σ (castSucc j)
    let cs_p = c.cast_succ(&pre.k, &pre.p); // castSucc p
    let last_k = c.last(&pre.k);
    let sig_last = Expr::app(pre.sigma.clone(), last_k.clone());

    // motive : (dd : Decidable prop) → Prop
    //   := fun dd => (val (complement_rec_at dd) = val p) → False
    //   At dd := discr this is the conclusion `(val (σ'' j) = val p) → False`.
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let dec_prop = Expr::app(c.decidable.clone(), prop.clone());
        let (dd_id, dd) = d.fresh_local(dec_prop.clone());
        let rec_dd = complement_rec_at(c, &pre, &d, &j, dd);
        let val_rec = c.val(&pre.k, &rec_dd);
        let arr = Expr::pi(
            BinderInfo::Default,
            c.eq_nat(val_rec, val_p.clone()),
            c.false_c.clone(),
        );
        d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_prop, arr))
    };

    // isFalse minor: fun (hne2 : ¬prop) (e : val (Fin.mk k v hlt) = val p) => proof.
    //   val (Fin.mk k v hlt) ≡ v ≡ val (σ (castSucc j)); `val (castSucc p) ≡ val p`,
    //   so e : val (σ (castSucc j)) = val (castSucc p) by defeq.
    let is_false_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (hne2_id, hne2) = d.fresh_local(not_p.clone());
        let spp_branch = complement_ne_branch_value(c, &pre, &d, &j, &hne2); // Fin.mk k v hlt
        let val_branch = c.val(&pre.k, &spp_branch);
        let e_ty = c.eq_nat(val_branch, val_p.clone());
        let (e_id, e) = d.fresh_local(e_ty.clone());
        // Fin.eq_of_val_eq (k+1) (σ (castSucc j)) (castSucc p) e
        //   (e : v = val p ≡ val (σ (castSucc j)) = val (castSucc p) by defeq)
        let e_fin = Expr::apps(
            c.fin_eq_of_val.clone(),
            [succ_k.clone(), sig_cs.clone(), cs_p.clone(), e.clone()],
        );
        // hcase.symm : castSucc p = σ (last k)
        let hcase_sym = Expr::apps(
            c.eq_symm.clone(),
            [
                pre.fin_succ.clone(),
                sig_last.clone(),
                cs_p.clone(),
                pre.hcase.clone(),
            ],
        );
        // e1 : σ (castSucc j) = σ (last k)   [e_fin.trans hcase.symm]
        let e1 = Expr::apps(
            c.eq_trans.clone(),
            [
                pre.fin_succ.clone(),
                sig_cs.clone(),
                cs_p.clone(),
                sig_last.clone(),
                e_fin,
                hcase_sym,
            ],
        );
        // congrArg σ e1 : σ (σ (castSucc j)) = σ (σ (last k))
        let ss_cs = Expr::app(pre.sigma.clone(), sig_cs.clone());
        let ss_last = Expr::app(pre.sigma.clone(), sig_last.clone());
        let cong = Expr::apps(
            c.congr_arg.clone(),
            [
                pre.fin_succ.clone(),
                pre.fin_succ.clone(),
                sig_cs.clone(),
                sig_last.clone(),
                pre.sigma.clone(),
                e1,
            ],
        );
        // hinv (castSucc j) : σ (σ (castSucc j)) = castSucc j  → symm
        let hinv_cs = Expr::app(pre.hinv.clone(), cs_j.clone());
        let hinv_cs_sym = Expr::apps(
            c.eq_symm.clone(),
            [pre.fin_succ.clone(), ss_cs.clone(), cs_j.clone(), hinv_cs],
        );
        // hinv (last k) : σ (σ (last k)) = last k
        let hinv_last = Expr::app(pre.hinv.clone(), last_k.clone());
        // chain: castSucc j = σ(σ(castSucc j)) = σ(σ(last)) = last
        let ab = Expr::apps(
            c.eq_trans.clone(),
            [
                pre.fin_succ.clone(),
                cs_j.clone(),
                ss_cs.clone(),
                ss_last.clone(),
                hinv_cs_sym,
                cong,
            ],
        );
        let cs_eq_last = Expr::apps(
            c.eq_trans.clone(),
            [
                pre.fin_succ.clone(),
                cs_j.clone(),
                ss_last.clone(),
                last_k.clone(),
                ab,
                hinv_last,
            ],
        );
        // Fin.castSucc_ne_last k j cs_eq_last : False
        let body = Expr::apps(
            c.cast_succ_ne_last.clone(),
            [pre.k.clone(), j.clone(), cs_eq_last],
        );
        // close `e` then `hne2`: minor : ¬prop → (val (Fin.mk k v hlt) = val p) → False
        let body = d.mk_lam(e_id, BinderInfo::Default, e_ty, body);
        d.finish_child(d.mk_lam(hne2_id, BinderInfo::Default, not_p.clone(), body))
    };

    // isTrue minor: fun (heq : prop) (e : val j = val p) => False.elim (hne heq).
    //   In the isTrue branch σ'' j ι-reduces to j, so the `e` here is `val j = val
    //   p`; but the outer `hne` already refutes `prop` — discharge vacuously.
    let is_true_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (heq_id, heq) = d.fresh_local(prop.clone());
        // e : val j = val p  (val (complement_rec_at (isTrue heq)) ≡ val j)
        let e_true_ty = c.eq_nat(val_j.clone(), val_p.clone());
        let (e_id2, _e2) = d.fresh_local(e_true_ty.clone());
        let false_pf = Expr::app(hne.clone(), heq.clone());
        let body = d.mk_lam(e_id2, BinderInfo::Default, e_true_ty, false_pf);
        d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, prop.clone(), body))
    };

    let discr = Expr::apps(c.nat_deceq.clone(), [val_j.clone(), val_p.clone()]);
    let rec_app = Expr::apps(
        c.decidable_rec0.clone(),
        [prop.clone(), motive, is_false_min, is_true_min, discr],
    );
    // rec_app : (val (σ'' j) = val p) → False  — exactly ne_p's conclusion.
    let body = pre.b.mk_lam(hne_id, BinderInfo::Default, not_p, rec_app);
    let body = pre
        .b
        .mk_lam(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, false)
}

include!("boolean_analysis_fin_sigma_complement_build4.rs");
