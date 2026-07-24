// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for the σ'' complement bundle, part 2: the `Fin.sigmaComplement`
// map itself + coherence (off-p) + fixed-point + involutivity. `include!`d into
// `boolean_analysis_fin_sigma_complement_build.rs` (transitively into the module
// owning `SigmaComplementConsts`). Keeps each file under the 500-line convention.

// ===========================================================================
// Fin.sigmaComplement : (k)(σ)(hinv)(p)(hcase)(j : Fin k) → Fin k
//
//   fun … j => @Decidable.rec.{1} (Eq Nat (val j) (val p))
//                (fun _ => Fin k)
//                (isFalse minor : (¬ val j = val p) → Fin k)   -- the Fin.mk branch
//                (isTrue  minor : (val j = val p)  → Fin k)    -- returns j
//                (Nat.decEq (val j) (val p))
// ===========================================================================
fn complement_type(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let (j_id, _j) = pre.b.fresh_local(pre.fin_k.clone());
    let body = pre.b.mk_pi(
        j_id,
        BinderInfo::Default,
        pre.fin_k.clone(),
        pre.fin_k.clone(),
    );
    close_cprefix(&pre, body, true)
}

/// The `Fin.mk k v hlt` value of the `≠`-branch, given `j` and the `hne`
/// (`val j = val p → False`) hypothesis. `v := val (σ (castSucc j))`.
/// `parent` is the builder that ALREADY allocated `hne` (and any other locals in
/// scope); the internal `hvk` local is spawned as a child of it so FVar IDs do
/// not collide with `hne`.
fn complement_ne_branch_value(
    c: &SigmaComplementConsts,
    pre: &CPrefix,
    parent: &EnvDeclBuilder,
    j: &Expr,
    hne: &Expr,
) -> Expr {
    let succ_k = c.succ(&pre.k);
    let cs_j = c.cast_succ(&pre.k, j);
    let sig_cs = Expr::app(pre.sigma.clone(), cs_j); // σ (castSucc j)
    let v = c.val(&succ_k, &sig_cs); // val (σ (castSucc j))
    let last_k = c.last(&pre.k);

    // hislt : Fin.isLt (k+1) (σ (castSucc j)) : Nat.lt v (k+1) ≡ Nat.le (succ v) (succ k)
    let hislt = Expr::apps(c.fin_islt.clone(), [succ_k.clone(), sig_cs.clone()]);
    // hle : Nat.le v k
    let hle = Expr::apps(c.nat_le_of_ss.clone(), [v.clone(), pre.k.clone(), hislt]);

    // hne_v : v = k → False
    let hne_v = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let eq_vk = c.eq_nat(v.clone(), pre.k.clone());
        let (hvk_id, hvk) = d.fresh_local(eq_vk.clone());
        // Fin.eq_of_val_eq (k+1) (σ(castSucc j)) (last k) hvk : σ(castSucc j) = last k
        //   (val (last k) ≡ k, so hvk : v = k fills the val-equality slot by defeq.)
        let e_fin = Expr::apps(
            c.fin_eq_of_val.clone(),
            [succ_k.clone(), sig_cs.clone(), last_k.clone(), hvk.clone()],
        );
        // Fin.sigmaComplement_ne_last k σ hinv p hcase j hne e_fin : False
        let ne_last = Expr::apps(
            Expr::const_(Name::from_string("Fin.sigmaComplement_ne_last"), vec![]),
            [
                pre.k.clone(),
                pre.sigma.clone(),
                pre.hinv.clone(),
                pre.p.clone(),
                pre.hcase.clone(),
                j.clone(),
                hne.clone(),
                e_fin,
            ],
        );
        d.finish_child(d.mk_lam(hvk_id, BinderInfo::Default, eq_vk, ne_last))
    };

    // hlt : Nat.lt_of_le_of_ne v k hle hne_v : Nat.lt v k
    let hlt = Expr::apps(
        c.nat_lt_of_le_ne.clone(),
        [v.clone(), pre.k.clone(), hle, hne_v],
    );
    // Fin.mk k v hlt : Fin k
    Expr::apps(c.fin_mk.clone(), [pre.k.clone(), v, hlt])
}

/// The `Fin.sigmaComplement` `Decidable.rec.{1}` value of `σ'' j` instantiated
/// at an ARBITRARY discriminant expression `dd : Decidable (val j = val p)`.
/// This is exactly the body of `Fin.sigmaComplement` with `dd` in place of the
/// canonical `Nat.decEq (val j) (val p)`.  Used both for the definition (with
/// `dd := Nat.decEq …`) and inside dependent motives (abstracting `dd`), so that
/// substituting a `Decidable.isFalse hne` / `isTrue heq` ι-reduces `σ'' j` to the
/// matching branch value.  `parent` must already own `j`'s scope.
fn complement_rec_at(
    c: &SigmaComplementConsts,
    pre: &CPrefix,
    parent: &EnvDeclBuilder,
    j: &Expr,
    dd: Expr,
) -> Expr {
    let val_j = c.val(&pre.k, j);
    let val_p = c.val(&pre.k, &pre.p);
    let prop = c.eq_nat(val_j, val_p);

    // motive : Decidable prop → Fin k := fun _ => Fin k
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let dec_prop = Expr::app(c.decidable.clone(), prop.clone());
        let (d_id, _d) = d.fresh_local(dec_prop.clone());
        d.finish_child(d.mk_lam(d_id, BinderInfo::Default, dec_prop, pre.fin_k.clone()))
    };
    // isFalse minor: fun (hne : prop → False) => Fin.mk k v hlt
    let not_p = Expr::pi(BinderInfo::Default, prop.clone(), c.false_c.clone());
    let is_false_min = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (hne_id, hne) = d.fresh_local(not_p.clone());
        let body = complement_ne_branch_value(c, pre, &d, j, &hne);
        d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_p.clone(), body))
    };
    // isTrue minor: fun (heq : prop) => j
    let is_true_min = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (heq_id, _heq) = d.fresh_local(prop.clone());
        d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, prop.clone(), j.clone()))
    };
    Expr::apps(
        c.decidable_rec1.clone(),
        [prop, motive, is_false_min, is_true_min, dd],
    )
}

fn complement_value(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let discr = Expr::apps(c.nat_deceq.clone(), [val_j, val_p]);
    let rec_app = complement_rec_at(c, &pre, &pre.b, &j, discr);
    let body = pre
        .b
        .mk_lam(j_id, BinderInfo::Default, pre.fin_k.clone(), rec_app);
    close_cprefix(&pre, body, false)
}

// ===========================================================================
// Fin.sigmaComplement_coh_ne :
//   (k)(σ)(hinv)(p)(hcase)(j : Fin k)(hne : val j = val p → False)
//     → @Eq (Fin (k+1)) (σ (castSucc k j)) (castSucc k (σ'' j))
//
// In the `≠` branch, σ'' j ι-reduces to `Fin.mk k v hlt` (v = val (σ (castSucc
// j))), so castSucc (σ'' j) has val ≡ v, and σ (castSucc j) has val ≡ v.  Close
// by Fin.eq_of_val_eq with Eq.refl.  We dispatch via Decidable.rec.{0} on the
// SAME discriminant so σ'' j reduces to the isFalse minor; the isTrue minor is
// vacuous (its heq : val j = val p contradicts hne).
// ===========================================================================
fn coh_ne_type(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let succ_k = c.succ(&pre.k);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let not_p = Expr::pi(
        BinderInfo::Default,
        c.eq_nat(val_j, val_p),
        c.false_c.clone(),
    );
    let (hne_id, hne) = pre.b.fresh_local(not_p.clone());
    let lhs = Expr::app(pre.sigma.clone(), c.cast_succ(&pre.k, &j));
    let spp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &j);
    let _ = &hne;
    let rhs = c.cast_succ(&pre.k, &spp);
    let concl = c.eq_fin(&succ_k, lhs, rhs);
    let body = pre.b.mk_pi(hne_id, BinderInfo::Default, not_p, concl);
    let body = pre
        .b
        .mk_pi(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, true)
}

/// Goal of `coh_ne` written with `σ'' j` REPLACED by `complement_rec_at(dd)`
/// for a discriminant `dd`: `σ (castSucc j) = castSucc (complement_rec_at dd)`.
/// At `dd := Nat.decEq …` this is the actual `coh_ne` goal; the dependent motive
/// abstracts `dd` so each branch's rec reduces.
fn coh_goal_at(c: &SigmaComplementConsts, pre: &CPrefix, j: &Expr, rec_dd: Expr) -> Expr {
    let succ_k = c.succ(&pre.k);
    let sig_cs = Expr::app(pre.sigma.clone(), c.cast_succ(&pre.k, j));
    c.eq_fin(&succ_k, sig_cs, c.cast_succ(&pre.k, &rec_dd))
}

fn coh_ne_value(c: &SigmaComplementConsts) -> Expr {
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

    // motive : (dd : Decidable prop) → Prop
    //   := fun dd => σ (castSucc j) = castSucc (complement_rec_at dd)
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let dec_prop = Expr::app(c.decidable.clone(), prop.clone());
        let (dd_id, dd) = d.fresh_local(dec_prop.clone());
        let goal_dd = coh_goal_at(c, &pre, &j, complement_rec_at(c, &pre, &d, &j, dd));
        d.finish_child(d.mk_lam(dd_id, BinderInfo::Default, dec_prop, goal_dd))
    };

    // isFalse minor: fun (hne2 : ¬prop) => Fin.eq_of_val_eq … (Eq.refl Nat v).
    //   Goal here is `σ (castSucc j) = castSucc (complement_rec_at (isFalse hne2))`
    //   ≡ `σ (castSucc j) = castSucc (Fin.mk k v hlt)` (ι); both have val ≡ v.
    let is_false_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (hne2_id, hne2) = d.fresh_local(not_p.clone());
        let spp_branch = complement_ne_branch_value(c, &pre, &d, &j, &hne2); // Fin.mk k v hlt
        let cs_spp = c.cast_succ(&pre.k, &spp_branch);
        let v = c.val(&succ_k, &sig_cs);
        let hval = Expr::apps(c.eq_refl_nat.clone(), [c.nat.clone(), v]);
        let body = Expr::apps(
            c.fin_eq_of_val.clone(),
            [succ_k.clone(), sig_cs.clone(), cs_spp, hval],
        );
        d.finish_child(d.mk_lam(hne2_id, BinderInfo::Default, not_p.clone(), body))
    };

    // isTrue minor: fun (heq : prop) => False.elim (hne heq) — outer hne excludes.
    //   Goal here is `σ (castSucc j) = castSucc j` (ι via isTrue), discharged
    //   vacuously by the contradiction `hne heq`.
    let is_true_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (heq_id, heq) = d.fresh_local(prop.clone());
        let goal_true = coh_goal_at(c, &pre, &j, j.clone()); // σ (castSucc j) = castSucc j
        let false_pf = Expr::app(hne.clone(), heq.clone());
        let false_elim0 = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
        let body = Expr::apps(false_elim0, [goal_true, false_pf]);
        d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, prop.clone(), body))
    };

    let discr = Expr::apps(c.nat_deceq.clone(), [val_j.clone(), val_p.clone()]);
    let rec_app = Expr::apps(
        c.decidable_rec0.clone(),
        [prop.clone(), motive, is_false_min, is_true_min, discr],
    );

    let body = pre.b.mk_lam(hne_id, BinderInfo::Default, not_p, rec_app);
    let body = pre
        .b
        .mk_lam(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, false)
}

include!("boolean_analysis_fin_sigma_complement_build3.rs");
