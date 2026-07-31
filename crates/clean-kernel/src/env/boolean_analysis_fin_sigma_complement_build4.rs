// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for the σ'' complement bundle, part 4: involutivity.
// `include!`d (transitively) into the module owning `SigmaComplementConsts`.

// ===========================================================================
// Fin.sigmaComplement_involutive :
//   (k)(σ)(hinv)(p)(hcase)(j : Fin k) → @Eq (Fin k) (σ'' (σ'' j)) j
//
// Case-split on `Nat.decEq (val j) (val p)` (Decidable.rec.{0}):
// - isTrue (heq : val j = val p):  hjp : σ'' j = j  [eq_self].
//     σ'' (σ'' j) = σ'' j  [congrArg σ''_fn hjp]  = j  [hjp].
// - isFalse (hne : val j = val p → False):
//     (II) coh_ne j hne : σ (castSucc j) = castSucc (σ'' j).
//     hne' := ne_p j hne : val (σ'' j) = val p → False.
//     (I)  coh_ne (σ'' j) hne' : σ (castSucc (σ'' j)) = castSucc (σ'' (σ'' j)).
//     (III) castSucc j = σ (σ (castSucc j)) = σ (castSucc (σ'' j))
//           [hinv (castSucc j) symm ; congrArg σ (II)].
//     (IV) castSucc j = castSucc (σ'' (σ'' j))  [(III) ; (I)].
//     castSucc_inj k j (σ''(σ'' j)) (IV) : j = σ''(σ'' j) ; symm.
// ===========================================================================
fn involutive_type(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let spp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &j);
    let spsp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &spp);
    let concl = c.eq_fin(&pre.k, spsp, j.clone());
    let body = pre
        .b
        .mk_pi(j_id, BinderInfo::Default, pre.fin_k.clone(), concl);
    close_cprefix(&pre, body, true)
}

fn involutive_value(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let _succ_k = c.succ(&pre.k);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let prop = c.eq_nat(val_j.clone(), val_p.clone());

    let spp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &j); // σ'' j
    let spsp = c.sigma_pp(&pre.k, &pre.sigma, &pre.hinv, &pre.p, &pre.hcase, &spp); // σ''(σ'' j)
    let goal = c.eq_fin(&pre.k, spsp.clone(), j.clone());

    // σ''_fn := Fin.sigmaComplement k σ hinv p hcase  (the Fin k → Fin k function)
    let spp_fn = Expr::apps(
        Expr::const_(Name::from_string("Fin.sigmaComplement"), vec![]),
        [
            pre.k.clone(),
            pre.sigma.clone(),
            pre.hinv.clone(),
            pre.p.clone(),
            pre.hcase.clone(),
        ],
    );

    // motive : Decidable prop → Prop := fun _ => goal
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let dec_prop = Expr::app(c.decidable.clone(), prop.clone());
        let (d_id, _d) = d.fresh_local(dec_prop.clone());
        d.finish_child(d.mk_lam(d_id, BinderInfo::Default, dec_prop, goal.clone()))
    };

    // ── isTrue minor: fun (heq : prop) => Eq.trans (congrArg σ''_fn hjp) hjp ──
    let is_true_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (heq_id, heq) = d.fresh_local(prop.clone());
        // hjp : σ'' j = j
        let hjp = Expr::apps(
            Expr::const_(Name::from_string("Fin.sigmaComplement_eq_self"), vec![]),
            [
                pre.k.clone(),
                pre.sigma.clone(),
                pre.hinv.clone(),
                pre.p.clone(),
                pre.hcase.clone(),
                j.clone(),
                heq.clone(),
            ],
        );
        // congrArg σ''_fn hjp : σ'' (σ'' j) = σ'' j
        let cong = Expr::apps(
            c.congr_arg.clone(),
            [
                pre.fin_k.clone(),
                pre.fin_k.clone(),
                spp.clone(),
                j.clone(),
                spp_fn.clone(),
                hjp.clone(),
            ],
        );
        // Eq.trans : σ''(σ'' j) = σ'' j = j
        let body = Expr::apps(
            c.eq_trans.clone(),
            [
                pre.fin_k.clone(),
                spsp.clone(),
                spp.clone(),
                j.clone(),
                cong,
                hjp,
            ],
        );
        d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, prop.clone(), body))
    };

    // ── isFalse minor: fun (hne : prop → False) => … ──
    let not_p = Expr::pi(BinderInfo::Default, prop.clone(), c.false_c.clone());
    let is_false_min = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (hne_id, hne) = d.fresh_local(not_p.clone());

        let cs_j = c.cast_succ(&pre.k, &j);
        let cs_spp = c.cast_succ(&pre.k, &spp);
        let cs_spsp = c.cast_succ(&pre.k, &spsp);
        let sig_cs_j = Expr::app(pre.sigma.clone(), cs_j.clone()); // σ (castSucc j)
        let sig_cs_spp = Expr::app(pre.sigma.clone(), cs_spp.clone()); // σ (castSucc (σ'' j))
        let ss_cs_j = Expr::app(pre.sigma.clone(), sig_cs_j.clone()); // σ(σ(castSucc j))

        // (II) coh_ne j hne : σ (castSucc j) = castSucc (σ'' j)
        let coh_ne = Expr::const_(Name::from_string("Fin.sigmaComplement_coh_ne"), vec![]);
        let coh_j = Expr::apps(
            coh_ne.clone(),
            [
                pre.k.clone(),
                pre.sigma.clone(),
                pre.hinv.clone(),
                pre.p.clone(),
                pre.hcase.clone(),
                j.clone(),
                hne.clone(),
            ],
        );
        // hne' := ne_p j hne : val (σ'' j) = val p → False
        let hne_prime = Expr::apps(
            Expr::const_(Name::from_string("Fin.sigmaComplement_ne_p"), vec![]),
            [
                pre.k.clone(),
                pre.sigma.clone(),
                pre.hinv.clone(),
                pre.p.clone(),
                pre.hcase.clone(),
                j.clone(),
                hne.clone(),
            ],
        );
        // (I) coh_ne (σ'' j) hne' : σ (castSucc (σ'' j)) = castSucc (σ'' (σ'' j))
        let coh_spp = Expr::apps(
            coh_ne,
            [
                pre.k.clone(),
                pre.sigma.clone(),
                pre.hinv.clone(),
                pre.p.clone(),
                pre.hcase.clone(),
                spp.clone(),
                hne_prime,
            ],
        );

        // hinv (castSucc j) : σ(σ(castSucc j)) = castSucc j  → symm
        let hinv_cs_j = Expr::app(pre.hinv.clone(), cs_j.clone());
        let hinv_cs_j_sym = Expr::apps(
            c.eq_symm.clone(),
            [
                pre.fin_succ.clone(),
                ss_cs_j.clone(),
                cs_j.clone(),
                hinv_cs_j,
            ],
        );
        // congrArg σ (coh_j) : σ(σ(castSucc j)) = σ(castSucc (σ'' j))
        let cong_coh_j = Expr::apps(
            c.congr_arg.clone(),
            [
                pre.fin_succ.clone(),
                pre.fin_succ.clone(),
                sig_cs_j.clone(),
                cs_spp.clone(),
                pre.sigma.clone(),
                coh_j,
            ],
        );
        // (III) castSucc j = σ (castSucc (σ'' j))
        let iii = Expr::apps(
            c.eq_trans.clone(),
            [
                pre.fin_succ.clone(),
                cs_j.clone(),
                ss_cs_j.clone(),
                sig_cs_spp.clone(),
                hinv_cs_j_sym,
                cong_coh_j,
            ],
        );
        // (IV) castSucc j = castSucc (σ'' (σ'' j))   [iii ; coh_spp]
        let iv = Expr::apps(
            c.eq_trans.clone(),
            [
                pre.fin_succ.clone(),
                cs_j.clone(),
                sig_cs_spp.clone(),
                cs_spsp.clone(),
                iii,
                coh_spp,
            ],
        );
        // Fin.castSucc_inj k j (σ''(σ'' j)) iv : j = σ''(σ'' j)
        let j_eq = Expr::apps(
            c.cast_succ_inj.clone(),
            [pre.k.clone(), j.clone(), spsp.clone(), iv],
        );
        // symm : σ''(σ'' j) = j
        let body = Expr::apps(
            c.eq_symm.clone(),
            [pre.fin_k.clone(), j.clone(), spsp.clone(), j_eq],
        );
        d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_p.clone(), body))
    };

    let discr = Expr::apps(c.nat_deceq.clone(), [val_j.clone(), val_p.clone()]);
    let rec_app = Expr::apps(
        c.decidable_rec0.clone(),
        [prop.clone(), motive, is_false_min, is_true_min, discr],
    );
    let body = pre
        .b
        .mk_lam(j_id, BinderInfo::Default, pre.fin_k.clone(), rec_app);
    close_cprefix(&pre, body, false)
}
