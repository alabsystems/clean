// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The `Fin.sum_reindex_twocycle_step` proof body. `include!`d (transitively)
// into the module owning `TwoCycleConsts`.

fn twocycle_step_value(c: &TwoCycleConsts) -> Expr {
    let mut pre = make_tc_prefix(c);
    let k = pre.k.clone();
    let k0 = pre.k0.clone();
    let m = pre.m.clone();
    let fin_m = pre.fin_m.clone();
    let fin_k = pre.fin_k.clone();
    let f_ty = c.fin_to_rat(&m);
    let (f_id, f) = pre.b.fresh_local(f_ty.clone());

    let last_k = c.last(&k); // Fin.last k : Fin m
    let cs_p = c.cast_succ(&k, &pre.p); // castSucc k p : Fin m

    // σ'' := Fin.sigmaComplement k σ hinv p hcase : Fin k → Fin k
    let spp_fn = Expr::apps(
        c.sigma_complement.clone(),
        [
            k.clone(),
            pre.sigma.clone(),
            pre.hinv.clone(),
            pre.p.clone(),
            pre.hcase.clone(),
        ],
    );

    // freindex := fun jx : Fin m => F (σ jx)   (the keystone LHS summand)
    let freindex = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (jx_id, jx) = d.fresh_local(fin_m.clone());
        let body = Expr::app(f.clone(), Expr::app(pre.sigma.clone(), jx.clone()));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, fin_m.clone(), body))
    };
    // Sσ := fun j : Fin k => F (σ (castSucc k j))   [≡ freindex ∘ castSucc, β]
    let s_sig = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        let body = Expr::app(f.clone(), Expr::app(pre.sigma.clone(), c.cast_succ(&k, &j)));
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    // Cf := fun j : Fin k => F (castSucc k j)
    let cf = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        let body = Expr::app(f.clone(), c.cast_succ(&k, &j));
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    // Sσ'' := fun j : Fin k => F (castSucc k (σ'' j))   [≡ Cf ∘ σ'', β]
    let s_spp = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        let body = Expr::app(
            f.clone(),
            c.cast_succ(&k, &Expr::app(spp_fn.clone(), j.clone())),
        );
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };

    let a = Expr::app(f.clone(), last_k.clone()); // F (last k)
    let bb = Expr::app(f.clone(), cs_p.clone()); // F (castSucc p)

    // ── complement summands over Fin k0 ──
    // Wσ := fun i : Fin k0 => Sσ (skipNth k0 p i)
    let w_sig = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (i_id, i) = d.fresh_local(c.fin_of(&k0));
        let body = Expr::app(s_sig.clone(), c.skip(&k0, &pre.p, &i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&k0), body))
    };
    // Wσ'' := fun i : Fin k0 => Sσ'' (skipNth k0 p i)
    let w_spp = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (i_id, i) = d.fresh_local(c.fin_of(&k0));
        let body = Expr::app(s_spp.clone(), c.skip(&k0, &pre.p, &i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&k0), body))
    };
    let sum_w_sig = c.sum(&k0, &w_sig);
    let sum_w_spp = c.sum(&k0, &w_spp);

    // ===========================================================================
    // LEG L1: Σ_m freindex = Σ_k Sσ + F (σ (last k))     [Fin.sum_succ k freindex]
    //   (the peeled prefix `fun i => freindex (castSucc i)` is β-eq to Sσ.)
    // ===========================================================================
    let sum_m_re = c.sum(&m, &freindex);
    let sum_k_ssig = c.sum(&k, &s_sig);
    let sig_last = Expr::app(pre.sigma.clone(), last_k.clone()); // σ (last k)
    let f_sig_last = Expr::app(f.clone(), sig_last.clone()); // F (σ (last k))
    let l1_rhs = c.add(sum_k_ssig.clone(), f_sig_last.clone());
    let l1 = Expr::apps(c.fin_sum_succ.clone(), [k.clone(), freindex.clone()]);
    // l1 : Σ_m freindex = Σ_k Sσ + F (σ (last k))   (kernel folds β)

    // L2: F (σ (last k)) = F (castSucc p) = bb    [congrArg F hcase]
    let l2 = Expr::apps(
        c.congr_arg.clone(),
        [
            fin_m.clone(),
            c.rat.clone(),
            sig_last.clone(),
            cs_p.clone(),
            f.clone(),
            pre.hcase.clone(),
        ],
    );
    // congrArg (Σ_k Sσ + ·) l2 : Σ_k Sσ + F(σ last) = Σ_k Sσ + bb
    let add_ssig = Expr::app(c.rat_add.clone(), sum_k_ssig.clone());
    let l1b_rhs = c.add(sum_k_ssig.clone(), bb.clone());
    let l2lift = Expr::apps(
        c.congr_arg.clone(),
        [
            c.rat.clone(),
            c.rat.clone(),
            f_sig_last.clone(),
            bb.clone(),
            add_ssig,
            l2,
        ],
    );
    // chain L1·L2lift : Σ_m freindex = Σ_k Sσ + bb
    let lhs_eq_ssigbb = Expr::apps(
        c.eq_trans.clone(),
        [
            c.rat.clone(),
            sum_m_re.clone(),
            l1_rhs.clone(),
            l1b_rhs.clone(),
            l1,
            l2lift,
        ],
    );

    // ===========================================================================
    // LEG R: Σ_m F = Σ_k Cf + a    [Fin.sum_succ k F]
    // ===========================================================================
    let sum_m_f = c.sum(&m, &f);
    let sum_k_cf = c.sum(&k, &cf);
    let _r_rhs = c.add(sum_k_cf.clone(), a.clone());
    let r1 = Expr::apps(c.fin_sum_succ.clone(), [k.clone(), f.clone()]);

    // The tail (sum_remove legs, complement-sum equality, IH, final assembly)
    // lives in build4 as a single block expression — the function's return value.
    include!("boolean_analysis_fin_reindex_twocycle_build4.rs")
}
