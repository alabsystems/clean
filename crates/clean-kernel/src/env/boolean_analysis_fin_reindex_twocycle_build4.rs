// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tail of `twocycle_step_value`: the sum_remove legs, the complement-sum
// equality (sum_congr + coh_ne), the IH application, and the final
// add_swap_outer assembly.  `include!`d as a SINGLE block expression at the END
// of `twocycle_step_value` (build3).
{
// ── LEG A: Σ_k Sσ = a + sum_w_sig ──
//   sum_remove k0 p Sσ : Σ_k Sσ = Sσ p + sum_w_sig.  Sσ p ≡ F (σ (castSucc p)).
//   partner : σ (castSucc p) = last k.  congrArg F partner : Sσ p = a.
let ssig_p = Expr::app(s_sig.clone(), pre.p.clone()); // Sσ p ≡ F (σ (castSucc p))
let remove_ssig = Expr::apps(
    c.fin_sum_remove.clone(),
    [k0.clone(), pre.p.clone(), s_sig.clone()],
);
// remove_ssig : Σ_k Sσ = Rat.add (Sσ p) sum_w_sig
let a_mid = c.add(ssig_p.clone(), sum_w_sig.clone());
// partner : σ (castSucc p) = last k
let partner = Expr::apps(
    c.sc_partner.clone(),
    [
        k.clone(),
        pre.sigma.clone(),
        pre.hinv.clone(),
        pre.p.clone(),
        pre.hcase.clone(),
    ],
);
// congrArg F partner : F (σ (castSucc p)) = F (last k) = a  [Sσ p ≡ F(σ(castSucc p))]
let sig_cs_p = Expr::app(pre.sigma.clone(), cs_p.clone()); // σ (castSucc p)
let ssig_p_eq_a = Expr::apps(
    c.congr_arg.clone(),
    [
        fin_m.clone(),
        c.rat.clone(),
        sig_cs_p.clone(),
        last_k.clone(),
        f.clone(),
        partner,
    ],
);
// congrArg (· + sum_w_sig) (ssig_p_eq_a) : (Sσ p + sum_w_sig) = (a + sum_w_sig)
let add_flip_wsig = {
    let mut d = EnvDeclBuilder::child_of(&pre.b);
    let (x_id, x) = d.fresh_local(c.rat.clone());
    let body = c.add(x.clone(), sum_w_sig.clone());
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
};
let a_plus_w = c.add(a.clone(), sum_w_sig.clone());
let leg_a_2 = Expr::apps(
    c.congr_arg.clone(),
    [
        c.rat.clone(),
        c.rat.clone(),
        ssig_p.clone(),
        a.clone(),
        add_flip_wsig,
        ssig_p_eq_a,
    ],
);
// legA : Σ_k Sσ = a + sum_w_sig
let leg_a = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_k_ssig.clone(),
        a_mid.clone(),
        a_plus_w.clone(),
        remove_ssig,
        leg_a_2,
    ],
);

// ── LEG B: Σ_k Sσ'' = bb + sum_w_spp ──
let sspp_p = Expr::app(s_spp.clone(), pre.p.clone()); // Sσ'' p ≡ F (castSucc (σ'' p))
let remove_sspp = Expr::apps(
    c.fin_sum_remove.clone(),
    [k0.clone(), pre.p.clone(), s_spp.clone()],
);
let b_mid = c.add(sspp_p.clone(), sum_w_spp.clone());
// fix_p : σ'' p = p
let fix_p = Expr::apps(
    c.sc_fix_p.clone(),
    [
        k.clone(),
        pre.sigma.clone(),
        pre.hinv.clone(),
        pre.p.clone(),
        pre.hcase.clone(),
    ],
);
// congrArg (fun x => F (castSucc k x)) fix_p : F (castSucc (σ'' p)) = F (castSucc p) = bb
let f_cast_fn = {
    let mut d = EnvDeclBuilder::child_of(&pre.b);
    let (x_id, x) = d.fresh_local(fin_k.clone());
    let body = Expr::app(f.clone(), c.cast_succ(&k, &x));
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, fin_k.clone(), body))
};
let spp_p = Expr::app(spp_fn.clone(), pre.p.clone()); // σ'' p
let sspp_p_eq_bb = Expr::apps(
    c.congr_arg.clone(),
    [
        fin_k.clone(),
        c.rat.clone(),
        spp_p.clone(),
        pre.p.clone(),
        f_cast_fn,
        fix_p,
    ],
);
let add_flip_wspp = {
    let mut d = EnvDeclBuilder::child_of(&pre.b);
    let (x_id, x) = d.fresh_local(c.rat.clone());
    let body = c.add(x.clone(), sum_w_spp.clone());
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
};
let bb_plus_wspp = c.add(bb.clone(), sum_w_spp.clone());
let leg_b_2 = Expr::apps(
    c.congr_arg.clone(),
    [
        c.rat.clone(),
        c.rat.clone(),
        sspp_p.clone(),
        bb.clone(),
        add_flip_wspp,
        sspp_p_eq_bb,
    ],
);
let sum_k_sspp = c.sum(&k, &s_spp);
let leg_b = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_k_sspp.clone(),
        b_mid.clone(),
        bb_plus_wspp.clone(),
        remove_sspp,
        leg_b_2,
    ],
);

// ── LEG W: sum_w_sig = sum_w_spp   [Fin.sum_congr k0 Wσ Wσ'' pw] ──
//   pw i : Wσ i = Wσ'' i, i.e. F (σ (castSucc (skipNth k0 p i)))
//                            = F (castSucc (σ'' (skipNth k0 p i))).
//   = congrArg F (coh_ne (skipNth k0 p i) (skipNth_ne_p k0 p i)).
let pw = {
    let mut d = EnvDeclBuilder::child_of(&pre.b);
    let (i_id, i) = d.fresh_local(c.fin_of(&k0));
    let sk = c.skip(&k0, &pre.p, &i); // skipNth k0 p i : Fin k
    // hne_sk : val sk = val p → False   [skipNth_ne_p k0 p i]
    let hne_sk = Expr::apps(c.skip_ne_p.clone(), [k0.clone(), pre.p.clone(), i.clone()]);
    // coh_ne k σ hinv p hcase sk hne_sk : σ (castSucc sk) = castSucc (σ'' sk)
    let coh = Expr::apps(
        c.sc_coh_ne.clone(),
        [
            k.clone(),
            pre.sigma.clone(),
            pre.hinv.clone(),
            pre.p.clone(),
            pre.hcase.clone(),
            sk.clone(),
            hne_sk,
        ],
    );
    let sig_cs_sk = Expr::app(pre.sigma.clone(), c.cast_succ(&k, &sk)); // σ (castSucc sk)
    let cs_spp_sk = c.cast_succ(&k, &Expr::app(spp_fn.clone(), sk.clone())); // castSucc (σ'' sk)
    // congrArg F coh : F (σ (castSucc sk)) = F (castSucc (σ'' sk))   [≡ Wσ i = Wσ'' i, β]
    let body = Expr::apps(
        c.congr_arg.clone(),
        [
            fin_m.clone(),
            c.rat.clone(),
            sig_cs_sk,
            cs_spp_sk,
            f.clone(),
            coh,
        ],
    );
    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&k0), body))
};
let leg_w = Expr::apps(
    c.fin_sum_congr.clone(),
    [k0.clone(), w_sig.clone(), w_spp.clone(), pw],
);
// leg_w : sum_w_sig = sum_w_spp

// ── IH: Σ_k Sσ'' = Σ_k Cf ──
//   ih σ'' (involutive) Cf : Σ_k (fun j => Cf (σ'' j)) = Σ_k Cf  [Cf(σ'' j) ≡ Sσ'' j, β]
let involutive = Expr::apps(
    c.sc_involutive.clone(),
    [
        k.clone(),
        pre.sigma.clone(),
        pre.hinv.clone(),
        pre.p.clone(),
        pre.hcase.clone(),
    ],
);
let ih_app = Expr::apps(pre.ih.clone(), [spp_fn.clone(), involutive, cf.clone()]);
// ih_app : Σ_k Sσ'' = Σ_k Cf   (LHS β-eq to Σ_k Sσ'')

// ===========================================================================
// FINAL ASSEMBLY
//   Σ_m freindex = Σ_k Sσ + bb          [lhs_eq_ssigbb]
//               = (a + sum_w_sig) + bb   [congrArg (·+bb) leg_a]
//               = (bb + sum_w_sig) + a   [add_swap_outer a sum_w_sig bb]
//               = Σ_m F                  [via leg_b, leg_w, ih_app, r1 — reversed]
// ===========================================================================

// step P1 : Σ_k Sσ + bb = (a + sum_w_sig) + bb   [congrArg (·+bb) leg_a]
let add_flip_bb = {
    let mut d = EnvDeclBuilder::child_of(&pre.b);
    let (x_id, x) = d.fresh_local(c.rat.clone());
    let body = c.add(x.clone(), bb.clone());
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
};
let awb = c.add(a_plus_w.clone(), bb.clone()); // (a + sum_w_sig) + bb
let p1 = Expr::apps(
    c.congr_arg.clone(),
    [
        c.rat.clone(),
        c.rat.clone(),
        sum_k_ssig.clone(),
        a_plus_w.clone(),
        add_flip_bb,
        leg_a,
    ],
);
// lhs1 : Σ_m freindex = (a + sum_w_sig) + bb
let lhs1 = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_m_re.clone(),
        c.add(sum_k_ssig.clone(), bb.clone()),
        awb.clone(),
        lhs_eq_ssigbb,
        p1,
    ],
);

// step SW : (a + sum_w_sig) + bb = (bb + sum_w_sig) + a   [add_swap_outer a sum_w_sig bb]
let bwa = c.add(c.add(bb.clone(), sum_w_sig.clone()), a.clone());
let sw = Expr::apps(
    c.rat_add_swap_outer.clone(),
    [a.clone(), sum_w_sig.clone(), bb.clone()],
);
// lhs2 : Σ_m freindex = (bb + sum_w_sig) + a
let lhs2 = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_m_re.clone(),
        awb.clone(),
        bwa.clone(),
        lhs1,
        sw,
    ],
);

// ── Now show Σ_m F = (bb + sum_w_sig) + a, then symm + trans. ──
// r1 : Σ_m F = Σ_k Cf + a
// e_cf_sspp : Σ_k Cf = Σ_k Sσ''   [ih_app.symm]
let e_cf_sspp = Expr::apps(
    c.eq_symm.clone(),
    [c.rat.clone(), sum_k_sspp.clone(), sum_k_cf.clone(), ih_app.clone()],
);
let add_flip_a = {
    let mut d = EnvDeclBuilder::child_of(&pre.b);
    let (x_id, x) = d.fresh_local(c.rat.clone());
    let body = c.add(x.clone(), a.clone());
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body))
};
let cf_a = c.add(sum_k_cf.clone(), a.clone());
let sspp_a = c.add(sum_k_sspp.clone(), a.clone());
// rstep1 : (Σ_k Cf + a) = (Σ_k Sσ'' + a)   [congrArg (·+a) e_cf_sspp]
let rstep1 = Expr::apps(
    c.congr_arg.clone(),
    [
        c.rat.clone(),
        c.rat.clone(),
        sum_k_cf.clone(),
        sum_k_sspp.clone(),
        add_flip_a.clone(),
        e_cf_sspp,
    ],
);
// r_to_sspp_a : Σ_m F = (Σ_k Sσ'' + a)    [r1 · rstep1]
let r_to_sspp_a = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_m_f.clone(),
        cf_a.clone(),
        sspp_a.clone(),
        r1,
        rstep1,
    ],
);
// leg_b : Σ_k Sσ'' = (bb + sum_w_spp) ; congrArg (·+a) → (Σ_k Sσ'' + a) = ((bb+sum_w_spp)+a)
let bwspp_a = c.add(bb_plus_wspp.clone(), a.clone());
let rstep2 = Expr::apps(
    c.congr_arg.clone(),
    [
        c.rat.clone(),
        c.rat.clone(),
        sum_k_sspp.clone(),
        bb_plus_wspp.clone(),
        add_flip_a.clone(),
        leg_b,
    ],
);
let r_to_bwspp_a = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_m_f.clone(),
        sspp_a.clone(),
        bwspp_a.clone(),
        r_to_sspp_a,
        rstep2,
    ],
);
// leg_w.symm : sum_w_spp = sum_w_sig ; congrArg (fun W => (bb + W) + a) → align ((bb+sum_w_spp)+a)=((bb+sum_w_sig)+a)
// leg_w : sum_w_sig = sum_w_spp  ⇒  Eq.symm with a=sum_w_sig, b=sum_w_spp gives sum_w_spp = sum_w_sig
let leg_w_sym = Expr::apps(
    c.eq_symm.clone(),
    [c.rat.clone(), sum_w_sig.clone(), sum_w_spp.clone(), leg_w],
);
let bw_plus_a_fn = {
    let mut d = EnvDeclBuilder::child_of(&pre.b);
    let (ww_id, ww) = d.fresh_local(c.rat.clone());
    let body = c.add(c.add(bb.clone(), ww.clone()), a.clone());
    d.finish_child(d.mk_lam(ww_id, BinderInfo::Default, c.rat.clone(), body))
};
let rstep3 = Expr::apps(
    c.congr_arg.clone(),
    [
        c.rat.clone(),
        c.rat.clone(),
        sum_w_spp.clone(),
        sum_w_sig.clone(),
        bw_plus_a_fn,
        leg_w_sym,
    ],
);
// r_to_bwa : Σ_m F = (bb + sum_w_sig) + a = bwa
let r_to_bwa = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_m_f.clone(),
        bwspp_a.clone(),
        bwa.clone(),
        r_to_bwspp_a,
        rstep3,
    ],
);
// r_to_bwa.symm : bwa = Σ_m F
let bwa_eq_f = Expr::apps(
    c.eq_symm.clone(),
    [c.rat.clone(), sum_m_f.clone(), bwa.clone(), r_to_bwa],
);

// proof : Σ_m freindex = Σ_m F   [lhs2 · bwa_eq_f]
let proof = Expr::apps(
    c.eq_trans.clone(),
    [
        c.rat.clone(),
        sum_m_re.clone(),
        bwa.clone(),
        sum_m_f.clone(),
        lhs2,
        bwa_eq_f,
    ],
);

let body = pre.b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
close_tc_prefix(&pre, body, false)
}
