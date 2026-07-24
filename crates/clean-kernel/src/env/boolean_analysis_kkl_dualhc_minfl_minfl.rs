// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Support-count identity `m·2^n = (2^n)²·Inf` term builder. `include!`d into
// `boolean_analysis_kkl_dualhc_minfl_build.rs`. Regular `//` comments only.

fn m_pow2_type(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let m = c.ssum(&n, c.m_integrand(&b, &n, &f, &i));
    let pp = c.pow(c.rat_two(), &n);
    let inf = c.influence_of(&n, &f, &i);

    let lhs = c.mul(m, pp.clone());
    let rhs = c.mul(c.mul(pp.clone(), pp), inf);
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn m_pow2_value(c: &MinflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let p = c.pow(c.rat_two(), &n); // P := Rat.powNat 2 n
    let pp = c.mul(p.clone(), p.clone()); // P·P
    let m = c.ssum(&n, c.m_integrand(&b, &n, &f, &i)); // m = subsetSum (g²·half²)
    let m_d = c.ssum(&n, c.ind_disagree_integrand(&b, &n, &f, &i)); // m_disagree = subsetSum(ind∘disagree)
    let lit = c.natcast(c.nat_pow_of(c.nat_two(), &n)); // L := mk(ofNat (Nat.pow 2 n)) 1
    let inv_l = c.inv(lit.clone());
    let inv_p = c.inv(p.clone());
    let inf = c.influence_of(&n, &f, &i); // Inf ≡ m_d · inv L (def-eq)

    // h_m : m = m_disagree   (dualhc_step2_m_eq_disagree_mass n f i).
    let h_m = Expr::apps(c.m_eq_mass.clone(), [n.clone(), f.clone(), i.clone()]);

    // h_PL : P = L   (powNat_two_eq_natCast n).
    let h_pl = c.pow_two_natcast_at(&n);

    // P ≠ 0 : ne_zero_of_pos P (0<P).
    let h_p_pos = c.pow_two_pos(&n);
    let h_p_ne = c.ne_at(p.clone(), h_p_pos);
    // P·inv P = 1.
    let p_invp_one = c.mul_inv_cancel_at(p.clone(), h_p_ne);

    // ── core ring chain : (P·P)·(m_d·inv P) = m_d·P ──
    let md_invp = c.mul(m_d.clone(), inv_p.clone()); // m_d·inv P
    let invp_md = c.mul(inv_p.clone(), m_d.clone()); // inv P·m_d
    let pp_md_invp = c.mul(pp.clone(), md_invp.clone()); // (P·P)·(m_d·inv P)
    let pp_invp_md = c.mul(pp.clone(), invp_md.clone()); // (P·P)·(inv P·m_d)
    let pp_invp = c.mul(pp.clone(), inv_p.clone()); // (P·P)·inv P
    let pp_invp_md_assoc = c.mul(pp_invp.clone(), m_d.clone()); // ((P·P)·inv P)·m_d
    let p_pinvp = c.mul(p.clone(), c.mul(p.clone(), inv_p.clone())); // P·(P·inv P)
    let p_one = c.mul(p.clone(), c.rat_one.clone()); // P·1
    let p_md = c.mul(p.clone(), m_d.clone()); // P·m_d
    let md_p = c.mul(m_d.clone(), p.clone()); // m_d·P

    // r1 : (P·P)·(m_d·inv P) = (P·P)·(inv P·m_d)   congr (P·P)·_ (comm m_d (inv P)).
    let r1 = c.congr_l(
        &b,
        &pp,
        md_invp.clone(),
        invp_md.clone(),
        c.comm(m_d.clone(), inv_p.clone()),
    );
    // r2 : (P·P)·(inv P·m_d) = ((P·P)·inv P)·m_d   symm(assoc (P·P)(inv P) m_d).
    let r2 = c.symm_rat(
        pp_invp_md_assoc.clone(),
        pp_invp_md.clone(),
        c.assoc(pp.clone(), inv_p.clone(), m_d.clone()),
    );
    // ppinvp_eq : (P·P)·inv P = P.
    //   a1 : (P·P)·inv P = P·(P·inv P)   assoc P P (inv P).
    let a1 = c.assoc(p.clone(), p.clone(), inv_p.clone());
    //   a2 : P·(P·inv P) = P·1   congr P·_ (P·inv P = 1).
    let a2 = c.congr_l(
        &b,
        &p,
        c.mul(p.clone(), inv_p.clone()),
        c.rat_one.clone(),
        p_invp_one,
    );
    //   a3 : P·1 = P   mul_one P.
    let a3 = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_one"), vec![]),
        [p.clone()],
    );
    let ppinvp_eq = {
        let ch = c.trans_rat(pp_invp.clone(), p_pinvp.clone(), p_one.clone(), a1, a2);
        c.trans_rat(pp_invp.clone(), p_one.clone(), p.clone(), ch, a3)
    };
    // r3 : ((P·P)·inv P)·m_d = P·m_d   congr (·m_d) ppinvp_eq.
    let r3 = c.congr_r(&b, &m_d, pp_invp.clone(), p.clone(), ppinvp_eq);
    // r4 : P·m_d = m_d·P   comm P m_d.
    let r4 = c.comm(p.clone(), m_d.clone());
    // core : (P·P)·(m_d·inv P) = m_d·P.
    let core = {
        let ch = c.trans_rat(
            pp_md_invp.clone(),
            pp_invp_md.clone(),
            pp_invp_md_assoc.clone(),
            r1,
            r2,
        );
        let ch = c.trans_rat(
            pp_md_invp.clone(),
            pp_invp_md_assoc.clone(),
            p_md.clone(),
            ch,
            r3,
        );
        c.trans_rat(pp_md_invp.clone(), p_md.clone(), md_p.clone(), ch, r4)
    };

    // ── LHS path : m·P = m_d·P = (P·P)·(m_d·inv P) ──
    // l1 : m·P = m_d·P   congr (·P) h_m.
    let l1 = c.congr_r(&b, &p, m.clone(), m_d.clone(), h_m);
    // l2 : m_d·P = (P·P)·(m_d·inv P)   symm core.
    let l2 = c.symm_rat(pp_md_invp.clone(), md_p.clone(), core);

    // ── RHS path : (P·P)·(m_d·inv P) = (P·P)·(m_d·inv L) = (P·P)·Inf ──
    let md_invl = c.mul(m_d.clone(), inv_l.clone()); // m_d·inv L
    let pp_md_invl = c.mul(pp.clone(), md_invl.clone()); // (P·P)·(m_d·inv L)
                                                         // h_invpl : inv P = inv L   congrArg inv h_PL.
    let h_invpl = {
        let f_inv = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat.clone());
            let body = c.inv(z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        Expr::apps(
            c.congr_arg1.clone(),
            [
                c.rat.clone(),
                c.rat.clone(),
                p.clone(),
                lit.clone(),
                f_inv,
                h_pl,
            ],
        )
    };
    // h_md_inv : m_d·inv P = m_d·inv L   congr (m_d·_) h_invpl.
    let h_md_inv = c.congr_l(&b, &m_d, inv_p.clone(), inv_l.clone(), h_invpl);
    // rr1 : (P·P)·(m_d·inv P) = (P·P)·(m_d·inv L)   congr (P·P)·_ h_md_inv.
    let rr1 = c.congr_l(&b, &pp, md_invp.clone(), md_invl.clone(), h_md_inv);
    // (P·P)·(m_d·inv L) ≡ (P·P)·Inf (def-eq), so retype the final target via refl.
    let pp_inf = c.mul(pp.clone(), inf.clone());
    let rr2 = c.refl_rat(pp_md_invl.clone()); // : (P·P)·(m_d·inv L) = (P·P)·Inf (def-eq retype)
    let _ = &pp_inf; // documents the def-eq target

    // ── assemble : m·P → m_d·P → (P·P)·(m_d·inv P) → (P·P)·(m_d·inv L) [≡ (P·P)·Inf] ──
    let mp = c.mul(m.clone(), p.clone());
    let proof = {
        let ch = c.trans_rat(mp.clone(), md_p.clone(), pp_md_invp.clone(), l1, l2);
        let ch = c.trans_rat(mp.clone(), pp_md_invp.clone(), pp_md_invl.clone(), ch, rr1);
        c.trans_rat(mp.clone(), pp_md_invl.clone(), pp_inf.clone(), ch, rr2)
    };

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}
