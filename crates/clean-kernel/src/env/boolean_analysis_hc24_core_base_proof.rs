// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_hc24_core_base.rs` — the carrier-collapse proof
// term for the `n = 0` base case. All terms inline (no new globals), so the
// theorem's axiom closure stays empty.

/// `Fin.sum 1 g = g (Fin.last 0)`.
///
/// `Fin.sum_succ 0 g : Fin.sum 1 g = Fin.sum 0 (g∘castSucc) + g(last 0)`;
/// `Fin.sum_zero` collapses the prefix to `0`; `Rat.zero_add` drops it.
fn sum_one_collapse(c: &Hc24Consts, parent: &EnvDeclBuilder, g: &Expr) -> Expr {
    let zero = c.nat_zero.clone();
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let fin_sum_succ = Expr::const_(Name::from_string("Fin.sum_succ"), vec![]);
    let fin_sum_zero = Expr::const_(Name::from_string("Fin.sum_zero"), vec![]);
    let fin_cast_succ = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
    let rat_add = c.rat_add.clone();
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);

    let g_last = Expr::app(g.clone(), c.last(&zero));

    // step_succ : Fin.sum 1 g = Fin.sum 0 (g∘castSucc) + g(last 0)
    let step_succ = Expr::apps(fin_sum_succ, [zero.clone(), g.clone()]);
    // g∘castSucc : fun i : Fin 0 => g (castSucc 0 i)
    let g_cast = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin0 = c.fin_of(&zero);
        let (i_id, i) = d.fresh_local(fin0.clone());
        let cast = Expr::apps(fin_cast_succ, [zero.clone(), i]);
        let body = Expr::app(g.clone(), cast);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin0, body))
    };
    let sum_prefix = c.sum(&zero, g_cast.clone());
    let succ_rhs = Expr::apps(rat_add.clone(), [sum_prefix.clone(), g_last.clone()]);
    // step_zero : Fin.sum 0 (g∘castSucc) = Rat.zero
    let step_zero = Expr::app(fin_sum_zero, g_cast);
    // cong : (prefix + g_last) = (0 + g_last)
    let add_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = Expr::apps(rat_add.clone(), [z, g_last.clone()]);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let zero_plus = Expr::apps(rat_add, [rat_zero.clone(), g_last.clone()]);
    let cong_zero = c.congr_arg(sum_prefix, rat_zero, add_fn, step_zero);
    // zero_add : 0 + g_last = g_last
    let zero_add = Expr::app(rat_zero_add, g_last.clone());

    let sum_one = c.sum(&one, g.clone());
    let t1 = c.trans(
        sum_one.clone(),
        succ_rhs.clone(),
        zero_plus.clone(),
        step_succ,
        cong_zero,
    );
    c.trans(sum_one, zero_plus, g_last, t1, zero_add)
}

/// The base-case proof body (the `LE` goal proof, with `ρ`, `F` free).
fn build_base_proof(c: &Hc24Consts, parent: &EnvDeclBuilder, rho: &Expr, f: &Expr) -> Expr {
    let zero = c.nat_zero.clone();
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let last0 = c.last(&zero);
    let dec = c.decode(&zero, &last0); // hcDecode 0 (last 0)
    let f_dec = Expr::app(f.clone(), dec.clone()); // F (hcDecode 0 (last 0))

    // ── The two summand functions in the goal.
    // lhs_fn jx := pow4 (noiseFn ρ 0 F jx)
    let lhs_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = d.fresh_local(c.fin_of(&c.pow2(&zero)));
        let body = c.pow4(&c.noise_fn(rho, &zero, f, &jx));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&c.pow2(&zero)), body))
    };
    // inner_fn jx := sq (F (hcDecode 0 jx))
    let inner_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = d.fresh_local(c.fin_of(&c.pow2(&zero)));
        let body = c.sq(&Expr::app(f.clone(), c.decode(&zero, &jx)));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&c.pow2(&zero)), body))
    };

    // LHS = Fin.sum 1 lhs_fn  (2^0 ≡ 1 defeq).
    let lhs = c.sum(&one, lhs_fn.clone());

    // ── LHS collapse: Fin.sum 1 lhs_fn = lhs_fn (last 0) = pow4 (noiseFn ρ 0 F (last 0)).
    let lhs_collapse = sum_one_collapse(c, parent, &lhs_fn);
    let noise_last = c.noise_fn(rho, &zero, f, &last0);
    let pow4_noise = c.pow4(&noise_last); // = lhs_fn (last 0)  (defeq)

    // ── noiseFn ρ 0 F (last 0) = F(dec)·noiseDensityW ρ 0 (dec)(dec)   [noiseFn_zero_dim]
    let noise_zero_dim = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noiseFn_zero_dim"), vec![]),
        [rho.clone(), f.clone(), last0.clone()],
    );
    let dens = c.density(rho, &zero, &dec, &dec); // noiseDensityW ρ 0 (dec)(dec) ≡ 1 defeq
    let f_dec_dens = c.mul(f_dec.clone(), dens.clone()); // F(dec)·(noiseDensityW ρ 0 …)
                                                         // F(dec)·(noiseDensityW ρ 0 …) = F(dec)·1 = F(dec)  [mul_one, density ≡ 1 defeq]
    let mul_one_fdec = c.mul_one(f_dec.clone()); // F(dec)·1 = F(dec); LHS defeq f_dec_dens
                                                 // noise_eq : noiseFn ρ 0 F (last 0) = F(dec)
    let noise_eq = c.trans(
        noise_last.clone(),
        f_dec_dens.clone(),
        f_dec.clone(),
        noise_zero_dim,
        mul_one_fdec,
    );

    // lift through pow4: pow4 (noiseFn …) = pow4 (F dec)
    let pow4_fdec = c.pow4(&f_dec);
    let pow4_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.pow4(&z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let pow4_eq = c.congr_arg(noise_last.clone(), f_dec.clone(), pow4_fn, noise_eq);
    // lhs_collapse : lhs = pow4_noise ; pow4_eq : pow4_noise = pow4_fdec
    let lhs_eq_pow4 = c.trans(
        lhs.clone(),
        pow4_noise.clone(),
        pow4_fdec.clone(),
        lhs_collapse,
        pow4_eq,
    );

    // ── RHS = (powNat 8 0) · sq (Fin.sum 1 inner_fn).
    let inner_sum = c.sum(&one, inner_fn.clone());
    let sq_inner = c.sq(&inner_sum);
    let rhs = c.mul(c.pow8(&zero), sq_inner.clone());

    // inner collapse: Fin.sum 1 inner_fn = inner_fn (last 0) = sq (F dec)  (defeq).
    let inner_collapse = sum_one_collapse(c, parent, &inner_fn);
    let sq_fdec = c.sq(&f_dec); // = inner_fn (last 0) defeq
                                // lift through sq: sq (Fin.sum 1 inner_fn) = sq (sq (F dec))
    let sq_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.sq(&z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let sq_sq_fdec = c.sq(&sq_fdec); // sq (sq (F dec)) = pow4 (F dec) syntactically (both (·²)·(·²))
    let sq_inner_eq = c.congr_arg(inner_sum.clone(), sq_fdec.clone(), sq_fn, inner_collapse);

    // lift through (powNat 8 0)·· : RHS = (powNat 8 0) · sq(sq(F dec))
    let pow8_0 = c.pow8(&zero);
    let mul_pow8_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(pow8_0.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let pow8_sqsq = c.mul(pow8_0.clone(), sq_sq_fdec.clone());
    let rhs_step1 = c.congr_arg(
        sq_inner.clone(),
        sq_sq_fdec.clone(),
        mul_pow8_fn,
        sq_inner_eq,
    );

    // powNat 8 0 = 1  [powNat_zero], lift over (·)·sq(sq(F dec))
    let powzero = Expr::apps(
        Expr::const_(Name::from_string("Rat.powNat_zero"), vec![]),
        [c.eight_rat()],
    );
    let mul_by_sqsq_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z, sq_sq_fdec.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let one_sqsq = c.mul(c.rat_one.clone(), sq_sq_fdec.clone());
    let rhs_step2 = c.congr_arg(pow8_0.clone(), c.rat_one.clone(), mul_by_sqsq_fn, powzero);
    // 1 · sq(sq(F dec)) = sq(sq(F dec))  [one_mul]
    let one_mul_sqsq = c.one_mul(sq_sq_fdec.clone());

    // rhs chain: rhs = pow8_sqsq = one_sqsq = sq_sq_fdec
    let r1 = c.trans(
        rhs.clone(),
        pow8_sqsq.clone(),
        one_sqsq.clone(),
        rhs_step1,
        rhs_step2,
    );
    let rhs_eq_pow4 = c.trans(rhs.clone(), one_sqsq, sq_sq_fdec.clone(), r1, one_mul_sqsq);

    // `sq_sq_fdec` and `pow4_fdec` are syntactically identical: both `(x·x)·(x·x)`
    // with x := F dec.  So `rhs = pow4_fdec` and `lhs = pow4_fdec`.

    // ── Close: le_refl (pow4 (F dec)) : pow4_fdec ≤ pow4_fdec, then substitute
    // LHS ⇐ pow4_fdec (symm lhs_eq_pow4) and RHS ⇐ pow4_fdec (symm rhs_eq_pow4).
    let refl = c.le_refl(pow4_fdec.clone()); // pow4_fdec ≤ pow4_fdec

    // subst on the LEFT operand of ≤:  motive z := (z ≤ pow4_fdec); transport along
    //   (symm lhs_eq_pow4) : pow4_fdec = lhs.
    let le_left_motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.le(z, pow4_fdec.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h_pow4_eq_lhs = c.symm(lhs.clone(), pow4_fdec.clone(), lhs_eq_pow4); // pow4_fdec = lhs
    let after_left = subst_prop(
        c,
        pow4_fdec.clone(),
        lhs.clone(),
        le_left_motive,
        h_pow4_eq_lhs,
        refl,
    );
    // now after_left : lhs ≤ pow4_fdec

    // subst on the RIGHT operand:  motive z := (lhs ≤ z); transport along
    //   (symm rhs_eq_pow4) : pow4_fdec = rhs.
    let le_right_motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.le(lhs.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h_pow4_eq_rhs = c.symm(rhs.clone(), pow4_fdec.clone(), rhs_eq_pow4); // pow4_fdec = rhs
    subst_prop(
        c,
        pow4_fdec,
        rhs,
        le_right_motive,
        h_pow4_eq_rhs,
        after_left,
    )
}

/// `@Eq.subst Rat motive a b h_ab pa : motive b`  (transport `pa : motive a`
/// along `h_ab : a = b`). The motive lands in `Prop` (the `≤` goal).
fn subst_prop(c: &Hc24Consts, a: Expr, b: Expr, motive: Expr, h_ab: Expr, pa: Expr) -> Expr {
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![c.l1.clone()]);
    Expr::apps(eq_subst, [c.rat.clone(), motive, a, b, h_ab, pa])
}
