// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_chi_sign_bilinear.rs — the per-index LOW+HIGH
// combine `chi_sign_bilinear_pair_combine`. Split out for the 500-line rule.
//
//   ∀ (n) (S T : HCPoint (n+1)) (j : Fin (2^n)),
//     (χ_S(xlo j)·χ_T(xlo j)) + (χ_S(xhi j)·χ_T(xhi j))
//       = (χ_n (rS)(dec n j) · χ_n (rT)(dec n j)) · (1 + pm(S last)·pm(T last))
//
// where xlo/xhi are the two SIGN cube halves (top bit 0/1), rS/rT the gate
// restrictions, dec n j = hcDecode n j. Dual of `chi_bilinear_pair_combine`:
// the SIGN point is split (gates fixed) instead of the gate (signs fixed).

impl SignBiConsts {
    /// 2-ary congruence over `op`: `op al bl = op ar br` from `hl : al=ar`,
    /// `hr : bl=br`.
    #[allow(clippy::too_many_arguments)]
    fn bin_congr(
        &self,
        parent: &EnvDeclBuilder,
        op: &Expr,
        al: Expr,
        ar: Expr,
        bl: Expr,
        br: Expr,
        hl: Expr,
        hr: Expr,
    ) -> Expr {
        let app2 = |a: Expr, b: Expr| Expr::apps(op.clone(), [a, b]);
        let m1 = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = app2(z, bl.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let s1 = self.congr_rat(al.clone(), ar.clone(), m1, hl);
        let m2 = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = app2(ar.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let s2 = self.congr_rat(bl.clone(), br.clone(), m2, hr);
        self.trans_rat(
            app2(al, bl.clone()),
            app2(ar.clone(), bl),
            app2(ar, br),
            s1,
            s2,
        )
    }
}

/// Build `χ_S(xhalf)·χ_T(xhalf) = prefix · (cf(S last, bit)·cf(T last, bit))`,
/// where `prefix = χ_n(rS)(dec n j)·χ_n(rT)(dec n j)` and the top SIGN bit of
/// `xhalf` is rewritten to `bit_target` (false for LOW, true for HIGH).
/// Returns `(proof, prefix, target)`.
#[allow(clippy::too_many_arguments)]
fn build_sign_half_eq(
    c: &SignBiConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    s: &Expr,
    t: &Expr,
    j: &Expr,
    idx_map: &Expr,
    restrict_lemma: &Expr,
    decode_bit_lemma: &Expr,
    testbit_value_lemma: &Expr,
    bit_target: &Expr,
    bit_inner: &Expr,
) -> (Expr, Expr, Expr) {
    let sn = c.succ(n);
    let xhalf = c.decoded(b, n, idx_map, j);
    let rs = c.restrict(b, n, s);
    let rt = c.restrict(b, n, t);
    let dec_n_j = Expr::apps(c.hc_decode.clone(), [n.clone(), j.clone()]);

    // r_x := restrict (xhalf) — the SIGN point chi_sign_pair_succ produces.
    let r_x = c.restrict(b, n, &xhalf);

    // prefix := χ_n (rS)(dec n j) · χ_n (rT)(dec n j).
    let p_s = c.chi(n.clone(), rs.clone(), dec_n_j.clone());
    let p_t = c.chi(n.clone(), rt.clone(), dec_n_j.clone());
    let prefix = c.mul(p_s.clone(), p_t.clone());

    let s_last = Expr::app(s.clone(), c.last(n));
    let t_last = Expr::app(t.clone(), c.last(n));
    let xhalf_last = Expr::app(xhalf.clone(), c.last(n));

    // chi_sign_pair_succ n S T xhalf :
    //   χ_S(xhalf)·χ_T(xhalf)
    //     = (χ_n (rS)(r_x) · χ_n (rT)(r_x)) · (cf(S last, xhalf_last) · cf(T last, xhalf_last))
    let lhs = c.mul(
        c.chi(sn.clone(), s.clone(), xhalf.clone()),
        c.chi(sn.clone(), t.clone(), xhalf.clone()),
    );
    let chi_pre_s = c.chi(n.clone(), rs.clone(), r_x.clone());
    let chi_pre_t = c.chi(n.clone(), rt.clone(), r_x.clone());
    let pre = c.mul(chi_pre_s.clone(), chi_pre_t.clone());
    let cf_sx = c.factor(b, s_last.clone(), xhalf_last.clone());
    let cf_tx = c.factor(b, t_last.clone(), xhalf_last.clone());
    let cf_pair = c.mul(cf_sx.clone(), cf_tx.clone());
    let peeled = c.mul(pre.clone(), cf_pair.clone());
    let leg_peel = Expr::apps(
        c.sign_peel.clone(),
        [n.clone(), s.clone(), t.clone(), xhalf.clone()],
    );

    // restrict_eq : r_x = hcDecode n j   (restrict lemma).
    let restrict_eq = Expr::apps(restrict_lemma.clone(), [n.clone(), j.clone()]);

    // Rewrite prefix `χ_n(rS)(r_x)·χ_n(rT)(r_x)` → `prefix` in two congr steps.
    let chi_fix_s = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (y_id, y) = d.fresh_local(c.hcpoint_of(n));
        let body = c.chi(n.clone(), rs.clone(), y);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.hcpoint_of(n), body))
    };
    let h_ps = Expr::apps(
        c.congr_arg_hr.clone(),
        [
            c.hcpoint_of(n),
            c.rat.clone(),
            r_x.clone(),
            dec_n_j.clone(),
            chi_fix_s,
            restrict_eq.clone(),
        ],
    );
    let chi_fix_t = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (y_id, y) = d.fresh_local(c.hcpoint_of(n));
        let body = c.chi(n.clone(), rt.clone(), y);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, c.hcpoint_of(n), body))
    };
    let h_pt = Expr::apps(
        c.congr_arg_hr.clone(),
        [
            c.hcpoint_of(n),
            c.rat.clone(),
            r_x.clone(),
            dec_n_j.clone(),
            chi_fix_t,
            restrict_eq.clone(),
        ],
    );
    // h_pre : pre = prefix.
    let mul_right_pre_t = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z, chi_pre_t.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h_pre1 = c.congr_rat(chi_pre_s.clone(), p_s.clone(), mul_right_pre_t, h_ps);
    let mul_left_ps = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(p_s.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h_pre2 = c.congr_rat(chi_pre_t.clone(), p_t.clone(), mul_left_ps, h_pt);
    let pre_mid = c.mul(p_s.clone(), chi_pre_t.clone());
    let h_pre = c.trans_rat(pre.clone(), pre_mid, prefix.clone(), h_pre1, h_pre2);

    // bit : xhalf_last = bit_target   via decode_bit_lemma + testbit_value_lemma.
    let bit_corr = Expr::apps(decode_bit_lemma.clone(), [n.clone(), j.clone(), c.last(n)]);
    let val_islt = Expr::apps(c.fin_islt.clone(), [c.pow2(n), j.clone()]);
    let val_j = c.val(&c.pow2(n), j);
    let bit_value = Expr::apps(testbit_value_lemma.clone(), [n.clone(), val_j, val_islt]);
    let testbit_n = Expr::apps(
        c.testbit.clone(),
        [bit_inner.clone(), c.val(&sn, &c.last(n))],
    );
    let bit = Expr::apps(
        c.eq_trans_bool.clone(),
        [
            c.bool_.clone(),
            xhalf_last.clone(),
            testbit_n,
            bit_target.clone(),
            bit_corr,
            bit_value,
        ],
    );

    // Rewrite the cf pair `cf(S last, xhalf_last)·cf(T last, xhalf_last)`
    //   → `cf(S last, bit)·cf(T last, bit)`  (congr in the SIGN slot via `bit`).
    let cf_s_bit = c.factor(b, s_last.clone(), bit_target.clone());
    let cf_t_bit = c.factor(b, t_last.clone(), bit_target.clone());
    let cf_motive_s = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (xb_id, xb) = d.fresh_local(c.bool_.clone());
        let body = c.factor(&d, s_last.clone(), xb);
        d.finish_child(d.mk_lam(xb_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let h_cfs = Expr::apps(
        c.congr_arg_br.clone(),
        [
            c.bool_.clone(),
            c.rat.clone(),
            xhalf_last.clone(),
            bit_target.clone(),
            cf_motive_s,
            bit.clone(),
        ],
    );
    let cf_motive_t = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (xb_id, xb) = d.fresh_local(c.bool_.clone());
        let body = c.factor(&d, t_last.clone(), xb);
        d.finish_child(d.mk_lam(xb_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let h_cft = Expr::apps(
        c.congr_arg_br.clone(),
        [
            c.bool_.clone(),
            c.rat.clone(),
            xhalf_last.clone(),
            bit_target.clone(),
            cf_motive_t,
            bit,
        ],
    );
    // h_cf : cf_pair = cf(S last, bit)·cf(T last, bit).
    let cf_target = c.mul(cf_s_bit.clone(), cf_t_bit.clone());
    let h_cf = c.bin_congr(
        b,
        &c.rat_mul,
        cf_sx.clone(),
        cf_s_bit.clone(),
        cf_tx.clone(),
        cf_t_bit.clone(),
        h_cfs,
        h_cft,
    );

    // h_body : peeled = prefix · cf_target.
    let target = c.mul(prefix.clone(), cf_target.clone());
    let h_body = c.bin_congr(
        b,
        &c.rat_mul,
        pre.clone(),
        prefix.clone(),
        cf_pair.clone(),
        cf_target.clone(),
        h_pre,
        h_cf,
    );

    // Full: lhs = peeled (chi_sign_pair_succ) then peeled = target (h_body).
    let proof = c.trans_rat(lhs, peeled, target.clone(), leg_peel, h_body);
    (proof, prefix, target)
}

fn build_sign_combine_type(c: &SignBiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let p2n = c.pow2(&n);
    let (j_id, j) = b.fresh_local(c.fin_of(&p2n));

    let xlo = c.decoded(&b, &n, &c.cast_add, &j);
    let xhi = c.decoded(&b, &n, &c.add_nat, &j);
    let lo = c.mul(
        c.chi(sn.clone(), s.clone(), xlo.clone()),
        c.chi(sn.clone(), t.clone(), xlo),
    );
    let hi = c.mul(
        c.chi(sn.clone(), s.clone(), xhi.clone()),
        c.chi(sn.clone(), t.clone(), xhi),
    );
    let lhs = c.add(lo, hi);

    let dec_n_j = Expr::apps(c.hc_decode.clone(), [n.clone(), j.clone()]);
    let rs = c.restrict(&b, &n, &s);
    let rt = c.restrict(&b, &n, &t);
    let prefix = c.mul(
        c.chi(n.clone(), rs, dec_n_j.clone()),
        c.chi(n.clone(), rt, dec_n_j),
    );
    let s_last = Expr::app(s.clone(), c.last(&n));
    let t_last = Expr::app(t.clone(), c.last(&n));
    let c_top = c.add(c.rat_one.clone(), c.mul(c.pm(s_last), c.pm(t_last)));
    let rhs = c.mul(prefix, c_top);

    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(j_id, BinderInfo::Default, c.fin_of(&p2n), concl);
    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), ty);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_sign_combine_value(c: &SignBiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let hcp = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let p2n = c.pow2(&n);
    let (j_id, j) = b.fresh_local(c.fin_of(&p2n));

    let val_j = c.val(&p2n, &j);
    let bit_inner_lo = val_j.clone();
    let bit_inner_hi = c.nadd(p2n.clone(), val_j);

    // LOW: χ_S(xlo)·χ_T(xlo) = prefix · (cf(S last,false)·cf(T last,false)).
    let (h_lo, prefix, target_lo) = build_sign_half_eq(
        c,
        &b,
        &n,
        &s,
        &t,
        &j,
        &c.cast_add,
        &c.restrict_lo,
        &c.decode_lo_bit,
        &c.testbit_lt_pow,
        &c.bfalse,
        &bit_inner_lo,
    );
    // HIGH: χ_S(xhi)·χ_T(xhi) = prefix · (cf(S last,true)·cf(T last,true)).
    let (h_hi, _p2, target_hi) = build_sign_half_eq(
        c,
        &b,
        &n,
        &s,
        &t,
        &j,
        &c.add_nat,
        &c.restrict_hi,
        &c.decode_hi_bit,
        &c.testbit_add_self,
        &c.btrue,
        &bit_inner_hi,
    );

    let xlo = c.decoded(&b, &n, &c.cast_add, &j);
    let xhi = c.decoded(&b, &n, &c.add_nat, &j);
    let lo = c.mul(
        c.chi(sn.clone(), s.clone(), xlo.clone()),
        c.chi(sn.clone(), t.clone(), xlo),
    );
    let hi = c.mul(
        c.chi(sn.clone(), s.clone(), xhi.clone()),
        c.chi(sn.clone(), t.clone(), xhi),
    );
    let lhs = c.add(lo.clone(), hi.clone());

    let s_last = Expr::app(s.clone(), c.last(&n));
    let t_last = Expr::app(t.clone(), c.last(&n));
    // cf pairs (false / true) — the two summands of chi_sign_factor_pair_sum.
    let cf_f = c.mul(
        c.factor(&b, s_last.clone(), c.bfalse.clone()),
        c.factor(&b, t_last.clone(), c.bfalse.clone()),
    );
    let cf_t_ = c.mul(
        c.factor(&b, s_last.clone(), c.btrue.clone()),
        c.factor(&b, t_last.clone(), c.btrue.clone()),
    );

    // step1 : LO + HI = (prefix·cf_f) + (prefix·cf_t).
    let add_right_hi = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.add(z, hi.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s1a = c.congr_rat(lo.clone(), target_lo.clone(), add_right_hi, h_lo);
    let add_left_tlo = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.add(target_lo.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s1b = c.congr_rat(hi.clone(), target_hi.clone(), add_left_tlo, h_hi);
    let add_mid = c.add(target_lo.clone(), hi.clone());
    let add_targets = c.add(target_lo.clone(), target_hi.clone());
    let step1 = c.trans_rat(lhs.clone(), add_mid, add_targets.clone(), s1a, s1b);

    // step2 : (prefix·cf_f)+(prefix·cf_t) = prefix·(cf_f+cf_t)  (Eq.symm left_distrib).
    let distrib = Expr::apps(
        c.left_distrib.clone(),
        [prefix.clone(), cf_f.clone(), cf_t_.clone()],
    );
    let p_sum = c.mul(prefix.clone(), c.add(cf_f.clone(), cf_t_.clone()));
    let step2 = c.symm_rat(p_sum.clone(), add_targets.clone(), distrib);

    // step3 : prefix·(cf_f+cf_t) = prefix·(1 + pm(S last)·pm(T last))
    //   congr (prefix·) (chi_sign_factor_pair_sum S_last T_last).
    let pair_sum = Expr::apps(c.sign_pair_sum.clone(), [s_last.clone(), t_last.clone()]);
    let pair_rhs = c.add(c.rat_one.clone(), c.mul(c.pm(s_last), c.pm(t_last)));
    let mul_left_p = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(prefix.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let cf_sum = c.add(cf_f.clone(), cf_t_.clone());
    let step3 = c.congr_rat(cf_sum, pair_rhs.clone(), mul_left_p, pair_sum);
    let final_rhs = c.mul(prefix.clone(), pair_rhs);

    let t1 = c.trans_rat(lhs.clone(), add_targets, p_sum.clone(), step1, step2);
    let proof = c.trans_rat(lhs, p_sum, final_rhs, t1, step3);

    let val = b.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2n), proof);
    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), val);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.chi_sign_bilinear_pair_combine`: the per-index
    /// LOW+HIGH combine for the SIGN-side split. Kernel-checked, constructive.
    /// Idempotent.
    pub(crate) fn register_chi_sign_bilinear_pair_combine_theorem(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.chi_sign_bilinear_pair_combine");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_chi_sign_pair_succ_theorem()?;
        self.register_chi_sign_factor_pair_sum_theorem()?;
        self.register_hc_decode_split_theorems()?;

        let c = SignBiConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_sign_combine_type(&c),
            value: build_sign_combine_value(&c),
        })
    }
}
