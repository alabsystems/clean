// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_chi_sign_bilinear.rs — the base case
// `subsetSum_chi_sign_bilinear_zero` and the `Nat.rec` induction
// (`build_sign_ind_type` / `build_sign_ind_value`). Split out for the 500-line
// rule. Gates S,T are summed-over indices' fixed gates; the SUM is over x.

impl SignBiConsts {
    /// `fun (x : HCPoint n) => χ_S(x)·χ_T(x)` — the subset-sum integrand.
    fn ss_int(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(
            self.chi(n.clone(), s.clone(), x.clone()),
            self.chi(n.clone(), t.clone(), x),
        );
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (i : Fin n) => 1 + pm(S i)·pm(T i)` — the product integrand.
    fn prod_int(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let pm_s = self.pm(Expr::app(s.clone(), i.clone()));
        let pm_t = self.pm(Expr::app(t.clone(), i.clone()));
        let body = self.add(self.rat_one.clone(), self.mul(pm_s, pm_t));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    fn ss_lhs(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum.clone(),
            [n.clone(), self.ss_int(parent, n, s, t)],
        )
    }
    fn prod_rhs(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        Expr::apps(
            self.fin_prod.clone(),
            [n.clone(), self.prod_int(parent, n, s, t)],
        )
    }
    /// `fun (j : Fin (2^n)) => χ_S(xhalf j)·χ_T(xhalf j)` — a cube SIGN-split half.
    fn half_int(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        s: &Expr,
        t: &Expr,
        idx_map: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let sn = self.succ(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let cp = self.cast_p(&b, n, idx_map, &j);
        let xhalf = Expr::apps(self.hc_decode.clone(), [sn.clone(), cp]);
        let body = self.mul(
            self.chi(sn.clone(), s.clone(), xhalf.clone()),
            self.chi(sn.clone(), t.clone(), xhalf),
        );
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
    /// `fun (j : Fin (2^n)) => χ_{rS}(dec n j)·χ_{rT}(dec n j)` — the prefix
    /// integrand, def-eq to `ss_int n rS rT ∘ hcDecode n` (the summand of
    /// `subsetSum n (ss_int n rS rT)`).
    fn prefix_int(&self, parent: &EnvDeclBuilder, n: &Expr, rs: &Expr, rt: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let dec = Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()]);
        let body = self.mul(
            self.chi(n.clone(), rs.clone(), dec.clone()),
            self.chi(n.clone(), rt.clone(), dec),
        );
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
    /// `fun (j : Fin (2^n)) => c · prefix(j)` — scaled integrand for Fin.sum_smul.
    fn scaled_int(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        rs: &Expr,
        rt: &Expr,
        cc: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (j_id, j) = b.fresh_local(self.fin_of(&p2n));
        let dec = Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()]);
        let pre = self.mul(
            self.chi(n.clone(), rs.clone(), dec.clone()),
            self.chi(n.clone(), rt.clone(), dec),
        );
        let body = self.mul(cc.clone(), pre);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }
}

// ── base case: subsetSum_chi_sign_bilinear_zero ──────────────────────────────

fn build_sign_base_type(c: &SignBiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let hcp = c.hcpoint_of(&zero);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs(&b, &zero, &s, &t);
    let rhs = c.prod_rhs(&b, &zero, &s, &t);
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    b.finish(ty)
}

fn build_sign_base_value(c: &SignBiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let hcp = c.hcpoint_of(&zero);
    let (s_id, _s) = b.fresh_local(hcp.clone());
    let (t_id, _t) = b.fresh_local(hcp.clone());

    // LHS ι-reduces to `Rat.add Rat.zero (Rat.mul Rat.one Rat.one)`; RHS to `1`.
    let one_mul_one = c.mul(c.rat_one.clone(), c.rat_one.clone());
    let zero_add_term = c.add(
        Expr::const_(Name::from_string("Rat.zero"), vec![]),
        one_mul_one.clone(),
    );
    let leg1 = Expr::apps(
        Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
        [one_mul_one.clone()],
    );
    let leg2 = Expr::apps(
        Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
        [c.rat_one.clone()],
    );
    let proof = c.trans_rat(zero_add_term, one_mul_one, c.rat_one.clone(), leg1, leg2);
    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_sign_bilinear_zero`: the `n = 0`
    /// base case. Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_chi_sign_bilinear_zero_theorem(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_sign_bilinear_zero");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?;
        self.register_subset_sum()?;

        let c = SignBiConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_sign_base_type(&c),
            value: build_sign_base_value(&c),
        })
    }
}

// ── Nat.rec induction ────────────────────────────────────────────────────────

fn build_sign_ind_motive(c: &SignBiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&k);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs(&b, &k, &s, &t);
    let rhs = c.prod_rhs(&b, &k, &s, &t);
    let concl = c.eq_rat(lhs, rhs);
    let body = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), concl);
    let body = b.mk_pi(s_id, BinderInfo::Default, hcp, body);
    b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
}

fn build_sign_ind_step(c: &SignBiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&k);

    // ih : ∀ S T : HCPoint k, subsetSum k (ss_int) = Fin.prod k (prod_int)
    let ih_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&k);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let (t_id, t) = d.fresh_local(hcp.clone());
        let lhs = c.ss_lhs(&d, &k, &s, &t);
        let rhs = c.prod_rhs(&d, &k, &s, &t);
        let concl = c.eq_rat(lhs, rhs);
        let tt = d.mk_pi(t_id, BinderInfo::Default, hcp.clone(), concl);
        d.finish_child(d.mk_pi(s_id, BinderInfo::Default, hcp, tt))
    };
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let hcp_sn = c.hcpoint_of(&sn);
    let (s_id, s) = b.fresh_local(hcp_sn.clone());
    let (t_id, t) = b.fresh_local(hcp_sn.clone());

    let p2k = c.pow2(&k);
    let rs = c.restrict(&b, &k, &s);
    let rt = c.restrict(&b, &k, &t);
    // c_top := 1 + pm(S last)·pm(T last)
    let s_last = Expr::app(s.clone(), c.last(&k));
    let t_last = Expr::app(t.clone(), c.last(&k));
    let c_top = c.add(c.rat_one.clone(), c.mul(c.pm(s_last), c.pm(t_last)));

    // Σ LO, Σ HI (subsetSum_split halves).
    let lo_int = c.half_int(&b, &k, &s, &t, &c.cast_add);
    let hi_int = c.half_int(&b, &k, &s, &t, &c.add_nat);
    let sum_lo = c.fsum(p2k.clone(), lo_int.clone());
    let sum_hi = c.fsum(p2k.clone(), hi_int.clone());
    let split_rhs = c.add(sum_lo.clone(), sum_hi.clone());

    // ss_lhs(k+1) := subsetSum (k+1) (ss_int (k+1) S T).
    let ss_lhs_sn = c.ss_lhs(&b, &sn, &s, &t);

    // A : ss_lhs(k+1) = Σ LO + Σ HI   (subsetSum_split k (ss_int (k+1) S T))
    let g_sn = c.ss_int(&b, &sn, &s, &t);
    let leg_a = Expr::apps(c.subset_sum_split.clone(), [k.clone(), g_sn]);

    // pair_int : fun j => LO(j) + HI(j)
    let pair_int = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(&p2k));
        let body = c.add(
            Expr::app(lo_int.clone(), j.clone()),
            Expr::app(hi_int.clone(), j.clone()),
        );
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2k), body))
    };
    let sum_pair = c.fsum(p2k.clone(), pair_int.clone());

    // B : Σ LO + Σ HI = Σ (LO+HI)   (Eq.symm (Fin.sum_add (2^k) lo hi))
    let sum_add_fwd = Expr::apps(
        c.sum_add.clone(),
        [p2k.clone(), lo_int.clone(), hi_int.clone()],
    );
    let leg_b = c.symm_rat(sum_pair.clone(), split_rhs.clone(), sum_add_fwd);

    // scaled_int : fun j => c_top · prefix(j)
    let scaled_int = c.scaled_int(&b, &k, &rs, &rt, &c_top);
    let sum_scaled = c.fsum(p2k.clone(), scaled_int.clone());

    // C : Σ (LO+HI) = Σ (c_top · prefix)   (Fin.sum_congr + per-index combine+comm).
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (j_id, j) = d.fresh_local(c.fin_of(&p2k));
        // combine k S T j : LO(j)+HI(j) = prefix(j) · c_top
        let combine_j = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.chi_sign_bilinear_pair_combine"),
                vec![],
            ),
            [k.clone(), s.clone(), t.clone(), j.clone()],
        );
        let dec = Expr::apps(c.hc_decode.clone(), [k.clone(), j.clone()]);
        let prefix_j = c.mul(
            c.chi(k.clone(), rs.clone(), dec.clone()),
            c.chi(k.clone(), rt.clone(), dec),
        );
        let lo_j = Expr::app(lo_int.clone(), j.clone());
        let hi_j = Expr::app(hi_int.clone(), j.clone());
        let pair_j = c.add(lo_j, hi_j);
        let pref_top = c.mul(prefix_j.clone(), c_top.clone());
        let top_pref = c.mul(c_top.clone(), prefix_j.clone());
        let comm = c.mul_comm(prefix_j.clone(), c_top.clone());
        let proof_j = c.trans_rat(pair_j, pref_top, top_pref, combine_j, comm);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2k), proof_j))
    };
    let leg_c = Expr::apps(
        c.sum_congr.clone(),
        [p2k.clone(), pair_int.clone(), scaled_int.clone(), pointwise],
    );

    // D : Σ (c_top · prefix) = c_top · Σ prefix   (Fin.sum_smul (2^k) c_top prefix_int)
    let prefix_int = c.prefix_int(&b, &k, &rs, &rt);
    let sum_prefix = c.fsum(p2k.clone(), prefix_int.clone());
    let c_sum_prefix = c.mul(c_top.clone(), sum_prefix.clone());
    let leg_d = Expr::apps(
        c.sum_smul.clone(),
        [p2k.clone(), c_top.clone(), prefix_int.clone()],
    );

    // Σ prefix ≡ subsetSum k (ss_int k rS rT) (def-eq); IH gives = Fin.prod k.
    let ss_k = c.ss_lhs(&b, &k, &rs, &rt);
    let prod_k = c.prod_rhs(&b, &k, &rs, &rt);
    // E : c_top · subsetSum k (...) = c_top · Fin.prod k (...)   congr (c_top·) (ih rS rT)
    let ih_st = Expr::apps(ih.clone(), [rs.clone(), rt.clone()]);
    let mul_left_ctop = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(c_top.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let c_prod_k = c.mul(c_top.clone(), prod_k.clone());
    let leg_e = c.congr_rat(ss_k.clone(), prod_k.clone(), mul_left_ctop, ih_st);

    // F : c_top · Fin.prod k = Fin.prod k · c_top   (mul_comm)
    let prod_c = c.mul(prod_k.clone(), c_top.clone());
    let leg_f = c.mul_comm(c_top.clone(), prod_k.clone());

    // G : Fin.prod k (prod rS rT) · c_top = Fin.prod (k+1) (prod (k+1) S T)
    //     Eq.symm (Fin.prod_succ k (prod_int (k+1) S T)).
    let prod_int_sn = c.prod_int(&b, &sn, &s, &t);
    let prod_succ_fwd = Expr::apps(c.prod_succ.clone(), [k.clone(), prod_int_sn]);
    let prod_rhs_sn = c.prod_rhs(&b, &sn, &s, &t);
    let leg_g = c.symm_rat(prod_rhs_sn.clone(), prod_c.clone(), prod_succ_fwd);

    // Chain.
    let t1 = c.trans_rat(
        ss_lhs_sn.clone(),
        split_rhs.clone(),
        sum_pair.clone(),
        leg_a,
        leg_b,
    );
    let t2 = c.trans_rat(ss_lhs_sn.clone(), sum_pair, sum_scaled.clone(), t1, leg_c);
    let t3 = c.trans_rat(
        ss_lhs_sn.clone(),
        sum_scaled,
        c_sum_prefix.clone(),
        t2,
        leg_d,
    );
    let t4 = c.trans_rat(ss_lhs_sn.clone(), c_sum_prefix, c_prod_k.clone(), t3, leg_e);
    let t5 = c.trans_rat(ss_lhs_sn.clone(), c_prod_k, prod_c.clone(), t4, leg_f);
    let proof = c.trans_rat(ss_lhs_sn, prod_c, prod_rhs_sn, t5, leg_g);

    let val = b.mk_lam(t_id, BinderInfo::Default, hcp_sn.clone(), proof);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp_sn, val);
    let val = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, val);
    let val = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

fn build_sign_ind_type(c: &SignBiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());
    let lhs = c.ss_lhs(&b, &n, &s, &t);
    let rhs = c.prod_rhs(&b, &n, &s, &t);
    let concl = c.eq_rat(lhs, rhs);
    let ty = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), concl);
    let ty = b.mk_pi(s_id, BinderInfo::Default, hcp, ty);
    let ty = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ty);
    b.finish(ty)
}

fn build_sign_ind_value(c: &SignBiConsts) -> Expr {
    let motive = build_sign_ind_motive(c);
    let base = c.base_zero.clone();
    let step = build_sign_ind_step(c);
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let body = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
}
