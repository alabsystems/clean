// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_influence_chain.rs — Leg 7, the normalization
// that lifts the un-normalized bridge (Leg 6) to the registered helper form
//   Influence n f i = subsetSum n (fun S => ind(S i)·f̂(S)²).
// Both `Influence` (= Σ.../2^n) and `f̂` (= A_S/2^n) are reducible, so this is
// the `Expect = subsetSum/2^n` + `f̂ = A_S/2^n` division bookkeeping.

impl InflConsts {
    /// helper-RHS `S`-integrand `fun S => ind(S i)·(f̂(S)·f̂(S))` (the registered
    /// form, with `f̂ = FourierCoefficient`).
    fn helper_rhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let fc = self.fcoeff(n, f, &s);
        let body = self.mul(
            self.ind_(Expr::app(s.clone(), i.clone())),
            self.mul(fc.clone(), fc),
        );
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => (P⁻¹·P⁻¹)·(ind(S i)·(A_S·A_S))` — helper RHS after pulling P⁻².
    fn pinv2_ind_amp_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let pinv = self.inv(self.cube(n));
        let pinv2 = self.mul(pinv.clone(), pinv.clone());
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let k = self.amp(&sb, n, b, &s);
        let is_ = self.ind_(Expr::app(s.clone(), i.clone()));
        let body = self.mul(pinv2.clone(), self.mul(is_, self.mul(k.clone(), k)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// Per-S identity: `ind·(f̂·f̂) = (P⁻¹·P⁻¹)·(ind·(A·A))`.
    /// (`f̂ ≡ A·P⁻¹` def-eq; `(A·P⁻¹)·(A·P⁻¹) = (A·A)·(P⁻¹·P⁻¹)` mmmc; then
    /// `ind·((A·A)·(P⁻¹·P⁻¹)) = (P⁻¹·P⁻¹)·(ind·(A·A))` via assoc+comm.)
    fn per_s_norm(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, s: &Expr, i: &Expr) -> Expr {
        let pinv = self.inv(self.cube(n));
        let pinv2 = self.mul(pinv.clone(), pinv.clone());
        let pmf = self.pm_f(parent, n, f);
        let a = self.amp(parent, n, &pmf, s);
        let fc = self.fcoeff(n, f, s); // ≡ a·P⁻¹ def-eq
        let is_ = self.ind_(Expr::app(s.clone(), i.clone()));
        let aa = self.mul(a.clone(), a.clone());

        // l0 := ind·(f̂·f̂)  (the goal LHS, with f̂).
        let fc_fc = self.mul(fc.clone(), fc.clone());
        let l0 = self.mul(is_.clone(), fc_fc.clone());

        // step_fc : (f̂·f̂) = (A·A)·(P⁻¹·P⁻¹)   mmmc A P⁻¹ A P⁻¹ (def-eq f̂ = A·P⁻¹).
        //   Built at A·P⁻¹ form; typed against f̂·f̂ (def-eq).
        let aa_pp = self.mul(aa.clone(), pinv2.clone());
        let step_fc = self.mmmc(a.clone(), pinv.clone(), a.clone(), pinv.clone());
        // lift to ind: ind·(f̂·f̂) = ind·((A·A)·(P⁻¹·P⁻¹))   congrArg(ind·) step_fc.
        let l1 = self.mul(is_.clone(), aa_pp.clone());
        let leg1 = self.mul_left_congr(parent, &is_, fc_fc.clone(), aa_pp.clone(), step_fc);

        // leg2 : ind·((A·A)·(P⁻¹·P⁻¹)) = (ind·(A·A))·(P⁻¹·P⁻¹)   symm (assoc ind (A·A) (P⁻¹·P⁻¹)).
        let ind_aa = self.mul(is_.clone(), aa.clone());
        let l2 = self.mul(ind_aa.clone(), pinv2.clone());
        let leg2 = self.symm(
            l2.clone(),
            l1.clone(),
            self.assoc(is_.clone(), aa.clone(), pinv2.clone()),
        );
        // leg3 : (ind·(A·A))·(P⁻¹·P⁻¹) = (P⁻¹·P⁻¹)·(ind·(A·A))   mul_comm.
        let l3 = self.mul(pinv2.clone(), ind_aa.clone());
        let leg3 = self.mul_comm_e(ind_aa.clone(), pinv2.clone());

        // chain: l0 = l1 = l2 = l3.
        let t1 = self.trans(l0.clone(), l1.clone(), l2.clone(), leg1, leg2);
        self.trans(l0, l2, l3, t1, leg3)
    }
}

fn influence_fourier_value(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let p = c.cube(&n);
    let pinv = c.inv(p.clone());
    let pinv2 = c.mul(pinv.clone(), pinv.clone());
    let pmf = c.pm_f(&b, &n, &f);

    // D := subsetSum(ind∘disagree)  (Influence ≡ D·P⁻¹) ;
    // R := subsetSum(ind·A²) ;  helper RHS := subsetSum(ind·f̂²).
    let dd = c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i));
    let r_un = c.ssum(&n, c.ind_amp_sq_fn(&b, &n, &pmf, &i));
    let helper_rhs = c.ssum(&n, c.helper_rhs_fn(&b, &n, &f, &i));
    let d_pinv = c.mul(dd.clone(), pinv.clone()); // ≡ Influence n f i
    let pinv2_r = c.mul(pinv2.clone(), r_un.clone());

    // ── div_bridge : D·P⁻¹ = P⁻²·R ───────────────────────────────────────
    // From Leg 6: P·D = R.  P⁻²·R = P⁻²·(P·D) and rearrange to D·P⁻¹.
    let unnorm = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_influence_unnorm"),
            vec![],
        ),
        [n.clone(), f.clone(), i.clone()],
    ); // P·D = R
    let p_d = c.mul(p.clone(), dd.clone());
    // chain D·P⁻¹ = P⁻¹·D = (P⁻¹·1)·D ... build forward toward P⁻²·R.
    //   a1 : D·P⁻¹ = P⁻¹·D                 mul_comm D P⁻¹.
    let pinv_d = c.mul(pinv.clone(), dd.clone());
    let a1 = c.mul_comm_e(dd.clone(), pinv.clone());
    //   a2 : P⁻¹·D = P⁻¹·(1·D)             congrArg(P⁻¹·) (symm (one_mul D)).
    let one_d = c.mul(c.rat_one.clone(), dd.clone());
    let pinv_one_d = c.mul(pinv.clone(), one_d.clone());
    let a2 = c.mul_left_congr(
        &b,
        &pinv,
        dd.clone(),
        one_d.clone(),
        c.symm(one_d.clone(), dd.clone(), c.one_mul(dd.clone())),
    );
    //   pinv_p : 1 = P⁻¹·P  (symm of P⁻¹·P=1).
    //   P⁻¹·P = 1 := trans (symm (mul_comm P P⁻¹)) (mul_inv_cancel P).
    let p_pinv = c.mul(p.clone(), pinv.clone());
    let pinv_p = c.mul(pinv.clone(), p.clone());
    let mic = c.mul_inv_cancel(p.clone(), c.p_ne_zero(&n)); // P·P⁻¹ = 1
    let cm = c.mul_comm_e(p.clone(), pinv.clone()); // P·P⁻¹ = P⁻¹·P
    let pinvp_eq_one = c.trans(
        pinv_p.clone(),
        p_pinv.clone(),
        c.rat_one.clone(),
        c.symm(p_pinv.clone(), pinv_p.clone(), cm),
        mic,
    );
    //   a3 : P⁻¹·(1·D) = P⁻¹·((P⁻¹·P)·D)   congrArg(P⁻¹·) (congrArg(·D) (symm pinvp_eq_one)).
    let pinvp_d = c.mul(pinv_p.clone(), dd.clone());
    let inner_a3 = c.mul_right_congr(
        &b,
        &dd,
        c.rat_one.clone(),
        pinv_p.clone(),
        c.symm(pinv_p.clone(), c.rat_one.clone(), pinvp_eq_one),
    );
    let pinv_pinvp_d = c.mul(pinv.clone(), pinvp_d.clone());
    let a3 = c.mul_left_congr(&b, &pinv, one_d.clone(), pinvp_d.clone(), inner_a3);
    //   a4 : P⁻¹·((P⁻¹·P)·D) = P⁻¹·(P⁻¹·(P·D))   congrArg(P⁻¹·) (mul_assoc P⁻¹ P D).
    let pinv_pd = c.mul(pinv.clone(), p_d.clone());
    let pinv_pinv_pd = c.mul(pinv.clone(), pinv_pd.clone());
    let a4 = c.mul_left_congr(
        &b,
        &pinv,
        pinvp_d.clone(),
        pinv_pd.clone(),
        c.assoc(pinv.clone(), p.clone(), dd.clone()),
    );
    //   a5 : P⁻¹·(P⁻¹·(P·D)) = (P⁻¹·P⁻¹)·(P·D)   symm (mul_assoc P⁻¹ P⁻¹ (P·D)).
    let pinv2_pd = c.mul(pinv2.clone(), p_d.clone());
    let a5 = c.symm(
        pinv2_pd.clone(),
        pinv_pinv_pd.clone(),
        c.assoc(pinv.clone(), pinv.clone(), p_d.clone()),
    );
    //   a6 : (P⁻¹·P⁻¹)·(P·D) = (P⁻¹·P⁻¹)·R   congrArg((P⁻¹·P⁻¹)·) unnorm.
    let a6 = c.mul_left_congr(&b, &pinv2, p_d.clone(), r_un.clone(), unnorm);

    // chain div_bridge: D·P⁻¹ = P⁻¹·D = P⁻¹·(1·D) = P⁻¹·((P⁻¹·P)·D)
    //   = P⁻¹·(P⁻¹·(P·D)) = (P⁻¹·P⁻¹)·(P·D) = (P⁻¹·P⁻¹)·R.
    let b1 = c.trans(d_pinv.clone(), pinv_d.clone(), pinv_one_d.clone(), a1, a2);
    let b2 = c.trans(
        d_pinv.clone(),
        pinv_one_d.clone(),
        pinv_pinvp_d.clone(),
        b1,
        a3,
    );
    let b3 = c.trans(
        d_pinv.clone(),
        pinv_pinvp_d.clone(),
        pinv_pinv_pd.clone(),
        b2,
        a4,
    );
    let b4 = c.trans(
        d_pinv.clone(),
        pinv_pinv_pd.clone(),
        pinv2_pd.clone(),
        b3,
        a5,
    );
    let div_bridge = c.trans(d_pinv.clone(), pinv2_pd.clone(), pinv2_r.clone(), b4, a6);

    // ── helper_eq : P⁻²·R = subsetSum(ind·f̂²) ────────────────────────────
    // per-S: ind·f̂² = P⁻²·(ind·A²) ; subsetSum_congr ; subsetSum_smul (reversed).
    let h = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pf = c.per_s_norm(&sb, &n, &f, &s, &i);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, pf))
    };
    // congr : subsetSum(ind·f̂²) = subsetSum(P⁻²·(ind·A²)).
    let congr = Expr::apps(
        c.subset_sum_congr.clone(),
        [
            n.clone(),
            c.helper_rhs_fn(&b, &n, &f, &i),
            c.pinv2_ind_amp_sq_fn(&b, &n, &pmf, &i),
            h,
        ],
    );
    // smul : subsetSum(P⁻²·(ind·A²)) = P⁻²·subsetSum(ind·A²) = P⁻²·R.
    let smul = c.smul(&n, pinv2.clone(), c.ind_amp_sq_fn(&b, &n, &pmf, &i));
    let ss_pinv2 = c.ssum(&n, c.pinv2_ind_amp_sq_fn(&b, &n, &pmf, &i));
    // helper_to_pinv2r : subsetSum(ind·f̂²) = P⁻²·R.
    let helper_to_pinv2r = c.trans(
        helper_rhs.clone(),
        ss_pinv2.clone(),
        pinv2_r.clone(),
        congr,
        smul,
    );
    // helper_eq : P⁻²·R = subsetSum(ind·f̂²)   := symm.
    let helper_eq = c.symm(helper_rhs.clone(), pinv2_r.clone(), helper_to_pinv2r);

    // proof : D·P⁻¹ = subsetSum(ind·f̂²)   (≡ Influence n f i = helper RHS).
    let proof = c.trans(
        d_pinv.clone(),
        pinv2_r.clone(),
        helper_rhs.clone(),
        div_bridge,
        helper_eq,
    );

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

/// Type `∀ n f i, @Eq Rat (Influence n f i) (subsetSum n (fun S => ind(S i)·f̂(S)²))`
/// — the registered `influence_fourier` statement (def-eq to
/// `∀ n f i, influence_fourier_helper n f i`).
#[cfg(test)]
fn influence_fourier_type(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let lhs = c.influence_(&n, &f, &i);
    let rhs = c.ssum(&n, c.helper_rhs_fn(&b, &n, &f, &i));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// The constructive proof term for `influence_fourier`
    /// (`Influence n f i = subsetSum n (fun S => ind(S i)·f̂(S)²)`, def-eq to
    /// `∀ n f i, influence_fourier_helper n f i`). Used by
    /// `register_influence_fourier` to install the CHECKED Theorem.
    pub(crate) fn influence_fourier_proof_value(&self) -> Expr {
        influence_fourier_value(&InflConsts::new())
    }
}

#[cfg(test)]
mod influence_final_tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_influence_fourier_value_constructive() {
        // Standalone sanity: the proof term checks against the explicit
        // `Influence = Σ ind·f̂²` type, with empty admitted-axiom closure.
        let mut env = Environment::with_prelude();
        env.register_subset_sum_influence_unnorm().expect("prereqs");
        env.register_subset_sum_smul_theorem().expect("smul");
        let c = InflConsts::new();
        let ty = influence_fourier_type(&c);
        let val = influence_fourier_value(&c);
        {
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(&val, &ty)
                .expect("influence_fourier proof term must check against its type");
        }
        // Closure check via a temporary registration.
        let name = Name::from_string("BoolAnalysis.influence_fourier_probe");
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value: val,
        })
        .expect("probe registers");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "influence_fourier closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
