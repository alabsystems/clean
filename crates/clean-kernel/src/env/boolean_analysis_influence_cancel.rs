// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_influence_chain.rs — the multiplicative
// cancellation helper and Leg 6, the un-normalized bridge
//   2^n · subsetSum n (ind∘disagree) = subsetSum n (fun S => ind(S i)·A_S²),
// obtained by cancelling the common nonzero factor (2^n · 4) from the combined
// master / disagree / coefficient identities.

impl InflConsts {
    /// Proof term for `x = y` from `hne : a = 0 → False` and `h : a·x = a·y`.
    /// (Left multiplicative cancellation via `a⁻¹`.)
    ///   x = 1·x = (a⁻¹·a)·x = a⁻¹·(a·x) = a⁻¹·(a·y) = (a⁻¹·a)·y = 1·y = y.
    fn cancel_left(
        &self,
        parent: &EnvDeclBuilder,
        a: Expr,
        x: Expr,
        y: Expr,
        hne: Expr,
        h: Expr,
    ) -> Expr {
        let ai = self.inv(a.clone());
        let one = self.rat_one.clone();
        // ha : a⁻¹·a = 1.
        //   mic : a·a⁻¹ = 1 ; cm : a·a⁻¹ = a⁻¹·a ; ha := trans (symm cm) mic.
        let mic = self.mul_inv_cancel(a.clone(), hne);
        let a_ai = self.mul(a.clone(), ai.clone());
        let ai_a = self.mul(ai.clone(), a.clone());
        let cm = self.mul_comm_e(a.clone(), ai.clone()); // a·a⁻¹ = a⁻¹·a
        let cm_sym = self.symm(a_ai.clone(), ai_a.clone(), cm); // a⁻¹·a = a·a⁻¹
        let ha = self.trans(ai_a.clone(), a_ai.clone(), one.clone(), cm_sym, mic); // a⁻¹·a = 1

        let ax = self.mul(a.clone(), x.clone());
        let ay = self.mul(a.clone(), y.clone());
        let one_x = self.mul(one.clone(), x.clone());
        let one_y = self.mul(one.clone(), y.clone());
        let aia_x = self.mul(ai_a.clone(), x.clone());
        let aia_y = self.mul(ai_a.clone(), y.clone());
        let ai_ax = self.mul(ai.clone(), ax.clone());
        let ai_ay = self.mul(ai.clone(), ay.clone());

        // p1 : x = 1·x        symm (one_mul x).
        let p1 = self.symm(one_x.clone(), x.clone(), self.one_mul(x.clone()));
        // p2 : 1·x = (a⁻¹·a)·x   congrArg(·x) (symm ha).
        let ha_sym = self.symm(ai_a.clone(), one.clone(), ha.clone()); // 1 = a⁻¹·a
        let p2 = self.mul_right_congr(parent, &x, one.clone(), ai_a.clone(), ha_sym.clone());
        // p3 : (a⁻¹·a)·x = a⁻¹·(a·x)   mul_assoc a⁻¹ a x.
        let p3 = self.assoc(ai.clone(), a.clone(), x.clone());
        // p4 : a⁻¹·(a·x) = a⁻¹·(a·y)   congrArg(a⁻¹·) h.
        let p4 = self.mul_left_congr(parent, &ai, ax.clone(), ay.clone(), h);
        // p5 : a⁻¹·(a·y) = (a⁻¹·a)·y   symm (mul_assoc a⁻¹ a y).
        let p5 = self.symm(
            aia_y.clone(),
            ai_ay.clone(),
            self.assoc(ai.clone(), a.clone(), y.clone()),
        );
        // p6 : (a⁻¹·a)·y = 1·y   congrArg(·y) ha.
        let p6 = self.mul_right_congr(parent, &y, ai_a.clone(), one.clone(), ha.clone());
        // p7 : 1·y = y   one_mul y.
        let p7 = self.one_mul(y.clone());

        // chain x = 1·x = (a⁻¹·a)·x = a⁻¹·(a·x) = a⁻¹·(a·y) = (a⁻¹·a)·y = 1·y = y.
        let t1 = self.trans(x.clone(), one_x.clone(), aia_x.clone(), p1, p2);
        let t2 = self.trans(x.clone(), aia_x.clone(), ai_ax.clone(), t1, p3);
        let t3 = self.trans(x.clone(), ai_ax.clone(), ai_ay.clone(), t2, p4);
        let t4 = self.trans(x.clone(), ai_ay.clone(), aia_y.clone(), t3, p5);
        let t5 = self.trans(x.clone(), aia_y.clone(), one_y.clone(), t4, p6);
        self.trans(x, one_y, y, t5, p7)
    }

    /// `P ≠ 0` proof: `natCast_ne_zero_of_pos (2^n) (one_le_two_pow n)`.
    fn p_ne_zero(&self, n: &Expr) -> Expr {
        let one_le = Expr::app(self.one_le_two_pow.clone(), n.clone());
        Expr::apps(self.natcast_ne_zero.clone(), [self.pow2(n), one_le])
    }
    /// `4 ≠ 0` proof: `natCast_ne_zero_of_pos 4 (1 ≤ 4)`.
    fn four_ne_zero(&self) -> Expr {
        let one = self.one_nat();
        let two = self.two_nat();
        let three = Expr::app(self.nat_succ.clone(), two.clone());
        let four = Expr::app(self.nat_succ.clone(), three.clone());
        // 1 ≤ 4 via Nat.le.refl 1 + three steps.
        let r1 = Expr::app(self.nat_le_refl.clone(), one.clone());
        let s2 = Expr::apps(self.nat_le_step.clone(), [one.clone(), one.clone(), r1]);
        let s3 = Expr::apps(self.nat_le_step.clone(), [one.clone(), two.clone(), s2]);
        let s4 = Expr::apps(self.nat_le_step.clone(), [one.clone(), three.clone(), s3]);
        Expr::apps(self.natcast_ne_zero.clone(), [four, s4])
    }
}

// ════════════ Leg 6: un-normalized bridge (P·D = R_un) ════════════

fn influence_unnorm_type(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let pmf = c.pm_f(&b, &n, &f);
    let dd = c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i)); // D
    let lhs = c.mul(c.cube(&n), dd);
    let rhs = c.ssum(&n, c.ind_amp_sq_fn(&b, &n, &pmf, &i)); // R_un
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn influence_unnorm_value(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let p = c.cube(&n);
    let four = c.rat_four();
    let pmf = c.pm_f(&b, &n, &f);

    // D := subsetSum(ind∘disagree) ; R := subsetSum(ind·A²).
    let dd = c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i));
    let r_un = c.ssum(&n, c.ind_amp_sq_fn(&b, &n, &pmf, &i));

    // K := (P·P)·4 (= disagree_const) ; sq_lhs := subsetSum((P·diff)²) ;
    // mid := P·subsetSum(a_fn²).
    let kk = c.disagree_const(&n); // (P·P)·4
    let sq_lhs = c.ssum(&n, c.disagree_lhs_fn(&b, &n, &f, &i));
    let a_sq = c.ssum(&n, c.a_sq_fn(&b, &n, &pmf, &i));
    let mid = c.mul(p.clone(), a_sq.clone());
    let p4 = c.mul(p.clone(), four.clone());
    let k_d = c.mul(kk.clone(), dd.clone());
    let p4_r = c.mul(p4.clone(), r_un.clone());

    // disagree_side n f i : sq_lhs = K·D.
    let dis = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_disagree_side"),
            vec![],
        ),
        [n.clone(), f.clone(), i.clone()],
    );
    // master n pmf i : sq_lhs = P·subsetSum(a_fn²).
    let master = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_influence_master"),
            vec![],
        ),
        [n.clone(), pmf.clone(), i.clone()],
    );
    // coeff_side n pmf i : P·subsetSum(a_fn²) = (P·4)·R.
    let coeff = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_coeff_side"),
            vec![],
        ),
        [n.clone(), pmf.clone(), i.clone()],
    );

    // combined : K·D = (P·4)·R.
    //   dis_sym : K·D = sq_lhs ; trans with master, coeff.
    let dis_sym = c.symm(sq_lhs.clone(), k_d.clone(), dis);
    let comb1 = c.trans(k_d.clone(), sq_lhs.clone(), mid.clone(), dis_sym, master);
    let combined = c.trans(k_d.clone(), mid.clone(), p4_r.clone(), comb1, coeff);

    // Rearrange K·D = ((P·P)·4)·D into P·((P·4)·D):
    //   r1 : (P·P)·4 = P·(P·4)            mul_assoc P P 4.
    //   r2 : ((P·P)·4)·D = (P·(P·4))·D    congrArg(·D) r1.
    //   r3 : (P·(P·4))·D = P·((P·4)·D)    mul_assoc P (P·4) D.
    let pp = c.mul(p.clone(), p.clone());
    let p_p4 = c.mul(p.clone(), p4.clone());
    let r1 = c.assoc(p.clone(), p.clone(), four.clone()); // (P·P)·4 = P·(P·4)
    let r2 = c.mul_right_congr(&b, &dd, kk.clone(), p_p4.clone(), r1); // ((P·P)·4)·D = (P·(P·4))·D
    let p_p4_d = c.mul(p_p4.clone(), dd.clone());
    let p4_d = c.mul(p4.clone(), dd.clone());
    let p_lhs = c.mul(p.clone(), p4_d.clone());
    let r3 = c.assoc(p.clone(), p4.clone(), dd.clone()); // (P·(P·4))·D = P·((P·4)·D)
                                                         // k_d_eq : K·D = P·((P·4)·D).
    let k_d_eq = c.trans(k_d.clone(), p_p4_d.clone(), p_lhs.clone(), r2, r3);

    // Rearrange (P·4)·R = P·(4·R):
    //   q1 : (P·4)·R = P·(4·R)   mul_assoc P 4 R.
    let four_r = c.mul(four.clone(), r_un.clone());
    let p_4r = c.mul(p.clone(), four_r.clone());
    let q1 = c.assoc(p.clone(), four.clone(), r_un.clone()); // (P·4)·R = P·(4·R)

    // From combined: P·((P·4)·D) = P·(4·R).
    //   step : symm k_d_eq ∘ combined ∘ q1.
    let comb_a = c.trans(
        p_lhs.clone(),
        k_d.clone(),
        p4_r.clone(),
        c.symm(k_d.clone(), p_lhs.clone(), k_d_eq),
        combined,
    );
    let eq_p = c.trans(p_lhs.clone(), p4_r.clone(), p_4r.clone(), comb_a, q1);
    // cancel P : (P·4)·D = 4·R.
    let cancel_p = c.cancel_left(
        &b,
        p.clone(),
        p4_d.clone(),
        four_r.clone(),
        c.p_ne_zero(&n),
        eq_p,
    );

    // Rearrange (P·4)·D = 4·(P·D):
    //   s1 : (P·4)·D = (4·P)·D   congrArg(·D) (mul_comm P 4).
    //   s2 : (4·P)·D = 4·(P·D)   mul_assoc 4 P D.
    let four_p = c.mul(four.clone(), p.clone());
    let s1 = c.mul_right_congr(
        &b,
        &dd,
        p4.clone(),
        four_p.clone(),
        c.mul_comm_e(p.clone(), four.clone()),
    );
    let p_d = c.mul(p.clone(), dd.clone());
    let four_pd = c.mul(four.clone(), p_d.clone());
    let four_p_d = c.mul(four_p.clone(), dd.clone());
    let s2 = c.assoc(four.clone(), p.clone(), dd.clone()); // (4·P)·D = 4·(P·D)
    let p4_d_eq = c.trans(p4_d.clone(), four_p_d.clone(), four_pd.clone(), s1, s2);
    // eq_four : 4·(P·D) = 4·R   := symm p4_d_eq ∘ cancel_p.
    let eq_four = c.trans(
        four_pd.clone(),
        p4_d.clone(),
        four_r.clone(),
        c.symm(p4_d.clone(), four_pd.clone(), p4_d_eq),
        cancel_p,
    );
    // cancel 4 : P·D = R.
    let proof = c.cancel_left(
        &b,
        four.clone(),
        p_d.clone(),
        r_un.clone(),
        c.four_ne_zero(),
        eq_four,
    );

    // Note: `pp` is built for documentation parity with disagree_const; silence unused.
    let _ = pp;

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_influence_unnorm` — the un-normalized
    /// influence bridge:
    ///   2^n · subsetSum n (fun x => ind(disagree x))
    ///     = subsetSum n (fun S => ind(S i)·A_S²),
    /// where `disagree x = Bool.not (Bool.beq (f x) (f(hcFlip n x i)))`,
    /// `A_S = subsetSum n (fun y => pm(f y)·χ_S(y))`. Combines the master x-side
    /// identity (Leg 4) with the disagree-side (Leg 5a) and coefficient-side
    /// (Leg 5b) normalizations, then cancels the common nonzero factor `2^n·4`.
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_influence_unnorm(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_influence_unnorm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_influence_master()?;
        self.register_subset_sum_disagree_side()?;
        self.register_subset_sum_coeff_side()?;
        self.register_expect_one_theorems()?; // natCast_ne_zero_of_pos, one_le_two_pow
        self.init_rat()?; // Rat.inv, Rat.mul_inv_cancel, Rat.one_mul
        self.init_rat_field_inst()?; // Rat.mul_assoc/comm
        self.init_le()?; // Nat.le.refl/step

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: influence_unnorm_type(&c),
            value: influence_unnorm_value(&c),
        })
    }
}

#[cfg(test)]
mod influence_cancel_tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_influence_unnorm_constructive() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_influence_unnorm()
            .expect("register influence_unnorm");
        env.register_subset_sum_influence_unnorm()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.subsetSum_influence_unnorm");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(name.clone(), vec![]))
            .expect("influence_unnorm should type-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "influence_unnorm closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
