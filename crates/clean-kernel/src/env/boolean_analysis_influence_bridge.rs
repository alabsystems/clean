// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_influence_chain.rs — the un-normalized bridge
// legs that convert the master x-side identity (Leg 4) into the relation
//   2^n · subsetSum n (ind∘disagree) = subsetSum n (fun S => ind(S i)·A_S²),
// the un-normalized core of `influence_fourier`. Built from disagree_sq_bridge,
// ind_mul_self, mmmc, mul_assoc and subsetSum_smul.

// ════════════ Leg 5a: disagree side ════════════
//
//   subsetSum n (fun x => (2^n·(pm(f x) − pm(f(hcFlip n x i))))²)
//     = ((2^n·2^n)·4) · subsetSum n (fun x => ind(disagree x)).
//
// Per-x integrand identity (under subsetSum_congr):
//   (P·diff)² = ((P·P)·4)·ind(disagree x),
// where diff = pm(f x) − pm(f(hcFlip n x i)), via mmmc + disagree_sq_bridge
// (diff² = 4·ind) + mul_assoc; then subsetSum_smul pulls the constant out.

impl InflConsts {
    /// `fun x => (2^n·(pm(f x) − pm(f(hcFlip n x i))))²` over the sign point.
    fn disagree_lhs_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let pmf = self.pm_f(parent, n, f);
        self.diff_sq_x_fn(parent, n, &pmf, i)
    }
    /// `fun x => ind(disagree x)` over the sign point.
    fn ind_disagree_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.ind_(self.disagree(n, f, &x, i));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => K·ind(disagree x)` where `K = (2^n·2^n)·4`.
    fn k_ind_disagree_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let kk = self.disagree_const(n);
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.mul(kk.clone(), self.ind_(self.disagree(n, f, &x, i)));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `K := (2^n·2^n)·4`.
    fn disagree_const(&self, n: &Expr) -> Expr {
        self.mul(self.mul(self.cube(n), self.cube(n)), self.rat_four())
    }

    /// Per-x integrand identity: `(P·diff)² = ((P·P)·4)·ind(disagree x)`.
    fn per_x_disagree(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        x: &Expr,
        i: &Expr,
    ) -> Expr {
        let p = self.cube(n);
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.hc_flip_(n, x, i));
        let diff = self.sub(self.pm_(fx.clone()), self.pm_(fflip.clone()));
        let pdiff = self.mul(p.clone(), diff.clone());
        let id = self.ind_(self.disagree(n, f, x, i));

        // s0 := (P·diff)·(P·diff).
        let s0 = self.mul(pdiff.clone(), pdiff.clone());
        // step1 : (P·diff)·(P·diff) = (P·P)·(diff·diff)   mmmc P diff P diff.
        let step1 = self.mmmc(p.clone(), diff.clone(), p.clone(), diff.clone());
        let pp = self.mul(p.clone(), p.clone());
        let diff_diff = self.mul(diff.clone(), diff.clone());
        let s1 = self.mul(pp.clone(), diff_diff.clone());
        // bridge : 4·ind(disagree) = diff·diff   (disagree_sq_bridge (f x)(f flip)).
        let bridge = self.disagree_bridge(fx.clone(), fflip.clone());
        let four_id = self.mul(self.rat_four(), id.clone());
        // bridge_sym : diff·diff = 4·ind(disagree).
        let bridge_sym = self.symm(four_id.clone(), diff_diff.clone(), bridge);
        // step2 : (P·P)·(diff·diff) = (P·P)·(4·ind)   congrArg((P·P)·) bridge_sym.
        let step2 =
            self.mul_left_congr(parent, &pp, diff_diff.clone(), four_id.clone(), bridge_sym);
        let s2 = self.mul(pp.clone(), four_id.clone());
        // step3 : (P·P)·(4·ind) = ((P·P)·4)·ind   symm (mul_assoc (P·P) 4 ind).
        let assoc = Expr::apps(
            self.rat_mul_assoc.clone(),
            [pp.clone(), self.rat_four(), id.clone()],
        );
        let pp4 = self.mul(pp.clone(), self.rat_four());
        let s3 = self.mul(pp4.clone(), id.clone());
        let step3 = self.symm(s3.clone(), s2.clone(), assoc);

        // chain: s0 = s1 = s2 = s3.
        let t1 = self.trans(s0.clone(), s1.clone(), s2.clone(), step1, step2);
        self.trans(s0, s2, s3, t1, step3)
    }
}

fn disagree_side_type(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.ssum(&n, c.disagree_lhs_fn(&b, &n, &f, &i));
    let rhs = c.mul(
        c.disagree_const(&n),
        c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i)),
    );
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn disagree_side_value(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    // leg1 : Σ_x (P·diff)² = Σ_x K·ind(disagree x)   (subsetSum_congr + per_x).
    let h = {
        let mut xb = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let pf = c.per_x_disagree(&xb, &n, &f, &x, &i);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, pf))
    };
    let leg1 = Expr::apps(
        c.subset_sum_congr.clone(),
        [
            n.clone(),
            c.disagree_lhs_fn(&b, &n, &f, &i),
            c.k_ind_disagree_fn(&b, &n, &f, &i),
            h,
        ],
    );
    // leg2 : Σ_x K·ind(disagree x) = K·Σ_x ind(disagree x)   (subsetSum_smul).
    let leg2 = c.smul(&n, c.disagree_const(&n), c.ind_disagree_fn(&b, &n, &f, &i));

    let e0 = c.ssum(&n, c.disagree_lhs_fn(&b, &n, &f, &i));
    let e1 = c.ssum(&n, c.k_ind_disagree_fn(&b, &n, &f, &i));
    let rhs = c.mul(
        c.disagree_const(&n),
        c.ssum(&n, c.ind_disagree_fn(&b, &n, &f, &i)),
    );
    let proof = c.trans(e0, e1, rhs, leg1, leg2);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_disagree_side` —
    ///   subsetSum n (fun x => (2^n·(pm(f x) − pm(f(hcFlip n x i))))²)
    ///     = ((2^n·2^n)·4) · subsetSum n (fun x => ind(disagree x)),
    /// where `disagree x = Bool.not (Bool.beq (f x) (f(hcFlip n x i)))`. The
    /// disagree-side normalization of the master identity: each squared scaled
    /// derivative collapses to `(2^n)²·4·[f x ≠ f(flip)]` via `disagree_sq_bridge`.
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_disagree_side(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_disagree_side");
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
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_disagree_sq_bridge()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.init_rat_field_inst()?; // Rat.mul_assoc

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: disagree_side_type(&c),
            value: disagree_side_value(&c),
        })
    }
}

// ════════════ Leg 5b: coefficient side ════════════
//
//   2^n · subsetSum n (fun S => a_fn(S)²)
//     = (2^n·4) · subsetSum n (fun S => ind(S i)·A_S²),
// a_fn(S) = (2·ind(S i))·A_S.
//
// Per-S integrand identity (under subsetSum_congr):
//   a_fn(S)² = 4·(ind(S i)·(A_S·A_S)),
// via mmmc (twice) + ind_mul_self + mul_assoc (and the ground 2·2 ≡ 4);
// then subsetSum_smul pulls 4 out and mul_assoc moves 2^n through.

impl InflConsts {
    /// `fun S => ind(S i)·(A_S·A_S)`.
    fn ind_amp_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let k = self.amp(&sb, n, b, &s);
        let is_ = self.ind_(Expr::app(s.clone(), i.clone()));
        let body = self.mul(is_, self.mul(k.clone(), k));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => 4·(ind(S i)·(A_S·A_S))`.
    fn four_ind_amp_sq_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let k = self.amp(&sb, n, b, &s);
        let is_ = self.ind_(Expr::app(s.clone(), i.clone()));
        let body = self.mul(self.rat_four(), self.mul(is_, self.mul(k.clone(), k)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// Per-S identity: `a_fn(S)² = 4·(is·(k·k))`, is=ind(S i), k=A_S.
    fn per_s_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, s: &Expr, i: &Expr) -> Expr {
        let is_ = self.ind_(Expr::app(s.clone(), i.clone()));
        let k = self.amp(parent, n, b, s);
        let two = self.rat_two();
        let two_is = self.mul(two.clone(), is_.clone());
        let kk = self.mul(k.clone(), k.clone());
        let is_is = self.mul(is_.clone(), is_.clone());
        let two_two = self.mul(two.clone(), two.clone());

        // s0 := ((2·is)·k)·((2·is)·k).
        let s0 = self.mul(
            self.mul(two_is.clone(), k.clone()),
            self.mul(two_is.clone(), k.clone()),
        );
        // step1 : s0 = ((2·is)·(2·is))·(k·k)   mmmc (2·is) k (2·is) k.
        let step1 = self.mmmc(two_is.clone(), k.clone(), two_is.clone(), k.clone());
        let tt_is = self.mul(two_is.clone(), two_is.clone());
        let s1 = self.mul(tt_is.clone(), kk.clone());

        // sub : (2·is)·(2·is) = (2·2)·(is·is)   mmmc 2 is 2 is.
        let sub_mmmc = self.mmmc(two.clone(), is_.clone(), two.clone(), is_.clone());
        let twotwo_isis = self.mul(two_two.clone(), is_is.clone());
        // ind² : is·is = is.
        let ind_sq = Expr::apps(self.ind_mul_self.clone(), [Expr::app(s.clone(), i.clone())]);
        // sub2 : (2·2)·(is·is) = (2·2)·is   congrArg((2·2)·) ind².
        let sub2 = self.mul_left_congr(parent, &two_two, is_is.clone(), is_.clone(), ind_sq);
        let twotwo_is = self.mul(two_two.clone(), is_.clone());
        // tt_is_eq : (2·is)·(2·is) = (2·2)·is.
        let tt_is_eq = self.trans(
            tt_is.clone(),
            twotwo_isis.clone(),
            twotwo_is.clone(),
            sub_mmmc,
            sub2,
        );
        // step2 : ((2·is)·(2·is))·(k·k) = ((2·2)·is)·(k·k)   congrArg(·(k·k)) tt_is_eq.
        let step2 = self.mul_right_congr(parent, &kk, tt_is.clone(), twotwo_is.clone(), tt_is_eq);
        let s2 = self.mul(twotwo_is.clone(), kk.clone());

        // step3 : ((2·2)·is)·(k·k) = (2·2)·(is·(k·k))   mul_assoc (2·2) is (k·k).
        let step3 = Expr::apps(
            self.rat_mul_assoc.clone(),
            [two_two.clone(), is_.clone(), kk.clone()],
        );
        let is_kk = self.mul(is_.clone(), kk.clone());
        let _s3 = self.mul(two_two.clone(), is_kk.clone());
        // target : 4·(is·(k·k))  — def-eq to (2·2)·(is·(k·k)).
        let target = self.mul(self.rat_four(), is_kk.clone());

        // chain: s0 = s1 = s2 = s3 (≡ target by 2·2 ≡ 4).
        let t1 = self.trans(s0.clone(), s1.clone(), s2.clone(), step1, step2);
        // last trans lands at s3 but typed as target (def-eq).
        self.trans(s0, s2, target, t1, step3)
    }
}

fn coeff_side_type(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let lhs = c.mul(c.cube(&n), c.ssum(&n, c.a_sq_fn(&b, &n, &bf, &i)));
    let p4 = c.mul(c.cube(&n), c.rat_four());
    let rhs = c.mul(p4, c.ssum(&n, c.ind_amp_sq_fn(&b, &n, &bf, &i)));
    let concl = c.eq_rat(lhs, rhs);
    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn coeff_side_value(c: &InflConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let p = c.cube(&n);
    // leg1 : Σ_S a_fn(S)² = Σ_S 4·(is·k²)   (subsetSum_congr + per_s_coeff).
    let h = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pf = c.per_s_coeff(&sb, &n, &bf, &s, &i);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, pf))
    };
    let leg1 = Expr::apps(
        c.subset_sum_congr.clone(),
        [
            n.clone(),
            c.a_sq_fn(&b, &n, &bf, &i),
            c.four_ind_amp_sq_fn(&b, &n, &bf, &i),
            h,
        ],
    );
    // leg2 : Σ_S 4·(is·k²) = 4·Σ_S (is·k²)   (subsetSum_smul).
    let leg2 = c.smul(&n, c.rat_four(), c.ind_amp_sq_fn(&b, &n, &bf, &i));

    // ss_a_sq := Σ_S a_fn(S)² ; ss_ind := Σ_S (is·k²).
    let ss_a_sq = c.ssum(&n, c.a_sq_fn(&b, &n, &bf, &i));
    let ss_4ind = c.ssum(&n, c.four_ind_amp_sq_fn(&b, &n, &bf, &i));
    let ss_ind = c.ssum(&n, c.ind_amp_sq_fn(&b, &n, &bf, &i));
    let four_ss_ind = c.mul(c.rat_four(), ss_ind.clone());
    // inner : Σ_S a_fn(S)² = 4·Σ_S (is·k²).
    let inner = c.trans(
        ss_a_sq.clone(),
        ss_4ind.clone(),
        four_ss_ind.clone(),
        leg1,
        leg2,
    );

    // proof : P·Σ_S a_fn(S)² = (P·4)·Σ_S (is·k²).
    //   leg_cong : P·Σa_fn² = P·(4·Σind)   congrArg(P·) inner ;
    //   leg_assoc : P·(4·Σind) = (P·4)·Σind   symm (mul_assoc P 4 Σind).
    let p_ssasq = c.mul(p.clone(), ss_a_sq.clone());
    let p_4ssind = c.mul(p.clone(), four_ss_ind.clone());
    let p4 = c.mul(p.clone(), c.rat_four());
    let p4_ssind = c.mul(p4.clone(), ss_ind.clone());
    let leg_cong = c.mul_left_congr(&b, &p, ss_a_sq.clone(), four_ss_ind.clone(), inner);
    let assoc = Expr::apps(
        c.rat_mul_assoc.clone(),
        [p.clone(), c.rat_four(), ss_ind.clone()],
    );
    let leg_assoc = c.symm(p4_ssind.clone(), p_4ssind.clone(), assoc);
    let proof = c.trans(p_ssasq, p_4ssind, p4_ssind, leg_cong, leg_assoc);

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_coeff_side` —
    ///   2^n · subsetSum n (fun S => a_fn(S)²)
    ///     = (2^n·4) · subsetSum n (fun S => ind(S i)·A_S²),
    /// where `a_fn(S) = (2·ind(S i))·A_S`, `A_S = subsetSum n (fun y => b(y)·χ_S(y))`.
    /// The coefficient-side normalization of the master identity: each squared
    /// modified coefficient collapses to `4·ind(S i)·A_S²` via `ind_mul_self`
    /// and mmmc, then `subsetSum_smul`/`mul_assoc` factor the constants.
    /// Kernel-checked, constructive. Idempotent.
    pub(crate) fn register_subset_sum_coeff_side(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_coeff_side");
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
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_ind_mul_self()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.init_rat_field_inst()?; // Rat.mul_assoc

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = InflConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: coeff_side_type(&c),
            value: coeff_side_value(&c),
        })
    }
}

#[cfg(test)]
mod influence_bridge_tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let n = Name::from_string(name);
        let tc = TypeChecker::with_mode(env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        let deps = env.axiom_deps(&n).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(
            names.is_empty(),
            "{name} closure must be ⊆ FOUNDATIONAL_AXIOMS, got {names:?}"
        );
        assert!(matches!(
            env.proof_quality(&n),
            Some(ProofQuality::Constructive)
        ));
    }

    #[test]
    fn test_ind_mul_self_constructive() {
        let mut env = Environment::with_prelude();
        env.register_ind_mul_self().expect("register ind_mul_self");
        env.register_ind_mul_self().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.ind_mul_self");
    }

    #[test]
    fn test_subset_sum_disagree_side_constructive() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_disagree_side()
            .expect("register disagree_side");
        env.register_subset_sum_disagree_side().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.subsetSum_disagree_side");
    }

    #[test]
    fn test_subset_sum_coeff_side_constructive() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_coeff_side()
            .expect("register coeff_side");
        env.register_subset_sum_coeff_side().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.subsetSum_coeff_side");
    }
}
