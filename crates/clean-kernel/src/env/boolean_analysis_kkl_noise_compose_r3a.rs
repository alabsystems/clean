// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose.rs — R3a, the UN-NORMALIZED
// spectral twin of the normalized rung 1. Shares `ComposeConsts` and reuses the
// `aa_eq` / `reassoc_acb_cab` / `q_fn` / `levelwt` helpers from the `_norm`
// include. Split out only for the 500-line-per-file convention; not a standalone
// module. (Regular `//` comments: inner doc `//!` is not allowed at an
// `include!` site.)
//
// ## What this proves
//
//   BoolAnalysis.noise_spectral_unnorm_eq_pow4 :
//     ∀ (n : Nat) (g : HCPoint n → Rat),
//       subsetSum n (fun S => levelWt (1/3) n S · (A g S · A g S))            -- Σ_S levelWt·A²
//         = Rat.mul (Rat.powNat 4 n)
//                   (Rat.mul (subsetSum n (fun y => noiseOp(1/3) n g y · noiseOp(1/3) n g y))
//                            (Rat.inv (Rat.powNat 8 n)))                      -- 4^n · W_norm
//
// i.e. `Σ_S levelWt·A² = 4^n · W_norm_g`, where `W_norm_g := (Σ_y (T g y)²)·inv(8^n)`
// is the normalized two-norm (= the LHS of `noise_two_norm_spectral_third_norm`)
// and `A g S := subsetSum n (fun x => g x·χ_S x)` is the un-normalized coefficient.
// This is the un-normalized twin of the NORMALIZED rung 1
// (`noise_two_norm_spectral_third_norm : W_norm = Σ_S levelWt·Ahat²`), recovered
// by the per-S coefficient rescale `A² = 4^n·Ahat²` (`aa_eq`, the same brick the
// normalized rung uses internally).
//
// ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//
//   Let Q := Σ_S levelWt·(Ahat·Ahat) (= rung-1-norm RHS), WN := (Σ_y (Tg)²)·inv8.
//   r1n  : WN = Q                       (noise_two_norm_spectral_third_norm).
//   Target LHS U := Σ_S levelWt·(A·A).
//     legA : U = Σ_S 4^n·(levelWt·(Ahat·Ahat))   ss_congr per-S
//              (per-S: levelWt·(A·A) = levelWt·(4^n·(Ahat·Ahat))   congr (levelWt·_) aa_eq
//                                    = 4^n·(levelWt·(Ahat·Ahat))   reassoc a·(c·b)=c·(a·b)).
//     legB : Σ_S 4^n·(levelWt·Ahat²) = 4^n·Σ_S levelWt·Ahat² = 4^n·Q   ss_smul.
//   So U = 4^n·Q. Then 4^n·WN = 4^n·Q (congr (4^n·_) r1n), symm ⟹ 4^n·Q = 4^n·WN,
//   chain U = 4^n·Q = 4^n·WN.
//
// Every leaf (`noise_two_norm_spectral_third_norm`, `aa_eq`, `reassoc_acb_cab`,
// `subsetSum_smul`, `subsetSum_congr`, `congrArg`, `Eq.*`) is `Constructive` with
// empty admitted-axiom closure, so R3a is too. No axiom is added or removed.
// Idempotent.

impl ComposeConsts {
    /// UN-normalized R3a integrand `fun S => levelWt (1/3) n S · (A g S · A g S)`
    /// — the TARGET LHS.
    fn u_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let lvl = self.levelwt(n, &s);
        let a = self.a_coeff(&sb, n, g, &s);
        let body = self.mul(lvl, self.mul(a.clone(), a));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// R3a middle integrand `fun S => 4^n · (levelWt · (Ahat · Ahat))`.
    fn u_mid_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let lvl = self.levelwt(n, &s);
        let ahat = self.ahat(&sb, n, g, &s);
        let ahat_ahat = self.mul(ahat.clone(), ahat);
        let body = self.mul(self.pownat_lit(4, n), self.mul(lvl, ahat_ahat));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

/// `∀ n g, Σ_S levelWt·(A·A) = 4^n·((Σ_y (Tg)²)·inv8)`.
fn unnorm_pow4_type(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);

    let u = c.ssum(&n, c.u_fn(&b, &n, &g)); // Σ_S levelWt·(A·A)
    let lhs_fn = {
        let mut yb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let tgy = c.op_apply(&c.third(), &n, &g, &y);
        let body = c.mul(tgy.clone(), tgy);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs_un = c.ssum(&n, lhs_fn); // Σ_y (Tg)²
    let inv8 = c.inv(c.pownat_lit(8, &n));
    let wn = c.mul(lhs_un, inv8); // W_norm = (Σ_y (Tg)²)·inv8
    let p4 = c.pownat_lit(4, &n);
    let concl = c.eq_rat(u, c.mul(p4, wn));

    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `λ n g => <U = 4^n·Q = 4^n·WN>`.
fn unnorm_pow4_value(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);

    let p4 = c.pownat_lit(4, &n);

    // WN := (Σ_y (Tg)²)·inv8.
    let lhs_fn = {
        let mut yb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let tgy = c.op_apply(&c.third(), &n, &g, &y);
        let body = c.mul(tgy.clone(), tgy);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs_un = c.ssum(&n, lhs_fn);
    let inv8 = c.inv(c.pownat_lit(8, &n));
    let wn = c.mul(lhs_un, inv8.clone());

    let u = c.ssum(&n, c.u_fn(&b, &n, &g)); // U = Σ_S levelWt·(A·A)
    let u_mid = c.ssum(&n, c.u_mid_fn(&b, &n, &g)); // Σ_S 4^n·(levelWt·Ahat²)
    let q = c.ssum(&n, c.q_fn(&b, &n, &g)); // Q = Σ_S levelWt·(Ahat·Ahat)
    let p4_q = c.mul(p4.clone(), q.clone()); // 4^n·Q
    let p4_wn = c.mul(p4.clone(), wn.clone()); // 4^n·WN

    // ── legA : U = Σ_S 4^n·(levelWt·Ahat²)   ss_congr over per-S ──
    let leg_a_hyp = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let lvl = c.levelwt(&n, &s);
        let a = c.a_coeff(&sb, &n, &g, &s);
        let aa = c.mul(a.clone(), a.clone());
        let inv2 = c.inv(c.pownat_lit(2, &n));
        let ahat = c.mul(a.clone(), inv2);
        let ahat_ahat = c.mul(ahat.clone(), ahat);
        // s1 : levelWt·(A·A) = levelWt·(4^n·(Ahat·Ahat))   congr (levelWt·_) aa_eq.
        let aa_eq = c.aa_eq(&sb, &n, &g, &s); // A·A = 4^n·(Ahat·Ahat)
        let rhs_in = c.mul(p4.clone(), ahat_ahat.clone());
        let mot_l = c.mul_left_motive(&sb, &lvl);
        let s1 = c.congr_rat(aa.clone(), rhs_in.clone(), mot_l, aa_eq);
        let lhs_s = c.mul(lvl.clone(), aa.clone());
        let mid_s = c.mul(lvl.clone(), rhs_in.clone());
        // s2 : levelWt·(4^n·(Ahat·Ahat)) = 4^n·(levelWt·(Ahat·Ahat))   reassoc a·(c·b)=c·(a·b).
        //   a := levelWt, c := 4^n, b := Ahat·Ahat.
        let s2 = c.reassoc_acb_cab(&sb, &lvl, &p4, &ahat_ahat);
        let tgt_s = c.mul(p4.clone(), c.mul(lvl.clone(), ahat_ahat.clone()));
        let body = c.trans(lhs_s, mid_s, tgt_s, s1, s2);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg_a = c.ss_congr(&n, &c.u_fn(&b, &n, &g), &c.u_mid_fn(&b, &n, &g), leg_a_hyp);
    // legB : Σ_S 4^n·(levelWt·Ahat²) = 4^n·Σ_S levelWt·Ahat² = 4^n·Q   ss_smul.
    let leg_b = c.ss_smul(&n, &p4, &c.q_fn(&b, &n, &g));
    // U = u_mid = 4^n·Q.
    let u_eq_4q = c.trans(u.clone(), u_mid.clone(), p4_q.clone(), leg_a, leg_b);

    // ── r1n : WN = Q  (noise_two_norm_spectral_third_norm n g) ──
    let r1n = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.noise_two_norm_spectral_third_norm"),
            vec![],
        ),
        [n.clone(), g.clone()],
    );
    // 4^n·WN = 4^n·Q   congr (4^n·_) r1n.
    let mot_p4 = c.mul_left_motive(&b, &p4);
    let p4wn_eq_p4q = c.congr_rat(wn.clone(), q.clone(), mot_p4, r1n); // 4^n·WN = 4^n·Q
                                                                       // symm : 4^n·Q = 4^n·WN.
    let p4q_eq_p4wn = c.symm(p4_wn.clone(), p4_q.clone(), p4wn_eq_p4q);

    // assemble : U = 4^n·Q = 4^n·WN.
    let proof = c.trans(u.clone(), p4_q.clone(), p4_wn.clone(), u_eq_4q, p4q_eq_p4wn);

    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.noise_spectral_unnorm_eq_pow4` — R3a, the
    /// UN-NORMALIZED spectral twin of the normalized rung 1:
    /// `∀ n g, subsetSum n (fun S => levelWt (1/3) n S · (A g S · A g S))
    ///    = (powNat 4 n) · ((subsetSum n (fun y => (T g y)²)) · inv(8^n))`,
    /// i.e. `Σ_S levelWt·A² = 4^n · W_norm_g`. Composes the NORMALIZED rung
    /// (`noise_two_norm_spectral_third_norm : W_norm = Σ_S levelWt·Ahat²`) with the
    /// per-S coefficient rescale `A² = 4^n·Ahat²` (`aa_eq`). See this include's
    /// module docs. Kernel-checked, `Constructive`, empty admitted-axiom closure.
    /// Idempotent; no axiom added/removed.
    pub fn register_noise_spectral_unnorm_eq_pow4(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_spectral_unnorm_eq_pow4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_op()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_noise_two_norm_spectral_third_norm()?; // NORMALIZED rung 1 (W_norm = Σ levelWt·Ahat²)
        self.register_level_wt()?; // levelWt
        self.register_rat_pow_nat()?; // Rat.powNat (2^n / 4^n / 8^n)
        self.register_rat_pow_nat_mul_base()?; // powNat_pos (for four_inv_two_sq_cancel deps)
        self.register_four_inv_two_sq_cancel()?; // 4^n·(inv2·inv2) = 1 (used inside aa_eq)
        self.register_rat_mul_mul_mul_comm_theorem()?; // mul_mul_mul_comm (used inside aa_eq)
        {
            // Rat.mul_one / Rat.one_mul / Rat.mul_comm / Rat.mul_assoc.
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ComposeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: unnorm_pow4_type(&c),
            value: unnorm_pow4_value(&c),
        })
    }
}

#[cfg(test)]
mod r3a_tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_noise_spectral_unnorm_eq_pow4_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_spectral_unnorm_eq_pow4()
            .expect("register_noise_spectral_unnorm_eq_pow4");
        let nm = Name::from_string("BoolAnalysis.noise_spectral_unnorm_eq_pow4");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("R3a un-norm twin proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_unnorm_pow4_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_noise_spectral_unnorm_eq_pow4().expect("first");
        env.register_noise_spectral_unnorm_eq_pow4()
            .expect("idempotent");
    }
}
