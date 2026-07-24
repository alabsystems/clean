// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **induction step** `hc24_core_step` of the
//! (2,4)-hypercontractivity operator induction.
//!
//! The `n → n+1` step, stated with the induction hypothesis as an explicit
//! `∀ F'` premise (so the final `hc24_core` can discharge it with a plain
//! `Nat.rec` minor premise, no recursion inside this lemma):
//!
//! ```text
//! BoolAnalysis.hc24_core_step : ∀ (ρ : Rat) (n : Nat),
//!   3·(ρ·ρ) ≤ 1 →
//!   (∀ (F' : HCPoint n → Rat), <concl n F'>) →
//!   ∀ (F : HCPoint (n+1) → Rat), <concl (n+1) F>
//! ```
//!
//! where `<concl m F>` is the `hc24_core_concl` LE goal
//! `Σ_{2^m} pow4(noiseFn ρ m F jx) ≤ 8^m · sq(Σ_{2^m} sq(F(hcDecode m jx)))`.
//!
//! ## Worked chain (root-free, TIGHT `8^n`)
//!
//! Write `G k := noiseFn ρ n (gPart n F) k`, `H k := noiseFn ρ n (liftH n F) k`,
//! `SG := Σ sq(gPart n F (dec k))`, `SH := Σ sq(liftH n F (dec k))`,
//! `SF' := Σ_{2^(n+1)} sq(F(hcDecode (n+1) jx))`,
//! `P := Σ pow4 G`, `Q := Σ pow4 H`, `R := Σ (sq G · sq H)`.
//!
//! - **S1** `finSumPow2SuccSplit` on `fun jx => pow4(noiseFn ρ (n+1) F jx)` +
//!   `symm Fin.sum_add` merges LHS(n+1) = `Σ_k (lowP k + highP k)`.
//! - **S1'/S2** per `k`, `noiseFn_succ_low/high` rewrite the split halves to
//!   `pow4(G+ρH)` / `pow4(G−ρH)`, and `fourth_power_rho_two_point_bound (G k)
//!   (H k) ρ h` bounds their sum by `(1+1)·sq(sq G + sq H)`. `Fin.sum_le` lifts:
//!   `LHS(n+1) ≤ Σ_k (1+1)·sq(sq G + sq H)`; `Fin.sum_smul` pulls the `(1+1)`.
//! - **S3** `add_sq_regroup (sq G)(sq H)` + `Fin.sum_add` + `Fin.sum_smul` give
//!   `Σ_k sq(sq G + sq H) = (P + Q) + (1+1)·R`.
//! - **S4–S5** `Fin.sum_cauchy_schwarz` ⇒ `R·R ≤ P·Q`; IH at `gPart`/`liftH`
//!   ⇒ `P ≤ 8^n SG²`, `Q ≤ 8^n SH²`; `mul_le_mul_of_nonneg_*` ⇒
//!   `P·Q ≤ (8^n SG²)(8^n SH²) = (8^n SG·SH)²`; `Rat.le_of_sq_le_sq` ⇒
//!   `R ≤ 8^n·SG·SH`.
//! - **S6** `hc24Assemble (8^n) SG SH` folds the IH-bounded legs into
//!   `8^n·(SG+SH)²`.
//! - **S7** `hc24S7` collapses `SG+SH = (1+1)·SF'`, so `(SG+SH)² = 4·SF'²`.
//! - **S8** `powNat_succ` + numeral algebra: `(1+1)·8^n·(SG+SH)² =
//!   (1+1)·8^n·4·SF'² = 8·8^n·SF'² = 8^{n+1}·SF'²`.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure).

use super::boolean_analysis_hc24_core_base::{hc24_core_concl, Hc24Consts};
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

include!("boolean_analysis_hc24_step_consts.rs");
include!("boolean_analysis_hc24_step_build.rs");

impl Environment {
    /// Register `BoolAnalysis.hc24_core_step` — the `n → n+1` induction step of
    /// the (2,4)-hypercontractivity operator bound. Idempotent; axiom-free.
    pub(crate) fn register_hc24_core_step(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_fin_sum()?;
        self.register_fin_sum_pow2_succ_split()?;
        self.register_noise_fn_succ()?; // noiseFn_succ_low / _high (+ gPart/liftH/noiseFn)
        self.init_boolean_analysis_two_point_bound()?; // fourth_power_rho_two_point_bound
        self.init_boolean_analysis_fourth_power()?; // Rat.add_sq_regroup
        self.register_fin_sum_cauchy_schwarz_theorem()?; // Fin.sum_cauchy_schwarz
        self.init_boolean_analysis_order_toolkit_b1d()?; // Rat.le_of_sq_le_sq
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_*, sq_nonneg
        self.register_hc24_assemble()?; // hc24Assemble (S6)
        self.register_hc24_s7()?; // hc24S7 (S7)
        self.register_rat_pow_nat_succ_theorem()?; // Rat.powNat_succ
        self.register_rat_pow_nat_nonneg()?; // Rat.powNat_nonneg
        self.init_boolean_analysis_hc_bounds()?; // Rat order surface
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // ring + order structural
        }

        let name = Name::from_string("BoolAnalysis.hc24_core_step");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = StepConsts::new();
        let (type_, value) = build_step(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_hc24_core_step_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_hc24_core_step()
            .expect("register_hc24_core_step");
        env.register_hc24_core_step().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc24_core_step");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc24_core_step proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
