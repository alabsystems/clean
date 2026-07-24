// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **HOME STRETCH**: H2, the per-coordinate LINEAR bound, and the
//! summed dual-HC `h_dual`.
//!
//! ## What this proves
//!
//! Three rungs, each a kernel-checked `Constructive` empty-closure Theorem,
//! chaining the landed H1 / `dualhc_final_le` / `rpow32_scale` /
//! `dualhc_m_pow2_eq_4pow_influence` bricks into the exact `h_dual` the assembly
//! `kkl_lowband_mass_of_dual_hc` consumes.
//!
//! Write `D := Rat.powNat 2 n`, `Inf_i := Influence n f i`, `W_i` the band-form
//! `subsetSum n (fun y => Tg y · Tg y)` (`Tg := noiseOp third n (D_i (pm∘f))`),
//! `Wb := subsetSum n (coord_w_band_fn n k f i)` (the assembly's `sum_w_band`
//! summand at coordinate `i`).
//!
//! 1. **H2** `BoolAnalysis.dualhc_h2`:
//!    ```text
//!    ∀ n f i r_i, IsRpow32 (Influence n f i) r_i → W_i ≤ four·((powNat 8 n)·r_i)
//!    ```
//!    `rpow32_scale` at `c := D` lifts `IsRpow32 Inf_i r_i` to `IsRpow32
//!    ((D·D)·Inf_i) (((D·D)·D)·r_i)`. Two `Eq.subst` rewrites land it on the
//!    `dualhc_final_le` hypothesis shape `IsRpow32 (m·D) r`:
//!    (a) `(D·D)·Inf_i = m·D` (symm of `dualhc_m_pow2_eq_4pow_influence` after the
//!    `powNat_two_eq_ofNat_pow` spelling rewrite); (b) `((D·D)·D)·r_i = 8^n·r_i`
//!    (`dualhc_pow8_eq_two_pow_cube`). Then `dualhc_final_le n f i (8^n·r_i)` gives
//!    `W_i ≤ four·(8^n·r_i)`.
//!
//! 2. **per-coord linear bound** `BoolAnalysis.dualhc_percoord_linear`:
//!    ```text
//!    ∀ n k f i r_i, IsRpow32 (Influence n f i) r_i → Wb ≤ (four·9^k)·r_i
//!    ```
//!    `dualhc_norm_cancel_8n` with `Wb := Wb`, `P9 := 9^k`, `W := W_i`, `q :=
//!    four·9^k`: H1 (`8^n·Wb ≤ 9^k·W_i`), H2 (`W_i ≤ four·(8^n·r_i)`), and the
//!    pure-ring regroup `9^k·(four·(8^n·r_i)) = 8^n·((four·9^k)·r_i)` and
//!    `0 ≤ 9^k` discharge the `8^n` cancellation.
//!
//! 3. **summed `h_dual`** `BoolAnalysis.dualhc_h_dual_sum`:
//!    ```text
//!    ∀ n k f (r : Fin n → Rat), (∀ i, IsRpow32 (Influence n f i) (r i))
//!      → Σ_i Wb_i ≤ (four·9^k)·Σ_i r_i
//!    ```
//!    `Fin.sum_le` over the per-coord bound gives `Σ_i Wb_i ≤ Σ_i ((four·9^k)·r_i)`;
//!    `Fin.sum_smul` rewrites the RHS to `(four·9^k)·Σ_i r_i`. This is the assembly's
//!    `h_dual` at `B := four·9^k`.
//!
//! Every leaf is a landed `Constructive` empty-closure Theorem, so each rung is
//! too. NO axiom is added or removed. NOT wired into the always-on
//! `init_boolean_analysis` aggregate (reachable via
//! `init_boolean_analysis_kkl_dualhc_percoord_recovered`). Idempotent.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

include!("boolean_analysis_kkl_dualhc_percoord_recovered_consts.rs");

impl Environment {
    /// Register H2, the per-coord linear bound, and the summed `h_dual`.
    /// Idempotent; kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_percoord_recovered(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_h2()?;
        self.register_dualhc_percoord_linear()?;
        self.register_dualhc_h_dual_sum()?;
        self.register_kkl_lowband_mass_fired()?;
        Ok(())
    }

    /// `BoolAnalysis.kkl_lowband_mass_fired` — the assembly FIRED on the proven
    /// `dualhc_h_dual_sum`. With `B := four·9^k` discharged from the per-coord
    /// chain:
    ///
    /// ```text
    /// ∀ (n k : Nat) (f : BoolFn n) (eps s : Rat) (r : Fin n → Rat),
    ///   (∀ i, 0 ≤ Influence n f i) → (∀ i, Influence n f i ≤ eps)
    ///     → 0 ≤ s → s·s = eps → (∀ i, IsRpow32 (Influence n f i) (r i))
    ///     → 4·M_{1..k}[f] ≤ ((four·9^k)·s) · TotalInfluence n f
    /// ```
    ///
    /// i.e. the dual-HC bound is no longer a HYPOTHESIS — it is the proven
    /// `dualhc_h_dual_sum`. The `B = four·9^k` carries through. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_kkl_lowband_mass_fired(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_lowband_mass_fired");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_nonneg()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_nonneg
        self.init_boolean_analysis_kkl_nnrpow()?;
        self.init_boolean_analysis_kkl_assembly()?; // kkl_lowband_mass_of_dual_hc
        self.register_dualhc_h_dual_sum()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = PercoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_fired(&c, false),
            value: build_fired(&c, true),
        })
    }

    /// `BoolAnalysis.dualhc_h2` — see the module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_h2(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_h2");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_nonneg()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.init_boolean_analysis_kkl_nnrpow()?; // IsRpow32, rpow32_scale
        self.register_rpow32_scale()?;
        self.init_boolean_analysis_kkl_dualhc_final()?; // dualhc_final_le, pow8_cube
        self.register_dualhc_pow8_eq_two_pow_cube()?;
        self.init_boolean_analysis_kkl_dualhc_norminfl()?; // m_pow2_eq_4pow_influence
        self.register_dualhc_m_pow2_eq_4pow_influence()?;
        self.register_pownat_two_eq_ofnat_pow()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = PercoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_h2(&c, false),
            value: build_h2(&c, true),
        })
    }

    /// `BoolAnalysis.dualhc_percoord_linear` — see the module docs.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_dualhc_percoord_linear(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_percoord_linear");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_nonneg()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.init_boolean_analysis_kkl_nnrpow()?;
        self.register_dualhc_h1()?; // H1
        self.register_dualhc_h2()?; // H2
        self.register_dualhc_norm_cancel_8n()?; // the 8^n-cancel
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = PercoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_percoord(&c, false),
            value: build_percoord(&c, true),
        })
    }

    /// `BoolAnalysis.dualhc_h_dual_sum` — see the module docs. The assembly's
    /// `h_dual` at `B := four·9^k`. Kernel-checked, `Constructive`, empty closure.
    /// Idempotent.
    pub fn register_dualhc_h_dual_sum(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_h_dual_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat()?;
        self.init_fin_sum()?;
        self.register_fin_sum_le_theorem()?;
        self.register_fin_sum_smul_theorem()?;
        self.register_subset_sum()?;
        self.register_rat_pow_nat()?;
        self.init_boolean_analysis_kkl_nnrpow()?;
        self.register_dualhc_percoord_linear()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = PercoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_h_dual(&c, false),
            value: build_h_dual(&c, true),
        })
    }
}

include!("boolean_analysis_kkl_dualhc_percoord_recovered_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn assert_ct(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_dualhc_h2_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_dualhc_h2().expect("register_dualhc_h2");
        env.register_dualhc_h2().expect("idempotent");
        assert_ct(&env, "BoolAnalysis.dualhc_h2");
    }

    #[test]
    fn test_dualhc_percoord_linear_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_dualhc_percoord_linear()
            .expect("register_dualhc_percoord_linear");
        env.register_dualhc_percoord_linear().expect("idempotent");
        assert_ct(&env, "BoolAnalysis.dualhc_percoord_linear");
    }

    #[test]
    fn test_dualhc_h_dual_sum_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_dualhc_h_dual_sum()
            .expect("register_dualhc_h_dual_sum");
        env.register_dualhc_h_dual_sum().expect("idempotent");
        assert_ct(&env, "BoolAnalysis.dualhc_h_dual_sum");
    }

    #[test]
    fn test_kkl_lowband_mass_fired_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_lowband_mass_fired()
            .expect("register_kkl_lowband_mass_fired");
        env.register_kkl_lowband_mass_fired().expect("idempotent");
        assert_ct(&env, "BoolAnalysis.kkl_lowband_mass_fired");
    }
}
