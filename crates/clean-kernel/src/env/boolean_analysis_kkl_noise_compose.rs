// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL finish — RUNG 1, the spatial noise-kernel **convolution** (discrete
//! Chapman–Kolmogorov) `T_{1/3} ∘ T_{1/3} = T_{1/9}` in un-normalized kernel form.
//!
//! The scalar semigroup `(1/3)^k·(1/3)^k = (1/9)^k`
//! (`BoolAnalysis.noise_semigroup_third`) is the per-level spectral signature of
//! the operator semigroup; the SPATIAL operator semigroup — the kernel
//! convolution itself — was the genuine missing link between the spatial
//! `noiseOp` world (`noise_self_adjoint_sq`) and the spectral `A_S` world (B3a
//! `noise_two_norm_eq_pairing`). This module lands it:
//!
//! ```text
//! BoolAnalysis.noiseDensityW_compose_third :
//!   ∀ (n : Nat) (x y : HCPoint n),
//!     subsetSum n (fun z => noiseDensityW (1/3) n x z · noiseDensityW (1/3) n z y)
//!       = Rat.mul (cube n) (noiseDensityW (1/9) n x y)
//! ```
//!
//! i.e. `Σ_z W_{1/3}(x,z)·W_{1/3}(z,y) = 2^n·W_{1/9}(x,y)`. The `2^n = cube n`
//! factor is the un-normalized footprint of composing two un-normalized noise
//! operators (each `noiseOp` is `2^n·T_ρ`); it is the precise `8^n / 2^n`
//! normalization the rung-1 identity later reconciles.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure) — REUSE, not re-derive
//!
//! The hard orthogonality is already packaged as the noise-kernel **eigen-action**
//! `noiseDensity_apply_chi_eigen` (the diagonal action of the kernel on a single
//! decoded character):
//!
//! ```text
//! noiseDensity_apply_chi_eigen ρ n jS y :
//!   subsetSum n (fun z => noiseDensityW ρ n z y · χ_S(z)) = (cube n · ρ^{|S|})·χ_S(y)
//!   (S := hcDecode n jS)
//! ```
//!
//! With `x, y` fixed, expand only the FIRST density spectrally
//! (`noiseDensityW (1/3) n x z` δ-unfolds, reducibly, to
//! `subsetSum n (fun S => (1/3)^{|S|}·(χ_S x·χ_S z))`) and chain endpoints:
//!
//! ```text
//!   Σ_z (Σ_S (1/3)^{|S|}·(χ_S x·χ_S z))·W_{1/3}(z,y)         (E0 ≡ LHS, δ on W x z)
//!     →[per-z right-smul]   Σ_z Σ_S ((1/3)^{|S|}·(χ_S x·χ_S z))·W_{1/3}(z,y)   (E1)
//!     →[subsetSum_swap]     Σ_S Σ_z ((1/3)^{|S|}·(χ_S x·χ_S z))·W_{1/3}(z,y)   (E2)
//!     →[per-S factor-out]   Σ_S ((1/3)^{|S|}·χ_S x)·(Σ_z χ_S(z)·W_{1/3}(z,y))  (E3)
//!     →[per-S eigen]        Σ_S ((1/3)^{|S|}·χ_S x)·((cube·(1/3)^{|S|})·χ_S y)  (E4)
//!     →[per-S regroup]      Σ_S cube·(((1/3)^{|S|}·(1/3)^{|S|})·(χ_S x·χ_S y))  (E5)
//!     →[subsetSum_smul]     cube·Σ_S ((1/3)^{|S|}·(1/3)^{|S|})·(χ_S x·χ_S y)    (E6)
//!     →[per-S semigroup]    cube·Σ_S (1/9)^{|S|}·(χ_S x·χ_S y)                  (E7)
//!     ≡[δ on W_{1/9} x y]   cube·W_{1/9}(x,y)                                   = RHS
//! ```
//!
//! The per-S eigen step (E3→E4) is the only one needing the decoded pivot: the
//! outer S-sum `subsetSum n (fun S => …)` δ-unfolds to `Fin.sum (2^n) (… ∘
//! hcDecode)`, so inside, `S ≡ hcDecode n jS` and `noiseDensity_apply_chi_eigen
//! (1/3) n jS y` applies verbatim; the leg is a `Fin.sum_congr` over the per-jS
//! pointwise identity. Every leaf (`subsetSum_swap`, `subsetSum_smul`,
//! `subsetSum_congr`, `Fin.sum_congr`, `noiseDensity_apply_chi_eigen`,
//! `noise_semigroup_third`, `Rat.mul_*`, `congrArg`, `Eq.*`) is `Constructive`
//! with empty admitted-axiom closure, so this convolution is too. No axiom is
//! added or removed. Idempotent.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Atoms for the spatial noise-kernel convolution. Every `noiseDensityW` /
/// `subsetSum` / popcount spelling is byte-identical to the landed
/// `noiseDensity_apply_chi_eigen` / `noiseDensityW` / `noise_semigroup_third`
/// shapes so the consumed lemmas chain by def-eq.
pub(super) struct ComposeConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) nat_succ: Expr,
    pub(super) nat_zero: Expr,
    pub(super) nat_pow: Expr,
    pub(super) int_of_nat: Expr,
    pub(super) rat_mk: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_mul_comm: Expr,
    pub(super) rat_mul_assoc: Expr,
    pub(super) pow_nat: Expr,
    pub(super) set_size_nat: Expr,
    pub(super) hcpoint: Expr,
    pub(super) hc_decode: Expr,
    pub(super) chi: Expr,
    pub(super) noise_density: Expr,
    pub(super) eigen: Expr,
    pub(super) semigroup_third: Expr,
    pub(super) self_adjoint_sq: Expr,
    pub(super) two_norm_eq_pairing: Expr,
    pub(super) noise_op: Expr,
    pub(super) bool_: Expr,
    pub(super) fin_sum_nat: Expr,
    pub(super) subset_sum: Expr,
    pub(super) subset_sum_congr: Expr,
    pub(super) subset_sum_swap: Expr,
    pub(super) subset_sum_smul: Expr,
    pub(super) fin: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) fin_sum: Expr,
    pub(super) fin_sum_congr: Expr,
    pub(super) eq1: Expr,
    pub(super) eq_trans: Expr,
    pub(super) eq_symm: Expr,
    pub(super) congr_arg: Expr,
}

include!("boolean_analysis_kkl_noise_compose_consts.rs");

include!("boolean_analysis_kkl_noise_compose_chain.rs");
include!("boolean_analysis_kkl_noise_compose_chain4.rs");
include!("boolean_analysis_kkl_noise_compose_chain6.rs");
include!("boolean_analysis_kkl_noise_compose_norm.rs");
include!("boolean_analysis_kkl_noise_compose_r3a.rs");

impl Environment {
    /// Register `BoolAnalysis.noiseDensityW_compose_third` — the spatial
    /// noise-kernel convolution `Σ_z W_{1/3}(x,z)·W_{1/3}(z,y) = 2^n·W_{1/9}(x,y)`
    /// (discrete Chapman–Kolmogorov / the operator semigroup `T_{1/3}∘T_{1/3} =
    /// T_{1/9}` in kernel form). See module docs. Kernel-checked, `Constructive`,
    /// empty admitted-axiom closure. Idempotent; no axiom added/removed.
    pub fn register_noise_density_w_compose_third(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseDensityW_compose_third");
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
        self.register_subset_sum_swap_theorem()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_rat_pow_nat()?;
        self.register_set_size_nat()?;
        self.register_noise_density_w()?;
        self.register_noise_density_apply_chi_eigen()?;
        self.register_noise_semigroup_third()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_comm, Rat.mul_assoc
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ComposeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: compose_type(&c),
            value: compose_value(&c),
        })
    }

    /// Register `BoolAnalysis.noiseOp_compose_third` — the OPERATOR semigroup
    /// `noiseOp (1/3) ∘ noiseOp (1/3) = 2^n · noiseOp (1/9)` applied to `g`
    /// (`T_{1/3}∘T_{1/3} = 2^n·T_{1/9}`, un-normalized):
    /// `∀ n g x, noiseOp (1/3) n (noiseOp (1/3) n g) x = cube n · noiseOp (1/9) n g x`.
    /// A Fubini wrapper around the kernel convolution
    /// `noiseDensityW_compose_third`; this is the form the spatial
    /// `noise_self_adjoint_sq` RHS consumes (RUNG 1 bridge). Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_noise_op_compose_third(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noiseOp_compose_third");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_op()?; // noiseOp (+ noiseDensityW, subsetSum)
        self.register_subset_sum_congr()?;
        self.register_subset_sum_swap_theorem()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_noise_density_w_compose_third()?; // the kernel convolution
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_comm, Rat.mul_assoc
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ComposeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: op_compose_type(&c),
            value: op_compose_value(&c),
        })
    }

    /// Register `BoolAnalysis.noise_two_norm_spectral_third` — RUNG 1, the
    /// un-normalized spatial = spectral 2-norm identity:
    /// `∀ n g, subsetSum n (fun y => noiseOp(1/3) n g y · noiseOp(1/3) n g y)
    ///    = cube n · subsetSum n (fun S => ((1/3)^{|S|}·(1/3)^{|S|})·(A g S·A g S))`,
    /// i.e. `Σ_y (T_{1/3}g)(y)² = 2^n·Σ_S ((1/3)^{|S|})²·A(S)²`. Composes the spatial
    /// self-adjoint pivot `noise_self_adjoint_sq`, the operator semigroup
    /// `noiseOp_compose_third`, and the spectral pairing B3a
    /// `noise_two_norm_eq_pairing`. The `cube = 2^n` factor is the un-normalized
    /// footprint that the NORMALIZED `W_norm = Σ_S levelWt·Ahat²` form later
    /// reconciles (`Ahat = A·inv(2^n)`, `W_norm = (Σ_y (Tg)²)·inv(8^n)`).
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent;
    /// no axiom added/removed.
    pub fn register_noise_two_norm_spectral_third(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_two_norm_spectral_third");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_op()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_noise_self_adjoint_sq()?; // the spatial self-adjoint pivot
        self.register_noise_op_compose_third()?; // the operator semigroup (this module)
        self.register_noise_two_norm_eq_pairing()?; // B3a spectral pairing
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.mul_comm, Rat.mul_assoc
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = ComposeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: two_norm_spectral_type(&c),
            value: two_norm_spectral_value(&c),
        })
    }

    /// Register `BoolAnalysis.noise_two_norm_spectral_third_norm` — RUNG 1
    /// NORMALIZED, the `W_norm = Σ_S levelWt·Ahat²` form:
    /// `∀ n g, (subsetSum n (fun y => noiseOp(1/3) n g y · noiseOp(1/3) n g y))·inv(8^n)
    ///    = subsetSum n (fun S => levelWt (1/3) n S · (Ahat g S · Ahat g S))`,
    /// where `Ahat g S := (A g S)·inv(2^n)`. Reconciles the un-normalized
    /// `cube = 2^n` footprint of `noise_two_norm_spectral_third` with the
    /// `inv(8^n)` normalization the dual-HC aggregate (`kkl_deriv_two_norm_sum_le`)
    /// consumes, collapsing the `2^n·4^n·inv(8^n)` prefactor to `1` via
    /// `powNat_two_four_inv_eight_cancel`. See the `_norm` include's module docs.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent;
    /// no axiom added/removed.
    pub fn register_noise_two_norm_spectral_third_norm(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.noise_two_norm_spectral_third_norm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_noise_op()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_noise_two_norm_spectral_third()?; // RUNG 1 (un-normalized)
        self.register_level_wt()?; // levelWt
        self.register_set_size_nat()?; // setSizeNat (popcount carrier)
        self.register_levelwt_eq_pow_nat()?; // levelWt = powNat(ρ·ρ)|S|
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_mul_base()?; // powNat_mul_base, powNat_pos
        self.register_rat_pow_nat_two_eq_natcast()?; // cube = 2^n bridge
        self.register_four_inv_two_sq_cancel()?; // 4^n·(inv2·inv2) = 1
        self.register_pownat_two_four_inv_eight_cancel()?; // (2^n·4^n)·inv8 = 1
        self.register_rat_mul_mul_mul_comm_theorem()?; // mul_mul_mul_comm
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
            type_: two_norm_spectral_norm_type(&c),
            value: two_norm_spectral_norm_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_noise_density_w_compose_third()
            .expect("register_noise_density_w_compose_third");
        env
    }

    #[test]
    fn test_noise_density_w_compose_third_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.noiseDensityW_compose_third");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("compose proof must check against its type: {e:?}"));
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
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_noise_density_w_compose_third().expect("first");
        env.register_noise_density_w_compose_third()
            .expect("idempotent");
    }

    #[test]
    fn test_noise_op_compose_third_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_op_compose_third()
            .expect("register_noise_op_compose_third");
        let nm = Name::from_string("BoolAnalysis.noiseOp_compose_third");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("noiseOp_compose proof must check: {e:?}"));
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
    fn test_op_compose_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_noise_op_compose_third().expect("first");
        env.register_noise_op_compose_third().expect("idempotent");
    }

    #[test]
    fn test_noise_two_norm_spectral_third_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_two_norm_spectral_third()
            .expect("register_noise_two_norm_spectral_third");
        let nm = Name::from_string("BoolAnalysis.noise_two_norm_spectral_third");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("rung-1 proof must check: {e:?}"));
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
    fn test_two_norm_spectral_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_noise_two_norm_spectral_third().expect("first");
        env.register_noise_two_norm_spectral_third()
            .expect("idempotent");
    }

    #[test]
    fn test_noise_two_norm_spectral_third_norm_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_noise_two_norm_spectral_third_norm()
            .expect("register_noise_two_norm_spectral_third_norm");
        let nm = Name::from_string("BoolAnalysis.noise_two_norm_spectral_third_norm");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("normalized rung-1 proof must check: {e:?}"));
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
    fn test_two_norm_spectral_norm_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_noise_two_norm_spectral_third_norm()
            .expect("first");
        env.register_noise_two_norm_spectral_third_norm()
            .expect("idempotent");
    }
}
