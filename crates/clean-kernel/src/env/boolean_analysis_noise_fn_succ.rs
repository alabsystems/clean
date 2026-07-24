// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the **operator-peel `noiseFn_succ`** identities: the
//! LAST unproven construction of the bonami campaign.
//!
//! After `noiseFn_succ_split` half-splits `noiseFn ρ (n+1) F jx` into the two
//! cube halves and the decode↔extend bridges identify each half's outer point,
//! at the LOW / HIGH split index `jx = castP(castAdd k)` / `castP(addNat k)` the
//! correlated density factors (`noiseDensityW_point_peel_*`) and the pointwise
//! ring keystone (`peel_pointwise_keystone`) fold the two half-sums into two
//! `n`-level `noiseFn` legs:
//!
//! ```text
//! BoolAnalysis.noiseFn_succ_low :
//!   ∀ (ρ : Rat) (n : Nat) (F : HCPoint (n+1) → Rat) (k : Fin (2^n)),
//!     noiseFn ρ (n+1) F (castP (Fin.castAdd (2^n) (2^n) k))
//!       = Rat.add (noiseFn ρ n (gPart n F) k)
//!                 (Rat.mul ρ (noiseFn ρ n (liftH n F) k))
//!
//! BoolAnalysis.noiseFn_succ_high :  (top bit true ⇒ pm(true) = −1 flips ρ's sign)
//!   ∀ (ρ : Rat) (n : Nat) (F : HCPoint (n+1) → Rat) (k : Fin (2^n)),
//!     noiseFn ρ (n+1) F (castP (Fin.addNat (2^n) (2^n) k))
//!       = Rat.sub (noiseFn ρ n (gPart n F) k)
//!                 (Rat.mul ρ (noiseFn ρ n (liftH n F) k))
//! ```
//!
//! with `gPart n F x ≡ F(extendF n x) + F(extendT n x)` (the unweighted "liftG"
//! leg) and `liftH n F x ≡ F(extendF n x) − F(extendT n x)` (the cross leg).
//!
//! ## Proof route (LOW; HIGH mirrors with peels `_tf`/`_tt` and ρ↦−ρ)
//!
//! Abbreviate `x' := hcDecode n k` (outer), `y := hcDecode n i` (inner),
//! `d := noiseDensityW ρ n x' y`, `p := F(extendF n y)`, `q := F(extendT n y)`.
//!
//! 1. `noiseFn_succ_split ρ n F (castP(castAdd k))`: the LHS = `(Σᵢ LOWᵢ) + (Σᵢ
//!    HIGHᵢ)` with `LOWᵢ = p·D₊`, `HIGHᵢ = q·D₋`, `D_b = noiseDensityW ρ (n+1)
//!    (hcDecode (n+1) (castP(castAdd k))) (extend_b n y)`.
//! 2. `Eq.symm (Fin.sum_add …)`: merge to `Σᵢ (LOWᵢ + HIGHᵢ)`.
//! 3. **per-index leaf** (`low_leaf` / `high_leaf`), lifted by `Fin.sum_congr`:
//!    a. bridge the outer point `hcDecode (n+1) (castP(castAdd k)) = extendF n x'`
//!       (`hcDecode_castP_castAdd_extendF`), `congrArg` into each density slot;
//!    b. peel `_ff`/`_ft`: `noiseDensityW ρ (n+1) (extendF x') (extend_c y) =
//!       d·(1+ρ·(pm false · pm c))`;
//!    c. **closed-bit cleanup** (`factor_ff`/`factor_ft`): `pm false·pm false ≡ 1`
//!       / `pm false·pm true ≡ −1` are defeq, so `Rat.mul_one`/`Rat.mul_neg`
//!       collapse `1+ρ·1 → 1+ρ` / `1+ρ·(−1) → 1−ρ` syntactically;
//!    d. lift through `p·(·)` / `q·(·)`, giving `LOWᵢ+HIGHᵢ = p·(d·(1+ρ)) +
//!       q·(d·(1−ρ))`;
//!    e. `peel_pointwise_keystone p q d ρ`: `= (p+q)·d + ρ·((p−q)·d)`, which is
//!       **δ-defeq** to `gPart n F y · d + ρ·(liftH n F y · d)` — the `n`-level
//!       `noiseFn` integrands of `gPart n F` / `liftH n F` at the outer point `x'`.
//! 4. `Fin.sum_add` splits the two legs; `Fin.sum_smul` pulls `ρ` out of the cross
//!    leg; both `Σ` legs are **δ-defeq** to `noiseFn ρ n (gPart n F) k` /
//!    `noiseFn ρ n (liftH n F) k`.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure):
//! leaves are `noiseFn_succ_split`, `noiseDensityW_point_peel_*`, the bridges,
//! `peel_pointwise_keystone`, `Fin.sum_{add,smul,congr}`, `Rat.mul_{one,neg}`, and
//! `Eq`/`congrArg` built-ins.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

include!("boolean_analysis_noise_fn_succ_consts.rs");
include!("boolean_analysis_noise_fn_succ_leaf.rs");
include!("boolean_analysis_noise_fn_succ_build.rs");

impl Environment {
    /// Register `BoolAnalysis.noiseFn_succ_low` and `_high`. Idempotent; axiom-free.
    pub(crate) fn register_noise_fn_succ(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.register_noise_fn_succ_split()?;
        self.init_boolean_analysis_noise_peel()?; // noiseDensityW_point_peel_*
        self.init_boolean_analysis_noise_extend_bridge()?; // decode↔extend bridges
        self.init_boolean_analysis_pointwise_keystone()?; // peel_pointwise_keystone
        self.init_boolean_analysis_peel_parts()?; // gPart / hPart
        self.register_lift_h()?; // liftH
        self.register_fin_sum_add_theorem()?; // Fin.sum_add
        self.register_fin_sum_smul_theorem()?; // Fin.sum_smul
        self.init_fin_sum()?; // Fin.sum_congr
        self.register_noise_fn()?;

        let c = NoiseFnSuccConsts::new();
        for (half, name) in [
            (Half::Low, "BoolAnalysis.noiseFn_succ_low"),
            (Half::High, "BoolAnalysis.noiseFn_succ_high"),
        ] {
            let name = Name::from_string(name);
            if self.get_const(&name).is_none() {
                let (ty, value) = build_noise_fn_succ(&c, half);
                self.add_decl(Declaration::Theorem {
                    name,
                    level_params: vec![],
                    type_: ty,
                    value,
                })?;
            }
        }
        Ok(())
    }
}

/// Which cube half a `noiseFn_succ` identity is about.
#[derive(Clone, Copy)]
pub(super) enum Half {
    /// LOW block: `castP ∘ castAdd`, outer top bit false (`extendF`), `+ρ`.
    Low,
    /// HIGH block: `castP ∘ addNat`, outer top bit true (`extendT`), `−ρ`.
    High,
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const NAMES: &[&str] = &[
        "BoolAnalysis.noiseFn_succ_low",
        "BoolAnalysis.noiseFn_succ_high",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_noise_fn_succ()
            .expect("register_noise_fn_succ");
        env
    }

    #[test]
    fn test_noise_fn_succ_are_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name_str in NAMES {
            let name = Name::from_string(name_str);
            let info = env
                .get_const(&name)
                .unwrap_or_else(|| panic!("{name_str} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name_str} is a Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name_str} proof must check: {e:?}"));
            let deps = env.axiom_deps(&name).expect("deps");
            let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name_str} must be axiom-free, got {dep_names:?}"
            );
            assert_eq!(
                env.proof_quality(&name),
                Some(ProofQuality::Constructive),
                "{name_str} must be Constructive"
            );
        }
    }
}
