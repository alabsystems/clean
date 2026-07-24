// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — **H1**: `8^n · W^{≤k}[D_i f] ≤ 9^k · W_i`.
//!
//! ## What this proves
//!
//! The H1 connect threads the landed band-form bridge (`dualhc_W_eq_band_form`),
//! RUNG A (`subsetSum_low_band_extract` at `b = 1/9`), the mask swap
//! (`subsetSum_mask_ble_eq_not_ble`) and the per-`S` band regroup
//! (`dualhc_band_regroup`) into the per-coordinate spectral→band inequality the
//! dual-HC normalization (`dualhc_norm_cancel_8n`) consumes:
//!
//! ```text
//! BoolAnalysis.dualhc_h1 :
//!   ∀ (n k : Nat) (f : BoolFn n) (i : Fin n),
//!     Rat.le
//!       (Rat.mul (Rat.powNat 8 n)                       -- 8^n
//!                (subsetSum n (coord_w_band_fn n k f i)))  -- W^{≤k}[D_i f]
//!       (Rat.mul (Rat.powNat 9 k)                       -- 9^k
//!                (subsetSum n (W_i_band_lhs n f i)))     -- W_i  (band-form LHS)
//! ```
//!
//! where `coord_w_band_fn` is RUNG B's `ind (S i) · (ind (not (ble (k+1) |S|)) ·
//! (4 · f̂(S)²))` (the assembly's `sum_w_band` summand) and `W_i` is
//! `dualhc_W_eq_band_form`'s LHS `subsetSum n (fun y => Tg y · Tg y)`,
//! `Tg := noiseOp third n (D_i (pm∘f))`.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Writing `D := mk(ofNat 2^n) 1`, `c8 := powNat 8 n`, `P9k := powNat 9 k`,
//! `ninth := third·third = 1/9`, `w S := (4·ind(S i))·(f̂·f̂)`, `feed := Σ_S
//! ninth^{|S|}·w S`, `Mble := Σ_S ind(ble |S| k)·w S`, `Wb := Σ_S coord_w_band`:
//!
//! 1. RUNG A `subsetSum_low_band_extract n k ninth w (0≤ninth)(ninth≤1)(∀S 0≤w S)`:
//!    `ninth^k · Mble ≤ feed`.
//! 2. clear-out: `mul_le_mul_of_nonneg_left P9k (ninth^k·Mble) feed (1)(0≤P9k)`
//!    gives `P9k·(ninth^k·Mble) ≤ P9k·feed`; and
//!    `P9k·(ninth^k·Mble) = Mble` because `9^k·(1/9)^k = (9·(1/9))^k = 1^k = 1`
//!    (`mul_assoc` ∘ `symm powNat_mul_base` ∘ `congr (·^k) nine_third_third_eq_one`
//!    ∘ `powNat_one_base` ∘ `one_mul`). `Eq.subst` → `Mble ≤ P9k·feed`.
//! 3. mask swap + band regroup: `Mble = Σ_S ind(not ble(k+1)|S|)·w S`
//!    (`subsetSum_mask_ble_eq_not_ble`) `= Wb` (`dualhc_band_regroup`).
//!    `Eq.subst` → `Wb ≤ P9k·feed`.
//! 4. scale by `c8`: `mul_le_mul_of_nonneg_left c8 Wb (P9k·feed) (3)(0≤c8)` gives
//!    `c8·Wb ≤ c8·(P9k·feed)`; and `c8·(P9k·feed) = P9k·(c8·feed) = P9k·W_i`
//!    because `c8 = (D·D)·D = D·(D·D)` (`dualhc_pow8_eq_two_pow_cube` ∘
//!    `powNat_two_eq_ofNat_pow` ∘ `mul_assoc`) and `(D·(D·D))·feed = W_i`
//!    (`symm dualhc_W_eq_band_form`). `Eq.subst` → `c8·Wb ≤ P9k·W_i`.
//!
//! Every leaf is a landed `Constructive` empty-closure Theorem, so H1 is too. NO
//! axiom is added or removed. NOT wired into the always-on `init_boolean_analysis`
//! aggregate (reachable via `register_dualhc_h1`). Idempotent.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

include!("boolean_analysis_kkl_dualhc_h1connect_consts.rs");

impl Environment {
    /// `BoolAnalysis.dualhc_h1` — see the module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_h1(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_h1");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_set_size_nat()?;
        self.register_level_wt()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_nonneg()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_pow_nat_mul_base_theorem()?;
        self.register_rat_pow_nat_one_base_theorem()?;
        self.register_rat_order_proofs()?;
        self.register_rat_minmax_proofs()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left, Rat.mul_nonneg
        self.register_ind_nonneg()?; // BoolAnalysis.ind_nonneg
        self.register_fourier_sq_nonneg()?; // BoolAnalysis.fourier_sq_nonneg
                                            // band-form bridge + per-S spectral
        self.init_boolean_analysis_kkl_dualhc_h1()?; // dualhc_W_eq_band_form (+ per-s)
                                                     // RUNG A
        self.init_boolean_analysis_kkl_lowband_extract()?; // subsetSum_low_band_extract
                                                           // mask swap + band regroup + 9·(1/9)=1
        self.init_boolean_analysis_kkl_band_reconcile()?; // subsetSum_mask_ble_eq_not_ble
        self.register_dualhc_band_regroup()?;
        self.register_nine_third_third_eq_one()?;
        // 8^n reconcile
        self.register_dualhc_pow8_eq_two_pow_cube()?;
        self.register_pownat_two_eq_ofnat_pow()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = H1ConnectConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_h1(&c, false),
            value: build_h1(&c, true),
        })
    }
}

include!("boolean_analysis_kkl_dualhc_h1connect_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_dualhc_h1().expect("register_dualhc_h1");
        env.register_dualhc_h1().expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
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
    fn test_dualhc_h1_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.dualhc_h1");
    }
}
