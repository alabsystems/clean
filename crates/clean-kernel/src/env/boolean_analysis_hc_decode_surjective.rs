// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive surjectivity of `BoolAnalysis.hcDecode` — every cube point is the
//! decode of some `Fin (2^n)` index (BUILD #1 of the KKL dual-HC endgame).
//!
//! ```text
//! BoolAnalysis.hcDecode_surjective :
//!   ∀ (n : Nat) (S : HCPoint n), ∃ (jS : Fin (Nat.pow 2 n)), hcDecode n jS = S
//! ```
//!
//! with `HCPoint n ≡ Fin n → Bool` and `hcDecode n k i ≡ Nat.testBit (Fin.val k)
//! (Fin.val i)`. This is the cube-enumeration completeness fact: the `2^n`
//! `hcDecode`-images cover the whole cube. It lifts every `jS`-keyed projection
//! (e.g. `subsetSum_subset_diag_extract_scaled`) to an arbitrary `S`.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! `Nat.rec` on `n` (motive `M n := ∀ S : HCPoint n, ∃ jS, hcDecode n jS = S`).
//!
//! - **`n = 0`** — `2^0 ≡ 1`, witness `jS := Fin.mk 1 0 (Nat.zero_lt_succ 0)`.
//!   `hcDecode 0 jS = S` by `funext` over the EMPTY `Fin 0`: the pointwise field
//!   is `fun (i : Fin 0) => False.elim _ (Nat.not_succ_le_zero (val i) (i.isLt))`
//!   (no coordinate exists, so the equation holds vacuously).
//!
//! - **`n = succ k`** — given `S : HCPoint (k+1)`, restrict to
//!   `S' := fun (i : Fin k) => S (Fin.castSucc k i) : HCPoint k`. The IH at `S'`
//!   yields `j' : Fin (2^k)` with `hj' : hcDecode k j' = S'`. The top coordinate
//!   bit `S (Fin.last k) : Bool` selects the high half: `Bool.casesOn` on it
//!   (with the run-time witness `hb : S (last k) = <bit>` threaded via the
//!   `(S (last k) = bv) → goal` motive applied to `Eq.refl`):
//!     * **false** → witness `jS := castP (Fin.castAdd (2^k) (2^k) j')` — the LOW
//!       block. Its top bit is `testBit (val j') k = false` (`Nat.testBit_lt_pow`,
//!       `val j' < 2^k`), and its low bits are `testBit (val j') (val i) =
//!       hcDecode k j' i` (`hcDecode_castP_castAdd`).
//!     * **true** → witness `jS := castP (Fin.addNat (2^k) (2^k) j')` — the HIGH
//!       block. Its top bit is `testBit (2^k + val j') k = true`
//!       (`Nat.testBit_add_two_pow_self`), and its low bits are `testBit (2^k +
//!       val j') (val i) = testBit (val j') (val i)` (`Nat.testBit_add_two_pow_lo`,
//!       through `hcDecode_castP_addNat`).
//!
//!   In both branches `hcDecode (k+1) jS = S` is proved by `funext` over
//!   `Fin (k+1)` with `Fin.lastCases`:
//!
//!     - `castSucc` minor at `i : Fin k`: the bit equals `hcDecode k j' i`
//!       (by the corresponding `hcDecode_castP_*` correspondence), then `hj'`
//!       (applied via `congrFun`) rewrites `hcDecode k j' i = S' i ≡ S (castSucc i)`;
//!     - `last` minor: the top bit equals `<bit>` (the testBit fact above), then
//!       `hb.symm` rewrites `<bit> = S (last k)`.
//!
//!   Package each branch with `Exists.intro.{1}` (witness `jS`, the `funext`
//!   proof).
//!
//! Every leaf (`Nat.rec`, `Fin.lastCases`, `Bool.casesOn`, `funext`, `Exists.intro`,
//! the `hcDecode_castP_*` correspondences, `Nat.testBit_lt_pow`,
//! `Nat.testBit_add_two_pow_self`, `Nat.testBit_add_two_pow_lo`, `Eq.*`/`congrFun`,
//! `False.elim`/`Nat.not_succ_le_zero`) is `Constructive` with empty admitted-axiom
//! closure, so this theorem is too. No axiom is added or removed. Idempotent.

#![allow(clippy::too_many_arguments)]

#[cfg(test)]
use super::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use super::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
include!("boolean_analysis_hc_decode_surjective_build.rs");

#[cfg(test)]
impl Environment {
    /// Register `BoolAnalysis.hcDecode_surjective` — see the module docs.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    #[cfg(test)]
    pub(crate) fn register_hc_decode_surjective(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hcDecode_surjective");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_exists()?; // Exists, Exists.intro, Exists.elim
        self.init_funext()?; // funext (FOUNDATIONAL)
        self.init_boolean_analysis_foundations()?; // HCPoint, hcDecode, Fin.*
        self.register_fin_last_cases()?; // Fin.lastCases
        self.init_boolean_analysis_peel()?; // extendF / extendT
        self.init_boolean_analysis_peel_compute()?; // extendF/T_castSucc / _last
        self.init_boolean_analysis_noise_extend_bridge()?; // hcDecode_castP_*_extend* bridges + castP deps
        self.register_nat_not_succ_le_zero_theorem()?; // Nat.not_succ_le_zero (empty Fin 0)
        self.init_nat_top_level_ordering()?; // Nat.zero_lt_succ (constructive Theorem form)

        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = SurjConsts::new();
        let (type_, value) = build_surjective(&c);
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
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_hc_decode_surjective()
            .expect("register_hc_decode_surjective");
        env.register_hc_decode_surjective().expect("idempotent");
        env
    }

    #[test]
    fn test_hc_decode_surjective_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.hcDecode_surjective");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("hcDecode_surjective must kernel-check: {e:?}"));
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
}
