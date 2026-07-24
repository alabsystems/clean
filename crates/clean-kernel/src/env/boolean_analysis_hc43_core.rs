// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3, 4)` campaign — `hc43_core`, the `(4/3,4)`-hypercontractivity
//! operator bound, assembled by `Nat.rec` from the base case (`hc43_core_base`)
//! and the induction step (taken as an explicit minor-premise hypothesis). The
//! dual of `hc24_core`.
//!
//! ```text
//! BoolAnalysis.hc43_core :
//!   ∀ (ρ : Rat) (n : Nat),
//!     Rat.le (3·(ρ·ρ)) 1 →
//!     (h_step : ∀ (m : Nat), motive m → motive (m+1)) →
//!       motive n
//! ```
//!
//! where the **motive** carries the full per-level witness bundle INSIDE the
//! recursion (so the step may instantiate it at `gPart m F`, `liftH m F`, and
//! their scaling witnesses):
//!
//! ```text
//!   motive m := ∀ (F s r : HCPoint m → Rat)
//!                 (hs : ∀ x, 0 ≤ s x)(hr : ∀ x, 0 ≤ r x)(hr1 : ∀ x, r x < 1)
//!                 (hrecon : ∀ x, |F x| = ((s x·s x)·s x)·r x)
//!                 (hnn : ∀ jx, 0 ≤ pow4 (noiseFn ρ m F jx))(h4n : 0 ≤ powNat 4 m),
//!                 <hc43_core_concl ρ m F s r hs hnn h4n>.
//! ```
//!
//! ## Assembly (dual of `hc24_core`)
//!
//! `ρ`, `n`, `h : 3·(ρ·ρ) ≤ 1`, and `h_step : ∀ m, motive m → motive (m+1)` are
//! bound; then `Nat.rec` with the motive above:
//!
//! - **base** `motive 0` is supplied by `hc43_core_base ρ` with the witness
//!   bundle re-bound INSIDE the motive shape and the captured `h` fed to its
//!   contraction slot,
//! - **step** is the explicit hypothesis `h_step` directly.
//!
//! `(Nat.rec motive base h_step n) : motive n` is the body. This is the GENUINE
//! `Nat.rec` tensorization, CONDITIONAL on the induction step `h_step` (the
//! `(4/3,4)` cross-term tower of design §11 — the LANDED `cube_minkowski_merge` /
//! `cube_superadd` / `finSum_cube_split` bricks discharge its rational core; the
//! cubed-AM-GM `27P²Q ≤ (2P+Q)³` residual is the named open rung). `h_step` is an
//! explicit minor premise, NOT an axiom — exactly as `hc24_core` takes its
//! `3·ρ²≤1` contraction hypothesis, and `hc43_core_base` is a genuine kernel
//! proof.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure): the
//! only leaves are `hc43_core_base` (Constructive), `Nat.rec`, and the explicit
//! `h_step` hypothesis (no axiom in the closure).

use super::boolean_analysis_hc43_core_base::{
    forall_lhs_nonneg_ty, forall_r_lt_one_ty, forall_r_nonneg_ty, forall_recon_ty,
    forall_scale_nonneg_ty, hc43_core_concl, hyp_contract_ty, Hc43Consts,
};
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

include!("boolean_analysis_hc43_core_motive.rs");

impl Environment {
    /// Register `BoolAnalysis.hc43_core` — the full `(4/3,4)`-hypercontractivity
    /// operator induction, CONDITIONAL on the explicit step hypothesis `h_step`.
    /// Idempotent; axiom-free (closure = base + Nat.rec + the explicit premise).
    pub fn init_boolean_analysis_hc43_core(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_hc43_core_base()?; // hc43_core_base + statement deps

        let name = Name::from_string("BoolAnalysis.hc43_core");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Hc43Consts::new();
        let (type_, value) = build_hc43_core(&c);
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
    fn test_hc43_core_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_hc43_core()
            .expect("init_boolean_analysis_hc43_core");
        env.init_boolean_analysis_hc43_core().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.hc43_core");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("hc43_core proof must check against its type");
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
