// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boolean analysis spec registration for the clean specification system.
//!
//! Registers the kernel-level theorem surfaces (S41-S43, S46, S50) as spec
//! definitions so that the `ProofLibrary` dependency audit can track them.
//!
//! All five live declarations are `Declaration::Theorem` (kernel-checked, with
//! an empty admitted-axiom closure — see
//! `clean_kernel::env::boolean_analysis_theorems`), so the metadata records
//! `is_axiom: false` / `AxiomCategory::DerivedLemma` /
//! `ProofStatus::DerivedProved`. The former `is_axiom: true` /
//! `ProofStatus::Axiom` values were stale: they survived the kernel-side
//! axiom→theorem retirement and made the spec census claim four admitted axioms
//! the kernel does not hold. `register_existing_definition` copies the live type
//! but does NOT re-derive these flags, so they are maintained here and
//! cross-checked by `crate::axiom_refutation_gate::run_gate`, which fails closed
//! when a spec-marked axiom does not lower to a live `ConstantKind::Axiom`.
//!
//! Part of #3333: Audit and fix placeholder DerivedProved proofs.

use std::collections::HashSet;

use crate::spec::{AxiomCategory, ProofStatus, SpecDefinition, SpecError, Specification};

impl Specification {
    /// Register Boolean analysis theorem surfaces as spec definitions.
    ///
    /// These are kernel-level theorems from `Environment::init_boolean_analysis()`.
    /// Registering them here lets the proof library's dependency audit resolve
    /// the `BoolAnalysis.*` property names correctly.
    ///
    /// Uses `register_existing_definition` because the declarations are already
    /// present in the environment after `init_boolean_analysis()` — calling
    /// `add_definition` would fail with `DuplicateName`.
    pub(crate) fn add_boolean_analysis_spec(&mut self) -> Result<(), SpecError> {
        // Ensure the kernel-level BoolAnalysis types (BoolFn, FourierCoeff, etc.)
        // and theorem declarations are present in the environment so that the
        // proof verifier can resolve types for these property names.
        self.env_mut()
            .init_boolean_analysis()
            .map_err(|e| SpecError::TypeError(format!("init_boolean_analysis: {e}")))?;

        // ── S41: Parseval's identity ────────────────────────────────────
        self.register_existing_definition(SpecDefinition {
            name: "BoolAnalysis.parseval_identity".to_string(),
            type_src: "(kernel theorem — type from environment)".to_string(),
            value_src: None,
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            description: "S41: Parseval's identity — the sum of squared Fourier \
                          coefficients equals E[f^2]. Kernel-checked theorem via \
                          subsetSum_parseval_core, with empty admitted-axiom closure. \
                          Ref: O'Donnell, Theorem 1.10."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S42: Influence-Fourier identity ─────────────────────────────
        self.register_existing_definition(SpecDefinition {
            name: "BoolAnalysis.influence_fourier".to_string(),
            type_src: "(kernel theorem — type from environment)".to_string(),
            value_src: None,
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            description: "S42: Influence-Fourier identity — the influence of variable i \
                          equals sum of hat{f}(S)^2 over S containing i. Kernel-checked \
                          theorem via the constructive influence/Fourier chain, with empty \
                          admitted-axiom closure. \
                          Ref: O'Donnell, Proposition 2.17."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S46: Total influence identity ───────────────────────────────
        self.register_existing_definition(SpecDefinition {
            name: "BoolAnalysis.total_influence_identity".to_string(),
            type_src: "(kernel theorem — type from environment)".to_string(),
            value_src: None,
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            description: "S46: Total influence identity — I(f) = sum_S |S| * hat{f}(S)^2. \
                          Kernel-checked theorem by definitional unfolding of \
                          TotalInfluence, with empty admitted-axiom closure. \
                          Ref: O'Donnell, Proposition 2.18."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S50: Bonami-Beckner hypercontractivity ──────────────────────
        self.register_existing_definition(SpecDefinition {
            name: "BoolAnalysis.bonami_beckner".to_string(),
            type_src: "(kernel theorem — type from environment)".to_string(),
            value_src: None,
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            description: "S50: Bonami-Beckner hypercontractivity — ||T_rho f||_q <= ||f||_p \
                          when rho^2 <= (p-1)/(q-1). The live declaration is a \
                          kernel-checked theorem in the modeled \
                          (2,4) regime via hc24_core, with empty admitted-axiom closure. \
                          Ref: Bonami (1970), Beckner (1975); O'Donnell Ch. 9."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // ── S43: KKL inequality ─────────────────────────────────────────
        self.register_existing_definition(SpecDefinition {
            name: "BoolAnalysis.kkl_inequality".to_string(),
            type_src: "(kernel theorem — type from environment)".to_string(),
            value_src: None,
            is_axiom: false,
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            description: "S43: KKL inequality — genuine max-influence bound. RETIRED to a \
                          kernel-CHECKED constructive Theorem (KKL finish): the helper is a \
                          reducible Definition carrying the genuine max-influence statement and \
                          kkl_inequality is proved by kkl_exists_max_influence (conditional sharp \
                          KKL fed through the general-n pigeonhole; empty admitted-axiom closure). \
                          Ref: Kahn, Kalai, Linial, FOCS 1988; O'Donnell, Theorem 9.28."
                .to_string(),
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}
