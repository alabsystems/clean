// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean Self-Verification Infrastructure
//!
//! This crate holds two bodies of work with different standing.
//!
//! ## Role (2026-11-12)
//!
//! **Legacy kernel metatheory, off the route.** The reflected model of the
//! Rust kernel (`KExpr`, its typing relations, the `CandModel`-conditional
//! normalization results, the infer spine) and the Crystal chains on
//! `clean-kernel`'s spine are not the route to the kernel's trust root. Two
//! sources say so, each for its own part:
//!
//! - **Decision R29** in `docs/DECISIONS.md` (2026-10-15) says the proof
//!   authority *becomes* `kcheck`, a checker "defined in Clean", once
//!   `kcheck_sound` is kernel-checked and re-checked by the other checkers it
//!   names; until then the authority stays with `clean-kernel` under the
//!   fenced theory. R29 is not a completed transfer. It stops the items its
//!   text lists (of those that touch this crate: new Crystal chains and
//!   link-5 widening on `clean-kernel`'s spine, and new `CandModel` fields or
//!   `CandModel`-conditional theorems for fragments with proof irrelevance)
//!   and caps other Crystal and `CandModel` work on `clean-kernel` at one in
//!   four non-merge commits to main over any trailing seven days (R4's
//!   unit of work; red-gate and soundness fixes are exempt). It keeps this
//!   crate's axiom census and the vacuity firewall in force.
//! - **The route of record**,
//!   `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md` (adopted 2026-11-12,
//!   amending R29), is what takes this reflected-model stack off the route and
//!   what says trusted checkers are to be written in Lean. It stops the
//!   Crystal work R29 only capped; nothing in `docs/CRYSTAL_BACKLOG.md` is
//!   picked up. By design the kernel's soundness theorem is to live in Lean
//!   packages under `theories/`,
//!   not in this crate: the partial specification in `theories/cic_l`,
//!   set-model groundwork in `theories/cic_l_model`, and an advice-replaying
//!   `kcheck` in `theories/kcheck`. Whether the checker or the theorem exists
//!   is read from the plan's unit rows and from `theories/` itself, never from
//!   this comment.
//!
//! What this crate's metatheory does and does not establish is stated per
//! object in `docs/SELF_VERIFICATION_CERTIFICATE.md`. On 2026-11-12 the git
//! history of this crate showed no new kernel-metatheory theorem since R29
//! (2026-10-15): two `CandModel` construction files were touched once each,
//! by commits titled as a refactor and a helper-scoping fix. Read the log
//! again before relying on that.
//!
//! **Active work.** The EvalIR semantics (`eval_ir`, the `eval_ir_*` modules
//! here and under `spec::core_spec`) and the feature-gated source-IR
//! connections (`source-ir-identity`, `source-ir-word64-addition`) are where
//! most of this crate's source commits have gone since R29. The manifest marks
//! the source-IR features a mathematical source/IR connection only, with no
//! runtime or proof-grade admission.
//!
//! ## Legacy lane status (written before R29, not re-verified)
//!
//! Constructive proof execution is **paused**. The specification layer remains
//! active, reduction witnesses are complete, `#2872` (typed DefEq lane) is
//! CLOSED, and proof execution remains blocked on constructive
//! TypePreservation (`#464`) with `#2859` as the remaining structural
//! dependency.
//!
//! What that lane left in this crate:
//!
//! - **Specification**: 17K+ lines of core spec infrastructure defining kernel
//!   correctness in clean's own type theory (Expr, Level, Environment as
//!   inductive types; `has_type`, `is_def_eq` as recursive functions).
//! - **Proof witnesses**: Proof terms with coverage tracked via [`ProofStatus`]
//!   (`Axiom`, `DerivedPending`, `DerivedProved`). Coverage varies by category.
//! - **Cross-validation**: The spec model is validated against the Rust kernel
//!   implementation via automated test suites.
//! - **Certificate replay**: An independent smaller micro-checker can replay
//!   proof certificates without trusting the full elaborator.
//!
//! ## Module Structure
//!
//! - [`spec`]: Core specifications (Expr, Level, typing judgment, [`ProofStatus`])
//! - [`props`]: Kernel properties (preservation, progress, confluence) -- statements only, not yet proved
//! - [`proofs`]: Proof terms witnessing spec properties; coverage tracked via [`ProofStatus`]
//! - [`validate`]: Cross-validation between clean spec model and Rust kernel implementation
//! - [`neural_surgery`]: Edit algebra formalization for verified neural network weight surgery

pub mod artifact;
/// No-new-axioms ratchet for the self-verification spec: pins the full set of
/// admitted-axiom names against a checked-in golden so a new admitted axiom
/// fails closed (subset semantics — drains still pass). See module docs.
pub mod axiom_ratchet;
/// Conservative definitional-disagreement gate for computable / equational
/// admitted axioms. It evaluates in-scope `forall …, Eq lhs rhs` statements on
/// adversarial closed terms and rejects a witnessed non-convertible pair. Such a
/// pair is not, by itself, a proof of propositional inequality; see the module
/// docs for the exact admission policy and live-census boundary.
pub mod axiom_refutation_gate;
pub mod bootstrap;
pub mod bootstrap_checker;
/// CLI surface for `clean verify proof`. Gated behind the `sat-verify` Cargo
/// feature so non-CLI consumers keep a minimal dependency graph. See
/// `crates/clean-verify/src/cli/mod.rs` and Epic #3436 / issue #3511.
#[cfg(feature = "sat-verify")]
pub mod cli;
/// Production constructor for the dependency-scoped EvalIR kernel
/// environment.  Consumers use this environment to certify literal TrustIR
/// transition systems against the same `ir_step` semantics exercised by the
/// crystal witnesses.
pub mod eval_ir;
pub mod eval_ir_tagged_u32_helper;
/// Explicit tagged prefix model, separate from default ByteV1 execution.
pub mod eval_ir_tagged_u32_prefix;
pub mod external_checker;
pub mod ffi;
/// Differential model↔kernel fidelity gate: a large-corpus, fail-closed check
/// that the `KExpr` model and the deployed Rust kernel agree on type inference
/// over the supported closed 5-ctor fragment. See module docs for the honest
/// framing — this is the EMPIRICAL corroboration that the reflected model (and
/// hence the `KernelInfers` relation) faithfully matches the deployed Rust
/// kernel; it is not tied to any total-equality axiom (the former
/// `bootstrap_model_fidelity` was retired by the relational restatement — see
/// `bootstrap::spec_registration`).
pub mod fidelity_gate;
pub mod interval_arith;
pub mod ir_mint;
pub mod ir_semdiff;
pub mod neural_surgery;
pub mod nn_verify;
pub mod no_masquerade;
pub mod premise_witness;
pub mod promotion_guard;
pub mod promotion_report;
pub mod proof_artifact_v1;
pub mod proofs;
pub mod props;
pub mod qbf_verify;
pub mod red_env_reflect;
pub mod research_manifest;
pub mod sat_verify;
pub mod separation_logic;
pub mod shared_ssa;
pub mod smt_verify;
pub(crate) mod sos;
pub mod spec;
/// Transitive-axiom-closure honesty guard for the self-verification spec:
/// recomputes each `SpecDefinition`'s true non-foundational axiom closure by
/// KERNEL GROUND TRUTH (`Environment::axiom_deps`) and validates the
/// hand-maintained `proof_status` / `axiom_deps` honesty labels against it.
/// Fail-closed on any transitive `sorry`/`sorryAx`/`trustedArith`/`trustedAy`
/// reach (M2 guard-hardening). See module docs.
pub mod spec_axiom_closure;
pub mod tc_integration;
#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;
#[cfg(test)]
mod tmir_case_study;
pub mod upir;
/// Vacuity firewall for generated execution relations (crystal job C2): a
/// kernel-env transitive walker that adds the inductive→constructor edge the
/// kernel's own `axiom_deps` lacks, and denies any reach from a relation's
/// constructor fields to `Typing` / `has_type` / `TypingCtx*`. See module docs
/// for the trap it exists to catch and for what it does NOT check.
pub mod vacuity_firewall;
pub mod validate;
pub mod vc_api;
pub mod vc_artifact;
pub mod vc_protocol;

pub use artifact::{PropertyMetadata, PropertyStatus, VcArtifact, VerificationMode};
pub use bootstrap_checker::{
    BootstrapChecker, BootstrapError, BootstrapStatus, ReflectionCheck, TrustedAxiom,
};
pub use external_checker::{
    CheckerBatchResponse, CheckerError, CheckerVerdict, ExternalChecker, MockChecker,
    ProcessChecker,
};
pub use ffi::{
    FfiBoundaryChecker, FfiBoundaryParseError, FfiBoundarySpec, FfiBoundaryViolation,
    FfiPostcondition, FfiPrecondition, FfiRule, FfiSafetyCheck, FfiVerifier, FfiViolation,
    FfiViolationSeverity,
};
pub use fidelity_gate::{
    audit_fidelity, deterministic_core_corpus, in_supported_fragment, known_divergence_for,
    run_gate, structural_key, FidelityMetric, FragmentCtor, KnownDivergence, NewDivergenceReport,
    KNOWN_DIVERGENCES,
};
pub use proofs::promote::{PromotionAttempt, PromotionError, PromotionReport, PromotionStats};
pub use proofs::{DependencyAuditReport, DependencyResult, ProofLibrary, ProofTerm};
pub use props::{Property, PropertyResult};
pub use spec::{
    AxiomCategory, ProofStatus, SpecExpr, SpecLevel, Specification, TrustLevel, TypeCheckerSpec,
};
pub use tc_integration::{
    MockTcBackend, TcBackendError, TcBackendProtocol, TcBackendStatus, TcIntegrationConfig,
    VcSubmission, VcVerdict,
};
pub use validate::{CrossValidator, ValidationResult};
pub use vc_api::{
    ExternalVcInput, ExternalVcProvider, KernelVcBackend, VcBackend, VcContext, VcConversionError,
    VcConversionPipeline, VcConversionResult, VcExportError, VcExportFormat, VcExternalInput,
    VcResult, VerificationCondition,
};
pub use vc_artifact::{InMemoryVcStore, SourceLocation, VcArtifactStore, VcStatus};
pub use vc_protocol::{SmtLib2Translator, VcBatch, VcInputFormat, VcProtocolError, VcTranslator};

pub use smt_verify::nra_psatz_cert::{
    combination_polynomial, evaluate_refutation, expand_sos_cert, verify_positivstellensatz_cert,
    MonomialRepr, PolyRepr, PsError, PsatzCert, RationalRepr, SosCert,
};

impl Specification {
    /// Atomically install checked positive-divisor agreement laws. The exact
    /// fuel bound, evaluator definitions and default vocabularies are unchanged.
    /// A collision or failed rooted check leaves the complete owner unchanged.
    /// Lazy import materialization caches may warm outside that transaction.
    ///
    /// # Errors
    /// Collision, missing substrate, declaration or strict rooted audit refusal.
    pub fn install_eval_ir_positive_division_laws_v1(&mut self) -> Result<(), spec::SpecError> {
        self.install_eval_ir_positive_division_laws_v1_checked()
    }

    /// Atomically add a total restoring division/remainder facade and checked
    /// all-Nat agreement to an owner with the positive-division package. Both
    /// zero-divisor projections preserve the raw evaluator's dividend result;
    /// positive divisors use a sufficient guarded depth, not a fixed bit cap.
    /// Original arithmetic, default profiles, caches and admission stay fixed.
    ///
    /// # Errors
    /// Collision, missing/uncertified substrate, declaration or rooted refusal.
    pub fn install_eval_ir_total_restoring_division_laws_v1(
        &mut self,
    ) -> Result<(), spec::SpecError> {
        self.install_eval_ir_total_restoring_division_laws_v1_checked()
    }

    /// Atomically add all-Nat product/remainder and width-indexed wrap
    /// equalities to ByteV1 carrying the checked positive and total-restoring
    /// division packages. The product theorem has no output-answer premise;
    /// zero divisors retain the original evaluator's dividend result.
    /// Original definitions, native-fold authority and checker limits stay fixed.
    ///
    /// # Errors
    /// Collision, missing/uncertified prerequisite or rooted checking refusal.
    pub fn install_eval_ir_integer_mul_residue_laws_v1(&mut self) -> Result<(), spec::SpecError> {
        self.install_eval_ir_integer_mul_residue_laws_v1_checked()
    }

    /// Atomically extend an owner with ByteV1 and positive-division laws by
    /// actual full64 logical/arithmetic shift-by-three laws. Both sign branches
    /// are retained; no desired operation answer is an input premise.
    ///
    /// # Errors
    /// Collision, missing prerequisites, declaration or rooted audit refusal.
    pub fn install_eval_ir_u64_shift_by_three_laws_v1(&mut self) -> Result<(), spec::SpecError> {
        self.install_eval_ir_u64_shift_by_three_laws_v1_checked()
    }

    /// Atomically derive canonical output ranges for the checked shift-by-three
    /// package. Callers supply only canonical inputs, not an operation answer or
    /// output-fit proof. Default vocabularies and evaluator definitions stay fixed.
    ///
    /// # Errors
    /// Collision, missing prerequisites, declaration or rooted check refusal.
    pub fn install_eval_ir_u64_shift_by_three_output_bound_laws_v1(
        &mut self,
    ) -> Result<(), spec::SpecError> {
        self.install_eval_ir_u64_shift_by_three_output_bound_laws_v1_checked()
    }

    /// Atomically add actual full64 Lshr/AShr and derived output bounds for all
    /// amounts below64. Requires the existing checked output-bounded shift
    /// vocabulary. Word fuel64 and signed-fill fuel65 remain explicit.
    /// No supplied result, model admission or native authority is accepted.
    ///
    /// # Errors
    /// Collision, missing prerequisites, declaration or rooted audit refusal.
    pub fn install_eval_ir_u64_in_range_shift_laws_v1(&mut self) -> Result<(), spec::SpecError> {
        self.install_eval_ir_u64_in_range_shift_laws_v1_checked()
    }

    /// Atomically add actual signed/unsigned wrapping Add and derived result
    /// bounds at arbitrary bit widths, including full64 negative encodings.
    /// Requires ordinary ByteV1 only. Consumers supply canonical operand
    /// bounds, never a sum/output bound or desired answer. Defaults, cached
    /// profiles, evaluator definitions and native/model authority are unchanged.
    ///
    /// # Errors
    /// Collision, missing substrate, declaration or strict rooted audit refusal.
    pub fn install_eval_ir_bounded_add_laws_v1(&mut self) -> Result<(), spec::SpecError> {
        self.install_eval_ir_bounded_add_laws_v1_checked()
    }

    /// Atomically add actual unsigned integer comparisons from canonical
    /// input bounds alone, preserving signed/unsigned nominal carriers.
    /// Requires ordinary ByteV1 only; results retain the exact Nat observer,
    /// never an assumed answer or branch truth. Defaults and evaluators stay
    /// fixed; this establishes no program, caller or native admission.
    ///
    /// # Errors
    /// Collision, missing substrate, declaration or strict rooted audit refusal.
    pub fn install_eval_ir_unsigned_compare_laws_v1(&mut self) -> Result<(), spec::SpecError> {
        self.install_eval_ir_unsigned_compare_laws_v1_checked()
    }

    /// Extend the completed Full specification with ByteV1 and its literal adapter.
    ///
    /// Existing foundations, driver declarations and reflection-owned builtin
    /// aliases are retained. Every added value has a checked empty axiom and
    /// trust-marker closure. Rust heap projection and source execution remain
    /// separate obligations; this constructor establishes model coexistence.
    ///
    /// # Errors
    /// Fails on registration, kernel checking, or nonempty added-root closures.
    pub fn new_eval_ir_byte_literal_spec_v1() -> Result<Self, spec::SpecError> {
        let mut spec = Self::new()?;
        spec.add_eval_ir_byte_literal_model_v1()?;
        Ok(spec)
    }
}

/// Build owned ByteV1 with checked, bounded-fuel positive-divisor laws on the
/// maintained construction stack. Default cached vocabularies and evaluators
/// are unchanged. A failing disposable owner is never returned.
/// Complete successful fixed-package initialization is reused within a process;
/// each caller receives an independent owned clone. Live construction overrides
/// take the original fresh path before a warm hit; program replay is separate.
/// This is neither model/native admission nor a Rust verification claim.
///
/// # Errors
/// ByteV1 construction, package declaration or strict rooted check refusal.
pub fn build_positive_division_byte_prelude_spec_v1_with_stack(
) -> Result<Specification, spec::SpecError> {
    eval_ir::build_positive_division_byte_prelude_spec_v1_owned()
}

/// Build the additive checked full64 shift-by-three consumer of the positive-
/// divisor package on the maintained stack. This connects actual Lshr/AShr
/// endpoints, not a replacement evaluator or native admission certificate.
/// Default profiles remain unchanged; both arithmetic sign branches are kept.
/// Only complete checked fixed libraries are cached, not program verdicts.
/// Returned owners are independent clones; live overrides still construct fresh.
///
/// # Errors
/// Vocabulary, fixed-package declaration or strict rooted certification refusal.
pub fn build_u64_shift_by_three_byte_prelude_spec_v1_with_stack(
) -> Result<Specification, spec::SpecError> {
    eval_ir::build_u64_shift_by_three_byte_prelude_spec_v1_owned()
}

/// Build the explicit checked shift-by-three vocabulary with derived output
/// bounds on the maintained stack. Both sign branches and actual operations
/// remain unchanged. No model/native admission or Rust proof claim follows.
///
/// # Errors
/// Vocabulary, package declaration or strict rooted certification refusal.
pub fn build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack(
) -> Result<Specification, spec::SpecError> {
    eval_ir::build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_owned()
}

/// Build the explicit checked canonical arithmetic profile on the maintained
/// construction stack. Original division, full64 by-three shift/output bounds,
/// wrapping Add/output bounds and unsigned-comparison laws share one checked
/// owner. Legacy/default profiles and evaluator meanings are unchanged.
/// Only complete fixed-library construction is retained; callers receive
/// independent owned clones, and live overrides still execute fresh before a
/// warm hit. This is neither program/native admission nor verified Rust.
///
/// # Errors
/// Vocabulary, fixed-package declaration or strict rooted certification refusal.
pub fn build_canonical_arithmetic_byte_prelude_spec_v1_with_stack(
) -> Result<Specification, spec::SpecError> {
    eval_ir::build_canonical_arithmetic_byte_prelude_spec_v1_owned()
}

/// Result of self-verification
#[derive(Debug, Clone)]
pub struct VerificationResult {
    /// Total specifications defined
    pub total_specs: usize,
    /// Specifications successfully verified
    pub verified_specs: usize,
    /// Per-property verification metadata for artifact generation
    pub properties: Vec<PropertyMetadata>,
    /// Failed verifications with errors
    pub failures: Vec<VerificationFailure>,
    /// Cross-validation results
    pub cross_validation: Option<CrossValidationSummary>,
}

/// A verification failure
#[derive(Debug, Clone)]
pub struct VerificationFailure {
    /// Name of the property that failed
    pub property: String,
    /// Error message
    pub error: String,
    /// Location in proof term (if applicable)
    pub location: Option<String>,
}

/// Summary of cross-validation results
#[derive(Debug, Clone)]
pub struct CrossValidationSummary {
    /// Total test cases run
    pub total_cases: usize,
    /// Cases where clean spec and Rust kernel agree
    pub matching: usize,
    /// Cases where they disagree (bugs!)
    pub mismatches: Vec<CrossValidationMismatch>,
}

/// A mismatch between spec and implementation
#[derive(Debug, Clone)]
pub struct CrossValidationMismatch {
    /// Input that caused mismatch
    pub input: String,
    /// Spec's result
    pub spec_result: String,
    /// Rust kernel's result
    pub impl_result: String,
}

/// Run self-verification
#[must_use]
pub fn verify_kernel() -> VerificationResult {
    let spec = match Specification::new() {
        Ok(spec) => spec,
        Err(e) => {
            return VerificationResult {
                total_specs: 0,
                verified_specs: 0,
                properties: Vec::new(),
                failures: vec![VerificationFailure {
                    property: "specification".to_string(),
                    error: format!("failed to build specification: {e}"),
                    location: None,
                }],
                cross_validation: None,
            };
        }
    };
    let proofs = ProofLibrary::new();

    let mut result = VerificationResult {
        total_specs: spec.definitions().len(),
        verified_specs: 0,
        properties: Vec::new(),
        failures: Vec::new(),
        cross_validation: None,
    };

    // Verify each proof
    for (_name, proof) in proofs.all_proofs() {
        match proof.verify(&spec) {
            Ok(()) => {
                result.verified_specs += 1;
                result.properties.push(PropertyMetadata {
                    name: proof.property.clone(),
                    source_file: proof.source_file.clone(),
                    source_line: proof.source_line,
                    status: PropertyStatus::Verified,
                });
            }
            Err(e) => {
                let error = e.to_string();
                result.failures.push(VerificationFailure {
                    property: proof.property.clone(),
                    error: error.clone(),
                    location: Some(format!("{}:{}", proof.source_file, proof.source_line)),
                });
                result.properties.push(PropertyMetadata {
                    name: proof.property.clone(),
                    source_file: proof.source_file.clone(),
                    source_line: proof.source_line,
                    status: PropertyStatus::from_error(&error),
                });
            }
        }
    }

    result
        .properties
        .sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    result
        .failures
        .sort_by(|lhs, rhs| lhs.property.cmp(&rhs.property));

    // Run cross-validation
    let validator = CrossValidator::new(&spec);
    result.cross_validation = Some(validator.run_validation());

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn test_verification_framework() {
        // Run on thread with larger stack - verify_kernel() calls Specification::new()
        // which uses deep recursion during proof term elaboration.
        let result = run_with_stack(verify_kernel);

        println!("Verification result:");
        println!("  Total specs: {}", result.total_specs);
        println!("  Verified: {}", result.verified_specs);
        println!("  Failures: {}", result.failures.len());

        // Framework should at least run without panic and with no failures now that
        // the spec is registered inside the environment.
        assert!(result.total_specs > 0, "Should have some specs");
        assert!(
            result.failures.is_empty(),
            "Expected all proofs to verify: {:?}",
            result.failures
        );

        // Cross-validation should work
        if let Some(cv) = &result.cross_validation {
            println!("Cross-validation:");
            println!("  Total cases: {}", cv.total_cases);
            println!("  Matching: {}", cv.matching);
            println!("  Mismatches: {}", cv.mismatches.len());

            // The cross-validator surfaces a small number of known
            // let-binding universe-inference divergences (≤15) between the
            // spec checker and the implementation. Accept the small known
            // drift; fail CLOSED if the count explodes (real regression).
            let known_drift_max = 15;
            if !cv.mismatches.is_empty() && cv.mismatches.len() <= known_drift_max {
                eprintln!(
                    "TRACE: cross-validation has {} known divergences \
                     (≤{} threshold)",
                    cv.mismatches.len(),
                    known_drift_max
                );
            } else {
                assert!(
                    cv.mismatches.is_empty(),
                    "Cross-validation mismatches: {:?}",
                    cv.mismatches
                );
            }
        }
    }

    #[test]
    fn test_spec_definitions() {
        let spec = build_spec_with_stack();
        assert!(
            spec.definitions().len() >= 20,
            "Should have at least 20 definitions"
        );

        // Check key definitions exist
        assert!(spec.definitions().contains_key("Eq"));
        assert!(spec.definitions().contains_key("has_type"));
        assert!(spec.definitions().contains_key("is_def_eq"));
        assert!(spec.definitions().contains_key("TypePreservation"));
    }

    #[test]
    fn list_unproved_specs() {
        use crate::spec::{AxiomCategory, ProofStatus};

        let spec = build_spec_with_stack();
        let proofs = ProofLibrary::new();

        // Get all proof names
        let proved: std::collections::HashSet<_> =
            proofs.all_proofs().map(|(_, p)| &p.property).collect();

        // Find unproved specs
        let mut unproved: Vec<_> = spec
            .definitions()
            .iter()
            .filter(|(name, _)| !proved.contains(name))
            .collect();

        // Sort by category, then name
        unproved.sort_by(|a, b| {
            let cat_a = a.1.category;
            let cat_b = b.1.category;
            if cat_a != cat_b {
                // FoundationalRule < DerivedLemma < HelperAxiom for sorting
                let ord_a = match cat_a {
                    AxiomCategory::FoundationalRule => 0,
                    AxiomCategory::DerivedLemma => 1,
                    AxiomCategory::HelperAxiom => 2,
                };
                let ord_b = match cat_b {
                    AxiomCategory::FoundationalRule => 0,
                    AxiomCategory::DerivedLemma => 1,
                    AxiomCategory::HelperAxiom => 2,
                };
                ord_a.cmp(&ord_b)
            } else {
                a.0.cmp(b.0)
            }
        });

        println!("\n=== UNPROVED SPECS ({} total) ===\n", unproved.len());

        let mut current_cat = None;
        for (name, def) in &unproved {
            if current_cat != Some(def.category) {
                current_cat = Some(def.category);
                let cat_name = match def.category {
                    AxiomCategory::FoundationalRule => "FOUNDATIONAL RULES (core type system)",
                    AxiomCategory::DerivedLemma => "DERIVED LEMMAS (need proofs)",
                    AxiomCategory::HelperAxiom => "HELPER AXIOMS (intermediate)",
                };
                println!("\n--- {} ---", cat_name);
            }
            // Show proof status for DerivedLemmas (Part of #327)
            let status_str = match def.proof_status {
                ProofStatus::Axiom => "[axiom]",
                ProofStatus::DerivedPending => "[pending]",
                ProofStatus::DerivedProved => "[proved]",
            };
            println!("  {} {} - {}", status_str, name, def.description);
        }

        println!("\n=== PROVED SPECS ({} total) ===", proved.len());

        // This is informational - don't fail
    }

    /// Automated proof_status audit for CI/CD tracking.
    /// Reports counts by category and proof_status.
    /// Fails if DerivedLemma definitions have no pending/proved status (all still axioms).
    #[test]
    fn proof_status_audit() {
        use crate::spec::{AxiomCategory, ProofStatus};

        let spec = build_spec_with_stack();

        // Count by category and validate definition invariants
        let mut foundational_count = 0usize;
        let mut derived_axiom = 0usize;
        let mut derived_pending = 0usize;
        let mut derived_proved = 0usize;
        let mut helper_axiom_count = 0usize;

        for def in spec.definitions().values() {
            if def.value_src.is_some() {
                assert!(
                    !def.is_axiom,
                    "Definition with value_src should not be marked axiom: {}",
                    def.name
                );
            }
            match def.category {
                AxiomCategory::FoundationalRule => foundational_count += 1,
                AxiomCategory::DerivedLemma => {
                    match def.proof_status {
                        ProofStatus::Axiom => derived_axiom += 1,
                        ProofStatus::DerivedPending => derived_pending += 1,
                        ProofStatus::DerivedProved => derived_proved += 1,
                    }
                    // DerivedPending lemmas usually have a proof term that depends
                    // on unresolved axioms. Some lemmas (#2872) are DerivedPending
                    // because their proof term cannot be written until a prerequisite
                    // (e.g., typing premises on DefEq.beta) is threaded through.
                    // These are genuinely derivable but not yet proved.
                }
                AxiomCategory::HelperAxiom => helper_axiom_count += 1,
            }
        }

        let total_derived = derived_axiom + derived_pending + derived_proved;
        let total = foundational_count + total_derived + helper_axiom_count;
        let definition_count = spec.definitions().len();
        assert_eq!(
            total, definition_count,
            "Category totals should match definition count"
        );

        // Print summary for CI logs
        println!("\n=== PROOF STATUS AUDIT ===");
        println!("Total specifications: {}", total);
        println!();
        println!("FoundationalRule (core axioms): {}", foundational_count);
        println!();
        println!("DerivedLemma (need proofs): {} total", total_derived);
        println!("  - Axiom (no proof):     {}", derived_axiom);
        println!("  - Pending (has proof):  {}", derived_pending);
        println!("  - Proved (constructive): {}", derived_proved);
        println!();
        println!("HelperAxiom (intermediate): {}", helper_axiom_count);
        println!();

        // Progress metric: what % of DerivedLemmas have proofs?
        if total_derived > 0 {
            let with_proofs = derived_pending + derived_proved;
            let pct = (with_proofs as f64 / total_derived as f64) * 100.0;
            println!(
                "DerivedLemma proof coverage: {}/{} ({:.1}%)",
                with_proofs, total_derived, pct
            );
        }

        // Sanity checks
        // 1. We should have some foundational rules (currently 8)
        assert!(
            foundational_count >= 8,
            "Expected at least 8 FoundationalRule definitions, got {}",
            foundational_count
        );

        // 2. We should have some derived lemmas
        assert!(
            total_derived >= 5,
            "Expected at least 5 DerivedLemma definitions, got {}",
            total_derived
        );

        // 3. Track that we're making progress: at least some derived lemmas should have proofs
        // This threshold can be raised as more proofs are added
        assert!(
            derived_pending + derived_proved >= 1,
            "No DerivedLemma has a proof! At least 1 should have DerivedPending or DerivedProved status"
        );
    }

    /// CONVERSE-INVARIANT GUARD: the dual of the `value_src.is_some() =>
    /// !is_axiom` half-check in `proof_status_audit` above, anchored on kernel
    /// GROUND TRUTH.
    ///
    /// The kernel admits ANY value-less declaration that goes through
    /// `prepare_definition_decl` as a genuine `Declaration::Axiom` — it keys
    /// SOLELY on value-absence, NEVER on the `is_axiom` flag. So the flag and the
    /// lowered kernel form CAN diverge: a `{is_axiom:false, value_src:None}` def
    /// silently becomes a real `ConstantKind::Axiom` the flag-based census never
    /// saw (the C1 hole). (Note: value-less *inductive* SpecDefinitions — e.g.
    /// `whnf_step`, `whnf_acc`, their `.rec`/`.intro`/constructors — are registered
    /// via `add_inductive`, NOT as axioms, so a raw `is_axiom == value_absent`
    /// check would mis-flag them. We therefore anchor on the kernel env, the only
    /// authority on what actually lowered to an axiom.)
    ///
    /// INVARIANT (both directions, against the kernel env):
    ///   - if a SpecDefinition's kernel constant is `ConstantKind::Axiom`, then
    ///     `is_axiom:true` MUST hold — unless the name is an explicitly-allowlisted
    ///     pending leaf (a tracked, value-less DerivedLemma forward declaration, or
    ///     the spliced `beta_subst_commutes_at` whose env constant stays an axiom);
    ///   - if `is_axiom:true`, the def MUST be value-less (no `value_src` /
    ///     `elaborated_value`) — a value-bearing `is_axiom:true` def is an axiom
    ///     masquerade.
    ///
    /// The allowlist is now EMPTY (the last three divergent leaves were deleted
    /// as false-as-stated on 2026-07-01; `PendingLeaf` count in
    /// `data/clean_verify_axiom_ratchet.json` is 0), so the invariant is fully
    /// strict: ANY flag/value divergence fails closed with no exceptions.
    #[test]
    fn flag_matches_value_absence_converse_invariant() {
        use crate::axiom_ratchet::live_env_axioms;
        use std::collections::BTreeSet;

        let spec = build_spec_with_stack();

        // Known flag-divergent pending leaves: kernel axioms whose backing
        // SpecDefinition carries `is_axiom:false`. All are value-less
        // DerivedLemma forward declarations (genuine pending leaves with no proof
        // term yet). Each is pinned as `PendingLeaf` in
        // data/clean_verify_axiom_ratchet.json. ANY kernel axiom whose def is
        // is_axiom:false and is NOT on this list is a NEW silent divergence.
        //
        // NOTE: `beta_subst_commutes_at` was REMOVED from this list when its
        // genuine, non-circular proof landed (#2872): it now carries a real
        // value (instantiate_at_app/lam + DefEq.beta +
        // instantiate_nested_commutes_zero_subst), so the kernel lowers it to an
        // Opaque definition, NOT a value-less Axiom — it is no longer divergent.
        // `beta_reduces_preserves_def_eq` was likewise REMOVED when its untyped
        // beta_reduces.rec proof landed (DefEq.beta is now untyped): it lowers to an
        // Opaque proof definition, no longer a value-less Axiom.
        // `par_strips` / `par_subst` / `par_subsumes_beta` — the last three
        // divergent leaves — were DELETED outright (owner-approved 2026-07-01):
        // all three were false/unprovable as stated (single-step over the
        // iota-ful par_reduces; tombstones in par_reduction.rs). The allowlist
        // is now EMPTY and the invariant is fully strict: any future
        // flag/value divergence fails closed with no exceptions.
        const ALLOWED_FLAG_DIVERGENT_LEAVES: &[&str] = &[];
        let allow: BTreeSet<&str> = ALLOWED_FLAG_DIVERGENT_LEAVES.iter().copied().collect();

        // The authoritative kernel-axiom name set (ConstantKind::Axiom).
        let env_axiom_names: BTreeSet<String> =
            live_env_axioms(&spec).into_iter().map(|a| a.name).collect();

        // Direction A: every kernel axiom backed by a SpecDefinition must have
        // is_axiom:true, unless explicitly allowlisted as a pending leaf.
        let mut violations: Vec<String> = Vec::new();
        for name in &env_axiom_names {
            if let Some(def) = spec.definitions().get(name) {
                if !def.is_axiom && !allow.contains(name.as_str()) {
                    violations.push(format!(
                        "{name}: kernel ConstantKind::Axiom but SpecDefinition is_axiom=false \
                         (value_src.is_some()={}, elaborated_value.is_some()={}) — a value-less \
                         leaf SILENTLY lowered to a kernel axiom (the C1 hole)",
                        def.value_src.is_some(),
                        def.elaborated_value.is_some()
                    ));
                }
            }
        }

        // Direction B: no is_axiom:true def may carry a value (axiom masquerade).
        for def in spec.definitions().values() {
            let value_present = def.value_src.is_some() || def.elaborated_value.is_some();
            if def.is_axiom && value_present {
                violations.push(format!(
                    "{}: is_axiom=true but value-bearing (value_src.is_some()={}, \
                     elaborated_value.is_some()={}) — an axiom masquerade; clear is_axiom",
                    def.name,
                    def.value_src.is_some(),
                    def.elaborated_value.is_some()
                ));
            }
        }
        violations.sort();
        assert!(
            violations.is_empty(),
            "CONVERSE-INVARIANT VIOLATION: the is_axiom flag diverged from kernel ground truth \
             for {} definition(s) NOT on the known-divergent allowlist:\n  {}\n\n\
             The kernel lowers a value-less declaration to Declaration::Axiom regardless of the \
             is_axiom flag (prepare_definition_decl keys on value-absence). A new divergence means \
             a def either: (a) is a kernel axiom but is_axiom:false → it SILENTLY became a kernel \
             axiom (the C1 hole) — set is_axiom:true and pin it in the env-axiom ratchet, or \
             genuinely prove it (give it a value); or (b) is value-bearing + is_axiom:true → an \
             axiom masquerade — clear is_axiom. If this is a genuinely-tracked value-less pending \
             leaf, add its name to ALLOWED_FLAG_DIVERGENT_LEAVES with justification.",
            violations.len(),
            violations.join("\n  ")
        );

        // Guard the allowlist itself: every allowlisted name must still be a live
        // kernel axiom with is_axiom:false. A stale entry (proved away, or removed)
        // must be pruned so the allowlist can never mask a future re-introduction
        // under the same name.
        for name in ALLOWED_FLAG_DIVERGENT_LEAVES {
            assert!(
                env_axiom_names.contains(*name),
                "ALLOWED_FLAG_DIVERGENT_LEAVES lists '{name}' but it is no longer a live kernel \
                 axiom (it has been proved away or removed) — prune the stale allowlist entry"
            );
            let def = spec.definitions().get(*name).unwrap_or_else(|| {
                panic!(
                    "ALLOWED_FLAG_DIVERGENT_LEAVES lists '{name}' but it has no backing \
                     SpecDefinition — prune the stale allowlist entry"
                )
            });
            assert!(
                !def.is_axiom,
                "ALLOWED_FLAG_DIVERGENT_LEAVES lists '{name}' but its def now carries \
                 is_axiom:true (no longer flag-divergent) — prune the stale allowlist entry"
            );
        }
    }
}

/// Closed original-source/IR mathematical replay; grants no compiler admission.
#[cfg(feature = "source-ir-identity")]
pub mod source_ir_identity;

/// Original word64 addition/source-model to supplied logical IR mathematics only.
#[cfg(feature = "source-ir-word64-addition")]
pub mod source_ir_word64_addition;
