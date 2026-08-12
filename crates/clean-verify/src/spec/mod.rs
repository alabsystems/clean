// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel Specification in clean Type Theory
//!
//! This module defines a model of the clean kernel as clean inductive types
//! and recursive functions. This specification serves as the formal definition
//! of "what the kernel should do."
//! ## Module Structure
//!
//! - `types`: Core type definitions (SpecExpr, SpecLevel, AxiomCategory, ProofStatus, TrustLevel)
//! - `definition`: SpecDefinition struct and methods
//! - `core_spec`: Core type theory specification definitions (add_core_spec impl)
//! - `error`: SpecError type
//!
//! ## Scope: KExpr as Intentional Subset
//!
//! The `KExpr` inductive models nine expression forms: sort, bvar, app, lam,
//! pi, const, let, projection, and natural literal. It is still a subset of
//! the production kernel expression surface: unsupported production forms and
//! metadata must not be inferred from the reflected theorems.
//!
//! See `SCOPE.md` for full documentation of what is and isn't modeled.
//!
//! ## Design
//!
//! We use clean's type theory to express:
//! - Expr, Level as inductive types
//! - has_type(env, ctx, e, T) as a predicate
//! - is_def_eq(env, a, b) as a predicate
//! - whnf(env, e) as a function
//!
//! The specification is written using clean surface syntax, which is then
//! elaborated and type-checked by the kernel.

mod core_spec;
mod declaration_registration;
mod definition;
mod definition_registration;
mod error;
mod reducible;
mod tc_spec;
#[cfg(test)]
mod tests;
mod type_checker_spec;
mod type_checker_spec_algorithm;
mod types;
mod verification;

pub use definition::SpecDefinition;
pub use error::SpecError;
pub use type_checker_spec::{
    check_defeq_spec, check_type_spec, CompletenessWitness, DefeqAlgorithm, TypeCheckStep,
    TypeCheckerSpec,
};
pub use types::{AxiomCategory, ProofStatus, SpecExpr, SpecLevel, TrustLevel};

use clean_kernel::Environment;
use std::collections::HashMap;

/// The complete kernel specification
#[derive(Debug)]
pub struct Specification {
    /// Environment with specification definitions
    env: Environment,
    /// Named definitions
    definitions: HashMap<String, SpecDefinition>,
    /// Fresh generated red-environment script to consume at the corresponding
    /// core-bundle stage. `None` uses the committed `include_str!` artifact.
    ///
    /// This is transient: `add_kernel_core_red_env` takes and clears it. It
    /// exists so the generator can build the complete live specification
    /// against the freshly rendered script before publishing any file.
    red_env_script_override: Option<String>,
}

impl Specification {
    /// Create a new specification with standard definitions
    ///
    /// # Errors
    /// Returns `SpecError` if specification construction fails.
    pub fn new() -> Result<Self, SpecError> {
        Self::new_with_optional_red_env_script(None)
    }

    /// Build the complete specification while injecting a freshly rendered
    /// red-environment script at the normal core-bundle stage.
    ///
    /// The reflection generator uses this artifact-independent path to prove
    /// that the exact in-memory script can support every downstream full-spec
    /// registration before it replaces the committed artifact.
    ///
    /// # Errors
    /// Returns `SpecError` if the script or any downstream full-spec stage
    /// fails parsing, elaboration, or kernel checking.
    #[doc(hidden)]
    pub fn new_with_red_env_reflection_script(script: &str) -> Result<Self, SpecError> {
        Self::new_with_optional_red_env_script(Some(script.to_string()))
    }

    fn new_with_optional_red_env_script(
        red_env_script_override: Option<String>,
    ) -> Result<Self, SpecError> {
        let mut spec = Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override,
        };

        // Add core type theory specification.
        spec.add_core_spec()?;
        if spec.red_env_script_override.is_some() {
            return Err(SpecError::TypeError(
                "fresh red-environment script was not consumed by the full core bundle".to_string(),
            ));
        }
        spec.add_type_checker_spec()?;
        // tc_spec registers algorithmic-correctness definitions
        // (tc_infer_type_correct, tc_def_eq_transitivity, …). Without this
        // call, the ProofLibrary's matching proof terms in
        // proofs/library_type_checker_spec.rs would fail with
        // "Unknown property: tc_infer_type_correct" during verify_kernel.
        spec.add_tc_spec()?;

        // Discharge the `Nat.shiftRight` EnvInjected axiom: the kernel's
        // `register_nat_shiftright_def` installs the real reducible Definition
        // `Nat.shiftRight := fun m n => Nat.iterDiv2 n m` (same `Nat → Nat → Nat`
        // type), so the constant stops being a value-less `ConstantKind::Axiom`
        // and drops out of the self-verification census. The routine calls its
        // own deps (`init_nat` / `register_nat_div2_lt_self_proof` /
        // `register_nat_testbit_def`) idempotently and is itself idempotent, so
        // this is safe regardless of build order. Mirrors how `init_bool` is
        // already invoked through `env_mut()` in `add_foundation_types`.
        spec.env_mut()
            .register_nat_shiftright_def()
            .map_err(|e| SpecError::EnvError(e.to_string()))?;

        Ok(spec)
    }

    /// Get the environment
    #[must_use]
    pub fn env(&self) -> &Environment {
        &self.env
    }

    /// Get mutable access to the environment.
    ///
    /// Used by spec registration stages that need to initialize kernel-level
    /// declarations before registering spec definitions (e.g., boolean analysis
    /// axioms). Part of #3333.
    pub(crate) fn env_mut(&mut self) -> &mut Environment {
        &mut self.env
    }

    /// Get all definitions
    #[must_use]
    pub fn definitions(&self) -> &HashMap<String, SpecDefinition> {
        &self.definitions
    }

    /// Get mutable access to definitions (for promotion pipeline).
    ///
    /// Part of #3221: Needed to update proof_status from DerivedPending
    /// to DerivedProved when proofs are validated.
    pub fn definitions_mut(&mut self) -> &mut HashMap<String, SpecDefinition> {
        &mut self.definitions
    }

    /// Get a definition by name
    #[must_use]
    pub fn get_definition(&self, name: &str) -> Option<&SpecDefinition> {
        self.definitions.get(name)
    }

    /// Get axiom category statistics for Phase 4 tracking
    ///
    /// Returns (foundational, derived, helper) counts:
    /// - foundational: Core modeling rules classified as foundational (they
    ///   may now be checked inductives, definitions, or theorems)
    /// - derived: Lemmas that should eventually have constructive proofs
    /// - helper: Intermediate axioms that may be derived in future
    #[must_use]
    pub fn axiom_category_stats(&self) -> (usize, usize, usize) {
        let mut foundational = 0;
        let mut derived = 0;
        let mut helper = 0;
        for def in self.definitions.values() {
            match def.category {
                AxiomCategory::FoundationalRule => foundational += 1,
                AxiomCategory::DerivedLemma => derived += 1,
                AxiomCategory::HelperAxiom => helper += 1,
            }
        }
        (foundational, derived, helper)
    }

    /// Get all derived lemmas that are still missing proofs (value_src: None)
    #[must_use]
    pub fn derived_lemmas_without_proofs(&self) -> Vec<&str> {
        self.definitions
            .values()
            .filter(|def| def.category == AxiomCategory::DerivedLemma && def.value_src.is_none())
            .map(|def| def.name.as_str())
            .collect()
    }
}

impl Default for Specification {
    fn default() -> Self {
        Self::new().expect("specification construction should succeed")
    }
}
