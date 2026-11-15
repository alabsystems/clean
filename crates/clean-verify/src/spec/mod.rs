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
//! pi, const, let, projection, and a tagged Nat/String literal leaf. It is still a subset of
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

pub use core_spec::{
    ir_br_module_defs, ir_fc_module_defs, ir_frm_module_defs, ir_frr_module_defs,
    ir_frs_module_defs, ir_fs_module_defs, ir_fw_module_defs, ir_gc_module_defs, ir_h2_module_defs,
    ir_hlb_module_defs, ir_ko_module_defs, ir_ni_module_defs, ir_pv_module_defs, ir_sm_module_defs,
    ir_sm_semdiff_defs, ir_vc_module_defs, ir_w2a_ee_module_defs, ir_w2a_sel_module_defs,
    ir_w2a_ud_module_defs, ir_w2a_uo_module_defs, ir_w2a_ur_module_defs, ir_w2b_al_module_defs,
    ir_w2b_pd_module_defs, ir_w2b_pm_module_defs, ir_w2b_pp_module_defs, ir_w2c_ci_module_defs,
    ir_w2c_ga_module_defs, ir_w3_os_module_defs, ir_w3_ou_module_defs, ir_w4_fc_module_defs,
    ACCEPTS_IN_PROOF_NAMES, ACCEPTS_TC_NAT_NAME_ALIASES, ACCEPTS_TC_QUOT_NAME_ALIASES,
    ACCEPTS_TC_STRING_NAME_ALIASES, BMEM_CORE_NAMES, BMEM_TRIE_NAMES, CTR_NAMES, CTR_STACK_NAMES,
    E5_NAMES, ITF_NAMES, IT_PC_NAMES, IT_SCTR_NAMES, LZD_PC_NAMES, LZD_SCTR_NAMES,
    NATIVE_NAT_PROOF_NAMES, SLOT_LEMMA_NAMES, STACK_AXES_MINTED_NAMES, STACK_AXES_NAMES,
    STACK_AXES_WITNESS_NAMES, STACK_MINTED_NAMES, STACK_SPLIT_NAMES, STACK_THEOREM_NAMES,
    STK_WITNESS_NAMES, STRING_LITERAL_PROOF_NAMES, STRING_LIT_CODEC_PROOF_NAMES,
};
pub(crate) mod decl_budget;
mod declaration_registration;
mod definition;
mod definition_registration;
mod error;
mod model_units;
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
pub(crate) use model_units::ModelUnitSource;
pub use type_checker_spec::{
    check_defeq_spec, check_type_spec, CompletenessWitness, DefeqAlgorithm, TypeCheckStep,
    TypeCheckerSpec,
};
pub use types::{AxiomCategory, ProofStatus, SpecExpr, SpecLevel, TrustLevel};

use clean_kernel::Environment;
use std::collections::HashMap;

/// The complete kernel specification
///
/// `Clone` is a deep copy of every owned map: the term DAG underneath is
/// immutable (`Arc<Expr>` children, interned `Arc` name components, no interior
/// mutability anywhere in `clean-kernel`), so a clone shares structure but
/// cannot observe another clone's registrations or `proof_status` edits. That
/// is what lets `test_utils` build the specification once per process and hand
/// every caller an independent copy instead of rebuilding it ~700 times.
#[derive(Debug, Clone)]
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
    /// Fresh semantic-name table paired with a generated script. Early literal
    /// aliases must consume it before the late red-environment registration.
    red_env_interning_override: Option<String>,
    /// Where `register_model_unit` reads the `.clean` model units from. Always
    /// the files in production; the fidelity oracle switches it to the
    /// retained literals or to a planted text (`model_units.rs`).
    model_unit_source: ModelUnitSource,
}

impl Specification {
    /// Create a new specification with standard definitions
    ///
    /// # Errors
    /// Returns `SpecError` if specification construction fails.
    pub fn new() -> Result<Self, SpecError> {
        Self::new_with_optional_red_env_script(None, None)
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
        Self::new_with_optional_red_env_script(Some(script.to_string()), None)
    }

    /// Validate a fresh script and its semantic-name table through the entire
    /// specification before either artifact is published. Early builtin aliases
    /// consume this table instead of requiring the old committed table to know
    /// names newly reserved by the generator.
    ///
    /// # Errors
    /// Returns `SpecError` for a malformed table or any failed full-spec stage.
    #[doc(hidden)]
    pub fn new_with_red_env_reflection_artifacts(
        script: &str,
        interning: &str,
    ) -> Result<Self, SpecError> {
        crate::red_env_reflect::parse_interning_tsv(interning)
            .map_err(|error| SpecError::EnvError(error.to_string()))?;
        Self::new_with_optional_red_env_script(
            Some(script.to_string()),
            Some(interning.to_string()),
        )
    }

    /// Resolve a model builtin or named witness through the same validated
    /// semantic-name table as the generated reduction environment. This is a bounded adapter,
    /// not a representation theorem for arbitrary structural kernel names.
    pub(crate) fn reflected_name_tag(&self, name: &str) -> Result<u64, SpecError> {
        crate::red_env_reflect::name_tag_in_table(
            self.red_env_interning_override
                .as_deref()
                .unwrap_or(crate::red_env_reflect::COMMITTED_INTERNING_TSV),
            name,
        )
        .map_err(|error| SpecError::EnvError(error.to_string()))
    }

    fn new_with_optional_red_env_script(
        red_env_script_override: Option<String>,
        red_env_interning_override: Option<String>,
    ) -> Result<Self, SpecError> {
        let mut spec = Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override,
            red_env_interning_override,
            model_unit_source: ModelUnitSource::default(),
        };
        // The same opt-out as `core_spec::Specification::new_empty`, which
        // carries the full rationale and the measurements. Both constructors
        // need it: this one serves `Specification::new()` (the full spec),
        // that one serves the bundle constructors.
        spec.env
            .set_option("relaxedAutoImplicit".to_string(), Some("false".to_string()));

        // Arm the kernel's ambient per-declaration runaway guard for the whole
        // build, and restore the thread's previous budget on the way out.
        //
        // WHY, measured: without it a single non-terminating declaration hangs
        // this constructor forever with no diagnostic — `ir_f64_w_fin_renormalise`
        // did exactly that for 7h48m at 100% CPU, taking every spec-paying test
        // target with it. Armed, the same shape is a named
        // `SpecError::DeclarationBudgetExhausted`. See `decl_budget` for the
        // bound, where its number comes from, and what it does NOT catch.
        //
        // Armed HERE and not around `Environment::new()`: the budget bounds the
        // spec's own declarations, not the fixed cost of standing up the
        // environment they are registered into — the same placement rule
        // `clean check` follows (`cmd_core.rs:184`).
        decl_budget::with_spec_declaration_budget(|| Self::build_stages(&mut spec))?;

        Ok(spec)
    }

    /// The registration stages of a full specification, run under an armed
    /// per-declaration budget by [`Self::new`].
    fn build_stages(spec: &mut Specification) -> Result<(), SpecError> {
        // Add core type theory specification.
        spec.add_core_spec()?;
        if spec.red_env_script_override.is_some() {
            return Err(SpecError::TypeError(
                "fresh red-environment script was not consumed by the full core bundle".to_string(),
            ));
        }
        // A stage-level refill, so a stage that registers declarations WITHOUT
        // going through `add_definition`/`add_inductive` (which refill
        // per-declaration) still starts from a full pot rather than inheriting
        // whatever the previous stage left.
        decl_budget::begin_declaration();
        spec.add_type_checker_spec()?;
        // tc_spec registers algorithmic-correctness definitions
        // (tc_infer_type_correct, tc_def_eq_transitivity, …). Without this
        // call, the ProofLibrary's matching proof terms in
        // proofs/library_type_checker_spec.rs would fail with
        // "Unknown property: tc_infer_type_correct" during verify_kernel.
        decl_budget::begin_declaration();
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
        decl_budget::begin_declaration();
        decl_budget::finish_declaration(
            "Nat.shiftRight",
            spec.env_mut()
                .register_nat_shiftright_def()
                .map_err(|e| SpecError::EnvError(e.to_string())),
        )?;
        // E4d: the native-Nat folds of the bitwise heads and `Nat.shiftRight`,
        // whose closures exist only from here on.
        decl_budget::begin_declaration();
        spec.add_accepts_tc_native_nat_late()?;

        Ok(())
    }

    /// Get the environment
    #[must_use]
    pub fn env(&self) -> &Environment {
        &self.env
    }

    /// Consume this specification and transfer its kernel environment.
    ///
    /// Retains the actual declarations, provenance and environment options
    /// without cloning their indexes. Specification-side source/registration
    /// bookkeeping is dropped. This is an ownership transfer, not a proof or
    /// an admission capability: consumers still check the exact terms and
    /// rooted authority closures needed by their own semantic model.
    #[must_use]
    pub fn into_environment(self) -> Environment {
        self.env
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
