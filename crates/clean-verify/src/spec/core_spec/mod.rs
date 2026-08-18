// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Core specification definitions for the clean type theory.
//!
//! Split from a single 3468-line file into thematic sub-modules (Part of #307):
//! - `foundation_types`: Eq, ProdType, Nat, Bool, AndType (PARTs 1-3.5)
//! - `expr_model`: KExpr, lift, instantiate operations (PART 4 + lift_at lemmas)
//! - `typing_universe_levels`: closed Nat-level universe helpers for Typing (PART 5 prelude)
//! - `typing_def_eq`: Typing, DefEq, delta/iota (PARTs 5, DefEq, Delta/Iota)
//! - `derived_rules`: Backward-compatible typing and def-eq aliases (PARTs 6-8)
//! - `whnf_reduction`: WHNF types, reduction, expression operations (PARTs 9-10)
//! - `whnf_lemmas`: Key lemmas axiomatized from Verus proofs (PART 11)
//! - `substitution_commutation`: bvar case chain for substitution commutation (PART 11a)
//! - `substitution_commutation_nested`: nested commutation theorem + corollaries (PART 11a cont.)
//! - `substitution_def_eq`: substitution/DefEq bridge lemmas layered on PART 11
//! - `type_preservation`: Type preservation infrastructure + theorem (PARTs 12-13)
//! - `type_preservation_generation_app`: app generation split from the main typing-generation module
//! - `micro_checker`: Micro-checker model, types, operations, correctness (PARTs 14-17)
//! - `micro_soundness`: Micro-checker soundness and cross-validation (PARTs 18-19)
//! - `env_extensions`: Definitional extension judgments and soundness (PART 20)
//! - `implementation_soundness`: kernel-state correspondence and forward simulation contracts (PART 21)
//! - `implementation_soundness_infer_accepts`: faithful KernelInferAccepts inductive + infer skolems + master inversion (PART 21, Step 3)
//! - `implementation_soundness_admissibility`: admissibility inversion lemmas for infer/check subcalls (PART 21g)
//! - `implementation_soundness_infer_refinement`: sort/bvar infer_type refinement foundations (PART 21f root)
//! - `implementation_soundness_whnf_decomposition`: whnf = spec whnf trace + DefEq derivation (PART 21e)
//! - `implementation_soundness_defeq_decomposition`: is_def_eq = normalize + structural comparison (PART 21d)
//! - `implementation_soundness_check_decomposition`: check_type = infer + def_eq decomposition (PART 21a)
//! - `implementation_soundness_infer_refinement_app`: app-case infer decomposition axiom + step projections (PART 21f app)
//! - `implementation_soundness_infer_refinement_app_sound`: app-case constructive sound theorem + dispatch wrapper (PART 21f app sound)
//! - `implementation_soundness_infer_refinement_binder`: lam/pi cert-backed binder witnesses + ProdType decompositions (#2869, #461) (PART 21f binder)
//! - `implementation_soundness_infer_refinement_binder_typing`: lam/pi typing-step projections from ProdType decompositions (#461) (PART 21f binder typing)
//! - `implementation_soundness_infer_refinement_binder_sound`: constructive lam/pi sound theorems + dispatch wrappers (#461) (PART 21f binder sound)
//! - `implementation_soundness_infer_refinement_dispatch`: KExpr.rec dispatcher (PART 21f dispatch)
//! - `implementation_soundness_simulation`: forward-simulation theorems and summary wrappers (PART 21b)
//! - `implementation_soundness_env_preservation`: add_decl environment preservation (PART 21c)

mod acc_wtype;
mod beta_bd_embedding;
mod beta_bd_sn;
mod beta_reduces_preserves_typing;
mod binder_join_components;
mod budget_induction_prereqs;
mod bundles;
mod bvar_slot;
mod closedness_bundle;
mod complete_development;
mod ctx_canonical_forms;
mod ctx_rep;
mod def_eq_joinable;
mod def_eq_lift_congr;
mod defeq_capstone;
mod defeq_complete_leaves;
mod defeq_complete_steps;
mod defeq_fuel;
mod defeq_fuel_mono;
mod defeq_fuel_wh3_mono;
mod defeq_iota_delta_gen;
mod defeq_nf_agree;
mod defeq_round_app;
mod defeq_round_binder;
mod defeq_round_leaf;
mod defeq_round_rest;
mod defeq_struct_intro;
mod defeq_struct_sound;
pub(super) mod defeq_whnf_join;
mod delta_step;
mod delta_step_bridge;
mod delta_subst;
mod dependent_sn_richmodel;
mod derived_rules;
mod env_closed_checkers;
mod env_closed_checkers_depth;
mod env_extensions;
mod eval_ir_activation;
mod eval_ir_bits;
mod eval_ir_bits_witnesses;
mod eval_ir_bvar_range;
mod eval_ir_contains;
mod eval_ir_correct;
mod eval_ir_cost;
mod eval_ir_crystal;
mod eval_ir_float;
mod eval_ir_float_div;
mod eval_ir_float_fin;
mod eval_ir_float_fin_ops;
mod eval_ir_float_fin_witnesses;
mod eval_ir_float_ops;
mod eval_ir_from_source;
mod eval_ir_fuel;
mod eval_ir_kind_ord;
mod eval_ir_machine;
mod eval_ir_meta_tag;
mod eval_ir_mode;
mod eval_ir_ops;
mod eval_ir_path_step;
mod eval_ir_repr;
mod eval_ir_state;
mod eval_ir_steps;
mod eval_ir_syntax;
mod eval_ir_trunc;
mod eval_ir_valid_char;
mod expr_model;
mod expr_model_discrimination;
mod expr_model_discrimination_lam_pi;
mod expr_model_discrimination_let;
mod expr_model_discrimination_pi;
mod expr_model_inst_ceiling;
mod expr_model_instantiate_lift_cancel_general;
mod expr_model_lift_cancel;
mod expr_model_lift_compose;
mod expr_model_lift_instantiate_swap;
mod expr_model_lift_lemmas;
mod expr_model_lift_shift;
mod expr_model_lift_shift_gen;
mod expr_model_subst_lift_cross_bvar;
mod expr_model_subst_lift_cross_compose;
mod expr_model_subst_lift_exchange;
mod expr_model_subst_lift_gen;
mod expr_model_subst_lift_interchange;
mod expr_model_subst_lift_interchange_bvar;
mod expr_model_subst_lift_interchange_bvar_cases;
mod expr_model_subst_lift_interchange_bvar_helpers;
mod expr_model_subst_lift_interchange_gen;
mod faithful_checkers;
mod faithful_confluence;
mod faithful_red_env;
mod foundation_arith_lemmas;
mod foundation_arith_positivity;
mod foundation_arith_transport;
mod foundation_arith_witnesses;
mod foundation_types;
mod fuel_adequacy;
mod fuel_pairing;
mod hiotap3_discharge;
mod hnf3_residual;
mod hnf_conv;
mod hnf_discharge3;
mod hnf_refutation;
mod impl_infer;
mod impl_infer_mode_gate;
mod impl_infer_sound;
mod impl_infer_syntax;
mod impl_infer_witnesses;
mod implementation_soundness;
mod implementation_soundness_admissibility;
mod implementation_soundness_admissibility_wrappers;
mod implementation_soundness_check_decomposition;
mod implementation_soundness_defeq_decomposition;
mod implementation_soundness_env_preservation;
mod implementation_soundness_infer_accepts;
mod implementation_soundness_infer_refinement;
mod implementation_soundness_infer_refinement_app;
mod implementation_soundness_infer_refinement_app_sound;
mod implementation_soundness_infer_refinement_binder;
mod implementation_soundness_infer_refinement_binder_sound;
mod implementation_soundness_infer_refinement_binder_typing;
mod implementation_soundness_infer_refinement_dispatch;
mod implementation_soundness_simulation;
mod implementation_soundness_whnf_decomposition;
mod infer_terminates_proof;
mod iota_closedness_bundle;
mod iota_core;
mod iota_immunity;
mod iota_prepass;
mod iota_step;
mod iota_step_bridge;
mod iota_subst;
mod iota_subst_const;
mod join_tag;
mod kernel_core_red_env;
mod kexpr_beq;
mod kexpr_beq_sound;
mod kexpr_discr;
mod micro_checker;
mod micro_soundness;
mod mutual_schema;
mod natrec;
mod nf_app_leg;
mod nf_head;
mod nf_head_const_name;
mod nf_shape;
mod par_reduces_c;
mod par_reduces_cd;
mod par_reduces_cd_commute;
mod par_reduces_cd_hr;
mod par_reduces_cd_hr_compose;
mod par_reduces_cd_injectivity;
mod par_reduces_cd_sound;
mod par_reduces_d;
mod par_reduces_d_conf;
mod par_reduces_d_diamond;
mod par_reduces_delta_sc;
mod par_reduces_iota_delta;
mod par_reduces_p;
mod par_reduces_p0;
mod par_reduces_p_injectivity;
mod par_reduces_p_marked;
mod par_reduces_p_topdev;
mod par_reduces_pd;
mod par_reduction;
mod pi_injectivity_confluence;
mod pi_injectivity_def_eq;
mod premise_witnesses;
mod proj_rigidity;
mod rbelow_descent;
mod rec_env;
mod rec_env_closed;
mod reduction_witnesses;
mod residual_narrowing;
mod rigid_app_head;
mod rigid_app_inv;
mod rigid_bridge;
mod rigid_preservation;
mod rigid_tag;
mod rose_schema;
mod schema;
mod slot_collapse;
mod slot_dispatch_at;
mod spine_join_components;
mod stuck_app_rigidity;
mod stuck_immunity;
mod stuck_major_confluence;
mod stuck_major_immune;
mod stuck_major_recmeta;
mod stuck_recursor;
mod subject_reduction_bundle;
mod substitution_commutation;
mod substitution_commutation_nested;
mod substitution_def_eq;
mod the_red_env;
mod type_preservation;
mod type_preservation_cases;
mod type_preservation_cases_congruence;
mod type_preservation_cases_def_eq;
mod type_preservation_eq_specializers;
mod type_preservation_generation;
mod type_preservation_generation_app;
mod type_preservation_raw_bridge;
mod type_preservation_subst;
mod type_preservation_weakening;
mod typing_def_eq;
mod typing_def_eq_reduction_families;
mod typing_def_eq_typed;
mod typing_universe_levels;
mod unique_normal_forms_c;
mod univ_poly;
mod wall_a_completeness;
mod wall_a_headmatch;
mod wbelow3;
mod wh3_fuel_adequacy;
mod wh3_hiota_repair;
mod wh3_norm_acc;
mod wh3_norm_acc_witness;
mod wh3_soundness;
mod wh3_spine;
mod wh3_stability;
mod wh3_stuck_head;
mod wh_fuel_adequacy;
mod wh_hiota_repair;
mod wh_neutral_stuck;
mod wh_soundness;
mod wh_step_arms;
mod wh_step_mono;
mod wh_step_mono_proof;
mod wh_under_applied;
mod whc3_inverter;
mod whnf_classify;
mod whnf_lemmas;
mod whnf_normalizes;
mod whnf_progress;
mod whnf_reduction;
mod whnf_shape;
mod whnf_terminates_well_typed;

use super::error::SpecError;
use super::Specification;
use clean_kernel::Environment;
use std::collections::HashMap;

impl Specification {
    /// Register all core specification definitions.
    ///
    /// Delegates to the centralized bundle planner in dependency order.
    pub(super) fn add_core_spec(&mut self) -> Result<(), SpecError> {
        bundles::run_bundle(self, bundles::CoreSpecBundle::Full)
    }

    /// Build the subset of the spec needed for substitution/WHNF helper tests.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_substitution_test_spec() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        bundles::run_bundle(&mut spec, bundles::CoreSpecBundle::Substitution)?;
        Ok(spec)
    }

    /// Build the subset of the spec needed for implementation-soundness tests.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_implementation_soundness_test_spec() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        bundles::run_bundle(&mut spec, bundles::CoreSpecBundle::ImplementationSoundness)?;
        Ok(spec)
    }

    /// Build the subset of the spec needed for interval arithmetic promotion tests.
    ///
    /// Registers foundation types (Eq, Nat, ProdType, Bool, AndType) and the interval
    /// arithmetic inductives + T01-T20 definitions. The 20 T0x definitions are
    /// DerivedPending at build time; the promote pipeline elaborates their
    /// proof terms and promotes each to DerivedProved. Part of #3362.
    ///
    /// # Errors
    /// Returns `SpecError` if spec construction fails.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_interval_arith_test_spec() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        bundles::run_bundle(&mut spec, bundles::CoreSpecBundle::IntervalArith)?;
        Ok(spec)
    }

    /// Build the subset of the spec needed for `EvalIR` tests: foundation types
    /// plus the trust-ir executable-semantics stage (crystal job C3).
    ///
    /// EvalIR is deliberately self-contained — it carries its own `IRList` /
    /// `IROption` families rather than reusing `ListType` / `OptionType`, whose
    /// stages drag in `KExpr` and the whole reduction substrate — so this bundle
    /// is two stages and builds in a fraction of the full spec's time. Both the
    /// EvalIR witness tests and the vacuity firewall's audit of the EvalIR
    /// relations use it.
    ///
    /// # Errors
    /// Returns `SpecError` if spec construction fails.
    pub fn new_eval_ir_spec() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        bundles::run_bundle(&mut spec, bundles::CoreSpecBundle::EvalIr)?;
        Ok(spec)
    }

    /// Build EvalIR in the ordinary Clean prelude environment.
    ///
    /// The dependency-scoped [`Self::new_eval_ir_spec`] is the right authority
    /// for EvalIR's own witnesses and vacuity firewall.  Consumers that compose
    /// EvalIR with authored Clean source need the standard notation,
    /// typeclasses, and logical vocabulary installed by
    /// [`Environment::with_prelude`].  This constructor adds the exact same
    /// single EvalIR stage to that production prelude without pulling in the
    /// unrelated self-verification specification.
    ///
    /// # Errors
    /// Returns `SpecError` if any EvalIR declaration fails to parse, elaborate,
    /// or kernel-check in the prelude environment.
    pub fn new_eval_ir_prelude_spec() -> Result<Self, SpecError> {
        let mut spec = Specification {
            env: Environment::with_prelude(),
            definitions: HashMap::new(),
            red_env_script_override: None,
        };
        spec.add_eval_ir()?;
        // A2's `add_eval_ir_repr` is deliberately NOT in this bundle. Its
        // `EncodesLevelArc` is indexed by `Level`, and this bundle starts from
        // `Environment::with_prelude()` — the Lean-style prelude — which carries
        // no reflected syntax, so the arms mention `Level.zero` with no `Level`
        // in scope and the elaborator reports dot-notation on an unknown
        // variable. Supplying `Level` is not a fix either: `add_expr_model`
        // then fails on `instantiate_bvar_at_below`, because the prelude's
        // universe-polymorphic `Eq` is not the `Eq` those lemmas were written
        // against, and `add_foundation_types` collides outright (`Duplicate
        // declaration: Eq.symm`). This bundle's job, per its own test, is that
        // the EvalIR authority and the standard classes coexist in one
        // environment; the Level-indexed A2/A4 stages belong to
        // `new_eval_ir_spec`, which is built on the spec foundation.
        Ok(spec)
    }

    /// Backward-compatible test-only name for [`Self::new_eval_ir_spec`].
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_eval_ir_test_spec() -> Result<Self, SpecError> {
        Self::new_eval_ir_spec()
    }

    /// Build the minimum spec needed for zonotope soundness (T01-T08 + T08A/B)
    /// promotion tests — foundation types (Nat, Eq, ...) plus the zonotope
    /// inductives and derived-lemma stubs. Used by `tests_zonotope_kernel` to
    /// keep the promotion fixture dependency-scoped instead of constructing the
    /// unrelated full specification. Part of #3363.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_zonotope_test_spec() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        // Zonotope proofs require only Nat (for the generator-count index).
        // Foundation types are the smallest bundle that provides Nat and its
        // constructors through the kernel Environment.
        spec.add_foundation_types()?;
        spec.add_zonotope_spec()?;
        Ok(spec)
    }

    /// Build the minimum spec needed for CDCL SAT invariant promotion tests
    /// (S01-S06). Registers foundation types (Nat, Eq, ...) plus the CDCL
    /// inductives and derived-lemma stubs.
    ///
    /// This mirrors `new_zonotope_test_spec` — the CDCL S01-S06 inductives
    /// only index over `Nat` so the foundation bundle is the minimal prefix
    /// required to elaborate the structural recursor proof terms. The dedicated
    /// builder keeps this fixture dependency-scoped and fast.
    /// Part of #3364.
    ///
    /// # Errors
    /// Returns `SpecError` if spec construction fails.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_cdcl_test_spec() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        // CDCL S01-S06 inductives (TrailOp, WatchOp, ResolutionStep,
        // BacktrackOp, BCPStep, CDCLStep and their `*Sound`/`*Valid`/
        // `*Complete`/`*Consistent`/`*Invariant`/`*Terminates` witnesses)
        // only reference Nat. Foundation types are the smallest bundle that
        // provides Nat and its constructors through the kernel Environment.
        spec.add_foundation_types()?;
        spec.add_cdcl_sat_spec()?;
        Ok(spec)
    }

    /// Build the minimal subset of the spec needed to validate Stage-0 Brick 2
    /// (`DefEq.iota_gen` / `DefEq.delta_gen`): the dependency prefix up to and
    /// including `add_defeq_iota_delta_gen`. Stops before the `par_reduces_*`
    /// confluence lane (which the brick does not depend on), so the brick's two
    /// proof terms are kernel-checked against the real `RecEnvWellformed` /
    /// `DefEnvWellformed` / keystone definitions without building the full spec.
    ///
    /// # Errors
    /// Returns `SpecError` if spec construction fails.
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_defeq_iota_delta_gen_test_spec() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        bundles::build_defeq_iota_delta_gen_prefix(&mut spec)?;
        Ok(spec)
    }

    /// Build exactly the live declarations consumed by red-environment
    /// reflection, without loading the generated artifact being rebuilt.
    ///
    /// This deliberately follows the reflection allowlists rather than the
    /// full bundle: it is the generator's bootstrap root and therefore must
    /// never call `add_kernel_core_red_env`.
    #[doc(hidden)]
    pub fn new_red_env_reflection_seed() -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        spec.add_foundation_types()?;
        spec.add_foundation_arith_lemmas()?;
        spec.add_foundation_arith_witnesses()?;
        spec.add_foundation_arith_positivity()?;
        spec.add_foundation_arith_transport()?;
        spec.add_expr_model()?;
        spec.add_rec_env()?;
        spec.add_iota_step()?;
        spec.add_delta_step_core()?;
        spec.add_red_env()?;
        spec.add_bvar_ceiling_definition()?;
        spec.add_env_closed_checker_defs()?;
        Ok(spec)
    }

    /// Parse, elaborate, and kernel-check every line of a freshly rendered
    /// red-environment script against an artifact-independent seed.
    ///
    /// The generator calls this before replacing any committed artifact, so a
    /// renderer/parser mismatch cannot publish an unloadable script.
    #[doc(hidden)]
    pub fn validate_red_env_reflection_script(script: &str) -> Result<(), SpecError> {
        let mut spec = Self::new_red_env_reflection_seed()?;
        spec.add_kernel_core_red_env_script(script)
    }

    /// Construct an empty specification for subset builders.
    fn new_empty() -> Self {
        Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override: None,
        }
    }
}
