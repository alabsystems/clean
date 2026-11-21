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

// The two chained EvalIR modules, re-exported so the GAP-2 encoding
// differential (`crate::ir_semdiff`) runs the machine on exactly the module
// the specification registers rather than on a second transcription.
pub use eval_ir_bvar_range::ir_br_module_defs;
pub use eval_ir_contains::ir_fc_module_defs;
pub use eval_ir_flat_flags_with::ir_fw_module_defs;
pub use eval_ir_from_source::ir_fs_module_defs;
pub use eval_ir_has_loose_bvars::ir_hlb_module_defs;
pub use eval_ir_kind_ord::ir_ko_module_defs;
pub use eval_ir_mode::ir_h2_module_defs;
pub use eval_ir_node_id_index::ir_ni_module_defs;
pub use eval_ir_priority::ir_pv_module_defs;
pub use eval_ir_slot_lemmas::SLOT_LEMMA_NAMES;
pub use eval_ir_strict_monads::{ir_sm_module_defs, ir_sm_semdiff_defs};
pub use eval_ir_trunc::ir_gc_module_defs;
pub use eval_ir_valid_char::ir_vc_module_defs;
pub use eval_ir_w2a_synth::{
    ir_w2a_ee_module_defs, ir_w2a_sel_module_defs, ir_w2a_ud_module_defs, ir_w2a_uo_module_defs,
    ir_w2a_ur_module_defs,
};
pub use eval_ir_w2b_synth::{
    ir_w2b_al_module_defs, ir_w2b_pd_module_defs, ir_w2b_pm_module_defs, ir_w2b_pp_module_defs,
};
pub use eval_ir_w2c_synth::{ir_w2c_ci_module_defs, ir_w2c_ga_module_defs};
pub use eval_ir_w3_synth::{ir_w3_os_module_defs, ir_w3_ou_module_defs};
pub use eval_ir_w4_synth::ir_w4_fc_module_defs;
pub use eval_ir_wfr_synth::{ir_frm_module_defs, ir_frr_module_defs, ir_frs_module_defs};
mod acceptance_cdp_in;
mod acceptance_constants;
mod acceptance_in;
mod acceptance_legacy;
mod beta_subst_congr;
mod bvar_slot;
mod candmodel_construct_r0;
mod candmodel_construct_r1;
mod candmodel_construct_r10;
mod candmodel_construct_r10_src;
mod candmodel_construct_r11;
mod candmodel_construct_r11_src;
mod candmodel_construct_r12;
mod candmodel_construct_r12_src;
mod candmodel_construct_r13;
mod candmodel_construct_r13_src;
mod candmodel_construct_r14;
mod candmodel_construct_r14_src;
mod candmodel_construct_r15;
mod candmodel_construct_r15_src;
mod candmodel_construct_r16;
mod candmodel_construct_r16_src;
mod candmodel_construct_r17;
mod candmodel_construct_r17_src;
mod candmodel_construct_r17_src2;
mod candmodel_construct_r18;
mod candmodel_construct_r18_src;
mod candmodel_construct_r19;
mod candmodel_construct_r19_src;
mod candmodel_construct_r2;
mod candmodel_construct_r20;
mod candmodel_construct_r20_src;
mod candmodel_construct_r21;
mod candmodel_construct_r21_src;
mod candmodel_construct_r22;
mod candmodel_construct_r22_src;
mod candmodel_construct_r23;
mod candmodel_construct_r23_src;
mod candmodel_construct_r24;
mod candmodel_construct_r24_src;
mod candmodel_construct_r25;
mod candmodel_construct_r25_src;
mod candmodel_construct_r26;
mod candmodel_construct_r26_src;
mod candmodel_construct_r27;
mod candmodel_construct_r27_src;
mod candmodel_construct_r28;
mod candmodel_construct_r28_src;
mod candmodel_construct_r29;
mod candmodel_construct_r29_src;
mod candmodel_construct_r3;
mod candmodel_construct_r4;
mod candmodel_construct_r5;
mod candmodel_construct_r6;
mod candmodel_construct_r7;
mod candmodel_construct_r8;
mod candmodel_construct_r9;
mod candmodel_construct_r9_rank;
mod candmodel_dep_pi_probe;
mod candmodel_inhabit_probe;
mod candmodel_necessary;
mod candmodel_whnf_backward;
mod candmodel_whnf_pi_intro;
mod candmodel_whnf_probe;
mod candmodel_whnf_typestep;
mod closedness_bundle;
mod complete_development;
mod constructor_projection;
mod constructor_return_coherence;
mod ctor_spine_lengths;
mod ctx_canonical_forms;
mod ctx_rep;
mod declaration_lookup_closedness;
mod declaration_lookup_instantiation;
mod declaration_signature_lookup;
mod declaration_signatures;
#[cfg(test)]
mod declaration_source_tests;
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
mod delta_universe_instantiation;
mod dependent_sn_richmodel;
mod derived_rules;
mod env_closed_checkers;
mod env_closed_checkers_depth;
mod env_extensions;
mod env_freshness;
mod eval_ir_activation;
mod eval_ir_adequacy;
mod eval_ir_bits;
mod eval_ir_bits_witnesses;
mod eval_ir_bvar_range;
mod eval_ir_byte;
mod eval_ir_byte_access_laws;
mod eval_ir_byte_alignment_laws;
mod eval_ir_byte_allocation_laws;
mod eval_ir_byte_allocation_world_laws;
mod eval_ir_byte_arc_frame;
mod eval_ir_byte_arc_tail;
mod eval_ir_byte_atomic;
mod eval_ir_byte_atomic_laws;
mod eval_ir_byte_atomic_step_laws;
#[cfg(test)]
mod eval_ir_byte_atomic_step_tests;
#[cfg(test)]
mod eval_ir_byte_atomic_tests;
mod eval_ir_byte_binding_laws;
mod eval_ir_byte_builtin_name;
mod eval_ir_byte_call_laws;
mod eval_ir_byte_cast;
mod eval_ir_byte_codec_laws;
mod eval_ir_byte_const;
#[cfg(test)]
mod eval_ir_byte_const_tests;
mod eval_ir_byte_enum;
#[cfg(test)]
mod eval_ir_byte_enum_tests;
mod eval_ir_byte_fat;
mod eval_ir_byte_fat_laws;
mod eval_ir_byte_field;
mod eval_ir_byte_field_extract_laws;
mod eval_ir_byte_field_get_laws;
mod eval_ir_byte_field_preservation_laws;
mod eval_ir_byte_field_set_laws;
#[cfg(test)]
mod eval_ir_byte_field_tests;
mod eval_ir_byte_fresh_separation_laws;
mod eval_ir_byte_function_laws;
mod eval_ir_byte_gep_typed;
#[cfg(test)]
mod eval_ir_byte_gep_typed_tests;
mod eval_ir_byte_import_laws;
mod eval_ir_byte_initialization_laws;
mod eval_ir_byte_lifetime_laws;
mod eval_ir_byte_literal_bridge;
mod eval_ir_byte_literal_typing;
mod eval_ir_byte_machine;
#[cfg(test)]
mod eval_ir_byte_machine_tests;
mod eval_ir_byte_memory;
mod eval_ir_byte_memory_laws;
mod eval_ir_byte_old_frame_laws;
mod eval_ir_byte_overflow;
#[cfg(test)]
mod eval_ir_byte_overflow_tests;
mod eval_ir_byte_radix_laws;
mod eval_ir_byte_range_laws;
mod eval_ir_byte_scalar_laws;
mod eval_ir_byte_site_order;
mod eval_ir_byte_step_laws;
mod eval_ir_byte_ty_eq_laws;
mod eval_ir_byte_types;
mod eval_ir_byte_usize;
mod eval_ir_byte_usize_cmp;
mod eval_ir_byte_usize_cmp_step_laws;
#[cfg(test)]
mod eval_ir_byte_usize_cmp_tests;
#[cfg(test)]
mod eval_ir_byte_usize_tests;
mod eval_ir_byte_world_laws;
mod eval_ir_cf;
mod eval_ir_contains;
mod eval_ir_correct;
mod eval_ir_cost;
mod eval_ir_crystal;
mod eval_ir_driver;
mod eval_ir_execution;
mod eval_ir_fbq;
mod eval_ir_fcmp;
mod eval_ir_flat_flags_with;
mod eval_ir_float;
mod eval_ir_float_add;
mod eval_ir_float_div;
mod eval_ir_float_fin;
mod eval_ir_float_fin_ops;
mod eval_ir_float_fin_witnesses;
mod eval_ir_float_mul;
mod eval_ir_float_ops;
mod eval_ir_float_res;
mod eval_ir_float_res_witnesses;
mod eval_ir_float_sub;
mod eval_ir_fng;
mod eval_ir_from_source;
mod eval_ir_fuel;
mod eval_ir_has_loose_bvars;
mod eval_ir_it;
mod eval_ir_itb;
mod eval_ir_itc;
mod eval_ir_itd;
mod eval_ir_ite;
mod eval_ir_its;
mod eval_ir_kind_ord;
mod eval_ir_level_minted;
mod eval_ir_lzb;
mod eval_ir_lzb_activation;
mod eval_ir_lzb_correct;
mod eval_ir_lzc;
mod eval_ir_lzd;
mod eval_ir_lzd_activation;
mod eval_ir_lzd_correct;
mod eval_ir_lzd_fresh;
mod eval_ir_machine;
mod eval_ir_meta_tag;
mod eval_ir_mode;
mod eval_ir_nat_bool_reflection_v1;
mod eval_ir_node_id_index;
mod eval_ir_ops;
mod eval_ir_path_step;
mod eval_ir_positive_division_v1;
mod eval_ir_priority;
mod eval_ir_repr;
mod eval_ir_rust_u64;
mod eval_ir_sh;
mod eval_ir_slot_lemmas;
mod eval_ir_stack;
mod eval_ir_stack_minted;
mod eval_ir_steps_scaling_probe;
#[cfg(test)]
mod eval_ir_vcg;
pub use eval_ir_stack_minted::STACK_MINTED_NAMES;
mod eval_ir_stack_theorems;
pub use eval_ir_stack_theorems::STACK_THEOREM_NAMES;
mod eval_ir_stack_split;
pub use eval_ir_stack_split::STACK_SPLIT_NAMES;
mod eval_ir_stack_axes_minted;
pub use eval_ir_stack_axes_minted::STACK_AXES_MINTED_NAMES;
mod eval_ir_stack_axes;
pub use eval_ir_stack_axes::STACK_AXES_NAMES;
mod eval_ir_itf;
pub use eval_ir_itf::ITF_NAMES;
mod eval_ir_stk_witness;
pub use eval_ir_stk_witness::STK_WITNESS_NAMES;
mod eval_ir_stack_axes_witness;
pub use eval_ir_stack_axes_witness::STACK_AXES_WITNESS_NAMES;
mod eval_ir_ctr;
pub use acceptance_cdp_in::{
    ACCEPTS_IN_PROOF_NAMES, ACCEPTS_TC_NAT_NAME_ALIASES, ACCEPTS_TC_QUOT_NAME_ALIASES,
    ACCEPTS_TC_STRING_NAME_ALIASES, NATIVE_NAT_PROOF_NAMES, STRING_LITERAL_PROOF_NAMES,
};
pub use eval_ir_ctr::CTR_NAMES;
pub use literal_string_codec::STRING_LIT_CODEC_PROOF_NAMES;
mod eval_ir_lzd_sctr;
pub use eval_ir_lzd_sctr::LZD_SCTR_NAMES;
mod eval_ir_ctr_stack;
pub use eval_ir_ctr_stack::CTR_STACK_NAMES;
mod eval_ir_e5;
pub use eval_ir_e5::E5_NAMES;
mod eval_ir_bmem_core;
#[cfg(test)]
mod eval_ir_bmem_strict_tests;
pub use eval_ir_bmem_core::BMEM_CORE_NAMES;
#[cfg(test)]
mod eval_ir_bmem_telescope_tests;
mod eval_ir_bmem_trie;
pub use eval_ir_bmem_trie::BMEM_TRIE_NAMES;
mod eval_ir_lzd_pc;
pub use eval_ir_lzd_pc::LZD_PC_NAMES;
mod eval_ir_it_sctr;
pub use eval_ir_it_sctr::IT_SCTR_NAMES;
mod eval_ir_it_pc;
pub use eval_ir_it_pc::IT_PC_NAMES;
mod declaration_input_admission;
#[cfg(test)]
mod eval_ir_congruence_tests;
mod eval_ir_state;
mod eval_ir_steps;
mod eval_ir_strict_monads;
mod eval_ir_syntax;
mod eval_ir_trunc;
mod eval_ir_valid_char;
mod eval_ir_w2a_synth;
mod eval_ir_w2b_synth;
mod eval_ir_w2c_synth;
mod eval_ir_w3_synth;
mod eval_ir_w4_synth;
mod eval_ir_wfr_synth;
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
mod impl_constant_soundness;
mod impl_infer;
mod impl_infer_mode_gate;
mod impl_infer_sound;
mod impl_infer_syntax;
mod impl_infer_witnesses;
mod impl_literal_soundness;
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
mod ind_ctor_env;
mod ind_ctor_table;
mod infer_terminates_proof;
mod iota_closedness_bundle;
mod iota_contractum;
mod iota_contractum_declines;
mod iota_core;
mod iota_immunity;
mod iota_option_views;
mod iota_prepass;
mod iota_reduct_views;
mod iota_step;
mod iota_step_bridge;
mod iota_subst;
mod iota_subst_const;
mod join_tag;
mod kernel_core_red_env;
mod kexpr_beq;
mod kexpr_beq_sound;
mod kexpr_discr;
mod kinfers_declarative;
mod literal_model;
mod literal_string_codec;
mod micro_checker;
mod micro_soundness;
mod micro_totality_contrast;
mod micro_verifies_r0;
mod mutual_schema;
mod named_block_return;
mod named_indexed_guard;
mod nat_zero_rhs_general;
mod nat_zero_rhs_typing;
mod natrec;
mod nf_app_leg;
mod nf_head;
mod nf_head_const_name;
mod nf_shape;
mod omega_not_sn;
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
mod projection_confluence;
mod projection_level_zero;
mod projection_metadata;
mod projection_reduction;
mod projection_semantic;
mod projection_telescope;
mod projection_typing;
mod projection_unused_binder;
mod r29_premise_witnesses;
mod raw_block_return;
mod rbelow_descent;
mod rec_env;
mod rec_env_closed;
mod recursor_generic_rhs_instances;
mod recursor_rhs_instantiation;
mod recursor_schematic_rhs_instances;
mod redabstraction_probe;
mod rednd_probe;
mod redrecgen_probe;
mod reduction_witnesses;
mod reflected_nat_zero_general;
mod reflected_nat_zero_source_bridge;
mod reflected_nat_zero_typing;
mod residual_narrowing;
mod rigid_app_head;
mod rigid_app_inv;
mod rigid_bridge;
mod rigid_preservation;
mod rigid_tag;
mod rose_schema;
mod schema;
mod schematic_delta_typing;
mod schematic_tenv_rep;
mod semantic_closedness;
mod semantic_delta_compat;
mod semantic_injectivity;
mod semantic_iota_compat;
mod semantic_iota_universe_instantiation;
mod semantic_join;
mod semantic_parallel_compat;
mod semantic_reduction_universe_instantiation;
mod semantic_spine_compat;
mod semantic_term_instantiation;
mod semantic_typed_spine;
mod semantic_typed_spine_forward;
mod semantic_typed_spine_select;
mod semantic_typing_inversion;
mod semantic_typing_universe_instantiation;
mod semantic_universe_substitution;
mod semantic_wh3_soundness_in;
mod slot_collapse;
mod slot_dispatch_at;
mod spine_join_components;
mod step_app_inversion;
mod stored_family_admission;
mod stratified_hurkens_block;
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
mod typing_closed_weakening;
mod typing_def_eq;
mod typing_def_eq_reduction_families;
mod typing_def_eq_typed;
mod typing_universe_levels;
mod typingctx_universe_instantiation;
mod typingctxconv_universe_instantiation;
mod unique_normal_forms_c;
mod univ_instantiation_syntax;
mod univ_poly;
mod universe_closedness;
mod universe_geq_bounded_offsets;
mod universe_geq_core;
mod universe_geq_stabilization;
mod universe_instantiation_bridge;
mod universe_lookup_bridge;
mod universe_normalization_offset_spine;
mod universe_param_support;
mod universe_schematic_rep;
mod universe_semantic_bridge;
mod universe_support_fusion;
mod wall_a_completeness;
mod wall_a_headmatch;
mod wbelow3;
mod wh3_defeq_soundness;
mod wh3_fuel_adequacy;
mod wh3_hiota_repair;
mod wh3_norm_acc;
mod wh3_norm_acc_witness;
mod wh3_soundness;
mod wh3_spine;
mod wh3_stability;
mod wh3_stuck_head;
mod wh3_to_wh_transfer;
mod wh3_to_wh_transfer_loop;
mod wh3_to_wh_transfer_step;
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
    /// [`Environment::with_prelude`]. This constructor installs the execution
    /// vocabulary and shared literal builders without the historical Crystal
    /// worked examples or the unrelated self-verification specification.
    ///
    /// # Errors
    /// Returns `SpecError` if any EvalIR declaration fails to parse, elaborate,
    /// or kernel-check in the prelude environment.
    pub fn new_eval_ir_prelude_spec() -> Result<Self, SpecError> {
        let mut spec = Specification {
            env: Environment::try_with_prelude()
                .map_err(|error| SpecError::EnvError(error.to_string()))?,
            definitions: HashMap::new(),
            red_env_script_override: None,
            red_env_interning_override: None,
            model_unit_source: super::ModelUnitSource::default(),
        };
        spec.add_eval_ir_execution()?;
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
        spec.add_declaration_signature_carrier()?;
        spec.add_rec_env()?;
        spec.add_univ_instantiation_syntax()?;
        spec.add_recursor_rhs_instantiation_syntax()?;
        spec.add_declaration_signatures()?;
        spec.add_iota_step()?;
        spec.add_delta_step_core()?;
        spec.add_ind_ctor_env()?;
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
        let mut spec = Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override: None,
            red_env_interning_override: None,
            model_unit_source: super::ModelUnitSource::default(),
        };
        // CLOSING THE FREE-VARIABLE FAIL-OPEN FOR THE SPEC (2026-09-20).
        //
        // `relaxedAutoImplicit` defaults TRUE -- Lean 4's own default, which
        // Clean reproduces faithfully and pins at
        // `tests/lean4_compat/lean4_tests/1011.lean` (3 must-succeed, 4
        // expected-fail). Under it, ANY undeclared identifier whose first
        // character is alphabetic auto-binds as a fresh implicit in TYPE
        // position, while the same spelling in VALUE position is a hard error
        // (`elab_core.rs`'s auto-implicit block, guarded by `!in_term_body`).
        // A declaration hitting that is true of an ARBITRARY inhabitant rather
        // than of the constant it names -- strictly weaker than it reads, and
        // it still kernel-checks. That is how `ir_lzd_max_running_at_9` and
        // `_at_10` came to be true of an arbitrary counter rather than of 64.
        //
        // THE ELABORATOR DEFAULT IS NOT TOUCHED. Changing it would diverge from
        // Lean and break that fidelity pin. This opts the SPEC's environment out
        // instead -- the same thing Mathlib does project-wide -- where an
        // undeclared name is always a bug and never a convenience.
        //
        // Only the RELAXED half is disabled, which is the surgical choice:
        // single-letter type variables still auto-bind, so inductive headers
        // keep the auto-implicit table `elab_inductive.rs` uses structurally for
        // `num_params`. Only multi-character names like `ir_d64` become errors.
        //
        // MEASURED before landing, at every scope this box can build: the
        // substitution spec (150 stages, 503.1 s), the EvalIR spec (50.7 s), and
        // the FULL spec via `axiom_ratchet` (3/3, headline still three). The
        // four `free_var_*` probe rows flip to `Unknown identifier` and are
        // pinned below as refusals, so removing this line makes them pass and
        // the test says so.
        spec.env
            .set_option("relaxedAutoImplicit".to_string(), Some("false".to_string()));
        spec
    }

    /// Build ONLY the stage prefix that registers the `.clean` model units
    /// (foundation types through `add_expr_model`), reading the units from
    /// `source`. This is what the W1 fidelity oracle compares: one build from
    /// the files, one from the retained literals, over the same six stages.
    ///
    /// # Errors
    /// Returns `SpecError` if any stage fails.
    #[cfg(test)]
    pub(crate) fn new_model_units_spec(source: super::ModelUnitSource) -> Result<Self, SpecError> {
        let mut spec = Self::new_empty();
        spec.set_model_unit_source(source);
        bundles::run_bundle(&mut spec, bundles::CoreSpecBundle::ModelUnits)?;
        Ok(spec)
    }
}

#[cfg(test)]
pub(super) fn test_bmem_source_rows() -> Vec<(&'static str, &'static str, &'static str)> {
    assert_eq!(BMEM_TRIE_NAMES.len(), 21);
    assert_eq!(BMEM_CORE_NAMES.len(), 153);
    eval_ir_bmem_trie::test_source_rows()
        .into_iter()
        .chain(eval_ir_bmem_core::test_source_rows())
        .collect()
}
