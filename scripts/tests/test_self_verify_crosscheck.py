#!/usr/bin/env python3
"""Exercise the replay runner's refusal paths, independently of proof replay.

These fake processes test orchestration only. The real self_verify_crosscheck.sh
run remains the evidence that Lean actually accepts the exported proof corpus.
"""

import ast
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


REPO = Path(__file__).resolve().parents[2]
FLAGSHIPS = (
    "tc_infer_soundness",
    "bootstrap_infer_sound",
    "whnf_terminates_well_typed_dependent",
    "ir_steps_shared_driver_agreement",
    "impl_bridge_fvar",
    "impl_bridge_fvar_witness",
    "literal_decode_encode",
    "literal_encode_decode",
    "literal_encode_injective",
    "literal_codes_disjoint",
    "literal_kinds_distinct",
    "literal_types_distinct",
    "kernelinfers_literal_result",
    "kernelinfers_nat_not_string",
    "kernelinfers_string_not_nat",
    "impl_bridge_lit",
    "impl_sound_lit",
    "impl_infer_sound_nat_literal",
    "impl_infer_sound_string_literal",
    "instL_preserves_closed_at",
    "instL_preserves_top_level_closed",
    "psubst_closed_cong2",
    "psubst_closed_cong3",
    "psubst_closed_upn_id",
    "psubst_closed_id",
    "name_eqb_symm",
    "univ_lookup_param_cons_compute",
    "univ_lookup_cons_compute",
    "univ_lookup_cons",
    "univ_lookup_succ_zero_absurd",
    "paramSubstN_eq_level_lookup",
    "paramSubstN_eq_lookup_result",
    "param_lookup_hit_witness",
    "param_lookup_short_lists_differ",
    "universe_bridge_congr2",
    "level_subst_eq_substL",
    "impl_inst_levels_list_eq_mapLL",
    "instL_preserves_impl_literal",
    "to_kexpr_at_impl_inst_levels",
    "to_kexpr_impl_inst_levels",
    "to_kexpr_instantiated_binder_witness",
    "to_kexpr_at_rho_independent",
    "to_kexpr_rho_independent",
    "to_kexpr_eq_of_nil",
    "impl_fvar_translation_depends_on_rho",
    "impl_unqualified_rho_independence_refuted",
    "impl_no_fvar_loose_bvar_witness",
    "impl_no_fvar_binder_mdata_witness",
    "to_kexpr_no_fvar_binder_mdata_witness",
    "list_getD_mapLL_substL",
    "level_list_len_mapLL",
    "paramSubstN_mapLL_supported",
    "substL_congr_on_support",
    "substL_param_instantiation_fusion",
    "supported_nonzero_fusion_witness",
    "unsupported_fusion_fails",
    "mapLL_congr_on_support",
    "instL_congr_on_support",
    "instL_instLevels_supported",
    "arity_mapLL",
    "supported_projection_fusion_witness",
    "kconst_arity_check_true",
    "kconst_arity_check_false",
    "kdecl_type_at_intro",
    "kdecl_type_at_missing",
    "kdecl_type_at_wrong_arity",
    "kdecl_type_at_some_inv",
    "kdecl_type_at_some_inv_prop",
    "impl_const_entry_signature",
    "impl_const_entry_no_fvar",
    "impl_schematic_instantiated_type",
    "schematic_tenv_lookup",
    "schematic_tenv_empty",
    "schematic_tenv_polymorphic_witness",
    "schematic_tenv_lookup_zero_witness",
    "schematic_tenv_lookup_one_witness",
    "schematic_tenv_missing_arity_witness",
    "kdecl_type_at_instL_supported_at",
    "kdecl_type_at_instL_supported",
    "kdecl_type_at_instL_nonzero_witness",
    "kdecl_type_at_instL_unsupported_fails",
    "kdecl_type_at_closed",
    "kdecl_type_at_psubst_closed",
    "kdecl_type_at_lift_closed",
    "ctx_lookup_mapLT",
    "ctx_lookup_mapLT_some",
    "typingctx_instL",
    "typingctx_instLevels",
    "defeq_instL",
    "instL_literal_nat",
    "instL_literal_nat_type",
    "instL_literal_string",
    "instL_literal_string_type",
    "typingctxconv_instL",
    "typingctxconv_instLevels",
    "typingctxconv_kdef_instantiated",
    "closed_weaken_empty_of_weaken1",
    "typingctxconv_closed_weaken_empty",
    "tec_defn_inst_typed",
    "tec_defval_typed",
    "kdef_value_at_intro",
    "kdef_value_at_wrong_arity",
    "kdef_value_at_some_inv",
    "kdef_value_at_some_inv_prop",
    "impl_bridge_const",
    "impl_sound_const",
    "impl_infer_sound",
    "impl_infer_sound_polymorphic_constant",
    "impl_infer_sound_constant_zero",
    "impl_infer_sound_constant_one",
    "delta_preserves_typing_ctx",
    "kernelinfers_constant_result",
    "kernelinfers_constant_lookup",
    "kernelinfers_constant_lookup_failure",
    "kernelinfers_constant_wrong_arity",
    "kernelinfers_polymorphic_missing_argument",
    "kdef_value_at_instL_supported_at",
    "kdef_value_at_instL_supported",
    "kapp_fn_instL",
    "kexpr_const_name_instL",
    "kexpr_const_levels_instL",
    "delta_instL_map_append",
    "kapp_args_instL",
    "instL_apply_spine",
    "delta_head_name_instL",
    "delta_head_levels_instL",
    "delta_step_instL_supported",
    "delta_reduces_instL_supported",
    "delta_universe_nonzero_spine_witness",
    "delta_universe_wrong_arity_none",
    "delta_universe_unsupported_initial_step",
    "delta_universe_unsupported_closure_fails",
    "tec_delta_universe_closed",
    "delta_reduct_no_value_at",
    "fvRel_const_levels",
    "delta_bool_and_cong",
    "rank_dominates_b_instL",
    "kexpr_is_lam_b_instL",
    "def_env_ranked_value_at",
    "def_env_all_lam_value_at",
    "whnf_level_list_len_mapLL",
    "whnf_has_defval_mapLL",
    "whnf_consts_defined_instL",
    "whnf_nat_add_cong",
    "whnf_instL_ceiling",
    "def_env_good_value_at",
    "whnf_consts_defined_red_instL",
    "whnf_red_closed_instL",
    "red_env_good_value_at",
    "wh3_stuck_const_name_no_delta",
    "wh3_stuck_app_head_no_delta",
    "delta_wrong_arity_is_stuck",
    "delta_wrong_arity_has_raw_body",
    "delta_stuck_raw_absence_converse_refuted",
    "natTEnv_rec_lookup",
    "natTEnv_rec_typed",
    "natTEnv_rec_missing_argument",
    "genTEnv_nat_fam",
    "genTEnv_nat_rec",
    "genTEnv_nat_c0",
    "iTEnv_lt_c0",
    "iTEnv_lt_rec",
    "genTEnv_nat_rec_typed",
    "iTEnv_lt_rec_typed",
    "mutTEnv_rec_nonzero_lookup",
    "mutTEnv_rec_nonzero_typing",
    "mutTEnv_rec_missing_universe",
    "wTEnv_rec_nonzero_lookup",
    "wTEnv_rec_nonzero_typing",
    "wTEnv_rec_missing_universe",
    "roseTEnv_rec_lookup",
    "roseTEnv_list_rec_lookup",
    "roseTEnv_rec_nonzero_typed",
    "roseTEnv_list_rec_nonzero_typed",
    "roseTEnv_rec_missing_argument",
    "roseTEnv_list_rec_missing_argument",
    "const_head_levels_preserved_cd",
    "const_head_levels_star_preserved",
    "iota_immune_of_guarded_dead_head",
    "iota_neutral_of_guarded_dead_head",
    "nf_head_app_of_guarded_dead_head",
    "hnf3_app_residual_of_guarded_dead_head",
    "guarded_head_wrong_arity_no_value",
    "guarded_head_wrong_arity_raw_present",
    "guarded_head_wrong_arity_nf_head",
    "nat_max_eq_natMax",
    "imax_nat_eq_imaxNat",
    "level_eval_eq_evalL",
    "level_is_nonzero_evalL_sound",
    "levelEqSem_refl",
    "levelEqSem_symm",
    "levelEqSem_trans",
    "levelListEqSem_refl",
    "levelListEqSem_symm",
    "levelListEqSem_view_type",
    "levelListEqSem_view",
    "levelListEqSem_trans",
    "kexprUniverseEq_refl",
    "kexprUniverseEq_symm",
    "kexprUniverseEq_view_type",
    "kexprUniverseEq_view",
    "kexprUniverseEq_trans",
    "kexprUniverseEq_lift_at",
    "kexprUniverseEq_instantiate_bvar_geq",
    "kexprUniverseEq_instantiate_bvar_at",
    "kexprUniverseEq_instantiate_at",
    "kexprUniverseEq_instantiate",
    "kexprUniverseEq_imax_zero",
    "kexprUniverseEq_binder_instantiation_witness",
    "whnf_red_step_star_to_def_eq_in",
    "kernel_infers_in_sound",
    "acceptance_imax_one_one",
    "kernel_infers_in_pi_one",
    "acceptance_pi_one_sound",
    "acceptance_example_delta_trace",
    "acceptance_example_alias_typed",
    "kernel_infers_in_delta_pi",
    "acceptance_delta_pi_sound",
    "acceptance_example_wrong_arity_none",
    "acceptance_example_missing_type_argument",
    "acceptance_seed_has_no_example_alias",
    "acceptance_example_env_not_seed",
    "def_eq_to_def_eq_in",
    "typingctxconv_to_typingctxconv_in",
    "level_imax_eq_sem",
    "kernel_infers_in_pi_smart",
    "acceptance_legacy_beta",
    "acceptance_legacy_zeta",
    "acceptance_legacy_conversion",
    "acceptance_legacy_literal_nat",
    "acceptance_legacy_literal_string",
    "kernel_infers_in_constant_result",
    "kernel_infers_in_constant_inv",
    "kernel_infers_in_constant_lookup_failure",
    "kernel_infers_in_constant_wrong_arity",
    "acceptance_constant_imax_lookup",
    "kernel_infers_in_constant_imax_zero",
    "acceptance_constant_imax_zero_sound",
    "acceptance_constant_imax_one_sound",
    "acceptance_constant_imax_missing_arity",
    "acceptance_constant_imax_missing_lookup",
    "acceptance_constant_imax_missing_argument",
    "kexprListUniverseEq_refl",
    "kexprListUniverseEq_length",
    "kexprListUniverseEq_append",
    "kexprListUniverseEq_tail",
    "kexprListUniverseEq_drop",
    "kexprListUniverseEq_take",
    "kexprUniverseEq_apply_spine",
    "kexprUniverseEq_kapp_fn",
    "kexprUniverseEq_kapp_args",
    "semantic_spine_reassemble_compat",
    "semantic_spine_partition_compat",
    "levelListEqSem_length",
    "levelListEqSem_list_getD",
    "paramSubstN_semantic_values",
    "substL_pointwise_semantic",
    "mapLL_substL_pointwise_semantic",
    "instL_pointwise_semantic",
    "instLevels_semantic_values",
    "kdef_value_at_semantic_values",
    "semantic_delta_universes_related",
    "semantic_delta_lookup_at",
    "semantic_delta_lookup_zero",
    "semantic_delta_lookup_one",
    "semantic_delta_compat_nonzero",
    "semantic_delta_missing_name",
    "semantic_delta_wrong_arity",
    "semantic_delta_no_body_support",
    "semantic_delta_duplicate_params",
    "kexprUniverseEq_const_name",
    "kexprUniverseEq_const_levels",
    "delta_reduct_of_value_some",
    "delta_reduct_semantic_compat",
    "semantic_delta_spine_step_at",
    "semantic_delta_spine_related",
    "semantic_delta_spine_caller",
    "semantic_delta_spine_wrong_arity",
    "semantic_delta_spine_missing_name",
    "kexprUniverseEq_head_name",
    "kexprListUniverseEq_head_some",
    "kexprListUniverseEq_drop_equal_counts",
    "semantic_iota_contractum_compat",
    "iota_reduct_universe_compat",
    "semantic_iota_fixture_success",
    "semantic_iota_fixture_related",
    "semantic_iota_fixture_output_relation",
    "semantic_iota_fixture_imax_zero",
    "semantic_iota_fixture_missing_major",
    "semantic_iota_fixture_missing_rule",
    "semantic_iota_fixture_missing_rec",
    "semantic_iota_fixture_constructor_universe_erasure",
    "ParUniverseTransport",
    "par_reduces_cd_universe_compat_at",
    "par_reduces_cd_universe_compat",
    "ParStarUniverseTransport",
    "par_reduces_cd_star_universe_compat_at",
    "par_reduces_cd_star_universe_compat",
    "semantic_parallel_beta_caller",
    "semantic_parallel_two_step_caller",
    "semantic_join_refl",
    "semantic_join_levels",
    "semantic_join_raw",
    "semantic_join_symm",
    "semantic_join_trans",
    "semantic_join_app",
    "semantic_join_lam",
    "semantic_join_pi",
    "semantic_join_let",
    "semantic_join_proj",
    "def_eq_in_to_semantic_join",
    "semantic_join_mixed_conversion",
    "semantic_join_mixed_caller",
    "par_reduces_cd_star_to_def_eq_in",
    "semantic_join_to_def_eq_in",
    "kexprUniverseEq_sort_injective",
    "kexprUniverseEq_pi_components",
    "semantic_join_sort_injective",
    "semantic_join_pi_components",
    "semantic_join_pi_domain",
    "semantic_join_pi_codomain",
    "def_eq_in_sort_injective",
    "def_eq_in_pi_components",
    "def_eq_in_pi_domain",
    "def_eq_in_pi_codomain",
    "semantic_sort_imax_zero_join",
    "semantic_sort_imax_zero_injective",
    "semantic_sort_imax_zero_syntax_distinct",
    "semantic_join_sort_zero_succ_absurd",
    "def_eq_in_sort_zero_succ_absurd",
    "def_eq_in_pi_zero_succ_domain_absurd",
    "semantic_pi_imax_zero_components",
    "levelListEqSem_substL",
    "kexprUniverseEq_instL",
    "semantic_universe_subst_changes_param",
    "semantic_universe_subst_input_related",
    "semantic_universe_subst_nonidentity_caller",
    "kexprUniverseEq_preserves_closed_at",
    "kernel_infers_in_constant_result_closed",
    "kernel_infers_in_constant_loose_result_refused",
    "semantic_constant_imax_stored_closed",
    "semantic_constant_imax_result_closed",
    "substL_nil_support_id",
    "mapLL_nil_support_id",
    "instL_nil_support_id",
    "mapLT_list_drop",
    "mapLT_list_take",
    "iota_instL_drop_args",
    "iota_instL_take_args",
    "iota_instL_args_length",
    "iota_instL_major_at",
    "iota_instL_fields",
    "iota_instL_apply_spine_reconstruct",
    "iota_instL_contractum",
    "iota_step_instL_paramfree",
    "rec_env_single_rhs_paramfree",
    "iota_inst_supported_env_support",
    "iota_inst_supported_initial_step",
    "iota_inst_supported_spine_caller",
    "iota_inst_supported_nonzero",
    "iota_inst_unsupported_bvar_closed",
    "iota_inst_unsupported_initial_step",
    "iota_inst_unsupported_closure_fails",
    "par_reduces_cd_instL_supported",
    "def_eq_in_instL_supported",
    "def_env_body_param_supported_empty",
    "semantic_reduction_mixed_conversion",
    "semantic_reduction_mixed_instantiation",
    "semantic_reduction_iota_nonzero",
    "typingctxconv_in_instL_supported",
    "typingctxconv_in_instLevels_supported",
    "typingctxconv_in_kdef_instantiated",
    "def_env_body_param_supported_add",
    "rec_env_rhs_paramfree_empty",
    "kdecl_env_type_param_supported_singleton",
    "acceptance_example_parameter_support",
    "acceptance_example_def_body_supported",
    "acceptance_example_types_supported",
    "acceptance_example_schematic_body_typed",
    "acceptance_example_instantiated_body_typed",
    "acceptance_example_instantiated_body_nonzero",
    "acceptance_example_constant_instantiation_caller",
    "acceptance_example_semantic_conversion_typed",
    "acceptance_example_semantic_typing_instantiation_caller",
    "level_strip_offset_eval",
    "level_geq_core_fuel_sound",
    "level_max_core_fuel_sound",
    "ugeq_join_children_refuse",
    "ugeq_join_comparison",
    "ugeq_join_semantic",
    "ugeq_join_subsume_left",
    "ugeq_join_subsume_right",
    "ugeq_join_max_caller",
    "ugeq_fresh_fallback",
    "ugeq_fallback_caller",
    "ugeq_same_base_offset",
    "ugeq_equal_offset_recurse",
    "ugeq_imax_zero_pivot",
    "ugeq_imax_positive",
    "ugeq_adversarial_refused",
    "ugeq_bad_or_would_accept",
    "ugeq_bad_or_semantics_false",
    "ugeq_reversed_order_false",
    "ugeq_zero_fuel_refuses_equal",
    "ugeq_zero_fuel_order_still_true",
    "ugeq_pair_bases_lt",
    "ugeq_core_step_congr",
    "level_geq_core_fuel_stable",
    "level_geq_core_fuel_agrees",
    "level_geq_core_equation",
    "level_geq_core_sound",
    "level_geq_core_fast_equation",
    "level_geq_core_structural_equation",
    "level_geq_core_positive_base_equation",
    "level_geq_core_rhs_max_equation",
    "level_geq_core_lhs_max_fallthrough",
    "ugeq_stable_join_true",
    "ugeq_stable_larger_fuel",
    "ugeq_stable_join_semantic",
    "ugeq_stable_join_fallthrough",
    "ugeq_stable_offset_descent",
    "ugeq_stable_offset_true",
    "ugeq_stable_small_fuel_refuses",
    "ugeq_stable_incomplete_refused",
    "ugeq_stable_incomplete_order",
    "ugeq_stable_semantic_completeness_false",
    "projection_pi_raw_fastpath",
    "projection_parameter_prefix_cons_inv",
    "projection_field_prefix_succ_inv",
    "projection_parameter_graph_unique",
    "projection_field_graph_unique",
    "projection_field_body_closed",
    "projection_field_body_eq_instantiate",
    "projection_count_guard_inv",
    "projection_count_guard_wrong",
    "projection_count_guard_none",
    "projection_telescope_wrong_universe_arity",
    "projection_telescope_wrong_type_arity",
    "projection_telescope_start_inv",
    "projection_ordered_instantiation_coherent",
    "projection_dep_pair_field1",
    "projection_dep_pair_connected",
    "projection_indexed_start_keeps_index",
    "projection_indexed_field1",
    "projection_indexed_connected",
    "projection_parameter_and_index_distinct",
    "projection_type_missing_refused",
    "projection_type_extra_refused",
    "projection_poly_ordered_coherence",
    "projection_universe_missing_refused",
    "projection_universe_extra_refused",
    "projection_polymorphic_start",
    "projection_universe_reordered_computation",
    "projection_universe_constructor_order_computation",
    "projection_parameter_stop_original",
    "projection_parameter_exhaustion_refused",
    "projection_field_nonpi_refused",
    "projection_field_body_loose_one",
    "projection_absent_nat_cases",
    "projection_absent_or_left",
    "projection_absent_or_right",
    "projection_absent_bvar",
    "instantiate_at_absent_independent",
    "instantiate_absent_independent",
    "projection_field_body_unused_binder",
    "projection_bound_instantiated_zero",
    "imaxNat_zero_right",
    "level_is_zero_of_evalL_ones",
    "level_is_zero_evalL_reflect",
    "level_is_zero_substL_true",
    "projection_bound_instantiated_bool_zero",
    "level_zero_nested_imax_caller",
    "level_zero_substitution_caller",
    "level_zero_parameter_before",
    "level_zero_parameter_after",
    "level_zero_false_preservation_refuted",
    "level_zero_bound_parameter_caller",
    "const_delta_step_in",
    "whc3_iota_sound_at_in",
    "hiotap3_discharged_in",
    "reduce_app_head_wh3_par_hw_in",
    "reduce_once_red_wh3_par_hw_in",
    "whnf_fuel_red_wh3_par_hw_in",
    "whnf_fuel_red_wh3_par_in",
    "whnf_fuel_red_wh3_sound_in",
    "wh3_sem_beta_computes",
    "wh3_sem_beta_caller",
    "wh3_sem_let_projection_computes",
    "wh3_sem_let_projection_caller",
    "wh3_sem_delta_computes",
    "wh3_sem_delta_caller",
    "wh3_sem_iota_computes",
    "wh3_sem_iota_caller",
    "wh3_sem_major_starved",
    "wh3_sem_wrong_arity_stuck",
    "projection_substL_identity",
    "projection_mapLL_identity",
    "projection_instL_identity",
    "projection_ctor_type_instantiation",
    "projection_ctor_type_coherent",
    "projection_const_infers",
    "projection_app_infers_raw",
    "projection_single_ctor_inv",
    "projection_single_ctor_intro",
    "projection_meta_guard_inv",
    "projection_meta_guard_intro",
    "projection_meta_bind_intro",
    "projection_resolve_ctor_inv",
    "projection_resolve_trace",
    "projection_resolve_intro",
    "projection_resolve_inv_type",
    "projection_resolve_inv",
    "projection_resolution_whnf",
    "projection_resolution_telescope",
    "projection_metadata_ctor_lookup",
    "projection_metadata_agreement_ordered",
    "projection_metadata_telescope_canonical",
    "projection_resolved_ctor_spine",
    "projection_subject_ready_semantics",
    "projection_subject_ctor_spine",
    "projection_subject_ctor_spine_normalized",
    "projection_metadata_nonempty_resolves",
    "projection_metadata_nonempty_trace",
    "projection_metadata_nonempty_agreement",
    "projection_metadata_missing_ind_refuses",
    "projection_metadata_missing_ctor_refuses",
    "projection_metadata_two_ctors_refuse",
    "projection_metadata_zero_ctors_refuse",
    "projection_metadata_field_bound_refuses",
    "projection_metadata_universe_arity_refuses",
    "projection_metadata_type_arity_refuses",
    "projection_metadata_wrong_name_refuses",
    "projection_metadata_wrong_parent_is_not_runtime_guard",
    "projection_prod_signature_shape",
    "projection_prod_input_shape",
    "projection_prod_nat_inferred",
    "projection_prod_zero_inferred",
    "projection_prod_one_inferred",
    "projection_prod_head_inferred",
    "projection_prod_apply_A_inferred",
    "projection_prod_apply_B_inferred",
    "projection_prod_apply_zero_inferred",
    "projection_prod_subject_inferred",
    "projection_prod_type_inferred",
    "projection_prod_resolves",
    "projection_prod_agreement",
    "projection_prod_subject_ready",
    "projection_prod_subject_semantics",
    "projection_prod_typed_constructor_spine",
    "projection_prod_canonical_parameter_telescope",
    "typed_raw_pi_spine_select",
    "typed_raw_pi_spine_select_at",
    "semantic_typed_spine_select_at",
    "typingctxconv_in_const_spine_select_at",
    "typed_spine_identity_selected_argument",
    "projection_prod_selected_zero_argument",
    "projection_prod_selected_succ_argument",
    # Finite reflected constructor rigidity and current-ParCD transport;
    # these audits do not introduce or prove projection beta.
    "ctor_metadata_no_def",
    "ctor_metadata_no_rec",
    "ctor_metadata_rigid_empty",
    "kctor_for_add_ind_some_inv",
    "ctor_metadata_rigid_add_ind",
    "ctor_metadata_rigid_add_ctor",
    "ctor_metadata_delta_none",
    "reflected_ctor_metadata_rigid",
    "reflected_prod_ctor_lookup",
    "reflected_prod_ctor_no_def",
    "reflected_prod_ctor_no_rec",
    "reflected_prod_value_delta_none",
    "ctor_metadata_iota_none",
    "reflected_prod_value_iota_none",
    "ctor_rigid_def_collision_lookup",
    "ctor_rigid_rec_collision_lookup",
    "ctor_rigid_def_collision_value",
    "ctor_rigid_rec_collision_value",
    "ctor_metadata_def_collision_refused",
    "ctor_metadata_rec_collision_refused",
    "par_reduces_cd_list_refl",
    "par_reduces_cd_list_append",
    "par_reduces_cd_list_tail",
    "par_reduces_cd_list_drop",
    "par_reduces_cd_list_head_some",
    "ctor_metadata_spine_preserved",
    "ctor_metadata_head_preserved",
    "ctor_metadata_spine_length",
    "ctor_metadata_selected_position",
    "ctor_metadata_selected_field",
    "ctor_spine_prod_beta",
    "ctor_spine_prod_step",
    "ctor_spine_prod_head_preserved",
    "ctor_spine_prod_length_preserved",
    "ctor_spine_prod_selected_zero",
    "ctor_spine_prod_selected_one",
    "projection_post_whnf_proj",
    "projection_post_whnf_field_intro",
    "projection_post_whnf_field_inv_type",
    "projection_post_whnf_transport",
    "projection_post_whnf_prod_before_zero",
    "projection_post_whnf_prod_after_zero",
    "projection_post_whnf_prod_before_one",
    "projection_post_whnf_prod_after_one",
    "projection_post_whnf_prod_transport_zero",
    "projection_post_whnf_prod_transport_one",
    "projection_post_whnf_missing_metadata",
    "projection_post_whnf_missing_argument",
    "projection_post_whnf_outer_app_refused",
    "projection_post_whnf_outer_sort_refused",
    "projection_post_whnf_nonconstant_head_refused",
    "projection_post_whnf_struct_name_ignored",
    "projection_post_whnf_prod_universe_arity_ignored",
    "projection_post_whnf_declared_field_count_ignored",
    "projection_post_whnf_field_inv",
    "projection_selected_map_head",
    "projection_post_whnf_field_instantiate_at",
    "projection_post_whnf_instantiate_at",
    "projection_post_whnf_field_lift_at",
    "projection_post_whnf_lift_at",
    "projection_binding_select",
    "projection_binding_substitution_computes",
    "projection_binding_lifting_computes",
    "projection_binding_substitution_caller",
    "projection_binding_lifting_caller",
    "projection_post_whnf_universe_compat",
    "projection_universe_subject_related",
    "projection_universe_source_select",
    "projection_universe_target_select",
    "projection_universe_selected_compat",
    "projection_universe_nonzero_caller",
    "projection_universe_not_syntactic",
    "par_reduces_cd_to_cdp",
    "par_reduces_cdp_list_refl",
    "par_reduces_cdp_list_append",
    "par_reduces_cdp_list_tail",
    "par_reduces_cdp_list_drop",
    "par_reduces_cdp_list_head_some",
    "par_reduces_cdp_list_length",
    "ctor_metadata_spine_preserved_cdp",
    "ctor_metadata_head_preserved_cdp",
    "ctor_metadata_selected_position_cdp",
    "ctor_metadata_selected_field_cdp",
    "ctor_metadata_spine_length_cdp",
    "projection_post_whnf_transport_cdp",
    "cdp_prod_inner_extract",
    "cdp_prod_inner_step",
    "cdp_prod_outer_step",
    "cdp_prod_head_preserved",
    "cdp_prod_length_preserved",
    "cdp_prod_selected_zero",
    "cdp_prod_old_beta_embedded",
    "cdp_prod_outer_extract",
    "cdp_prod_selector_transport",
    "projection_post_whnf_deterministic",
    "par_cdp_projection_beta_beta",
    "par_cdp_projection_beta_cong",
    "par_cdp_prod_beta_projection_join",
    # Actual projection-only confluence, mixed commutation and CDP-star composition.
    "relation_star_single",
    "relation_star_trans",
    "relation_star_bind",
    "relation_join_map",
    "relation_join_swap",
    "relation_diamond_strip",
    "relation_diamond_confluent",
    "relation_union_diamond",
    "relation_union_to_macro",
    "relation_macro_to_union",
    "relation_strong_commute_strip",
    "relation_strong_commute_star",
    "relation_union_confluent",
    "relation_union_confluent_of_strong",
    "cdp_lift_contract_eq",
    "par_lift_cdp",
    "par_subst_same_cdp",
    "par_cdp_nat_select",
    "par_subst_bvar_cdp",
    "par_subst_value_cdp",
    "par_cdp_to_star",
    "par_cdp_star_trans",
    "par_lift_cdp_star",
    "par_subst_same_cdp_star",
    "par_subst_value_cdp_star",
    "par_subst_cdp",
    "par_subst_cdp_star",
    "par_instantiate_cdp",
    "par_instantiate_cdp_star",
    "cdp_binding_projection_step",
    "cdp_binding_lift_caller",
    "cdp_binding_same_subst_caller",
    "cdp_binding_two_sided_caller",
    "cdp_binding_two_sided_star_caller",
    "cdp_binding_beta_step",
    "cdp_binding_beta_lift_caller",
    "cdp_binding_zeta_step",
    "cdp_binding_zeta_subst_caller",
    "projection_parallel_list_refl",
    "projection_parallel_list_append",
    "projection_parallel_list_tail",
    "projection_parallel_list_drop",
    "projection_parallel_list_head_some",
    "projection_parallel_list_length",
    "projection_parallel_const_spine",
    "projection_parallel_selected_position",
    "projection_parallel_selector_transport",
    "projection_parallel_to_cdp",
    "projection_parallel_join_symm",
    "projection_parallel_join_app",
    "projection_parallel_join_lam",
    "projection_parallel_join_pi",
    "projection_parallel_join_forall_",
    "projection_parallel_join_let_cong",
    "projection_parallel_join_proj",
    "projection_parallel_inv_app",
    "projection_parallel_inv_lam",
    "projection_parallel_inv_pi",
    "projection_parallel_inv_let_cong",
    "projection_parallel_inv_proj",
    "projection_parallel_join_extract_cong",
    "projection_parallel_join_extract_extract",
    "projection_parallel_diamond",
    "projection_parallel_strip",
    "projection_parallel_star_confluent",
    "projection_parallel_inner_step",
    "projection_parallel_outer_step",
    "projection_parallel_retained_extract",
    "projection_parallel_retained_root",
    "projection_parallel_retained_cong",
    "projection_parallel_retained_join",
    "projection_parallel_retained_tail",
    "projection_parallel_retained_explicit_meet",
    "projection_parallel_discarded_extract",
    "projection_parallel_discarded_root",
    "projection_parallel_discarded_cong",
    "projection_parallel_discarded_join",
    "projection_parallel_discarded_tail",
    "projection_parallel_discarded_explicit_meet",
    "projection_parallel_retained_star_join",
    "projection_parallel_discarded_embedded",
    "projection_parallel_lift",
    "projection_parallel_subst_same",
    "projection_parallel_nat_select",
    "projection_parallel_subst_bvar",
    "projection_parallel_subst_value",
    "projection_parallel_to_star",
    "projection_parallel_star_trans",
    "projection_parallel_lift_star",
    "projection_parallel_subst_same_star",
    "projection_parallel_subst_value_star",
    "projection_parallel_subst",
    "projection_parallel_subst_star",
    "projection_parallel_instantiate",
    "projection_parallel_instantiate_star",
    "cd_projection_beta_root",
    "cd_projection_beta_source_left",
    "cd_projection_beta_source_right",
    "cd_projection_zeta_root",
    "cd_projection_zeta_source_left",
    "cd_projection_zeta_source_right",
    "cd_projection_extract_root",
    "cd_projection_extract_source_left",
    "cd_projection_extract_source_right",
    "projection_parallel_list_apply",
    "cd_projection_delta_root",
    "cd_projection_dup_instantiate",
    "cd_projection_dup_zero_instantiate",
    "cd_projection_dup_residual",
    "cd_projection_dup_beta_left",
    "cd_projection_dup_beta_right",
    "cd_projection_dup_beta_peak",
    "cd_projection_dup_beta_explicit_meet",
    "cd_projection_dup_zeta_left",
    "cd_projection_dup_zeta_right",
    "cd_projection_dup_zeta_peak",
    "cd_projection_nested_body_run",
    "cd_projection_nested_body_step",
    "cd_projection_nested_instantiate",
    "cd_projection_nested_simultaneous",
    "cd_projection_nested_beta_peak",
    "cd_projection_extract_actual_left",
    "cd_projection_extract_actual_right",
    "cd_projection_extract_actual_peak",
    "cd_projection_extract_actual_explicit_meet",
    "cd_projection_delta_inner_run",
    "cd_projection_delta_inner_step",
    "cd_projection_delta_lookup",
    "cd_projection_delta_run",
    "cd_projection_delta_left",
    "cd_projection_delta_right",
    "cd_projection_delta_actual_peak",
    "cd_projection_delta_refuses_arity",
    "projection_parallel_list_take",
    "projection_parallel_iota_fields_ok",
    "projection_parallel_iota_contractum",
    "cd_projection_iota_root",
    "imix_inner_run",
    "imix_inner_step",
    "imix_source_projection",
    "imix_project_after",
    "imix_project_retained",
    "imix_project_discarded",
    "imix_run_before",
    "imix_run_after",
    "imix_run_retained",
    "imix_run_discarded",
    "imix_old_iota_left",
    "imix_peak_after",
    "imix_peak_retained",
    "imix_peak_discarded",
    "imix_result_projection",
    "imix_explicit_after_meet",
    "imix_discarded_explicit_meet",
    "imix_rhs_once",
    "imix_head_nonzero",
    "imix_fields_guard",
    "imix_arity_guard",
    "imix_refuses_missing_universe",
    "imix_refuses_extra_universe",
    "imix_refuses_short_fields",
    "imix_short_guard_false",
    "imix_nat_rule_lookup",
    "imix_nat_rule_fields",
    "imix_nat_run_before",
    "imix_nat_run_after",
    "imix_nat_projection",
    "imix_nat_peak",
    "imix_nat_old_iota",
    "imix_nat_residual",
    "imix_nat_explicit_meet",
    "projection_parallel_star_congr1",
    "projection_parallel_star_congr2",
    "projection_parallel_star_congr3",
    "cd_projection_peak_app",
    "cd_projection_peak_lam",
    "cd_projection_peak_pi",
    "cd_projection_peak_forall_",
    "cd_projection_peak_let_cong",
    "cd_projection_peak_proj",
    "cd_projection_peak_beta",
    "cd_projection_peak_zeta",
    "cd_projection_strong_commute",
    "cd_projection_strong_dup_beta",
    "cd_projection_strong_dup_zeta",
    "cd_projection_strong_actual_extract",
    "cd_projection_strong_nested_context",
    "cd_projection_strong_nested_body",
    "cd_projection_strong_actual_legs",
    "cd_projection_union_star_single_cd",
    "cd_projection_union_star_single_projection",
    "cd_projection_union_star_trans",
    "cd_projection_union_star_context",
    "cd_projection_union_star_app",
    "cd_projection_union_star_lam",
    "cd_projection_union_star_pi",
    "cd_projection_union_star_forall_",
    "cd_projection_union_star_let_cong",
    "cd_projection_union_star_proj",
    "cdp_to_cd_projection_union_star",
    "cdp_star_to_cd_projection_union_star",
    "cd_projection_union_to_cdp",
    "cd_projection_union_star_to_cdp_star",
    "cdp_union_mixed_projection_leg",
    "cdp_union_mixed_beta_leg",
    "cdp_union_mixed_explicit_trace",
    "cdp_union_mixed_from_parallel",
    "cdp_union_mixed_to_cdp_star",
    "cdp_union_mixed_roundtrip",
    "cdp_confluence_cd_star_to_generic",
    "cdp_confluence_generic_to_cd_star",
    "cdp_confluence_projection_star_to_generic",
    "cdp_confluence_generic_to_projection_star",
    "cdp_confluence_cd_corner",
    "cdp_confluence_projection_corner",
    "cdp_confluence_mixed_corner",
    "cd_projection_union_star_confluent",
    "par_reduces_cdp_star_confluent",
    "par_reduces_cdp_star_confluent_faithful",
    "the_red_env_cdp_star_confluent",
    "cdp_confluence_prod_left",
    "cdp_confluence_prod_right",
    "cdp_confluence_prod_join",
    "cdp_confluence_prod_explicit_meet",
    "par_reduces_cdp_universe_compat_at",
    "par_reduces_cdp_universe_compat",
    "par_reduces_cdp_star_universe_compat_at",
    "par_reduces_cdp_star_universe_compat",
    "cdp_universe_projection_select",
    "cdp_universe_projection_step",
    "cdp_universe_projection_related",
    "cdp_universe_projection_caller",
    "cdp_universe_nonzero_levels",
    "cdp_universe_projection_nonzero",
    "cdp_universe_beta_parallel",
    "cdp_universe_beta_related",
    "cdp_universe_beta_nonzero_transport",
    "cdp_universe_beta_star",
    "cdp_universe_star_nonzero_transport",
    "semantic_join_cdp_refl",
    "semantic_join_cdp_levels",
    "semantic_join_cdp_raw",
    "semantic_join_cdp_symm",
    "semantic_join_cdp_trans",
    "semantic_join_cdp_old_star",
    "semantic_join_to_cdp",
    "the_red_env_semantic_join_cdp_trans",
    "semantic_join_cdp_projection_caller",
    "semantic_join_cdp_level_caller",
    "semantic_join_cdp_composed_caller",
    "semantic_join_cdp_reverse_caller",
    "semantic_join_cdp_old_beta_caller",
    "par_reduces_cdp_star_app",
    "par_reduces_cdp_star_lam",
    "par_reduces_cdp_star_pi",
    "par_reduces_cdp_star_forall_",
    "par_reduces_cdp_star_let_cong",
    "par_reduces_cdp_star_proj",
    "semantic_join_cdp_app",
    "semantic_join_cdp_lam",
    "semantic_join_cdp_pi",
    "semantic_join_cdp_let",
    "semantic_join_cdp_proj",
    "par_reduces_cdp_star_to_def_eq_cdp_in",
    "semantic_join_cdp_to_def_eq_cdp_in",
    "def_eq_cdp_in_to_semantic_join_cdp",
    "def_eq_in_to_cdp_in",
    "def_eq_cdp_projection_computed",
    "def_eq_cdp_nonzero_projection_conversion",
    "def_eq_cdp_nonzero_projection_join",
    "def_eq_cdp_nonzero_projection_roundtrip",
    "def_eq_cdp_capture_projection",
    "def_eq_cdp_old_mixed_embedding",
    "par_reduces_cdp_sort_inv_eq",
    "par_reduces_cdp_pi_inv_eq",
    "par_reduces_cdp_star_sort_inv_eq",
    "par_reduces_cdp_star_pi_inv_eq",
    "semantic_join_cdp_sort_injective",
    "semantic_join_cdp_pi_components",
    "semantic_join_cdp_pi_domain",
    "semantic_join_cdp_pi_codomain",
    "def_eq_cdp_in_sort_injective",
    "def_eq_cdp_in_pi_components",
    "def_eq_cdp_in_pi_domain",
    "def_eq_cdp_in_pi_codomain",
    "cdp_sort_nonzero_step_rigid",
    "cdp_sort_nonzero_star_rigid",
    "cdp_sort_projection_roundtrip",
    "cdp_sort_projection_injective",
    "cdp_pi_projection_step",
    "cdp_pi_projection_step_domain",
    "cdp_pi_projection_star",
    "cdp_pi_projection_star_components",
    "cdp_pi_projection_nonzero_join",
    "cdp_pi_projection_nonzero_domain",
    "cdp_pi_projection_nonzero_codomain",
    "semantic_join_cdp_sort_zero_succ_absurd",
    "def_eq_cdp_in_sort_zero_succ_absurd",
    "def_eq_cdp_in_pi_zero_succ_domain_absurd",
    "dp_disjoint",
    "dp_ctor_no_def",
    "dp_faithful",
    "dp_resolve_run",
    "dp_resolution",
    "dp_agreement",
    "dp_ctor_lookup",
    "dp_field_domains",
    "dp_raw_spine_run",
    "dp_raw_field1_prefix",
    "dp_selected_field1",
    "dp_select_field0",
    "dp_select_field1",
    "dp_field1_domain_conversion",
    "dp_whole_spine",
    "dp_field1_from_whole",
    "dp_actual_whole",
    "dp_actual_selected",
    "dp_actual_domain_conversion",
    "dp_invalid_field_refused",
    "dp_wrong_family_refused",
    "dp_inferred_field1_run",
    "dp_field1_connected",
    "dp_actual_connected",
    "typingctxconv_in_to_cdp_in",
    "dp_cdp_field1_from_whole",
    "dp_cdp_field1_typed",
    "dp_cdp_whole_typed",
    "dp_cdp_old_beta_conversion_embeds",
    "typing_cdp_open_var_embeds",
    "typing_cdp_nat_literal_embeds",
    "typing_cdp_string_literal_embeds",
    "semantic_typing_cdp_generation_convert",
    "typingcdpctxconv_in_generation",
    "typingcdpctxconv_in_app_gen",
    "typingcdpctxconv_in_constant_gen",
    "typingcdpctxconv_in_pi_gen",
    "typingcdpctxconv_in_constant_lookup_failure",
    "cgen_projection_converts",
    "cgen_constant_typed",
    "cgen_app_typed",
    "cgen_actual_app_generation",
    "cgen_actual_constant_generation",
    "cgen_actual_pi_generation",
    "def_eq_cdp_in_beta",
    "def_eq_cdp_in_instantiate_congr",
    "def_eq_cdp_in_instantiate_same",
    "def_eq_cdp_in_instantiate_value",
    "semantic_typing_cdp_const_pi_conversion",
    "typingcdpctxconv_in_const_app_gen",
    "dp_cdp_const_app_rigid",
    "dp_cdp_ctor_partial_typed",
    "dp_cdp_ctor_partial_converted",
    "dp_cdp_const_app_argument",
    "dp_cdp_const_app_codomain",
    "dp_cdp_instantiate_beta_projection",
    "cdp_instantiate_retains_outer_variable",
    "raw_pi_head_canonical_cdp_const",
    "raw_pi_head_canonical_cdp_app",
    "semantic_typed_spine_cdp_nil",
    "semantic_typed_spine_cdp_cons",
    "semantic_typed_spine_cdp_from_trace",
    "typingcdpctxconv_in_const_spine",
    "typingcdpctxconv_in_const_spine_gen",
    "dp_cdp_partial_spine",
    "dp_cdp_partial_arguments",
    "dp_cdp_partial_conversion",
    "dp_cdp_full_through_projection",
    "dp_cdp_full_spine",
    "dp_cdp_full_arguments",
    "cdp_spine_capture_run",
    "cdp_spine_capture_whole",
    "cdp_spine_capture_package",
    "cdp_spine_capture_arguments",
    "ac_well_formed_returns",
    "ac_const_preserves",
    "ac_inductive_preserves",
    "ac_extension_preserves",
    "ac_env_sound_returns",
    "ac_selected_return_guard",
    "ac_well_formed_selected_return",
    "ac_sound_last_inductive_selected",
    "ac_existing_admitted_caller",
    "ac_nonuniform_environment_refused",
    "ac_nonuniform_guard_false",
    "ac_uniform_parameter_guard_true",
    "rpa_family_typed",
    "rpa_self_typed",
    "rpa_A_typed",
    "rpa_B_typed",
    "rpa_return_typed",
    "rpa_x_domain_typed",
    "rpa_y_domain_typed",
    "rpa_ctor_typed",
    "rpa_fields_bounded",
    "rpa_ctors_typed",
    "rpa_well_formed",
    "rpa_positive",
    "rpa_extension",
    "rpa_env_sound",
    "rpa_uniform_from_admission",
    "rpa_family_name",
    "rpa_ctor_name",
    "rpa_names_distinct",
    "rpa_family_signature",
    "rpa_close_self",
    "rpa_ctor_signature",
    "rpa_family_metadata",
    "rpa_ctor_metadata",
    "rpa_family_lookup",
    "rpa_ctor_lookup",
    "rpa_family_decl_lookup",
    "rpa_ctor_decl_lookup",
    "rpa_connected_admission",
    "arc_is_bvar_eq_sound",
    "arc_return_guard_spine",
    "arc_admitted_selected_arity",
    "arc_admitted_selected_spine",
    "arc_sound_selected_spine",
    "arc_prod_spine_from_admission",
    "arc_prod_close_canonical",
    "arc_prod_source_return",
    "arc_raw_underflow_guard_passes",
    "arc_underflow_arity_refuses",
    "gcc_sub_le",
    "gcc_slot_below",
    "gcc_close_self_bvar",
    "gcc_close_parameter_bvar",
    "gcc_bvar_const_count",
    "gcc_bvar_const_return",
    "gcc_count_pi_close_const",
    "gcc_add_succ_transfer",
    "gcc_return_type_close_const",
    "gcc_return_type_close_self",
    "gcc_close_return_spine",
    "gcc_admitted_return_named",
    "gcc_admitted_closed_arity",
    "gcc_prod_admitted_named",
    "gcc_prod_source_named",
    "gcc_prod_source_slots",
    "gcc_prod_source_count",
    "gcc_prod_closed_arity",
    "gcc_underflow_full_guard_refuses",
    "gcc_underflow_raw_guard_passes",
    "gcc_underflow_captures_parameter",
    "nig_and_intro",
    "nig_not_true_false",
    "nig_slots_length",
    "nig_args_sound",
    "nig_args_complete",
    "nig_head_sound",
    "nig_head_complete",
    "nig_strict_sound",
    "nig_strict_complete",
    "nig_strict_decompose",
    "nig_strict_arity",
    "nig_prefix_bound",
    "nig_checked_indices_sound",
    "nig_selected_member_count",
    "nig_or_elim_prop",
    "nig_block_free_sound",
    "nig_indices_free_at",
    "nig_index_excludes_member",
    "nig_pi_domains_length",
    "nig_eq_actual_guard",
    "nig_eq_actual_facts",
    "nig_eq_actual_arity",
    "nig_eq_prefix_guard",
    "nig_eq_caller_bound",
    "nig_eq_member_count",
    "nig_eq_suffix_exclusion",
    "nig_eq_field_count_is_not_index_count",
    "nig_two_members_left",
    "nig_two_members_right",
    "nig_two_member_selected_count",
    "nig_two_member_prefix_bound",
    "nig_refuses_wrong_family",
    "nig_refuses_nonconstant_head",
    "nig_refuses_missing_index",
    "nig_refuses_extra_index",
    "nig_refuses_wrong_member_index_count",
    "nig_refuses_constant_parameter",
    "nig_refuses_own_index",
    "nig_refuses_sibling_index",
    "nig_refuses_wrong_levels",
    "nig_refuses_shared_domain",
    "nig_refuses_prefix_underflow",
    "nig_refuses_mutual_app_function",
    "nig_refuses_mutual_app_argument",
    "nig_refuses_mutual_lam_domain",
    "nig_refuses_mutual_lam_body",
    "nig_refuses_mutual_pi_domain",
    "nig_refuses_mutual_pi_body",
    "nig_refuses_mutual_let_type",
    "nig_refuses_mutual_let_value",
    "nig_refuses_mutual_let_body",
    "nig_refuses_mutual_projection_subject",
    "nig_refuses_raw_semantic_level",
    "nig_projection_label_not_occurrence",
    "nig_level_parameter_not_occurrence",
    "nig_checked_index_underflow",
    "nig_missing_member",
    "nig_strict_computed_suffix",
    "nig_eq_actual_suffix_free",
    "nig_eq_actual_decomposition",
    "nig_eq_actual_suffix_exact",
    "nig_eq_actual_member_exclusion",
    "nig_refuses_swapped_eq_parameters",
    "nig_refuses_same_length_level_name",
    "nig_refuses_reordered_level_names",
    "nig_refuses_genuine_const_parameter",
    "nig_eq_stored_inductive_lookup",
    "nig_eq_stored_constructor_lookup",
    "nig_eq_stored_inductive_signature",
    "nig_eq_stored_constructor_signature",
    "nig_eq_tenv_inductive_signature",
    "nig_eq_tenv_constructor_signature",
    "nig_eq_stored_constructor_parent",
    "nig_eq_stored_block_member",
    "nig_eq_stored_constructor_member",
    "nig_eq_stored_block_exact",
    "nig_eq_stored_constructor_index",
    "nig_eq_stored_parameter_agreement",
    "nig_eq_stored_universe_parameters",
    "nig_eq_stored_constructor_count",
    "nig_eq_extracted_former_count",
    "nig_eq_extracted_domain_count",
    "nig_eq_domains_from_former",
    "nig_eq_connected_stored_context",
    "nrb_option_selected",
    "nrb_option_resolve",
    "nrb_all_index_at",
    "nrb_names_eq_sound",
    "nrb_nat_some_sound",
    "nrb_block_walk_select",
    "nrb_selected_constructor",
    "nrb_demo_whole",
    "nrb_demo_selected_g",
    "nrb_demo_other_parent_refuses",
    "nrb_demo_other_index_refuses",
    "nrb_demo_member_arity_refuses",
    "nrb_demo_swapped_block_refuses",
    "nrb_demo_missing_refuses",
    "nrb_demo_wrong_kind_refuses",
    "ict_kind_append",
    "ict_kind_append_fresh",
    "ict_kind_append_seen",
    "ict_kind_add_ind_same",
    "ict_kind_add_ind_other",
    "ict_kind_add_ctor_same",
    "ict_kind_add_ctor_other",
    "ict_ctor_append",
    "ict_ctor_append_fresh",
    "ict_ctor_append_seen",
    "ict_ctor_add_ind_same",
    "ict_ctor_add_ind_other",
    "ict_ctor_add_ctor_same",
    "ict_ctor_add_ctor_other",
    "ict_eq_kind",
    "ict_eq_ctor",
    "ict_eq_unrelated_kind",
    "ict_eq_ctor_shadows_ind",
    "ict_eq_ind_shadows_ctor",
    "nsi_mem_cons_false_head",
    "nsi_mem_cons_false_tail",
    "nsi_mem_cons_false_intro",
    "nsi_mem_cons_true_head",
    "nsi_mem_cons_true_tail",
    "nsi_unique_cons_head",
    "nsi_unique_cons_tail",
    "nsi_unique_cons_intro",
    "nsi_mem_append_false_left",
    "nsi_mem_append_false_right",
    "nsi_unique_append_left",
    "nsi_unique_append_right",
    "nsi_unique_append_cross",
    "nsi_unique_append_cross_right",
    "nsi_mem_append_false_intro",
    "nsi_unique_append_remove_middle",
    "nsi_at_mem",
    "nsi_at_name_at",
    "nsi_ctor_install_absent",
    "nsi_ctor_install_selected",
    "nsi_ctor_install_selected_zero",
    "nsi_mem_append_true_left",
    "nsi_source_unique_tail",
    "nsi_source_head_ctors_unique",
    "nsi_member_install_absent",
    "nsi_source_head_ctor_other",
    "nsi_source_head_ctor_tail_absent",
    "nsi_member_head_ctor_selected",
    "nsi_member_install_ctor_selected",
    "nsi_raw_ctor_lookup_installed",
    "nsi_demo_unique",
    "nsi_demo_second_ctor",
    "nsi_demo_f_indices",
    "nsi_demo_g_indices",
    "nsi_demo_unrelated_old_lookup",
    "nsi_demo_cross_kind_collision",
    "nsi_demo_later_family_shadows_ctor",
    "nsi_ctor_install_kind_absent",
    "nsi_member_install_kind_absent",
    "nsi_source_head_family_tail_absent",
    "nsi_member_head_kind_selected",
    "nsi_member_install_kind_selected",
    "nsi_raw_kind_lookup_installed",
    "nsi_raw_selected_lookups",
    "nfi_demo_second_family",
    "nfi_demo_unrelated_old_kind",
    "nfi_demo_preserves_captured_eq",
    "nfi_demo_six_equation_consumer",
    "nsi_raw_member_name_at",
    "nsi_member_ctor_name_at",
    "nsi_raw_first_name_at",
    "nsi_demo_g_member_position",
    "nsi_demo_cg2_constructor_position",
    "nwr_all_index_names_eq",
    "nwr_all_index_at",
    "nwr_raw_success_unique",
    "nwr_ctor_leaf_agree",
    "nwr_ctor_walk_agree",
    "nwr_member_leaf_agree",
    "nwr_member_walk_agree",
    "nwr_installed_block_fields",
    "nwr_installed_return_of_raw",
    "nwr_selected_constructor_from_raw",
    "nwr_selected_strict_facts",
    "nwr_demo_raw_success",
    "nwr_demo_installed_success",
    "nwr_demo_selected_second_ctor",
    "nwr_empty_outer_refuses",
    "nwr_empty_raw_fold_true",
    "nwr_empty_ctor_member_accepts",
    "nwr_empty_ctor_installed_success",
    "nwr_cross_kind_raw_refuses",
    "nwr_bad_other_member_refuses",
    "nwr_selected_local_still_accepts",
    "nwr_short_former_refuses",
    "nwr_wrong_level_refuses",
    "sfa_const_entries",
    "sfa_inductive_entries",
    "sfa_extension_entries",
    "sfa_sound_entries",
    "sfa_entries_at",
    "sfa_stored_family_admission",
    "sfa_prior_family_caller",
    "sfa_constant_tail_caller",
    "dia_entries_sound",
    "dia_stored_constant_admission",
    "dia_stored_constant_prior_sound",
    "dia_stored_family_prior_sound",
    "dia_input_admitted",
    "dia_input_to_old_chain",
    "dia_old_chain_trans",
    "dia_chain_to_old_chain",
    "dia_input_preserves_sound",
    "dia_chain_admitted",
    "dia_chain_sound",
    "dia_fresh_family",
    "dia_fresh_constant",
    "dia_reuse_family",
    "dia_reuse_constant",
    "dia_mixed_chain",
    "dia_mixed_admissions",
    "dia_mixed_preservation",
    "dia_reused_family_admitted",
    "dia_reused_constant_admitted",
    "projection_unused_outer_bvar",
    "projection_unused_outer_not_closed",
    "projection_unused_nested_lambda",
    "projection_unused_nested_pi_let",
    "projection_live_binder_independence_false",
    "projection_nested_live_binder_present",
    "projection_occurs_bound_lam_absent",
    "projection_occurs_bound_pi_absent",
    "projection_occurs_outer_pi_present",
    "projection_occurs_bound_let_absent",
    "projection_occurs_outer_let_present",
    "projection_positivity_nested_self_refused",
    "projection_positivity_bound_domain_allowed",
    "projection_ctor_nested_self_refused",
    "projection_ctor_bound_domain_allowed",
    "projection_ctor_list_nested_self_refused",
    "projection_ctor_list_bound_domain_allowed",
    "projection_return_one_parameter_allowed",
    "projection_return_two_parameters_allowed",
    "projection_return_swapped_parameters_refused",
    "projection_return_missing_parameter_refused",
    "projection_ctor_parameter_return_allowed",
    "projection_ctor_list_parameter_return_allowed",
    "env_freshness_and_intro",
    "env_freshness_and_false_right",
    "ctor_ids_fresh_head_refused",
    "ctor_ids_fresh_tail_refused",
    "kenv_stored_ctor_refused",
    "kenv_occupied_const_preserved",
    "kenv_occupied_inductive_preserved",
    "fresh_ctor_decls_nil",
    "fresh_ctor_decls_cons_intro",
    "fresh_ctor_decls_head_old",
    "fresh_ctor_decls_head_family",
    "fresh_ctor_decls_head_distinct",
    "fresh_ctor_decls_tail",
    "well_formed_ctor_decls_fresh",
    "fresh_ctor_decls_occupied_refused",
    "fresh_ctor_decls_self_refused",
    "fresh_ctor_decls_duplicate_refused",
    "fresh_decl_occupied_refused",
    "env_freshness_ctor_typed",
    "env_freshness_well_formed",
    "env_freshness_extension",
    "env_freshness_first_extension",
    "env_freshness_first_sound",
    "env_freshness_second_extension",
    "env_freshness_second_accepted",
    "env_freshness_acceptance_extends",
    "env_freshness_acceptance_preserves_sound",
    "env_freshness_const_extension",
    "env_freshness_const_accepted",
    "env_freshness_const_preserves_sound",
    "env_freshness_stored_ctor_refused",
    "env_freshness_existing_ctor_refused",
    "env_freshness_existing_family_refused",
    "env_freshness_self_family_refused",
    "env_freshness_intra_list_refused",
    "env_freshness_reducible_const_refused",
    "env_freshness_opaque_const_refused",
    "env_freshness_old_ctor_still_refused",
    "env_freshness_nonadjacent_duplicate_refused",
    "recursor_rhs_at_guard_inv",
    "recursor_rhs_at_guard_inv_prop",
    "recursor_rhs_at_intro",
    "recursor_rhs_at_wrong_arity",
    "recursor_rhs_at_some_inv",
    "recursor_rhs_at_some_inv_prop",
    "recursor_rhs_at_instL_supported",
    "recursor_rhs_instance_closed_at",
    "recursor_rhs_at_preserves_closed_at",
    "recursor_rhs_at_semantic_values",
    "recursor_rhs_fixture_supported",
    "recursor_rhs_fixture_closed",
    "recursor_rhs_fixture_step",
    "recursor_rhs_nonzero",
    "recursor_rhs_missing",
    "recursor_rhs_extra",
    "recursor_rhs_prop_inversion",
    "recursor_rhs_closed_nonzero",
    "recursor_rhs_fusion_nonzero",
    "recursor_rhs_semantic_nonzero",
    "recursor_rhs_unsupported_fusion_fails",
    "level_offsets_bound_count",
    "level_offsets_bound_base",
    "level_cap_inc_below",
    "level_cap_inc_saturated",
    "level_offset_cap_eq",
    "level_geq_count_step_nat",
    "level_geq_cap_step_nat",
    "ugeq_core_step_bounded_congr",
    "level_geq_cap_fuel_eq",
    "level_geq_cap_core_eq",
    "level_geq_cap_fuel_agrees",
    "level_geq_cap_core_sound",
    "level_geq_cap_core_equation",
    "ugeq_cap_nonzero_compare",
    "ugeq_cap_nonzero_bridge",
    "ugeq_cap_nonzero_semantic",
    "ugeq_cap_join_fallthrough",
    "ugeq_cap_boundary_count",
    "ugeq_cap_boundary_exact_count",
    "ugeq_cap_boundary_accepts",
    "ugeq_cap_boundary_raw_refuses",
    "ugeq_cap_boundary_order_false",
    "ugeq_cap_boundary_bound_false",
    "ugeq_cap_top_count_still_bounded",
    "ugeq_cap_hidden_subterm_bound_false",
    "ugeq_cap_unbounded_correspondence_false",
    "semantic_typing_generation_convert",
    "typingctxconv_in_generation",
    "typingctxconv_in_app_gen",
    "typingctxconv_in_constant_gen",
    "typingctxconv_in_pi_gen",
    "typingctxconv_in_constant_lookup_failure",
    "semantic_typing_constant_conv_caller",
    "semantic_typing_constant_gen_caller",
    "semantic_typing_constant_missing_caller",
    "semantic_typing_app_lookup",
    "semantic_typing_app_function",
    "semantic_typing_app_conv_caller",
    "semantic_typing_app_gen_caller",
    "semantic_typing_pi_conv_caller",
    "semantic_typing_pi_gen_caller",
    "level_succ_path_implies_offsets",
    "level_add_offset_eval",
    "level_add_offset_path",
    "level_add_offset_count",
    "level_strip_offset_path",
    "level_add_offset_offsets",
    "offset_natMax_add_right",
    "offset_natMax_assoc",
    "level_raw_max_singleton",
    "level_max_restore_zero",
    "level_max_restore_singleton",
    "level_flatten_into_nonempty",
    "level_flatten_raw_eval",
    "level_flatten_raw_path",
    "level_max_restore_sem",
    "level_flatten_restore_sem",
    "level_max_restore_path",
    "level_flatten_restore_path",
    "level_max_restore_offsets",
    "level_flatten_restore_offsets",
    "offset_spine_output_exact",
    "offset_spine_semantic",
    "offset_spine_weak_input",
    "offset_spine_weak_output_false",
    "offset_spine_weak_preservation_false",
    "offset_spine_safe_output",
    "offset_spine_safe_from_members",
    "offset_spine_capped_caller",
    "offset_spine_sort_caller",
    "offset_spine_flatten_order",
    "offset_spine_flatten_barriers",
    "offset_spine_empty_sem_false",
    "offset_spine_empty_path_false",
    "offset_spine_unqualified_distribution_false",
    "recmeta_signature_mk",
    "natRecMeta_signature",
    "genRecMeta_nat_signature",
    "iRecMeta_lt_signature",
    "mutRecMeta_deg_signature",
    "wRecMeta_signature",
    "roseRecMeta_signature",
    "roseListRecMeta_declared_signature",
    "def_eq_in_beta",
    "def_eq_in_instantiate_congr",
    "def_eq_in_instantiate_same",
    "def_eq_in_instantiate_value",
    "semantic_typing_const_pi_conversion",
    "typingctxconv_in_const_app_gen",
    "semantic_dependent_app_lookup",
    "semantic_dependent_app_argument_typed",
    "semantic_dependent_app_typed",
    "semantic_dependent_codomain_caller",
    "RecEnvRhsClosed",
    "recenv_closed_raw_rhs",
    "recenv_lift_closed_raw_rhs",
    "recenv_closed_to_lift_closed",
    "recenv_lift_closed_to_closed",
    "recenv_closed_rhs_instance",
    "recenv_lift_closed_rhs_instance",
    "recenv_closed_rhs_at",
    "recenv_lift_closed_rhs_at",
    "recursor_schematic_parameter_supported",
    "nat_rec_rhs_zero_instLevels",
    "nat_rec_rhs_zero_param_support",
    "nat_rec_rhs_zero_stored_support",
    "nat_rec_rhs_zero_stored_closed",
    "nat_rec_rhs_zero_guarded",
    "nat_rec_rhs_zero_instance_closed",
    "nat_rec_rhs_zero_self_parameter",
    "nat_rec_rhs_succ_instLevels",
    "nat_rec_rhs_succ_param_support",
    "nat_rec_rhs_succ_stored_support",
    "nat_rec_rhs_succ_stored_closed",
    "nat_rec_rhs_succ_guarded",
    "nat_rec_rhs_succ_instance_closed",
    "nat_rec_rhs_succ_self_parameter",
    "w_rec_rhs_instLevels",
    "w_rec_rhs_param_support",
    "w_rec_rhs_stored_support",
    "w_rec_rhs_stored_closed",
    "w_rec_rhs_guarded",
    "w_rec_rhs_instance_closed",
    "w_rec_rhs_self_parameter",
    "nat_rec_rhs_old_storage_double_instantiates",
    "nat_rec_rhs_old_storage_not_once",
    "gen_rhs_instL_piN",
    "gen_rhs_instL_lamN",
    "gen_rhs_instL_ihTel",
    "gen_rhs_instL_bvarSeq",
    "gen_rhs_instL_bvar_spine",
    "gen_rhs_instL_minorTy",
    "gen_rhs_instL_minorsLam",
    "gen_rhs_mapLT_natural",
    "gen_rhs_instL_rec_call",
    "gen_rhs_instL_recursive_spine",
    "genRecRhsBody_instL",
    "genRecRhs_instL",
    "genRecRhs_schematic_instance",
    "genRecRhs_schematic_guarded",
    "genRecRhs_schematic_nat_zero",
    "genRecRhs_schematic_nat_succ",
    "genRecRhs_schematic_self_parameter",
    "iota_contractum_at_guard_inv",
    "iota_contractum_at_guard_inv_type",
    "iota_contractum_at_intro",
    "iota_tail_fixture_accepts",
    "iota_tail_fixture_intro",
    "iota_tail_fixture_invert",
    "iota_tail_fixture_missing_universe",
    "iota_tail_fixture_extra_universe",
    "iota_tail_fixture_missing_field",
    "raw_pi_spine_trace_nil",
    "raw_pi_spine_trace_cons",
    "raw_pi_spine_trace",
    "raw_pi_head_canonical_const",
    "raw_pi_head_canonical_app",
    "semantic_typed_spine_nil",
    "semantic_typed_spine_cons",
    "semantic_typed_spine_from_trace",
    "typingctxconv_in_const_spine",
    "typingctxconv_in_const_spine_gen",
    "typed_spine_identity_body_typed",
    "typed_spine_identity_stored_body_typed",
    "typed_spine_identity_lookup",
    "typed_spine_identity_run",
    "typed_spine_identity_result_convert",
    "typed_spine_identity_applied",
    "typed_spine_identity_applied_converted",
    "typed_spine_identity_package",
    "typed_spine_identity_arguments",
    "typed_spine_identity_conversion",
    "typed_spine_identity_recovered_head",
    "raw_pi_spine_empty",
    "raw_pi_spine_sort_refuses",
    "iota_reduct_full_inv",
    "iota_reduct_full_inv_type",
    "iota_reduct_full_recon",
    "iota_reduct_some_inv",
    "iota_reduct_some_inv_type",
    "iota_reduct_full_roundtrip",
    "iota_view_fixture_success",
    "iota_view_fixture_roundtrip",
    "iota_view_fixture_compat",
    "iota_view_fixture_compat_type",
    "iota_view_fixture_missing_universe",
    "iota_view_fixture_extra_universe",
    "iota_view_fixture_missing_field",
    "iota_contractum_at_none_inv",
    "iota_contractum_at_none_inv_type",
    "iota_contractum_at_none_of_fields_false",
    "iota_contractum_at_none_of_arity_false",
    "iota_contractum_at_none_arity_of_fields",
    "iota_tail_declines_missing_field",
    "iota_tail_declines_missing_field_case",
    "iota_tail_declines_missing_universe",
    "iota_tail_declines_missing_universe_case",
    "iota_tail_declines_missing_universe_arity",
    "iota_tail_declines_extra_universe",
    "iota_tail_declines_extra_universe_case",
    "iota_tail_declines_extra_universe_arity",
    "const_spine_length_preserved_cd",
    "const_spine_length_star_preserved",
    "ctor_spine_length_preserved_cd",
    "ctor_spine_length_preserved_star",
    "ctor_spine_test_beta",
    "ctor_spine_test_first",
    "ctor_spine_test_second",
    "ctor_spine_test_trace",
    "ctor_spine_test_lookup",
    "ctor_spine_test_one_count",
    "ctor_spine_test_star_count",
    "ctor_spine_test_exact_length",
    "prepass_tail_fixture_whc_accepts",
    "prepass_tail_fixture_whc3_accepts",
    "prepass_tail_fixture_missing_universe_stuck",
    "prepass_tail_fixture_extra_universe_stuck",
    "prepass_tail_fixture_missing_field_stuck",
    "prepass_tail_fixture_starved_before_guards",
    "prepass_tail_fixture_missing_universe_uses_ktail",
    "prepass_tail_fixture_extra_universe_uses_ktail",
    "prepass_tail_fixture_missing_field_uses_ktail",
    "whc_tail_args_congr",
    "whc_swap_tail",
    "semantic_iota_head_levels",
    "semantic_iota_fields_guard",
    "semantic_iota_arity_guard",
    "semantic_iota_fixture_missing_universe",
    "semantic_iota_fixture_extra_universe",
    "iota_instL_head_level_length",
    "iota_instL_fields_guard",
    "iota_instL_arity_guard",
    "iota_instL_rhs_instance",
    "levelParamSupport_nil_weaken",
    "levelListParamSupport_nil_weaken",
    "kexprParamSupport_nil_weaken",
    "rec_env_rhs_paramfree_supported",
    "iota_step_instL_supported",
    "rec_env_single_rhs_property",
    "rec_env_single_rhs_supported",
    "iota_inst_schematic_supported",
    "iota_inst_schematic_initial",
    "iota_inst_schematic_caller",
    "iota_inst_schematic_self_parameter",
    "iota_inst_schematic_nonzero_transport",
    "rec_env_rhs_supported_empty",
    "ifg_hlevels_guarded",
    "ifg_hfields_guarded",
    "ifg_harity_guarded",
    "ifg_hinstance_guarded",
    "ifg_hfinal_guarded",
    "competing_ctor_spine_views",
    "competing_ctor_spine_length",
    "stuck_major_fields_short_no_firing",
    "competing_ctor_spine_actual_trace",
    "par_reduces_c_preserves_kapp_fn_nr",
    "under_applied_levels_preserved_cd",
    "iota_neutral_of_stuck_recursor_spine",
    "hno_at",
    "slot_res_at",
    "hnf3_stuck_all",
    "hnf3_full",
    "delta_cong_preserves_kapp_fn",
    "par_reduces_p_preserves_kapp_fn_below_boundary",
    "under_levels_fixture_trace",
    "under_levels_fixture_preserved",
    "fvRel_iota_bisim",
    "par_reduces_p_app_redex",
    "par_reduces_p_reduct_cong",
    "par_reduces_p_reduct_cong_spine",
    "par_reduces_p_app_reduct_cong_minimal",
    "app_redex_tri",
    "rec_env_reduct_not_redex_of_b",
    "whc_fires_plain_gen",
    "whc3_iota_sound_at",
    "hiotap3_discharged",
    "whcd3_iota_sound_at",
    "hiotad3_discharged",
    "iota_case_a_contradiction",
    "iota_case_a_contradiction_type",
    "wh_step_mono_app_iota_case",
    "iota_reduct_red_closed",
    "iota_reduct_defined_red",
    "stuck_major_iota_arm_absurd",
    "stuck_major_app_arm",
    "stuck_major_step_inv",
    "stuck_major_star_inv",
    "iota_immune_of_stuck_major",
    "par_reduces_p0_redex_preserved_boundary",
    "nz_nat_typed",
    "nz_zero_typed",
    "nz_succ_typed",
    "nz_motive_typed",
    "nz_zero_domain_typed",
    "nz_sarm_typed",
    "nz_rhs_typed",
    "nz_stored_rhs_typed",
    "nz_typing_to_semantic",
    "nz_motive_core_typed",
    "nz_minor_core_typed",
    "nz_motive_beta",
    "nz_minor_type_conversion",
    "nz_motive_argument_typed",
    "nz_zero_argument_typed",
    "nz_minor_argument_typed",
    "nz_input_typed",
    "nz_guarded_step",
    "nz_raw_result_typed",
    "typed_raw_pi_spine_apply",
    "typed_raw_pi_spine_const_apply",
    "typed_raw_pi_spine_identity_trace",
    "typed_raw_pi_spine_identity_body_apply",
    "typed_raw_pi_spine_identity_const_apply",
    "nz_zero_after_m_eq",
    "nz_zero_sarm_after_z_eq",
    "nz_zero_after_z_eq",
    "nz_zero_after_s_eq",
    "nz_zero_typed_spine",
    "nz_general_raw_result_typed",
    "nz_general_guarded_step",
    "nz_general_guarded_result_typed",
    "nz_general_nonzero_caller",
    "nz_general_nonzero_caller_nat",
    "nz_general_nonzero_step",
    "nz_zero_spine_open_motive_control",
    "nz_zero_input_after_m_eq",
    "nz_zero_input_after_z_eq",
    "nz_zero_input_after_s_eq",
    "nz_zero_input_after_major_eq",
    "nz_zero_input_typed_spine",
    "nz_general_input_typed",
    "nz_general_nonzero_input",
    "rfnz_parameter_list",
    "rfnz_signature_shape",
    "rfnz_nat_lookup",
    "rfnz_zero_lookup",
    "rfnz_succ_lookup",
    "rfnz_rec_lookup",
    "rfnz_nat_typed",
    "rfnz_zero_typed",
    "rfnz_succ_typed",
    "rfnz_motive_typed",
    "rfnz_zero_domain_typed",
    "rfnz_sarm_typed",
    "rfnz_rhs_typed",
    "rfnz_stored_rhs_shape",
    "rfnz_stored_rhs_typed",
    "rfnz_actual_metadata",
    "rfnz_actual_zero_rule",
    "rfnz_lookup_rhs_typed",
    "rfnz_rec_signature_supported",
    "rfnz_tenv_extend_supported",
    "rfnz_tenv_supported",
    "rfnz_rhs_instance_shape",
    "rfnz_rule_type_instance_shape",
    "rfnz_lookup_instance_typed",
    "rfnz_actual_instance_typed",
    "rfnz_self_parameter_instance_typed",
    "rfnz_rec_typed",
    "rfnz_motive_core_typed",
    "rfnz_minor_core_typed",
    "rfnz_motive_beta",
    "rfnz_minor_type_conversion",
    "rfnz_motive_argument_typed",
    "rfnz_zero_argument_typed",
    "rfnz_minor_argument_typed",
    "rfnz_input_typed",
    "rfnz_guarded_step",
    "rfnz_raw_result_typed",
    "rfnz_source_tenv_eq",
    "rfnz_source_lookup_agrees",
    "rfnz_source_tenv_supported",
    "rfnz_source_stored_rhs_typed",
    "rfnz_source_lookup_instance_typed",
    "rfnz_source_actual_instance_typed",
    "rfnz_source_input_typed",
    "rfnz_source_raw_result_typed",
    "rfnzg_zero_after_m_eq",
    "rfnzg_zero_sarm_after_z_eq",
    "rfnzg_zero_after_z_eq",
    "rfnzg_zero_after_s_eq",
    "rfnzg_zero_typed_spine",
    "rfnzg_zero_spine_open_motive_control",
    "rfnzg_zero_input_after_m_eq",
    "rfnzg_zero_input_after_z_eq",
    "rfnzg_zero_input_after_s_eq",
    "rfnzg_zero_input_after_major_eq",
    "rfnzg_zero_input_typed_spine",
    "rfnzg_source_rec_lookup",
    "rfnzg_source_zero_typed",
    "rfnzg_source_general_raw_result_typed",
    "rfnzg_source_general_input_typed",
    "rfnzg_source_general_guarded_step",
    "rfnzg_source_motive_argument_typed",
    "rfnzg_source_zero_argument_typed",
    "rfnzg_source_minor_argument_typed",
    "rfnzg_source_nonzero_input",
    "rfnzg_source_nonzero_input_nat",
    "rfnzg_source_nonzero_raw_result",
    "rfnzg_source_nonzero_raw_result_nat",
    "rfnzg_source_nonzero_step",
    "ReplayBridge.sub_agrees",
    "ReplayBridge.ir_nat_ltb_agrees",
    "ReplayBridge.ir_nat_eqb_agrees",
    "ReplayBridge.ir_nat_sub_ltb_agrees",
    "ReplayBridge.ir_nat_sub_eqb_agrees",
)


def _ict_rust_masker():
    """Share the repository lexer between partition reading and mutations."""
    import importlib.util

    path = REPO / "scripts/crystal_freshness_scope.py"
    spec = importlib.util.spec_from_file_location("ict_rust_masker", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.mask_code


def _ict_source_partition(source, *, allow_inductives=False,
                          allow_indexed_inductives=False):
    """Read this unit's literal-only arrays; never count Rust source mentions.

    The repository masker owns Rust comments/literals and offset preservation.
    This bounded reader accepts only the current const-array/tuple grammar;
    unsupported expressions fail closed rather than becoming missing entries.
    """
    mask_code = _ict_rust_masker()
    code = mask_code(source)
    literals = mask_code(source, literals=False)

    def require(condition, detail):
        if not condition:
            raise ValueError("ICT source partition: " + detail)

    def array(label, type_pattern):
        matches = list(re.finditer(
            r"\bconst\s+" + label + r"\s*:\s*" + type_pattern
            + r"\s*=\s*&\s*\[", code,
        ))
        require(len(matches) == 1, "missing or duplicate " + label)
        start = matches[0].end()
        end = code.find("]", start)
        require(end >= 0 and re.match(r"\s*;", code[end + 1:]),
                "unsupported array shape for " + label)
        return start, end

    def fields(start, end):
        spans = []
        stops = [start + m.start() for m in re.finditer(",", code[start:end])]
        for stop in stops + [end]:
            if stop != end or literals[start:stop].strip():
                spans.append((start, stop))
            start = stop + 1
        return spans

    def literal(span, *, name=False):
        start, end = span
        text = literals[start:end].strip()
        require(not code[start:end].strip(), "nonliteral argument")
        # These are grammar-delimited slots, not a search through source text.
        # The masker has already checked termination and removed all comments.
        raw = re.match(r'r(#*)"', text)
        valid = (text.find('"' + raw[1], raw.end())
                 == len(text) - 1 - len(raw[1])) if raw else bool(
                     re.fullmatch(r'"(?:\\[\s\S]|[^"\\])*"', text))
        require(valid, "expected one string literal")
        if name:
            match = re.fullmatch(r'"([A-Za-z_][A-Za-z_0-9]*)"', text)
            require(match is not None, "expected unescaped identifier name")
            return match[1]
        return text

    def rows(label, *, declarations=False):
        type_pattern = (r"&\s*\[\s*DeclarationInput\s*\]" if declarations
                        else r"&\s*\[\s*\(\s*&str\s*,\s*&str\s*,\s*&str\s*\)\s*\]")
        start, end = array(label, type_pattern)
        kinds = (r"(Proof|Data|Inductive)" if allow_inductives
                 else r"(Proof|Data)")
        pattern = (r"DeclarationInput\s*::\s*" + kinds + r"\s*\("
                   if declarations else r"\(")
        result = []
        while literals[start:end].strip():
            start += len(literals[start:end]) - len(literals[start:end].lstrip())
            match = re.match(pattern, code[start:end])
            require(match is not None, "unsupported row in " + label)
            args_start = start + match.end()
            close = code.find(")", args_start, end)
            require(close >= 0, "unclosed tuple in " + label)
            args = fields(args_start, close)
            kind = match[1] if declarations else None
            if kind == "Inductive":
                require(len(args) == 1, "expected one inductive literal")
                declaration = literal(args[0])
                # The old raw-carrier callers remain parameter/index-free.
                # The admission unit additionally permits named simple-typed
                # parameters and an arrow spine ending in Type. This reads
                # names only; real Rust tests parse/kernel-check declarations.
                ident = r"[A-Za-z_][A-Za-z_0-9]*"
                prefix = r'r(#*)"inductive\s+(' + ident + r')'
                if allow_indexed_inductives:
                    parameter = r"\s+\(" + ident + r"\s*:\s*" + ident + r"\)"
                    index = ident + r"(?:\s+" + ident + r")*\s*->\s*"
                    signature = (r"(?:" + parameter + r")*\s*:\s*(?:"
                                 + index + r")*Type\s*\n\|")
                else:
                    signature = r'\s*:\s*Type(?=\s|")'
                header = re.match(prefix + signature, declaration)
                require(header is not None, "unsupported inductive header")
                name = header[2]
            else:
                require(len(args) == 3, "expected three literal arguments")
                name = literal(args[0], name=True)
                for arg in args[1:]:
                    literal(arg)
            result.append((kind, name) if declarations else name)
            start = close + 1
            start += len(literals[start:end]) - len(literals[start:end].lstrip())
            require(start == end or code[start] == ",",
                    "missing tuple separator")
            if start != end:
                start += 1
        return result

    arrays = {}
    for label in ("PROOF_ROOTS", "DATA_NAMES", "INDUCTIVE_NAMES",
                  "PROP_PROOF_ROOTS", "TYPE_PROOF_ROOTS"):
        start, end = array(label, r"&\s*\[\s*&str\s*\]")
        arrays[label] = [literal(span, name=True) for span in fields(start, end)]
    declarations = rows("DECLARATIONS", declarations=True)
    proofs = [name for kind, name in declarations if kind == "Proof"]
    data = [name for kind, name in declarations if kind == "Data"]
    bad = rows("NEGATIVE_CONTROLS")
    if allow_inductives:
        carriers = [name for kind, name in declarations if kind == "Inductive"]
        require(len(carriers) == len(set(carriers)), "duplicate carrier name")
        require(carriers == arrays["INDUCTIVE_NAMES"], "carrier list mismatch")
        return arrays, proofs, data, bad, carriers
    return arrays, proofs, data, bad


class CrosscheckRunnerTests(unittest.TestCase):
    def test_audited_roots_stay_in_sync(self):
        exporter_dir = REPO / "crates/clean-verify/src/bin/lean_export"
        exporter = (exporter_dir / "audit_roots.rs").read_text()
        groups_match = re.search(
            r"static DEFAULT_ROOTS: \[&\[&str\]; (\d+)\] = \[(.*?)\];",
            exporter, re.DOTALL,
        )
        self.assertIsNotNone(groups_match)
        groups = re.findall(r"&([\w:]+)", groups_match.group(2))
        self.assertEqual(int(groups_match.group(1)), len(groups))
        self.assertEqual(len(groups), len(set(groups)))
        sources = {"": exporter}
        for module in re.findall(r"^mod (\w+);$", exporter, re.MULTILINE):
            sources[f"{module}::"] = (
                exporter_dir / "audit_roots" / f"{module}.rs"
            ).read_text()
        arrays = {}
        for prefix, source in sources.items():
            for name, length, body in re.findall(
                r"static (\w+): \[&str; (\d+)\] = \[(.*?)\n\];",
                source, re.DOTALL,
            ):
                values = re.findall(r'^\s*"([^"]+)"', body, re.MULTILINE)
                self.assertEqual(int(length), len(values), prefix + name)
                self.assertNotIn(prefix + name, arrays)
                arrays[prefix + name] = values
        self.assertEqual(set(groups), set(arrays))
        source_roots = [root for group in groups for root in arrays[group]]
        iterator = re.search(
            r"fn default_roots\(\) -> impl Iterator<Item = &'static str> \{(.*?)\n\}",
            exporter, re.DOTALL,
        )
        self.assertIsNotNone(iterator)
        self.assertEqual(
            re.sub(r"\s+", "", iterator.group(1)),
            "DEFAULT_ROOTS.iter().flat_map(|roots|roots.iter().copied())",
        )
        # The exported, ordered-first and footer-audited roots all come from
        # one selection (`profile.rs`, since 4e90bc81a), and the Full
        # profile's defaults are exactly these audit roots.
        profile = re.sub(r"\s+", "", (exporter_dir / "profile.rs").read_text())
        self.assertEqual(
            profile.count(
                "Self::Full=>super::audit_roots::default_roots().map(str::to_owned).collect(),"
            ),
            1,
        )
        self.assertEqual(profile.count("letdefaults=self.profile.default_roots();"), 1)
        main = re.sub(r"\s+", "", (exporter_dir / "main.rs").read_text())
        self.assertEqual(main.count("default_roots("), 0)
        self.assertEqual(main.count("options.select_roots("), 1)
        self.assertEqual(main.count("letroots=&selection.roots;"), 1)
        self.assertEqual(main.count("letaudit_roots=&selection.audit_roots;"), 1)
        self.assertEqual(
            source_roots,
            [root for root in FLAGSHIPS if not root.startswith("ReplayBridge.")],
        )
        runner = (REPO / "scripts/self_verify_crosscheck.sh").read_text()
        audit_match = re.search(r"FLAGSHIPS=\((.*?)\n\)", runner, re.DOTALL)
        self.assertIsNotNone(audit_match)
        audit_roots = re.findall(
            r'^\s*"CleanVerify\.([^"]+)"', audit_match.group(1), re.MULTILINE
        )
        self.assertEqual(audit_roots, list(FLAGSHIPS))
        self.assertEqual(len(source_roots), len(set(source_roots)))
        self.assertEqual(len(FLAGSHIPS), len(set(FLAGSHIPS)))

    def test_projection_typing_proof_partition_is_mandatory(self):
        directory = REPO / "crates/clean-verify/src/spec/core_spec/projection_typing"
        proofs = []
        nonproofs = []
        for cohort, count in (("domain", 24), ("typing", 8), ("generation", 12),
                              ("instantiation", 13), ("spine", 17)):
            source = (directory / f"{cohort}.rs").read_text()
            arrays = {}
            for label in ("PROOF_ROOTS", "DATA_NAMES", "INDUCTIVE_NAMES"):
                match = re.search(
                    r"const " + label + r":\s*&\[&str\]\s*=\s*&\[(.*?)\];",
                    source, re.DOTALL,
                )
                self.assertIsNotNone(match, (cohort, label))
                arrays[label] = re.findall(r'"([^"]+)"', match.group(1))
            actual = re.findall(r'DeclarationInput::Proof\(\s*"([^"]+)"', source)
            self.assertEqual(actual, arrays["PROOF_ROOTS"], cohort)
            self.assertEqual(len(actual), count, cohort)
            proofs.extend(actual)
            nonproofs.extend(arrays["DATA_NAMES"] + arrays["INDUCTIVE_NAMES"])
        self.assertEqual(len(proofs), 74)
        self.assertEqual(len(set(proofs)), 74)
        self.assertEqual(len(nonproofs), 33)
        start = FLAGSHIPS.index("dp_disjoint")
        self.assertEqual(list(FLAGSHIPS[start:start + 74]), proofs)
        self.assertTrue(set(nonproofs).isdisjoint(FLAGSHIPS))

    def test_constructor_return_coherence_proof_partition_is_mandatory(self):
        directory = (
            REPO / "crates/clean-verify/src/spec/core_spec/constructor_return_coherence"
        )
        proofs = []
        data = []
        negatives = []
        prop_proofs = []
        type_proofs = []
        for cohort, proof_count, data_count, prop_count, type_count, bad_count in (
            ("admission", 12, 5, 11, 1, 3),
            ("prod_admission", 28, 25, 14, 14, 3),
            ("return_spine", 10, 1, 10, 0, 2),
        ):
            source = (directory / f"{cohort}.rs").read_text()
            arrays = {}
            for label in ("PROOF_ROOTS", "DATA_NAMES", "INDUCTIVE_NAMES",
                          "PROP_PROOF_ROOTS", "TYPE_PROOF_ROOTS"):
                matches = re.findall(
                    r"const " + label + r":\s*&\[&str\]\s*=\s*&\[(.*?)\];",
                    source, re.DOTALL,
                )
                self.assertEqual(len(matches), 1, (cohort, label))
                arrays[label] = re.findall(r'"([^"]+)"', matches[0])
            actual_proofs = re.findall(
                r'DeclarationInput::Proof\(\s*"([^"]+)"', source
            )
            actual_data = re.findall(
                r'DeclarationInput::Data\(\s*"([^"]+)"', source
            )
            self.assertEqual(actual_proofs, arrays["PROOF_ROOTS"], cohort)
            self.assertEqual(actual_data, arrays["DATA_NAMES"], cohort)
            self.assertEqual(len(actual_proofs), proof_count, cohort)
            self.assertEqual(len(actual_data), data_count, cohort)
            self.assertEqual(arrays["INDUCTIVE_NAMES"], [], cohort)
            self.assertNotIn("DeclarationInput::Inductive(", source)
            self.assertEqual(len(arrays["PROP_PROOF_ROOTS"]), prop_count, cohort)
            self.assertEqual(len(arrays["TYPE_PROOF_ROOTS"]), type_count, cohort)
            self.assertTrue(set(arrays["PROP_PROOF_ROOTS"]).isdisjoint(
                arrays["TYPE_PROOF_ROOTS"]
            ))
            self.assertEqual(
                set(arrays["PROP_PROOF_ROOTS"] + arrays["TYPE_PROOF_ROOTS"]),
                set(actual_proofs), cohort,
            )
            bad_match = re.search(
                r"const NEGATIVE_CONTROLS:\s*&\[\(&str, &str, &str\)\]"
                r"\s*=\s*&\[(.*?)\];", source, re.DOTALL,
            )
            self.assertIsNotNone(bad_match, cohort)
            bad = re.findall(r'\(\s*"([^"]+)",\s*r"', bad_match.group(1))
            self.assertEqual(len(bad), bad_count, cohort)
            proofs.extend(actual_proofs)
            data.extend(actual_data)
            negatives.extend(bad)
            prop_proofs.extend(arrays["PROP_PROOF_ROOTS"])
            type_proofs.extend(arrays["TYPE_PROOF_ROOTS"])
        self.assertEqual((len(proofs), len(data), len(negatives)), (50, 31, 8))
        self.assertEqual(len(set(proofs + data + negatives)), 89)
        self.assertEqual((len(prop_proofs), len(type_proofs)), (35, 15))
        self.assertIn("arc_admitted_selected_arity", prop_proofs)
        self.assertNotIn("arc_admitted_selected_arity", type_proofs)
        start = FLAGSHIPS.index("cdp_spine_capture_arguments") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + 50]), proofs)
        self.assertTrue(set(data + negatives).isdisjoint(FLAGSHIPS))

    def test_generic_constructor_closing_proof_partition_is_mandatory(self):
        source = (
            REPO / "crates/clean-verify/src/spec/core_spec/constructor_return_coherence"
            / "generic_closing.rs"
        ).read_text()
        arrays = {}
        for label in ("PROOF_ROOTS", "DATA_NAMES", "INDUCTIVE_NAMES",
                      "PROP_PROOF_ROOTS", "TYPE_PROOF_ROOTS"):
            matches = re.findall(
                r"const " + label + r":\s*&\[&str\]\s*=\s*&\[(.*?)\];",
                source, re.DOTALL,
            )
            self.assertEqual(len(matches), 1, label)
            arrays[label] = re.findall(r'"([^"]+)"', matches[0])
        proofs = re.findall(r'DeclarationInput::Proof\(\s*"([^"]+)"', source)
        data = re.findall(r'DeclarationInput::Data\(\s*"([^"]+)"', source)
        self.assertEqual(proofs, arrays["PROOF_ROOTS"])
        self.assertEqual(proofs, arrays["PROP_PROOF_ROOTS"])
        self.assertEqual((len(proofs), len(set(proofs))), (21, 21))
        self.assertEqual(data, ["gcc_named_return_spine"])
        self.assertEqual(data, arrays["DATA_NAMES"])
        self.assertEqual(arrays["TYPE_PROOF_ROOTS"], [])
        self.assertEqual(arrays["INDUCTIVE_NAMES"], [])
        self.assertNotIn("DeclarationInput::Inductive(", source)
        bad_match = re.search(
            r"const NEGATIVE_CONTROLS:\s*&\[\(&str, &str, &str\)\]"
            r"\s*=\s*&\[(.*?)\];", source, re.DOTALL,
        )
        self.assertIsNotNone(bad_match)
        bad = re.findall(r'\(\s*"([^"]+)",\s*r"', bad_match.group(1))
        self.assertEqual(bad, ["gcc_forged_wrong_family", "gcc_forged_wrong_order",
                               "gcc_forged_underflow_endpoint"])
        self.assertEqual(len(set(proofs + data + bad)), 25)
        self.assertIn("gcc_admitted_return_named", proofs)
        self.assertIn("gcc_admitted_closed_arity", proofs)
        start = FLAGSHIPS.index("arc_underflow_arity_refuses") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + 21]), proofs)
        self.assertTrue(set(data + bad).isdisjoint(FLAGSHIPS))

    def test_named_indexed_guard_proof_partition_is_mandatory(self):
        directory = REPO / "crates/clean-verify/src/spec/core_spec/named_indexed_guard"
        proofs, data, carriers, negatives, prop, nonprop = [], [], [], [], [], []
        for cohort, counts in (("guard", (19, 11, 1, 16, 3, 0)),
                               ("evidence", (65, 7, 0, 62, 3, 11))):
            source = (directory / f"{cohort}.rs").read_text()
            arrays = {}
            for label in ("PROOF_ROOTS", "DATA_NAMES", "INDUCTIVE_NAMES",
                          "PROP_PROOF_ROOTS", "TYPE_PROOF_ROOTS"):
                matches = re.findall(
                    r"const " + label + r":\s*&\[&str\]\s*=\s*&\[(.*?)\];",
                    source, re.DOTALL,
                )
                self.assertEqual(len(matches), 1, (cohort, label))
                arrays[label] = re.findall(r'"([^"]+)"', matches[0])
            actual_proofs = re.findall(r'DeclarationInput::Proof\(\s*"([^"]+)"', source)
            actual_data = re.findall(r'DeclarationInput::Data\(\s*"([^"]+)"', source)
            actual_carriers = re.findall(r'DeclarationInput::Inductive\(\s*r"inductive (\w+)', source)
            self.assertEqual(actual_proofs, arrays["PROOF_ROOTS"])
            self.assertEqual(actual_data, arrays["DATA_NAMES"])
            self.assertEqual(actual_carriers, arrays["INDUCTIVE_NAMES"])
            bad_match = re.search(
                r"const NEGATIVE_CONTROLS:\s*&\[\(&str, &str, &str\)\]"
                r"\s*=\s*&\[(.*?)\];", source, re.DOTALL,
            )
            self.assertIsNotNone(bad_match)
            bad = re.findall(r'\(\s*"([^"]+)",\s*r"', bad_match.group(1))
            self.assertEqual((len(actual_proofs), len(actual_data), len(actual_carriers),
                              len(arrays["PROP_PROOF_ROOTS"]), len(arrays["TYPE_PROOF_ROOTS"]), len(bad)), counts)
            kinds = arrays["PROP_PROOF_ROOTS"] + arrays["TYPE_PROOF_ROOTS"]
            self.assertEqual(len(kinds), len(set(kinds)))
            self.assertEqual(set(kinds), set(actual_proofs))
            proofs.extend(actual_proofs)
            data.extend(actual_data)
            carriers.extend(actual_carriers)
            negatives.extend(bad)
            prop.extend(arrays["PROP_PROOF_ROOTS"])
            nonprop.extend(arrays["TYPE_PROOF_ROOTS"])
        self.assertEqual((len(proofs), len(data), len(carriers), len(prop), len(nonprop), len(negatives)), (84, 18, 1, 78, 6, 11))
        self.assertEqual(len(set(proofs + data + carriers + negatives)), 114)
        self.assertEqual(carriers, ["NamedStrictAppFacts"])
        self.assertEqual(nonprop, ["nig_args_sound", "nig_strict_sound", "nig_strict_decompose",
                                  "nig_eq_actual_facts", "nig_eq_actual_decomposition", "nig_eq_connected_stored_context"])
        start = FLAGSHIPS.index("gcc_underflow_captures_parameter") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + 84]), proofs)
        self.assertTrue(set(data + carriers + negatives).isdisjoint(FLAGSHIPS))
        self.assertEqual(proofs[-1], "nig_eq_connected_stored_context")

    def test_named_block_return_proof_partition_is_mandatory(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec/named_block_return"
                  / "records.rs").read_text()
        arrays = {}
        for label in ("PROOF_ROOTS", "DATA_NAMES", "INDUCTIVE_NAMES",
                      "PROP_PROOF_ROOTS", "TYPE_PROOF_ROOTS"):
            matches = re.findall(
                r"const " + label + r":\s*&\[&str\]\s*=\s*&\[(.*?)\];",
                source, re.DOTALL,
            )
            self.assertEqual(len(matches), 1, label)
            arrays[label] = re.findall(r'"([^"]+)"', matches[0])
        proofs = re.findall(r'DeclarationInput::Proof\(\s*"([^"]+)"', source)
        data = re.findall(r'DeclarationInput::Data\(\s*"([^"]+)"', source)
        self.assertEqual(proofs, arrays["PROOF_ROOTS"])
        self.assertEqual(data, arrays["DATA_NAMES"])
        self.assertEqual(arrays["INDUCTIVE_NAMES"], [])
        self.assertNotIn("DeclarationInput::Inductive(", source)
        self.assertEqual((len(proofs), len(data)), (15, 33))
        self.assertEqual((len(arrays["PROP_PROOF_ROOTS"]),
                          len(arrays["TYPE_PROOF_ROOTS"])), (11, 4))
        kinds = arrays["PROP_PROOF_ROOTS"] + arrays["TYPE_PROOF_ROOTS"]
        self.assertEqual(len(kinds), len(set(kinds)))
        self.assertEqual(set(kinds), set(proofs))
        self.assertIn("nrb_nat_some_sound", arrays["PROP_PROOF_ROOTS"])
        self.assertIn("nrb_selected_constructor", arrays["TYPE_PROOF_ROOTS"])
        bad_match = re.search(
            r"const NEGATIVE_CONTROLS:\s*&\[\(&str, &str, &str\)\]"
            r"\s*=\s*&\[(.*?)\];", source, re.DOTALL,
        )
        self.assertIsNotNone(bad_match)
        bad = re.findall(r'\(\s*"([^"]+)",\s*r"', bad_match.group(1))
        self.assertEqual(bad, ["nrb_false_other_parent_accepts",
                              "nrb_false_other_index_accepts",
                              "nrb_false_g_index_count_zero",
                              "nrb_false_selected_family"])
        self.assertEqual(len(set(proofs + data + bad)), 52)
        start = FLAGSHIPS.index("nig_eq_connected_stored_context") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + 15]), proofs)
        self.assertTrue(set(data + bad).isdisjoint(FLAGSHIPS))

    def test_ind_ctor_table_proof_partition_is_mandatory(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec/ind_ctor_table"
                  / "records.rs").read_text()
        arrays, proofs, data, bad = _ict_source_partition(source)
        self.assertEqual(proofs, arrays["PROOF_ROOTS"])
        self.assertEqual(proofs, arrays["PROP_PROOF_ROOTS"])
        self.assertEqual(data, arrays["DATA_NAMES"])
        self.assertEqual(arrays["INDUCTIVE_NAMES"], [])
        self.assertEqual(arrays["TYPE_PROOF_ROOTS"], [])
        self.assertEqual((len(proofs), len(data)), (19, 3))
        self.assertEqual(data, ["ict_append", "ict_has_name_b", "ict_eq_updates"])
        self.assertEqual(bad, ["ict_false_cross_kind_survives",
                              "ict_false_other_without_inequality",
                              "ict_false_append_order",
                              "ict_false_cross_kind_is_fresh"])
        self.assertEqual(len(set(proofs + data + bad)), 26)
        start = FLAGSHIPS.index("nrb_demo_wrong_kind_refuses") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + 19]), proofs)
        self.assertTrue(set(data + bad).isdisjoint(FLAGSHIPS))

    def test_ind_ctor_table_partition_ignores_noncode_mentions(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec/ind_ctor_table"
                  / "records.rs").read_text()
        expected = _ict_source_partition(source)
        fake = ('const PROOF_ROOTS: &[&str] = &["fake"]; '
                'const DECLARATIONS: &[DeclarationInput] = &['
                'DeclarationInput::Proof("fake", r"Nat", r"Nat.zero")]; '
                'DeclarationInput::Inductive("fake")')
        variants = {
            "line comment": "// " + fake + "\n" + source,
            "nested comment": "/* outer /* inner */ " + fake + " */\n" + source,
            "ordinary string": ('const PROSE: &str = ' + json.dumps(fake)
                                + ";\n" + source),
            "raw string": 'const PROSE: &str = r###"' + fake + '"###;\n' + source,
            "proof body": source.replace(
                'r"fun (base updates : IndCtorEnv) =>',
                'r###"' + fake + ' // literal /* text */\n'
                'fun (base updates : IndCtorEnv) =>', 1,
            ).replace(' updates",', ' updates"###,', 1),
            "inter-token comments": source.replace(
                "DeclarationInput::", "DeclarationInput /* a /* b */ c */ ::"
            ).replace("const PROOF_ROOTS", "const /* name */ PROOF_ROOTS"),
        }
        for label, changed in variants.items():
            with self.subTest(label=label):
                self.assertEqual(_ict_source_partition(changed), expected)

    def test_ind_ctor_table_partition_refuses_unsupported_live_shapes(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec/ind_ctor_table"
                  / "records.rs").read_text()
        changes = {
            "duplicate array": source + '\nconst PROOF_ROOTS: &[&str] = &[];',
            "missing array": source.replace("const PROOF_ROOTS", "const UNUSED"),
            "unknown declaration": source.replace("DeclarationInput::Data(",
                                                  "DeclarationInput::Inductive(", 1),
            "nonliteral argument": source.replace('"ict_append",', "SOME_NAME,", 1),
            "missing argument": source.replace('"ict_append",', "", 1),
            "stray leading literal": source.replace(
                "const DECLARATIONS: &[DeclarationInput] = &[",
                'const DECLARATIONS: &[DeclarationInput] = &[r"stray" ', 1),
            "stray trailing literal": source.replace("\n];", '\n r"stray"\n];', 1),
            "stray literal before separator": source.replace(
                "    ),\n", '    ) r"stray",\n', 1),
        }
        for label, changed in changes.items():
            with self.subTest(label=label):
                with self.assertRaises(ValueError):
                    _ict_source_partition(changed)
        # Still see live changes; comments/string protection must not hide them.
        changed = source.replace('"ict_kind_append",', '"ict_renamed",', 1)
        arrays, proofs, _, _ = _ict_source_partition(changed)
        self.assertNotEqual(proofs, arrays["PROOF_ROOTS"])

    def test_ind_ctor_table_partition_rejects_unterminated_noncode(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec/ind_ctor_table"
                  / "records.rs").read_text()
        for tail in ('\n/* outer /* inner */', '\nconst BAD: &str = r###"open'):
            with self.subTest(tail=tail):
                # Existing masker has a dedicated ExtractError, not ValueError.
                with self.assertRaisesRegex(Exception, "unterminated"):
                    _ict_source_partition(source + tail)

    def test_raw_block_return_proof_partition_is_mandatory(self):
        folder = REPO / "crates/clean-verify/src/spec/core_spec/raw_block_return"
        expected = {
            "raw": (37, 0, 23, ["NamedCtorSource", "NamedMemberSource"]),
            "family": (14, 2, 0, []),
            "whole": (20, 3, 11, []),
        }
        proofs, other, all_names = [], [], []
        for cohort, (prop_count, type_count, data_count, carrier_names) in expected.items():
            source = (folder / f"{cohort}.rs").read_text()
            arrays, actual, data, bad, carriers = _ict_source_partition(
                source, allow_inductives=True,
            )
            self.assertEqual(actual, arrays["PROOF_ROOTS"])
            self.assertEqual(data, arrays["DATA_NAMES"])
            self.assertEqual(carriers, carrier_names)
            self.assertEqual(len(arrays["PROP_PROOF_ROOTS"]), prop_count)
            self.assertEqual(len(arrays["TYPE_PROOF_ROOTS"]), type_count)
            kinds = arrays["PROP_PROOF_ROOTS"] + arrays["TYPE_PROOF_ROOTS"]
            self.assertEqual(len(kinds), len(set(kinds)))
            self.assertEqual(set(kinds), set(actual))
            self.assertEqual(len(data), data_count)
            self.assertEqual(len(bad), 4)
            proofs.extend(actual)
            other.extend(data + carriers + bad)
            all_names.extend(actual + data + carriers + bad)
        self.assertEqual((len(proofs), len(other), len(all_names)), (76, 48, 124))
        self.assertEqual(len(set(all_names)), 124)
        start = FLAGSHIPS.index("ict_eq_ind_shadows_ctor") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + 76]), proofs)
        self.assertTrue(set(other).isdisjoint(FLAGSHIPS))

    def test_stored_family_admission_proof_partition_is_mandatory(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec"
                  / "stored_family_admission.rs").read_text()
        arrays, proofs, data, bad = _ict_source_partition(source)
        self.assertEqual(proofs, arrays["PROOF_ROOTS"])
        self.assertEqual(proofs, arrays["TYPE_PROOF_ROOTS"])
        self.assertEqual(arrays["PROP_PROOF_ROOTS"], [])
        self.assertEqual(arrays["INDUCTIVE_NAMES"], [])
        self.assertEqual(data, arrays["DATA_NAMES"])
        self.assertEqual(data, ["sfa_entry_at", "sfa_entries"])
        self.assertEqual(bad, [
            "sfa_false_changed_former", "sfa_false_changed_parameters",
            "sfa_false_shortened_constructors", "sfa_false_wrong_position",
        ])
        self.assertEqual((len(proofs), len(data), len(bad)), (8, 2, 4))
        self.assertEqual(len(set(proofs + data + bad)), 14)
        start = FLAGSHIPS.index("nwr_wrong_level_refuses") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + 8]), proofs)
        self.assertTrue(set(data + bad).isdisjoint(FLAGSHIPS))

    def test_declaration_input_admission_proof_partition_is_mandatory(self):
        folder = REPO / "crates/clean-verify/src/spec/core_spec"
        source = ((folder / "declaration_input_admission.rs").read_text()
                  + "\n" + (folder / "declaration_input_admission/controls.rs").read_text())
        arrays, proofs, data, bad, carriers = _ict_source_partition(
            source, allow_inductives=True, allow_indexed_inductives=True,
        )
        self.assertEqual(proofs, arrays["PROOF_ROOTS"])
        self.assertEqual(proofs, arrays["TYPE_PROOF_ROOTS"])
        self.assertEqual(arrays["PROP_PROOF_ROOTS"], [])
        self.assertEqual(carriers, arrays["INDUCTIVE_NAMES"])
        self.assertEqual(carriers, [
            "KernelDeclInput", "KernelDeclInputAdmission",
            "KernelDeclInputAccepts", "KernelDeclInputChain",
        ])
        self.assertEqual(data, arrays["DATA_NAMES"])
        self.assertEqual((len(proofs), len(data), len(carriers)), (20, 5, 4))
        self.assertEqual(bad, [
            "dia_false_constant_kind", "dia_false_constant_type",
            "dia_false_constant_value", "dia_false_family_type",
            "dia_false_family_parameters", "dia_false_family_constructors",
            "dia_false_reuse_position", "dia_false_nonempty_nil",
            "dia_false_admission_body",
        ])
        all_names = proofs + data + carriers + bad
        self.assertEqual(len(set(all_names)), len(all_names))
        start = FLAGSHIPS.index("sfa_constant_tail_caller") + 1
        self.assertEqual(list(FLAGSHIPS[start:start + len(proofs)]), proofs)
        self.assertTrue(set(data + carriers + bad).isdisjoint(FLAGSHIPS))

    def test_declaration_input_partition_refuses_malformed_indexed_headers(self):
        folder = REPO / "crates/clean-verify/src/spec/core_spec"
        source = ((folder / "declaration_input_admission.rs").read_text()
                  + "\n" + (folder / "declaration_input_admission/controls.rs").read_text())
        header = "KernelDeclInputAccepts (env : KEnv) : KernelDeclInput -> KEnv -> Type"
        self.assertIn(header, source)
        for replacement in (
            "KernelDeclInputAccepts (env KEnv) : KernelDeclInput -> KEnv -> Type",
            "KernelDeclInputAccepts (env : KEnv : KernelDeclInput -> KEnv -> Type",
            "KernelDeclInputAccepts (env : KEnv) : KernelDeclInput -> KEnv -> Prop",
            "KernelDeclInputAccepts (env : KEnv) : KernelDeclInput -> KEnv -> Type garbage",
        ):
            with self.subTest(header=replacement):
                with self.assertRaises(ValueError):
                    _ict_source_partition(
                        source.replace(header, replacement, 1),
                        allow_inductives=True, allow_indexed_inductives=True,
                    )
        with self.assertRaises(ValueError):
            _ict_source_partition(source, allow_inductives=True)

    def test_raw_block_return_inductive_partition_ignores_noncode(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec/raw_block_return"
                  / "raw.rs").read_text()
        expected = _ict_source_partition(source, allow_inductives=True)
        fake = ('DeclarationInput::Inductive(r"inductive Counterfeit : Type '
                '| mk : Counterfeit"), const INDUCTIVE_NAMES: &[&str] = &["Counterfeit"];')
        variants = {
            "line comment": "// " + fake + "\n" + source,
            "nested comment": "/* outer /* inner */ " + fake + " */\n" + source,
            "ordinary literal": "const TEXT: &str = " + json.dumps(fake) + ";\n" + source,
            "raw literal": 'const TEXT: &str = r###"' + fake + '"###;\n' + source,
            "inter-token comments": source.replace(
                "DeclarationInput::Inductive", "DeclarationInput /* nested /* x */ */ :: Inductive"
            ),
        }
        for label, changed in variants.items():
            with self.subTest(label=label):
                self.assertEqual(
                    _ict_source_partition(changed, allow_inductives=True), expected,
                )
        # The old default still refuses this newly opted-in carrier grammar.
        with self.assertRaises(ValueError):
            _ict_source_partition(source)

    def test_raw_block_return_inductive_partition_refuses_malformed_carriers(self):
        source = (REPO / "crates/clean-verify/src/spec/core_spec/raw_block_return"
                  / "raw.rs").read_text()
        code = _ict_rust_masker()(source)
        name_arrays = list(re.finditer(
            r"\bconst\s+INDUCTIVE_NAMES\s*:\s*&\s*\[\s*&str\s*\]"
            r"\s*=\s*&\[", code,
        ))
        self.assertEqual(len(name_arrays), 1, "one actual carrier-name array")
        start = name_arrays[0].end()
        end = code.find("]", start)
        self.assertGreaterEqual(end, start, "closed carrier-name array")

        def changed_names(values):
            # Both compact and rustfmt-expanded arrays name these live tokens.
            # Do not depend on indentation or a trailing comma to mutate them.
            body = ", ".join(json.dumps(name) for name in values)
            return source[:start] + body + source[end:]

        changes = {
            "wrong declaration header": source.replace(
                'r"inductive NamedCtorSource', 'r"def NamedCtorSource', 1),
            "unsupported indexed header": source.replace(
                'inductive NamedCtorSource : Type',
                'inductive NamedCtorSource (n : Nat) : Type', 1),
            "missing carrier identifier": source.replace(
                'inductive NamedCtorSource : Type', 'inductive : Type', 1),
            "duplicate carrier identifier": source.replace(
                'inductive NamedMemberSource : Type',
                'inductive NamedCtorSource : Type', 1),
            "missing carrier name entry": changed_names(["NamedMemberSource"]),
            "duplicate carrier name entry": changed_names(
                ["NamedCtorSource", "NamedCtorSource"]),
            "wrong literal arity": source.replace(
                'DeclarationInput::Inductive(', 'DeclarationInput::Inductive("extra", ', 1),
        }
        for label, changed in changes.items():
            with self.subTest(label=label):
                self.assertTrue(changed != source, "control must mutate real source")
                with self.assertRaises(ValueError):
                    _ict_source_partition(changed, allow_inductives=True)

    def test_root_chunks_are_explicit_replay_cache_inputs(self):
        # Inspect the real row without importing the runner or touching its
        # persistent state. Its existing digest includes git-visible files in
        # workspace crates as well as every declared extra file path.
        tree = ast.parse((REPO / "scripts/verify_runner.py").read_text())
        rows = next(
            node.value.elts for node in tree.body
            if isinstance(node, ast.Assign)
            and any(isinstance(target, ast.Name) and target.id == "WORKSPACE_GATES"
                    for target in node.targets)
        )
        entry = next(
            {ast.literal_eval(key): value for key, value in zip(row.keys, row.values)}
            for row in rows
            if isinstance(row, ast.Dict)
            and any(isinstance(key, ast.Constant) and key.value == "id"
                    and isinstance(value, ast.Constant) and value.value == "gate::leancross"
                    for key, value in zip(row.keys, row.values))
        )
        extra = ast.literal_eval(entry["_extra_paths"])
        self.assertEqual(len(extra), len(set(extra)))
        exporter_dir = REPO / "crates/clean-verify/src/bin/lean_export"
        inputs = [exporter_dir / "audit_roots.rs"]
        inputs.extend((exporter_dir / "audit_roots").rglob("*.rs"))
        self.assertGreater(len(inputs), 1)
        for path in inputs:
            self.assertIn(path.relative_to(REPO).as_posix(), extra)

    def test_merged_gate_manifest_keeps_unique_keys_and_four_real_controls(self):
        def unique_object(pairs):
            result = {}
            for key, value in pairs:
                self.assertNotIn(key, result, f"duplicate JSON key: {key}")
                result[key] = value
            return result

        demos = json.loads(
            (REPO / "data/gate_demonstrations.json").read_text(),
            object_pairs_hook=unique_object,
        )
        json.loads(
            (REPO / "data/gate_registry.json").read_text(),
            object_pairs_hook=unique_object,
        )
        arms = demos["arms"]["gate::leancross"]
        self.assertEqual(len(arms), 4)
        self.assertEqual(len({arm["arm"] for arm in arms}), 4)
        self.assertEqual(
            {arm["mutate"]["file"] for arm in arms},
            {
                "crates/clean-verify/src/spec/core_spec/eval_ir_state.rs",
                "crates/clean-verify/src/bin/lean_export/printer.rs",
                "crates/clean-verify/src/bin/lean_export/emit.rs",
                "crates/clean-verify/src/bin/lean_export/main.rs",
            },
        )
        for arm in arms:
            self.assertEqual(arm["sandbox"], "build")
            self.assertEqual(
                arm["command"],
                "scripts/heavy_gate.sh run 24 leancross-demo -- scripts/self_verify_crosscheck.sh",
            )
            mutation = arm["mutate"]
            source = (REPO / mutation["file"]).read_text()
            self.assertRegex(source, mutation["pattern"])
            self.assertNotEqual(
                re.sub(mutation["pattern"], mutation["replacement"], source, count=1),
                source,
            )
        proof_arm = next(arm for arm in arms if arm["mutate"]["file"].endswith("/emit.rs"))
        self.assertIn(
            'lean_name == "ReplayBridge.ir_nat_ltb_walk_eqOriginal"',
            proof_arm["mutate"]["replacement"],
        )
        self.assertEqual(proof_arm["expect_contains"], "lean reported")
        self.assertNotIn("gate::leancross", demos["arm_coverage_debt"]["rows"])

    def run_case(self, mode):
        with tempfile.TemporaryDirectory(prefix="replay-runner-test-") as td:
            root = Path(td)
            (root / "repo/scripts").mkdir(parents=True)
            (root / "sysroot/bin").mkdir(parents=True)
            (root / "path").mkdir()
            (root / "artifacts").mkdir()
            (root / "custom-target/release").mkdir(parents=True)
            runner = root / "repo/scripts/self_verify_crosscheck.sh"
            shutil.copyfile(REPO / "scripts/self_verify_crosscheck.sh", runner)

            def program(path, body):
                # A `#!{sys.executable}` line breaks when the interpreter's
                # path holds a space (aterm's is under "Application Support"):
                # the kernel execs the text before the space. A shell wrapper
                # execs the quoted interpreter on the body instead.
                script = path.with_name(path.name + ".fixture.py")
                script.write_text(body)
                path.write_text(
                    "#!/bin/sh\n"
                    f'exec {shlex.quote(sys.executable)} {shlex.quote(str(script))} "$@"\n'
                )
                path.chmod(0o755)

            program(root / "path/trustc", """
import os, sys
assert sys.argv[1:] == ['--print', 'sysroot']
print(os.environ['FAKE_ROOT'] + '/sysroot')
""")
            program(root / "sysroot/bin/targo", """
import os, sys
assert sys.argv[1:] == ['--unverified', 'build', '--locked', '--release', '-p', 'clean-verify', '--bin', 'lean_export']
if os.environ['FAKE_MODE'] == 'build-failed':
    print('compiler diagnostic must survive', file=sys.stderr)
    sys.exit(7)
""")
            program(root / "custom-target/release/lean_export", r"""
import os, sys
from pathlib import Path
assert sys.argv[1:3] == ['--all-spec', '--out']
mode = os.environ['FAKE_MODE']
if mode == 'export-failed':
    print('spec construction diagnostic must survive', file=sys.stderr)
    sys.exit(9)
Path(sys.argv[3]).write_text('-- synthetic harness fixture, not proof evidence\n')
lines = [
    '[lean_export] emitted 9 Lean declarations (9 closure items)',
    '[lean_export] spec-definition coverage: 7 directly + 2 via inductive blocks, of 9 total spec definitions',
    '[lean_export] explicit axioms in export (3):',
    '[lean_export]   axiom propext',
    '[lean_export]   axiom Quot.sound',
    '[lean_export]   axiom Classical.choice',
    '[lean_export] skipped: none',
]
if mode == 'coverage-gap':
    lines[1] = lines[1].replace('of 9 total', 'of 10 total')
if mode == 'domain-axiom':
    lines[5] = '[lean_export]   axiom arbitrary_truth'
if mode == 'skipped':
    lines[-1] = '[lean_export] SKIPPED (1): unexpected_case'
print('\n'.join(lines), file=sys.stderr)
""")
            program(root / "path/lean", f"""
import os, sys
assert sys.argv[1] == '+leanprover/lean4:v4.30.0-rc2'
mode = os.environ['FAKE_MODE']
if mode == 'lean-abort':
    print('Stack overflow detected')
    sys.exit(134)
if mode == 'diagnostic-zero-exit':
    print('fixture.lean:1:1: error(lean.unknownIdentifier): unknown constant')
if mode == 'diagnostic-nonzero-exit':
    print('fixture.lean:1:1: error(lean.unknownIdentifier): unknown constant')
    sys.exit(1)
if mode == 'legacy-diagnostic':
    print('fixture.lean:1:1: error: invalid proof')
    sys.exit(1)
if mode == 'admitted-proof':
    print("fixture.lean:1:1: warning: declaration uses 'sorry'")
if mode == 'sorry-axiom':
    print("'CleanVerify.nonFlagship' depends on axioms: [sorryAx]")
for name in {FLAGSHIPS!r}:
    if mode == 'missing-shared-driver-agreement-closure' and name == 'ir_steps_shared_driver_agreement':
        continue
    if mode == 'nonempty-shared-driver-agreement-closure' and name == 'ir_steps_shared_driver_agreement':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-closure' and name == 'bootstrap_infer_sound':
        continue
    if mode == 'missing-typing-closure' and name == 'dp_field1_connected':
        continue
    if mode == 'nonempty-typing-closure' and name == 'typingcdpctxconv_in_const_spine_gen':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-constructor-return-closure' and name == 'arc_prod_source_return':
        continue
    if mode == 'nonempty-constructor-arity-closure' and name == 'arc_admitted_selected_arity':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-generic-constructor-return-closure' and name == 'gcc_admitted_return_named':
        continue
    if mode == 'nonempty-generic-constructor-closure' and name == 'gcc_admitted_closed_arity':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-named-indexed-closure' and name == 'nig_eq_connected_stored_context':
        continue
    if mode == 'nonempty-named-indexed-closure' and name == 'nig_eq_extracted_domain_count':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-named-block-return-closure' and name == 'nrb_selected_constructor':
        continue
    if mode == 'nonempty-named-block-return-closure' and name == 'nrb_nat_some_sound':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-ind-ctor-table-closure' and name == 'ict_kind_append':
        continue
    if mode == 'nonempty-ind-ctor-table-closure' and name == 'ict_eq_ind_shadows_ctor':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-raw-block-return-closure' and name == 'nwr_installed_return_of_raw':
        continue
    if mode == 'nonempty-raw-block-return-closure' and name == 'nwr_selected_constructor_from_raw':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'missing-stored-family-admission-closure' and name == 'sfa_stored_family_admission':
        continue
    if mode == 'missing-declaration-input-closure' and name == 'dia_input_admitted':
        continue
    if mode == 'nonempty-declaration-input-closure' and name == 'dia_chain_sound':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    if mode == 'nonempty-stored-family-admission-closure' and name == 'sfa_constant_tail_caller':
        print("'CleanVerify." + name + "' depends on axioms: [arbitrary_truth]")
        continue
    print("'CleanVerify." + name + "' does not depend on any axioms")
""")
            env = dict(
                os.environ,
                PATH=f"{root / 'path'}:{os.environ['PATH']}",
                FAKE_ROOT=str(root),
                FAKE_MODE=mode,
                CARGO_TARGET_DIR=str(root / "custom-target"),
                CLEAN_REPLAY_ARTIFACT_ROOT=str(root / "artifacts"),
            )
            result = subprocess.run(
                ["bash", str(runner)], env=env, capture_output=True, text=True
            )
            evidence = list((root / "artifacts").iterdir())
            self.assertEqual(len(evidence), 1)
            self.assertIn(str(evidence[0]), result.stdout + result.stderr)
            if mode == "green":
                self.assertTrue((evidence[0] / "lean_check.txt").exists())
                self.assertTrue((evidence[0] / "CleanVerifyExportAll.lean").exists())
            return result

    def test_custom_target_and_evidence_survive_success(self):
        result = self.run_case("green")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("foreign-kernel cross-check green", result.stdout)
        self.assertIn(f"flagship closures  : {len(FLAGSHIPS)} × zero-axiom", result.stdout)

    def test_constructor_return_missing_closure_is_refused(self):
        result = self.run_case("missing-constructor-return-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.arc_prod_source_return' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_constructor_return_nonempty_prop_closure_is_refused(self):
        result = self.run_case("nonempty-constructor-arity-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.arc_admitted_selected_arity' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_generic_constructor_return_missing_closure_is_refused(self):
        result = self.run_case("missing-generic-constructor-return-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.gcc_admitted_return_named' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_generic_constructor_nonempty_prop_closure_is_refused(self):
        result = self.run_case("nonempty-generic-constructor-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.gcc_admitted_closed_arity' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_named_indexed_missing_connected_closure_is_refused(self):
        result = self.run_case("missing-named-indexed-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.nig_eq_connected_stored_context' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_named_indexed_nonempty_prop_closure_is_refused(self):
        result = self.run_case("nonempty-named-indexed-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.nig_eq_extracted_domain_count' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_named_block_return_missing_selected_closure_is_refused(self):
        result = self.run_case("missing-named-block-return-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.nrb_selected_constructor' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_named_block_return_nonempty_prop_closure_is_refused(self):
        result = self.run_case("nonempty-named-block-return-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.nrb_nat_some_sound' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_ind_ctor_table_missing_lookup_closure_is_refused(self):
        result = self.run_case("missing-ind-ctor-table-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.ict_kind_append' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_ind_ctor_table_nonempty_shadow_closure_is_refused(self):
        result = self.run_case("nonempty-ind-ctor-table-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.ict_eq_ind_shadows_ctor' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_raw_block_return_missing_whole_closure_is_refused(self):
        result = self.run_case("missing-raw-block-return-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.nwr_installed_return_of_raw' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_raw_block_return_nonempty_selected_type_closure_is_refused(self):
        result = self.run_case("nonempty-raw-block-return-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.nwr_selected_constructor_from_raw' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_stored_family_admission_missing_recovery_closure_is_refused(self):
        result = self.run_case("missing-stored-family-admission-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.sfa_stored_family_admission' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_declaration_input_missing_admission_closure_is_refused(self):
        result = self.run_case("missing-declaration-input-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.dia_input_admitted' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_shared_driver_missing_agreement_closure_is_refused(self):
        result = self.run_case("missing-shared-driver-agreement-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.ir_steps_shared_driver_agreement' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_shared_driver_nonempty_agreement_closure_is_refused(self):
        result = self.run_case("nonempty-shared-driver-agreement-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.ir_steps_shared_driver_agreement' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_declaration_input_nonempty_chain_closure_is_refused(self):
        result = self.run_case("nonempty-declaration-input-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.dia_chain_sound' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_stored_family_admission_nonempty_caller_closure_is_refused(self):
        result = self.run_case("nonempty-stored-family-admission-closure")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(
            "flagship 'CleanVerify.sfa_constant_tail_caller' did NOT report a zero-axiom closure",
            result.stderr,
        )

    def test_failure_arms_remain_red_and_inspectable(self):
        cases = {
            "build-failed": "compiler diagnostic must survive",
            "export-failed": "spec construction diagnostic must survive",
            "coverage-gap": "coverage not 100%",
            "domain-axiom": "missing foundational axiom",
            "skipped": "export has skips",
            "lean-abort": "lean exited 134",
            "diagnostic-zero-exit": "reported 1 error diagnostic",
            "diagnostic-nonzero-exit": "lean reported 1 error diagnostic",
            "legacy-diagnostic": "lean reported 1 error diagnostic",
            "admitted-proof": "reported an admitted proof",
            "sorry-axiom": "reported an admitted proof",
            "missing-closure": "did NOT report a zero-axiom closure",
            "missing-typing-closure": "flagship 'CleanVerify.dp_field1_connected' did NOT report a zero-axiom closure",
            "nonempty-typing-closure": "flagship 'CleanVerify.typingcdpctxconv_in_const_spine_gen' did NOT report a zero-axiom closure",
        }
        for mode, needle in cases.items():
            with self.subTest(mode=mode):
                result = self.run_case(mode)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn(needle, result.stderr)


if __name__ == "__main__":
    unittest.main()
