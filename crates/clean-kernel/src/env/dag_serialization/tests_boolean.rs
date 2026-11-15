// Copyright 2026 Andrew Yates | Apache-2.0
//! Named one-hot field controls against the independent fixed-format vector.
use super::*;

struct BooleanCase {
    name: &'static str,
    offset: usize,
    set: fn(&mut Environment),
    get: fn(&Environment) -> bool,
}

// Share one bounded case frame rather than expanding 491 independent sets of
// large Environment/WireEnvironment locals in a single debug test function.
#[inline(never)]
fn check_boolean_slot(empty: &[u8], case: &BooleanCase) {
    let mut source = Environment::default();
    (case.set)(&mut source);
    let mut expected = empty.to_vec();
    expected[24 + case.offset] = 1;
    assert_eq!(source.to_dag_bincode().unwrap(), expected, "{}", case.name);
    let restored = Environment::from_dag_bincode(&expected).unwrap();
    assert!((case.get)(&restored), "{}", case.name);
    let mut p = Projection::default();
    let before = source.to_wire(&mut p).unwrap();
    let mut p = Projection::default();
    let after = restored.to_wire(&mut p).unwrap();
    assert_eq!(before, after, "{}", case.name);
}

macro_rules! boolean_slots {
    ($($field:ident => $offset:literal,)*) => {
        #[test]
        fn every_persisted_boolean_has_its_exact_distinct_wire_slot() {
            let empty=include_bytes!("../../../tests/fixtures/environment_dag_wire/empty-v2.dag");
            assert_eq!(Environment::default().to_dag_bincode().unwrap(),empty);
            let cases: &[BooleanCase] = &[$(BooleanCase {
                name: stringify!($field),
                offset: $offset,
                set: |source| source.$field = true,
                get: |source| source.$field,
            },)*];
            assert_eq!(cases.len(),491);
            for case in cases {
                check_boolean_slot(empty, case);
            }
        }
    };
}
boolean_slots! {
    quot_init => 60, eq_init => 61, heq_init => 62,
    propext_init => 63, funext_init => 64, quot_sound_init => 65,
    iff_init => 66, prop_eq_lemmas_init => 67, bool_simp_lemmas_init => 68,
    nat_sub_simp_lemmas_init => 69, decidable_init => 70, ite_init => 71,
    decidable_true_false_inst_init => 72, classical_init => 73, and_init => 74,
    or_init => 75, exists_init => 76, true_false_init => 77,
    prod_init => 78, pprod_init => 79, sigma_init => 80,
    subtype_init => 81, option_init => 82, sum_init => 83,
    psum_init => 84, psigma_init => 85, empty_init => 86,
    pempty_init => 87, bool_init => 88, nat_init => 89,
    ulift_init => 90, char_init => 91, string_init => 92,
    string_append_init => 93, list_init => 94, list_mem_init => 95,
    list_perm_init => 96, multiset_init => 97, finset_init => 98,
    int_init => 99, uint8_init => 100, uint16_init => 101,
    uint32_init => 102, uint64_init => 103, float_init => 104,
    unit_init => 105, punit_init => 106, plift_init => 107,
    fin_init => 108, array_init => 109, io_init => 110,
    io_ops_init => 111, state_t_init => 112, state_m_init => 113,
    id_init => 114, monad_classes_init => 115, fun_id_init => 116,
    fun_comp_init => 117, fun_flip_init => 118, fun_const_init => 119,
    functor_class_init => 120, functor_instances_init => 121, seq_classes_init => 122,
    seq_option_insts_init => 123, pure_bind_classes_init => 124, monad_option_insts_init => 125,
    monad_id_insts_init => 126, monad_list_insts_init => 127, core_monad_instances_init => 128,
    lean_init_modeled => 129, lean4_core_strict_monads => 130, handthen_horelse_init => 131,
    handthen_horelse_option_insts_init => 132, bind_combinators_init => 133, dvd_init => 134,
    nat_dvd_inst_init => 135, getelem_classes_init => 136, getelem_list_instances_init => 137,
    insert_singleton_init => 138, list_insert_singleton_inst_init => 139, except_t_init => 140,
    option_t_init => 141, ordering_init => 142, option_ops_init => 143,
    bool_ops_init => 144, list_ops_init => 145, list_mapm_init => 146,
    for_in_step_init => 147, for_in_init => 148, list_for_in_inst_init => 149,
    nat_cmp_init => 150, inhabited_init => 151, beq_init => 152,
    nat_minmax_init => 153, minmax_class_init => 154, nat_minmax_inst_init => 155,
    ord_init => 156, decidable_eq_init => 157, hashable_init => 158,
    repr_init => 159, to_string_init => 160, le_init => 161,
    lt_init => 162, ge_init => 163, gt_init => 164,
    trans_init => 165, suppress_lossy_structure_stubs => 166, cumulative => 167,
    preorder_init => 168, partial_order_init => 169, linear_order_init => 170,
    reflexive_init => 171, antisymm_init => 172, irrefl_init => 173,
    asymm_init => 174, nat_preorder_init => 175, nat_partial_order_init => 176,
    nat_linear_order_init => 177, nat_le_reflexive_init => 178, nat_lt_irrefl_init => 179,
    nat_lt_asymm_init => 180, nat_lt_trans_init => 181, nat_le_antisymm_init => 182,
    nat_le_trans_init => 183, strict_order_init => 184, nat_lt_strict_order_init => 185,
    nat_trans_lt_le_lt_init => 186, nat_trans_le_lt_lt_init => 187, nat_trans_lt_lt_le_init => 188,
    nat_lt_or_eq_of_le_init => 189, nat_lt_of_le_of_ne_init => 190, nat_not_lt_le_init => 191,
    nat_succ_base_init => 192, nat_succ_lt_init => 193, nat_lt_trichotomy_init => 194,
    nat_decidable_ord_init => 195, uint_decidable_ord_init => 196, nat_minmax_lemmas_init => 197,
    nat_add_ord_init => 198, nat_mul_ord_init => 199, nat_sub_ord_init => 200,
    nat_pow_ord_init => 201, int_arith_init => 202, int_ord_init => 203,
    int_decidable_ord_init => 204, int_ord_lemmas_init => 205, int_linear_order_init => 206,
    int_sign_abs_init => 207, int_arith_lemmas_init => 208, nat_arith_lemmas_init => 209,
    int_nat_conv_lemmas_init => 210, cast_simp_lemmas_init => 211, zero_init => 212,
    one_init => 213, add_init => 214, mul_init => 215,
    neg_init => 216, sub_init => 217, nat_zero_inst_init => 218,
    nat_one_inst_init => 219, nat_add_inst_init => 220, nat_mul_inst_init => 221,
    nat_sub_inst_init => 222, int_zero_inst_init => 223, int_one_inst_init => 224,
    int_add_inst_init => 225, int_mul_inst_init => 226, int_neg_inst_init => 227,
    int_sub_inst_init => 228, hadd_init => 229, hsub_init => 230,
    hmul_init => 231, hdiv_init => 232, div_init => 233,
    hmod_init => 234, mod_init => 235, hpow_init => 236,
    pow_init => 237, nat_hadd_inst_init => 238, int_hadd_inst_init => 239,
    nat_hsub_inst_init => 240, int_hsub_inst_init => 241, nat_hmul_inst_init => 242,
    int_hmul_inst_init => 243, float_arith_ops_init => 244, float_hadd_inst_init => 245,
    float_hsub_inst_init => 246, float_hmul_inst_init => 247, float_hdiv_inst_init => 248,
    float_neg_inst_init => 249, hand_init => 250, hor_init => 251,
    hxor_init => 252, hshiftleft_init => 253, hshiftright_init => 254,
    happend_init => 255, string_happend_inst_init => 256, list_happend_inst_init => 257,
    nat_hand_inst_init => 258, nat_hor_inst_init => 259, nat_hxor_inst_init => 260,
    nat_hshiftleft_inst_init => 261, nat_hshiftright_inst_init => 262, semigroup_init => 263,
    add_semigroup_init => 264, monoid_init => 265, add_monoid_init => 266,
    nat_add_semigroup_inst_init => 267, int_add_semigroup_inst_init => 268, nat_add_monoid_inst_init => 269,
    int_add_monoid_inst_init => 270, group_init => 271, add_group_init => 272,
    int_add_group_inst_init => 273, comm_semigroup_init => 274, add_comm_semigroup_init => 275,
    comm_monoid_init => 276, add_comm_monoid_init => 277, comm_group_init => 278,
    add_comm_group_init => 279, nat_add_comm_semigroup_inst_init => 280, int_add_comm_semigroup_inst_init => 281,
    nat_add_comm_monoid_inst_init => 282, int_add_comm_monoid_inst_init => 283, int_add_comm_group_inst_init => 284,
    semiring_init => 285, ring_init => 286, comm_semiring_init => 287,
    comm_ring_init => 288, nat_semiring_inst_init => 289, int_semiring_inst_init => 290,
    int_ring_inst_init => 291, nat_comm_semiring_inst_init => 292, int_comm_semiring_inst_init => 293,
    int_comm_ring_inst_init => 294, division_ring_init => 295, field_init => 296,
    integral_domain_init => 297, int_integral_domain_inst_init => 298, nat_integral_domain_inst_init => 299,
    nontrivial_init => 300, int_nontrivial_inst_init => 301, well_founded_init => 302,
    wf_recursion_support_init => 303, euclidean_domain_init => 304, int_euclidean_domain_inst_init => 305,
    int_gcd_init => 306, nat_gcd_init => 307, gcd_monoid_init => 308,
    nat_gcd_monoid_inst_init => 309, nat_prime_init => 310, irreducible_init => 311,
    associated_init => 312, ufm_init => 313, nat_ufm_inst_init => 314,
    prime_init => 315, is_principal_ideal_ring_init => 316, polynomial_init => 317,
    rat_init => 318, rat_arith_init => 319, rat_field_inst_init => 320,
    rat_normalize_init => 321, rat_ord_init => 322, rat_linear_order_init => 323,
    linear_ordered_field_init => 324, rat_ordered_field_axioms_init => 325, rat_linear_ordered_field_inst_init => 326,
    rat_decidable_ord_init => 327, rat_minmax_init => 328, rat_abs_init => 329,
    int_minmax_init => 330, int_abs_props_init => 331, nat_abs_diff_init => 332,
    rat_dist_init => 333, int_dist_init => 334, nat_dist_init => 335,
    metric_space_init => 336, nat_metric_space_init => 337, int_metric_space_init => 338,
    rat_metric_space_init => 339, metric_ball_init => 340, metric_continuous_init => 341,
    metric_lipschitz_init => 342, metric_uniform_continuous_init => 343, metric_cauchy_seq_init => 344,
    metric_complete_init => 345, metric_bounded_init => 346, metric_compact_init => 347,
    metric_totally_bounded_init => 348, metric_separable_init => 349, topological_space_init => 350,
    topology_continuous_init => 351, topology_connected_init => 352, topology_compact_init => 353,
    topology_hausdorff_init => 354, topology_homeomorphism_init => 355, topology_locally_compact_init => 356,
    topology_path_connected_init => 357, topology_simply_connected_init => 358, topology_contractible_init => 359,
    topology_covering_space_init => 360, topology_fundamental_group_init => 361, topology_homotopy_equivalence_init => 362,
    topology_retract_init => 363, topology_fiber_bundle_init => 364, topology_quotient_init => 365,
    topology_subspace_init => 366, topology_product_init => 367, topology_higher_homotopy_init => 368,
    topology_suspension_init => 369, topology_vector_bundle_init => 370, topology_coproduct_init => 371,
    topology_cw_init => 372, topology_simplicial_complex_init => 373, topology_homology_init => 374,
    topology_derham_init => 375, topology_morse_init => 376, topology_ktheory_init => 377,
    topology_filtration_init => 378, topology_spectral_init => 379, topology_sheaf_init => 380,
    topology_scheme_init => 381, topology_cobordism_init => 382, topology_characteristic_init => 383,
    topology_manifold_init => 384, topology_lie_group_init => 385, topology_principal_bundle_init => 386,
    topology_connection_init => 387, topology_symplectic_init => 388, topology_kahler_init => 389,
    topology_spin_init => 390, algebra_linear_init => 391, nn_verification_init => 392,
    module_init => 393, algebra_init => 394, submodule_init => 395,
    ideal_init => 396, domain_types_init => 397, fate_x_order_stubs_init => 398,
    category_theory_init => 399, homological_algebra_init => 400, number_theory_init => 401,
    algebraic_geometry_init => 402, representation_theory_init => 403, measure_theory_init => 404,
    functional_analysis_init => 405, information_theory_init => 406, differential_equations_init => 407,
    combinatorics_init => 408, optimization_init => 409, computability_init => 410,
    set_theory_init => 411, set_init => 412, fixed_point_init => 413,
    stochastic_processes_init => 414, formal_logic_init => 415, cryptography_init => 416,
    real_complex_analysis_init => 417, real_ord_init => 418, real_linear_order_init => 419,
    real_hadd_inst_init => 420, real_hmul_inst_init => 421, real_neg_inst_init => 422,
    real_hpow_nat_inst_init => 423, ofnat_init => 424, ofnat_nat_inst_init => 425,
    ofnat_real_inst_init => 426, ofnat_uint8_inst_init => 427, ofnat_uint16_inst_init => 428,
    ofnat_uint32_inst_init => 429, ofnat_uint64_inst_init => 430, usize_init => 431,
    ofnat_usize_inst_init => 432, causal_inference_init => 433, differential_privacy_init => 434,
    graph_theory_init => 435, computational_geometry_init => 436, euclidean_geometry_init => 437,
    euclidean_angle_init => 438, concurrency_theory_init => 439, type_theory_init => 440,
    subgroup_init => 441, subring_init => 442, subfield_init => 443,
    submonoid_init => 444, fact_init => 445, odd_init => 446,
    nat_card_init => 447, ring_hom_init => 448, is_empty_init => 449,
    finite_init => 450, tensor_ml_init => 451, nn_verification_c002_init => 452,
    nn_verify_softmax_c011_init => 453, nn_verification_c009_init => 454, nn_verify_abstract_domain_init => 455,
    nn_verify_abstract_domain_ibp_init => 456, nn_verify_types_init => 457, nn_verify_types_ops_init => 458,
    nn_verify_foundation_types_init => 459, nn_verify_foundation_theorems_init => 460, nn_verify_farkas_constructive_init => 461,
    nn_verify_farkas_list_init => 462, nn_verify_farkas_to_interval_constructive_init => 463, fin_sum_init => 464,
    nn_verify_relu_init => 465, nn_verify_proofs_init => 466, nn_verify_interval_arith_proofs_init => 467,
    nn_verify_interval_containment_proofs_init => 468, nn_verify_interval_primitives_init => 469, nn_verify_rat_interval_init => 470,
    nn_verify_rat_interval_proofs_init => 471, nn_verify_ibp_linear_init => 472, nn_verify_rat_ordering_init => 473,
    nn_verify_ibp_composition_init => 474, nn_verify_crown_layernorm_init => 475, nn_verify_orbit_crown_init => 476,
    nn_verify_blockwise_crown_init => 477, nn_verify_ibp_tightness_init => 478, nn_verify_ibp_width_zero_init => 479,
    nn_verify_tier_a_rat_min_zero_init => 480, nn_verify_tier_a_rat_le_refl_zero_init => 481, nn_verify_tier_a_rat_zero_eq_max_init => 482,
    nn_verify_tier_a_rat_zero_eq_min_init => 483, nn_verify_tier_a_rat_max_eq_min_init => 484, nn_verify_tier_a_rat_min_eq_max_init => 485,
    nn_verify_tier_a_rat_max_zero_zero_alt_init => 486, nn_verify_tier_a_rat_min_zero_zero_alt_init => 487, nn_verify_tier_a_rat_le_refl_max_zero_zero_init => 488,
    nn_verify_tier_a_rat_le_refl_min_zero_zero_init => 489, nn_verify_tier_a_rat_mul_zero_zero_init => 490, nn_verify_tier_a_rat_mul_one_zero_init => 491,
    nn_verify_tier_a_rat_mul_zero_one_init => 492, nn_verify_tier_a_rat_add_neg_self_zero_init => 493, nn_verify_tier_a_rat_add_left_neg_zero_init => 494,
    nn_verify_tier_a_rat_mul_neg_zero_zero_init => 495, nn_verify_tier_a_rat_neg_zero_zero_init => 496, nn_verify_tier_a_nat_ordering_init => 497,
    nat_top_level_ordering_init => 498, nn_verify_tier_a_rat_min_le_max_zero_zero_init => 499, nn_verify_tier_a_rat_max_le_min_zero_zero_init => 500,
    nn_verify_tier_a_rat_min_min_zero_zero_init => 501, nn_verify_tier_a_rat_max_max_zero_zero_init => 502, nn_verify_tier_a_rat_max_min_zero_zero_init => 503,
    rat_min_le_max_init => 504, nn_verify_network_proof_init => 505, nn_verify_mccormick_init => 506,
    nn_verify_elementwise_init => 507, nn_verify_certified_training_init => 508, nn_verify_certified_eval_init => 509,
    boolean_analysis_init => 510, boolean_analysis_init_in_progress => 511, boolean_analysis_foundations_init => 512,
    boolean_analysis_order_toolkit_init => 513, boolean_analysis_order_toolkit_b1b_init => 514, boolean_analysis_order_toolkit_b1c_init => 515,
    boolean_analysis_order_toolkit_b1d_init => 516, boolean_analysis_ring_identities_init => 517, boolean_analysis_fourth_power_init => 518,
    boolean_analysis_peel_init => 519, boolean_analysis_peel_compute_init => 520, boolean_analysis_peel_parts_init => 521,
    boolean_analysis_noise_peel_init => 522, boolean_analysis_noise_extend_bridge_init => 523, fourier_boolean_init => 524,
    resolution_complexity_init => 525, tree_width_resolution_init => 526, width_expansion_init => 527,
    proof_hierarchy_init => 528, craig_interpolation_init => 529, cutting_planes_init => 530,
    veripb_checker_init => 531, abstract_interpretation_init => 532, abstract_interpretation_framework_init => 533,
    labelled_interpolation_minimality_init => 534, learned_clause_minimality_init => 535, gf2_polynomial_calculus_init => 536,
    pb_pigeonhole_init => 537, pb_pigeonhole_length_bound_init => 538, nn_verify_float_rational_init => 539,
    nn_verify_zonotope_compress_init => 540, nn_verify_zonotope_proofs_init => 541, feasible_interpolation_init => 542,
    extension_rule_init => 543, bounded_width_automatizability_init => 544, cdcl_soundness_init => 545,
    entropy_clause_quality_init => 546, extension_rule_soundness_init => 547, isasat_refinement_init => 548,
    bcp_loop_refinement_init => 549, verified_proof_search_init => 550,
}
