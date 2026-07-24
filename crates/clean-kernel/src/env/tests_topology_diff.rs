// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Topology tests for Environment
use super::test_helpers::expr_contains_const;
use super::*;

fn namespace_constant_count(env: &Environment, namespace: &str) -> usize {
    let prefix = format!("{namespace}.");
    env.constants()
        .filter(|info| info.name.to_string().starts_with(&prefix))
        .count()
}

// ================================================================
// TopologicalSpace Tests
// ================================================================

#[test]
fn test_topology_morse_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_morse());
    env.init_topology_morse().unwrap();
    assert!(env.has_topology_morse());
}

#[test]
fn test_topology_morse_idempotent() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();
    env.init_topology_morse().unwrap();
    assert!(env.has_topology_morse());
}

#[test]
fn test_topology_morse_overlay_namespace_decl_count() {
    let mut env = Environment::new();
    env.init_topology_morse().expect("init_topology_morse");

    assert_eq!(namespace_constant_count(&env, "Topology.Morse"), 26);

    for name in [
        "Topology.Morse.MorseFunction",
        "Topology.Morse.SublevelFiltration",
        "Topology.Morse.morse_differential",
        "Topology.Morse.riemannian_metric",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} missing after init_topology_morse"
        );
    }

    env.init_topology_morse()
        .expect("idempotent init_topology_morse");
    assert_eq!(namespace_constant_count(&env, "Topology.Morse"), 26);
}

#[test]
fn test_topology_morse_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let constants = [
        "Topology.Morse.MorseFunction",
        "Topology.Morse.CriticalPoint",
        "Topology.Morse.Nondegenerate",
        "Topology.Morse.MorseIndex",
        "Topology.Morse.MorseLemma",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_morse_function_type() {
    use crate::tc::TypeChecker;
    // Topology.Morse.MorseFunction : {M : Type u} → [TopologicalSpace M] →
    //   {dim : Nat} → (f : M → Rat) → Prop
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let mf = Expr::const_(
        Name::from_string("Topology.Morse.MorseFunction"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&mf)
        .expect("invariant: MorseFunction should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 4,
        "MorseFunction should have 4 Pi binders (M, [TS M], dim, f)"
    );
}

#[test]
fn test_topology_morse_critical_point_type() {
    use crate::tc::TypeChecker;
    // Topology.Morse.CriticalPoint : {M : Type u} → [TopologicalSpace M] →
    //   {dim : Nat} → (f : M → Rat) → (x : M) → Prop
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let cp = Expr::const_(
        Name::from_string("Topology.Morse.CriticalPoint"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&cp)
        .expect("invariant: CriticalPoint should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "CriticalPoint should have 5 Pi binders (M, [TS M], dim, f, x)"
    );
}

#[test]
fn test_topology_morse_nondegenerate_type() {
    use crate::tc::TypeChecker;
    // Topology.Morse.Nondegenerate : {M : Type u} → [TopologicalSpace M] →
    //   {n : Nat} → (f : M → Rat) → (p : M) → Prop
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let nd = Expr::const_(
        Name::from_string("Topology.Morse.Nondegenerate"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&nd)
        .expect("invariant: Nondegenerate should type-check");
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 5,
        "Nondegenerate should have 5 Pi binders (M, [TS M], n, f, p)"
    );
}

#[test]
fn test_topology_morse_flow_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let constants = [
        "Topology.Morse.GradientFlow",
        "Topology.Morse.gradient_flow_exists",
        "Topology.Morse.StableManifold",
        "Topology.Morse.UnstableManifold",
        "Topology.Morse.MorseSmale",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_morse_complex_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let constants = [
        "Topology.Morse.SublevelFiltration",
        "Topology.Morse.MorseComplex",
        "Topology.Morse.morse_differential",
        "Topology.Morse.morse_d_squared_zero",
        "Topology.Morse.MorseHomology",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_morse_homology_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let constants = [
        "Topology.Morse.morse_homology_eq_singular",
        "Topology.Morse.morse_inequalities",
        "Topology.Morse.perfect_morse_function",
        "Topology.Morse.palais_smale_condition",
        "Topology.Morse.handle_decomposition",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_morse_additional_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    let constants = [
        "Topology.Morse.handle_slides",
        "Topology.Morse.witten_deformation",
        "Topology.Morse.sard_for_morse",
        "Topology.Morse.homology_of_sublevel",
        "Topology.Morse.morse_smash_product",
        "Topology.Morse.riemannian_metric",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_morse_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_eq());
    assert!(env.has_topology_derham());
    assert!(env.has_topology_homology());
    assert!(env.has_topology_filtration());
    assert!(env.has_add_comm_group());
}

// ============================================================
// Topology.KTheory tests
// ============================================================

#[test]
fn test_topology_ktheory_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_ktheory());
    env.init_topology_ktheory().unwrap();
    assert!(env.has_topology_ktheory());
}

#[test]
fn test_topology_ktheory_idempotent() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();
    env.init_topology_ktheory().unwrap(); // Should not error
    assert!(env.has_topology_ktheory());
}

#[test]
fn test_topology_ktheory_k_groups_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    // Core K-group types
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.K"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.K_zero"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.K_neg_one"))
        .is_some());
}

#[test]
fn test_topology_ktheory_algebraic_structure_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.K_is_add_comm_group"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.K_zero_is_ring"))
        .is_some());
}

#[test]
fn test_topology_ktheory_vector_bundle_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.VectorBundleClass"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.KTheory.grothendieck_completion"
        ))
        .is_some());
}

#[test]
fn test_topology_ktheory_bott_periodicity_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.bott_periodicity"))
        .is_some());
}

#[test]
fn test_topology_ktheory_adams_operations_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.adams_operation"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.adams_ring_hom"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.adams_composition"))
        .is_some());
}

#[test]
fn test_topology_ktheory_functoriality_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.induced"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.functoriality"))
        .is_some());
}

#[test]
fn test_topology_ktheory_reduced_k_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.ReducedK"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.reduced_splitting"))
        .is_some());
}

#[test]
fn test_topology_ktheory_chern_character_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.chern_character"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.chern_is_ring_hom"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.chern_isomorphism"))
        .is_some());
}

#[test]
fn test_topology_ktheory_exact_sequences_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.exact_sequence"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.split_exact"))
        .is_some());
}

#[test]
fn test_topology_ktheory_homotopy_invariance_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.homotopy_invariance"))
        .is_some());
}

#[test]
fn test_topology_ktheory_computations_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.K_sphere"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.K_point"))
        .is_some());
}

#[test]
fn test_topology_ktheory_isomorphisms_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.suspension_iso"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.thom_isomorphism"))
        .is_some());
}

#[test]
fn test_topology_ktheory_spectral_sequence_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.atiyah_hirzebruch"))
        .is_some());
}

#[test]
fn test_topology_ktheory_auxiliary_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.tensor_product"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.wedge_axiom"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.dimension"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.KTheory.clutching"))
        .is_some());
}

#[test]
fn test_topology_ktheory_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    let constants = [
        "Topology.KTheory.K",
        "Topology.KTheory.K_zero",
        "Topology.KTheory.K_neg_one",
        "Topology.KTheory.K_is_add_comm_group",
        "Topology.KTheory.K_zero_is_ring",
        "Topology.KTheory.VectorBundleClass",
        "Topology.KTheory.grothendieck_completion",
        "Topology.KTheory.bott_periodicity",
        "Topology.KTheory.adams_operation",
        "Topology.KTheory.adams_ring_hom",
        "Topology.KTheory.adams_composition",
        "Topology.KTheory.induced",
        "Topology.KTheory.functoriality",
        "Topology.KTheory.ReducedK",
        "Topology.KTheory.reduced_splitting",
        "Topology.KTheory.tensor_product",
        "Topology.KTheory.chern_character",
        "Topology.KTheory.chern_is_ring_hom",
        "Topology.KTheory.chern_isomorphism",
        "Topology.KTheory.exact_sequence",
        "Topology.KTheory.homotopy_invariance",
        "Topology.KTheory.K_sphere",
        "Topology.KTheory.K_point",
        "Topology.KTheory.suspension_iso",
        "Topology.KTheory.thom_isomorphism",
        "Topology.KTheory.atiyah_hirzebruch",
        "Topology.KTheory.wedge_axiom",
        "Topology.KTheory.dimension",
        "Topology.KTheory.clutching",
        "Topology.KTheory.split_exact",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_ktheory_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_rat());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_vector_bundle());
    assert!(env.has_topology_suspension());
    assert!(env.has_topology_compact());
    assert!(env.has_eq());
    assert!(env.has_add_comm_group());
    assert!(env.has_ring());
}

// ============================================================
// Topology.Filtration tests
// ============================================================

#[test]
fn test_topology_filtration_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_filtration());
    env.init_topology_filtration().unwrap();
    assert!(env.has_topology_filtration());
}

#[test]
fn test_topology_filtration_idempotent() {
    let mut env = Environment::new();
    env.init_topology_filtration().unwrap();
    env.init_topology_filtration().unwrap();
    assert!(env.has_topology_filtration());
}

#[test]
fn test_topology_filtration_overlay_namespace_decl_count() {
    let mut env = Environment::new();
    env.init_topology_filtration()
        .expect("init_topology_filtration");

    assert_eq!(namespace_constant_count(&env, "Topology.Filtration"), 18);

    for name in [
        "Topology.Filtration.Filtration",
        "Topology.Filtration.level",
        "Topology.Filtration.FilteredComplex",
        "Topology.Filtration.topology_from_filtration",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} missing after init_topology_filtration"
        );
    }

    env.init_topology_filtration()
        .expect("idempotent init_topology_filtration");
    assert_eq!(namespace_constant_count(&env, "Topology.Filtration"), 18);
}

#[test]
fn test_topology_filtration_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_filtration().unwrap();

    let constants = [
        "Topology.Filtration.Filtration",
        "Topology.Filtration.level",
        "Topology.Filtration.associated_graded",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_filtration_properties_exist() {
    let mut env = Environment::new();
    env.init_topology_filtration().unwrap();

    let constants = [
        "Topology.Filtration.is_increasing",
        "Topology.Filtration.bounded_below",
        "Topology.Filtration.exhaustive",
        "Topology.Filtration.separated",
        "Topology.Filtration.complete",
        "Topology.Filtration.finite_length",
        "Topology.Filtration.exhaustive_complete_equiv",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_filtration_structure_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_filtration().unwrap();

    let constants = [
        "Topology.Filtration.shift",
        "Topology.Filtration.morphism",
        "Topology.Filtration.compatible",
        "Topology.Filtration.topology_from_filtration",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_filtration_complex_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_filtration().unwrap();

    let constants = [
        "Topology.Filtration.FilteredComplex",
        "Topology.Filtration.filtered_boundary_compatible",
        "Topology.Filtration.associated_graded_complex",
        "Topology.Filtration.induced_filtration_on_homology",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_filtration_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_filtration().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_eq());
    assert!(env.has_ring());
    assert!(env.has_add_comm_group());
    assert!(env.has_topology_homology());
}

// ============================================================
// Topology.Spectral tests
// ============================================================

#[test]
fn test_topology_spectral_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_spectral());
    env.init_topology_spectral().unwrap();
    assert!(env.has_topology_spectral());
}

#[test]
fn test_topology_spectral_idempotent() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();
    env.init_topology_spectral().unwrap(); // Should not error
    assert!(env.has_topology_spectral());
}

#[test]
fn test_topology_spectral_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.SpectralSequence"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.E_page"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.differential"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.E_infty"))
        .is_some());
}

#[test]
fn test_topology_spectral_fundamental_properties_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.d_squared_zero"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.page_homology"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.converges_to"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.convergence_theorem"))
        .is_some());
}

#[test]
fn test_topology_spectral_serre_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.serre"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.serre_e2"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.serre_converges"))
        .is_some());
}

#[test]
fn test_topology_spectral_adams_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.adams"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.adams_e2"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.adams_converges"))
        .is_some());
}

#[test]
fn test_topology_spectral_atiyah_hirzebruch_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.atiyah_hirzebruch"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.ah_e2"))
        .is_some());
}

#[test]
fn test_topology_spectral_leray_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.leray"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.leray_e2"))
        .is_some());
}

#[test]
fn test_topology_spectral_grothendieck_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.grothendieck"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.grothendieck_e2"))
        .is_some());
}

#[test]
fn test_topology_spectral_edge_and_transgression_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.edge_horizontal"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.edge_vertical"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.transgression"))
        .is_some());
}

#[test]
fn test_topology_spectral_bounded_properties_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.is_first_quadrant"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.is_bounded"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.bounded_collapses"))
        .is_some());
}

#[test]
fn test_topology_spectral_collapse_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.collapses_at"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.degenerates"))
        .is_some());
}

#[test]
fn test_topology_spectral_multiplicative_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.is_multiplicative"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.product"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.leibniz"))
        .is_some());
}

#[test]
fn test_topology_spectral_exact_couple_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.ExactCouple"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.derived_couple"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.couple_to_spectral"))
        .is_some());
}

#[test]
fn test_topology_spectral_comparison_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.morphism"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spectral.comparison_theorem"))
        .is_some());
}

#[test]
fn test_topology_spectral_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    let constants = [
        "Topology.Spectral.SpectralSequence",
        "Topology.Spectral.E_page",
        "Topology.Spectral.differential",
        "Topology.Spectral.d_squared_zero",
        "Topology.Spectral.page_homology",
        "Topology.Spectral.E_infty",
        "Topology.Spectral.converges_to",
        "Topology.Spectral.filtration",
        "Topology.Spectral.associated_graded",
        "Topology.Spectral.convergence_theorem",
        "Topology.Spectral.serre",
        "Topology.Spectral.serre_e2",
        "Topology.Spectral.serre_converges",
        "Topology.Spectral.atiyah_hirzebruch",
        "Topology.Spectral.ah_e2",
        "Topology.Spectral.adams",
        "Topology.Spectral.adams_e2",
        "Topology.Spectral.adams_converges",
        "Topology.Spectral.leray",
        "Topology.Spectral.leray_e2",
        "Topology.Spectral.grothendieck",
        "Topology.Spectral.grothendieck_e2",
        "Topology.Spectral.edge_horizontal",
        "Topology.Spectral.edge_vertical",
        "Topology.Spectral.transgression",
        "Topology.Spectral.is_first_quadrant",
        "Topology.Spectral.is_bounded",
        "Topology.Spectral.bounded_collapses",
        "Topology.Spectral.collapses_at",
        "Topology.Spectral.degenerates",
        "Topology.Spectral.is_multiplicative",
        "Topology.Spectral.product",
        "Topology.Spectral.leibniz",
        "Topology.Spectral.ExactCouple",
        "Topology.Spectral.derived_couple",
        "Topology.Spectral.couple_to_spectral",
        "Topology.Spectral.morphism",
        "Topology.Spectral.comparison_theorem",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_spectral_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_topology_filtration());
    assert!(env.has_topology_homology());
    assert!(env.has_topology_fiber_bundle());
    assert!(env.has_eq());
    assert!(env.has_add_comm_group());
}

// ================================================================
// Topology.Sheaf Tests
// ================================================================

#[test]
fn test_topology_sheaf_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_sheaf());
    env.init_topology_sheaf().unwrap();
    assert!(env.has_topology_sheaf());
}

#[test]
fn test_topology_sheaf_idempotent() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();
    env.init_topology_sheaf().unwrap(); // Should not error
    assert!(env.has_topology_sheaf());
}

#[test]
fn test_topology_sheaf_presheaf_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.Presheaf"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.sections"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.restriction"))
        .is_some());
}

#[test]
fn test_topology_sheaf_sheaf_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.Sheaf"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.to_presheaf"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.gluing"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.locality"))
        .is_some());
}

#[test]
fn test_topology_sheaf_stalk_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.Stalk"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.germ"))
        .is_some());
}

#[test]
fn test_topology_sheaf_sheafification_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.sheafify"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.sheafify_unit"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.sheafify_universal"))
        .is_some());
}

#[test]
fn test_topology_sheaf_constructions_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.GlobalSections"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.constant_sheaf"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.skyscraper"))
        .is_some());
}

#[test]
fn test_topology_sheaf_functors_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.direct_image"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.inverse_image"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.adjunction"))
        .is_some());
}

#[test]
fn test_topology_sheaf_morphism_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.SheafHom"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.kernel"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.cokernel"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.image"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.exact_sequence"))
        .is_some());
}

#[test]
fn test_topology_sheaf_cohomology_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.SheafCohomology"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.h0_global_sections"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.long_exact_sequence"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.CechCohomology"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.cech_sheaf_comparison"))
        .is_some());
}

#[test]
fn test_topology_sheaf_acyclicity_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.flasque"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.flasque_acyclic"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.soft"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.fine"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.fine_soft"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.soft_acyclic"))
        .is_some());
}

#[test]
fn test_topology_sheaf_ringed_space_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.RingedSpace"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.structure_sheaf"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.LocallyRingedSpace"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.stalk_local"))
        .is_some());
}

#[test]
fn test_topology_sheaf_locally_free_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.locally_free"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Sheaf.rank"))
        .is_some());
}

#[test]
fn test_topology_sheaf_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    let constants = [
        "Topology.Sheaf.Presheaf",
        "Topology.Sheaf.sections",
        "Topology.Sheaf.restriction",
        "Topology.Sheaf.Sheaf",
        "Topology.Sheaf.to_presheaf",
        "Topology.Sheaf.gluing",
        "Topology.Sheaf.locality",
        "Topology.Sheaf.Stalk",
        "Topology.Sheaf.germ",
        "Topology.Sheaf.sheafify",
        "Topology.Sheaf.sheafify_unit",
        "Topology.Sheaf.sheafify_universal",
        "Topology.Sheaf.GlobalSections",
        "Topology.Sheaf.constant_sheaf",
        "Topology.Sheaf.skyscraper",
        "Topology.Sheaf.direct_image",
        "Topology.Sheaf.inverse_image",
        "Topology.Sheaf.adjunction",
        "Topology.Sheaf.SheafHom",
        "Topology.Sheaf.kernel",
        "Topology.Sheaf.cokernel",
        "Topology.Sheaf.image",
        "Topology.Sheaf.exact_sequence",
        "Topology.Sheaf.SheafCohomology",
        "Topology.Sheaf.h0_global_sections",
        "Topology.Sheaf.long_exact_sequence",
        "Topology.Sheaf.CechCohomology",
        "Topology.Sheaf.cech_sheaf_comparison",
        "Topology.Sheaf.flasque",
        "Topology.Sheaf.flasque_acyclic",
        "Topology.Sheaf.soft",
        "Topology.Sheaf.fine",
        "Topology.Sheaf.fine_soft",
        "Topology.Sheaf.soft_acyclic",
        "Topology.Sheaf.RingedSpace",
        "Topology.Sheaf.structure_sheaf",
        "Topology.Sheaf.LocallyRingedSpace",
        "Topology.Sheaf.stalk_local",
        "Topology.Sheaf.locally_free",
        "Topology.Sheaf.rank",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_sheaf_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_eq());
    assert!(env.has_add_comm_group());
    assert!(env.has_ring());
}

// ================================================================
// Topology.Scheme tests
// ================================================================

#[test]
fn test_topology_scheme_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_scheme());
    env.init_topology_scheme().unwrap();
    assert!(env.has_topology_scheme());
}

#[test]
fn test_topology_scheme_idempotent() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();
    env.init_topology_scheme().unwrap();
    assert!(env.has_topology_scheme());
}

#[test]
fn test_topology_scheme_core_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();

    let constants = [
        "Topology.Scheme.Scheme",
        "Topology.Scheme.Spec",
        "Topology.Scheme.morphism",
        "Topology.Scheme.id",
        "Topology.Scheme.comp",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_scheme_structure_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();

    let constants = [
        "Topology.Scheme.underlying_space",
        "Topology.Scheme.structure_sheaf",
        "Topology.Scheme.global_sections",
        "Topology.Scheme.affine_open_cover",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_scheme_morphism_properties_exist() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();

    let constants = [
        "Topology.Scheme.is_isomorphism",
        "Topology.Scheme.open_immersion",
        "Topology.Scheme.closed_immersion",
        "Topology.Scheme.pullback",
        "Topology.Scheme.fiber_product",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_scheme_separation_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();

    let constants = [
        "Topology.Scheme.separated",
        "Topology.Scheme.quasi_compact",
        "Topology.Scheme.quasi_separated",
        "Topology.Scheme.noetherian",
        "Topology.Scheme.integral",
        "Topology.Scheme.reduced",
        "Topology.Scheme.normal",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_scheme_morphism_classes_exist() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();

    let constants = [
        "Topology.Scheme.proper",
        "Topology.Scheme.smooth",
        "Topology.Scheme.etale",
        "Topology.Scheme.flat",
        "Topology.Scheme.finite_type",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_scheme_cohomological_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();

    let constants = [
        "Topology.Scheme.coherent_sheaf",
        "Topology.Scheme.invertible_sheaf",
        "Topology.Scheme.line_bundle",
        "Topology.Scheme.divisor",
        "Topology.Scheme.cartier_divisor",
        "Topology.Scheme.picard_group",
        "Topology.Scheme.scheme_gluing",
        "Topology.Scheme.spec_adjoint_global_sections",
        "Topology.Scheme.base_change",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_scheme_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_eq());
    assert!(env.has_ring());
    assert!(env.has_comm_ring());
    assert!(env.has_topology_sheaf());
}

// ================================================================
// Topology.Cobordism tests
// ================================================================

#[test]
fn test_topology_cobordism_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_cobordism());
    env.init_topology_cobordism().unwrap();
    assert!(env.has_topology_cobordism());
}

#[test]
fn test_topology_cobordism_idempotent() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();
    env.init_topology_cobordism().unwrap(); // Should not error
    assert!(env.has_topology_cobordism());
}

#[test]
fn test_topology_cobordism_manifold_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.Manifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.boundary"))
        .is_some());
}

#[test]
fn test_topology_cobordism_relation_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.Cobordant"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.cobordant_refl"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.cobordant_symm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.cobordant_trans"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.Cobordism"))
        .is_some());
}

#[test]
fn test_topology_cobordism_group_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.CobordismGroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.OrientedCobordismGroup"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.FramedCobordismGroup"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.SpinCobordismGroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.cobordism_class"))
        .is_some());
}

#[test]
fn test_topology_cobordism_operations_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.disjoint_union"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.empty_manifold"))
        .is_some());
}

#[test]
fn test_topology_cobordism_thom_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.ThomSpace"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.thom_class"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.thom_isomorphism"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.pontryagin_thom"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.pontryagin_thom_iso"))
        .is_some());
}

#[test]
fn test_topology_cobordism_ring_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.CobordismRing"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.OrientedCobordismRing"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.ring_product"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.thom_structure_theorem"
        ))
        .is_some());
}

#[test]
fn test_topology_cobordism_surgery_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.hCobordism"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.h_cobordism_theorem"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.Surgery"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.perform_surgery"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.surgery_cobordant"))
        .is_some());
}

#[test]
fn test_topology_cobordism_characteristic_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.StiefelWhitneyNumber"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.PontryaginNumber"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.characteristic_cobordism_invariant"
        ))
        .is_some());
}

#[test]
fn test_topology_cobordism_spectrum_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.MOSpectrum"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.MSOSpectrum"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.MUSpectrum"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.spectrum_homology"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.MO_homology_cobordism"
        ))
        .is_some());
}

#[test]
fn test_topology_cobordism_complex_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.Cobordism.ComplexCobordismGroup"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.FormalGroupLaw"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.MU_formal_group"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Cobordism.quillen_theorem"))
        .is_some());
}

#[test]
fn test_topology_cobordism_all_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    let constants = [
        "Topology.Cobordism.Manifold",
        "Topology.Cobordism.boundary",
        "Topology.Cobordism.Cobordant",
        "Topology.Cobordism.cobordant_refl",
        "Topology.Cobordism.cobordant_symm",
        "Topology.Cobordism.cobordant_trans",
        "Topology.Cobordism.Cobordism",
        "Topology.Cobordism.CobordismGroup",
        "Topology.Cobordism.OrientedCobordismGroup",
        "Topology.Cobordism.FramedCobordismGroup",
        "Topology.Cobordism.SpinCobordismGroup",
        "Topology.Cobordism.cobordism_class",
        "Topology.Cobordism.disjoint_union",
        "Topology.Cobordism.empty_manifold",
        "Topology.Cobordism.ThomSpace",
        "Topology.Cobordism.thom_class",
        "Topology.Cobordism.thom_isomorphism",
        "Topology.Cobordism.pontryagin_thom",
        "Topology.Cobordism.pontryagin_thom_iso",
        "Topology.Cobordism.CobordismRing",
        "Topology.Cobordism.OrientedCobordismRing",
        "Topology.Cobordism.ring_product",
        "Topology.Cobordism.thom_structure_theorem",
        "Topology.Cobordism.hCobordism",
        "Topology.Cobordism.h_cobordism_theorem",
        "Topology.Cobordism.Surgery",
        "Topology.Cobordism.perform_surgery",
        "Topology.Cobordism.surgery_cobordant",
        "Topology.Cobordism.StiefelWhitneyNumber",
        "Topology.Cobordism.PontryaginNumber",
        "Topology.Cobordism.characteristic_cobordism_invariant",
        "Topology.Cobordism.MOSpectrum",
        "Topology.Cobordism.MSOSpectrum",
        "Topology.Cobordism.MUSpectrum",
        "Topology.Cobordism.spectrum_homology",
        "Topology.Cobordism.MO_homology_cobordism",
        "Topology.Cobordism.ComplexCobordismGroup",
        "Topology.Cobordism.FormalGroupLaw",
        "Topology.Cobordism.MU_formal_group",
        "Topology.Cobordism.quillen_theorem",
    ];

    for name in &constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

#[test]
fn test_topology_cobordism_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_eq());
    assert!(env.has_topology_homology());
    assert!(env.has_add_comm_group());
    assert!(env.has_ring());
}

// ========================================================================
// Topology.Characteristic (characteristic classes) tests
// ========================================================================

#[test]
fn test_topology_characteristic_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_characteristic());
    env.init_topology_characteristic().unwrap();
    assert!(env.has_topology_characteristic());
}

#[test]
fn test_topology_characteristic_idempotent() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();
    env.init_topology_characteristic().unwrap(); // Should not error
    assert!(env.has_topology_characteristic());
}

#[test]
fn test_topology_characteristic_cohomology_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.CohomologyRing"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.Z2CohomologyRing"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_stiefel_whitney_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.RealVectorBundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.stiefel_whitney"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.total_stiefel_whitney"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.sw_zero"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.sw_vanishes_above_rank"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.sw_naturality"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.whitney_sum_formula"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_chern_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.ComplexVectorBundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.chern"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.total_chern"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.chern_zero"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.chern_vanishes_above_rank"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.chern_naturality"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.chern_whitney_sum"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.first_chern_line_bundle"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_pontryagin_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.pontryagin"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.total_pontryagin"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.pontryagin_via_chern"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.pontryagin_naturality"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_euler_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.OrientedBundle"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.euler"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.euler_square_pontryagin"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.euler_mod2_sw"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.euler_self_intersection"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_chern_character_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.chern_character"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.chern_character_additive"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.chern_character_multiplicative"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.todd"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.hirzebruch_riemann_roch"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_wu_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.wu"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.wu_formula"))
        .is_some());
}

#[test]
fn test_topology_characteristic_classifying_space_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.BO"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.BU"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.BSO"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.universal_real_bundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.universal_complex_bundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.classifying_map"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.pullback_universal"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_splitting_principle_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.FlagBundle"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.splitting_principle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.flag_injection"))
        .is_some());
}

#[test]
fn test_topology_characteristic_index_theory_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.a_hat"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.l_genus"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.atiyah_singer"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.hirzebruch_signature"
        ))
        .is_some());
}

#[test]
fn test_topology_characteristic_thom_gysin_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.Characteristic.thom_isomorphism"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.gysin_sequence"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Characteristic.euler_gysin"))
        .is_some());
}

#[test]
fn test_topology_characteristic_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_eq());
    assert!(env.has_topology_vector_bundle());
    assert!(env.has_topology_homology());
    assert!(env.has_add_comm_group());
    assert!(env.has_ring());
}

// =========================================================================
// Topology.Manifold Tests
// =========================================================================

#[test]
fn test_topology_manifold_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_manifold());
    env.init_topology_manifold().unwrap();
    assert!(env.has_topology_manifold());
}

#[test]
fn test_topology_manifold_idempotent() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();
    env.init_topology_manifold().unwrap(); // Should not error
    assert!(env.has_topology_manifold());
}

#[test]
fn test_topology_manifold_chart_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Chart"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Chart.domain"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Chart.toFun"))
        .is_some());
}

#[test]
fn test_topology_manifold_atlas_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Atlas"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Atlas.charts"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.SmoothAtlas"))
        .is_some());
}

#[test]
fn test_topology_manifold_smooth_manifold_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.SmoothManifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.TangentSpace"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.TangentBundle"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.CotangentSpace"))
        .is_some());
}

#[test]
fn test_topology_manifold_smooth_map_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.SmoothMap"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Diffeomorphism"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.IsDiffeomorphic"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.LocalDiffeomorphism"))
        .is_some());
}

#[test]
fn test_topology_manifold_immersion_submersion_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Immersion"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Submersion"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Embedding"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Submanifold"))
        .is_some());
}

#[test]
fn test_topology_manifold_differential_form_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.VectorField"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.DifferentialForm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.ExteriorDerivative"))
        .is_some());
}

#[test]
fn test_topology_manifold_orientation_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Orientable"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Orientation"))
        .is_some());
}

#[test]
fn test_topology_manifold_riemannian_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.RiemannianMetric"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.RiemannianManifold"))
        .is_some());
}

#[test]
fn test_topology_manifold_boundary_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.ManifoldWithBoundary"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.Boundary"))
        .is_some());
}

#[test]
fn test_topology_manifold_partition_of_unity_exists() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Manifold.PartitionOfUnity"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Manifold.paracompact_smooth_manifold"
        ))
        .is_some());
}

#[test]
fn test_topology_manifold_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_eq());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_homeomorphism());
    assert!(env.has_add_comm_group());
}

// =========================================================================
// Topology.LieGroup Tests
// =========================================================================

#[test]
fn test_topology_lie_group_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_lie_group());
    env.init_topology_lie_group().unwrap();
    assert!(env.has_topology_lie_group());
}

#[test]
fn test_topology_lie_group_idempotent() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();
    env.init_topology_lie_group().unwrap(); // Should not error
    assert!(env.has_topology_lie_group());
}

#[test]
fn test_topology_lie_group_basic_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.LieGroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.LieAlgebra"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.LieBracket"))
        .is_some());
}

#[test]
fn test_topology_lie_group_exp_map_exists() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.ExpMap"))
        .is_some());
}

#[test]
fn test_topology_lie_group_hom_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.LieGroupHom"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.LieAlgebraHom"))
        .is_some());
}

#[test]
fn test_topology_lie_algebra_hom_phi_uses_lie_algebra_types() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_topology_lie_group()
        .expect("invariant: lie group init should succeed");

    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let tc = TypeChecker::new(&env);
    let lie_algebra_hom = Expr::const_(
        Name::from_string("Topology.LieGroup.LieAlgebraHom"),
        vec![Level::param(u), Level::param(v)],
    );
    let ty = tc
        .infer_type(&lie_algebra_hom)
        .expect("invariant: LieAlgebraHom should type-check");

    let mut binders: Vec<Expr> = Vec::new();
    let mut t = ty;
    while let ExprKind::Pi(_, domain, body) = &t.kind {
        binders.push(domain.as_ref().clone());
        t = body.as_ref().clone();
    }

    assert_eq!(
        binders.len(),
        11,
        "LieAlgebraHom should have 11 Pi binders (G, H, [TS G], [TS H], [Group G], [Group H], m, n, [LieGroup G m], [LieGroup H n], phi)"
    );

    let phi_ty = binders
        .last()
        .expect("invariant: LieAlgebraHom must include phi binder");
    let (phi_domain, phi_codomain) = match &phi_ty.kind {
        ExprKind::Pi(_, domain, codomain) => (domain.as_ref(), codomain.as_ref()),
        other => panic!("expected function type for phi binder, got: {other:?}"),
    };

    let lie_algebra = Name::from_string("Topology.LieGroup.LieAlgebra");
    assert!(
        expr_contains_const(phi_domain, &lie_algebra),
        "LieAlgebraHom phi domain should mention Topology.LieGroup.LieAlgebra"
    );
    assert!(
        expr_contains_const(phi_codomain, &lie_algebra),
        "LieAlgebraHom phi codomain should mention Topology.LieGroup.LieAlgebra"
    );
    assert!(
        matches!(&t.kind, ExprKind::Sort(Level::Zero)),
        "LieAlgebraHom codomain should be Prop"
    );
}

#[test]
fn test_topology_lie_group_subgroup_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.LieSubgroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.OneParameterSubgroup"))
        .is_some());
}

fn expr_head_const_name(expr: &Expr) -> Option<&Name> {
    let mut cur = expr;
    loop {
        match &cur.kind {
            ExprKind::App(f, _) => cur = f.as_ref(),
            ExprKind::Const(name, _) => return Some(name),
            _ => return None,
        }
    }
}

#[test]
fn test_topology_lie_group_one_parameter_subgroup_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_topology_lie_group()
        .expect("invariant: lie group init should succeed");

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let one_param = Expr::const_(
        Name::from_string("Topology.LieGroup.OneParameterSubgroup"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&one_param)
        .expect("invariant: OneParameterSubgroup should type-check");

    let mut count = 0;
    let mut t = ty;
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 6,
        "OneParameterSubgroup should have 6 Pi binders (G, [TS G], [Group G], n, [LieGroup G n], gamma)"
    );

    assert!(
        matches!(&t.kind, ExprKind::Sort(Level::Zero)),
        "OneParameterSubgroup codomain should be Prop"
    );
}

#[test]
fn test_topology_lie_group_adjoint_rep_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_topology_lie_group()
        .expect("invariant: lie group init should succeed");

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let adjoint_rep = Expr::const_(
        Name::from_string("Topology.LieGroup.AdjointRep"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&adjoint_rep)
        .expect("invariant: AdjointRep should type-check");

    let mut count = 0;
    let mut t = ty;
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 7,
        "AdjointRep should have 7 Pi binders (G, [TS G], [Group G], n, [LieGroup G n], g, X)"
    );

    let lie_algebra = Name::from_string("Topology.LieGroup.LieAlgebra");
    assert!(
        matches!(expr_head_const_name(&t), Some(name) if name == &lie_algebra),
        "AdjointRep codomain should reduce to LieAlgebra"
    );
}

#[test]
fn test_topology_lie_group_little_adjoint_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_topology_lie_group()
        .expect("invariant: lie group init should succeed");

    let u = Name::from_string("u");
    let u_level = Level::param(u);
    let tc = TypeChecker::new(&env);
    let little_adjoint = Expr::const_(
        Name::from_string("Topology.LieGroup.adjoint_rep"),
        vec![u_level],
    );
    let ty = tc
        .infer_type(&little_adjoint)
        .expect("invariant: adjoint_rep should type-check");

    let mut count = 0;
    let mut t = ty;
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 7,
        "adjoint_rep should have 7 Pi binders (G, [TS G], [Group G], n, [LieGroup G n], X, Y)"
    );

    let lie_algebra = Name::from_string("Topology.LieGroup.LieAlgebra");
    assert!(
        matches!(expr_head_const_name(&t), Some(name) if name == &lie_algebra),
        "adjoint_rep codomain should reduce to LieAlgebra"
    );
}

#[test]
fn test_topology_lie_group_adjoint_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.AdjointRep"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.adjoint_rep"))
        .is_some());
}

#[test]
fn test_topology_lie_group_property_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.IsConnected"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.IsSimplyConnected"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.IsCompact"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.IsSemisimple"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.IsSimple"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.IsAbelian"))
        .is_some());
}

#[test]
fn test_topology_lie_group_universal_cover_exists() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.UniversalCover"))
        .is_some());
}

#[test]
fn test_topology_lie_group_killing_form_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.KillingForm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.LieGroup.killing_form_semisimple"
        ))
        .is_some());
}

#[test]
fn test_topology_lie_group_exp_one_param_exists() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.LieGroup.exp_one_param"))
        .is_some());
}

#[test]
fn test_topology_lie_group_depends_on_manifold() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    // LieGroup module should have initialized Manifold module
    assert!(env.has_topology_manifold());
}

#[test]
fn test_topology_lie_group_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_eq());
    assert!(env.has_topology_manifold());
    assert!(env.has_group());
    assert!(env.has_add_comm_group());
}

// ============================================================================
// Topology.PrincipalBundle Tests
// ============================================================================

#[test]
fn test_topology_principal_bundle_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_principal_bundle());
    env.init_topology_principal_bundle().unwrap();
    assert!(env.has_topology_principal_bundle());
}

#[test]
fn test_topology_principal_bundle_idempotent() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();
    env.init_topology_principal_bundle().unwrap();
    assert!(env.has_topology_principal_bundle());
}

#[test]
fn test_topology_principal_bundle_basic_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.PrincipalBundle.PrincipalBundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.proj"))
        .is_some());
}

#[test]
fn test_topology_principal_bundle_action_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.action"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.action_free"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.PrincipalBundle.action_transitive"
        ))
        .is_some());
}

#[test]
fn test_topology_principal_bundle_gauge_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.GaugeTrans"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.GaugeGroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.PrincipalBundle.gauge_trans_compose"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.PrincipalBundle.gauge_trans_id"
        ))
        .is_some());
}

#[test]
fn test_topology_principal_bundle_bundle_operations_exist() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.PrincipalBundle.AssociatedBundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.PrincipalBundle.PullbackBundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.PrincipalBundle.BundleMorphism"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.FrameBundle"))
        .is_some());
}

#[test]
fn test_topology_principal_bundle_structure_operations_exist() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.TrivialBundle"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.Reduction"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.PrincipalBundle.Extension"))
        .is_some());
}

#[test]
fn test_topology_principal_bundle_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_eq());
    assert!(env.has_topology_fiber_bundle());
    assert!(env.has_topology_lie_group());
    assert!(env.has_group());
}

// ============================================================================
// Topology.Connection Tests
// ============================================================================

#[test]
fn test_topology_connection_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_connection());
    env.init_topology_connection().unwrap();
    assert!(env.has_topology_connection());
}

#[test]
fn test_topology_connection_idempotent() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();
    env.init_topology_connection().unwrap();
    assert!(env.has_topology_connection());
}

#[test]
fn test_topology_connection_basic_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Connection.Connection"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.form"))
        .is_some());
}

#[test]
fn test_topology_connection_curvature_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Connection.curvature"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.flat"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.holonomy"))
        .is_some());
}

#[test]
fn test_topology_connection_levi_civita_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Connection.LeviCivita"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Connection.levi_civita_metric_compatible"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Connection.levi_civita_torsion_free"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.levi_civita_unique"))
        .is_some());
}

#[test]
fn test_topology_connection_curvature_tensors_exist() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Connection.Christoffel"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.RiemannCurvature"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.RicciTensor"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.ScalarCurvature"))
        .is_some());
}

#[test]
fn test_topology_connection_transport_constants_exist() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Connection.Geodesic"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.ParallelTransport"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.HorizontalLift"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Connection.BianchiIdentity"))
        .is_some());
}

#[test]
fn test_topology_connection_vector_connection_exists() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Connection.VectorConnection"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Connection.covariant_derivative"
        ))
        .is_some());
}

#[test]
fn test_topology_connection_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_eq());
    assert!(env.has_topology_principal_bundle());
    assert!(env.has_topology_manifold());
    assert!(env.has_topology_lie_group());
}

// ============================================================================
// Topology.Symplectic Tests
// ============================================================================

#[test]
fn test_topology_symplectic_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_symplectic());
    env.init_topology_symplectic().unwrap();
    assert!(env.has_topology_symplectic());
}

#[test]
fn test_topology_symplectic_idempotent() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();
    env.init_topology_symplectic().unwrap();
    assert!(env.has_topology_symplectic());
}

#[test]
fn test_topology_symplectic_core_structures_exist() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.SymplecticForm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.SymplecticManifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.symplectic_form_closed"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.symplectic_form_nondegenerate"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.symplectic_dim_even"
        ))
        .is_some());
}

#[test]
fn test_topology_symplectic_symplectomorphisms_exist() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.Symplectomorphism"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.symplectomorphism_compose"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.symplectomorphism_inv"
        ))
        .is_some());
}

#[test]
fn test_topology_symplectic_hamiltonian_mechanics_exist() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.HamiltonianVector"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.HamiltonianFlow"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.PoissonBracket"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.poisson_jacobi"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.poisson_leibniz"))
        .is_some());
}

#[test]
fn test_topology_symplectic_submanifolds_exist() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.LagrangianSubmanifold"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.CoisotropicSubmanifold"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.IsotropicSubmanifold"
        ))
        .is_some());
}

#[test]
fn test_topology_symplectic_reduction_exist() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.MomentMap"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.moment_equivariant"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Symplectic.SymplecticReduction"
        ))
        .is_some());
}

#[test]
fn test_topology_symplectic_fundamental_theorems_exist() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.Darboux"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.Moser"))
        .is_some());
}

#[test]
fn test_topology_symplectic_contact_geometry_exist() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.ContactManifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.ContactForm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.Reeb"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.Contactomorphism"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.Legendrian"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Symplectic.GrayStability"))
        .is_some());
}

#[test]
fn test_topology_symplectic_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_eq());
    assert!(env.has_topology_manifold());
    assert!(env.has_topology_lie_group());
    assert!(env.has_topology_derham());
}

#[test]
fn test_topology_symplectic_constant_count() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();

    // There should be 27 constants in the symplectic module
    let symplectic_names = [
        "Topology.Symplectic.SymplecticForm",
        "Topology.Symplectic.SymplecticManifold",
        "Topology.Symplectic.symplectic_form_closed",
        "Topology.Symplectic.symplectic_form_nondegenerate",
        "Topology.Symplectic.symplectic_dim_even",
        "Topology.Symplectic.Symplectomorphism",
        "Topology.Symplectic.symplectomorphism_compose",
        "Topology.Symplectic.symplectomorphism_inv",
        "Topology.Symplectic.HamiltonianVector",
        "Topology.Symplectic.HamiltonianFlow",
        "Topology.Symplectic.PoissonBracket",
        "Topology.Symplectic.poisson_jacobi",
        "Topology.Symplectic.poisson_leibniz",
        "Topology.Symplectic.LagrangianSubmanifold",
        "Topology.Symplectic.CoisotropicSubmanifold",
        "Topology.Symplectic.IsotropicSubmanifold",
        "Topology.Symplectic.MomentMap",
        "Topology.Symplectic.moment_equivariant",
        "Topology.Symplectic.SymplecticReduction",
        "Topology.Symplectic.Darboux",
        "Topology.Symplectic.Moser",
        "Topology.Symplectic.ContactManifold",
        "Topology.Symplectic.ContactForm",
        "Topology.Symplectic.Reeb",
        "Topology.Symplectic.Contactomorphism",
        "Topology.Symplectic.Legendrian",
        "Topology.Symplectic.GrayStability",
    ];

    for name in &symplectic_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

// ============================================================================
// Topology.Kahler (Kähler manifolds) tests
// ============================================================================

#[test]
fn test_topology_kahler_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_kahler());
    env.init_topology_kahler().unwrap();
    assert!(env.has_topology_kahler());
}

#[test]
fn test_topology_kahler_idempotent() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();
    env.init_topology_kahler().unwrap();
    assert!(env.has_topology_kahler());
}

#[test]
fn test_topology_kahler_complex_structures_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.ComplexStructure"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.complex_structure_sq"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.AlmostComplexManifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.Integrable"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.ComplexManifold"))
        .is_some());
}

#[test]
fn test_topology_kahler_compatibility_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.Hermitian"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.KahlerForm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Kahler.kahler_form_compatibility"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.KahlerManifold"))
        .is_some());
}

#[test]
fn test_topology_kahler_holomorphic_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.HolomorphicMap"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.Biholomorphism"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Kahler.HolomorphicVectorBundle"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.HolomorphicSection"))
        .is_some());
}

#[test]
fn test_topology_kahler_chern_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.ChernConnection"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "Topology.Kahler.chern_connection_unique"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.ChernCurvature"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.ChernClass"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.first_chern_class"))
        .is_some());
}

#[test]
fn test_topology_kahler_ricci_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.RicciForm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.ricci_form_closed"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.ScalarCurvature"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.KahlerEinstein"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.CalabiYau"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.CalabiConjecture"))
        .is_some());
}

#[test]
fn test_topology_kahler_hodge_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.HodgeDecomposition"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.hodge_symmetry"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.DolbeaultCohomology"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.DolbeaultOperator"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.HardLefschetz"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.LefschetzDecomposition"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.KodairaVanishing"))
        .is_some());
}

#[test]
fn test_topology_kahler_examples_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.FubiniStudyMetric"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.FubiniStudyKahler"))
        .is_some());
}

#[test]
fn test_topology_kahler_hyperkahler_exist() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.HyperKahlerManifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.hypercomplex_relation"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.QuaternionicKahler"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Kahler.hyperkahler_holonomy"))
        .is_some());
}

#[test]
fn test_topology_kahler_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_eq());
    assert!(env.has_topology_manifold()); // includes RiemannianManifold
    assert!(env.has_topology_symplectic());
    assert!(env.has_topology_derham());
}

#[test]
fn test_topology_kahler_constant_count() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();

    // There should be 37 constants in the Kähler module
    let kahler_names = [
        "Topology.Kahler.ComplexStructure",
        "Topology.Kahler.complex_structure_sq",
        "Topology.Kahler.AlmostComplexManifold",
        "Topology.Kahler.Integrable",
        "Topology.Kahler.ComplexManifold",
        "Topology.Kahler.Hermitian",
        "Topology.Kahler.KahlerForm",
        "Topology.Kahler.kahler_form_compatibility",
        "Topology.Kahler.KahlerManifold",
        "Topology.Kahler.HolomorphicMap",
        "Topology.Kahler.Biholomorphism",
        "Topology.Kahler.HolomorphicVectorBundle",
        "Topology.Kahler.HolomorphicSection",
        "Topology.Kahler.ChernConnection",
        "Topology.Kahler.chern_connection_unique",
        "Topology.Kahler.ChernCurvature",
        "Topology.Kahler.ChernClass",
        "Topology.Kahler.first_chern_class",
        "Topology.Kahler.RicciForm",
        "Topology.Kahler.ricci_form_closed",
        "Topology.Kahler.ScalarCurvature",
        "Topology.Kahler.KahlerEinstein",
        "Topology.Kahler.CalabiYau",
        "Topology.Kahler.CalabiConjecture",
        "Topology.Kahler.HodgeDecomposition",
        "Topology.Kahler.hodge_symmetry",
        "Topology.Kahler.DolbeaultCohomology",
        "Topology.Kahler.DolbeaultOperator",
        "Topology.Kahler.HardLefschetz",
        "Topology.Kahler.LefschetzDecomposition",
        "Topology.Kahler.KodairaVanishing",
        "Topology.Kahler.FubiniStudyMetric",
        "Topology.Kahler.FubiniStudyKahler",
        "Topology.Kahler.HyperKahlerManifold",
        "Topology.Kahler.hypercomplex_relation",
        "Topology.Kahler.QuaternionicKahler",
        "Topology.Kahler.hyperkahler_holonomy",
    ];

    for name in &kahler_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

// ============================================================================
// Topology.Spin (Spin geometry) tests
// ============================================================================

#[test]
fn test_topology_spin_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_topology_spin());
    env.init_topology_spin().unwrap();
    assert!(env.has_topology_spin());
}

#[test]
fn test_topology_spin_idempotent() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();
    env.init_topology_spin().unwrap();
    assert!(env.has_topology_spin());
}

#[test]
fn test_topology_spin_clifford_algebra_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.QuadraticForm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.polarization"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.CliffordAlgebra"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.clifford_relation"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.CliffordEven"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.CliffordOdd"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.clifford_grading"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.clifford_embedding"))
        .is_some());
}

#[test]
fn test_topology_spin_groups_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinGroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_double_cover"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_kernel"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_lie_algebra"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.PinPlus"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.PinMinus"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.pin_relation"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_low_dim"))
        .is_some());
}

#[test]
fn test_topology_spin_structures_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.FrameBundle"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinStructure"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_lift"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_obstruction"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinManifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_uniqueness"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_bordism"))
        .is_some());
}

#[test]
fn test_topology_spin_spinor_bundles_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinRepresentation"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinorBundle"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.ComplexSpinors"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.RealSpinors"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinorField"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.clifford_action"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.ChiralityOperator"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.WeylSpinors"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.chiral_decomposition"))
        .is_some());
}

#[test]
fn test_topology_spin_dirac_operators_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinConnection"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spin_connection_lift"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.DiracOperator"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.dirac_self_adjoint"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.dirac_square"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.WeitzenbockFormula"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.DiracSpectrum"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.dirac_discrete_spectrum"))
        .is_some());
}

#[test]
fn test_topology_spin_index_theory_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.DiracIndex"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.AtiyahSingerSpin"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.AHatGenus"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.ahat_characteristic"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.ahat_multiplicative"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.RokhlinTheorem"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.alpha_invariant"))
        .is_some());
}

#[test]
fn test_topology_spin_spinc_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinCGroup"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spinc_exact"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinCStructure"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spinc_obstruction"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spinc_always_4d"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinCManifold"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spinc_line_bundle"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinCDirac"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.spinc_index"))
        .is_some());
}

#[test]
fn test_topology_spin_physics_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.FermionField"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.DiracEquation"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.dirac_covariant"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.ChiralAnomaly"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.anomaly_index"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.MajoranaSpinor"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.majorana_condition"))
        .is_some());
}

#[test]
fn test_topology_spin_advanced_exist() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinorNorm"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.ChargeConjugation"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.RealityCondition"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.PeriodicityBott"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.SpinFoam"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.TwistedSpinors"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.KillingSpinor"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.ParallelSpinor"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("Topology.Spin.parallel_holonomy"))
        .is_some());
}

#[test]
fn test_topology_spin_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_eq());
    assert!(env.has_topology_manifold());
    assert!(env.has_topology_principal_bundle());
    assert!(env.has_topology_connection());
    assert!(env.has_topology_characteristic());
}

#[test]
fn test_topology_spin_constant_count() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();

    // There should be 63 constants in the Spin module
    let spin_names = [
        // Clifford Algebras (8)
        "Topology.Spin.QuadraticForm",
        "Topology.Spin.polarization",
        "Topology.Spin.CliffordAlgebra",
        "Topology.Spin.clifford_relation",
        "Topology.Spin.CliffordEven",
        "Topology.Spin.CliffordOdd",
        "Topology.Spin.clifford_grading",
        "Topology.Spin.clifford_embedding",
        // Spin and Pin Groups (8)
        "Topology.Spin.SpinGroup",
        "Topology.Spin.spin_double_cover",
        "Topology.Spin.spin_kernel",
        "Topology.Spin.spin_lie_algebra",
        "Topology.Spin.PinPlus",
        "Topology.Spin.PinMinus",
        "Topology.Spin.pin_relation",
        "Topology.Spin.spin_low_dim",
        // Spin Structures (7)
        "Topology.Spin.FrameBundle",
        "Topology.Spin.SpinStructure",
        "Topology.Spin.spin_lift",
        "Topology.Spin.spin_obstruction",
        "Topology.Spin.SpinManifold",
        "Topology.Spin.spin_uniqueness",
        "Topology.Spin.spin_bordism",
        // Spinor Bundles (9)
        "Topology.Spin.SpinRepresentation",
        "Topology.Spin.SpinorBundle",
        "Topology.Spin.ComplexSpinors",
        "Topology.Spin.RealSpinors",
        "Topology.Spin.SpinorField",
        "Topology.Spin.clifford_action",
        "Topology.Spin.ChiralityOperator",
        "Topology.Spin.WeylSpinors",
        "Topology.Spin.chiral_decomposition",
        // Dirac Operators (8)
        "Topology.Spin.SpinConnection",
        "Topology.Spin.spin_connection_lift",
        "Topology.Spin.DiracOperator",
        "Topology.Spin.dirac_self_adjoint",
        "Topology.Spin.dirac_square",
        "Topology.Spin.WeitzenbockFormula",
        "Topology.Spin.DiracSpectrum",
        "Topology.Spin.dirac_discrete_spectrum",
        // Index Theory (7)
        "Topology.Spin.DiracIndex",
        "Topology.Spin.AtiyahSingerSpin",
        "Topology.Spin.AHatGenus",
        "Topology.Spin.ahat_characteristic",
        "Topology.Spin.ahat_multiplicative",
        "Topology.Spin.RokhlinTheorem",
        "Topology.Spin.alpha_invariant",
        // Spin^c Structures (9)
        "Topology.Spin.SpinCGroup",
        "Topology.Spin.spinc_exact",
        "Topology.Spin.SpinCStructure",
        "Topology.Spin.spinc_obstruction",
        "Topology.Spin.spinc_always_4d",
        "Topology.Spin.SpinCManifold",
        "Topology.Spin.spinc_line_bundle",
        "Topology.Spin.SpinCDirac",
        "Topology.Spin.spinc_index",
        // Physics Applications (7)
        "Topology.Spin.FermionField",
        "Topology.Spin.DiracEquation",
        "Topology.Spin.dirac_covariant",
        "Topology.Spin.ChiralAnomaly",
        "Topology.Spin.anomaly_index",
        "Topology.Spin.MajoranaSpinor",
        "Topology.Spin.majorana_condition",
        // Advanced Topics (9)
        "Topology.Spin.SpinorNorm",
        "Topology.Spin.ChargeConjugation",
        "Topology.Spin.RealityCondition",
        "Topology.Spin.PeriodicityBott",
        "Topology.Spin.SpinFoam",
        "Topology.Spin.TwistedSpinors",
        "Topology.Spin.KillingSpinor",
        "Topology.Spin.ParallelSpinor",
        "Topology.Spin.parallel_holonomy",
    ];

    for name in &spin_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing constant: {name}"
        );
    }
}

// ================================================================
// Type well-formedness tests (Issue #1538)
//
// One tc.infer_type() call per topology domain to verify registered
// types are well-formed, not just present.
// ================================================================

/// Helper: verify a single topology constant has a well-formed type.
/// Looks up the constant's declaration for correct universe parameter count.
/// Verifies tc.infer_type() succeeds (proves type well-formedness) and
/// that the result is a Sort or Pi type (type-level or function-level constant).
fn assert_topology_key_type_well_formed(env: &Environment, name: &str) {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    let n = Name::from_string(name);
    let ci = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name}: constant not found in env"));
    let levels: Vec<Level> = ci.level_params.iter().map(|_| Level::zero()).collect();
    let expr = Expr::const_(n, levels);
    let ty = tc
        .infer_type(&expr)
        .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
    // Type must be a Sort (type constant) or Pi (function/predicate constant)
    assert!(
        matches!(&ty.kind, ExprKind::Sort(_) | ExprKind::Pi(..)),
        "{name}: expected Sort or Pi type, got {ty:?}"
    );
}

#[test]
fn test_topology_morse_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Morse.MorseFunction");
}

#[test]
fn test_topology_ktheory_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.KTheory.K");
}

#[test]
fn test_topology_filtration_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_filtration().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Filtration.Filtration");
}

#[test]
fn test_topology_spectral_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_spectral().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Spectral.SpectralSequence");
}

#[test]
fn test_topology_sheaf_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_sheaf().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Sheaf.Presheaf");
}

#[test]
fn test_topology_scheme_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_scheme().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Scheme.Scheme");
}

#[test]
fn test_topology_cobordism_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Cobordism.Manifold");
}

#[test]
fn test_topology_characteristic_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_characteristic().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Characteristic.CohomologyRing");
}

#[test]
fn test_topology_manifold_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_manifold().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Manifold.Chart");
}

#[test]
fn test_topology_lie_group_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_lie_group().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.LieGroup.LieGroup");
}

#[test]
fn test_topology_principal_bundle_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_principal_bundle().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.PrincipalBundle.PrincipalBundle");
}

#[test]
fn test_topology_connection_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_connection().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Connection.Connection");
}

#[test]
fn test_topology_symplectic_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Symplectic.SymplecticForm");
}

#[test]
fn test_topology_kahler_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_kahler().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Kahler.ComplexStructure");
}

#[test]
fn test_topology_spin_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_topology_spin().unwrap();
    assert_topology_key_type_well_formed(&env, "Topology.Spin.QuadraticForm");
}

// ================================================================
// Universe polymorphism tests (Issue #1538, acceptance criteria #2)
//
// Verify key topology constants type-check with Level::param() universes
// (not just Level::zero()), confirming universe polymorphism is well-formed.
// ================================================================

/// Helper: verify a topology constant type-checks with Level::param() universes.
fn assert_topology_polymorphic_type_well_formed(env: &Environment, name: &str) {
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    let n = Name::from_string(name);
    let ci = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name}: constant not found in env"));
    let levels: Vec<Level> = ci
        .level_params
        .iter()
        .map(|p| Level::param(p.clone()))
        .collect();
    let expr = Expr::const_(n, levels);
    let _ = tc
        .infer_type(&expr)
        .unwrap_or_else(|e| panic!("{name}: tc.infer_type with param levels failed: {e}"));
}

#[test]
fn test_topology_morse_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_topology_morse().unwrap();
    assert_topology_polymorphic_type_well_formed(&env, "Topology.Morse.MorseFunction");
    assert_topology_polymorphic_type_well_formed(&env, "Topology.Morse.CriticalPoint");
}

#[test]
fn test_topology_ktheory_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_topology_ktheory().unwrap();
    assert_topology_polymorphic_type_well_formed(&env, "Topology.KTheory.K");
}

#[test]
fn test_topology_cobordism_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_topology_cobordism().unwrap();
    assert_topology_polymorphic_type_well_formed(&env, "Topology.Cobordism.Manifold");
}

#[test]
fn test_topology_symplectic_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_topology_symplectic().unwrap();
    assert_topology_polymorphic_type_well_formed(&env, "Topology.Symplectic.SymplecticForm");
}
