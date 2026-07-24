// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for C009: CROWN exponentially tighter than IBP
//!
//! Validates that the C009 formalization registers all declaration groups:
//! - 3 Definitions (type constructor, configuration values)
//! - 7 Opaques (data objects, computed functions)
//! - 3 hypothesis-wrapped Theorems (IBP wrapping)
//! - 10 sorry-inhabited Opaques (CROWN correlation, exponential gap,
//!   depth scaling, summary conjecture)
//!
//! Part of #3371.

use clean_kernel::{Environment, Name};

#[test]
fn test_c009_init_succeeds() {
    let mut env = Environment::new();
    env.init_nn_verification_c009()
        .expect("C009 init should succeed");
}

#[test]
fn test_c009_init_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();
    let count_after_first = env.num_constants();

    env.init_nn_verification_c009().unwrap();
    assert_eq!(
        env.num_constants(),
        count_after_first,
        "second init should not add duplicate declarations"
    );
}

#[test]
fn test_c009_definitions_present() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    // 3 Definitions: type constructor and configuration values
    for name in &[
        "NNVerification.C009ReLUNetwork",
        "NNVerification.c009_depth",
        "NNVerification.c009_contraction_factor",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing Definition: {name}"
        );
    }
}

#[test]
fn test_c009_opaques_present() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    // 7 Opaques: data objects and computed functions
    for name in &[
        "NNVerification.c009_input_radius",
        "NNVerification.c009_weight_matrices",
        "NNVerification.c009_relu_relaxation_slopes",
        "NNVerification.c009_effective_crown_matrix",
        "NNVerification.c009_ibp_width",
        "NNVerification.c009_crown_width",
        "NNVerification.c009_crown_ibp_ratio",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing Opaque: {name}"
        );
    }
}

#[test]
fn test_c009_ibp_wrapping_theorems_present() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    for name in &[
        "NNVerification.ibp_wrapping_single_layer",
        "NNVerification.ibp_wrapping_compounds",
        "NNVerification.ibp_wrapping_correlation_loss",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing IBP wrapping theorem: {name}"
        );
    }
}

#[test]
fn test_c009_crown_correlation_axioms_present() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    for name in &[
        "NNVerification.crown_backsubstitution",
        "NNVerification.crown_combined_matrix",
        "NNVerification.crown_correlation_retained",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing CROWN correlation opaque: {name}"
        );
    }
}

#[test]
fn test_c009_exponential_gap_axioms_present() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    for name in &[
        "NNVerification.norm_product_vs_product_norm",
        "NNVerification.crown_uses_product",
        "NNVerification.ibp_uses_product_of_norms",
        "NNVerification.crown_ibp_ratio_exponential",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing exponential gap opaque: {name}"
        );
    }
}

#[test]
fn test_c009_depth_scaling_axioms_present() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    for name in &[
        "NNVerification.ratio_monotone_depth",
        "NNVerification.ratio_limit_zero",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing depth scaling opaque: {name}"
        );
    }
}

#[test]
fn test_c009_summary_conjecture_present() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    assert!(
        env.get_const(&Name::from_string(
            "NNVerification.c009_exponentially_tighter_than_ibp"
        ))
        .is_some(),
        "missing C009 summary conjecture"
    );
}

#[test]
fn test_c009_total_declaration_count() {
    // 3 definitions + 7 data opaques + 3 theorems + 10 sorry opaques = 23
    // C009-specific declarations.
    let mut env = Environment::new();
    let count_before = env.num_constants();
    env.init_nn_verification_c009().unwrap();
    let count_after = env.num_constants();

    let c009_decls = count_after - count_before;
    // C009 adds exactly 23 declarations (deps may add more)
    assert!(
        c009_decls >= 23,
        "expected at least 23 C009-specific declarations, got {c009_decls}"
    );
}

#[test]
fn test_c009_all_declarations_exhaustive() {
    let mut env = Environment::new();
    env.init_nn_verification_c009().unwrap();

    let all_c009_names = [
        // Definitions (3)
        "NNVerification.C009ReLUNetwork",
        "NNVerification.c009_depth",
        "NNVerification.c009_contraction_factor",
        // Opaques (7)
        "NNVerification.c009_input_radius",
        "NNVerification.c009_weight_matrices",
        "NNVerification.c009_relu_relaxation_slopes",
        "NNVerification.c009_effective_crown_matrix",
        "NNVerification.c009_ibp_width",
        "NNVerification.c009_crown_width",
        "NNVerification.c009_crown_ibp_ratio",
        // IBP Wrapping theorems (3)
        "NNVerification.ibp_wrapping_single_layer",
        "NNVerification.ibp_wrapping_compounds",
        "NNVerification.ibp_wrapping_correlation_loss",
        // CROWN Correlation opaques (3)
        "NNVerification.crown_backsubstitution",
        "NNVerification.crown_combined_matrix",
        "NNVerification.crown_correlation_retained",
        // Exponential Gap opaques (4)
        "NNVerification.norm_product_vs_product_norm",
        "NNVerification.crown_uses_product",
        "NNVerification.ibp_uses_product_of_norms",
        "NNVerification.crown_ibp_ratio_exponential",
        // Depth Scaling opaques (2)
        "NNVerification.ratio_monotone_depth",
        "NNVerification.ratio_limit_zero",
        // Summary conjecture (1)
        "NNVerification.c009_exponentially_tighter_than_ibp",
    ];

    for name in &all_c009_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing C009 declaration: {name}"
        );
    }
    assert_eq!(
        all_c009_names.len(),
        23,
        "expected 23 total C009 declarations: 3 def + 17 opaque + 3 theorem"
    );
}
