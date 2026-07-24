// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof complexity lower bounds module.

use super::lower_bounds::{
    lower_bounds_registry, php_tree_resolution_lower_bound, random_cnf_resolution_threshold,
    tseitin_resolution_lower_bound, verify_lower_bound_witness, width_space_tradeoff,
    ResolutionComplexity, PC05_PHP_LOWER_BOUND, PC06_TSEITIN_LOWER_BOUND,
};
use super::proof_complexity_registry;
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// PHP tree-resolution lower bound tests
// ---------------------------------------------------------------------------

#[test]
fn test_php_lower_bound_small_n() {
    // PHP(3,2): 2^(2/10) = 2^0.2 ~ 1.149
    let bound = php_tree_resolution_lower_bound(3, 2);
    assert!(
        bound > 1.0,
        "bound for PHP(3,2) should exceed 1.0, got {bound}"
    );
    assert!(
        bound < 2.0,
        "bound for PHP(3,2) should be < 2.0, got {bound}"
    );
}

#[test]
fn test_php_lower_bound_growth_rate() {
    // Bound should grow exponentially: larger holes => larger bound.
    let b5 = php_tree_resolution_lower_bound(6, 5);
    let b10 = php_tree_resolution_lower_bound(11, 10);
    let b20 = php_tree_resolution_lower_bound(21, 20);

    assert!(b10 > b5, "bound should grow: b10={b10} > b5={b5}");
    assert!(b20 > b10, "bound should grow: b20={b20} > b10={b10}");
    // Exponential: b20 should be much larger than b10
    assert!(
        b20 > b10 * 1.5,
        "exponential growth: b20={b20} should be >> b10={b10}"
    );
}

#[test]
fn test_php_lower_bound_trivial_case() {
    // pigeons <= holes: satisfiable, lower bound is 1.0.
    assert_eq!(php_tree_resolution_lower_bound(2, 3), 1.0);
    assert_eq!(php_tree_resolution_lower_bound(3, 3), 1.0);
}

#[test]
fn test_php_lower_bound_zero_holes() {
    assert_eq!(php_tree_resolution_lower_bound(5, 0), 1.0);
}

#[test]
fn test_php_lower_bound_zero_pigeons() {
    assert_eq!(php_tree_resolution_lower_bound(0, 5), 1.0);
}

#[test]
fn test_php_lower_bound_one_hole() {
    // PHP(2,1): 2^(1/10) ~ 1.0718
    let bound = php_tree_resolution_lower_bound(2, 1);
    assert!(bound > 1.0);
    assert!(bound < 1.1);
}

#[test]
fn test_php_lower_bound_known_value() {
    // PHP(11,10): 2^(10/10) = 2^1 = 2.0
    let bound = php_tree_resolution_lower_bound(11, 10);
    let expected = 2.0_f64;
    assert!(
        (bound - expected).abs() < 1e-10,
        "PHP(11,10): expected {expected}, got {bound}"
    );
}

// ---------------------------------------------------------------------------
// Tseitin resolution lower bound tests
// ---------------------------------------------------------------------------

#[test]
fn test_tseitin_lower_bound_basic() {
    // 10 vertices: 2^(10/10) = 2.0
    let bound = tseitin_resolution_lower_bound(10);
    assert!(
        (bound - 2.0).abs() < 1e-10,
        "Tseitin(10) expected 2.0, got {bound}"
    );
}

#[test]
fn test_tseitin_lower_bound_growth() {
    let b10 = tseitin_resolution_lower_bound(10);
    let b20 = tseitin_resolution_lower_bound(20);
    let b50 = tseitin_resolution_lower_bound(50);

    assert!(b20 > b10, "b20={b20} > b10={b10}");
    assert!(b50 > b20, "b50={b50} > b20={b20}");
}

#[test]
fn test_tseitin_lower_bound_degenerate() {
    assert_eq!(tseitin_resolution_lower_bound(0), 1.0);
    assert_eq!(tseitin_resolution_lower_bound(1), 1.0);
}

#[test]
fn test_tseitin_lower_bound_two_vertices() {
    // 2 vertices: 2^(2/10) = 2^0.2 ~ 1.149
    let bound = tseitin_resolution_lower_bound(2);
    assert!(bound > 1.0 && bound < 1.2);
}

// ---------------------------------------------------------------------------
// Random CNF resolution threshold tests
// ---------------------------------------------------------------------------

#[test]
fn test_random_cnf_below_threshold() {
    let result = random_cnf_resolution_threshold(100, 3.0);
    assert_eq!(result, ResolutionComplexity::Satisfiable);
}

#[test]
fn test_random_cnf_at_threshold() {
    let result = random_cnf_resolution_threshold(100, 4.5);
    assert_eq!(result, ResolutionComplexity::HardRefutable);
}

#[test]
fn test_random_cnf_above_threshold() {
    let result = random_cnf_resolution_threshold(100, 6.0);
    assert_eq!(result, ResolutionComplexity::EasyRefutable);
}

#[test]
fn test_random_cnf_exactly_at_threshold() {
    // 4.267 is the threshold; should be in the hard region.
    let result = random_cnf_resolution_threshold(100, 4.267);
    assert_eq!(result, ResolutionComplexity::HardRefutable);
}

#[test]
fn test_random_cnf_just_below_threshold() {
    let result = random_cnf_resolution_threshold(100, 4.266);
    assert_eq!(result, ResolutionComplexity::Satisfiable);
}

#[test]
fn test_random_cnf_zero_vars() {
    let result = random_cnf_resolution_threshold(0, 5.0);
    assert_eq!(result, ResolutionComplexity::Satisfiable);
}

#[test]
fn test_random_cnf_negative_ratio() {
    let result = random_cnf_resolution_threshold(100, -1.0);
    assert_eq!(result, ResolutionComplexity::Satisfiable);
}

#[test]
fn test_random_cnf_zero_ratio() {
    let result = random_cnf_resolution_threshold(100, 0.0);
    assert_eq!(result, ResolutionComplexity::Satisfiable);
}

#[test]
fn test_random_cnf_upper_hard_boundary() {
    // 4.267 + 1.0 = 5.267 should still be HardRefutable
    let result = random_cnf_resolution_threshold(100, 5.267);
    assert_eq!(result, ResolutionComplexity::HardRefutable);
}

#[test]
fn test_random_cnf_just_above_hard_region() {
    // 5.268 should be EasyRefutable
    let result = random_cnf_resolution_threshold(100, 5.268);
    assert_eq!(result, ResolutionComplexity::EasyRefutable);
}

// ---------------------------------------------------------------------------
// Witness verification tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_witness_valid() {
    // Proof size 100 with lower bound 50: valid
    assert!(verify_lower_bound_witness(10, 100, 50.0));
}

#[test]
fn test_verify_witness_exact_match() {
    // Proof size exactly matches lower bound
    assert!(verify_lower_bound_witness(10, 50, 50.0));
}

#[test]
fn test_verify_witness_invalid_too_short() {
    // Proof size 10 with lower bound 50: invalid
    assert!(!verify_lower_bound_witness(10, 10, 50.0));
}

#[test]
fn test_verify_witness_zero_formula() {
    // Trivial formula: always valid
    assert!(verify_lower_bound_witness(0, 0, 100.0));
}

#[test]
fn test_verify_witness_zero_bound() {
    // Vacuous bound: always valid
    assert!(verify_lower_bound_witness(10, 5, 0.0));
}

#[test]
fn test_verify_witness_negative_bound() {
    // Negative bound: vacuous, always valid
    assert!(verify_lower_bound_witness(10, 0, -1.0));
}

#[test]
fn test_verify_witness_zero_proof_size() {
    // Zero proof with positive bound: invalid
    assert!(!verify_lower_bound_witness(10, 0, 1.0));
}

// ---------------------------------------------------------------------------
// Width-space tradeoff tests
// ---------------------------------------------------------------------------

#[test]
fn test_width_space_satisfied() {
    // width=10, space=10, vars=100: 10*10 = 100 >= 100
    assert!(width_space_tradeoff(10, 10, 100));
}

#[test]
fn test_width_space_exceeded() {
    // width=20, space=10, vars=100: 200 >= 100
    assert!(width_space_tradeoff(20, 10, 100));
}

#[test]
fn test_width_space_violated() {
    // width=5, space=5, vars=100: 25 < 100
    assert!(!width_space_tradeoff(5, 5, 100));
}

#[test]
fn test_width_space_zero_vars() {
    // Trivial: always satisfied
    assert!(width_space_tradeoff(0, 0, 0));
}

#[test]
fn test_width_space_zero_width() {
    // width=0: product is 0, violates if vars > 0
    assert!(!width_space_tradeoff(0, 100, 1));
}

#[test]
fn test_width_space_zero_space() {
    // space=0: product is 0, violates if vars > 0
    assert!(!width_space_tradeoff(100, 0, 1));
}

#[test]
fn test_width_space_exact_boundary() {
    // width=5, space=20, vars=100: 100 >= 100
    assert!(width_space_tradeoff(5, 20, 100));
}

#[test]
fn test_width_space_large_values_no_overflow() {
    // Ensure saturating_mul prevents overflow
    assert!(width_space_tradeoff(usize::MAX, 2, usize::MAX));
}

// ---------------------------------------------------------------------------
// Registry and constant tests
// ---------------------------------------------------------------------------

#[test]
fn test_pc05_status() {
    assert_eq!(PC05_PHP_LOWER_BOUND, ProofStatus::DerivedPending);
}

#[test]
fn test_pc06_status() {
    assert_eq!(PC06_TSEITIN_LOWER_BOUND, ProofStatus::DerivedPending);
}

#[test]
fn test_lower_bounds_registry_count() {
    let entries = lower_bounds_registry();
    assert_eq!(entries.len(), 2);
}

#[test]
fn test_lower_bounds_registry_names() {
    let entries = lower_bounds_registry();
    let names: Vec<&str> = entries.iter().map(|(n, _)| *n).collect();
    assert!(names.contains(&"PC05_php_lower_bound"));
    assert!(names.contains(&"PC06_tseitin_lower_bound"));
}

#[test]
fn test_proof_complexity_registry_includes_lower_bounds() {
    let registry = proof_complexity_registry();
    let names: Vec<&str> = registry.iter().map(|(n, _)| *n).collect();
    assert!(
        names.contains(&"PC05_php_lower_bound"),
        "registry should contain PC05_php_lower_bound"
    );
    assert!(
        names.contains(&"PC06_tseitin_lower_bound"),
        "registry should contain PC06_tseitin_lower_bound"
    );
}

#[test]
fn test_proof_complexity_registry_updated_count() {
    // Original 6 entries + 2 from lower_bounds = 8
    assert_eq!(proof_complexity_registry().len(), 8);
}

// ---------------------------------------------------------------------------
// Resolution complexity enum tests
// ---------------------------------------------------------------------------

#[test]
fn test_resolution_complexity_debug() {
    let s = format!("{:?}", ResolutionComplexity::Satisfiable);
    assert_eq!(s, "Satisfiable");
    let h = format!("{:?}", ResolutionComplexity::HardRefutable);
    assert_eq!(h, "HardRefutable");
    let e = format!("{:?}", ResolutionComplexity::EasyRefutable);
    assert_eq!(e, "EasyRefutable");
}

#[test]
fn test_resolution_complexity_clone_eq() {
    let a = ResolutionComplexity::HardRefutable;
    let b = a;
    assert_eq!(a, b);
}

// ---------------------------------------------------------------------------
// Lower bound certificate infrastructure tests
// ---------------------------------------------------------------------------

use super::lower_bounds::{
    check_lower_bound_witness, is_hard_for, known_lower_bounds, suggest_proof_system,
    AsymptoticBound, FormulaFamily, FormulaStats, LowerBoundCertificate, ProofSystemClass,
};

// --- known_lower_bounds registry tests ---

#[test]
fn test_known_lower_bounds_registry_not_empty() {
    let bounds = known_lower_bounds();
    assert!(
        bounds.len() >= 8,
        "expected at least 8 known lower bounds, got {}",
        bounds.len()
    );
}

#[test]
fn test_known_lower_bounds_includes_haken() {
    let bounds = known_lower_bounds();
    let haken = bounds.iter().find(|c| {
        c.family == FormulaFamily::PHP
            && c.proof_system == ProofSystemClass::Resolution
            && c.year == 1985
    });
    assert!(haken.is_some(), "should include Haken 1985 PHP lower bound");
}

#[test]
fn test_known_lower_bounds_includes_razborov_pc() {
    let bounds = known_lower_bounds();
    let razborov = bounds.iter().find(|c| {
        c.family == FormulaFamily::PHP && c.proof_system == ProofSystemClass::PolynomialCalculus
    });
    assert!(
        razborov.is_some(),
        "should include Razborov 1998 PC degree lower bound for PHP"
    );
}

#[test]
fn test_known_lower_bounds_includes_pudlak_cp() {
    let bounds = known_lower_bounds();
    let pudlak = bounds.iter().find(|c| {
        c.family == FormulaFamily::Clique && c.proof_system == ProofSystemClass::CuttingPlanes
    });
    assert!(
        pudlak.is_some(),
        "should include Pudlak 1997 clique-coloring CP lower bound"
    );
}

#[test]
fn test_known_lower_bounds_all_have_references() {
    for cert in known_lower_bounds() {
        assert!(
            !cert.reference.is_empty(),
            "certificate for {:?}/{:?} missing reference",
            cert.family,
            cert.proof_system
        );
        assert!(
            cert.year >= 1968 && cert.year <= 2026,
            "year {} out of range for {:?}",
            cert.year,
            cert.family
        );
    }
}

// --- check_lower_bound_witness tests ---

#[test]
fn test_check_lower_bound_witness_php_n10() {
    let haken = LowerBoundCertificate {
        family: FormulaFamily::PHP,
        proof_system: ProofSystemClass::Resolution,
        bound: AsymptoticBound::Exponential { base: 2.0 },
        reference: "Haken (1985)",
        year: 1985,
    };
    let bound = check_lower_bound_witness(&haken, 10);
    // 2^10 = 1024
    assert_eq!(bound, 1024);
}

#[test]
fn test_check_lower_bound_witness_php_n20() {
    let haken = LowerBoundCertificate {
        family: FormulaFamily::PHP,
        proof_system: ProofSystemClass::Resolution,
        bound: AsymptoticBound::Exponential { base: 2.0 },
        reference: "Haken (1985)",
        year: 1985,
    };
    let bound = check_lower_bound_witness(&haken, 20);
    // 2^20 = 1_048_576
    assert_eq!(bound, 1_048_576);
}

#[test]
fn test_check_lower_bound_witness_php_n50() {
    let haken = LowerBoundCertificate {
        family: FormulaFamily::PHP,
        proof_system: ProofSystemClass::Resolution,
        bound: AsymptoticBound::Exponential { base: 2.0 },
        reference: "Haken (1985)",
        year: 1985,
    };
    let bound = check_lower_bound_witness(&haken, 50);
    // 2^50 = 1_125_899_906_842_624
    assert_eq!(bound, 1_125_899_906_842_624);
}

#[test]
fn test_check_lower_bound_witness_exponential_growth() {
    let cert = LowerBoundCertificate {
        family: FormulaFamily::Tseitin,
        proof_system: ProofSystemClass::Resolution,
        bound: AsymptoticBound::Exponential { base: 2.0 },
        reference: "test",
        year: 1999,
    };
    let b10 = check_lower_bound_witness(&cert, 10);
    let b20 = check_lower_bound_witness(&cert, 20);
    let b50 = check_lower_bound_witness(&cert, 50);
    assert!(b20 > b10, "b20={b20} > b10={b10}");
    assert!(b50 > b20, "b50={b50} > b20={b20}");
}

#[test]
fn test_check_lower_bound_witness_polynomial() {
    let cert = LowerBoundCertificate {
        family: FormulaFamily::PHP,
        proof_system: ProofSystemClass::PolynomialCalculus,
        bound: AsymptoticBound::Polynomial { degree: 1 },
        reference: "test",
        year: 1998,
    };
    // n^1 = n
    assert_eq!(check_lower_bound_witness(&cert, 10), 10);
    assert_eq!(check_lower_bound_witness(&cert, 100), 100);
}

#[test]
fn test_check_lower_bound_witness_polynomial_degree_3() {
    let cert = LowerBoundCertificate {
        family: FormulaFamily::Clique,
        proof_system: ProofSystemClass::CuttingPlanes,
        bound: AsymptoticBound::Polynomial { degree: 3 },
        reference: "test",
        year: 2000,
    };
    // 10^3 = 1000
    assert_eq!(check_lower_bound_witness(&cert, 10), 1000);
}

#[test]
fn test_check_lower_bound_witness_quasipolynomial() {
    let cert = LowerBoundCertificate {
        family: FormulaFamily::Clique,
        proof_system: ProofSystemClass::CuttingPlanes,
        bound: AsymptoticBound::Quasipolynomial,
        reference: "test",
        year: 2000,
    };
    // n=16: log2(16)=4, 4^2=16, 2^16 = 65536
    assert_eq!(check_lower_bound_witness(&cert, 16), 65536);
}

#[test]
fn test_check_lower_bound_witness_zero_size() {
    let cert = LowerBoundCertificate {
        family: FormulaFamily::PHP,
        proof_system: ProofSystemClass::Resolution,
        bound: AsymptoticBound::Exponential { base: 2.0 },
        reference: "test",
        year: 1985,
    };
    assert_eq!(check_lower_bound_witness(&cert, 0), 1);
}

#[test]
fn test_check_lower_bound_witness_saturates_at_u64_max() {
    let cert = LowerBoundCertificate {
        family: FormulaFamily::PHP,
        proof_system: ProofSystemClass::Resolution,
        bound: AsymptoticBound::Exponential { base: 2.0 },
        reference: "test",
        year: 1985,
    };
    // 2^200 overflows u64
    assert_eq!(check_lower_bound_witness(&cert, 200), u64::MAX);
}

// --- suggest_proof_system tests ---

#[test]
fn test_suggest_proof_system_cardinality() {
    let stats = FormulaStats {
        num_vars: 100,
        num_clauses: 500,
        max_clause_width: 10,
        has_cardinality_structure: true,
        has_xor_structure: false,
        is_random: false,
    };
    let suggestions = suggest_proof_system(&stats);
    let systems: Vec<_> = suggestions.iter().map(|(s, _)| *s).collect();
    assert!(
        systems.contains(&ProofSystemClass::CuttingPlanes),
        "should recommend CP for cardinality structure"
    );
}

#[test]
fn test_suggest_proof_system_xor() {
    let stats = FormulaStats {
        num_vars: 100,
        num_clauses: 300,
        max_clause_width: 3,
        has_cardinality_structure: false,
        has_xor_structure: true,
        is_random: false,
    };
    let suggestions = suggest_proof_system(&stats);
    let systems: Vec<_> = suggestions.iter().map(|(s, _)| *s).collect();
    assert!(
        systems.contains(&ProofSystemClass::ExtendedFrege),
        "should recommend Extended Frege for XOR structure"
    );
}

#[test]
fn test_suggest_proof_system_random() {
    let stats = FormulaStats {
        num_vars: 200,
        num_clauses: 900,
        max_clause_width: 3,
        has_cardinality_structure: false,
        has_xor_structure: false,
        is_random: true,
    };
    let suggestions = suggest_proof_system(&stats);
    let systems: Vec<_> = suggestions.iter().map(|(s, _)| *s).collect();
    assert!(
        systems.contains(&ProofSystemClass::Frege),
        "should recommend Frege for random instances"
    );
    assert!(
        systems.contains(&ProofSystemClass::ExtendedFrege),
        "should recommend Extended Frege for random instances"
    );
}

#[test]
fn test_suggest_proof_system_always_includes_resolution() {
    let stats = FormulaStats {
        num_vars: 50,
        num_clauses: 100,
        max_clause_width: 5,
        has_cardinality_structure: false,
        has_xor_structure: false,
        is_random: false,
    };
    let suggestions = suggest_proof_system(&stats);
    let systems: Vec<_> = suggestions.iter().map(|(s, _)| *s).collect();
    assert!(
        systems.contains(&ProofSystemClass::Resolution),
        "should always include Resolution baseline"
    );
}

#[test]
fn test_suggest_proof_system_avoids_known_hard() {
    let stats = FormulaStats {
        num_vars: 100,
        num_clauses: 500,
        max_clause_width: 10,
        has_cardinality_structure: true,
        has_xor_structure: false,
        is_random: false,
    };
    let suggestions = suggest_proof_system(&stats);
    // First recommendation should NOT be Resolution for cardinality formulas
    assert_eq!(
        suggestions[0].0,
        ProofSystemClass::CuttingPlanes,
        "first suggestion for cardinality structure should be CP"
    );
}

// --- is_hard_for tests ---

#[test]
fn test_is_hard_for_php_resolution() {
    let cert = is_hard_for(&FormulaFamily::PHP, &ProofSystemClass::Resolution);
    assert!(cert.is_some(), "PHP should be known-hard for Resolution");
    let cert = cert.unwrap();
    assert!(matches!(cert.bound, AsymptoticBound::Exponential { .. }));
    assert_eq!(cert.year, 1985);
}

#[test]
fn test_is_hard_for_tseitin_resolution() {
    let cert = is_hard_for(&FormulaFamily::Tseitin, &ProofSystemClass::Resolution);
    assert!(
        cert.is_some(),
        "Tseitin should be known-hard for Resolution"
    );
}

#[test]
fn test_is_hard_for_tseitin_tree_resolution() {
    let cert = is_hard_for(&FormulaFamily::Tseitin, &ProofSystemClass::TreeResolution);
    assert!(
        cert.is_some(),
        "Tseitin should be known-hard for Tree Resolution"
    );
}

#[test]
fn test_is_hard_for_clique_cp() {
    let cert = is_hard_for(&FormulaFamily::Clique, &ProofSystemClass::CuttingPlanes);
    assert!(
        cert.is_some(),
        "Clique-coloring should be known-hard for Cutting Planes"
    );
}

#[test]
fn test_is_hard_for_php_not_hard_for_cp() {
    // PHP has polynomial CP proofs, so it should NOT be exponentially hard for CP.
    let cert = is_hard_for(&FormulaFamily::PHP, &ProofSystemClass::CuttingPlanes);
    assert!(
        cert.is_none(),
        "PHP should NOT be known-hard for Cutting Planes (has poly proofs)"
    );
}

#[test]
fn test_is_hard_for_parity_resolution() {
    let cert = is_hard_for(&FormulaFamily::Parity, &ProofSystemClass::Resolution);
    assert!(cert.is_some(), "Parity should be known-hard for Resolution");
}

#[test]
fn test_is_hard_for_ordering_resolution() {
    let cert = is_hard_for(&FormulaFamily::Ordering, &ProofSystemClass::Resolution);
    assert!(
        cert.is_some(),
        "Ordering principle should be known-hard for Resolution"
    );
}

#[test]
fn test_is_hard_for_random_ksat_resolution() {
    let cert = is_hard_for(&FormulaFamily::RandomKSat, &ProofSystemClass::Resolution);
    assert!(
        cert.is_some(),
        "Random k-SAT should be known-hard for Resolution"
    );
}

#[test]
fn test_is_hard_for_unknown_combination() {
    // Random k-SAT is not known to be hard for Extended Frege.
    let cert = is_hard_for(&FormulaFamily::RandomKSat, &ProofSystemClass::ExtendedFrege);
    assert!(
        cert.is_none(),
        "Random k-SAT should not be known-hard for Extended Frege"
    );
}

// --- FormulaFamily and ProofSystemClass enum tests ---

#[test]
fn test_formula_family_copy_eq() {
    let a = FormulaFamily::PHP;
    let b = a;
    assert_eq!(a, b);
}

#[test]
fn test_proof_system_class_debug() {
    let s = format!("{:?}", ProofSystemClass::PolynomialCalculus);
    assert_eq!(s, "PolynomialCalculus");
}

#[test]
fn test_asymptotic_bound_debug() {
    let exp = AsymptoticBound::Exponential { base: 2.0 };
    let s = format!("{:?}", exp);
    assert!(s.contains("Exponential"));
    assert!(s.contains("2.0"));
}

// --- Tseitin lower bound with expansion constant ---

#[test]
fn test_tseitin_lower_bound_with_expansion_constant() {
    // The certificate for Tseitin uses base 2.0 exponential.
    // For expansion constant encoded in the graph size:
    // 20 vertices on expander with constant degree -> 2^20 = 1_048_576
    let cert = is_hard_for(&FormulaFamily::Tseitin, &ProofSystemClass::Resolution)
        .expect("Tseitin known-hard for Resolution");
    let bound = check_lower_bound_witness(&cert, 20);
    assert_eq!(bound, 1_048_576, "2^20 for 20-vertex expander graph");
}
