// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Boolean Fourier analysis (S41, S42).

use super::fourier::*;

// =========================================================================
// chi (character function)
// =========================================================================

#[test]
fn test_chi_empty_subset_always_one() {
    for x in 0..8u32 {
        assert_eq!(chi(0, x), 1.0, "chi(empty, {x}) should be 1");
    }
}

#[test]
fn test_chi_singleton_matches_variable() {
    // chi({0}, x) = (-1)^{x_0}
    assert_eq!(chi(1, 0b000), 1.0);
    assert_eq!(chi(1, 0b001), -1.0);
    assert_eq!(chi(1, 0b010), 1.0);
    assert_eq!(chi(1, 0b011), -1.0);
}

#[test]
fn test_chi_pair_product() {
    // chi({0,1}, x) = x_0 * x_1 = (-1)^{b_0 + b_1}
    assert_eq!(chi(0b11, 0b00), 1.0);
    assert_eq!(chi(0b11, 0b01), -1.0);
    assert_eq!(chi(0b11, 0b10), -1.0);
    assert_eq!(chi(0b11, 0b11), 1.0);
}

#[test]
fn test_chi_full_set_is_parity() {
    for x in 0..8u32 {
        let expected = if (x.count_ones()) % 2 == 0 { 1.0 } else { -1.0 };
        assert_eq!(chi(0b111, x), expected, "chi(all3, {x})");
    }
}

// =========================================================================
// Dictator
// =========================================================================

#[test]
fn test_dictator_fourier_only_singleton() {
    let f = BooleanFunction::dictator(0, 3).expect("valid dictator");
    let coeffs = compute_all_fourier(&f).expect("fourier ok");
    assert!((coeffs[0b001] - 1.0).abs() < 1e-12, "f_hat({{0}}) = 1");
    for (s, c) in coeffs.iter().enumerate() {
        if s != 0b001 {
            assert!(c.abs() < 1e-12, "f_hat({s:#05b}) should be 0, got {c}");
        }
    }
}

#[test]
fn test_dictator_var1_fourier() {
    let f = BooleanFunction::dictator(1, 3).expect("valid");
    let coeffs = compute_all_fourier(&f).expect("ok");
    assert!((coeffs[0b010] - 1.0).abs() < 1e-12);
    for (s, c) in coeffs.iter().enumerate() {
        if s != 0b010 {
            assert!(c.abs() < 1e-12, "s={s}: {c}");
        }
    }
}

#[test]
fn test_dictator_var2_fourier() {
    let f = BooleanFunction::dictator(2, 4).expect("valid");
    let coeffs = compute_all_fourier(&f).expect("ok");
    assert!((coeffs[0b0100] - 1.0).abs() < 1e-12);
}

// =========================================================================
// Parity
// =========================================================================

#[test]
fn test_parity_fourier_only_full_set() {
    let f = BooleanFunction::parity(3).expect("valid");
    let coeffs = compute_all_fourier(&f).expect("ok");
    assert!((coeffs[0b111] - 1.0).abs() < 1e-12, "f_hat([3]) = 1");
    for (s, c) in coeffs.iter().enumerate() {
        if s != 0b111 {
            assert!(c.abs() < 1e-12, "s={s:#05b}: {c}");
        }
    }
}

#[test]
fn test_parity_2vars_fourier() {
    let f = BooleanFunction::parity(2).expect("valid");
    let coeffs = compute_all_fourier(&f).expect("ok");
    assert!((coeffs[0b11] - 1.0).abs() < 1e-12);
    assert!(coeffs[0b00].abs() < 1e-12);
    assert!(coeffs[0b01].abs() < 1e-12);
    assert!(coeffs[0b10].abs() < 1e-12);
}

#[test]
fn test_parity_1var_is_dictator() {
    let f = BooleanFunction::parity(1).expect("valid");
    let d = BooleanFunction::dictator(0, 1).expect("valid");
    assert_eq!(f.values(), d.values());
}

// =========================================================================
// Majority (n=3) -- analytical Fourier spectrum
// =========================================================================

#[test]
fn test_majority_3_fourier_analytical() {
    // MAJ_3 Fourier coefficients (O'Donnell Ch.1):
    //   f_hat(empty) = 0
    //   f_hat({i}) = 1/2 for each i
    //   f_hat({i,j}) = 0 for each pair
    //   f_hat({0,1,2}) = -1/2
    let f = BooleanFunction::majority(3).expect("valid");
    let coeffs = compute_all_fourier(&f).expect("ok");

    assert!(coeffs[0b000].abs() < 1e-12, "f_hat(empty) = 0");
    assert!((coeffs[0b001] - 0.5).abs() < 1e-12, "f_hat({{0}}) = 1/2");
    assert!((coeffs[0b010] - 0.5).abs() < 1e-12, "f_hat({{1}}) = 1/2");
    assert!((coeffs[0b100] - 0.5).abs() < 1e-12, "f_hat({{2}}) = 1/2");
    assert!(coeffs[0b011].abs() < 1e-12, "f_hat({{0,1}}) = 0");
    assert!(coeffs[0b101].abs() < 1e-12, "f_hat({{0,2}}) = 0");
    assert!(coeffs[0b110].abs() < 1e-12, "f_hat({{1,2}}) = 0");
    assert!(
        (coeffs[0b111] - (-0.5)).abs() < 1e-12,
        "f_hat({{0,1,2}}) = -1/2"
    );
}

#[test]
fn test_majority_values_spot_check() {
    let f = BooleanFunction::majority(3).expect("valid");
    let v = f.values();
    assert_eq!(v[0b000], 1.0); // all +1 => sum=3 => +1
    assert_eq!(v[0b001], 1.0); // var0=-1, sum=1 => +1
    assert_eq!(v[0b011], -1.0); // var0,1=-1 => sum=-1 => -1
    assert_eq!(v[0b111], -1.0); // all -1 => sum=-3 => -1
}

// =========================================================================
// Parseval identity (S41)
// =========================================================================

#[test]
fn test_parseval_dictator_n3() {
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    verify_parseval(&f).expect("Parseval should hold for dictator");
}

#[test]
fn test_parseval_dictator_all_vars_n5() {
    for n in 1..=5 {
        for i in 0..n {
            let f = BooleanFunction::dictator(i, n).expect("valid");
            verify_parseval(&f).expect("Parseval holds");
        }
    }
}

#[test]
fn test_parseval_parity_sweep() {
    for n in 1..=6 {
        let f = BooleanFunction::parity(n).expect("valid");
        verify_parseval(&f).expect("Parseval holds for parity");
    }
}

#[test]
fn test_parseval_majority_odd() {
    for &n in &[1, 3, 5, 7] {
        let f = BooleanFunction::majority(n).expect("valid");
        verify_parseval(&f).expect("Parseval holds for majority");
    }
}

#[test]
fn test_parseval_constant_plus() {
    let f = BooleanFunction::constant(1.0, 3).expect("valid");
    verify_parseval(&f).expect("Parseval holds for constant 1");
}

#[test]
fn test_parseval_constant_minus() {
    let f = BooleanFunction::constant(-1.0, 3).expect("valid");
    verify_parseval(&f).expect("Parseval holds for constant -1");
}

#[test]
fn test_parseval_and2() {
    let f = BooleanFunction::and2(3).expect("valid");
    verify_parseval(&f).expect("Parseval holds for AND2");
}

#[test]
fn test_parseval_or2() {
    let f = BooleanFunction::or2(3).expect("valid");
    verify_parseval(&f).expect("Parseval holds for OR2");
}

#[test]
fn test_parseval_custom_truth_table() {
    let f = BooleanFunction::from_truth_table(&[1.0, -1.0, -1.0, 1.0]).expect("valid");
    verify_parseval(&f).expect("Parseval holds for custom");
}

// =========================================================================
// Influence (S42)
// =========================================================================

#[test]
fn test_influence_dictator_own_variable() {
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    let inf0 = compute_influence(&f, 0).expect("ok");
    assert!((inf0 - 1.0).abs() < 1e-12, "Inf_0(dict_0) = 1");
    let inf1 = compute_influence(&f, 1).expect("ok");
    assert!(inf1.abs() < 1e-12, "Inf_1(dict_0) = 0");
    let inf2 = compute_influence(&f, 2).expect("ok");
    assert!(inf2.abs() < 1e-12, "Inf_2(dict_0) = 0");
}

#[test]
fn test_influence_parity_all_one() {
    let f = BooleanFunction::parity(3).expect("valid");
    for i in 0..3 {
        let inf = compute_influence(&f, i).expect("ok");
        assert!((inf - 1.0).abs() < 1e-12, "Inf_{i}(parity) = 1");
    }
}

#[test]
fn test_influence_constant_zero() {
    let f = BooleanFunction::constant(1.0, 3).expect("valid");
    for i in 0..3 {
        let inf = compute_influence(&f, i).expect("ok");
        assert!(inf.abs() < 1e-12, "constant has zero influence");
    }
}

#[test]
fn test_influence_majority_3_symmetric() {
    let f = BooleanFunction::majority(3).expect("valid");
    for i in 0..3 {
        let inf = compute_influence(&f, i).expect("ok");
        assert!((inf - 0.5).abs() < 1e-12, "Inf_{i}(MAJ_3) = 1/2");
    }
}

// =========================================================================
// Influence-Fourier identity (S42)
// =========================================================================

#[test]
fn test_influence_fourier_dictator() {
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    for i in 0..3 {
        verify_influence_fourier(&f, i).expect("influence-Fourier identity holds");
    }
}

#[test]
fn test_influence_fourier_parity() {
    let f = BooleanFunction::parity(4).expect("valid");
    for i in 0..4 {
        verify_influence_fourier(&f, i).expect("identity holds for parity");
    }
}

#[test]
fn test_influence_fourier_majority() {
    let f = BooleanFunction::majority(3).expect("valid");
    for i in 0..3 {
        verify_influence_fourier(&f, i).expect("identity holds for majority");
    }
}

#[test]
fn test_influence_fourier_and2() {
    let f = BooleanFunction::and2(3).expect("valid");
    for i in 0..3 {
        verify_influence_fourier(&f, i).expect("identity holds for AND2");
    }
}

#[test]
fn test_influence_fourier_or2() {
    let f = BooleanFunction::or2(3).expect("valid");
    for i in 0..3 {
        verify_influence_fourier(&f, i).expect("identity holds for OR2");
    }
}

#[test]
fn test_influence_fourier_all_constructors_n4() {
    let functions: Vec<BooleanFunction> = vec![
        BooleanFunction::dictator(0, 4).expect("ok"),
        BooleanFunction::dictator(3, 4).expect("ok"),
        BooleanFunction::parity(4).expect("ok"),
        BooleanFunction::constant(1.0, 4).expect("ok"),
        BooleanFunction::constant(-1.0, 4).expect("ok"),
        BooleanFunction::and2(4).expect("ok"),
        BooleanFunction::or2(4).expect("ok"),
    ];
    for f in &functions {
        for i in 0..4 {
            verify_influence_fourier(f, i).expect("identity holds");
        }
    }
}

// =========================================================================
// Total influence
// =========================================================================

#[test]
fn test_total_influence_dictator() {
    let f = BooleanFunction::dictator(0, 4).expect("valid");
    let ti = total_influence(&f).expect("ok");
    assert!((ti - 1.0).abs() < 1e-12);
}

#[test]
fn test_total_influence_parity() {
    let f = BooleanFunction::parity(5).expect("valid");
    let ti = total_influence(&f).expect("ok");
    assert!((ti - 5.0).abs() < 1e-12);
}

#[test]
fn test_total_influence_constant() {
    let f = BooleanFunction::constant(1.0, 4).expect("valid");
    let ti = total_influence(&f).expect("ok");
    assert!(ti.abs() < 1e-12);
}

#[test]
fn test_total_influence_majority_3() {
    // I(MAJ_3) = 3 * (1/2) = 3/2 by symmetry
    let f = BooleanFunction::majority(3).expect("valid");
    let ti = total_influence(&f).expect("ok");
    assert!((ti - 1.5).abs() < 1e-12);
}

// =========================================================================
// Error cases
// =========================================================================

#[test]
fn test_too_many_variables() {
    assert!(BooleanFunction::dictator(0, 17).is_err());
    assert!(BooleanFunction::parity(17).is_err());
    assert!(BooleanFunction::majority(17).is_err());
}

#[test]
fn test_variable_out_of_range() {
    assert!(BooleanFunction::dictator(3, 3).is_err());
    let f = BooleanFunction::parity(3).expect("valid");
    assert!(compute_influence(&f, 3).is_err());
    assert!(verify_influence_fourier(&f, 5).is_err());
}

#[test]
fn test_bad_table_length() {
    assert!(BooleanFunction::from_truth_table(&[1.0, -1.0, 1.0]).is_err());
    assert!(BooleanFunction::from_truth_table(&[]).is_err());
}

#[test]
fn test_subset_out_of_range() {
    let f = BooleanFunction::parity(2).expect("valid");
    assert!(fourier_coefficient(&f, 0b100).is_err());
}

// =========================================================================
// Proof status registry
// =========================================================================

#[test]
fn test_frontier_entries_registry() {
    let entries = super::all_entries();
    assert_eq!(entries.len(), 12);
    assert_eq!(entries[0].id, "S40");
    assert_eq!(entries[1].id, "S41");
    assert_eq!(entries[2].id, "S42");
    assert_eq!(entries[3].id, "S43");
    assert_eq!(entries[4].id, "S44");
    assert_eq!(entries[5].id, "S45");
    assert_eq!(entries[6].id, "S46");
    assert_eq!(entries[7].id, "S47");
    assert_eq!(entries[8].id, "S48");
    assert_eq!(entries[9].id, "S49");
    assert_eq!(entries[10].id, "S50");
    assert_eq!(entries[11].id, "S51");
    for entry in &entries {
        assert_eq!(entry.status, crate::spec::ProofStatus::DerivedPending,);
    }
}
