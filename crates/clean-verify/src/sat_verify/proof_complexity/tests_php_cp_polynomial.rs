// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end verification tests for the polynomial CP proof of PHP.
//!
//! Constructs the concrete cutting planes refutation of PHP(n+1, n) for
//! various n, verifies each proof, and asserts:
//!
//! 1. **Correctness**: The proof is a valid CP refutation (derives 0 >= c, c > 0).
//! 2. **Polynomial bound**: The total proof size (axioms + derived steps) is O(n).
//!    Since O(n) < O(n^3), this is a stronger result than the classic O(n^3)
//!    bound from Cook, Coullard & Turan (1987).
//! 3. **Exponential separation**: For large n, the Haken lower bound
//!    2^{n/20} exceeds the CP proof size, witnessing the exponential gap.
//!
//! This module provides the computational evidence backing the kernel-level
//! formalization in `clean-kernel::env::pb_pigeonhole_length_bound`.
//!
//! Part of #3164.

use super::cutting_planes::CpInequality;
use super::encodings::{encode_php, encode_php_cp, php_num_clauses};
use super::separations::{
    php_cp_size_upper_bound, php_resolution_size_lower_bound, php_separation_witness,
    ProofSizeBound,
};
use super::separations_cp::{cp_proof_of_php, php_cp_axioms, verify_cp_derivation};

// ===== Correctness: CP proofs verify for PHP(n+1, n) =====

#[test]
fn test_php_cp_proof_verifies_n1_through_n20() {
    for n in 1..=20 {
        let axioms = php_cp_axioms(n);
        let steps = cp_proof_of_php(n);
        assert!(
            verify_cp_derivation(&axioms, &steps),
            "CP proof of PHP({},{}) must verify",
            n + 1,
            n
        );
    }
}

#[test]
fn test_php_cp_proof_verifies_n50() {
    let axioms = php_cp_axioms(50);
    let steps = cp_proof_of_php(50);
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_php_cp_proof_verifies_n100() {
    let axioms = php_cp_axioms(100);
    let steps = cp_proof_of_php(100);
    assert!(verify_cp_derivation(&axioms, &steps));
}

// ===== Step count is exactly 2*n =====

#[test]
fn test_php_cp_step_count_formula() {
    for n in 1..=50 {
        let steps = cp_proof_of_php(n);
        assert_eq!(
            steps.len(),
            2 * n,
            "PHP({},{}) should have exactly 2n = {} steps, got {}",
            n + 1,
            n,
            2 * n,
            steps.len()
        );
    }
}

// ===== Axiom count is exactly 2*n + 1 =====

#[test]
fn test_php_cp_axiom_count_formula() {
    for n in 1..=50 {
        let axioms = php_cp_axioms(n);
        assert_eq!(
            axioms.len(),
            2 * n + 1,
            "PHP({},{}) should have 2n+1 = {} axioms, got {}",
            n + 1,
            n,
            2 * n + 1,
            axioms.len()
        );
    }
}

// ===== Total proof size is 4*n + 1 (axioms + steps) =====

#[test]
fn test_php_cp_total_size_formula() {
    for n in 1..=50 {
        let axioms = php_cp_axioms(n);
        let steps = cp_proof_of_php(n);
        let total = axioms.len() + steps.len();
        assert_eq!(
            total,
            4 * n + 1,
            "PHP({},{}) total size should be 4n+1 = {}, got {}",
            n + 1,
            n,
            4 * n + 1,
            total
        );
    }
}

// ===== O(n^3) upper bound holds =====

#[test]
fn test_php_cp_total_size_bounded_by_cubic() {
    // The bound 4n+1 <= n^3 holds for n >= 5 (4*5+1=21 <= 125=5^3).
    // For n=1..4 the cubic bound is vacuous since the formula is small,
    // but the proof still has polynomial size.
    for n in 5..=100 {
        let axioms = php_cp_axioms(n);
        let steps = cp_proof_of_php(n);
        let total = axioms.len() + steps.len();
        let cubic = n * n * n;
        assert!(
            total <= cubic,
            "PHP({},{}) total size {} must be <= n^3 = {} (Cook et al. 1987)",
            n + 1,
            n,
            total,
            cubic
        );
    }
}

#[test]
fn test_php_cp_total_size_bounded_by_2n3_for_all_n() {
    // Using the classic 2*n^3 bound from Cook et al. (1987):
    // 4n+1 <= 2n^3 holds for all n >= 2.
    for n in 2..=100 {
        let axioms = php_cp_axioms(n);
        let steps = cp_proof_of_php(n);
        let total = axioms.len() + steps.len();
        let cubic = 2 * n * n * n;
        assert!(
            total <= cubic,
            "PHP({},{}) total size {} must be <= 2n^3 = {} (Cook et al. 1987)",
            n + 1,
            n,
            total,
            cubic
        );
    }
}

// ===== Steps are all additions (no division, multiplication, etc.) =====

#[test]
fn test_php_cp_proof_uses_only_additions() {
    use super::separations_cp::SepCpStep;
    for n in 1..=20 {
        for (i, step) in cp_proof_of_php(n).iter().enumerate() {
            match step {
                SepCpStep::Addition(_, _) => {}
                other => panic!(
                    "PHP({},{}) step {i} is {other:?}, expected Addition",
                    n + 1,
                    n
                ),
            }
        }
    }
}

// ===== Exponential separation witness =====

#[test]
fn test_php_exponential_separation_at_n1000() {
    let n = 1000;
    let haken_lower = php_resolution_size_lower_bound(n);
    let cp_total = 4 * n + 1;
    let cp_cubic = php_cp_size_upper_bound(n);
    // Haken: 2^{1000/20} = 2^50 ~ 1.13e15
    // CP cubic: 2 * 10^9 = 2e9
    // CP actual: 4001
    assert!(
        haken_lower > cp_total as f64,
        "Haken {haken_lower:.2e} must exceed actual CP size {cp_total}"
    );
    assert!(
        haken_lower > cp_cubic as f64,
        "Haken {haken_lower:.2e} must exceed CP cubic bound {cp_cubic}"
    );
}

#[test]
fn test_php_separation_crossover_point() {
    // Find the smallest n where Haken lower bound exceeds CP total size.
    // 2^{n/20} > 4n+1. Numerically, n=95 gives 2^{4.75} ~ 26.9 > 381 -- no.
    // n=200: 2^10 = 1024 > 801 -- yes.
    let mut crossover = None;
    for n in 1..=300 {
        let haken = php_resolution_size_lower_bound(n);
        let cp_total = (4 * n + 1) as f64;
        if haken > cp_total {
            crossover = Some(n);
            break;
        }
    }
    assert!(
        crossover.is_some(),
        "Exponential separation must occur for some n <= 300"
    );
    let n = crossover.expect("crossover exists");
    assert!(
        n <= 300,
        "crossover at n={n} should be within reasonable range"
    );
}

// ===== Proof size growth rate verification =====

#[test]
fn test_php_cp_size_growth_linear() {
    // Verify the proof size grows linearly (constant ratio per step).
    let sizes: Vec<(usize, usize)> = (1..=20)
        .map(|n| {
            let axioms = php_cp_axioms(n);
            let steps = cp_proof_of_php(n);
            (n, axioms.len() + steps.len())
        })
        .collect();

    for window in sizes.windows(2) {
        let (n1, s1) = window[0];
        let (n2, s2) = window[1];
        let diff = s2 - s1;
        // Each step from n to n+1 adds exactly 4 to total size.
        assert_eq!(
            diff, 4,
            "Size difference from n={n1} ({s1}) to n={n2} ({s2}) should be 4, got {diff}"
        );
    }
}

// ===== Resolution clause count grows quadratically, CP stays linear =====

#[test]
fn test_php_resolution_clauses_vs_cp_steps() {
    for n in 2..=20 {
        let (_, cnf_clauses) = encode_php(n);
        let cp_steps = cp_proof_of_php(n);
        // Resolution clause count = n+1 + C(n+1, 2)*n = n+1 + n*(n+1)/2 * n = Theta(n^3)
        // CP step count = 2n
        // So resolution input alone exceeds CP proof size for moderate n.
        let res_clause_count = cnf_clauses.len();
        let cp_step_count = cp_steps.len();
        if n >= 5 {
            assert!(
                res_clause_count > cp_step_count,
                "At n={n}, resolution clauses ({res_clause_count}) should exceed CP steps ({cp_step_count})"
            );
        }
    }
}

// ===== PHP encoding + CP encoding consistency =====

#[test]
fn test_php_cp_encoding_matches_cnf() {
    // The CP pigeon constraints correspond to the CNF pigeon clauses:
    // CNF pigeon clause for pigeon i: OR_j p_{i,j}
    // CP pigeon constraint for pigeon i: sum_j x_{i,j} >= 1
    for n in 1..=10 {
        let pigeons = n + 1;
        let cp_axioms = php_cp_axioms(n);
        let cp_ineqs = encode_php_cp(n);

        // Both should have (n+1) pigeon constraints + n hole constraints
        assert_eq!(cp_axioms.len(), cp_ineqs.len());
        assert_eq!(cp_axioms.len(), pigeons + n);

        // Pigeon constraints: same coefficient structure
        for (i, ax) in cp_axioms.iter().take(pigeons).enumerate() {
            assert_eq!(ax.rhs, 1, "pigeon {i} should have rhs=1");
            let ones = ax.coeffs.iter().filter(|&&c| c == 1).count();
            assert_eq!(ones, n, "pigeon {i} should have exactly n ones");
        }

        // Hole constraints: same structure
        for j in 0..n {
            let ax = &cp_axioms[pigeons + j];
            assert_eq!(ax.rhs, -1, "hole {j} should have rhs=-1");
            let neg_ones = ax.coeffs.iter().filter(|&&c| c == -1).count();
            assert_eq!(neg_ones, pigeons, "hole {j} should have n+1 negative ones");
        }
    }
}

// ===== Separation witness structure =====

#[test]
fn test_php_separation_witness_structure() {
    for n in [2, 5, 10, 50, 100] {
        let w = php_separation_witness(n);
        assert_eq!(w.formula_family, format!("PHP({},{})", n + 1, n));
        assert_eq!(w.parameter, n);
        match &w.weaker_size {
            ProofSizeBound::LowerBound(lb) => {
                assert!(*lb > 0.0, "Haken lower bound must be positive at n={n}");
            }
            _ => panic!("Expected LowerBound for resolution at n={n}"),
        }
        match &w.stronger_size {
            ProofSizeBound::UpperBound(ub) => {
                assert_eq!(*ub, php_cp_size_upper_bound(n));
            }
            _ => panic!("Expected UpperBound for CP at n={n}"),
        }
    }
}

// ===== Degenerate case: n=0 =====

#[test]
fn test_php_cp_proof_n0_degenerate() {
    let axioms = php_cp_axioms(0);
    let steps = cp_proof_of_php(0);
    // PHP(1,0): one pigeon, zero holes. Axiom is already 0 >= 1.
    assert!(steps.is_empty());
    assert!(verify_cp_derivation(&axioms, &steps));
    assert_eq!(axioms.len(), 1);
}
