// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for KKL inequality proof infrastructure (S43/S47).

use super::fourier::{compute_all_fourier, BooleanFunction};
use super::kkl_proof::{
    build_kkl_witness, entropy_influence_bound, kkl_constant, level_one_lower_bound,
    level_one_weight, tribe_function_influence, verify_balanced, verify_kkl_computational,
    verify_kkl_proof_chain, verify_kkl_steps, KklProofStep, KKL_CONSTANT,
    S43A_KKL_BALANCED_HYPOTHESIS, S43B_KKL_HYPERCONTRACTIVE_STEP, S43C_KKL_FULL_CHAIN,
};
use super::noise_sensitivity::{max_influence, total_influence, variable_influence};
use crate::spec::ProofStatus;

const TOL: f64 = 1e-8;

// -- Balanced verification --

#[test]
fn test_verify_balanced_dictator_is_balanced() {
    let f = BooleanFunction::dictator(0, 3).unwrap();
    assert!(verify_balanced(&f).unwrap(), "dictator is balanced");
}

#[test]
fn test_verify_balanced_parity_is_balanced() {
    let f = BooleanFunction::parity(4).unwrap();
    assert!(verify_balanced(&f).unwrap(), "parity is balanced");
}

#[test]
fn test_verify_balanced_majority_odd_is_balanced() {
    let f = BooleanFunction::majority(3).unwrap();
    assert!(verify_balanced(&f).unwrap(), "majority(3) is balanced");
}

#[test]
fn test_verify_balanced_majority_5_is_balanced() {
    let f = BooleanFunction::majority(5).unwrap();
    assert!(verify_balanced(&f).unwrap(), "majority(5) is balanced");
}

#[test]
fn test_verify_balanced_constant_not_balanced() {
    let f = BooleanFunction::constant(1.0, 3).unwrap();
    assert!(!verify_balanced(&f).unwrap(), "constant +1 is not balanced");
    let g = BooleanFunction::constant(-1.0, 3).unwrap();
    assert!(!verify_balanced(&g).unwrap(), "constant -1 is not balanced");
}

// -- KKL constant --

#[test]
fn test_kkl_constant_value() {
    let c = kkl_constant();
    assert!((c - 0.23398).abs() < 0.001, "KKL constant ~ 0.234, got {c}");
    assert!(
        (c - KKL_CONSTANT).abs() < 1e-15,
        "function and constant agree"
    );
    // KKL_CONSTANT is a compile-time const so checking it directly is vacuous;
    // assert the same (0, 1) range bound on the runtime-computed value instead.
    assert!(c > 0.0 && c < 1.0, "KKL constant in (0, 1), got {c}");
}

// -- Level-1 weight --

#[test]
fn test_level_one_weight_dictator_is_one() {
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let w1 = level_one_weight(&f).unwrap();
    assert!((w1 - 1.0).abs() < TOL, "W^1(dictator) = 1, got {w1}");
}

#[test]
fn test_level_one_weight_parity_is_zero() {
    let f = BooleanFunction::parity(4).unwrap();
    let w1 = level_one_weight(&f).unwrap();
    assert!(w1.abs() < TOL, "W^1(parity) = 0, got {w1}");
}

#[test]
fn test_level_one_weight_majority_3() {
    let f = BooleanFunction::majority(3).unwrap();
    let w1 = level_one_weight(&f).unwrap();
    assert!((w1 - 0.75).abs() < TOL, "W^1(MAJ_3) = 3/4, got {w1}");
}

#[test]
fn test_level_one_weight_constant_is_zero() {
    let f = BooleanFunction::constant(1.0, 3).unwrap();
    let w1 = level_one_weight(&f).unwrap();
    assert!(w1.abs() < TOL, "W^1(const) = 0, got {w1}");
}

// -- Level-1 lower bound --

#[test]
fn test_level_one_lower_bound_dictator_holds() {
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let (w1, bound, holds) = level_one_lower_bound(&f).unwrap();
    assert!(
        holds,
        "level-1 bound holds for dictator: w1={w1}, bound={bound}"
    );
}

#[test]
fn test_level_one_lower_bound_majority_holds() {
    let f = BooleanFunction::majority(5).unwrap();
    let (_w1, _bound, holds) = level_one_lower_bound(&f).unwrap();
    assert!(holds, "level-1 bound holds for majority");
}

#[test]
fn test_level_one_lower_bound_parity_violates() {
    // Parity: W^1 = 0 < I(f)^2/n^2 = 1 => bound violated (expected).
    let f = BooleanFunction::parity(4).unwrap();
    let (_w1, _bound, holds) = level_one_lower_bound(&f).unwrap();
    assert!(!holds, "parity violates level-1 lower bound");
}

// -- Computational KKL verification --

#[test]
fn test_verify_kkl_computational_standard_functions() {
    let cases: Vec<(&str, BooleanFunction)> = vec![
        ("dictator", BooleanFunction::dictator(0, 3).unwrap()),
        ("parity", BooleanFunction::parity(5).unwrap()),
        ("MAJ_3", BooleanFunction::majority(3).unwrap()),
        ("MAJ_5", BooleanFunction::majority(5).unwrap()),
        ("MAJ_7", BooleanFunction::majority(7).unwrap()),
        ("AND2", BooleanFunction::and2(2).unwrap()),
    ];
    for (name, f) in &cases {
        assert!(verify_kkl_computational(f), "KKL holds for {name}");
    }
}

#[test]
fn test_verify_kkl_computational_n1_trivial() {
    let f = BooleanFunction::dictator(0, 1).unwrap();
    assert!(verify_kkl_computational(&f), "trivially true for n=1");
}

// -- Full proof chain --

#[test]
fn test_verify_kkl_proof_chain_dictator() {
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let steps = verify_kkl_proof_chain(&f).unwrap();
    assert_eq!(steps.len(), 4);
    for (step, passed) in &steps {
        assert!(passed, "step {:?} should pass for dictator", step);
    }
}

#[test]
fn test_verify_kkl_proof_chain_majority() {
    for n in [3, 5] {
        let f = BooleanFunction::majority(n).unwrap();
        let steps = verify_kkl_proof_chain(&f).unwrap();
        for (step, passed) in &steps {
            assert!(passed, "step {:?} should pass for MAJ_{n}", step);
        }
    }
}

#[test]
fn test_verify_kkl_proof_chain_constant_fails_balanced() {
    let f = BooleanFunction::constant(1.0, 3).unwrap();
    let steps = verify_kkl_proof_chain(&f).unwrap();
    let inf_step = steps
        .iter()
        .find(|(s, _)| *s == KklProofStep::InfluenceLowerBound);
    assert!(
        !inf_step.unwrap().1,
        "influence lower bound fails for constant"
    );
}

#[test]
fn test_verify_kkl_proof_chain_returns_four_steps() {
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let steps = verify_kkl_proof_chain(&f).unwrap();
    assert_eq!(steps.len(), 4);
    assert_eq!(steps[0].0, KklProofStep::BonamiBeckner);
    assert_eq!(steps[1].0, KklProofStep::LevelWeightBound);
    assert_eq!(steps[2].0, KklProofStep::InfluenceLowerBound);
    assert_eq!(steps[3].0, KklProofStep::MaxInfluenceBound);
}

// -- Entropy-influence bound --

#[test]
fn test_entropy_influence_balanced_function() {
    // Balanced f: H(1/2)/ln(2) = 1. Dictator I(f) = 1 => tight.
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let (inf, bound, holds) = entropy_influence_bound(&f).unwrap();
    assert!(holds, "entropy-influence holds for dictator");
    assert!(
        (bound - 1.0).abs() < TOL,
        "bound = 1 for balanced: got {bound}"
    );
    assert!((inf - 1.0).abs() < TOL);
}

#[test]
fn test_entropy_influence_parity() {
    let f = BooleanFunction::parity(4).unwrap();
    let (inf, bound, holds) = entropy_influence_bound(&f).unwrap();
    assert!(holds, "entropy-influence holds for parity");
    assert!((inf - 4.0).abs() < TOL, "I(parity_4) = 4");
    assert!((bound - 1.0).abs() < TOL);
}

#[test]
fn test_entropy_influence_constant_trivial() {
    let f = BooleanFunction::constant(1.0, 3).unwrap();
    let (inf, bound, holds) = entropy_influence_bound(&f).unwrap();
    assert!(holds, "entropy-influence trivially holds for constant");
    assert!(bound.abs() < TOL && inf.abs() < TOL);
}

#[test]
fn test_entropy_influence_majority_and_and2() {
    let f = BooleanFunction::majority(5).unwrap();
    let (_, _, holds) = entropy_influence_bound(&f).unwrap();
    assert!(holds, "entropy-influence holds for majority");

    let g = BooleanFunction::and2(3).unwrap();
    let (_, _, holds2) = entropy_influence_bound(&g).unwrap();
    assert!(holds2, "entropy-influence holds for AND2");
}

// -- Tribes function --

#[test]
fn test_tribe_function_influence_n3() {
    let (mi, bound, ratio) = tribe_function_influence(3).unwrap();
    assert!(mi > 0.0 && bound > 0.0);
    assert!(ratio >= 1.0 - TOL, "tribes satisfies KKL: ratio={ratio}");
}

#[test]
fn test_tribe_function_influence_n5() {
    // At n=5 the tribes approximation is coarse (group_size=1).
    let (mi, bound, ratio) = tribe_function_influence(5).unwrap();
    assert!(mi > 0.0 && bound > 0.0);
    assert!(ratio > 0.5, "tribes ratio > 0.5 for n=5: ratio={ratio}");
}

#[test]
fn test_tribe_function_influence_n8() {
    let (mi, bound, _) = tribe_function_influence(8).unwrap();
    assert!(mi > 0.0);
    assert!(mi >= bound - TOL, "tribes satisfies KKL bound for n=8");
}

#[test]
fn test_tribe_function_edge_cases() {
    assert!(tribe_function_influence(17).is_err(), "n=17 exceeds limit");
    let (mi, bound, _) = tribe_function_influence(1).unwrap();
    assert!((mi - 1.0).abs() < TOL, "n=1 tribes is a single variable");
    assert!(bound.abs() < TOL, "KKL bound = 0 for n=1");
}

// -- Build and verify witness --

#[test]
fn test_build_kkl_witness_dictator() {
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    assert_eq!(w.n, 3);
    assert!(w.is_balanced);
    assert!(w.bonami_beckner_holds);
    assert!(w.kkl_bound_satisfied);
    assert!((w.max_influence - 1.0).abs() < TOL);
    assert!((w.total_influence - 1.0).abs() < TOL);
    assert!((w.level_one_weight - 1.0).abs() < TOL);
    assert_eq!(w.influences.len(), 3);
}

#[test]
fn test_build_kkl_witness_majority_5() {
    let f = BooleanFunction::majority(5).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    assert_eq!(w.n, 5);
    assert!(w.is_balanced && w.bonami_beckner_holds && w.kkl_bound_satisfied);
    assert_eq!(w.influences.len(), 5);
    for i in 1..5 {
        assert!(
            (w.influences[i] - w.influences[0]).abs() < TOL,
            "MAJ_5 is symmetric"
        );
    }
}

#[test]
fn test_build_witness_then_verify_steps_roundtrip() {
    let f = BooleanFunction::dictator(0, 4).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    let steps = verify_kkl_steps(&w);
    assert_eq!(steps.len(), 4);
    for (step, passed) in &steps {
        assert!(passed, "step {:?} should pass for dictator witness", step);
    }
}

#[test]
fn test_build_witness_constant_not_balanced() {
    let f = BooleanFunction::constant(1.0, 3).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    assert!(!w.is_balanced);
    let steps = verify_kkl_steps(&w);
    let inf_step = steps
        .iter()
        .find(|(s, _)| *s == KklProofStep::InfluenceLowerBound);
    assert!(!inf_step.unwrap().1, "influence bound fails for unbalanced");
}

#[test]
fn test_witness_fourier_coefficients_nonempty() {
    let f = BooleanFunction::majority(3).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    assert_eq!(w.fourier_coefficients.len(), 8, "2^3 = 8 coefficients");
}

// -- Verify each step independently --

#[test]
fn test_verify_kkl_steps_bb_independent() {
    let f = BooleanFunction::majority(3).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    let steps = verify_kkl_steps(&w);
    let bb = steps
        .iter()
        .find(|(s, _)| *s == KklProofStep::BonamiBeckner)
        .unwrap();
    assert!(bb.1, "BB step passes independently");
}

#[test]
fn test_verify_kkl_steps_level_weight_independent() {
    let f = BooleanFunction::majority(3).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    let steps = verify_kkl_steps(&w);
    let lw = steps
        .iter()
        .find(|(s, _)| *s == KklProofStep::LevelWeightBound)
        .unwrap();
    assert!(lw.1, "level weight step passes independently");
}

#[test]
fn test_verify_kkl_steps_max_influence_independent() {
    let f = BooleanFunction::parity(5).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    let steps = verify_kkl_steps(&w);
    let mi = steps
        .iter()
        .find(|(s, _)| *s == KklProofStep::MaxInfluenceBound)
        .unwrap();
    assert!(mi.1, "max influence step passes for parity");
}

// -- Edge cases --

#[test]
fn test_kkl_n1_function() {
    let f = BooleanFunction::dictator(0, 1).unwrap();
    assert!(verify_kkl_computational(&f));
    let w = build_kkl_witness(&f).unwrap();
    assert_eq!(w.n, 1);
    assert!(w.kkl_bound_satisfied);
}

#[test]
fn test_kkl_n2_and_function() {
    let f = BooleanFunction::and2(2).unwrap();
    assert!(verify_kkl_computational(&f));
    let chain = verify_kkl_proof_chain(&f).unwrap();
    let mi_step = chain
        .iter()
        .find(|(s, _)| *s == KklProofStep::MaxInfluenceBound)
        .unwrap();
    assert!(mi_step.1, "KKL max influence holds for AND2");
}

#[test]
fn test_kkl_constant_function_max_influence_zero() {
    let f = BooleanFunction::constant(1.0, 3).unwrap();
    let mi = max_influence(&f);
    assert!(mi.abs() < TOL, "max influence of constant = 0");
    assert!(!verify_kkl_computational(&f), "constant violates KKL");
}

// -- Proof status constants --

#[test]
fn test_proof_status_constants() {
    assert_eq!(S43A_KKL_BALANCED_HYPOTHESIS, ProofStatus::DerivedPending);
    assert_eq!(S43B_KKL_HYPERCONTRACTIVE_STEP, ProofStatus::DerivedPending);
    assert_eq!(S43C_KKL_FULL_CHAIN, ProofStatus::DerivedPending);
}

// -- Influence value spot checks --

#[test]
fn test_dictator_influence_is_one() {
    let f = BooleanFunction::dictator(0, 5).unwrap();
    let inf0 = variable_influence(&f, 0).unwrap();
    assert!((inf0 - 1.0).abs() < TOL, "Inf_0(dictator) = 1");
    assert!((max_influence(&f) - 1.0).abs() < TOL);
}

#[test]
fn test_parity_all_influences_equal_one() {
    let f = BooleanFunction::parity(5).unwrap();
    for i in 0..5 {
        let inf = variable_influence(&f, i).unwrap();
        assert!((inf - 1.0).abs() < TOL, "Inf_{i}(parity) = 1, got {inf}");
    }
}

#[test]
fn test_majority_max_influence_scales_correctly() {
    let f3 = BooleanFunction::majority(3).unwrap();
    let mi3 = max_influence(&f3);
    assert!((mi3 - 0.5).abs() < TOL, "MAJ_3 max inf = 0.5, got {mi3}");
    let f5 = BooleanFunction::majority(5).unwrap();
    let mi5 = max_influence(&f5);
    assert!(mi5 < mi3 && mi5 > 0.0, "MAJ_5 max inf < MAJ_3 max inf");
}

// -- Cross-module consistency --

#[test]
fn test_witness_matches_noise_sensitivity_module() {
    let f = BooleanFunction::majority(5).unwrap();
    let w = build_kkl_witness(&f).unwrap();
    assert!(
        (w.max_influence - max_influence(&f)).abs() < TOL,
        "witness max_inf matches noise_sensitivity::max_influence"
    );
    assert!(
        (w.total_influence - total_influence(&f)).abs() < TOL,
        "witness total_inf matches noise_sensitivity::total_influence"
    );
}

#[test]
fn test_level_one_weight_matches_hypercontractivity_module() {
    let f = BooleanFunction::majority(3).unwrap();
    let w1_kkl = level_one_weight(&f).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let w1_hyper = super::hypercontractivity::level_k_weight(&coeffs, 3, 1);
    assert!(
        (w1_kkl - w1_hyper).abs() < TOL,
        "level_one_weight matches hypercontractivity::level_k_weight"
    );
}
