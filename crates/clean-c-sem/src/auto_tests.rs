// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::Name;

fn kernel_evidence(trusted_ay_subterms: usize) -> KernelProofEvidence {
    KernelProofEvidence {
        proof: Expr::const_(Name::from_string("kernelProof"), vec![]),
        trusted_ay_subterms,
    }
}

#[test]
fn test_trivially_true() {
    let prover = VCProver::new();

    assert!(prover.is_trivially_true(&Spec::True));
    assert!(prover.is_trivially_true(&Spec::and(vec![Spec::True, Spec::True])));

    // Closed integer reflexivity is trivially true.
    let eq_self = Spec::eq(Spec::int(7), Spec::int(7));
    assert!(prover.is_trivially_true(&eq_self));

    let ge_self = Spec::ge(Spec::int(7), Spec::int(7));
    assert!(prover.is_trivially_true(&ge_self));

    let untyped = Spec::eq(Spec::var("possibly_nan"), Spec::var("possibly_nan"));
    assert!(!prover.is_trivially_true(&untyped));
}

#[test]
fn test_trivially_false() {
    let prover = VCProver::new();

    assert!(prover.is_trivially_false(&Spec::False));
    assert!(prover.is_trivially_false(&Spec::or(vec![Spec::False, Spec::False])));

    // Closed integer non-equality to self is trivially false.
    let ne_self = Spec::ne(Spec::int(7), Spec::int(7));
    assert!(prover.is_trivially_false(&ne_self));

    let lt_self = Spec::lt(Spec::int(7), Spec::int(7));
    assert!(prover.is_trivially_false(&lt_self));

    let untyped = Spec::ne(Spec::var("possibly_nan"), Spec::var("possibly_nan"));
    assert!(!prover.is_trivially_false(&untyped));
}

#[test]
fn test_simplify_and() {
    // True && P = P
    let spec = Spec::and(vec![Spec::True, Spec::var("P")]);
    assert_eq!(simplify_spec(&spec), Spec::var("P"));

    // False && P = False
    let spec = Spec::and(vec![Spec::False, Spec::var("P")]);
    assert_eq!(simplify_spec(&spec), Spec::False);

    // True && True = True
    let spec = Spec::and(vec![Spec::True, Spec::True]);
    assert_eq!(simplify_spec(&spec), Spec::True);
}

#[test]
fn test_simplify_or() {
    // False || P = P
    let spec = Spec::or(vec![Spec::False, Spec::var("P")]);
    assert_eq!(simplify_spec(&spec), Spec::var("P"));

    // True || P = True
    let spec = Spec::or(vec![Spec::True, Spec::var("P")]);
    assert_eq!(simplify_spec(&spec), Spec::True);
}

#[test]
fn test_simplify_implies() {
    // False => P = True
    let spec = Spec::implies(Spec::False, Spec::var("P"));
    assert_eq!(simplify_spec(&spec), Spec::True);

    // P => True = True
    let spec = Spec::implies(Spec::var("P"), Spec::True);
    assert_eq!(simplify_spec(&spec), Spec::True);

    // True => P = P
    let spec = Spec::implies(Spec::True, Spec::var("P"));
    assert_eq!(simplify_spec(&spec), Spec::var("P"));
}

#[test]
fn test_simplify_not() {
    // !!P = P
    let spec = Spec::not(Spec::not(Spec::var("P")));
    assert_eq!(simplify_spec(&spec), Spec::var("P"));

    // !True = False
    assert_eq!(simplify_spec(&Spec::not(Spec::True)), Spec::False);

    // !False = True
    assert_eq!(simplify_spec(&Spec::not(Spec::False)), Spec::True);
}

#[test]
fn test_simplify_comparison() {
    // An untyped symbol may be a floating NaN, so reflexivity must stay open.
    let spec = Spec::eq(Spec::var("x"), Spec::var("x"));
    assert_eq!(simplify_spec(&spec), spec);

    // The same applies to non-equality: NaN != NaN is true.
    let spec = Spec::ne(Spec::var("x"), Spec::var("x"));
    assert_eq!(simplify_spec(&spec), spec);

    let spec = Spec::eq(Spec::int(3), Spec::int(3));
    assert_eq!(simplify_spec(&spec), Spec::True);

    // 1 < 2 = True
    let spec = Spec::lt(Spec::int(1), Spec::int(2));
    assert_eq!(simplify_spec(&spec), Spec::True);

    // 2 < 1 = False
    let spec = Spec::lt(Spec::int(2), Spec::int(1));
    assert_eq!(simplify_spec(&spec), Spec::False);

    // 1 + 2 = 3
    let spec = Spec::binop(BinOp::Add, Spec::int(1), Spec::int(2));
    assert_eq!(simplify_spec(&spec), Spec::Int(3));
}

#[test]
fn test_constant_folding() {
    // 3 >= 0 = True
    let spec = Spec::ge(Spec::int(3), Spec::int(0));
    assert_eq!(simplify_spec(&spec), Spec::True);

    // -1 >= 0 = False
    let spec = Spec::ge(Spec::int(-1), Spec::int(0));
    assert_eq!(simplify_spec(&spec), Spec::False);
}

#[test]
fn test_prove_vc_simplifies_constant_ub_side_condition_before_lowering() {
    let vc = VC {
        description: "concrete divisor".to_string(),
        obligation: Spec::ne(Spec::int(2), Spec::int(0)),
        location: None,
        kind: VCKind::NoUB,
    };
    assert!(
        VCProver::new().prove_vc(&vc).is_fully_verified(),
        "a semantics-preserving constant fold must lower to a checked proof of True"
    );
}

#[test]
fn test_prove_vc_simplification_does_not_turn_false_goal_into_success() {
    let vc = VC {
        description: "zero divisor".to_string(),
        obligation: Spec::ne(Spec::int(0), Spec::int(0)),
        location: None,
        kind: VCKind::NoUB,
    };
    assert!(
        !VCProver::new().prove_vc(&vc).is_established(),
        "simplification must preserve a false UB side condition as failure"
    );
}

#[test]
fn test_authority_fold_preserves_symbolic_reflexive_comparison() {
    let symbolic = Spec::eq(Spec::var("possibly_nan"), Spec::var("possibly_nan"));
    assert_eq!(
        simplify_closed_literals(&symbolic),
        symbolic,
        "untyped reflexivity is not an authority-safe rewrite because a float may be NaN"
    );
}

#[test]
fn test_prover_does_not_certify_untyped_symbolic_reflexivity() {
    let symbolic = Spec::eq(Spec::var("possibly_nan"), Spec::var("possibly_nan"));
    assert!(
        !VCProver::new().prove_spec(&symbolic).is_established(),
        "the structural fallback must not re-introduce untyped reflexivity authority after the safe fold"
    );
}

#[test]
fn test_prover_does_not_certify_negated_untyped_nonreflexivity() {
    let symbolic = Spec::not(Spec::ne(
        Spec::var("possibly_nan"),
        Spec::var("possibly_nan"),
    ));
    assert!(
        !VCProver::new().prove_spec(&symbolic).is_established(),
        "NaN != NaN makes negated untyped nonreflexivity false"
    );
}

#[test]
fn test_verification_summary() {
    let mut summary = VerificationSummary::new();

    summary.add(
        "kernel".to_string(),
        ProofStatus::KernelVerified(kernel_evidence(0)),
    );
    summary.add("structural".to_string(), ProofStatus::StructuralProved);
    summary.add(
        "unverified".to_string(),
        ProofStatus::Unverified("reconstruction missing".to_string()),
    );
    summary.add(
        "failed".to_string(),
        ProofStatus::Failed("reason".to_string()),
    );
    summary.add("unknown".to_string(), ProofStatus::Unknown);

    assert_eq!(summary.total, 5);
    assert_eq!(summary.proved, 2);
    assert_eq!(summary.kernel_verified, 1);
    assert_eq!(summary.structural_proved, 1);
    assert_eq!(summary.unverified, 1);
    assert_eq!(summary.failed, 1);
    assert_eq!(summary.unknown, 1);
    assert!(!summary.all_proved());
    assert!(!summary.all_fully_verified());
    assert!(summary.has_failures());
}

#[test]
fn test_proof_status_helper_methods_distinguish_strict_success() {
    let fully_verified = ProofStatus::KernelVerified(kernel_evidence(0));
    let trusted_kernel = ProofStatus::KernelVerified(kernel_evidence(2));
    let structural = ProofStatus::StructuralProved;
    let unverified = ProofStatus::Unverified("reconstruction missing".to_string());

    assert!(fully_verified.is_established());
    assert!(fully_verified.is_kernel_verified());
    assert!(fully_verified.is_fully_verified());

    assert!(trusted_kernel.is_established());
    assert!(trusted_kernel.is_kernel_verified());
    assert!(!trusted_kernel.is_fully_verified());

    assert!(structural.is_established());
    assert!(!structural.is_kernel_verified());
    assert!(!structural.is_fully_verified());

    assert!(!unverified.is_established());
    assert!(!unverified.is_kernel_verified());
    assert!(!unverified.is_fully_verified());
}

#[test]
fn test_quick_check_fully_verified_accepts_kernel_success() {
    assert!(quick_check(&Spec::True));
    assert!(quick_check_fully_verified(&Spec::True));
}

#[test]
fn test_unverified_fallback_preserves_status_without_structural_proof() {
    let prover = VCProver::new();
    let expr = prover
        .spec_to_expr(&Spec::valid(Spec::var("p")))
        .expect("valid(p) should translate");

    let status = prover.fallback_to_structural_or(
        &expr,
        &VCKind::Assertion,
        ProofStatus::Unverified("reconstruction missing".to_string()),
    );

    assert_eq!(
        status,
        ProofStatus::Unverified("reconstruction missing".to_string())
    );
}

#[test]
fn test_unverified_fallback_yields_structural_success_when_independent_proof_exists() {
    let prover = VCProver::new();
    let expr = prover
        .spec_to_expr(&Spec::True)
        .expect("True should translate");

    let status = prover.fallback_to_structural_or(
        &expr,
        &VCKind::Assertion,
        ProofStatus::Unverified("reconstruction missing".to_string()),
    );

    assert_eq!(status, ProofStatus::StructuralProved);
}

#[test]
fn test_trivial_specs() {
    let prover = VCProver::new();

    let eq_self = Spec::eq(Spec::int(11), Spec::int(11));
    assert!(prover.is_trivially_true(&eq_self));

    let simplified = simplify_spec(&eq_self);
    assert_eq!(simplified, Spec::True);
}
