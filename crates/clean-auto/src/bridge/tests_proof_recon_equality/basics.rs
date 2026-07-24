// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic equality proof-reconstruction coverage.

use super::*;

#[test]
fn test_proof_reconstruction_reflexivity() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a (reflexivity should produce Eq.refl proof)
    let goal = make_eq(a_ty, a.clone(), a);

    let result = bridge
        .prove(&goal)
        .expect("reflexivity goal should reconstruct");
    assert!(result.is_verified(), "Should prove a = a");

    let proof_result = result
        .verified()
        .expect("reflexivity result should be verified");
    // Check that the proof term is Eq.refl application
    let proof = proof_result.proof_term();
    // Verify proof head is Eq.refl (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("refl")),
        "Reflexivity proof head should be Eq.refl, got {head:?}"
    );

    // Check the proof step
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Refl(_)),
        "Proof step should be Refl, got {step:?}"
    );
}

#[test]
fn test_proof_reconstruction_direct_hypothesis() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Add hypothesis h : a = b with FVarId for proof tracking
    let hyp_fvar = FVarId::new(42);
    let hyp = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp, Some(hyp_fvar))
        .expect("direct hypothesis should register");

    // Goal: a = b (should use the hypothesis directly)
    let goal = make_eq(a_ty, a, b);

    let result = bridge
        .prove(&goal)
        .expect("direct hypothesis goal should reconstruct");
    assert!(result.is_verified(), "Should prove a = b from h : a = b");

    let proof_result = result
        .verified()
        .expect("direct hypothesis result should be verified");

    // The proof term should be the hypothesis FVar
    let proof = proof_result.proof_term();
    assert!(
        matches!(proof.kind(), ExprKind::FVar(fvar) if fvar.as_u64() == 42),
        "Proof should be FVar(42), got {proof:?}"
    );

    // The proof step must be Hypothesis(42)
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Hypothesis(fvar) if fvar.as_u64() == 42),
        "Proof step should be Hypothesis(42), got {step:?}"
    );
}

#[test]
fn test_proof_reconstruction_symmetry() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Add hypothesis h : a = b
    let hyp_fvar = FVarId::new(1);
    let hyp = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp, Some(hyp_fvar))
        .expect("symmetry hypothesis should register");

    // Goal: b = a (needs symmetry of h)
    let goal = make_eq(a_ty, b, a);

    let result = bridge
        .prove(&goal)
        .expect("symmetry goal should reconstruct");
    assert!(result.is_verified(), "Should prove b = a from h : a = b");

    let proof_result = result
        .verified()
        .expect("symmetry result should be verified");

    // The proof should be Eq.symm applied to the hypothesis
    let proof = proof_result.proof_term();
    // Verify proof head is Eq.symm (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("symm")),
        "Symmetry proof head should be Eq.symm, got {head:?}"
    );

    // Proof step must be Symm wrapping a sub-proof
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Symm(_)),
        "Proof step should be Symm, got {step:?}"
    );
    if let ProofStep::Symm(inner) = step {
        assert!(
            matches!(inner.as_ref(), ProofStep::Hypothesis(fvar) if fvar.as_u64() == 1),
            "Symm should wrap Hypothesis(1), got {inner:?}"
        );
    }
}

#[test]
fn test_proof_reconstruction_transitivity() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Add hypotheses h1 : a = b and h2 : b = c
    let hyp_fvar1 = FVarId::new(1);
    let hyp_fvar2 = FVarId::new(2);
    let hyp1 = make_eq(a_ty.clone(), a.clone(), b.clone());
    let hyp2 = make_eq(a_ty.clone(), b.clone(), c.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp1, Some(hyp_fvar1))
        .expect("left transitivity hypothesis should register");
    bridge
        .add_hypothesis_with_fvar(&hyp2, Some(hyp_fvar2))
        .expect("right transitivity hypothesis should register");

    // Goal: a = c (needs transitivity: h1 trans h2)
    let goal = make_eq(a_ty, a, c);

    let result = bridge
        .prove(&goal)
        .expect("transitivity goal should reconstruct");
    assert!(
        result.is_verified(),
        "Should prove a = c from h1 : a = b, h2 : b = c"
    );

    let proof_result = result
        .verified()
        .expect("transitivity result should be verified");

    // The proof should be Eq.trans applied to h1 and h2
    let proof = proof_result.proof_term();
    // Verify proof head is Eq.trans (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("trans")),
        "Transitivity proof head should be Eq.trans, got {head:?}"
    );

    // Proof step must be Trans(left, right) with both being Hypothesis references
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Trans(_, _)),
        "Proof step should be Trans, got {step:?}"
    );
    if let ProofStep::Trans(left, right) = step {
        assert!(
            matches!(left.as_ref(), ProofStep::Hypothesis(fvar) if fvar.as_u64() == 1),
            "Trans left should be Hypothesis(1) for h1: a=b, got {left:?}"
        );
        assert!(
            matches!(right.as_ref(), ProofStep::Hypothesis(fvar) if fvar.as_u64() == 2),
            "Trans right should be Hypothesis(2) for h2: b=c, got {right:?}"
        );
    }
}

#[test]
fn test_proof_reconstruction_transitivity_reversed() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Add hypotheses h1 : b = a and h2 : b = c
    // Need: a = c, which requires symm(h1) trans h2
    let hyp_fvar1 = FVarId::new(1);
    let hyp_fvar2 = FVarId::new(2);
    let hyp1 = make_eq(a_ty.clone(), b.clone(), a.clone()); // b = a
    let hyp2 = make_eq(a_ty.clone(), b.clone(), c.clone()); // b = c
    bridge
        .add_hypothesis_with_fvar(&hyp1, Some(hyp_fvar1))
        .expect("reversed left transitivity hypothesis should register");
    bridge
        .add_hypothesis_with_fvar(&hyp2, Some(hyp_fvar2))
        .expect("reversed right transitivity hypothesis should register");

    // Goal: a = c
    let goal = make_eq(a_ty, a, c);

    let result = bridge
        .prove(&goal)
        .expect("reversed transitivity goal should reconstruct");
    assert!(
        result.is_verified(),
        "Should prove a = c from h1 : b = a, h2 : b = c"
    );

    let proof_result = result
        .verified()
        .expect("reversed transitivity result should be verified");
    let proof = proof_result.proof_term();
    // Verify proof head is Eq.trans or Eq.symm (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _)
            if name.to_string().contains("trans") || name.to_string().contains("symm")),
        "Reversed transitivity proof head should be Eq.trans or Eq.symm, got {head:?}"
    );

    // Reversed transitivity requires Symm: Trans(Symm(h1), h2)
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Trans(_, _)),
        "Proof step should be Trans, got {step:?}"
    );
    if let ProofStep::Trans(left, right) = step {
        // Left side should be Symm(h1) since h1 is b=a but we need a=b
        assert!(
            matches!(left.as_ref(), ProofStep::Symm(_)),
            "Left of Trans should be Symm (reversing h1: b=a), got {left:?}"
        );
        // Right side should be a hypothesis reference
        assert!(
            matches!(right.as_ref(), ProofStep::Hypothesis(_)),
            "Right of Trans should be Hypothesis (h2: b=c), got {right:?}"
        );
    }
}
