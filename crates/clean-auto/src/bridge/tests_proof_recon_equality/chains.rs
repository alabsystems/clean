// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality chain-search and shortest-path coverage.

use super::*;

#[test]
fn test_proof_reconstruction_long_transitive_chain() {
    // Test BFS finding longer paths: a=b, b=c, c=d, d=e -> a=e
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);
    let e = Expr::const_(Name::from_string("e"), vec![]);

    // Add chain of hypotheses
    let h1 = make_eq(ty.clone(), a.clone(), b.clone()); // a = b
    let h2 = make_eq(ty.clone(), b.clone(), c.clone()); // b = c
    let h3 = make_eq(ty.clone(), c.clone(), d.clone()); // c = d
    let h4 = make_eq(ty.clone(), d.clone(), e.clone()); // d = e

    bridge
        .add_hypothesis_with_fvar(&h1, Some(FVarId::new(1)))
        .expect("chain hypothesis h1 should register");
    bridge
        .add_hypothesis_with_fvar(&h2, Some(FVarId::new(2)))
        .expect("chain hypothesis h2 should register");
    bridge
        .add_hypothesis_with_fvar(&h3, Some(FVarId::new(3)))
        .expect("chain hypothesis h3 should register");
    bridge
        .add_hypothesis_with_fvar(&h4, Some(FVarId::new(4)))
        .expect("chain hypothesis h4 should register");

    // Goal: a = e (needs 4-step transitivity chain)
    let goal = make_eq(ty.clone(), a.clone(), e.clone());

    let result = bridge
        .prove(&goal)
        .expect("long chain goal should reconstruct");
    assert!(result.is_verified(), "Should prove a = e from chain h1..h4");

    let proof_result = result
        .verified()
        .expect("long chain result should be verified");
    let proof = proof_result.proof_term();
    // Verify proof head is Eq.trans (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("trans")),
        "Long transitivity proof head should be Eq.trans, got {head:?}"
    );

    // Must be nested Trans: Trans(Trans(Trans(h1, h2), h3), h4)
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Trans(_, _)),
        "Proof step should be Trans at top level, got {step:?}"
    );
    if let ProofStep::Trans(left, _right) = step {
        // A 4-step chain a=b=c=d=e requires at least 2 levels of nesting:
        // Trans(Trans(...), h4) where the inner is also Trans
        assert!(
            matches!(left.as_ref(), ProofStep::Trans(_, _)),
            "4-step transitivity chain should have nested Trans on left, got {left:?}"
        );
    }
    // Verify all 4 hypothesis FVarIds appear in the proof tree
    let hyp_ids = collect_hypothesis_ids(step);
    for expected_id in 1u64..=4 {
        assert!(
            hyp_ids.contains(&FVarId::new(expected_id)),
            "4-step transitivity proof must reference hypothesis FVarId({expected_id}), \
             found IDs: {hyp_ids:?}"
        );
    }
}

#[test]
fn test_proof_reconstruction_long_chain_mixed_directions() {
    // Test BFS with mixed directions: a=b, c=b, c=d -> a=d
    // Path: a -h1-> b <-symm(h2)- c -h3-> d
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    // Add hypotheses with mixed directions
    let h1 = make_eq(ty.clone(), a.clone(), b.clone()); // a = b
    let h2 = make_eq(ty.clone(), c.clone(), b.clone()); // c = b (reversed!)
    let h3 = make_eq(ty.clone(), c.clone(), d.clone()); // c = d

    bridge
        .add_hypothesis_with_fvar(&h1, Some(FVarId::new(1)))
        .expect("mixed-direction hypothesis h1 should register");
    bridge
        .add_hypothesis_with_fvar(&h2, Some(FVarId::new(2)))
        .expect("mixed-direction hypothesis h2 should register");
    bridge
        .add_hypothesis_with_fvar(&h3, Some(FVarId::new(3)))
        .expect("mixed-direction hypothesis h3 should register");

    // Goal: a = d
    // Proof path: a = b (h1), b = c (symm h2), c = d (h3)
    let goal = make_eq(ty.clone(), a.clone(), d.clone());

    let result = bridge
        .prove(&goal)
        .expect("mixed-direction goal should reconstruct");
    assert!(
        result.is_verified(),
        "Should prove a = d with mixed direction hypotheses"
    );

    let proof_result = result
        .verified()
        .expect("mixed-direction result should be verified");
    let proof = proof_result.proof_term();
    // Verify proof head is Eq.trans (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("trans")),
        "Mixed-direction proof head should be Eq.trans, got {head:?}"
    );

    // Mixed directions: Trans(Trans(h1, Symm(h2)), h3)
    // The proof must contain a Symm somewhere in the tree to handle c=b->b=c reversal
    let step = proof_result.proof_step();
    fn contains_symm(step: &ProofStep) -> bool {
        match step {
            ProofStep::Symm(_) => true,
            ProofStep::Trans(l, r) => contains_symm(l) || contains_symm(r),
            ProofStep::Congr(_, args) => args.iter().any(contains_symm),
            _ => false,
        }
    }
    assert!(
        matches!(step, ProofStep::Trans(_, _)),
        "Proof step should be Trans at top level, got {step:?}"
    );
    assert!(
        contains_symm(step),
        "Mixed-direction proof must contain a Symm step for reversed hypothesis, got {step:?}"
    );
    // Verify all 3 hypothesis FVarIds (h1, h2, h3) appear in the proof tree
    let hyp_ids = collect_hypothesis_ids(step);
    for expected_id in 1u64..=3 {
        assert!(
            hyp_ids.contains(&FVarId::new(expected_id)),
            "Mixed-direction proof must reference hypothesis FVarId({expected_id}), \
             found IDs: {hyp_ids:?}"
        );
    }
}

#[test]
fn test_proof_reconstruction_finds_shortest_path() {
    // Test that BFS finds shortest path when multiple exist
    // Direct: a = d
    // Long: a = b = c = d
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    // Add both direct and indirect paths
    let h_direct = make_eq(ty.clone(), a.clone(), d.clone()); // a = d (direct)
    let h1 = make_eq(ty.clone(), a.clone(), b.clone()); // a = b
    let h2 = make_eq(ty.clone(), b.clone(), c.clone()); // b = c
    let h3 = make_eq(ty.clone(), c.clone(), d.clone()); // c = d

    bridge
        .add_hypothesis_with_fvar(&h_direct, Some(FVarId::new(100)))
        .expect("direct shortest-path hypothesis should register");
    bridge
        .add_hypothesis_with_fvar(&h1, Some(FVarId::new(1)))
        .expect("indirect shortest-path hypothesis h1 should register");
    bridge
        .add_hypothesis_with_fvar(&h2, Some(FVarId::new(2)))
        .expect("indirect shortest-path hypothesis h2 should register");
    bridge
        .add_hypothesis_with_fvar(&h3, Some(FVarId::new(3)))
        .expect("indirect shortest-path hypothesis h3 should register");

    // Goal: a = d
    let goal = make_eq(ty.clone(), a.clone(), d.clone());

    let result = bridge
        .prove(&goal)
        .expect("shortest-path goal should reconstruct");
    assert!(result.is_verified(), "Should prove a = d");

    let proof_result = result
        .verified()
        .expect("shortest-path result should be verified");

    // BFS should find shortest path: direct hypothesis FVar(100)
    let proof = proof_result.proof_term();
    assert!(
        matches!(proof.kind(), ExprKind::FVar(fvar) if fvar.as_u64() == 100),
        "Proof should use direct hypothesis FVar(100), got {proof:?}"
    );

    // Proof step should be Hypothesis(100), not Trans chain
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Hypothesis(fvar) if fvar.as_u64() == 100),
        "Proof step should be Hypothesis(100), got {step:?}"
    );
}
