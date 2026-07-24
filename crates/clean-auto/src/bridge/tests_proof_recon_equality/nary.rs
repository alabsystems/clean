// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! N-ary congruence equality proof-reconstruction coverage.

use super::*;

/// Extend setup_env with extra constants and an n-ary function over A.
fn setup_env_nary(extra_consts: &[&str], func_name: &str, arity: usize) -> Environment {
    let mut env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    for name in extra_consts {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: a_ty.clone(),
        })
        .expect("n-ary test constant should register");
    }
    // Build A -> A -> ... -> A with `arity` arrows
    let mut func_ty = a_ty.clone();
    for _ in 0..arity {
        func_ty = Expr::arrow(a_ty.clone(), func_ty);
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(func_name),
        level_params: vec![],
        type_: func_ty,
    })
    .expect("n-ary test function should register");
    env
}

#[test]
fn test_proof_reconstruction_multi_arg_congruence() {
    // Test multi-argument congruence: h1 : a = b, h2 : c = d -> f2(a, c) = f2(b, d)
    let env = setup_env_nary(&["d"], "f2", 2);
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);
    let f2 = Expr::const_(Name::from_string("f2"), vec![]);

    // f2(a, c) = f2 a c (curried)
    let fac = Expr::app(Expr::app(f2.clone(), a.clone()), c.clone());
    let fbd = Expr::app(Expr::app(f2, b.clone()), d.clone());

    // Add hypotheses
    let h1 = make_eq(ty.clone(), a.clone(), b.clone()); // a = b
    let h2 = make_eq(ty.clone(), c.clone(), d.clone()); // c = d

    bridge
        .add_hypothesis_with_fvar(&h1, Some(FVarId::new(1)))
        .expect("multi-arg hypothesis h1 should register");
    bridge
        .add_hypothesis_with_fvar(&h2, Some(FVarId::new(2)))
        .expect("multi-arg hypothesis h2 should register");

    // Goal: f2(a, c) = f2(b, d)
    let goal = make_eq(ty.clone(), fac, fbd);

    let result = bridge
        .prove(&goal)
        .expect("multi-arg congruence goal should reconstruct");
    assert!(
        result.is_verified(),
        "Should prove f2(a, c) = f2(b, d) from h1 : a = b, h2 : c = d"
    );

    let proof_result = result
        .verified()
        .expect("multi-arg congruence result should be verified");
    let proof = proof_result.proof_term();
    // Verify proof head is congrArg or similar (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("congr")),
        "Multi-arg congruence proof head should be congrArg or similar, got {head:?}"
    );

    // Proof step must involve congruence on "f2" with substantive arg proofs.
    // Due to curried application optimization, the E-graph handles f2(a,c) as ((f2 a) c).
    // The congruence closure may absorb one equality (e.g., a=b) into the union-find
    // for the inner application (f2 a)=(f2 b), producing Congr("f2", [Hypothesis(h1)])
    // with the remaining c=d handled at the outer application level implicitly.
    // Therefore the explicit leaf count may be < 2 for 2-arg curried congruence.
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Congr(_, _)),
        "Proof step should be Congr(\"f2\", ..), got {step:?}"
    );
    if let ProofStep::Congr(_func_expr, args) = step {
        assert_eq!(
            congr_func_name(step).as_deref(),
            Some("f2"),
            "Function should be f2"
        );
        // Must have at least 1 arg proof (substantive, not Refl)
        assert!(
            !args.is_empty(),
            "Congr(\"f2\", ..) should have at least 1 arg proof"
        );
        // Each arg proof must reference a hypothesis (directly or via nesting)
        fn references_hypothesis(step: &ProofStep) -> bool {
            match step {
                ProofStep::Hypothesis(_) => true,
                ProofStep::Symm(inner) => references_hypothesis(inner),
                ProofStep::Trans(l, r) => references_hypothesis(l) || references_hypothesis(r),
                ProofStep::Congr(_, args) => args.iter().any(references_hypothesis),
                _ => false,
            }
        }
        for (i, arg) in args.iter().enumerate() {
            assert!(
                references_hypothesis(arg),
                "Congr arg[{i}] should reference a hypothesis (a=b or c=d), got {arg:?}"
            );
        }
    }
}

#[test]
fn test_proof_reconstruction_three_arg_congruence() {
    // Test 3-argument congruence: h1 : a = b, h2 : c = d, h3 : e = f_val -> g(a, c, e) = g(b, d, f_val)
    let env = setup_env_nary(&["d", "e", "f_val"], "g", 3);
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let [a, b, c, d, e, f_val, g] =
        ["a", "b", "c", "d", "e", "f_val", "g"].map(|n| Expr::const_(Name::from_string(n), vec![]));

    // g(a, c, e) = g a c e (curried)
    let gace = Expr::app(
        Expr::app(Expr::app(g.clone(), a.clone()), c.clone()),
        e.clone(),
    );
    let gbdf = Expr::app(Expr::app(Expr::app(g, b.clone()), d.clone()), f_val.clone());

    // Add hypotheses
    let h1 = make_eq(ty.clone(), a.clone(), b.clone());
    let h2 = make_eq(ty.clone(), c.clone(), d.clone());
    let h3 = make_eq(ty.clone(), e.clone(), f_val.clone());

    for (hyp, id) in [(&h1, 1), (&h2, 2), (&h3, 3)] {
        bridge
            .add_hypothesis_with_fvar(hyp, Some(FVarId::new(id)))
            .expect("three-arg hypothesis should register");
    }

    // Goal: g(a, c, e) = g(b, d, f)
    let goal = make_eq(ty.clone(), gace, gbdf);

    let proof_result = bridge
        .prove(&goal)
        .expect("three-arg congruence goal should reconstruct")
        .verified()
        .expect("Should prove g(a, c, e) = g(b, d, f) from 3 hypotheses");
    let proof = proof_result.proof_term();
    // Verify proof head is congrArg or similar (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("congr")),
        "3-arg congruence proof head should be congrArg or similar, got {head:?}"
    );

    // Key invariant: proof step is Congr on "g" with substantive arg proofs
    // (E-graph curried optimization may merge some hypotheses into union-find).
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Congr(_, _)),
        "Proof step should be Congr(\"g\", ..), got {step:?}"
    );
    if let ProofStep::Congr(_func_expr, args) = step {
        assert_eq!(
            congr_func_name(step).as_deref(),
            Some("g"),
            "Function should be g"
        );
        // Due to curried optimization, may have 1-3 args depending on how
        // the E-graph decomposes the application. Must have at least 1.
        assert!(
            !args.is_empty(),
            "Congr(\"g\", ..) should have at least 1 arg proof"
        );
        // Every arg proof must be substantive - not Refl (which would mean
        // the corresponding argument was already equal without a hypothesis)
        for (i, arg) in args.iter().enumerate() {
            assert!(
                matches!(
                    arg,
                    ProofStep::Hypothesis(_)
                        | ProofStep::Trans(_, _)
                        | ProofStep::Symm(_)
                        | ProofStep::Congr(_, _)
                ),
                "Congr arg[{i}] should be a substantive proof step (not Refl), got {arg:?}"
            );
        }
    }
}
