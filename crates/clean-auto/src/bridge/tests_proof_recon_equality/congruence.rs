// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Congruence-oriented equality proof-reconstruction coverage.

use super::*;

#[test]
fn test_proof_reconstruction_congruence() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fa = Expr::app(f.clone(), a.clone());
    let fb = Expr::app(f, b.clone());

    // Add hypothesis h : a = b with FVarId
    let hyp_fvar = FVarId::new(1);
    let hyp = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp, Some(hyp_fvar))
        .expect("congruence hypothesis should register");

    // Goal: f(a) = f(b) (needs congruence)
    let goal = make_eq(a_ty, fa, fb);

    let result = bridge
        .prove(&goal)
        .expect("congruence goal should reconstruct");
    assert!(
        result.is_verified(),
        "Should prove f(a) = f(b) from h : a = b"
    );

    let proof_result = result
        .verified()
        .expect("congruence result should be verified");

    // The proof should be congrArg applied to f and h
    let proof = proof_result.proof_term();
    // Verify proof head is congrArg (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("congr")),
        "Congruence proof head should be congrArg or similar, got {head:?}"
    );

    // Proof step must be Congr(f_expr, [Hypothesis(1)])
    let step = proof_result.proof_step();
    assert!(
        matches!(step, ProofStep::Congr(_, _)),
        "Proof step should be Congr(\"f\", ..), got {step:?}"
    );
    if let ProofStep::Congr(func_expr, args) = step {
        assert_eq!(
            congr_func_name(step).as_deref(),
            Some("f"),
            "Congruence function should be f, got {func_expr:?}"
        );
        assert_eq!(
            args.len(),
            1,
            "Congr(\"f\", ..) for f(a)=f(b) should have exactly 1 arg proof, got {}",
            args.len()
        );
        assert!(
            matches!(&args[0], ProofStep::Hypothesis(fvar) if fvar.as_u64() == 1),
            "Congr arg should be Hypothesis(1) for h: a=b, got {:?}",
            args[0]
        );
    }
}

#[test]
fn test_proof_reconstruction_nested_congruence() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let ffa = Expr::app(f.clone(), Expr::app(f.clone(), a.clone())); // f(f(a))
    let ffb = Expr::app(f.clone(), Expr::app(f, b.clone())); // f(f(b))

    // Add hypothesis h : a = b
    let hyp_fvar = FVarId::new(1);
    let hyp = make_eq(a_ty.clone(), a.clone(), b.clone());
    bridge
        .add_hypothesis_with_fvar(&hyp, Some(hyp_fvar))
        .expect("nested congruence hypothesis should register");

    // Goal: f(f(a)) = f(f(b)) (needs nested congruence)
    let goal = make_eq(a_ty, ffa, ffb);

    let result = bridge
        .prove(&goal)
        .expect("nested congruence goal should reconstruct");
    assert!(
        result.is_verified(),
        "Should prove f(f(a)) = f(f(b)) from h : a = b"
    );
    let proof_result = result
        .verified()
        .expect("nested congruence result should be verified");
    let proof = proof_result.proof_term();
    // Verify proof head is congrArg or similar (not just any application)
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string().contains("congr")),
        "Nested congruence proof head should be congrArg or similar, got {head:?}"
    );

    // Nested congruence: Congr("f", [Congr("f", [Hypothesis(1)])])
    // For f(f(a)) = f(f(b)) from h: a=b, the outer Congr("f") must contain
    // an inner Congr("f") that wraps the hypothesis - a bare Hypothesis would
    // mean f(a)=f(b) which is only one level of congruence.
    let step = proof_result.proof_step();
    fn count_congr_depth(step: &ProofStep, func_name: &str) -> usize {
        match step {
            ProofStep::Congr(f_expr, args) => {
                let matches_name = matches!(f_expr.kind(), ExprKind::Const(ref n, _) if n.to_string() == func_name);
                let sub_max = args
                    .iter()
                    .map(|a| count_congr_depth(a, func_name))
                    .max()
                    .unwrap_or(0);
                if matches_name {
                    1 + sub_max
                } else {
                    sub_max
                }
            }
            ProofStep::Symm(inner) => count_congr_depth(inner, func_name),
            ProofStep::Trans(l, r) => {
                count_congr_depth(l, func_name).max(count_congr_depth(r, func_name))
            }
            _ => 0,
        }
    }
    assert!(
        matches!(step, ProofStep::Congr(_, _)),
        "Proof step should be Congr(\"f\", ..), got {step:?}"
    );
    if let ProofStep::Congr(_func_expr, args) = step {
        assert_eq!(
            congr_func_name(step).as_deref(),
            Some("f"),
            "Outer congruence should be on function f"
        );
        assert!(
            !args.is_empty(),
            "Congr(\"f\", ..) should have at least 1 arg proof"
        );
        // f(f(a)) = f(f(b)) requires at least depth-2 Congr("f") nesting:
        // the outer f(_)=f(_) and the inner f(a)=f(b).
        let depth = count_congr_depth(step, "f");
        assert!(
            depth >= 2,
            "Nested congruence f(f(a))=f(f(b)) requires at least 2 levels of \
             Congr(\"f\"), got depth {depth} in {step:?}"
        );
        // The innermost leaf proof must be the hypothesis (a=b)
        fn has_hypothesis_leaf(step: &ProofStep) -> bool {
            match step {
                ProofStep::Hypothesis(_) => true,
                ProofStep::Congr(_, args) => args.iter().any(has_hypothesis_leaf),
                ProofStep::Symm(inner) => has_hypothesis_leaf(inner),
                ProofStep::Trans(l, r) => has_hypothesis_leaf(l) || has_hypothesis_leaf(r),
                _ => false,
            }
        }
        assert!(
            has_hypothesis_leaf(step),
            "Nested congruence must bottom out at the hypothesis h: a=b, got {step:?}"
        );
    }
}
