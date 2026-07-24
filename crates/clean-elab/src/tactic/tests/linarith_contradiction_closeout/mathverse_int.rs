// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse-delegated Int contradiction-closeout regressions.

use super::*;

fn int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

#[test]
fn test_mathverse_delegation_int_contradiction_produces_false_proof() {
    use crate::tactic::arith_mathverse_proof::build_mathverse_proof;
    use crate::tactic::omega_tactic::{MathverseCertificate, MathverseContradictionType};

    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize for mathverse Int contradiction test");
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_int_le_tc(int_ofnat(5), int_ofnat(3));
    let mut state = ProofState::with_context(
        env.clone(),
        false_const,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );
    let goal = state.current_goal().expect("should have a goal").clone();

    let cert = MathverseCertificate {
        coefficients: vec![1],
        uses_goal_negation: false,
        contradiction_type: MathverseContradictionType::Arithmetic,
    };
    let proof = build_mathverse_proof(&state, &goal, &cert, &[h_id], &env)
        .expect("mathverse Int contradiction should reconstruct a False proof");
    assert_ne!(
        proof,
        Expr::fvar(h_id),
        "mathverse Int contradiction proof must not be the raw inequality hypothesis"
    );
    assert!(
        expr_contains_const(&proof, "Int.NonNeg.casesOn"),
        "mathverse Int contradiction should use the Int NonNeg closeout path"
    );

    let result = state.close_goal(&goal, proof);
    assert!(
        result.is_ok(),
        "close_goal should accept mathverse's Int contradiction proof, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "mathverse Int contradiction proof should close the goal"
    );
}
