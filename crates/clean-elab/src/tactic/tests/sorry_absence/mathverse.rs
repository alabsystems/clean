// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Build env with Nat, False, Even, Odd for parity contradiction tests.
fn setup_env_with_parity() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_true_false().unwrap();
    let nat_to_prop = Expr::arrow(Expr::const_(Name::from_string("Nat"), vec![]), Expr::prop());
    for name in ["Even", "Odd"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_to_prop.clone(),
        })
        .unwrap();
    }
    env
}

#[test]
#[serial]
fn test_mathverse_parity_fail_closed_without_non_kernel_terms() {
    reset_all_counters();
    let env = setup_env_with_parity();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n_fvar = FVarId::new(0);
    let even_ty = Expr::app(
        Expr::const_(Name::from_string("Even"), vec![]),
        Expr::fvar(n_fvar),
    );
    let odd_ty = Expr::app(
        Expr::const_(Name::from_string("Odd"), vec![]),
        Expr::fvar(n_fvar),
    );
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);

    let mut state = ProofState::with_context(
        env,
        false_ty,
        vec![
            LocalDecl {
                fvar: n_fvar,
                name: "n".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_even".to_string(),
                ty: even_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h_odd".to_string(),
                ty: odd_ty,
                value: None,
            },
        ],
    );

    let before = sorry_count();
    let result = omega(&mut state);
    let after = sorry_count();
    let sorry_used = after - before;
    let arith_used = arith_proof_count();
    let ay_used = ay_proof_count();

    let total_non_kernel = sorry_used + arith_used + ay_used;
    assert!(
        matches!(result, Err(TacticError::ArithmeticFailed { ref tactic, .. }) if tactic == "mathverse"),
        "mathverse should fail closed on bare Even/Odd axioms, got: {result:?}"
    );
    assert!(
        total_non_kernel == 0,
        "REGRESSION: mathverse used {} non-kernel proof terms on unsupported parity contradiction \
         (sorry={}, trustedArith={}, trustedAy={}, expected 0)",
        total_non_kernel,
        sorry_used,
        arith_used,
        ay_used
    );
    assert!(
        !state.is_complete(),
        "fail-closed mathverse should leave the parity goal open"
    );
}
