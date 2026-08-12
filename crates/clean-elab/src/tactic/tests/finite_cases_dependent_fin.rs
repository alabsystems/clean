// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for dependent `fin_cases` fallback proofs on `Fin n`.

use super::*;
use clean_kernel::env::Declaration;

fn setup_env_for_dependent_fin_cases() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_fin().unwrap();
    env.init_classical().unwrap();

    let fin3_ty = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        make_nat_literal(3),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("R"),
        level_params: vec![],
        type_: Expr::arrow(fin3_ty, Expr::prop()),
    })
    .unwrap();

    for value in 0..3 {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&format!("r{value}")),
            level_params: vec![],
            type_: Expr::app(
                Expr::const_(Name::from_string("R"), vec![]),
                make_fin_literal(3, value),
            ),
        })
        .unwrap();
    }

    env
}

fn make_fin_literal(bound: u64, value: u64) -> Expr {
    // `Fin.mk`'s `isLt` slot needs a real proof of `Nat.lt value bound`
    // (defeq `Nat.le (value+1) bound`); build the constructive witness so the
    // `r{value}` axioms kernel-check. `isLt` is proof-irrelevant, so this need
    // not be byte-identical to the witness `fin_cases` synthesizes.
    let is_lt = norm_num_ext::build_nat_le_witness(value + 1, bound);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Fin.mk"), vec![]),
                make_nat_literal(bound),
            ),
            make_nat_literal(value),
        ),
        is_lt,
    )
}

fn expect_fin_case_scope(goal: &Goal, has_proved_equality: bool) {
    let hyp = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("dependent Fin sub-goal should keep hypothesis h in context");
    assert!(
        hyp.value.is_none(),
        "fallback cases must not fake a let value"
    );
    assert_eq!(
        goal.local_ctx.iter().any(|decl| decl.name == "h_eq"),
        has_proved_equality,
        "only a branch introduced by an equality lambda may expose h_eq"
    );
}

/// `fin_cases` should preserve dependent targets on the Or.rec fallback path
/// while exposing only equality hypotheses established by the Or.rec proof.
#[test]
fn test_fin_cases_fin3_dependent_target_succeeds() {
    let env = setup_env_for_dependent_fin_cases();
    let fin3_ty = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        make_nat_literal(3),
    );
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    let h_fvar = FVarId::new(0);
    let target = Expr::app(r_const.clone(), Expr::fvar(h_fvar));
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: fin3_ty,
            value: None,
        }],
    );

    let result = fin_cases(&mut state, "h");
    assert!(
        result.is_ok(),
        "fin_cases Fin 3 with dependent target should succeed, got: {result:?}"
    );
    assert_eq!(state.goals.len(), 3, "Fin 3 should create 3 sub-goals");

    for (idx, goal) in state.goals.iter().enumerate() {
        assert_eq!(
            goal.target,
            Expr::app(r_const.clone(), Expr::fvar(h_fvar)),
            "dependent Fin sub-goals should preserve the original target"
        );
        expect_fin_case_scope(goal, idx + 1 < state.goals.len());
    }
}

#[test]
fn test_fin_cases_fin3_branch_requires_equality_transport() {
    let env = setup_env_for_dependent_fin_cases();
    let fin3_ty = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        make_nat_literal(3),
    );
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    let h_fvar = FVarId::new(0);
    let target = Expr::app(r_const, Expr::fvar(h_fvar));
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: fin3_ty,
            value: None,
        }],
    );

    fin_cases(&mut state, "h").expect("fin_cases should split a dependent Fin goal");
    let first_goal = state
        .current_goal()
        .expect("fin_cases should leave the first branch as the current goal")
        .clone();

    let result = state.verify_proof(&first_goal, &Expr::const_(Name::from_string("r0"), vec![]));
    assert!(
        result.is_err(),
        "a specialized proof of R 0 must not inhabit R h without using h_eq transport"
    );
    assert!(first_goal.local_ctx.iter().any(|decl| decl.name == "h_eq"));
}
