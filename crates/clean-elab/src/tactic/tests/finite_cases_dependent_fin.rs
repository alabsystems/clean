// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for dependent `fin_cases` fallback proofs on `Fin n`.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;

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
    let is_lt = crate::tactic::norm_num_ext::build_nat_le_witness(value + 1, bound);
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

fn expect_fin_mk_value(goal: &Goal, expected_bound: u64, expected_value: u64) {
    let hyp = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("dependent Fin sub-goal should keep hypothesis h in context");
    let value = hyp
        .value
        .as_ref()
        .expect("dependent Fin sub-goal should assign h a constructor value");
    let args = value.get_app_args();

    assert!(
        matches!(value.get_app_fn().kind(), ExprKind::Const(name, _) if name.to_string() == "Fin.mk"),
        "dependent Fin sub-goal should assign a Fin.mk constructor, got: {value:?}"
    );
    assert_eq!(args.len(), 3, "Fin.mk should be fully applied in sub-goals");
    assert_eq!(*args[0], make_nat_literal(expected_bound));
    assert_eq!(*args[1], make_nat_literal(expected_value));
    // The `isLt` witness is now a constructive `Nat.le` proof (a
    // `Nat.le.refl` / `Nat.le.step` chain), not the old ill-typed `False`
    // placeholder.
    let witness_head = args[2].get_app_fn();
    assert!(
        matches!(witness_head.kind(), ExprKind::Const(name, _)
            if matches!(name.to_string().as_str(), "Nat.le.refl" | "Nat.le.step")),
        "Fin.mk isLt witness should be a Nat.le.refl/step proof, got: {:?}",
        args[2]
    );
}

/// `fin_cases` should preserve dependent targets on the Or.rec fallback path
/// while assigning constructor values to the split hypothesis.
#[test]
fn test_fin_cases_fin3_dependent_target_succeeds() {
    let env = setup_env_for_dependent_fin_cases();
    let fin3_ty = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        make_nat_literal(3),
    );
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    let mut state = ProofState::new(env, Expr::prop());
    let h_fvar = state.fresh_fvar();
    state.goals[0].target = Expr::app(r_const.clone(), Expr::fvar(h_fvar));
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_fvar,
        name: "h".to_string(),
        ty: fin3_ty,
        value: None,
    });

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
        expect_fin_mk_value(goal, 3, idx as u64);
    }
}

#[test]
fn test_fin_cases_fin3_branch_accepts_specialized_proof_via_let_binding() {
    let env = setup_env_for_dependent_fin_cases();
    let fin3_ty = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        make_nat_literal(3),
    );
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    let mut state = ProofState::new(env, Expr::prop());
    let h_fvar = state.fresh_fvar();
    state.goals[0].target = Expr::app(r_const, Expr::fvar(h_fvar));
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: h_fvar,
        name: "h".to_string(),
        ty: fin3_ty,
        value: None,
    });

    fin_cases(&mut state, "h").expect("fin_cases should split a dependent Fin goal");
    let first_goal = state
        .current_goal()
        .expect("fin_cases should leave the first branch as the current goal")
        .clone();

    let _ = state
        .verify_proof(&first_goal, &Expr::const_(Name::from_string("r0"), vec![]))
        .expect("branch-local let-binding should let a specialized proof inhabit R h");
}
