// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_auto::AutomationEngine;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, LocalContext, Name};
use std::time::Duration;

fn setup_eq_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("Eq should initialize");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("A should register");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: a_ty.clone(),
        })
        .unwrap_or_else(|_| panic!("add {name}"));
    }

    env
}

fn make_eq(type_: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                type_,
            ),
            lhs,
        ),
        rhs,
    )
}

#[test]
fn test_auto_prove_uses_local_context_hypotheses() {
    let env = setup_eq_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let goal = make_eq(a_ty, a, b);
    let engine = AutomationEngine::new();

    assert!(
        engine
            .auto_prove(&env, &goal, Duration::from_secs(5), None)
            .is_none(),
        "auto_prove should not prove a = b without supporting hypotheses"
    );

    let mut local_ctx = LocalContext::new();
    local_ctx.push_with_id(
        FVarId::new(42),
        Name::from_string("h"),
        goal.clone(),
        BinderInfo::Default,
    );

    let result = engine
        .auto_prove(&env, &goal, Duration::from_secs(5), Some(&local_ctx))
        .expect("auto_prove should use local_ctx hypotheses to prove the goal");

    let proof_context = result
        .proof_context()
        .expect("local_ctx-backed proof should preserve the proof context");
    let names: Vec<String> = proof_context
        .iter()
        .map(|decl| decl.name.to_string())
        .collect();
    assert_eq!(names, vec!["h".to_string()]);

    let inferred = result.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "auto_prove local-context proof should type-check: {:?}",
        inferred.err()
    );
}
