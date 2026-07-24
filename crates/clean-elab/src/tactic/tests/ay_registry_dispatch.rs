// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for ay tactic registration and dispatch through
//! the production [`TacticRegistry`].
//!
//! Part of #2427: verifies that the pipeline activation wiring connects
//! ay tactics to production dispatch (Gate 1 of the activation design).

use super::*;
use crate::tactic::builtins::register_builtin_tactics;
use crate::tactic::registry::TacticRegistry;
use clean_kernel::env::Declaration;

/// Verify ay tactics are registered in the production TacticRegistry.
///
/// This is the core activation test for #2427: the pipeline has zero
/// production callers unless these names resolve in the registry.
#[test]
fn test_ay_tactics_registered_in_production_registry() {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    for name in ["ay_omega", "ay_bv", "ay_smt", "ay_decide", "ay_lra"] {
        assert!(
            registry.get(name).is_some(),
            "{name} should be registered in production TacticRegistry"
        );
    }
}

/// Dispatch ay_decide through the registry handler and close a reflexivity goal.
///
/// Tests the full handler path: registry.get("ay_decide") -> handler closure
/// -> ay_decide(ps, AyConfig::from_env()) -> goal closed.
#[test]
fn test_ay_decide_registry_dispatch_closes_goal() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_trusted_ay().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);

    let entry = registry
        .get("ay_decide")
        .expect("ay_decide must be registered");

    // Goal: a = a (reflexivity — provable by any SMT solver or decide fallback)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            a.clone(),
        ),
        a,
    );

    let mut ps = ProofState::new(env, target);
    (entry.handler)(&mut ps, &[]).expect("ay_decide registry handler should close reflexivity");

    assert!(
        ps.is_complete(),
        "goal should be closed after registry dispatch"
    );
}
