// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for superposition_reconstruction e2e tests.

use super::super::*;
use crate::superposition::{Clause, Inference, Literal, Term};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, ExprKind, Level, LocalContext, TypeChecker};

/// Create an environment with Eq, Nat, Not/absurd/False, and two fresh Nat axioms.
pub(super) fn mk_env_with_test_constants() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testA"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .expect("add testA");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testB"),
        level_params: vec![],
        type_: nat_ty,
    })
    .expect("add testB");
    env
}

/// Shared fixture for refutation tests using abstract Nat constants.
pub(super) struct RefutationFixture {
    pub(super) env: Environment,
    pub(super) ctx: LocalContext,
    pub(super) map: SymbolMap,
}

/// Build a literal from components.
pub(super) fn mk_lit(lhs: Term, rhs: Term, positive: bool) -> Literal {
    Literal { lhs, rhs, positive }
}

/// Build a unit equation input clause: `lhs = rhs`.
pub(super) fn mk_input_eq(id: u64, lhs: Term, rhs: Term) -> Clause {
    Clause {
        literals: vec![Literal {
            lhs,
            rhs,
            positive: true,
        }],
        id,
        parents: vec![],
        inference: Inference::Input,
    }
}

/// Build a negated equation input clause: `lhs ≠ rhs`.
pub(super) fn mk_input_neq(id: u64, lhs: Term, rhs: Term) -> Clause {
    Clause {
        literals: vec![Literal {
            lhs,
            rhs,
            positive: false,
        }],
        id,
        parents: vec![],
        inference: Inference::Input,
    }
}

/// Assert that a proof term type-checks to False.
pub(super) fn assert_proof_type_checks_to_false(
    env: &Environment,
    ctx: LocalContext,
    proof: &Expr,
    msg: &str,
) {
    let tc = TypeChecker::with_context(env, ctx);
    let result = tc.infer_type(proof);
    assert!(
        result.is_ok(),
        "{msg}: type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");
    assert!(
        matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
        "{msg}: expected type False, got {:?}",
        ty.kind(),
    );
}

/// Helper: build Eq expression `@Eq.{u} ty a b`
pub(super) fn mk_eq(ty: &Expr, a: &Expr, b: &Expr, u: &Level) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u.clone()]),
                ty.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Helper: build Or expression `@Or a b`
pub(super) fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

/// Create an environment with Eq, Nat, Not/absurd/False, Or/Classical.em,
/// and three fresh Nat axioms (testA, testB, testC).
pub(super) fn mk_env_with_three_test_constants() -> Environment {
    let mut env = mk_env_with_test_constants();
    env.init_classical().expect("init_classical");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testC"),
        level_params: vec![],
        type_: nat_ty,
    })
    .expect("add testC");
    env
}

/// Build environment with testA, testB, testC, testD : Nat for Or-goal tests.
pub(super) fn mk_env_with_four_constants() -> Environment {
    let mut env = mk_env_with_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testC"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .expect("add testC");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testD"),
        level_params: vec![],
        type_: nat_ty,
    })
    .expect("add testD");
    env
}

pub(super) fn mk_env_with_six_constants() -> Environment {
    let mut env = mk_env_with_four_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testE"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .expect("add testE");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testF"),
        level_params: vec![],
        type_: nat_ty,
    })
    .expect("add testF");
    env
}
