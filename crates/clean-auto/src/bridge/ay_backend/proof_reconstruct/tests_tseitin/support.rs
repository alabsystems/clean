// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for Tseitin rule-family tests.

use super::{Declaration, Environment, Expr, Level, Name, Sort, TermStore, VariableMapping};

/// Create an environment with Or, And, Classical.em, Eq, Int, absurd, and test axioms.
pub(super) fn mk_env_with_classical() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testA", "testB", "testC"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .expect("test axiom insertion should succeed");
    }
    env
}

/// Build `@Eq.{1} Int x y`.
pub(super) fn mk_eq_int(x: &str, y: &str) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), int_ty),
            Expr::const_(Name::from_string(x), vec![]),
        ),
        Expr::const_(Name::from_string(y), vec![]),
    )
}

/// Build ay terms for an and_pos/and_neg scenario: `And(p, q)` where
/// `p = (a=b)` and `q = (b=c)`.
///
/// Returns `(terms, map, ay_p, ay_q, ay_and_pq, ay_not_and_pq)`.
pub(super) fn mk_binary_and_terms() -> (
    TermStore,
    VariableMapping,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
    ay_core::TermId,
) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ay_a = terms.mk_var("fvar_1", Sort::Int);
    let ay_b = terms.mk_var("fvar_2", Sort::Int);
    let ay_c = terms.mk_var("fvar_3", Sort::Int);

    map.register_var(
        "fvar_1",
        Expr::const_(Name::from_string("testA"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_2",
        Expr::const_(Name::from_string("testB"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_3",
        Expr::const_(Name::from_string("testC"), vec![]),
        int_ty,
    );

    let ay_p = terms.mk_eq(ay_a, ay_b);
    let ay_q = terms.mk_eq(ay_b, ay_c);
    let ay_and_pq = terms.mk_and(vec![ay_p, ay_q]);
    // Use mk_not_raw to preserve Not(And(...)) - mk_not applies De Morgan.
    // In real proofs, the sat_proof_manager uses raw negation for clause literals.
    let ay_not_and_pq = terms.mk_not_raw(ay_and_pq);

    (terms, map, ay_p, ay_q, ay_and_pq, ay_not_and_pq)
}
