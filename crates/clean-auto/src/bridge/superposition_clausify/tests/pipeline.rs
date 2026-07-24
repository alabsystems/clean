// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end clausify pipeline tests.

use super::super::*;
use super::support::{mk_eq, mk_nat_env_with_test_consts};
use clean_kernel::{ExprKind, Level, LocalContext};

fn mk_eq_refutation_trace(eq_lit: &Literal, neq_lit: &Literal) -> crate::superposition::ProofTrace {
    use crate::superposition::{Clause, Inference, Literal as SupLiteral, Position, ProofTrace};

    let c0 = Clause {
        literals: vec![eq_lit.clone()],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let c1 = Clause {
        literals: vec![neq_lit.clone()],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    let c2 = Clause {
        literals: vec![SupLiteral {
            lhs: eq_lit.rhs.clone(),
            rhs: eq_lit.rhs.clone(),
            positive: false,
        }],
        id: 2,
        parents: vec![0, 1],
        inference: Inference::Superposition(0, 1, Position::root()),
    };
    let c3 = Clause {
        literals: vec![],
        id: 3,
        parents: vec![2],
        inference: Inference::EqualityResolution(2),
    };
    ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c0, c1, c2, c3],
    }
}

#[test]
fn test_superposition_proves_reflexive_eq() {
    use crate::superposition::{ProverResult, SuperpositionProver};

    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let goal = mk_eq(nat, a.clone(), a);

    let (clause_sets, _) = clausifier.clausify_goal(&goal);
    assert_eq!(clause_sets.len(), 1);

    let mut prover = SuperpositionProver::new();
    for literals in &clause_sets {
        prover.add_clause(literals.clone());
    }

    let result = prover.prove(1000);
    assert!(
        matches!(result, ProverResult::Unsatisfiable(_)),
        "should refute a != a"
    );
}

#[test]
fn test_clausify_reconstruct_type_checks() {
    use crate::bridge::superposition_reconstruction::SuperpositionReconstructor;

    let (env, nat_ty, a, b) = mk_nat_env_with_test_consts();
    let u1 = Level::succ(Level::zero());

    let eq_a_b = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), nat_ty),
            a,
        ),
        b,
    );
    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );

    let (h_eq_id, h_neq_id) = (FVarId::new(10), FVarId::new(20));
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_a_b.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_neq_id,
        Name::from_string("h_neq"),
        neq_a_b.clone(),
        BinderInfo::Default,
    );

    let mut clausifier = GoalClausifier::new_with_env(&env);
    let eq_clauses = clausifier.clausify_hypothesis(&eq_a_b, 0, h_eq_id);
    let neq_clauses = clausifier.clausify_hypothesis(&neq_a_b, 1, h_neq_id);
    assert_eq!(eq_clauses.len(), 1);
    assert_eq!(neq_clauses.len(), 1);

    let trace = mk_eq_refutation_trace(&eq_clauses[0][0], &neq_clauses[0][0]);
    let symbol_map = clausifier.into_symbol_map();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &symbol_map, &env);
    let (proof, _desc) = reconstructor
        .reconstruct()
        .expect("clausifier-to-reconstructor pipeline should succeed");

    let tc = TypeChecker::with_context(&env, ctx);
    let ty = tc
        .infer_type(&proof)
        .unwrap_or_else(|error| panic!("e2e proof type-check failed: {error:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Const(name, _) if *name == Name::from_string("False")),
        "e2e pipeline proof should type-check to False, got {:?}",
        ty.kind(),
    );
}
