// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! byContradiction goal wrapper tests.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker};

/// Build fixture for byContradiction test:
/// - Goal: Eq Nat testA testB
/// - Hypothesis: h_eq : Eq Nat testA testB (FVarId 100)
/// - Negated goal clause (from clausify_goal): testA ≠ testB (clause 0, FVarId 0)
/// - Hypothesis clause: testA = testB (clause 1, FVarId 100)
fn mk_by_contradiction_fixture() -> RefutationFixture {
    let mut env = mk_env_with_test_constants();
    env.init_classical().expect("init_classical");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_a_b = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u1]),
                nat_ty.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    );
    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );

    // FVarId 0 is the negated goal hypothesis (bound by byContradiction lambda)
    // FVarId 100 is the actual hypothesis h_eq
    let h_eq_id = FVarId::new(100);
    let mut ctx = LocalContext::new();
    // Only the real hypothesis goes in the type-checking context
    // (FVarId 0 will be abstracted over by reconstruct_goal)
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_a_b.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty);

    // Clause 0: negated goal (testA ≠ testB) with FVarId 0
    map.add_input_clause(0, FVarId::new(0), neq_a_b);
    // Clause 1: hypothesis (testA = testB) with FVarId 100
    map.add_input_clause(1, h_eq_id, eq_a_b.clone());

    // Set goal info for byContradiction wrapper
    map.set_goal_info(eq_a_b, 1);

    RefutationFixture { env, ctx, map }
}

/// Build trace: goal refutation for byContradiction.
///
/// c0: testA ≠ testB (negated goal, input)
/// c1: testA = testB (hypothesis, input)
/// c2: Superposition(c1, c0, root) → testB ≠ testB
/// c3: EqualityResolution(c2) → ⊥
fn mk_by_contradiction_trace() -> ProofTrace {
    let c0 = mk_input_neq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_eq(1, Term::Const(0), Term::Const(1));
    let c2 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(1),
            positive: false,
        }],
        id: 2,
        parents: vec![1, 0],
        inference: Inference::Superposition(1, 0, Position::root()),
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

/// End-to-end: reconstruct_goal() produces a proof of the goal via byContradiction.
///
/// Goal: Eq Nat testA testB. Hypothesis: h_eq : Eq Nat testA testB.
/// The prover refutes ¬(testA = testB) using h_eq, then reconstruct_goal()
/// wraps with Classical.byContradiction to produce a proof of testA = testB.
#[test]
fn test_reconstruct_goal_by_contradiction_type_checks() {
    let f = mk_by_contradiction_fixture();
    let trace = mk_by_contradiction_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let (proof, desc) = reconstructor
        .reconstruct_goal()
        .expect("byContradiction goal reconstruction should succeed");

    assert!(
        desc.contains("byContradiction"),
        "description should mention byContradiction"
    );

    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "byContradiction goal proof type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    let ty = tc.whnf(&ty);

    // Should be Eq Nat testA testB
    let (head, args) = {
        let mut e = &ty;
        let mut args = Vec::new();
        while let ExprKind::App(func, a) = e.kind() {
            args.push(a.as_ref());
            e = func;
        }
        args.reverse();
        (e, args)
    };

    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Eq")),
        "byContradiction goal proof type should be Eq(...), got {:?}",
        ty
    );
    assert_eq!(args.len(), 3, "Eq should have 3 args (type, lhs, rhs)");
}
