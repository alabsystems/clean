// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-clause Or-goal tests.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker};

/// Fixture for multi-clause Or-goal test:
///
/// Goal: Or (Eq Nat testA testB) (Eq Nat testC testD)
/// Hypothesis: h_eq : Eq Nat testA testB (FVarId 100)
///
/// Negated goal produces 2 clauses:
/// - Clause 0 (FVarId 0): testA ≠ testB
/// - Clause 1 (FVarId 1): testC ≠ testD
fn mk_or_goal_fixture() -> RefutationFixture {
    let mut env = mk_env_with_four_constants();
    env.init_classical().expect("init_classical");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let d = Expr::const_(Name::from_string("testD"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_a_b = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
                nat_ty.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    );
    let eq_c_d = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u1]),
                nat_ty.clone(),
            ),
            c.clone(),
        ),
        d.clone(),
    );

    // Goal: Or (Eq Nat testA testB) (Eq Nat testC testD)
    let or_goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            eq_a_b.clone(),
        ),
        eq_c_d.clone(),
    );

    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );
    let neq_c_d = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_c_d);

    let h_eq_id = FVarId::new(100);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_a_b.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty.clone());
    map.add_symbol(2, c, nat_ty.clone());
    map.add_symbol(3, d, nat_ty);

    // Clause 0: negated first disjunct (testA ≠ testB) with FVarId 0
    map.add_input_clause(0, FVarId::new(0), neq_a_b);
    // Clause 1: negated second disjunct (testC ≠ testD) with FVarId 1
    map.add_input_clause(1, FVarId::new(1), neq_c_d);
    // Clause 2: hypothesis (testA = testB) with FVarId 100
    map.add_input_clause(2, h_eq_id, eq_a_b);

    // 2 goal clauses (Or-goal)
    map.set_goal_info(or_goal, 2);

    RefutationFixture { env, ctx, map }
}

/// Build trace: Or-goal refutation using first disjunct.
///
/// c0: testA ≠ testB (negated first disjunct, input)
/// c1: testC ≠ testD (negated second disjunct, input)
/// c2: testA = testB (hypothesis, input)
/// c3: Superposition(c2, c0, root) → testB ≠ testB
/// c4: EqualityResolution(c3) → ⊥
fn mk_or_goal_trace() -> ProofTrace {
    let c0 = mk_input_neq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_neq(1, Term::Const(2), Term::Const(3));
    let c2 = mk_input_eq(2, Term::Const(0), Term::Const(1));
    let c3 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(1),
            positive: false,
        }],
        id: 3,
        parents: vec![2, 0],
        inference: Inference::Superposition(2, 0, Position::root()),
    };
    let c4 = Clause {
        literals: vec![],
        id: 4,
        parents: vec![3],
        inference: Inference::EqualityResolution(3),
    };
    ProofTrace {
        empty_clause: c4.clone(),
        clauses: vec![c0, c1, c2, c3, c4],
    }
}

/// End-to-end: reconstruct_goal() handles multi-clause Or-goals.
///
/// Goal: Or (Eq Nat testA testB) (Eq Nat testC testD)
/// Hypothesis: h_eq : Eq Nat testA testB
///
/// The prover refutes ¬(a=b) ∧ ¬(c=d) using h_eq to contradict ¬(a=b).
/// reconstruct_goal() decomposes h : ¬(P ∨ Q) into ¬P and ¬Q, substitutes
/// them for FVar(0) and FVar(1), and wraps with byContradiction.
#[test]
fn test_reconstruct_goal_multi_clause_or_type_checks() {
    let f = mk_or_goal_fixture();
    let trace = mk_or_goal_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let (proof, desc) = reconstructor
        .reconstruct_goal()
        .expect("multi-clause Or-goal reconstruction should succeed");

    assert!(
        desc.contains("byContradiction"),
        "description should mention byContradiction"
    );

    // Type-check: proof should have type Or (Eq Nat testA testB) (Eq Nat testC testD)
    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "multi-clause Or-goal proof type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    let ty = tc.whnf(&ty);

    // Verify the type is Or(...)
    let (head, _args) = {
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
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Or")),
        "multi-clause Or-goal proof type should be Or(...), got {:?}",
        ty
    );
}

/// Test that extract_or_disjuncts correctly decomposes Or chains.
#[test]
fn test_extract_or_disjuncts() {
    use super::super::proof_helpers::extract_or_disjuncts;

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    // Single proposition
    assert_eq!(extract_or_disjuncts(&p).len(), 1);

    // Or P Q → [P, Q]
    let or_pq = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p.clone()),
        q.clone(),
    );
    let disjuncts = extract_or_disjuncts(&or_pq);
    assert_eq!(disjuncts.len(), 2);
    assert_eq!(disjuncts[0], p);
    assert_eq!(disjuncts[1], q);

    // Or P (Or Q R) → [P, Q, R]
    let or_qr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), q.clone()),
        r.clone(),
    );
    let or_p_qr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p.clone()),
        or_qr,
    );
    let disjuncts = extract_or_disjuncts(&or_p_qr);
    assert_eq!(disjuncts.len(), 3);
    assert_eq!(disjuncts[0], p);
    assert_eq!(disjuncts[1], q);
    assert_eq!(disjuncts[2], r);
}
