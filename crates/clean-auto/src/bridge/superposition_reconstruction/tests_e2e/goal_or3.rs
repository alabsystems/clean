// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! 3-disjunct Or goal tests.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker};

// ================================================================
// 3-disjunct Or goal: (a = b) ∨ (c = d) ∨ (e = f)
//
// Verifies that build_multi_clause_body handles >2 disjuncts correctly.
// The right-associative Or chain Or P (Or Q R) produces 3 clauses:
//   c0: a ≠ b (negated first disjunct)
//   c1: c ≠ d (negated second disjunct)
//   c2: e ≠ f (negated third disjunct)
//
// The proof injects into the 3-way Or chain via Or.inl / Or.inr ∘ Or.inl / Or.inr ∘ Or.inr.
// ================================================================

/// Fixture for 3-disjunct Or-goal test:
///
/// Goal: Or (Eq Nat a b) (Or (Eq Nat c d) (Eq Nat e f))
/// Hypothesis: h_eq : Eq Nat a b (FVarId 100)
///
/// Negated goal produces 3 clauses:
/// - Clause 0 (FVarId 0): a ≠ b
/// - Clause 1 (FVarId 1): c ≠ d
/// - Clause 2 (FVarId 2): e ≠ f
fn mk_or3_goal_fixture() -> RefutationFixture {
    let mut env = mk_env_with_six_constants();
    env.init_classical().expect("init_classical");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let d = Expr::const_(Name::from_string("testD"), vec![]);
    let e = Expr::const_(Name::from_string("testE"), vec![]);
    let f = Expr::const_(Name::from_string("testF"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_a_b = mk_eq(&nat_ty, &a, &b, &u1);
    let eq_c_d = mk_eq(&nat_ty, &c, &d, &u1);
    let eq_e_f = mk_eq(&nat_ty, &e, &f, &u1);

    // Goal: Or (Eq a b) (Or (Eq c d) (Eq e f))  — right-associative
    let or_cd_ef = mk_or(&eq_c_d, &eq_e_f);
    let or3_goal = mk_or(&eq_a_b, &or_cd_ef);

    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );
    let neq_c_d = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_c_d.clone(),
    );
    let neq_e_f = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_e_f.clone(),
    );

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
    map.add_symbol(3, d, nat_ty.clone());
    map.add_symbol(4, e, nat_ty.clone());
    map.add_symbol(5, f, nat_ty);

    // Clause 0: ¬(a = b) with FVarId 0
    map.add_input_clause(0, FVarId::new(0), neq_a_b);
    // Clause 1: ¬(c = d) with FVarId 1
    map.add_input_clause(1, FVarId::new(1), neq_c_d);
    // Clause 2: ¬(e = f) with FVarId 2
    map.add_input_clause(2, FVarId::new(2), neq_e_f);
    // Clause 3: hypothesis (a = b) with FVarId 100
    map.add_input_clause(3, h_eq_id, eq_a_b);

    // 3 goal clauses
    map.set_goal_info(or3_goal, 3);

    RefutationFixture { env, ctx, map }
}

/// Proof trace: 3-disjunct Or-goal refutation using first disjunct.
///
/// c0: a ≠ b (negated first disjunct, input)
/// c1: c ≠ d (negated second disjunct, input)
/// c2: e ≠ f (negated third disjunct, input)
/// c3: a = b (hypothesis h_eq, input)
/// c4: Superposition(c3, c0, root) → b ≠ b
/// c5: EqualityResolution(c4) → ⊥
fn mk_or3_goal_trace() -> ProofTrace {
    let c0 = mk_input_neq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_neq(1, Term::Const(2), Term::Const(3));
    let c2 = mk_input_neq(2, Term::Const(4), Term::Const(5));
    let c3 = mk_input_eq(3, Term::Const(0), Term::Const(1));
    let c4 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(1),
            positive: false,
        }],
        id: 4,
        parents: vec![3, 0],
        inference: Inference::Superposition(3, 0, Position::root()),
    };
    let c5 = Clause {
        literals: vec![],
        id: 5,
        parents: vec![4],
        inference: Inference::EqualityResolution(4),
    };
    ProofTrace {
        empty_clause: c5.clone(),
        clauses: vec![c0, c1, c2, c3, c4, c5],
    }
}

/// End-to-end: reconstruct_goal() handles 3-disjunct Or-goals.
///
/// Goal: Or (Eq Nat a b) (Or (Eq Nat c d) (Eq Nat e f))
/// Hypothesis: h_eq : Eq Nat a b
///
/// Verifies that inject_into_or_chain correctly builds Or.inr ∘ Or.inl and
/// Or.inr ∘ Or.inr chains for the 2nd and 3rd positions in a 3-way Or.
#[test]
fn test_reconstruct_goal_or3_type_checks() {
    let f = mk_or3_goal_fixture();
    let trace = mk_or3_goal_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let (proof, desc) = reconstructor
        .reconstruct_goal()
        .expect("3-disjunct Or-goal reconstruction should succeed");

    assert!(
        desc.contains("byContradiction"),
        "description should mention byContradiction"
    );

    // Type-check: proof should have type Or (Eq a b) (Or (Eq c d) (Eq e f))
    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "3-disjunct Or-goal proof type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    let ty = tc.whnf(&ty);

    // Verify the outer type is Or(...)
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
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Or")),
        "3-disjunct Or-goal proof type should be Or(...), got {:?}",
        ty
    );
    assert_eq!(args.len(), 2, "Or should have 2 args (P, Or Q R)");
}
