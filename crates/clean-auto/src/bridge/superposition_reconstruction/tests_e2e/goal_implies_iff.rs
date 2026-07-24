// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implies and Iff goal tests.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Environment, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker,
};

// ================================================================
// Implies goal: (a = b) → (a = b)
//
// The clausifier negates to (a = b) ∧ ¬(a = b), producing 2 clauses:
//   c0: a = b (positive, from antecedent)
//   c1: a ≠ b (negative, from ¬consequent)
// Resolution produces ⊥.
//
// The proof structure is:
//   fun (p : Eq Nat a b) => byContradiction @(Eq Nat a b)
//     (fun nq : ¬(Eq Nat a b) => <false from p and nq>)
// ================================================================

fn mk_implies_goal_fixture() -> RefutationFixture {
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

    // Goal: (Eq Nat a b) → (Eq Nat a b) (non-dependent Pi)
    let implies_goal = Expr::pi(BinderInfo::Default, eq_a_b.clone(), eq_a_b.clone());

    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );

    let ctx = LocalContext::new();

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty);

    // Clause 0 (FVarId 0): a = b (from antecedent P of negated Implies)
    map.add_input_clause(0, FVarId::new(0), eq_a_b.clone());
    // Clause 1 (FVarId 1): a ≠ b (from ¬Q of negated Implies)
    map.add_input_clause(1, FVarId::new(1), neq_a_b);

    map.set_goal_info(implies_goal, 2);

    RefutationFixture { env, ctx, map }
}

fn mk_implies_goal_trace() -> ProofTrace {
    let c0 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_neq(1, Term::Const(0), Term::Const(1));
    let c2 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(1),
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
    let empty = c3.clone();
    ProofTrace {
        clauses: vec![c0, c1, c2, c3],
        empty_clause: empty,
    }
}

#[test]
fn test_reconstruct_goal_implies_type_checks() {
    let f = mk_implies_goal_fixture();
    let trace = mk_implies_goal_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let (proof, desc) = reconstructor
        .reconstruct_goal()
        .expect("implies goal reconstruction should succeed");

    assert!(
        desc.contains("implies"),
        "description should mention implies, got: {desc}"
    );

    // Type-check: proof should have type (Eq Nat testA testB) → (Eq Nat testA testB)
    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "implies goal proof type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    let ty = tc.whnf(&ty);

    assert!(
        matches!(ty.kind(), ExprKind::Pi(_, _, _)),
        "implies goal proof should have Pi type, got {:?}",
        ty
    );
}

// ================================================================
// Iff goal: (a = b) ↔ (c = d)
//
// The clausifier negates to ¬((a=b) ↔ (c=d)) which expands to
// (a=b ∧ c≠d) ∨ (a≠b ∧ c=d), producing 4 CNF clauses:
//   c0: [a=b, a≠b]     (tautology — prover eliminates)
//   c1: [a=b, c=d]     (non-tautological)
//   c2: [c≠d, a≠b]     (non-tautological)
//   c3: [c≠d, c=d]     (tautology — prover eliminates)
//
// The proof uses Iff.intro with two byContradiction wrappers:
//   Iff.intro
//     (fun hp : P => byContradiction @Q (fun hnq : ¬Q => ...))
//     (fun hq : Q => byContradiction @P (fun hnp : ¬P => ...))
// ================================================================

/// Build environment for Iff goal tests: testA, testB, testC, testD : Nat
/// plus Eq, Nat, True/False, Classical, and Iff.
fn mk_env_for_iff_goal() -> Environment {
    let mut env = mk_env_with_four_constants();
    env.init_classical().expect("init_classical");
    env.init_iff().expect("init_iff");
    env
}

/// Fixture for Iff goal test:
///
/// Goal: Iff (Eq Nat testA testB) (Eq Nat testC testD)
/// Hypotheses: h1 : Eq Nat testA testB (FVarId 100)
///             h2 : Eq Nat testC testD (FVarId 101)
///
/// Negated goal produces 4 clauses:
/// - Clause 0 (FVarId 0): [a=b, a≠b] — tautology
/// - Clause 1 (FVarId 1): [a=b, c=d]
/// - Clause 2 (FVarId 2): [c≠d, a≠b]
/// - Clause 3 (FVarId 3): [c≠d, c=d] — tautology
fn mk_iff_goal_fixture() -> RefutationFixture {
    let env = mk_env_for_iff_goal();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let d = Expr::const_(Name::from_string("testD"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_a_b = mk_eq(&nat_ty, &a, &b, &u1);
    let eq_c_d = mk_eq(&nat_ty, &c, &d, &u1);

    // Goal: Iff (Eq Nat testA testB) (Eq Nat testC testD)
    let iff_goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Iff"), vec![]),
            eq_a_b.clone(),
        ),
        eq_c_d.clone(),
    );

    // Clause propositions (as built by clause_to_prop):
    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );
    let neq_c_d = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_c_d.clone(),
    );

    // Only register non-tautological clauses (1 and 2) — the prover eliminates
    // clauses 0 and 3 during preprocessing.
    // Clause 1 prop: Or (Eq a b) (Eq c d)
    let clause_1_prop = mk_or(&eq_a_b, &eq_c_d);
    // Clause 2 prop: Or (Not (Eq c d)) (Not (Eq a b))
    let clause_2_prop = mk_or(&neq_c_d, &neq_a_b);

    let h1_id = FVarId::new(100);
    let h2_id = FVarId::new(101);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h1_id,
        Name::from_string("h1"),
        eq_a_b.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h2_id,
        Name::from_string("h2"),
        eq_c_d.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty.clone());
    map.add_symbol(2, c, nat_ty.clone());
    map.add_symbol(3, d, nat_ty);

    // Clause 1 (FVarId 1): [a=b, c=d] — non-tautological
    map.add_input_clause(1, FVarId::new(1), clause_1_prop);
    // Clause 2 (FVarId 2): [c≠d, a≠b] — non-tautological
    map.add_input_clause(2, FVarId::new(2), clause_2_prop);
    // Clause 4: hypothesis h1 (a = b)
    map.add_input_clause(4, h1_id, eq_a_b.clone());
    // Clause 5: hypothesis h2 (c = d)
    map.add_input_clause(5, h2_id, eq_c_d);

    // 4 goal clauses (Iff produces 4 CNF clauses)
    map.set_goal_info(iff_goal, 4);

    RefutationFixture { env, ctx, map }
}

/// Build trace: Iff goal refutation.
///
/// c1: [a=b, c=d] (negated goal clause 1, input)
/// c2: [c≠d, a≠b] (negated goal clause 2, input)
/// c4: a=b (hypothesis h1, input)
/// c5: c=d (hypothesis h2, input)
///
/// Refutation:
/// c6: Superposition(c4, c2, root) → [c≠d, b≠b] (rewrite a→b in a≠b)
/// c7: EqualityResolution(c6) → [c≠d] (resolve b≠b)
/// c8: Superposition(c5, c7, root) → [d≠d] (rewrite c→d in c≠d)
/// c9: EqualityResolution(c8) → ⊥
fn mk_iff_goal_trace() -> ProofTrace {
    let (a, b, c, d) = (
        Term::Const(0),
        Term::Const(1),
        Term::Const(2),
        Term::Const(3),
    );

    // Non-tautological goal clauses (input)
    let c1 = Clause {
        literals: vec![
            mk_lit(a.clone(), b.clone(), true),
            mk_lit(c.clone(), d.clone(), true),
        ],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    let c2 = Clause {
        literals: vec![
            mk_lit(c.clone(), d.clone(), false),
            mk_lit(a.clone(), b.clone(), false),
        ],
        id: 2,
        parents: vec![],
        inference: Inference::Input,
    };
    let c4 = mk_input_eq(4, a, b.clone()); // h1: a=b
    let c5 = mk_input_eq(5, c.clone(), d.clone()); // h2: c=d

    // Superposition(c4, c2): rewrite a→b in a≠b → [c≠d, b≠b]
    let c6 = Clause {
        literals: vec![
            mk_lit(c.clone(), d.clone(), false),
            mk_lit(b.clone(), b, false),
        ],
        id: 6,
        parents: vec![4, 2],
        inference: Inference::Superposition(4, 2, Position::root()),
    };
    // EqualityResolution(c6): resolve b≠b → [c≠d]
    let c7 = Clause {
        literals: vec![mk_lit(c, d.clone(), false)],
        id: 7,
        parents: vec![6],
        inference: Inference::EqualityResolution(6),
    };
    // Superposition(c5, c7): rewrite c→d in c≠d → [d≠d]
    let c8 = Clause {
        literals: vec![mk_lit(d.clone(), d, false)],
        id: 8,
        parents: vec![5, 7],
        inference: Inference::Superposition(5, 7, Position::root()),
    };
    // EqualityResolution(c8): ⊥
    let c9 = Clause {
        literals: vec![],
        id: 9,
        parents: vec![8],
        inference: Inference::EqualityResolution(8),
    };

    ProofTrace {
        empty_clause: c9.clone(),
        clauses: vec![c1, c2, c4, c5, c6, c7, c8, c9],
    }
}

/// End-to-end: reconstruct_goal() handles Iff goals via Iff.intro.
///
/// Goal: Iff (Eq Nat testA testB) (Eq Nat testC testD)
/// Hypotheses: h1 : Eq Nat testA testB, h2 : Eq Nat testC testD
///
/// The prover refutes the negated Iff using h1 and h2.
/// reconstruct_goal() builds Iff.intro with two byContradiction wrappers,
/// substituting each goal clause FVar with Or.inl (forward) / Or.inr (backward)
/// derivations from the bound variables.
#[test]
fn test_reconstruct_goal_iff_type_checks() {
    let f = mk_iff_goal_fixture();
    let trace = mk_iff_goal_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let (proof, desc) = reconstructor
        .reconstruct_goal()
        .expect("iff goal reconstruction should succeed");

    assert!(
        desc.contains("iff"),
        "description should mention iff, got: {desc}"
    );

    // Type-check: proof should have type Iff (Eq Nat testA testB) (Eq Nat testC testD)
    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "iff goal proof type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    let ty = tc.whnf(&ty);

    // Verify the type is Iff(...)
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
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Iff")),
        "iff goal proof type should be Iff(...), got {:?}",
        ty
    );
    assert_eq!(args.len(), 2, "Iff should have 2 args (P, Q)");
}
