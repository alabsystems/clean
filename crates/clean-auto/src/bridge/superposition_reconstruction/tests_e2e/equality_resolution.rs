// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-literal equality resolution e2e tests and factoring+resolution chain.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker};

/// Build fixture for multi-literal equality resolution with 3 literals:
/// - symbol 0 → testA : Nat
/// - symbol 1 → testB : Nat
/// - symbol 2 → testC : Nat
/// - clause 0 → h_parent : Or (Eq Nat testA testB) (Or (Not (Eq Nat testA testA)) (Eq Nat testA testC))
fn mk_equality_resolution_multi_literal_fixture() -> RefutationFixture {
    let env = mk_env_with_three_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
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
    let eq_a_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
                nat_ty.clone(),
            ),
            a.clone(),
        ),
        a.clone(),
    );
    let not_eq_a_a = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_a_a);
    let eq_a_c = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u1]),
                nat_ty.clone(),
            ),
            a.clone(),
        ),
        c.clone(),
    );

    // Or (Not (Eq Nat testA testA)) (Eq Nat testA testC)
    let inner_or = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), not_eq_a_a),
        eq_a_c,
    );
    // Or (Eq Nat testA testB) (Or (Not (Eq Nat testA testA)) (Eq Nat testA testC))
    let parent_prop = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_a_b),
        inner_or,
    );

    let h_parent_id = FVarId::new(30);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_parent_id,
        Name::from_string("h_parent"),
        parent_prop.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty.clone());
    map.add_symbol(2, c, nat_ty);
    map.add_input_clause(0, h_parent_id, parent_prop);

    RefutationFixture { env, ctx, map }
}

/// Build trace for multi-literal equality resolution (3-literal parent):
/// c0 (Input): testA=testB ∨ testA≠testA ∨ testA=testC
/// c1 (EqualityResolution(0)): testA=testB ∨ testA=testC
fn mk_equality_resolution_multi_literal_trace() -> ProofTrace {
    let c0 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(0),
                positive: false,
            },
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(2),
                positive: true,
            },
        ],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let c1 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(2),
                positive: true,
            },
        ],
        id: 1,
        parents: vec![0],
        inference: Inference::EqualityResolution(0),
    };
    ProofTrace {
        empty_clause: c1.clone(),
        clauses: vec![c0, c1],
    }
}

/// End-to-end: multi-literal equality resolution (3-literal parent) → type-checks.
///
/// Parent: testA=testB ∨ testA≠testA ∨ testA=testC
/// Resolved literal: testA≠testA (index 1, trivially self-equal)
/// Result: testA=testB ∨ testA=testC
/// Proof uses Or.rec on the 3-literal parent with absurd on the resolved literal.
#[test]
fn test_end_to_end_equality_resolution_multi_literal_type_checks() {
    let f = mk_equality_resolution_multi_literal_fixture();
    let trace = mk_equality_resolution_multi_literal_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let proof = reconstructor
        .reconstruct_clause(1)
        .expect("multi-literal equality resolution should succeed");

    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "multi-literal eq resolution type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    // whnf to reduce Or.rec motive application
    let ty = tc.whnf(&ty);

    let (head, args) = {
        let mut e = &ty;
        let mut args = Vec::new();
        while let ExprKind::App(f, a) = e.kind() {
            args.push(a.as_ref());
            e = f;
        }
        args.reverse();
        (e, args)
    };

    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Or")),
        "multi-literal eq resolution proof type should be Or(...), got {:?}",
        ty
    );
    assert_eq!(
        args.len(),
        2,
        "Or should have 2 args (left disjunct, right disjunct)"
    );
}

// ---- Full refutation: EqualityFactoring → EqualityResolution chain ----

/// Build fixture for full refutation combining EqualityFactoring + EqualityResolution.
///
/// Hypotheses:
/// - h_parent : Or (Eq Nat testA testB) (Eq Nat testA testB) (duplicated literal)
/// - h_neq : Not (Eq Nat testA testB)
fn mk_factoring_resolution_refutation_fixture() -> RefutationFixture {
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

    let parent_prop = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            eq_a_b.clone(),
        ),
        eq_a_b.clone(),
    );

    let neq_prop = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_a_b);

    let h_parent_id = FVarId::new(30);
    let h_neq_id = FVarId::new(40);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_parent_id,
        Name::from_string("h_parent"),
        parent_prop.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_neq_id,
        Name::from_string("h_neq"),
        neq_prop.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty);
    map.add_input_clause(0, h_parent_id, parent_prop);
    map.add_input_clause(1, h_neq_id, neq_prop);

    RefutationFixture { env, ctx, map }
}

/// Build full refutation trace: EqualityFactoring → EqualityResolution →
/// Superposition → EqualityResolution → ⊥.
///
/// c0 (Input): testA=testB ∨ testA=testB (duplicated)
/// c1 (Input): testA≠testB
/// c2 (EqualityFactoring(0)): testA=testB ∨ testB≠testB
/// c3 (EqualityResolution(2)): testA=testB (resolved testB≠testB)
/// c4 (Superposition(3, 1, root)): testB≠testB (rewrote testA→testB in c1)
/// c5 (EqualityResolution(4)): ⊥
fn mk_factoring_resolution_refutation_trace() -> ProofTrace {
    let c0 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
        ],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let c1 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(0),
            rhs: Term::Const(1),
            positive: false,
        }],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    let c2 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(1),
                rhs: Term::Const(1),
                positive: false,
            },
        ],
        id: 2,
        parents: vec![0],
        inference: Inference::EqualityFactoring(0),
    };
    let c3 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(0),
            rhs: Term::Const(1),
            positive: true,
        }],
        id: 3,
        parents: vec![2],
        inference: Inference::EqualityResolution(2),
    };
    let c4 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(1),
            positive: false,
        }],
        id: 4,
        parents: vec![3, 1],
        inference: Inference::Superposition(3, 1, Position::root()),
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

/// End-to-end: EqualityFactoring → EqualityResolution → Superposition →
/// EqualityResolution → ⊥. Type-checks to False.
///
/// Full refutation combining 4 inference steps:
/// 1. EqualityFactoring deduplicates testA=testB ∨ testA=testB
/// 2. EqualityResolution removes trivial testB≠testB
/// 3. Superposition rewrites testA→testB using the derived equation
/// 4. EqualityResolution derives contradiction from testB≠testB
#[test]
fn test_end_to_end_factoring_resolution_refutation_type_checks() {
    let f = mk_factoring_resolution_refutation_fixture();
    let trace = mk_factoring_resolution_refutation_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);
    let (proof, desc) = reconstructor
        .reconstruct()
        .expect("factoring-resolution refutation should succeed");

    assert!(
        desc.contains("Superposition"),
        "description should mention superposition"
    );
    assert_proof_type_checks_to_false(
        &f.env,
        f.ctx,
        &proof,
        "EqualityFactoring → EqualityResolution → Superposition → EqualityResolution refutation",
    );
}
