// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality factoring e2e tests.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker,
};

/// Build fixture for equality factoring:
/// - symbol 0 → testA : Nat (the shared LHS 's')
/// - symbol 1 → testB : Nat (t₁)
/// - symbol 2 → testC : Nat (t₂)
/// - clause 0 → h_parent : Or (Eq Nat testA testB) (Eq Nat testA testC)
fn mk_equality_factoring_fixture() -> RefutationFixture {
    let env = mk_env_with_three_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let u1 = Level::succ(Level::zero());

    // h_parent : Or (Eq Nat testA testB) (Eq Nat testA testC)
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
    let parent_prop = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            eq_a_b.clone(),
        ),
        eq_a_c.clone(),
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

/// Build trace for equality factoring:
/// c0 (Input): testA=testB ∨ testA=testC
/// c1 (EqualityFactoring(0)): testA=testB ∨ testB≠testC
fn mk_equality_factoring_trace_e2e() -> ProofTrace {
    let c0 = Clause {
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
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    // Factoring output: [testA=testB (kept), testB≠testC (new disequation)]
    let c1 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(1),
                rhs: Term::Const(2),
                positive: false,
            },
        ],
        id: 1,
        parents: vec![0],
        inference: Inference::EqualityFactoring(0),
    };
    ProofTrace {
        empty_clause: c1.clone(),
        clauses: vec![c0, c1],
    }
}

/// End-to-end: equality factoring → reconstruct() → type-checks correctly.
///
/// Trace: h_parent: testA=testB ∨ testA=testC → EqualityFactoring →
///        testA=testB ∨ testB≠testC.
/// Verifies the proof has the correct Or type (not False, since this is not
/// a full refutation — just the factoring step).
#[test]
fn test_end_to_end_equality_factoring_type_checks() {
    let f = mk_equality_factoring_fixture();
    let trace = mk_equality_factoring_trace_e2e();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let proof = reconstructor
        .reconstruct_clause(1)
        .expect("equality factoring reconstruction should succeed");

    // Type-check the proof
    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "equality factoring proof type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    // The proof should have type: Or (Eq Nat testA testB) (Not (Eq Nat testB testC))
    // Or.rec returns `motive t` which may be a beta-redex; whnf to reduce.
    let ty = tc.whnf(&ty);

    // Verify it's an Or application
    let (or_head, or_args) = {
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
        matches!(or_head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Or")),
        "factoring proof type should be Or(...), got {:?}",
        ty
    );
    assert_eq!(
        or_args.len(),
        2,
        "Or should have 2 args (left disjunct, right disjunct)"
    );
}

/// Build fixture with testF(testA, testA) ≠ testF(testB, testA).
///
/// testA appears 3 times in the clause prop — exercises position-aware abstraction.
/// Symbols: 0→testA, 1→testB, 2→testF (Nat→Nat→Nat).
pub(super) fn mk_overlapping_terms_fixture() -> RefutationFixture {
    let mut env = mk_env_with_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let testf_ty = Expr::pi(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::pi(BinderInfo::Default, nat_ty.clone(), nat_ty.clone()),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testF"),
        level_params: vec![],
        type_: testf_ty.clone(),
    })
    .expect("add testF");

    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let f = Expr::const_(Name::from_string("testF"), vec![]);
    let u1 = Level::succ(Level::zero());
    let fa_a = Expr::app(Expr::app(f.clone(), a.clone()), a.clone());
    let fb_a = Expr::app(Expr::app(f.clone(), b.clone()), a.clone());

    let eq_prop = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
                nat_ty.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    );
    let neq_prop = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![u1]),
                    nat_ty.clone(),
                ),
                fa_a,
            ),
            fb_a,
        ),
    );

    let h_eq_id = FVarId::new(10);
    let h_neq_id = FVarId::new(20);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_prop.clone(),
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
    map.add_symbol(2, f, testf_ty);
    map.add_input_clause(0, h_eq_id, eq_prop);
    map.add_input_clause(1, h_neq_id, neq_prop);
    RefutationFixture { env, ctx, map }
}

/// Build trace: a=b, f(a,a)≠f(b,a) → superposition at pos [0] → EqRes → ⊥.
pub(super) fn mk_overlapping_superposition_trace() -> ProofTrace {
    let c0 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c1 = Clause {
        literals: vec![Literal {
            lhs: Term::App(2, vec![Term::Const(0), Term::Const(0)]),
            rhs: Term::App(2, vec![Term::Const(1), Term::Const(0)]),
            positive: false,
        }],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    let c2 = Clause {
        literals: vec![Literal {
            lhs: Term::App(2, vec![Term::Const(1), Term::Const(0)]),
            rhs: Term::App(2, vec![Term::Const(1), Term::Const(0)]),
            positive: false,
        }],
        id: 2,
        parents: vec![0, 1],
        inference: Inference::Superposition(0, 1, Position(vec![0])),
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
