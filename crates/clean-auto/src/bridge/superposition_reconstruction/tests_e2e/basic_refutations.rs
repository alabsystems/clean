// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Basic refutation e2e tests: superposition and demodulation.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level, LocalContext};

/// Build the shared fixture with two axiom constants that share no subterms.
///
/// - symbol 0 → testA : Nat
/// - symbol 1 → testB : Nat
/// - clause 0 → h_eq : Eq Nat testA testB
/// - clause 1 → h_neq : Not(Eq Nat testA testB)
fn mk_refutation_fixture() -> RefutationFixture {
    let env = mk_env_with_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_prop = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u1]),
                nat_ty.clone(),
            ),
            a.clone(),
        ),
        b.clone(),
    );
    let neq_prop = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_prop.clone(),
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
    map.add_input_clause(0, h_eq_id, eq_prop);
    map.add_input_clause(1, h_neq_id, neq_prop);

    RefutationFixture { env, ctx, map }
}

/// Build refutation: Input(a=b) → Input(a≠b) → Superposition → EqRes → ⊥.
fn mk_superposition_refutation_trace() -> ProofTrace {
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
    ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c0, c1, c2, c3],
    }
}

/// Build refutation: Input(a=b) → Input(a≠b) → Demodulation → EqRes → ⊥.
fn mk_demodulation_refutation_trace() -> ProofTrace {
    let c0 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c1 = mk_input_neq(1, Term::Const(0), Term::Const(1));
    let c2 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(1),
            positive: false,
        }],
        id: 2,
        parents: vec![1, 0],
        inference: Inference::Demodulation(1, 0),
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

/// End-to-end: superposition refutation → reconstruct() → type-checks to False.
///
/// Trace: h_eq: testA=testB, h_neq: testA≠testB → Superposition → EqRes → ⊥.
/// Acceptance criteria #2245.
#[test]
fn test_end_to_end_superposition_reconstruct_type_checks() {
    let f = mk_refutation_fixture();
    let trace = mk_superposition_refutation_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);
    let (proof, desc) = reconstructor
        .reconstruct()
        .expect("superposition reconstruction should succeed");

    assert!(
        desc.contains("Superposition"),
        "description should mention superposition"
    );
    assert_proof_type_checks_to_false(&f.env, f.ctx, &proof, "superposition refutation");
}

/// End-to-end: demodulation refutation → reconstruct() → type-checks to False.
///
/// Trace: h_eq: testA=testB, h_neq: testA≠testB → Demodulation → EqRes → ⊥.
/// Acceptance criteria #2245.
#[test]
fn test_end_to_end_demodulation_reconstruct_type_checks() {
    let f = mk_refutation_fixture();
    let trace = mk_demodulation_refutation_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);
    let (proof, _desc) = reconstructor
        .reconstruct()
        .expect("demodulation reconstruction should succeed");

    assert_proof_type_checks_to_false(&f.env, f.ctx, &proof, "demodulation refutation");
}
