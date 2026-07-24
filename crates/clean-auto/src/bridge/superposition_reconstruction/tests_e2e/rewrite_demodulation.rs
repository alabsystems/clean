// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Demodulation rewrite tests: multi-literal and multi-position orig clauses.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker};

/// Build fixture for demodulation with multi-literal orig clause:
/// - symbol 0 → testA : Nat, symbol 1 → testB : Nat, symbol 2 → testC : Nat
/// - clause 0 → h_eq : Eq Nat testA testB (unit equation)
/// - clause 1 → h_multi : Or (Not (Eq Nat testA testB)) (Not (Eq Nat testC testC))
fn mk_demod_multi_literal_fixture() -> RefutationFixture {
    let env = mk_env_with_three_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_a_b = mk_eq(&nat_ty, &a, &b, &u1);
    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );
    let eq_c_c = mk_eq(&nat_ty, &c, &c, &u1);
    let neq_c_c = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_c_c);
    let multi_prop = mk_or(&neq_a_b, &neq_c_c);

    let h_eq_id = FVarId::new(10);
    let h_multi_id = FVarId::new(20);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_a_b.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_multi_id,
        Name::from_string("h_multi"),
        multi_prop.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty.clone());
    map.add_symbol(2, c, nat_ty);
    map.add_input_clause(0, h_eq_id, eq_a_b);
    map.add_input_clause(1, h_multi_id, multi_prop);
    RefutationFixture { env, ctx, map }
}

/// Build trace: demodulation with multi-literal orig (lhs appears once).
///
/// c0: testA=testB (input, unit equation)
/// c1: testA≠testB ∨ testC≠testC (input, multi-literal)
/// c2: Demodulation(c1, c0) → testB≠testB ∨ testC≠testC
/// c3: EqualityResolution(c2) → testC≠testC
/// c4: EqualityResolution(c3) → ⊥
fn mk_demod_multi_literal_trace() -> ProofTrace {
    let c0 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c1 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: false,
            },
            Literal {
                lhs: Term::Const(2),
                rhs: Term::Const(2),
                positive: false,
            },
        ],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    // Demodulation rewrites testA→testB in c1 using c0
    let c2 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(1),
                rhs: Term::Const(1),
                positive: false,
            },
            Literal {
                lhs: Term::Const(2),
                rhs: Term::Const(2),
                positive: false,
            },
        ],
        id: 2,
        parents: vec![1, 0],
        inference: Inference::Demodulation(1, 0),
    };
    let c3 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(2),
            rhs: Term::Const(2),
            positive: false,
        }],
        id: 3,
        parents: vec![2],
        inference: Inference::EqualityResolution(2),
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

/// End-to-end: demodulation with multi-literal orig → type-checks to False.
///
/// Exercises demodulation when the orig clause has 2+ literals.
/// The unit equation (testA=testB) rewrites testA→testB in the first literal.
/// `build_motive` abstracts ALL occurrences of lhs from orig_prop — here testA
/// appears only once in the clause proposition, so all-occurrence abstraction
/// is correct.
#[test]
fn test_demodulation_multi_literal_orig_type_checks() {
    let f = mk_demod_multi_literal_fixture();
    let trace = mk_demod_multi_literal_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);
    let (proof, _desc) = reconstructor
        .reconstruct()
        .expect("demodulation multi-literal reconstruction should succeed");

    assert_proof_type_checks_to_false(
        &f.env,
        f.ctx,
        &proof,
        "demodulation with multi-literal orig",
    );
}

// ---- Demodulation multi-position test: lhs appears in multiple literals ----

/// Build fixture for demodulation where lhs appears in BOTH literals of orig.
/// - symbol 0 → testA : Nat, symbol 1 → testB : Nat, symbol 2 → testC : Nat
/// - clause 0 → h_eq : Eq Nat testA testB (unit equation)
/// - clause 1 → h_multi : Or (Not (Eq Nat testA testB)) (Not (Eq Nat testA testC))
fn mk_demod_multi_position_fixture() -> RefutationFixture {
    let env = mk_env_with_three_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_a_b = mk_eq(&nat_ty, &a, &b, &u1);
    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );
    let eq_a_c = mk_eq(&nat_ty, &a, &c, &u1);
    let neq_a_c = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_a_c);
    let multi_prop = mk_or(&neq_a_b, &neq_a_c);

    let h_eq_id = FVarId::new(10);
    let h_multi_id = FVarId::new(20);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_a_b.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_multi_id,
        Name::from_string("h_multi"),
        multi_prop.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty.clone());
    map.add_symbol(2, c, nat_ty);
    map.add_input_clause(0, h_eq_id, eq_a_b);
    map.add_input_clause(1, h_multi_id, multi_prop);
    RefutationFixture { env, ctx, map }
}

/// Build trace: demodulation where lhs (testA) appears in both literals.
///
/// `build_motive` abstracts ALL occurrences of testA, so the result type has
/// testB in BOTH positions. This tests the soundness of all-occurrence
/// abstraction when the prover's demodulation rewrites both positions.
///
/// c0: testA=testB (input, unit equation)
/// c1: testA≠testB ∨ testA≠testC (input, testA in both literals)
/// c2: Demodulation(c1, c0) → testB≠testB ∨ testB≠testC (all testA→testB)
/// c3: EqualityResolution(c2) → testB≠testC
/// c4: (need additional hypothesis for full refutation — omit, test c2 type only)
fn mk_demod_multi_position_trace() -> ProofTrace {
    let c0 = mk_input_eq(0, Term::Const(0), Term::Const(1));
    let c1 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: false,
            },
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(2),
                positive: false,
            },
        ],
        id: 1,
        parents: vec![],
        inference: Inference::Input,
    };
    // All-occurrence rewrite: testA→testB in both literals
    let c2 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(1),
                rhs: Term::Const(1),
                positive: false,
            },
            Literal {
                lhs: Term::Const(1),
                rhs: Term::Const(2),
                positive: false,
            },
        ],
        id: 2,
        parents: vec![1, 0],
        inference: Inference::Demodulation(1, 0),
    };
    let c3 = Clause {
        literals: vec![Literal {
            lhs: Term::Const(1),
            rhs: Term::Const(2),
            positive: false,
        }],
        id: 3,
        parents: vec![2],
        inference: Inference::EqualityResolution(2),
    };
    ProofTrace {
        empty_clause: c3.clone(),
        clauses: vec![c0, c1, c2, c3],
    }
}

/// End-to-end: demodulation with lhs in multiple literals of orig.
///
/// Tests `build_motive` all-occurrence abstraction when lhs (testA) appears
/// in both literals of a 2-literal clause. The motive abstracts both testA
/// occurrences, producing result type with testB in both positions.
/// This is a non-refutation trace (c3 is testB≠testC, not ⊥).
#[test]
fn test_demodulation_multi_position_orig_type_checks() {
    let f = mk_demod_multi_position_fixture();
    let trace = mk_demod_multi_position_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let proof = reconstructor
        .reconstruct_clause(2)
        .expect("demodulation multi-position reconstruction should succeed");

    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "demodulation multi-position type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    // whnf to reduce Eq.subst motive application
    let ty = tc.whnf(&ty);

    // Should be Or (Not (Eq Nat testB testB)) (Not (Eq Nat testB testC))
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
        "demodulation multi-position proof type should be Or(...), got {:?}",
        ty
    );
    assert_eq!(
        args.len(),
        2,
        "Or should have 2 args (left disjunct, right disjunct)"
    );
}
