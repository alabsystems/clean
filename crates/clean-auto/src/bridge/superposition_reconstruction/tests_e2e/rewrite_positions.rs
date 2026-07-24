// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rewrite position tests: multi-literal superposition and position-aware motive.

use super::super::*;
use super::equality_factoring::{mk_overlapping_superposition_trace, mk_overlapping_terms_fixture};
use super::support::*;
use crate::superposition::{Clause, Inference, Literal, Position, ProofTrace, Term};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker};

/// Build fixture for multi-literal c1 superposition test (#2284):
/// - symbol 0 → testA : Nat, symbol 1 → testB : Nat, symbol 2 → testC : Nat
/// - clause 0 → h_multi : Or (Eq Nat testA testB) (Not (Eq Nat testC testC))
/// - clause 1 → h_neq : Not (Eq Nat testA testB)
fn mk_multi_literal_c1_fixture() -> RefutationFixture {
    let env = mk_env_with_three_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let u1 = Level::succ(Level::zero());

    let eq_a_b = mk_eq(&nat_ty, &a, &b, &u1);
    let eq_c_c = mk_eq(&nat_ty, &c, &c, &u1);
    let neq_c_c = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_c_c);
    let multi_prop = mk_or(&eq_a_b, &neq_c_c);
    let neq_a_b = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_a_b);

    let h_multi_id = FVarId::new(10);
    let h_neq_id = FVarId::new(20);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_multi_id,
        Name::from_string("h_multi"),
        multi_prop.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_neq_id,
        Name::from_string("h_neq"),
        neq_a_b.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty.clone());
    map.add_symbol(2, c, nat_ty);
    map.add_input_clause(0, h_multi_id, multi_prop);
    map.add_input_clause(1, h_neq_id, neq_a_b);
    RefutationFixture { env, ctx, map }
}

/// Build trace: multi-literal c1 → Superposition → 2x EqualityResolution → ⊥.
///
/// c0: testA=testB ∨ testC≠testC (input, multi-literal equation clause)
/// c1: testA≠testB (input)
/// c2: Superposition(c0, c1, root) → testB≠testB ∨ testC≠testC
/// c3: EqualityResolution(c2) → testC≠testC
/// c4: EqualityResolution(c3) → ⊥
fn mk_multi_literal_c1_trace() -> ProofTrace {
    let c0 = Clause {
        literals: vec![
            Literal {
                lhs: Term::Const(0),
                rhs: Term::Const(1),
                positive: true,
            },
            Literal {
                lhs: Term::Const(2),
                rhs: Term::Const(2),
                positive: false,
            },
        ],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let c1 = mk_input_neq(1, Term::Const(0), Term::Const(1));
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
        parents: vec![0, 1],
        inference: Inference::Superposition(0, 1, Position::root()),
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

/// End-to-end: superposition with multi-literal c1 (equation clause).
///
/// c1 = (testA=testB ∨ testC≠testC) is multi-literal. Or.rec decomposes
/// c1_proof: equation branch applies Eq.subst, side literal branch injects
/// directly into the result Or chain. Full refutation type-checks to False.
#[test]
fn test_superposition_multi_literal_c1_type_checks() {
    let f = mk_multi_literal_c1_fixture();
    let trace = mk_multi_literal_c1_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    let (proof, _desc) = reconstructor
        .reconstruct()
        .expect("multi-literal c1 reconstruction should succeed");

    assert_proof_type_checks_to_false(&f.env, f.ctx, &proof, "superposition with multi-literal c1");
}

/// End-to-end: position-aware superposition with overlapping terms.
///
/// lhs (testA) appears 3 times in c1's prop. Superposition rewrites only the
/// first arg of testF. Without position-aware abstraction the motive would be
/// `fun x => Not(Eq (f x x) (f b x))` [WRONG]; with it:
/// `fun x => Not(Eq (f x a) (f b a))` [CORRECT].
#[test]
fn test_superposition_position_aware_motive_type_checks() {
    let f = mk_overlapping_terms_fixture();
    let trace = mk_overlapping_superposition_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);
    let (proof, desc) = reconstructor
        .reconstruct()
        .expect("position-aware reconstruction should succeed");

    assert!(desc.contains("Superposition"));
    assert_proof_type_checks_to_false(
        &f.env,
        f.ctx,
        &proof,
        "position-aware superposition with overlapping terms",
    );
}

// ---- Multi-literal c1 AND multi-literal c2 superposition (Or chain weakening) ----

/// Build fixture for multi-literal c1 + multi-literal c2 superposition:
/// - symbol 0 → testA, symbol 1 → testB, symbol 2 → testC
/// - clause 0 → h_c1 : Or (Eq testA testB) (Not (Eq testC testC))
///   (2-literal equation clause)
/// - clause 1 → h_c2 : Or (Not (Eq testA testB)) (Not (Eq testA testC))
///   (2-literal clause to be rewritten)
fn mk_multi_c1_c2_fixture() -> RefutationFixture {
    let env = mk_env_with_three_test_constants();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let c = Expr::const_(Name::from_string("testC"), vec![]);
    let u1 = Level::succ(Level::zero());

    // c1 prop: Or (Eq Nat testA testB) (Not (Eq Nat testC testC))
    let eq_a_b = mk_eq(&nat_ty, &a, &b, &u1);
    let eq_c_c = mk_eq(&nat_ty, &c, &c, &u1);
    let neq_c_c = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_c_c);
    let c1_prop = mk_or(&eq_a_b, &neq_c_c);

    // c2 prop: Or (Not (Eq Nat testA testB)) (Not (Eq Nat testA testC))
    let neq_a_b = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        eq_a_b.clone(),
    );
    let eq_a_c = mk_eq(&nat_ty, &a, &c, &u1);
    let neq_a_c = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_a_c);
    let c2_prop = mk_or(&neq_a_b, &neq_a_c);

    let h_c1_id = FVarId::new(10);
    let h_c2_id = FVarId::new(20);
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_c1_id,
        Name::from_string("h_c1"),
        c1_prop.clone(),
        BinderInfo::Default,
    );
    ctx.push_with_id(
        h_c2_id,
        Name::from_string("h_c2"),
        c2_prop.clone(),
        BinderInfo::Default,
    );

    let mut map = SymbolMap::new();
    map.add_symbol(0, a, nat_ty.clone());
    map.add_symbol(1, b, nat_ty.clone());
    map.add_symbol(2, c, nat_ty);
    map.add_input_clause(0, h_c1_id, c1_prop);
    map.add_input_clause(1, h_c2_id, c2_prop);
    RefutationFixture { env, ctx, map }
}

/// Build a clause from literal specs `(lhs, rhs, positive)`.
fn mk_clause(id: u64, lits: &[(u32, u32, bool)], parents: Vec<u64>, inf: Inference) -> Clause {
    Clause {
        literals: lits
            .iter()
            .map(|&(l, r, pos)| Literal {
                lhs: Term::Const(l),
                rhs: Term::Const(r),
                positive: pos,
            })
            .collect(),
        id,
        parents,
        inference: inf,
    }
}

/// Build trace: multi-literal c1 + multi-literal c2 → Or chain weakening.
///
/// c0: testA=testB ∨ testC≠testC (input, multi-literal equation clause)
/// c1: testA≠testB ∨ testA≠testC (input, multi-literal rewrite target)
/// c2: Superposition(c0, c1, root) → testB≠testB ∨ testA≠testC ∨ testC≠testC
/// c3: EqualityResolution(c2) → testA≠testC ∨ testC≠testC
/// c4: EqualityResolution(c3) → testA≠testC
fn mk_multi_c1_c2_trace() -> ProofTrace {
    let c0 = mk_clause(0, &[(0, 1, true), (2, 2, false)], vec![], Inference::Input);
    let c1 = mk_clause(1, &[(0, 1, false), (0, 2, false)], vec![], Inference::Input);
    // Superposition: rewrite testA→testB in c1's first literal
    let c2 = mk_clause(
        2,
        &[(1, 1, false), (0, 2, false), (2, 2, false)],
        vec![0, 1],
        Inference::Superposition(0, 1, Position::root()),
    );
    let c3 = mk_clause(
        3,
        &[(0, 2, false), (2, 2, false)],
        vec![2],
        Inference::EqualityResolution(2),
    );
    let c4 = mk_clause(
        4,
        &[(0, 2, false)],
        vec![3],
        Inference::EqualityResolution(3),
    );
    ProofTrace {
        empty_clause: c4.clone(),
        clauses: vec![c0, c1, c2, c3, c4],
    }
}

/// End-to-end: superposition with multi-literal c1 AND multi-literal c2.
///
/// Exercises the Or chain weakening path: Eq.subst produces a proof of the
/// c2-derived sub-disjunction (2 literals), which must be weakened into the
/// full 3-literal result clause via recursive Or.rec decomposition.
#[test]
fn test_superposition_multi_c1_multi_c2_type_checks() {
    let f = mk_multi_c1_c2_fixture();
    let trace = mk_multi_c1_c2_trace();
    let mut reconstructor = SuperpositionReconstructor::with_env(&trace, &f.map, &f.env);

    // Test clause 2 reconstruction (the superposition step with Or chain weakening)
    let proof = reconstructor
        .reconstruct_clause(2)
        .expect("multi-c1 multi-c2 superposition reconstruction should succeed");

    let tc = TypeChecker::with_context(&f.env, f.ctx);
    let result = tc.infer_type(&proof);
    assert!(
        result.is_ok(),
        "multi-c1 multi-c2 superposition type-check failed: {:?}",
        result.err()
    );
    let ty = result.expect("invariant: type-check succeeded");

    let ty = tc.whnf(&ty);

    // Should be Or (Not (Eq Nat testB testB)) (Or (Not (Eq Nat testA testC)) (Not (Eq Nat testC testC)))
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
        "multi-c1 multi-c2 superposition proof type should be Or(...), got {:?}",
        ty
    );
    assert_eq!(
        args.len(),
        2,
        "Or should have 2 args (left disjunct, right disjunct)"
    );
}
