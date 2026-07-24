// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the ProofBuilder DSL.
//!
//! Validates that the builder produces correct, kernel-verified proof terms.

use super::proof_builder::ProofBuilder;
use super::test_helpers::assert_const;
use super::*;
use crate::expr::{BinderInfo, ExprKind};

/// Helper: create a prelude environment with ProofBuilder.
fn setup() -> (Environment, ProofBuilder) {
    let env = Environment::with_prelude();
    let pb = ProofBuilder::new();
    (env, pb)
}

// =========================================================================
// Test 1: Eq.refl builds a valid proof
// =========================================================================

#[test]
fn test_eq_refl_builds_valid_proof() {
    let (mut env, pb) = setup();

    // Prove: 0 = 0 (at type Nat, universe level 1)
    let zero = pb.nat_zero();
    let ty = pb.eq_nat(zero.clone(), zero.clone());
    let proof = pb.eq_refl_nat(zero);

    pb.register_theorem(&mut env, "test.eq_refl_zero", ty, proof)
        .expect("Eq.refl Nat Nat.zero should be kernel-verified");

    assert_const(&env, "test.eq_refl_zero");
}

// =========================================================================
// Test 2: Eq.trans chain — compose two equalities
// =========================================================================

#[test]
fn test_eq_trans_chain() {
    let (mut env, pb) = setup();

    // Prove: 0 = 0 via Eq.trans (0 = 0) (0 = 0)
    // Trivial but validates the combinator wiring.
    let zero = pb.nat_zero();

    let refl_proof = pb.eq_refl_nat(zero.clone());
    let trans_proof = pb.eq_trans_nat(
        zero.clone(),
        zero.clone(),
        zero.clone(),
        refl_proof.clone(),
        refl_proof,
    );
    let ty = pb.eq_nat(zero.clone(), zero);

    pb.register_theorem(&mut env, "test.eq_trans_trivial", ty, trans_proof)
        .expect("Eq.trans with two Eq.refl proofs should be kernel-verified");

    assert_const(&env, "test.eq_trans_trivial");
}

// =========================================================================
// Test 3: And.intro — prove A /\ B from proofs of A and B
// =========================================================================

#[test]
fn test_and_intro() {
    let (mut env, pb) = setup();

    // Prove: (0 = 0) /\ (0 = 0)
    let zero = pb.nat_zero();
    let eq_zero = pb.eq_nat(zero.clone(), zero.clone());
    let refl = pb.eq_refl_nat(zero);

    let proof = pb.and_intro(eq_zero.clone(), eq_zero.clone(), refl.clone(), refl);
    let ty = pb.and(eq_zero.clone(), eq_zero);

    pb.register_theorem(&mut env, "test.and_intro_refl", ty, proof)
        .expect("And.intro with two Eq.refl proofs should be kernel-verified");

    assert_const(&env, "test.and_intro_refl");
}

// =========================================================================
// Test 4: Nat.rec induction — define a function by recursion
// =========================================================================

#[test]
fn test_nat_rec_induction() {
    let (mut env, pb) = setup();

    // Define double : Nat -> Nat by recursion
    //   double 0 = 0
    //   double (succ n) = succ (succ (double n))
    let nat = pb.nat();
    let zero = pb.nat_zero();

    // motive: fun _ : Nat => Nat
    let motive = pb.lam("_", nat.clone(), |_| nat.clone());

    // base case: Nat.zero
    let base = zero;

    // step case: fun (n : Nat) (ih : Nat) => Nat.succ (Nat.succ ih)
    let step = pb.build(|b| {
        let (n_id, _n) = b.fresh_local(nat.clone());
        let (ih_id, ih) = b.fresh_local(nat.clone());
        let body = pb.nat_succ_of(pb.nat_succ_of(ih));
        let e = b.mk_lam(ih_id, BinderInfo::Default, nat.clone(), body);
        b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e)
    });

    // double = fun n : Nat => Nat.rec motive base step n
    let double_value = pb.lam("n", nat.clone(), |n| {
        pb.nat_rec(motive.clone(), base.clone(), step.clone(), n)
    });

    let double_type = pb.arrow(nat.clone(), nat.clone());

    pb.register_definition(&mut env, "test.double", double_type, double_value)
        .expect("double definition via Nat.rec should be kernel-verified");

    assert_const(&env, "test.double");
}

// =========================================================================
// Test 5: Lambda application — build and register identity function
// =========================================================================

#[test]
fn test_lambda_application() {
    let (mut env, pb) = setup();

    // Define id_nat : Nat -> Nat := fun (n : Nat) => n
    let nat = pb.nat();
    let id_value = pb.lam("n", nat.clone(), |n| n);
    let id_type = pb.arrow(nat.clone(), nat.clone());

    pb.register_definition(&mut env, "test.id_nat", id_type, id_value)
        .expect("Identity function on Nat should be kernel-verified");

    assert_const(&env, "test.id_nat");

    // Verify the structure: Lam(Default, Nat, BVar(0))
    let ci = env
        .get_const(&Name::from_string("test.id_nat"))
        .expect("test.id_nat should exist");
    let value = ci.value.as_ref().expect("definition should have value");
    match value.kind() {
        ExprKind::Lam(bi, ty, body) => {
            assert_eq!(bi.info, BinderInfo::Default);
            assert!(
                matches!(ty.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat")),
                "lambda binder type should be Nat"
            );
            assert!(
                matches!(body.kind(), ExprKind::BVar(0)),
                "identity body should be BVar(0)"
            );
        }
        _ => panic!("expected Lam, got {:?}", value.kind()),
    }
}

// =========================================================================
// Test 6: Full roundtrip — build + register + verify
// =========================================================================

#[test]
fn test_register_theorem_kernel_verified() {
    let (mut env, pb) = setup();

    // Register a monomorphic theorem: forall (a : Nat), a = a
    let nat = pb.nat();

    // Type: forall (a : Nat), @Eq.{1} Nat a a
    let thm_type = pb.build(|b| {
        let (a_id, a) = b.fresh_local(nat.clone());
        let eq_a_a = pb.eq_nat(a.clone(), a);
        b.mk_pi(a_id, BinderInfo::Default, nat.clone(), eq_a_a)
    });

    // Proof: fun (a : Nat) => @Eq.refl.{1} Nat a
    let thm_proof = pb.build(|b| {
        let (a_id, a) = b.fresh_local(nat.clone());
        let refl = pb.eq_refl_nat(a);
        b.mk_lam(a_id, BinderInfo::Default, nat.clone(), refl)
    });

    pb.register_theorem(&mut env, "test.nat_refl_forall", thm_type, thm_proof)
        .expect("forall a : Nat, a = a should be kernel-verified");

    // Verify it was registered as a Theorem
    let ci = env
        .get_const(&Name::from_string("test.nat_refl_forall"))
        .expect("test.nat_refl_forall should exist");
    assert_eq!(ci.name, Name::from_string("test.nat_refl_forall"));
    assert!(ci.value.is_some(), "theorem should have a proof term");
}

// =========================================================================
// Test 7: Eq.symm — prove b = a from a = b
// =========================================================================

#[test]
fn test_eq_symm() {
    let (mut env, pb) = setup();

    // Prove: 0 = 0 from symmetry of 0 = 0
    let zero = pb.nat_zero();

    let refl = pb.eq_refl_nat(zero.clone());
    let symm_proof = pb.eq_symm_nat(zero.clone(), zero.clone(), refl);
    let ty = pb.eq_nat(zero.clone(), zero);

    pb.register_theorem(&mut env, "test.eq_symm_zero", ty, symm_proof)
        .expect("Eq.symm on Eq.refl should be kernel-verified");

    assert_const(&env, "test.eq_symm_zero");
}

// =========================================================================
// Test 8: Const reference helpers
// =========================================================================

#[test]
fn test_const_ref_helpers() {
    let pb = ProofBuilder::new();

    // const_ref produces Const with no levels
    let nat = pb.const_ref("Nat");
    match nat.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("Nat"));
            assert!(levels.is_empty());
        }
        _ => panic!("expected Const"),
    }

    // const_ref_levels produces Const with specified levels
    let eq = pb.const_ref_levels("Eq", vec![Level::succ(Level::zero())]);
    match eq.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("Eq"));
            assert_eq!(levels.len(), 1);
        }
        _ => panic!("expected Const"),
    }
}

// =========================================================================
// Test 9: nat_lit builds correct successor chains
// =========================================================================

#[test]
fn test_nat_lit_values() {
    let pb = ProofBuilder::new();

    // nat_lit(0) = Nat.zero
    let zero = pb.nat_lit(0);
    assert!(
        matches!(zero.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.zero")),
        "nat_lit(0) should be Nat.zero"
    );

    // nat_lit(1) = Nat.succ Nat.zero
    let one = pb.nat_lit(1);
    match one.kind() {
        ExprKind::App(f, arg) => {
            assert!(
                matches!(f.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.succ")),
                "nat_lit(1) function should be Nat.succ"
            );
            assert!(
                matches!(arg.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.zero")),
                "nat_lit(1) argument should be Nat.zero"
            );
        }
        _ => panic!("nat_lit(1) should be App"),
    }

    // nat_lit(2) = Nat.succ (Nat.succ Nat.zero)
    let two = pb.nat_lit(2);
    match two.kind() {
        ExprKind::App(f, inner) => {
            assert!(
                matches!(f.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.succ"))
            );
            match inner.kind() {
                ExprKind::App(f2, arg2) => {
                    assert!(
                        matches!(f2.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.succ"))
                    );
                    assert!(
                        matches!(arg2.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.zero"))
                    );
                }
                _ => panic!("inner of nat_lit(2) should be App"),
            }
        }
        _ => panic!("nat_lit(2) should be App"),
    }
}

// =========================================================================
// Test 10: Pi/arrow type builders produce correct structure
// =========================================================================

#[test]
fn test_pi_and_arrow_structure() {
    let pb = ProofBuilder::new();

    // arrow(Nat, Nat) should be Pi(Default, Nat, Nat) — non-dependent
    let nat = pb.nat();
    let fn_type = pb.arrow(nat.clone(), nat.clone());
    match fn_type.kind() {
        ExprKind::Pi(bi, domain, codomain) => {
            assert_eq!(bi.info, BinderInfo::Default);
            assert!(
                matches!(domain.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat"))
            );
            // Non-dependent: body doesn't reference bvar, so it's just Nat
            assert!(
                matches!(codomain.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat"))
            );
        }
        _ => panic!("arrow should produce Pi"),
    }

    // pi("x", Nat, |x| x) should be Pi(Default, Nat, BVar(0)) — dependent
    let dep_type = pb.pi("x", nat.clone(), |x| x);
    match dep_type.kind() {
        ExprKind::Pi(bi, domain, body) => {
            assert_eq!(bi.info, BinderInfo::Default);
            assert!(
                matches!(domain.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat"))
            );
            assert!(
                matches!(body.kind(), ExprKind::BVar(0)),
                "dependent pi body should be BVar(0), got {:?}",
                body.kind()
            );
        }
        _ => panic!("pi should produce Pi"),
    }
}

// =========================================================================
// Test 11: And proposition building
// =========================================================================

#[test]
fn test_and_proposition_structure() {
    let pb = ProofBuilder::new();

    let a = pb.prop();
    let b = pb.prop();
    let and_ab = pb.and(a, b);

    // Should be App(App(And, Prop), Prop)
    match and_ab.kind() {
        ExprKind::App(f, _rhs) => match f.kind() {
            ExprKind::App(and_const, _lhs) => {
                assert!(
                    matches!(and_const.kind(), ExprKind::Const(n, _) if n == &Name::from_string("And")),
                    "inner function should be And constant"
                );
            }
            _ => panic!("expected nested App"),
        },
        _ => panic!("expected App"),
    }
}

// =========================================================================
// Test 12: Kernel rejects invalid proofs
// =========================================================================

#[test]
fn test_kernel_rejects_wrong_proof() {
    let (mut env, pb) = setup();

    // Try to prove 0 = 1 using Eq.refl — this should fail!
    let zero = pb.nat_zero();
    let one = pb.nat_succ_of(zero.clone());

    let wrong_ty = pb.eq_nat(zero.clone(), one); // 0 = 1
    let wrong_proof = pb.eq_refl_nat(zero); // Eq.refl Nat 0 : 0 = 0

    let result = pb.register_theorem(&mut env, "test.bad_proof", wrong_ty, wrong_proof);
    assert!(
        result.is_err(),
        "Kernel should reject a proof of 0 = 1 using Eq.refl 0"
    );
}

// =========================================================================
// Test 13: Universe-polymorphic theorem (forall a : Sort u, a = a)
// =========================================================================

#[test]
fn test_universe_polymorphic_theorem() {
    let (mut env, pb) = setup();

    // Prove: forall (T : Sort u) (a : T), a = a
    // This uses Level::param("u") and must be registered with register_theorem_poly.
    let sort_u = pb.sort_u();
    let u_level = Level::param(Name::from_string("u"));

    let thm_type = pb.build(|b| {
        let (t_id, t) = b.fresh_local(sort_u.clone());
        let (a_id, a) = b.fresh_local(t.clone());
        let eq_a_a = pb.eq_at(u_level.clone(), t.clone(), a.clone(), a);
        let inner = b.mk_pi(a_id, BinderInfo::Implicit, t.clone(), eq_a_a);
        b.mk_pi(t_id, BinderInfo::Implicit, sort_u.clone(), inner)
    });

    let thm_proof = pb.build(|b| {
        let (t_id, t) = b.fresh_local(sort_u.clone());
        let (a_id, a) = b.fresh_local(t.clone());
        let refl = pb.eq_refl_at(u_level.clone(), t.clone(), a);
        let inner = b.mk_lam(a_id, BinderInfo::Implicit, t.clone(), refl);
        b.mk_lam(t_id, BinderInfo::Implicit, sort_u.clone(), inner)
    });

    pb.register_theorem_poly(&mut env, "test.poly_refl", thm_type, thm_proof)
        .expect("Universe-polymorphic Eq.refl should be kernel-verified");

    assert_const(&env, "test.poly_refl");
}
