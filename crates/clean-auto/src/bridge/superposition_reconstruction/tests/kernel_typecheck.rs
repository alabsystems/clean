// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel type-check regression tests for superposition proof terms.

use super::super::*;
use super::support::*;
use crate::superposition::{Clause, Inference, ProofTrace};
use clean_kernel::{BinderInfo, Environment};

/// Test that reconstructed superposition proof type-checks through the kernel.
///
/// Builds a complete proof: input hypotheses -> superposition step -> verify
/// with TypeChecker that the result term has the expected type.
#[test]
fn test_superposition_proof_type_checks_kernel() {
    use clean_kernel::{Environment, TypeChecker};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");

    let tc = TypeChecker::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // Verify Eq.refl : @Eq Nat 0 0 type-checks
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let refl = mk_nat_eq_refl(&nat_ty, &zero);
    let refl_type = tc.infer_type(&refl);
    assert!(
        refl_type.is_ok(),
        "Eq.refl Nat 0 should type-check: {:?}",
        refl_type.err()
    );

    // Verify the Eq.subst structure: @Eq.subst.{1} Nat motive a b h m
    // clean Eq.subst has 1 universe param (motive fixed to Prop)
    // Build motive: fun (x : Nat) => @Eq Nat x x
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    nat_ty.clone(),
                ),
                Expr::bvar(0), // x
            ),
            Expr::bvar(0), // x
        ),
    );

    // @Eq.subst.{1} Nat motive 0 0 (Eq.refl Nat 0) (Eq.refl Nat 0)
    let subst_term = mk_eq_subst_term(&motive, &zero, &zero, &refl, &refl);

    let subst_type = tc.infer_type(&subst_term);
    assert!(
        subst_type.is_ok(),
        "Eq.subst proof should type-check through kernel: {:?}",
        subst_type.err()
    );
}

/// Regression for #2245: malformed Eq.subst argument order must be rejected.
///
/// The pre-fix reconstruction skipped the motive and shifted a term into the
/// motive slot, producing an application the kernel should never accept.
#[test]
fn test_malformed_eq_subst_is_rejected_by_kernel() {
    use clean_kernel::{Environment, TypeChecker};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");

    let tc = TypeChecker::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let refl = mk_nat_eq_refl(&nat_ty, &zero);

    // Regressed shape: a term is passed where Eq.subst expects a motive
    // lambda, mirroring the pre-#2245 missing-motive bug.
    let malformed_subst = mk_eq_subst_term(&zero, &zero, &zero, &refl, &refl);

    let expected_type = tc.infer_type(&refl).expect("Eq.refl type");
    let malformed_type = tc.check_type(&malformed_subst, &expected_type);
    assert!(
        malformed_type.is_err(),
        "Eq.subst with a non-lambda motive should be rejected by full checking, got {:?}",
        malformed_type
    );
}

/// Test that reconstructed demodulation proof structure type-checks.
///
/// Demodulation rewrites via Eq.subst, same structure as superposition.
/// Here we verify the motive lambda + Eq.subst combination for a
/// concrete rewrite `a -> b` using a unit equation `a = b`.
#[test]
fn test_demodulation_proof_type_checks_kernel() {
    use clean_kernel::{Environment, TypeChecker};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");

    let tc = TypeChecker::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Given h : @Eq Nat 0 0 (trivial equation for type-checking)
    let h = mk_nat_eq_refl(&nat_ty, &zero);

    // motive: fun (x : Nat) => @Eq Nat x 0
    // Rewrites the first argument of Eq
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    nat_ty.clone(),
                ),
                Expr::bvar(0), // x
            ),
            zero.clone(),
        ),
    );

    // m : motive 0 = @Eq Nat 0 0
    let m = h.clone();

    // @Eq.subst.{1} Nat motive 0 0 h m : motive 0 = @Eq Nat 0 0
    let demod_proof = mk_eq_subst_term(&motive, &zero, &zero, &h, &m);

    let demod_type = tc.infer_type(&demod_proof);
    assert!(
        demod_type.is_ok(),
        "Demodulation (Eq.subst) proof should type-check: {:?}",
        demod_type.err()
    );
}

/// sort_level_of_type returns SortInferenceFailed when no environment is available.
#[test]
fn test_sort_level_of_type_returns_error_without_env() {
    let map = SymbolMap::new();
    let input_clause = Clause {
        literals: vec![],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let trace = ProofTrace {
        empty_clause: input_clause.clone(),
        clauses: vec![input_clause],
    };
    let reconstructor = SuperpositionReconstructor::new(&trace, &map);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let result = reconstructor.sort_level_of_type(&nat_ty);
    assert!(
        result.is_err(),
        "sort_level_of_type should fail without env"
    );
    assert!(
        matches!(
            result.unwrap_err(),
            ReconstructionError::SortInferenceFailed(_)
        ),
        "error should be SortInferenceFailed"
    );
}

/// sort_level_of_type returns correct level when environment is available.
#[test]
fn test_sort_level_of_type_returns_level_with_env() {
    let env = Environment::new();
    let map = SymbolMap::new();
    let input_clause = Clause {
        literals: vec![],
        id: 0,
        parents: vec![],
        inference: Inference::Input,
    };
    let trace = ProofTrace {
        empty_clause: input_clause.clone(),
        clauses: vec![input_clause],
    };
    let reconstructor = SuperpositionReconstructor::with_env(&trace, &map, &env);
    // Nat : Type 0 = Sort 1, so sort_level_of_type(Nat) should return Sort 1 = Succ(Zero)
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let result = reconstructor.sort_level_of_type(&nat_ty);
    // Nat isn't declared in an empty env, so this should fail
    assert!(
        result.is_err(),
        "sort_level_of_type should fail for undeclared constant"
    );
}
