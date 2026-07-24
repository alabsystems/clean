// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel type-check coverage for arithmetic proof-builder closeout terms.

use super::super::expr_builders_arith::{
    mk_int_concrete_false, mk_real_concrete_false, mk_real_ofint_concrete_false, CmpOp,
};
use super::super::expr_builders_real_downcast::downcast_real_hyp_to_int;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Level, LocalContext, TypeChecker};

fn mk_int_order_env() -> Environment {
    let mut env = Environment::new();
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas (pulls in all Int arithmetic + ordering)");
    env
}

fn mk_real_order_env() -> Environment {
    super::super::tests_e2e_lra::mk_env_for_real_lra()
}

fn mk_int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn mk_int_negsucc(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    )
}

fn mk_le_int(a: &Expr, b: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    int_ty,
                ),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

fn mk_lt_int(a: &Expr, b: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    int_ty,
                ),
                Expr::const_(Name::from_string("instLTInt"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

fn mk_real_ofint(int_expr: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr.clone(),
    )
}

fn mk_le_real(a: &Expr, b: &Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    real_ty,
                ),
                Expr::const_(Name::from_string("instLEReal"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

fn mk_lt_real(a: &Expr, b: &Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    real_ty,
                ),
                Expr::const_(Name::from_string("instLTReal"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

fn assert_concrete_false_type_checks_to_false(
    op: CmpOp,
    start: &Expr,
    end_: &Expr,
    chain_ty: Expr,
    msg: &str,
) {
    let env = mk_int_order_env();
    let proof_id = FVarId::new(700);
    let chain_proof = Expr::fvar(proof_id);
    let proof_term = mk_int_concrete_false(op, start, end_, &chain_proof);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        proof_id,
        Name::from_string("h_chain"),
        chain_ty,
        BinderInfo::Default,
    );

    let tc = TypeChecker::with_context(&env, ctx);
    let inferred = tc
        .infer_type(&proof_term)
        .unwrap_or_else(|err| panic!("{msg}: proof term should type-check in the kernel: {err:?}"));
    let expected_false = Expr::const_(Name::from_string("False"), vec![]);

    assert!(
        tc.is_def_eq(&inferred, &expected_false),
        "{msg}: expected False, got {:?}",
        inferred
    );
}

fn assert_real_ofint_concrete_false_type_checks_to_false(
    op: CmpOp,
    start_int: &Expr,
    end_int: &Expr,
    chain_ty: Expr,
    msg: &str,
) {
    let env = mk_real_order_env();
    let proof_id = FVarId::new(710);
    let chain_proof = Expr::fvar(proof_id);
    let proof_term = mk_real_ofint_concrete_false(op, start_int, end_int, &chain_proof);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        proof_id,
        Name::from_string("h_real_chain"),
        chain_ty,
        BinderInfo::Default,
    );

    let tc = TypeChecker::with_context(&env, ctx);
    let inferred = tc
        .infer_type(&proof_term)
        .unwrap_or_else(|err| panic!("{msg}: proof term should type-check in the kernel: {err:?}"));
    let expected_false = Expr::const_(Name::from_string("False"), vec![]);

    assert!(
        tc.is_def_eq(&inferred, &expected_false),
        "{msg}: expected False, got {:?}",
        inferred
    );
}

#[test]
fn test_mk_int_concrete_false_le_positive_endpoints_type_checks_to_false() {
    let start = mk_int_ofnat(5);
    let end_ = mk_int_ofnat(3);
    let chain_ty = mk_le_int(&start, &end_);

    assert_concrete_false_type_checks_to_false(
        CmpOp::Le,
        &start,
        &end_,
        chain_ty,
        "positive-endpoint Le contradiction",
    );
}

#[test]
fn test_mk_int_concrete_false_le_negsucc_endpoints_type_checks_to_false() {
    let start = mk_int_negsucc(0);
    let end_ = mk_int_negsucc(2);
    let chain_ty = mk_le_int(&start, &end_);

    assert_concrete_false_type_checks_to_false(
        CmpOp::Le,
        &start,
        &end_,
        chain_ty,
        "negative-endpoint Le contradiction",
    );
}

#[test]
fn test_mk_int_concrete_false_lt_equality_boundary_type_checks_to_false() {
    let start = mk_int_ofnat(5);
    let end_ = mk_int_ofnat(5);
    let chain_ty = mk_lt_int(&start, &end_);

    assert_concrete_false_type_checks_to_false(
        CmpOp::Lt,
        &start,
        &end_,
        chain_ty,
        "equality-boundary Lt contradiction",
    );
}

#[test]
fn test_mk_real_ofint_concrete_false_le_mixed_sign_type_checks_to_false() {
    let start_int = mk_int_ofnat(3);
    let end_int = mk_int_negsucc(1);
    let chain_ty = mk_le_real(&mk_real_ofint(&start_int), &mk_real_ofint(&end_int));

    assert_real_ofint_concrete_false_type_checks_to_false(
        CmpOp::Le,
        &start_int,
        &end_int,
        chain_ty,
        "mixed-sign Real.ofInt Le contradiction",
    );
}

#[test]
fn test_mk_real_ofint_concrete_false_lt_equality_boundary_type_checks_to_false() {
    let start_int = mk_int_ofnat(5);
    let end_int = mk_int_ofnat(5);
    let chain_ty = mk_lt_real(&mk_real_ofint(&start_int), &mk_real_ofint(&end_int));

    assert_real_ofint_concrete_false_type_checks_to_false(
        CmpOp::Lt,
        &start_int,
        &end_int,
        chain_ty,
        "equality-boundary Real.ofInt Lt contradiction",
    );
}

// --- mk_real_concrete_false kernel type-check tests (Real.ofNat bridge axioms) ---

fn mk_real_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn mk_le_real_ofnat(m: u64, n: u64) -> Expr {
    mk_le_real(&mk_real_ofnat(m), &mk_real_ofnat(n))
}

fn mk_lt_real_ofnat(m: u64, n: u64) -> Expr {
    mk_lt_real(&mk_real_ofnat(m), &mk_real_ofnat(n))
}

fn assert_real_concrete_false_type_checks_to_false(
    op: CmpOp,
    start_nat: u64,
    end_nat: u64,
    chain_ty: Expr,
    msg: &str,
) {
    let env = mk_real_order_env();
    let proof_id = FVarId::new(720);
    let chain_proof = Expr::fvar(proof_id);
    let proof_term = mk_real_concrete_false(op, start_nat, end_nat, &chain_proof);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        proof_id,
        Name::from_string("h_real_chain"),
        chain_ty,
        BinderInfo::Default,
    );

    let tc = TypeChecker::with_context(&env, ctx);
    let inferred = tc
        .infer_type(&proof_term)
        .unwrap_or_else(|err| panic!("{msg}: proof term should type-check in the kernel: {err:?}"));
    let expected_false = Expr::const_(Name::from_string("False"), vec![]);

    assert!(
        tc.is_def_eq(&inferred, &expected_false),
        "{msg}: expected False, got {:?}",
        inferred
    );
}

#[test]
fn test_mk_real_concrete_false_le_positive_endpoints_type_checks_to_false() {
    assert_real_concrete_false_type_checks_to_false(
        CmpOp::Le,
        5,
        3,
        mk_le_real_ofnat(5, 3),
        "Real.ofNat Le contradiction (5 <= 3)",
    );
}

#[test]
fn test_mk_real_concrete_false_lt_positive_endpoints_type_checks_to_false() {
    assert_real_concrete_false_type_checks_to_false(
        CmpOp::Lt,
        5,
        3,
        mk_lt_real_ofnat(5, 3),
        "Real.ofNat Lt contradiction (5 < 3)",
    );
}

#[test]
fn test_mk_real_concrete_false_lt_equality_boundary_type_checks_to_false() {
    assert_real_concrete_false_type_checks_to_false(
        CmpOp::Lt,
        5,
        5,
        mk_lt_real_ofnat(5, 5),
        "Real.ofNat Lt equality boundary (5 < 5)",
    );
}

// --- downcast_real_hyp_to_int kernel type-check tests ---

/// Verify that downcast_real_hyp_to_int produces a well-typed Int-level
/// hypothesis when given a Real.ofNat-endpoint Le bound.
#[test]
fn test_downcast_real_hyp_to_int_ofnat_le_type_checks() {
    let env = mk_real_order_env();

    let lhs = mk_real_ofnat(3);
    let rhs = mk_real_ofnat(7);
    let chain_ty = mk_le_real(&lhs, &rhs);
    let hyp_id = FVarId::new(730);
    let h_real = Expr::fvar(hyp_id);

    let (a_int, b_int, h_int) = downcast_real_hyp_to_int(CmpOp::Le, &lhs, &rhs, &h_real)
        .expect("downcast should succeed for Real.ofNat Le endpoints");

    let expected_ty = mk_le_int(&a_int, &b_int);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        hyp_id,
        Name::from_string("h_real"),
        chain_ty,
        BinderInfo::Default,
    );

    let tc = TypeChecker::with_context(&env, ctx);
    let inferred = tc
        .infer_type(&h_int)
        .unwrap_or_else(|err| panic!("downcast Le proof should type-check: {err:?}"));

    assert!(
        tc.is_def_eq(&inferred, &expected_ty),
        "downcast Le: expected Int.le, got {:?}",
        inferred
    );
}

/// Verify that downcast_real_hyp_to_int produces a well-typed Int-level
/// hypothesis when given Real.ofInt-endpoint Lt bound (mixed-sign).
#[test]
fn test_downcast_real_hyp_to_int_ofint_lt_mixed_sign_type_checks() {
    let env = mk_real_order_env();

    let a_int = mk_int_negsucc(0); // -1
    let b_int = mk_int_ofnat(3);
    let lhs = mk_real_ofint(&a_int);
    let rhs = mk_real_ofint(&b_int);
    let chain_ty = mk_lt_real(&lhs, &rhs);
    let hyp_id = FVarId::new(731);
    let h_real = Expr::fvar(hyp_id);

    let (out_a, out_b, h_int) = downcast_real_hyp_to_int(CmpOp::Lt, &lhs, &rhs, &h_real)
        .expect("downcast should succeed for Real.ofInt Lt endpoints");

    let expected_ty = mk_lt_int(&out_a, &out_b);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        hyp_id,
        Name::from_string("h_real"),
        chain_ty,
        BinderInfo::Default,
    );

    let tc = TypeChecker::with_context(&env, ctx);
    let inferred = tc
        .infer_type(&h_int)
        .unwrap_or_else(|err| panic!("downcast Lt proof should type-check: {err:?}"));

    assert!(
        tc.is_def_eq(&inferred, &expected_ty),
        "downcast Lt mixed-sign: expected Int.lt, got {:?}",
        inferred
    );
}

/// Verify downcast with Real.ofNat Lt endpoints — the
/// normalize_real_cmp_proof_to_ofint step must rewrite ofNat to ofInt.
#[test]
fn test_downcast_real_hyp_to_int_ofnat_lt_type_checks() {
    let env = mk_real_order_env();

    let lhs = mk_real_ofnat(5);
    let rhs = mk_real_ofnat(10);
    let chain_ty = mk_lt_real(&lhs, &rhs);
    let hyp_id = FVarId::new(732);
    let h_real = Expr::fvar(hyp_id);

    let (out_a, out_b, h_int) = downcast_real_hyp_to_int(CmpOp::Lt, &lhs, &rhs, &h_real)
        .expect("downcast should succeed for Real.ofNat Lt endpoints");

    let expected_ty = mk_lt_int(&out_a, &out_b);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        hyp_id,
        Name::from_string("h_real"),
        chain_ty,
        BinderInfo::Default,
    );

    let tc = TypeChecker::with_context(&env, ctx);
    let inferred = tc
        .infer_type(&h_int)
        .unwrap_or_else(|err| panic!("downcast ofNat Lt proof should type-check: {err:?}"));

    assert!(
        tc.is_def_eq(&inferred, &expected_ty),
        "downcast ofNat Lt: expected Int.lt, got {:?}",
        inferred
    );
}
