// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the LCNF validation pass.

use super::validate::{validate_decl, ValidationError};
use crate::lcnf::*;
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

/// Helper: build a valid simple declaration.
fn valid_identity_decl() -> Decl {
    Decl::new(
        name("id"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::ret(fvar(0)),
        false,
    )
}

#[test]
fn test_validate_valid_identity() {
    let decl = valid_identity_decl();
    let errors = validate_decl(&decl);
    assert!(
        errors.is_empty(),
        "valid identity decl should have no errors: {errors:?}"
    );
}

#[test]
fn test_validate_valid_let_binding() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_ty(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert!(
        errors.is_empty(),
        "valid let binding should have no errors: {errors:?}"
    );
}

#[test]
fn test_validate_unbound_return() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::ret(fvar(99)),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(errors.len(), 1);
    assert!(
        matches!(&errors[0], ValidationError::UnboundFVar { fvar: f, context: "return" } if *f == fvar(99)),
        "expected UnboundFVar for fvar(99) in return, got: {errors:?}"
    );
}

#[test]
fn test_validate_unbound_let_value_ref() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_ty(),
                LetValue::Const {
                    name: name("Nat.add"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(50)), Arg::FVar(fvar(50))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(errors.len(), 2, "expected 2 unbound errors: {errors:?}");
    for err in &errors {
        assert!(
            matches!(err, ValidationError::UnboundFVar { fvar: f, .. } if *f == fvar(50)),
            "expected UnboundFVar for fvar(50): {err:?}"
        );
    }
}

#[test]
fn test_validate_join_point_scope() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::join_point(
            FunDecl::new(
                fvar(10),
                name("jp"),
                vec![Param::new(fvar(11), name("r"), nat_ty())],
                nat_ty(),
                Code::ret(fvar(11)),
            ),
            Code::jmp(fvar(10), vec![Arg::FVar(fvar(0))]),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert!(
        errors.is_empty(),
        "valid join point should have no errors: {errors:?}"
    );
}

#[test]
fn test_validate_jmp_to_non_join_point() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(10), name("_10"), nat_ty(), LetValue::nat(42)),
            Code::jmp(fvar(10), vec![]),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(errors.len(), 1, "expected 1 error: {errors:?}");
    assert!(
        matches!(&errors[0], ValidationError::JmpToNonJoinPoint { fvar: f } if *f == fvar(10)),
        "expected JmpToNonJoinPoint for fvar(10): {errors:?}"
    );
}

#[test]
fn test_validate_empty_cases() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::Cases(Cases::new(name("Bool"), nat_ty(), fvar(0), vec![])),
        false,
    );
    let errors = validate_decl(&decl);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::EmptyCases)),
        "expected EmptyCases error: {errors:?}"
    );
}

#[test]
fn test_validate_cases_with_ctor_params() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::Cases(Cases::new(
            name("Bool"),
            nat_ty(),
            fvar(0),
            vec![
                Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(0))),
                Alt::ctor(
                    name("Bool.false"),
                    vec![Param::new(fvar(1), name("y"), nat_ty())],
                    Code::ret(fvar(1)),
                ),
            ],
        )),
        false,
    );
    let errors = validate_decl(&decl);
    assert!(
        errors.is_empty(),
        "valid cases should have no errors: {errors:?}"
    );
}

#[test]
fn test_validate_ctor_param_not_visible_outside_alt() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::Cases(Cases::new(
            name("Foo"),
            nat_ty(),
            fvar(0),
            vec![Alt::ctor(
                name("Foo.mk"),
                vec![Param::new(fvar(1), name("y"), nat_ty())],
                Code::ret(fvar(99)),
            )],
        )),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 error for unbound fvar(99): {errors:?}"
    );
    assert!(
        matches!(&errors[0], ValidationError::UnboundFVar { fvar: f, .. } if *f == fvar(99)),
        "expected UnboundFVar for fvar(99): {errors:?}"
    );
}

#[test]
fn test_validate_duplicate_binding() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![Param::new(fvar(0), name("x"), nat_ty())],
        Code::let_bind(
            LetDecl::new(fvar(0), name("x"), nat_ty(), LetValue::nat(42)),
            Code::ret(fvar(0)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 duplicate binding error: {errors:?}"
    );
    assert!(
        matches!(&errors[0], ValidationError::DuplicateBinding { fvar: f } if *f == fvar(0)),
        "expected DuplicateBinding for fvar(0): {errors:?}"
    );
}

#[test]
fn test_validate_fun_body_scope_isolation() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::fun(
            FunDecl::new(
                fvar(10),
                name("g"),
                vec![Param::new(fvar(11), name("y"), nat_ty())],
                nat_ty(),
                Code::ret(fvar(11)),
            ),
            Code::ret(fvar(11)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 error for leaked fun param: {errors:?}"
    );
    assert!(
        matches!(&errors[0], ValidationError::UnboundFVar { fvar: f, context: "return" } if *f == fvar(11)),
        "expected UnboundFVar for fvar(11) in return: {errors:?}"
    );
}

#[test]
fn test_validate_projection_unbound() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_ty(),
                LetValue::Proj {
                    type_name: name("Foo"),
                    idx: 0,
                    structure: fvar(99),
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 unbound projection error: {errors:?}"
    );
    assert!(
        matches!(&errors[0], ValidationError::UnboundFVar { fvar: f, context: "projection structure" } if *f == fvar(99)),
        "expected UnboundFVar for projection structure: {errors:?}"
    );
}

#[test]
fn test_validate_fvar_application_unbound() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_ty(),
                LetValue::FVar {
                    fvar: fvar(99),
                    args: vec![],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 unbound fvar application error: {errors:?}"
    );
}

#[test]
fn test_validate_reuse_unbound_slot() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_ty(),
                LetValue::Reuse {
                    slot: fvar(99),
                    ctor_name: name("Foo.mk"),
                    levels: vec![],
                    args: vec![],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 unbound reuse slot error: {errors:?}"
    );
}

#[test]
fn test_validate_extern_decl_skipped() {
    let decl = Decl::extern_decl(name("io_print"), vec![], nat_ty(), vec![], vec![]);
    let errors = validate_decl(&decl);
    assert!(
        errors.is_empty(),
        "extern decl should have no errors: {errors:?}"
    );
}

#[test]
fn test_validate_jmp_unbound_target() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::jmp(fvar(99), vec![]),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 error for unbound jmp target: {errors:?}"
    );
    assert!(
        matches!(&errors[0], ValidationError::UnboundFVar { fvar: f, context: "jmp target" } if *f == fvar(99)),
        "expected UnboundFVar for jmp target: {errors:?}"
    );
}

#[test]
fn test_validate_jmp_unbound_arg() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::join_point(
            FunDecl::new(
                fvar(10),
                name("jp"),
                vec![Param::new(fvar(11), name("r"), nat_ty())],
                nat_ty(),
                Code::ret(fvar(11)),
            ),
            Code::jmp(fvar(10), vec![Arg::FVar(fvar(99))]),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(
        errors.len(),
        1,
        "expected 1 error for unbound jmp arg: {errors:?}"
    );
    assert!(
        matches!(&errors[0], ValidationError::UnboundFVar { fvar: f, context: "jmp argument" } if *f == fvar(99)),
        "expected UnboundFVar for jmp argument: {errors:?}"
    );
}

#[test]
fn test_validate_erased_args_ignored() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_ty(),
                LetValue::Const {
                    name: name("Nat.zero"),
                    levels: vec![],
                    args: vec![Arg::Erased, Arg::Type(Expr::prop())],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert!(
        errors.is_empty(),
        "erased/type args should not cause errors: {errors:?}"
    );
}

#[test]
fn test_validate_nested_join_point_in_fun() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::fun(
            FunDecl::new(
                fvar(10),
                name("g"),
                vec![Param::new(fvar(11), name("y"), nat_ty())],
                nat_ty(),
                Code::join_point(
                    FunDecl::new(
                        fvar(20),
                        name("jp"),
                        vec![Param::new(fvar(21), name("r"), nat_ty())],
                        nat_ty(),
                        Code::ret(fvar(21)),
                    ),
                    Code::jmp(fvar(20), vec![Arg::FVar(fvar(11))]),
                ),
            ),
            Code::ret(fvar(10)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert!(
        errors.is_empty(),
        "nested jp in fun should validate: {errors:?}"
    );
}

#[test]
fn test_validate_multiple_errors() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_ty(),
        vec![],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_ty(),
                LetValue::FVar {
                    fvar: fvar(50),
                    args: vec![Arg::FVar(fvar(60))],
                },
            ),
            Code::ret(fvar(99)),
        ),
        false,
    );
    let errors = validate_decl(&decl);
    assert_eq!(errors.len(), 3, "expected 3 errors: {errors:?}");
}
