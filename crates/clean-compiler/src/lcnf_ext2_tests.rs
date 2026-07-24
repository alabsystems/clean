// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for LCNF extended transformations (lcnf_ext2): substitution,
//! alpha-equivalence, and validation.

use crate::lcnf::{Alt, Arg, Code, FunDecl, LetDecl, LetValue, Param};
use crate::lcnf_ext2::*;
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

/// Helper: `let _xN := 42; return _xN`
fn simple_let(id: u64) -> Code {
    Code::let_bind(
        LetDecl::new(fvar(id), name("v"), nat_ty(), LetValue::nat(42)),
        Code::ret(fvar(id)),
    )
}

// ════════════════════════════════════════════════════════════════════════════
// Substitution
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_substitute_return() {
    let code = Code::ret(fvar(0));
    let result = substitute_fvar(&code, fvar(0), fvar(99)).expect("should succeed");
    assert_eq!(result, Code::ret(fvar(99)));
}

#[test]
fn test_substitute_not_found() {
    let code = Code::ret(fvar(0));
    assert!(substitute_fvar(&code, fvar(999), fvar(1)).is_err());
}

#[test]
fn test_substitute_in_let_value_const_args() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("r"),
            nat_ty(),
            LetValue::Const {
                name: name("f"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );
    let result = substitute_fvar(&code, fvar(0), fvar(5)).expect("should succeed");
    if let Code::Let(decl, _) = &result {
        if let LetValue::Const { args, .. } = &decl.value {
            assert_eq!(args[0], Arg::FVar(fvar(5)));
            return;
        }
    }
    panic!("unexpected structure after substitution");
}

#[test]
fn test_substitute_scrutinee() {
    let code = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(3),
        vec![Alt::default(Code::ret(fvar(3)))],
    );
    let result = substitute_fvar(&code, fvar(3), fvar(7)).expect("should succeed");
    if let Code::Cases(cases) = &result {
        assert_eq!(cases.scrutinee, fvar(7));
    } else {
        panic!("expected Cases");
    }
}

#[test]
fn test_substitute_jmp_jp_and_args() {
    let code = Code::jmp(fvar(10), vec![Arg::FVar(fvar(10))]);
    let result = substitute_fvar(&code, fvar(10), fvar(20)).expect("should succeed");
    if let Code::Jmp { jp, args } = &result {
        assert_eq!(*jp, fvar(20));
        assert_eq!(args[0], Arg::FVar(fvar(20)));
    } else {
        panic!("expected Jmp");
    }
}

#[test]
fn test_substitute_in_reuse() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(5),
            name("v"),
            nat_ty(),
            LetValue::Reuse {
                slot: fvar(0),
                ctor_name: name("List.cons"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(5)),
    );
    let result = substitute_fvar(&code, fvar(0), fvar(9)).expect("should succeed");
    if let Code::Let(decl, _) = &result {
        if let LetValue::Reuse { slot, args, .. } = &decl.value {
            assert_eq!(*slot, fvar(9));
            assert_eq!(args[0], Arg::FVar(fvar(9)));
            return;
        }
    }
    panic!("unexpected structure");
}

#[test]
fn test_substitute_proj_structure() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("p"),
            nat_ty(),
            LetValue::Proj {
                type_name: name("Prod"),
                idx: 0,
                structure: fvar(0),
            },
        ),
        Code::ret(fvar(1)),
    );
    let result = substitute_fvar(&code, fvar(0), fvar(7)).expect("should succeed");
    if let Code::Let(decl, _) = &result {
        if let LetValue::Proj { structure, .. } = &decl.value {
            assert_eq!(*structure, fvar(7));
            return;
        }
    }
    panic!("unexpected structure");
}

#[test]
fn test_substitute_fvar_call() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(2),
            name("r"),
            nat_ty(),
            LetValue::FVar {
                fvar: fvar(0),
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::ret(fvar(2)),
    );
    let result = substitute_fvar(&code, fvar(0), fvar(9)).expect("should succeed");
    if let Code::Let(decl, _) = &result {
        if let LetValue::FVar { fvar: f, .. } = &decl.value {
            assert_eq!(*f, fvar(9));
            return;
        }
    }
    panic!("unexpected structure");
}

// ════════════════════════════════════════════════════════════════════════════
// Alpha equivalence
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_alpha_eq_identical_returns() {
    assert!(alpha_eq(&Code::ret(fvar(0)), &Code::ret(fvar(0))));
}

#[test]
fn test_alpha_eq_different_free_vars() {
    assert!(!alpha_eq(&Code::ret(fvar(0)), &Code::ret(fvar(1))));
}

#[test]
fn test_alpha_eq_let_renamed() {
    assert!(alpha_eq(&simple_let(0), &simple_let(99)));
}

#[test]
fn test_alpha_eq_different_values() {
    let a = Code::let_bind(
        LetDecl::new(fvar(0), name("v"), nat_ty(), LetValue::nat(1)),
        Code::ret(fvar(0)),
    );
    let b = Code::let_bind(
        LetDecl::new(fvar(0), name("v"), nat_ty(), LetValue::nat(2)),
        Code::ret(fvar(0)),
    );
    assert!(!alpha_eq(&a, &b));
}

#[test]
fn test_alpha_eq_unreachable() {
    assert!(alpha_eq(
        &Code::Unreachable(nat_ty()),
        &Code::Unreachable(Expr::const_str("Bool")),
    ));
}

#[test]
fn test_alpha_eq_fun_renamed_params() {
    let fa = FunDecl::new(
        fvar(0),
        name("f"),
        vec![Param::new(fvar(1), name("a"), nat_ty())],
        nat_ty(),
        Code::ret(fvar(1)),
    );
    let fb = FunDecl::new(
        fvar(100),
        name("g"),
        vec![Param::new(fvar(200), name("b"), nat_ty())],
        nat_ty(),
        Code::ret(fvar(200)),
    );
    assert!(alpha_eq(
        &Code::fun(fa, Code::ret(fvar(0))),
        &Code::fun(fb, Code::ret(fvar(100))),
    ));
}

#[test]
fn test_alpha_eq_cases_ctor_name_matters() {
    let a = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(0),
        vec![Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(0)))],
    );
    let b = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(0),
        vec![Alt::ctor(name("Bool.false"), vec![], Code::ret(fvar(0)))],
    );
    assert!(!alpha_eq(&a, &b));
}

#[test]
fn test_alpha_eq_different_kinds() {
    assert!(!alpha_eq(&Code::ret(fvar(0)), &Code::Unreachable(nat_ty())));
}

#[test]
fn test_alpha_eq_jmp() {
    let a = Code::jmp(fvar(0), vec![Arg::FVar(fvar(1))]);
    let b = Code::jmp(fvar(0), vec![Arg::FVar(fvar(1))]);
    assert!(alpha_eq(&a, &b));
}

#[test]
fn test_alpha_eq_default_alt() {
    let a = Code::cases(
        name("X"),
        nat_ty(),
        fvar(0),
        vec![Alt::default(Code::ret(fvar(0)))],
    );
    let b = Code::cases(
        name("X"),
        nat_ty(),
        fvar(0),
        vec![Alt::default(Code::ret(fvar(0)))],
    );
    assert!(alpha_eq(&a, &b));
}

#[test]
fn test_alpha_eq_different_alt_count() {
    let a = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(0),
        vec![Alt::default(Code::ret(fvar(0)))],
    );
    let b = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(0),
        vec![
            Alt::ctor(name("Bool.true"), vec![], Code::ret(fvar(0))),
            Alt::default(Code::ret(fvar(0))),
        ],
    );
    assert!(!alpha_eq(&a, &b));
}

// ════════════════════════════════════════════════════════════════════════════
// Validation
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_validate_simple_let_ok() {
    validate(&simple_let(0)).expect("should be valid");
}

#[test]
fn test_validate_unbound_return() {
    let err = validate(&Code::ret(fvar(99)));
    assert!(err.is_err());
    let msg = err.unwrap_err().to_string();
    assert!(msg.contains("99"), "error should mention FVarId: {msg}");
}

#[test]
fn test_validate_unbound_in_let_value() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(0),
            name("v"),
            nat_ty(),
            LetValue::FVar {
                fvar: fvar(77),
                args: vec![],
            },
        ),
        Code::ret(fvar(0)),
    );
    assert!(validate(&code).is_err());
}

#[test]
fn test_validate_duplicate_binding() {
    let code = Code::let_bind(
        LetDecl::new(fvar(0), name("a"), nat_ty(), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(0), name("b"), nat_ty(), LetValue::nat(2)),
            Code::ret(fvar(0)),
        ),
    );
    let msg = validate(&code).unwrap_err().to_string();
    assert!(msg.contains("duplicate"), "expected duplicate error: {msg}");
}

#[test]
fn test_validate_jp_arity_mismatch() {
    let jp = FunDecl::new(
        fvar(10),
        name("jp"),
        vec![
            Param::new(fvar(11), name("a"), nat_ty()),
            Param::new(fvar(12), name("b"), nat_ty()),
        ],
        nat_ty(),
        Code::ret(fvar(11)),
    );
    let code = Code::let_bind(
        LetDecl::new(fvar(0), name("x"), nat_ty(), LetValue::nat(0)),
        Code::join_point(jp, Code::jmp(fvar(10), vec![Arg::FVar(fvar(0))])),
    );
    let msg = validate(&code).unwrap_err().to_string();
    assert!(msg.contains("expects 2"), "expected arity error: {msg}");
}

#[test]
fn test_validate_cases_bound_params() {
    let code = Code::let_bind(
        LetDecl::new(fvar(0), name("s"), nat_ty(), LetValue::nat(0)),
        Code::cases(
            name("List"),
            nat_ty(),
            fvar(0),
            vec![Alt::ctor(
                name("List.cons"),
                vec![
                    Param::new(fvar(1), name("hd"), nat_ty()),
                    Param::new(fvar(2), name("tl"), nat_ty()),
                ],
                Code::ret(fvar(1)),
            )],
        ),
    );
    validate(&code).expect("should be valid");
}

#[test]
fn test_validate_unreachable_always_ok() {
    validate(&Code::Unreachable(nat_ty())).expect("unreachable is always valid");
}

#[test]
fn test_validate_unbound_scrutinee() {
    let code = Code::cases(
        name("Bool"),
        nat_ty(),
        fvar(42),
        vec![Alt::default(Code::Unreachable(nat_ty()))],
    );
    let msg = validate(&code).unwrap_err().to_string();
    assert!(msg.contains("42"), "expected unbound error: {msg}");
}

#[test]
fn test_validate_unbound_jmp_arg() {
    let jp = FunDecl::new(
        fvar(10),
        name("jp"),
        vec![Param::new(fvar(11), name("a"), nat_ty())],
        nat_ty(),
        Code::ret(fvar(11)),
    );
    let code = Code::join_point(jp, Code::jmp(fvar(10), vec![Arg::FVar(fvar(99))]));
    assert!(validate(&code).is_err());
}

#[test]
fn test_validate_fun_params_scoped() {
    let fun = FunDecl::new(
        fvar(5),
        name("f"),
        vec![Param::new(fvar(6), name("x"), nat_ty())],
        nat_ty(),
        Code::ret(fvar(6)),
    );
    // In the continuation, fvar(6) should NOT be in scope
    let code = Code::fun(fun, Code::ret(fvar(5)));
    validate(&code).expect("fun decl with proper scoping should be valid");
}

#[test]
fn test_validate_fun_param_not_leaked() {
    let fun = FunDecl::new(
        fvar(5),
        name("f"),
        vec![Param::new(fvar(6), name("x"), nat_ty())],
        nat_ty(),
        Code::ret(fvar(6)),
    );
    // Try to use fvar(6) in the continuation -- should fail
    let code = Code::fun(fun, Code::ret(fvar(6)));
    assert!(validate(&code).is_err());
}
