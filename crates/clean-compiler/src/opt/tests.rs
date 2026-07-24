// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Arg, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn test_optimize_code_basic() {
    // let _1 := 1
    // let _2 := 2
    // let _3 := Nat.add _1 _2
    // return _3
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(2)),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("_3"),
                    nat_type(),
                    LetValue::Const {
                        name: name("Nat.add"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );

    let config = OptConfig::default();
    let result = optimize_code(&code, &config);

    // Check that optimization produced some result
    match result {
        Code::Let(_, _) => {}
        Code::Return(_) => {}
        _ => panic!("Unexpected result: {:?}", result),
    }
}

#[test]
fn test_optimize_fixpoint_convergence() {
    // Simple code that should reach fixpoint in 1 iteration
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::ret(fvar(1)),
    );

    let config = OptConfig::default();
    let result = optimize_code(&code, &config);

    assert!(matches!(result, Code::Let(_, _)));
}

#[test]
fn test_optimize_minimal_config() {
    // With minimal config (only DCE), other optimizations should not run
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_unused"), nat_type(), LetValue::nat(1)),
        Code::let_bind(
            LetDecl::new(fvar(2), name("_used"), nat_type(), LetValue::nat(2)),
            Code::ret(fvar(2)),
        ),
    );

    let config = OptConfig::minimal();
    let result = optimize_code(&code, &config);

    // DCE should remove _unused, keep _used
    match result {
        Code::Let(decl, _) => {
            assert_eq!(decl.fvar_id, fvar(2));
        }
        _ => panic!("Expected single let binding, got {:?}", result),
    }
}

#[test]
fn test_optimize_disable_inline() {
    let fun_decl = crate::lcnf::FunDecl::new(
        fvar(1),
        name("f"),
        vec![],
        nat_type(),
        Code::let_bind(
            LetDecl::new(fvar(10), name("_"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(10)),
        ),
    );

    let code = Code::fun(
        fun_decl,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("x"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let config = OptConfig {
        max_iterations: 1,
        inline_threshold: 0,
        enable_cse: false,
        enable_constant_fold: false,
        enable_simp_value: false,
        enable_dce: false,
        enable_inline: false,
        enable_join_points: false,
        enable_specialize: false,
        enable_lambda_lift: false,
        enable_extract_closed: false,
        enable_pull_let_decls: false,
    };
    let result = optimize_code(&code, &config);

    let s = result.to_string();
    assert!(s.contains("fun _x1"), "Inline should be disabled:\n{s}");
}

#[test]
fn test_optimize_decl() {
    let decl = Decl::new(
        name("test_fn"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(100)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let config = OptConfig::default();
    let result = optimize(&decl, &config);

    assert_eq!(result.name, name("test_fn"));
    assert!(matches!(result.body, DeclValue::Code(_)));
}

#[test]
fn test_join_points_after_optimization() {
    // fun loop (n : Nat) : Nat := return n
    // let _1 := loop 42
    // return _1
    // Use a config with only join point conversion enabled
    let loop_decl = crate::lcnf::FunDecl::new(
        fvar(1),
        name("loop"),
        vec![Param::new(fvar(10), name("n"), nat_type())],
        nat_type(),
        Code::ret(fvar(10)),
    );

    let code = Code::fun(
        loop_decl,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![Arg::FVar(fvar(100))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );

    let config = OptConfig {
        max_iterations: 1,
        inline_threshold: 0,
        enable_cse: false,
        enable_constant_fold: false,
        enable_simp_value: false,
        enable_dce: false,
        enable_inline: false,
        enable_join_points: true,
        enable_specialize: false,
        enable_lambda_lift: false,
        enable_extract_closed: false,
        enable_pull_let_decls: false,
    };
    let result = optimize_code(&code, &config);

    // Should have converted to JoinPoint
    match result {
        Code::JoinPoint(jp_decl, body) => {
            assert_eq!(jp_decl.fvar_id, fvar(1));
            assert!(matches!(*body, Code::Jmp { .. }));
        }
        _ => panic!("Expected JoinPoint, got {:?}", result),
    }
}

#[test]
fn test_optimize_all_batch() {
    // Test that optimize_all processes multiple declarations
    let decl1 = Decl::new(
        name("fn1"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(1)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let decl2 = Decl::new(
        name("fn2"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(2), name("_2"), nat_type(), LetValue::nat(2)),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let decls = vec![decl1, decl2];
    let config = OptConfig::default();
    let results = optimize_all(&decls, &config);

    // Should have at least as many results as input
    // (specialization might add more)
    assert!(results.len() >= 2);
    assert_eq!(results[0].name, name("fn1"));
    assert_eq!(results[1].name, name("fn2"));
}

#[test]
fn test_optimize_all_with_specialize_disabled() {
    // Verify optimize_all works with specialization disabled
    let decl = Decl::new(
        name("fn1"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let config = OptConfig {
        enable_specialize: false,
        ..Default::default()
    };
    let results = optimize_all(&[decl], &config);

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, name("fn1"));
}

/// Build a decl containing a local function (Code::Fun) for lambda lift tests.
fn make_decl_with_local_fn() -> Decl {
    let inner_fn = crate::lcnf::FunDecl::new(
        fvar(1),
        name("inner"),
        vec![Param::new(fvar(10), name("x"), nat_type())],
        nat_type(),
        Code::ret(fvar(10)),
    );
    let code = Code::fun(
        inner_fn,
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("result"),
                nat_type(),
                LetValue::FVar {
                    fvar: fvar(1),
                    args: vec![Arg::FVar(fvar(100))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );
    Decl::new(name("outer"), vec![], nat_type(), vec![], code, false)
}

#[test]
fn test_optimize_all_lambda_lift_produces_lifted_decls() {
    // With lambda lifting enabled, local functions are lifted to top-level decls
    let decl = make_decl_with_local_fn();
    let config = OptConfig {
        enable_specialize: false,
        ..Default::default()
    };
    let results = optimize_all(&[decl], &config);

    assert!(
        results.len() > 1,
        "Lambda lifting should produce additional declarations, got {}",
        results.len()
    );

    let outer = &results[0];
    assert_eq!(outer.name, name("outer"));
    if let DeclValue::Code(body) = &outer.body {
        let s = body.to_string();
        assert!(
            !s.contains("fun "),
            "Local function should have been lifted out of the body:\n{s}"
        );
    }

    let has_lifted = results
        .iter()
        .skip(1)
        .any(|d| d.name.to_string().contains("inner"));
    assert!(
        has_lifted,
        "Should find a lifted declaration named after 'inner'"
    );
}

#[test]
fn test_optimize_all_lambda_lift_disabled_preserves_fun() {
    // With lambda lifting disabled, Code::Fun nodes remain untouched
    let decl = make_decl_with_local_fn();
    let config = OptConfig {
        enable_specialize: false,
        enable_lambda_lift: false,
        ..Default::default()
    };
    let results = optimize_all(&[decl], &config);

    assert_eq!(
        results.len(),
        1,
        "Without lambda lifting, should have exactly 1 declaration"
    );
}
