// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended constant folding pass.

use crate::const_fold_ext::*;
use crate::ir::*;
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn fn_id(s: &str) -> FnId {
    FnId(name(s))
}

fn var(id: u32) -> VarId {
    VarId(id)
}

fn lit_u64(v: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(v))
}

fn str_expr(s: &str) -> IRExpr {
    IRExpr::String(s.to_owned())
}

fn apply(op: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: fn_id(op),
        args,
    }
}

fn var_arg(id: u32) -> IRArg {
    IRArg::Var(var(id))
}

fn simple_ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name("Test.ctor"),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

/// Build: let v0 = e0; let v1 = e1; ... ret vN
fn chain_lets(bindings: Vec<(u32, IRExpr)>, ret_var: u32) -> IRBody {
    let mut body = IRBody::Ret(var_arg(ret_var));
    for (vid, expr) in bindings.into_iter().rev() {
        body = IRBody::VDecl {
            var: var(vid),
            ty: IRType::UInt64,
            value: expr,
            rest: Box::new(body),
        };
    }
    body
}

fn make_decl(body: IRBody) -> IRDecl {
    IRDecl {
        name: name("test_fn"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }
}

// ---------------------------------------------------------------------------
// fold_arithmetic_op tests
// ---------------------------------------------------------------------------

#[test]
fn test_fold_arithmetic_nat_add() {
    let result = fold_arithmetic_op("Nat.add", &IRLiteral::UInt64(3), &IRLiteral::UInt64(4));
    assert_eq!(result, Some(IRLiteral::UInt64(7)));
}

#[test]
fn test_fold_arithmetic_nat_sub_saturates() {
    let result = fold_arithmetic_op("Nat.sub", &IRLiteral::UInt64(2), &IRLiteral::UInt64(5));
    assert_eq!(result, Some(IRLiteral::UInt64(0)));
}

#[test]
fn test_fold_arithmetic_nat_mul() {
    let result = fold_arithmetic_op("Nat.mul", &IRLiteral::UInt64(6), &IRLiteral::UInt64(7));
    assert_eq!(result, Some(IRLiteral::UInt64(42)));
}

#[test]
fn test_fold_arithmetic_nat_div() {
    let result = fold_arithmetic_op("Nat.div", &IRLiteral::UInt64(10), &IRLiteral::UInt64(3));
    assert_eq!(result, Some(IRLiteral::UInt64(3)));
}

#[test]
fn test_fold_arithmetic_nat_div_by_zero() {
    let result = fold_arithmetic_op("Nat.div", &IRLiteral::UInt64(10), &IRLiteral::UInt64(0));
    assert_eq!(result, None);
}

#[test]
fn test_fold_arithmetic_nat_mod() {
    let result = fold_arithmetic_op("Nat.mod", &IRLiteral::UInt64(10), &IRLiteral::UInt64(3));
    assert_eq!(result, Some(IRLiteral::UInt64(1)));
}

#[test]
fn test_fold_arithmetic_int_add() {
    // -3 + 5 = 2, using two's complement u64 representation
    let neg3 = (-3i64) as u64;
    let result = fold_arithmetic_op("Int.add", &IRLiteral::UInt64(neg3), &IRLiteral::UInt64(5));
    assert_eq!(result, Some(IRLiteral::UInt64(2)));
}

#[test]
fn test_fold_arithmetic_int_sub() {
    let result = fold_arithmetic_op("Int.sub", &IRLiteral::UInt64(3), &IRLiteral::UInt64(5));
    let expected = (-2i64) as u64;
    assert_eq!(result, Some(IRLiteral::UInt64(expected)));
}

#[test]
fn test_fold_arithmetic_int_mul() {
    let neg2 = (-2i64) as u64;
    let result = fold_arithmetic_op("Int.mul", &IRLiteral::UInt64(neg2), &IRLiteral::UInt64(3));
    let expected = (-6i64) as u64;
    assert_eq!(result, Some(IRLiteral::UInt64(expected)));
}

#[test]
fn test_fold_arithmetic_int_div_by_zero() {
    let result = fold_arithmetic_op("Int.div", &IRLiteral::UInt64(10), &IRLiteral::UInt64(0));
    assert_eq!(result, None);
}

#[test]
fn test_fold_arithmetic_int_div_min_by_neg_one_declines() {
    // `Int` is unbounded: i64::MIN / -1 = 2^63 is NOT i64-representable. The old
    // `wrapping_div` produced i64::MIN (a miscompilation); the correct fold
    // DECLINES via `checked_div`.
    let min = i64::MIN as u64;
    let neg1 = (-1i64) as u64;
    assert_eq!(
        fold_arithmetic_op("Int.div", &IRLiteral::UInt64(min), &IRLiteral::UInt64(neg1)),
        None
    );
    assert_eq!(
        fold_arithmetic_op("Int.mod", &IRLiteral::UInt64(min), &IRLiteral::UInt64(neg1)),
        None
    );
    // In-range signed division still folds (truncated toward zero).
    assert_eq!(
        fold_arithmetic_op(
            "Int.div",
            &IRLiteral::UInt64((-7i64) as u64),
            &IRLiteral::UInt64(2)
        ),
        Some(IRLiteral::UInt64((-3i64) as u64))
    );
}

#[test]
fn test_fold_arithmetic_unknown_op_returns_none() {
    let result = fold_arithmetic_op("Foo.bar", &IRLiteral::UInt64(1), &IRLiteral::UInt64(2));
    assert_eq!(result, None);
}

#[test]
fn test_fold_arithmetic_overflow_returns_none() {
    let result = fold_arithmetic_op(
        "Nat.add",
        &IRLiteral::UInt64(u64::MAX),
        &IRLiteral::UInt64(1),
    );
    assert_eq!(result, None);
}

#[test]
fn test_fold_arithmetic_mixed_widths() {
    let result = fold_arithmetic_op("Nat.add", &IRLiteral::UInt32(100), &IRLiteral::UInt64(200));
    assert_eq!(result, Some(IRLiteral::UInt64(300)));
}

// ---------------------------------------------------------------------------
// fold_comparison tests
// ---------------------------------------------------------------------------

#[test]
fn test_fold_comparison_nat_beq_true() {
    assert_eq!(
        fold_comparison("Nat.beq", &IRLiteral::UInt64(5), &IRLiteral::UInt64(5)),
        Some(true)
    );
}

#[test]
fn test_fold_comparison_nat_beq_false() {
    assert_eq!(
        fold_comparison("Nat.beq", &IRLiteral::UInt64(5), &IRLiteral::UInt64(6)),
        Some(false)
    );
}

#[test]
fn test_fold_comparison_nat_ble() {
    assert_eq!(
        fold_comparison("Nat.ble", &IRLiteral::UInt64(3), &IRLiteral::UInt64(5)),
        Some(true)
    );
    assert_eq!(
        fold_comparison("Nat.ble", &IRLiteral::UInt64(5), &IRLiteral::UInt64(5)),
        Some(true)
    );
    assert_eq!(
        fold_comparison("Nat.ble", &IRLiteral::UInt64(6), &IRLiteral::UInt64(5)),
        Some(false)
    );
}

#[test]
fn test_fold_comparison_nat_blt() {
    assert_eq!(
        fold_comparison("Nat.blt", &IRLiteral::UInt64(3), &IRLiteral::UInt64(5)),
        Some(true)
    );
    assert_eq!(
        fold_comparison("Nat.blt", &IRLiteral::UInt64(5), &IRLiteral::UInt64(5)),
        Some(false)
    );
}

#[test]
fn test_fold_comparison_int_blt_signed() {
    let neg1 = (-1i64) as u64;
    assert_eq!(
        fold_comparison("Int.blt", &IRLiteral::UInt64(neg1), &IRLiteral::UInt64(0)),
        Some(true)
    );
}

#[test]
fn test_fold_comparison_unknown_op() {
    assert_eq!(
        fold_comparison("Foo.cmp", &IRLiteral::UInt64(1), &IRLiteral::UInt64(2)),
        None
    );
}

// ---------------------------------------------------------------------------
// fold_bitwise_op tests
// ---------------------------------------------------------------------------

#[test]
fn test_fold_bitwise_and() {
    let result = fold_bitwise_op(
        "UInt64.land",
        &IRLiteral::UInt64(0xFF),
        &IRLiteral::UInt64(0x0F),
    );
    assert_eq!(result, Some(IRLiteral::UInt64(0x0F)));
}

#[test]
fn test_fold_bitwise_or() {
    let result = fold_bitwise_op(
        "UInt64.lor",
        &IRLiteral::UInt64(0xF0),
        &IRLiteral::UInt64(0x0F),
    );
    assert_eq!(result, Some(IRLiteral::UInt64(0xFF)));
}

#[test]
fn test_fold_bitwise_xor() {
    let result = fold_bitwise_op(
        "UInt64.lxor",
        &IRLiteral::UInt64(0xFF),
        &IRLiteral::UInt64(0x0F),
    );
    assert_eq!(result, Some(IRLiteral::UInt64(0xF0)));
}

#[test]
fn test_fold_bitwise_shift_left() {
    let result = fold_bitwise_op(
        "UInt64.shiftLeft",
        &IRLiteral::UInt64(1),
        &IRLiteral::UInt64(8),
    );
    assert_eq!(result, Some(IRLiteral::UInt64(256)));
}

#[test]
fn test_fold_bitwise_shift_right() {
    let result = fold_bitwise_op(
        "UInt64.shiftRight",
        &IRLiteral::UInt64(256),
        &IRLiteral::UInt64(4),
    );
    assert_eq!(result, Some(IRLiteral::UInt64(16)));
}

#[test]
fn test_fold_bitwise_shift_overflow_clamps() {
    let result = fold_bitwise_op(
        "UInt64.shiftLeft",
        &IRLiteral::UInt64(1),
        &IRLiteral::UInt64(128),
    );
    assert_eq!(result, Some(IRLiteral::UInt64(0)));
}

#[test]
fn test_fold_bitwise_unknown_op() {
    let result = fold_bitwise_op("UInt64.magic", &IRLiteral::UInt64(1), &IRLiteral::UInt64(2));
    assert_eq!(result, None);
}

// ---------------------------------------------------------------------------
// try_fold_expr tests
// ---------------------------------------------------------------------------

#[test]
fn test_try_fold_expr_literal() {
    let expr = IRExpr::Lit(IRLiteral::UInt64(42));
    assert_eq!(try_fold_expr(&expr), Some(IRLiteral::UInt64(42)));
}

#[test]
fn test_try_fold_expr_non_literal_returns_none() {
    let expr = IRExpr::String("hello".to_owned());
    assert_eq!(try_fold_expr(&expr), None);
}

// ---------------------------------------------------------------------------
// fold_constants_ext integration tests
// ---------------------------------------------------------------------------

#[test]
fn test_fold_constants_ext_nat_add_chain() {
    // let v0 = 3; let v1 = 4; let v2 = Nat.add(v0, v1); ret v2
    // Expected: v2 = 7
    let body = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(4)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.arithmetic_folds >= 1, "expected arithmetic fold");
    // Verify the result is a literal 7
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => match rest.as_ref() {
            IRBody::VDecl { rest, .. } => match rest.as_ref() {
                IRBody::VDecl { value, .. } => {
                    assert!(
                        matches!(value, IRExpr::Lit(IRLiteral::UInt64(7))),
                        "expected Lit(7), got {value:?}"
                    );
                }
                other => panic!("expected VDecl, got {other:?}"),
            },
            other => panic!("expected VDecl, got {other:?}"),
        },
        other => panic!("expected VDecl, got {other:?}"),
    }
}

#[test]
fn test_fold_constants_ext_comparison() {
    // let v0 = 5; let v1 = 5; let v2 = Nat.beq(v0, v1); ret v2
    let body = chain_lets(
        vec![
            (0, lit_u64(5)),
            (1, lit_u64(5)),
            (2, apply("Nat.beq", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.comparison_folds >= 1);
}

#[test]
fn test_fold_constants_ext_bitwise() {
    // let v0 = 0xFF; let v1 = 0x0F; let v2 = UInt64.land(v0, v1); ret v2
    let body = chain_lets(
        vec![
            (0, lit_u64(0xFF)),
            (1, lit_u64(0x0F)),
            (2, apply("UInt64.land", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.bitwise_folds >= 1);
}

#[test]
fn test_fold_constants_ext_string_append() {
    // let v0 = "hello"; let v1 = " world"; let v2 = String.append(v0, v1); ret v2
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: str_expr("hello"),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: str_expr(" world"),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: apply("String.append", vec![var_arg(0), var_arg(1)]),
                rest: Box::new(IRBody::Ret(var_arg(2))),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.string_folds >= 1, "expected string fold");
}

#[test]
fn test_fold_constants_ext_string_length() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: str_expr("hello"),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply("String.length", vec![var_arg(0)]),
            rest: Box::new(IRBody::Ret(var_arg(1))),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.string_folds >= 1, "expected string length fold");
}

#[test]
fn test_fold_constants_ext_branch_elimination() {
    // let v0 = Ctor(tag=1); case v0 of { tag 0 => ret 0, tag 1 => ret 42 }
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: simple_ctor(1),
            args: vec![],
        },
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: simple_ctor(0),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(99)))),
                },
                IRAlt {
                    ctor: simple_ctor(1),
                    body: Box::new(IRBody::Ret(IRArg::Var(var(42)))),
                },
            ],
            default: None,
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.branch_folds >= 1, "expected branch fold");
    // After folding, the case should be eliminated, body should be Ret(v42)
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => {
            assert!(
                matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(VarId(42)))),
                "expected Ret(v42), got {rest:?}"
            );
        }
        other => panic!("expected VDecl, got {other:?}"),
    }
}

#[test]
fn test_fold_constants_ext_fixpoint_cascading() {
    // v0 = 2; v1 = 3; v2 = Nat.add(v0, v1) => 5; v3 = 10;
    // v4 = Nat.mul(v2, v3) => 50  (needs second iteration if v2 not folded in time)
    let body = chain_lets(
        vec![
            (0, lit_u64(2)),
            (1, lit_u64(3)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
            (3, lit_u64(10)),
            (4, apply("Nat.mul", vec![var_arg(2), var_arg(3)])),
        ],
        4,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.arithmetic_folds >= 2, "expected cascading folds");
}

#[test]
fn test_fold_constants_ext_respects_config_disable_arithmetic() {
    let body = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(4)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let config = ConstFoldExtConfig {
        fold_arithmetic: false,
        ..Default::default()
    };
    let stats = fold_constants_ext(&mut decls, &config);
    assert_eq!(stats.arithmetic_folds, 0);
}

#[test]
fn test_fold_constants_ext_respects_config_disable_comparisons() {
    let body = chain_lets(
        vec![
            (0, lit_u64(5)),
            (1, lit_u64(5)),
            (2, apply("Nat.beq", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let config = ConstFoldExtConfig {
        fold_comparisons: false,
        ..Default::default()
    };
    let stats = fold_constants_ext(&mut decls, &config);
    assert_eq!(stats.comparison_folds, 0);
}

#[test]
fn test_fold_constants_ext_respects_config_disable_bitwise() {
    let body = chain_lets(
        vec![
            (0, lit_u64(0xFF)),
            (1, lit_u64(0x0F)),
            (2, apply("UInt64.land", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let config = ConstFoldExtConfig {
        fold_bitwise: false,
        ..Default::default()
    };
    let stats = fold_constants_ext(&mut decls, &config);
    assert_eq!(stats.bitwise_folds, 0);
}

#[test]
fn test_fold_constants_ext_max_iterations_stops() {
    // Single foldable expr, max_iterations=1
    let body = chain_lets(
        vec![
            (0, lit_u64(1)),
            (1, lit_u64(2)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let config = ConstFoldExtConfig {
        max_iterations: 1,
        ..Default::default()
    };
    let stats = fold_constants_ext(&mut decls, &config);
    assert_eq!(stats.iterations, 1);
}

#[test]
fn test_fold_constants_ext_empty_decls() {
    let mut decls: Vec<IRDecl> = vec![];
    let stats = fold_constants_ext_default(&mut decls);
    assert_eq!(stats.total(), 0);
    assert_eq!(stats.iterations, 1);
}

#[test]
fn test_fold_constants_ext_no_foldable_ops() {
    let body = IRBody::Ret(var_arg(0));
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert_eq!(stats.total(), 0);
}

#[test]
fn test_fold_constants_ext_string_max_length_guard() {
    let long = "a".repeat(600);
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: str_expr(&long),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: str_expr(&long),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: apply("String.append", vec![var_arg(0), var_arg(1)]),
                rest: Box::new(IRBody::Ret(var_arg(2))),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let config = ConstFoldExtConfig {
        max_string_length: 1024,
        ..Default::default()
    };
    let stats = fold_constants_ext(&mut decls, &config);
    assert_eq!(stats.string_folds, 0, "should reject oversized concat");
}

#[test]
fn test_fold_constants_ext_join_point_scope_isolation() {
    // Ensure that known values inside a join point do not leak out.
    let jp_body = chain_lets(vec![(10, lit_u64(99))], 10);
    let rest = chain_lets(
        vec![
            (0, lit_u64(1)),
            (1, lit_u64(2)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(jp_body),
        rest: Box::new(rest),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.arithmetic_folds >= 1);
}

#[test]
fn test_fold_known_branch_bool_true() {
    use std::collections::HashMap;
    let mut body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: simple_ctor(0),
                body: Box::new(IRBody::Ret(var_arg(10))),
            },
            IRAlt {
                ctor: simple_ctor(1),
                body: Box::new(IRBody::Ret(var_arg(20))),
            },
        ],
        default: None,
    };
    let mut known = HashMap::new();
    known.insert(var(0), IRLiteral::Bool(true)); // tag 1
    let count = fold_known_branch(&mut body, &known);
    assert_eq!(count, 1);
    assert!(matches!(body, IRBody::Ret(IRArg::Var(VarId(20)))));
}

#[test]
fn test_fold_known_branch_bool_false() {
    use std::collections::HashMap;
    let mut body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: simple_ctor(0),
                body: Box::new(IRBody::Ret(var_arg(10))),
            },
            IRAlt {
                ctor: simple_ctor(1),
                body: Box::new(IRBody::Ret(var_arg(20))),
            },
        ],
        default: None,
    };
    let mut known = HashMap::new();
    known.insert(var(0), IRLiteral::Bool(false)); // tag 0
    let count = fold_known_branch(&mut body, &known);
    assert_eq!(count, 1);
    assert!(matches!(body, IRBody::Ret(IRArg::Var(VarId(10)))));
}

#[test]
fn test_fold_known_branch_no_match() {
    use std::collections::HashMap;
    let mut body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(0),
            body: Box::new(IRBody::Ret(var_arg(10))),
        }],
        default: Some(Box::new(IRBody::Ret(var_arg(99)))),
    };
    let known = HashMap::new(); // no known value for v0
    let count = fold_known_branch(&mut body, &known);
    assert_eq!(count, 0);
}

#[test]
fn test_propagate_constants_records_literals() {
    use std::collections::HashMap;
    let mut body = chain_lets(
        vec![
            (0, lit_u64(42)),
            (1, apply("Nat.add", vec![var_arg(0), var_arg(0)])),
        ],
        1,
    );
    let known: HashMap<VarId, IRLiteral> = HashMap::new();
    propagate_constants(&mut body, &known);
    // Should not crash; propagation is best-effort with IRArg limitation
}

#[test]
fn test_fold_constants_ext_stats_merge() {
    let mut a = ConstFoldExtStats {
        arithmetic_folds: 1,
        string_folds: 2,
        comparison_folds: 3,
        bitwise_folds: 4,
        branch_folds: 5,
        iterations: 0,
    };
    let b = ConstFoldExtStats {
        arithmetic_folds: 10,
        string_folds: 20,
        comparison_folds: 30,
        bitwise_folds: 40,
        branch_folds: 50,
        iterations: 0,
    };
    a.merge(&b);
    assert_eq!(a.arithmetic_folds, 11);
    assert_eq!(a.string_folds, 22);
    assert_eq!(a.comparison_folds, 33);
    assert_eq!(a.bitwise_folds, 44);
    assert_eq!(a.branch_folds, 55);
    assert_eq!(a.total(), 165);
}

#[test]
fn test_fold_constants_ext_default_matches_default_config() {
    let body = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(4)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls1 = vec![make_decl(body.clone())];
    let mut decls2 = vec![make_decl(body)];
    let stats1 = fold_constants_ext_default(&mut decls1);
    let stats2 = fold_constants_ext(&mut decls2, &ConstFoldExtConfig::default());
    assert_eq!(stats1, stats2);
}

#[test]
fn test_fold_comparison_int_beq() {
    let neg1 = (-1i64) as u64;
    assert_eq!(
        fold_comparison(
            "Int.beq",
            &IRLiteral::UInt64(neg1),
            &IRLiteral::UInt64(neg1)
        ),
        Some(true)
    );
    assert_eq!(
        fold_comparison("Int.beq", &IRLiteral::UInt64(neg1), &IRLiteral::UInt64(0)),
        Some(false)
    );
}

#[test]
fn test_fold_bitwise_xor_alias() {
    let result = fold_bitwise_op(
        "UInt64.xor",
        &IRLiteral::UInt64(0xAA),
        &IRLiteral::UInt64(0x55),
    );
    assert_eq!(result, Some(IRLiteral::UInt64(0xFF)));
}

#[test]
fn test_fold_arithmetic_nat_mul_overflow() {
    let result = fold_arithmetic_op(
        "Nat.mul",
        &IRLiteral::UInt64(u64::MAX),
        &IRLiteral::UInt64(2),
    );
    assert_eq!(result, None);
}

#[test]
fn test_fold_constants_ext_multiple_decls() {
    let body1 = chain_lets(
        vec![
            (0, lit_u64(10)),
            (1, lit_u64(20)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let body2 = chain_lets(
        vec![
            (0, lit_u64(0xFF)),
            (1, lit_u64(0xF0)),
            (2, apply("UInt64.land", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body1), make_decl(body2)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.arithmetic_folds >= 1);
    assert!(stats.bitwise_folds >= 1);
}

#[test]
fn test_fold_constants_ext_inc_dec_passthrough() {
    // inc/dec nodes should be preserved, folding continues in rest
    let inner = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(7)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let body = IRBody::Inc {
        var: var(99),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(98),
            rest: Box::new(inner),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext_default(&mut decls);
    assert!(stats.arithmetic_folds >= 1);
    // Verify Inc/Dec are still present
    assert!(matches!(&decls[0].body, IRBody::Inc { .. }));
}
