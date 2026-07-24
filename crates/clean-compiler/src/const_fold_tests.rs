// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR constant folding.
//! Part of #3084 - IO/FFI/Native epic.

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}
fn arg(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}
fn ret(v: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(var(v)))
}
fn lit_u64(n: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(n))
}
fn lit_bool(b: bool) -> IRExpr {
    IRExpr::Lit(IRLiteral::Bool(b))
}
fn str_lit(s: &str) -> IRExpr {
    IRExpr::String(s.to_string())
}

fn apply(name_str: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: fn_id(name_str),
        args,
    }
}

fn let_u64(v: u32, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::UInt64,
        value,
        rest: Box::new(rest),
    }
}

fn let_bool(v: u32, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Bool,
        value,
        rest: Box::new(rest),
    }
}

fn let_obj(v: u32, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Object,
        value,
        rest: Box::new(rest),
    }
}

fn make_decl(n: &str, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(n),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }
}

/// Extract the value expression from a VDecl chain at the given depth.
fn extract_value_at_depth(body: &IRBody, depth: usize) -> Option<&IRExpr> {
    let mut current = body;
    for _ in 0..depth {
        match current {
            IRBody::VDecl { rest, .. } => current = rest,
            _ => return None,
        }
    }
    match current {
        IRBody::VDecl { value, .. } => Some(value),
        _ => None,
    }
}

/// Build a standard binary op test: let v1 := lhs; let v2 := rhs; let v3 := op(v1, v2); ret v3
fn binop_body(op: &str, lhs: IRExpr, rhs: IRExpr, ty: IRType) -> IRBody {
    let let_fn = match &ty {
        IRType::Bool => let_bool,
        _ => let_u64,
    };
    IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lhs,
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: rhs,
            rest: Box::new(let_fn(3, apply(op, vec![arg(1), arg(2)]), ret(3))),
        }),
    }
}

fn fold_and_check(body: &IRBody, config: &ConstFoldConfig) -> (IRBody, ConstFoldStats) {
    let mut stats = ConstFoldStats::default();
    let mut known = KnownValues::new();
    let folded = fold_body(body, &mut known, config, &mut stats);
    (folded, stats)
}

fn cfg() -> ConstFoldConfig {
    ConstFoldConfig::default()
}

// === Nat arithmetic ===

#[test]
fn test_fold_nat_add_simple() {
    let body = binop_body("Nat.add", lit_u64(2), lit_u64(3), IRType::UInt64);
    let (folded, stats) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(5))) => {}
        other => panic!("Expected UInt64(5), got {:?}", other),
    }
    assert_eq!(stats.folded_arithmetic, 1);
}

#[test]
fn test_fold_nat_sub_saturating() {
    let body = binop_body("Nat.sub", lit_u64(3), lit_u64(10), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(0))) => {}
        other => panic!("Expected UInt64(0), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_mul() {
    let body = binop_body("Nat.mul", lit_u64(6), lit_u64(7), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(42))) => {}
        other => panic!("Expected UInt64(42), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_div() {
    let body = binop_body("Nat.div", lit_u64(20), lit_u64(4), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(5))) => {}
        other => panic!("Expected UInt64(5), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_mod() {
    let body = binop_body("Nat.mod", lit_u64(17), lit_u64(5), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(2))) => {}
        other => panic!("Expected UInt64(2), got {:?}", other),
    }
}

// === Overflow / div-by-zero safety ===

#[test]
fn test_fold_nat_add_overflow_does_not_fold() {
    let body = binop_body("Nat.add", lit_u64(u64::MAX), lit_u64(1), IRType::UInt64);
    let (folded, stats) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Nat.add"),
        other => panic!("Expected Apply(Nat.add), got {:?}", other),
    }
    assert_eq!(stats.folded_arithmetic, 0);
}

#[test]
fn test_fold_nat_mul_overflow_does_not_fold() {
    let body = binop_body("Nat.mul", lit_u64(u64::MAX), lit_u64(2), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Nat.mul"),
        other => panic!("Expected Apply(Nat.mul), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_div_by_zero_does_not_fold() {
    let body = binop_body("Nat.div", lit_u64(10), lit_u64(0), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Nat.div"),
        other => panic!("Expected Apply(Nat.div), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_mod_by_zero_does_not_fold() {
    let body = binop_body("Nat.mod", lit_u64(10), lit_u64(0), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Nat.mod"),
        other => panic!("Expected Apply(Nat.mod), got {:?}", other),
    }
}

// === Nat comparisons ===

#[test]
fn test_fold_nat_beq_true() {
    let body = binop_body("Nat.beq", lit_u64(5), lit_u64(5), IRType::Bool);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(true))) => {}
        other => panic!("Expected Bool(true), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_beq_false() {
    let body = binop_body("Nat.beq", lit_u64(5), lit_u64(6), IRType::Bool);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(false))) => {}
        other => panic!("Expected Bool(false), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_ble() {
    let body = binop_body("Nat.ble", lit_u64(3), lit_u64(5), IRType::Bool);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(true))) => {}
        other => panic!("Expected Bool(true), got {:?}", other),
    }
}

#[test]
fn test_fold_nat_blt_equal_is_false() {
    let body = binop_body("Nat.blt", lit_u64(5), lit_u64(5), IRType::Bool);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(false))) => {}
        other => panic!("Expected Bool(false), got {:?}", other),
    }
}

// === Boolean folding ===

#[test]
fn test_fold_bool_and_true_true() {
    let body = let_bool(
        1,
        lit_bool(true),
        let_bool(
            2,
            lit_bool(true),
            let_bool(3, apply("Bool.and", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let (folded, stats) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(true))) => {}
        other => panic!("Expected Bool(true), got {:?}", other),
    }
    assert_eq!(stats.folded_boolean, 1);
}

#[test]
fn test_fold_bool_and_true_false() {
    let body = let_bool(
        1,
        lit_bool(true),
        let_bool(
            2,
            lit_bool(false),
            let_bool(3, apply("Bool.and", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(false))) => {}
        other => panic!("Expected Bool(false), got {:?}", other),
    }
}

#[test]
fn test_fold_bool_or_false_true() {
    let body = let_bool(
        1,
        lit_bool(false),
        let_bool(
            2,
            lit_bool(true),
            let_bool(3, apply("Bool.or", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(true))) => {}
        other => panic!("Expected Bool(true), got {:?}", other),
    }
}

#[test]
fn test_fold_bool_or_false_false() {
    let body = let_bool(
        1,
        lit_bool(false),
        let_bool(
            2,
            lit_bool(false),
            let_bool(3, apply("Bool.or", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::Bool(false))) => {}
        other => panic!("Expected Bool(false), got {:?}", other),
    }
}

#[test]
fn test_fold_bool_not_true() {
    let body = let_bool(
        1,
        lit_bool(true),
        let_bool(2, apply("Bool.not", vec![arg(1)]), ret(2)),
    );
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 1) {
        Some(IRExpr::Lit(IRLiteral::Bool(false))) => {}
        other => panic!("Expected Bool(false), got {:?}", other),
    }
}

#[test]
fn test_fold_bool_not_false() {
    let body = let_bool(
        1,
        lit_bool(false),
        let_bool(2, apply("Bool.not", vec![arg(1)]), ret(2)),
    );
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 1) {
        Some(IRExpr::Lit(IRLiteral::Bool(true))) => {}
        other => panic!("Expected Bool(true), got {:?}", other),
    }
}

// === String folding ===

#[test]
fn test_fold_string_append() {
    let body = let_obj(
        1,
        str_lit("hello"),
        let_obj(
            2,
            str_lit(" world"),
            let_obj(3, apply("String.append", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let (folded, stats) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::String(s)) => assert_eq!(s, "hello world"),
        other => panic!("Expected String(\"hello world\"), got {:?}", other),
    }
    assert_eq!(stats.folded_string, 1);
}

#[test]
fn test_fold_string_append_empty() {
    let body = let_obj(
        1,
        str_lit("abc"),
        let_obj(
            2,
            str_lit(""),
            let_obj(3, apply("String.append", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::String(s)) => assert_eq!(s, "abc"),
        other => panic!("Expected String(\"abc\"), got {:?}", other),
    }
}

#[test]
fn test_fold_string_too_long_does_not_fold() {
    let body = let_obj(
        1,
        str_lit(&"a".repeat(3000)),
        let_obj(
            2,
            str_lit(&"b".repeat(3000)),
            let_obj(3, apply("String.append", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let config = ConstFoldConfig {
        max_string_length: 4096,
        ..cfg()
    };
    let (folded, stats) = fold_and_check(&body, &config);
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "String.append"),
        other => panic!("Expected Apply(String.append), got {:?}", other),
    }
    assert_eq!(stats.folded_string, 0);
}

// === Conditional elimination ===

#[test]
fn test_fold_conditional_known_tag() {
    let mk_ctor = |n: &str, tag: u32| CtorInfo {
        name: name(n),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: mk_ctor("MyType.b", 1),
            args: vec![],
        },
        rest: Box::new(IRBody::Case {
            scrutinee: var(1),
            alts: vec![
                IRAlt {
                    ctor: mk_ctor("MyType.a", 0),
                    body: Box::new(let_u64(10, lit_u64(100), ret(10))),
                },
                IRAlt {
                    ctor: mk_ctor("MyType.b", 1),
                    body: Box::new(let_u64(11, lit_u64(200), ret(11))),
                },
            ],
            default: None,
        }),
    };
    let (folded, stats) = fold_and_check(&body, &cfg());
    assert_eq!(stats.folded_conditionals, 1);
    // Result: VDecl for v1, then body of alt[1]
    match &folded {
        IRBody::VDecl { rest, .. } => match rest.as_ref() {
            IRBody::VDecl { var: v, value, .. } => {
                assert_eq!(v.0, 11);
                match value {
                    IRExpr::Lit(IRLiteral::UInt64(200)) => {}
                    other => panic!("Expected UInt64(200), got {:?}", other),
                }
            }
            other => panic!("Expected VDecl for v11, got {:?}", other),
        },
        other => panic!("Expected VDecl, got {:?}", other),
    }
}

// === No-fold cases ===

#[test]
fn test_no_fold_dynamic_arg() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("get_value"),
            args: vec![],
        },
        rest: Box::new(let_u64(
            2,
            lit_u64(3),
            let_u64(3, apply("Nat.add", vec![arg(1), arg(2)]), ret(3)),
        )),
    };
    let (folded, stats) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Nat.add"),
        other => panic!("Expected Apply(Nat.add), got {:?}", other),
    }
    assert_eq!(stats.total_folded(), 0);
}

#[test]
fn test_no_fold_erased_arg() {
    let body = let_u64(
        1,
        lit_u64(5),
        let_u64(2, apply("Nat.add", vec![arg(1), IRArg::Erased]), ret(2)),
    );
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 1) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Nat.add"),
        other => panic!("Expected Apply(Nat.add), got {:?}", other),
    }
}

// === Config options ===

#[test]
fn test_config_disable_arithmetic() {
    let body = binop_body("Nat.add", lit_u64(2), lit_u64(3), IRType::UInt64);
    let config = ConstFoldConfig {
        fold_arithmetic: false,
        ..cfg()
    };
    let (folded, stats) = fold_and_check(&body, &config);
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Nat.add"),
        other => panic!("Expected Apply(Nat.add), got {:?}", other),
    }
    assert_eq!(stats.folded_arithmetic, 0);
}

#[test]
fn test_config_disable_boolean() {
    let body = let_bool(
        1,
        lit_bool(true),
        let_bool(
            2,
            lit_bool(false),
            let_bool(3, apply("Bool.and", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let config = ConstFoldConfig {
        fold_boolean: false,
        ..cfg()
    };
    let (folded, stats) = fold_and_check(&body, &config);
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "Bool.and"),
        other => panic!("Expected Apply(Bool.and), got {:?}", other),
    }
    assert_eq!(stats.folded_boolean, 0);
}

#[test]
fn test_config_disable_string() {
    let body = let_obj(
        1,
        str_lit("a"),
        let_obj(
            2,
            str_lit("b"),
            let_obj(3, apply("String.append", vec![arg(1), arg(2)]), ret(3)),
        ),
    );
    let config = ConstFoldConfig {
        fold_string: false,
        ..cfg()
    };
    let (folded, _) = fold_and_check(&body, &config);
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "String.append"),
        other => panic!("Expected Apply(String.append), got {:?}", other),
    }
}

// === Full pass (run_const_fold) ===

#[test]
fn test_run_const_fold_multiple_decls() {
    let decl1 = make_decl(
        "f",
        binop_body("Nat.add", lit_u64(10), lit_u64(20), IRType::UInt64),
    );
    let decl2 = make_decl(
        "g",
        binop_body("Nat.mul", lit_u64(7), lit_u64(6), IRType::UInt64),
    );
    let (folded, stats) = run_const_fold(&[decl1, decl2], &cfg());
    assert_eq!(folded.len(), 2);
    assert_eq!(stats.folded_arithmetic, 2);
    match extract_value_at_depth(&folded[0].body, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(30))) => {}
        other => panic!("Expected UInt64(30), got {:?}", other),
    }
    match extract_value_at_depth(&folded[1].body, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(42))) => {}
        other => panic!("Expected UInt64(42), got {:?}", other),
    }
}

#[test]
fn test_run_const_fold_default_works() {
    let decl = make_decl(
        "h",
        binop_body("Nat.sub", lit_u64(100), lit_u64(1), IRType::UInt64),
    );
    let (folded, stats) = run_const_fold_default(&[decl]);
    assert_eq!(stats.folded_arithmetic, 1);
    match extract_value_at_depth(&folded[0].body, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(99))) => {}
        other => panic!("Expected UInt64(99), got {:?}", other),
    }
}

// === Chained / nested folding ===

#[test]
fn test_fold_chained_arithmetic() {
    // v1:=2, v2:=3, v3:=add(v1,v2)=5, v4:=10, v5:=mul(v3,v4)=50
    let body = let_u64(
        1,
        lit_u64(2),
        let_u64(
            2,
            lit_u64(3),
            let_u64(
                3,
                apply("Nat.add", vec![arg(1), arg(2)]),
                let_u64(
                    4,
                    lit_u64(10),
                    let_u64(5, apply("Nat.mul", vec![arg(3), arg(4)]), ret(5)),
                ),
            ),
        ),
    );
    let (folded, stats) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(5))) => {}
        other => panic!("Expected v3=UInt64(5), got {:?}", other),
    }
    match extract_value_at_depth(&folded, 4) {
        Some(IRExpr::Lit(IRLiteral::UInt64(50))) => {}
        other => panic!("Expected v5=UInt64(50), got {:?}", other),
    }
    assert_eq!(stats.folded_arithmetic, 2);
}

// === Edge cases ===

#[test]
fn test_fold_nat_add_zero() {
    let body = binop_body("Nat.add", lit_u64(0), lit_u64(0), IRType::UInt64);
    let (folded, _) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Lit(IRLiteral::UInt64(0))) => {}
        other => panic!("Expected UInt64(0), got {:?}", other),
    }
}

#[test]
fn test_fold_unknown_function_not_folded() {
    let body = binop_body("MyCustom.operation", lit_u64(1), lit_u64(2), IRType::UInt64);
    let (folded, stats) = fold_and_check(&body, &cfg());
    match extract_value_at_depth(&folded, 2) {
        Some(IRExpr::Apply { fn_id, .. }) => assert_eq!(fn_id.0.to_string(), "MyCustom.operation"),
        other => panic!("Expected Apply(MyCustom.operation), got {:?}", other),
    }
    assert_eq!(stats.total_folded(), 0);
}

#[test]
fn test_fold_preserves_rc_operations() {
    let body = IRBody::Inc {
        var: var(1),
        n: 2,
        rest: Box::new(let_u64(
            2,
            lit_u64(5),
            IRBody::Dec {
                var: var(1),
                rest: Box::new(ret(2)),
            },
        )),
    };
    let (folded, _) = fold_and_check(&body, &cfg());
    match &folded {
        IRBody::Inc { var: v, n: 2, rest } => {
            assert_eq!(v.0, 1);
            match rest.as_ref() {
                IRBody::VDecl {
                    var: v2,
                    value,
                    rest: inner,
                    ..
                } => {
                    assert_eq!(v2.0, 2);
                    match value {
                        IRExpr::Lit(IRLiteral::UInt64(5)) => {}
                        _ => panic!("Expected UInt64(5)"),
                    }
                    match inner.as_ref() {
                        IRBody::Dec { var: dv, .. } => assert_eq!(dv.0, 1),
                        other => panic!("Expected Dec, got {:?}", other),
                    }
                }
                other => panic!("Expected VDecl, got {:?}", other),
            }
        }
        other => panic!("Expected Inc, got {:?}", other),
    }
}

#[test]
fn test_fold_stats_accumulate() {
    let decl = make_decl(
        "mixed",
        let_u64(
            1,
            lit_u64(2),
            let_u64(
                2,
                lit_u64(3),
                let_u64(
                    3,
                    apply("Nat.add", vec![arg(1), arg(2)]),
                    let_bool(
                        4,
                        lit_bool(true),
                        let_bool(
                            5,
                            lit_bool(false),
                            let_bool(6, apply("Bool.and", vec![arg(4), arg(5)]), ret(6)),
                        ),
                    ),
                ),
            ),
        ),
    );
    let (_, stats) = run_const_fold(&[decl], &cfg());
    assert_eq!(stats.folded_arithmetic, 1);
    assert_eq!(stats.folded_boolean, 1);
    assert_eq!(stats.total_folded(), 2);
}

#[test]
fn test_fold_empty_decls() {
    let (folded, stats) = run_const_fold(&[], &cfg());
    assert!(folded.is_empty());
    assert_eq!(stats.total_folded(), 0);
}
