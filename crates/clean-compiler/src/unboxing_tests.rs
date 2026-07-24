// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the unboxing optimization pass.
//!
//! Part of Epic #3084 — IO/FFI/Native.

use crate::ir::*;
use crate::unboxing::rules::{classify_arithmetic, classify_comparison, literal_type};
use crate::unboxing::*;
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// Helper constructors
// ---------------------------------------------------------------------------

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_fn_id(s: &str) -> FnId {
    FnId(mk_name(s))
}

fn var(n: u32) -> VarId {
    VarId(n)
}

fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}

/// Build `let v : ty = value; rest`.
fn mk_vdecl(v: u32, ty: IRType, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty,
        value,
        rest: Box::new(rest),
    }
}

fn mk_box(ty: IRType, v: u32) -> IRExpr {
    IRExpr::Box {
        ty,
        arg: arg_var(v),
    }
}

fn mk_unbox(ty: IRType, v: u32) -> IRExpr {
    IRExpr::Unbox {
        ty,
        arg: arg_var(v),
    }
}

fn mk_ret(v: u32) -> IRBody {
    IRBody::Ret(arg_var(v))
}

fn mk_apply(name: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: mk_fn_id(name),
        args,
    }
}

fn mk_simple_decl(name: &str, params: Vec<(u32, IRType)>, ret: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: mk_name(name),
        params: params.into_iter().map(|(v, t)| (var(v), t)).collect(),
        return_type: ret,
        body,
    }
}

// ---------------------------------------------------------------------------
// UnboxingConfig tests
// ---------------------------------------------------------------------------

#[test]
fn test_config_default_enables_all() {
    let cfg = UnboxingConfig::new();
    assert!(cfg.eliminate_box_unbox_pairs);
    assert!(cfg.unbox_arithmetic);
    assert!(cfg.unbox_comparisons);
    assert!(cfg.enable_type_flow);
    assert!(cfg.specialize_returns);
}

#[test]
fn test_config_disabled_disables_all() {
    let cfg = UnboxingConfig::disabled();
    assert!(!cfg.eliminate_box_unbox_pairs);
    assert!(!cfg.unbox_arithmetic);
    assert!(!cfg.unbox_comparisons);
    assert!(!cfg.enable_type_flow);
    assert!(!cfg.specialize_returns);
}

// ---------------------------------------------------------------------------
// Box/unbox pair elimination
// ---------------------------------------------------------------------------

#[test]
fn test_eliminate_unbox_of_box_u64() {
    // let x0 : UInt64 = <param>
    // let x1 : Object = box UInt64 x0
    // let x2 : UInt64 = unbox UInt64 x1
    // ret x2
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(2, IRType::UInt64, mk_unbox(IRType::UInt64, 1), mk_ret(2)),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::UInt64, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (result, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.pairs_eliminated, 1, "should eliminate one pair");
    assert_eq!(result.len(), 1);
}

#[test]
fn test_eliminate_box_of_unbox() {
    // let x1 : UInt64 = unbox UInt64 x0
    // let x2 : Object = box UInt64 x1
    // ret x2
    let body = mk_vdecl(
        1,
        IRType::UInt64,
        mk_unbox(IRType::UInt64, 0),
        mk_vdecl(2, IRType::Object, mk_box(IRType::UInt64, 1), mk_ret(2)),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::Object)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (result, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(
        stats.pairs_eliminated, 1,
        "should eliminate one box(unbox) pair"
    );
    assert_eq!(result.len(), 1);
}

#[test]
fn test_no_elimination_different_types() {
    // box(UInt32, x) then unbox(UInt64, y) — types don't match, no elimination.
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt32, 0),
        mk_vdecl(2, IRType::UInt64, mk_unbox(IRType::UInt64, 1), mk_ret(2)),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt32)], IRType::UInt64, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(
        stats.pairs_eliminated, 0,
        "different types should not be eliminated"
    );
}

#[test]
fn test_eliminate_multiple_pairs() {
    // Two independent box/unbox pairs.
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::UInt64,
            mk_unbox(IRType::UInt64, 1),
            mk_vdecl(
                3,
                IRType::Object,
                mk_box(IRType::UInt32, 0),
                mk_vdecl(4, IRType::UInt32, mk_unbox(IRType::UInt32, 3), mk_ret(4)),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::UInt32, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.pairs_eliminated, 2, "should eliminate two pairs");
}

// ---------------------------------------------------------------------------
// Unboxed arithmetic
// ---------------------------------------------------------------------------

#[test]
fn test_unbox_nat_add() {
    // let x1 = box(UInt64, x0)
    // let x2 = box(UInt64, x0)
    // let x3 = Nat.add(x1, x2)
    // ret x3
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt64, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("Nat.add", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.arithmetic_unboxed, 1, "should unbox Nat.add");
}

#[test]
fn test_unbox_nat_mul() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt64, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("Nat.mul", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.arithmetic_unboxed, 1, "should unbox Nat.mul");
}

#[test]
fn test_unbox_uint32_add() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt32, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt32, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("UInt32.add", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt32)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.arithmetic_unboxed, 1, "should unbox UInt32.add");
}

#[test]
fn test_no_unbox_unknown_function() {
    // Calling a function that is NOT known arithmetic should not be unboxed.
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt64, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("MyModule.custom_add", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.arithmetic_unboxed, 0);
}

#[test]
fn test_no_unbox_non_boxed_args() {
    // Nat.add with args that are NOT box expressions — can't unbox.
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_apply("Nat.add", vec![arg_var(0), arg_var(0)]),
        mk_ret(1),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::Object)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(
        stats.arithmetic_unboxed, 0,
        "non-boxed args can't be unboxed"
    );
}

// ---------------------------------------------------------------------------
// Unboxed comparisons
// ---------------------------------------------------------------------------

#[test]
fn test_unbox_nat_dec_lt() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt64, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("Nat.decLt", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.comparisons_unboxed, 1, "should unbox Nat.decLt");
}

#[test]
fn test_unbox_nat_beq() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt64, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("Nat.beq", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.comparisons_unboxed, 1, "should unbox Nat.beq");
}

#[test]
fn test_unbox_uint64_dec_eq() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt64, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("UInt64.decEq", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.comparisons_unboxed, 1, "should unbox UInt64.decEq");
}

// ---------------------------------------------------------------------------
// Type flow analysis
// ---------------------------------------------------------------------------

#[test]
fn test_type_flow_literal_type_correction() {
    // A literal assigned as Object should have its type corrected.
    let body = mk_vdecl(
        1,
        IRType::Object, // declared as Object, but it's actually a UInt64 literal
        IRExpr::Lit(IRLiteral::UInt64(42)),
        mk_ret(1),
    );
    let decl = mk_simple_decl("test_fn", vec![], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (result, _) = unbox_decls(&[decl], &cfg);
    // The VDecl type should be corrected to UInt64.
    match &result[0].body {
        IRBody::VDecl { ty, .. } => {
            assert_eq!(*ty, IRType::UInt64, "literal type should be corrected");
        }
        _ => panic!("expected VDecl"),
    }
}

#[test]
fn test_type_flow_bool_literal() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        IRExpr::Lit(IRLiteral::Bool(true)),
        mk_ret(1),
    );
    let decl = mk_simple_decl("test_fn", vec![], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (result, _) = unbox_decls(&[decl], &cfg);
    match &result[0].body {
        IRBody::VDecl { ty, .. } => {
            assert_eq!(*ty, IRType::Bool, "Bool literal type should be corrected");
        }
        _ => panic!("expected VDecl"),
    }
}

// ---------------------------------------------------------------------------
// Disabled config tests
// ---------------------------------------------------------------------------

#[test]
fn test_disabled_config_no_pair_elimination() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(2, IRType::UInt64, mk_unbox(IRType::UInt64, 1), mk_ret(2)),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::UInt64, body);
    let cfg = UnboxingConfig::disabled();
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(
        stats.pairs_eliminated, 0,
        "disabled config should not optimize"
    );
}

#[test]
fn test_disabled_arithmetic_keeps_boxed() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_box(IRType::UInt64, 0),
            mk_vdecl(
                3,
                IRType::Object,
                mk_apply("Nat.add", vec![arg_var(1), arg_var(2)]),
                mk_ret(3),
            ),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        unbox_arithmetic: false,
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(
        stats.arithmetic_unboxed, 0,
        "disabled arithmetic should not unbox"
    );
}

// ---------------------------------------------------------------------------
// is_unboxing_candidate
// ---------------------------------------------------------------------------

#[test]
fn test_is_candidate_with_box() {
    let body = mk_vdecl(1, IRType::Object, mk_box(IRType::UInt64, 0), mk_ret(1));
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    assert!(is_unboxing_candidate(&decl));
}

#[test]
fn test_is_candidate_with_unbox() {
    let body = mk_vdecl(1, IRType::UInt64, mk_unbox(IRType::UInt64, 0), mk_ret(1));
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::Object)], IRType::UInt64, body);
    assert!(is_unboxing_candidate(&decl));
}

#[test]
fn test_not_candidate_no_box_unbox() {
    let body = mk_vdecl(
        1,
        IRType::UInt64,
        IRExpr::Lit(IRLiteral::UInt64(42)),
        mk_ret(1),
    );
    let decl = mk_simple_decl("test_fn", vec![], IRType::UInt64, body);
    assert!(!is_unboxing_candidate(&decl));
}

// ---------------------------------------------------------------------------
// count_box_unbox_ops
// ---------------------------------------------------------------------------

#[test]
fn test_count_box_unbox_ops_basic() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::UInt64,
            mk_unbox(IRType::UInt64, 1),
            mk_vdecl(3, IRType::Object, mk_box(IRType::UInt32, 0), mk_ret(3)),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let (boxes, unboxes) = count_box_unbox_ops(&decl);
    assert_eq!(boxes, 2);
    assert_eq!(unboxes, 1);
}

#[test]
fn test_count_box_unbox_ops_zero() {
    let body = mk_vdecl(
        1,
        IRType::UInt64,
        IRExpr::Lit(IRLiteral::UInt64(0)),
        mk_ret(1),
    );
    let decl = mk_simple_decl("test_fn", vec![], IRType::UInt64, body);
    let (boxes, unboxes) = count_box_unbox_ops(&decl);
    assert_eq!(boxes, 0);
    assert_eq!(unboxes, 0);
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

#[test]
fn test_stats_default_zero() {
    let stats = UnboxingStats::default();
    assert_eq!(stats.pairs_eliminated, 0);
    assert_eq!(stats.arithmetic_unboxed, 0);
    assert_eq!(stats.comparisons_unboxed, 0);
    assert_eq!(stats.returns_specialized, 0);
    assert_eq!(stats.decls_processed, 0);
}

#[test]
fn test_stats_accumulate_across_decls() {
    // Two decls, each with one box/unbox pair.
    let body1 = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(2, IRType::UInt64, mk_unbox(IRType::UInt64, 1), mk_ret(2)),
    );
    let body2 = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt32, 0),
        mk_vdecl(2, IRType::UInt32, mk_unbox(IRType::UInt32, 1), mk_ret(2)),
    );
    let decl1 = mk_simple_decl("fn1", vec![(0, IRType::UInt64)], IRType::UInt64, body1);
    let decl2 = mk_simple_decl("fn2", vec![(0, IRType::UInt32)], IRType::UInt32, body2);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl1, decl2], &cfg);
    assert_eq!(
        stats.pairs_eliminated, 2,
        "stats should accumulate across decls"
    );
    assert_eq!(stats.decls_processed, 2);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_empty_decls() {
    let cfg = UnboxingConfig::new();
    let (result, stats) = unbox_decls(&[], &cfg);
    assert!(result.is_empty());
    assert_eq!(stats.decls_processed, 0);
}

#[test]
fn test_unreachable_body() {
    let decl = mk_simple_decl("test_fn", vec![], IRType::Void, IRBody::Unreachable);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (result, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(result.len(), 1);
    assert_eq!(stats.decls_processed, 1);
    assert_eq!(stats.pairs_eliminated, 0);
}

#[test]
fn test_case_body_optimization() {
    // Box/unbox pair inside a case alternative.
    let inner_body = mk_vdecl(
        10,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(11, IRType::UInt64, mk_unbox(IRType::UInt64, 10), mk_ret(11)),
    );
    let ctor = CtorInfo {
        name: mk_name("Nat.zero"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor,
            body: Box::new(inner_body),
        }],
        default: None,
    };
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::Object)], IRType::UInt64, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(stats.pairs_eliminated, 1, "should optimize inside case alt");
}

#[test]
fn test_jdecl_body_optimization() {
    // Box/unbox pair inside a join point.
    let jp_body = mk_vdecl(
        10,
        IRType::Object,
        mk_box(IRType::UInt64, 1),
        mk_vdecl(11, IRType::UInt64, mk_unbox(IRType::UInt64, 10), mk_ret(11)),
    );
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(var(1), IRType::UInt64)],
        body: Box::new(jp_body),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![arg_var(0)],
        }),
    };
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::UInt64, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    let (_, stats) = unbox_decls(&[decl], &cfg);
    assert_eq!(
        stats.pairs_eliminated, 1,
        "should optimize inside join point"
    );
}

#[test]
fn test_unbox_default_convenience() {
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(2, IRType::UInt64, mk_unbox(IRType::UInt64, 1), mk_ret(2)),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::UInt64, body);
    let (result, stats) = unbox_decls_default(&[decl]);
    assert_eq!(result.len(), 1);
    assert!(stats.pairs_eliminated >= 1);
}

#[test]
fn test_classify_all_arithmetic_ops() {
    // Verify all known arithmetic operations are classified.
    for name in &[
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.div",
        "Nat.mod",
        "UInt64.add",
        "UInt64.sub",
        "UInt64.mul",
        "UInt32.add",
        "UInt32.sub",
        "UInt32.mul",
    ] {
        assert!(
            classify_arithmetic(name).is_some(),
            "{} should be classified as arithmetic",
            name
        );
    }
    assert!(classify_arithmetic("unknown_fn").is_none());
}

#[test]
fn test_classify_all_comparison_ops() {
    for name in &[
        "Nat.decLt",
        "Nat.decLe",
        "Nat.decEq",
        "Nat.beq",
        "UInt64.decLt",
        "UInt64.decLe",
        "UInt64.decEq",
        "UInt32.decLt",
        "UInt32.decLe",
        "UInt32.decEq",
    ] {
        assert!(
            classify_comparison(name),
            "{} should be classified as comparison",
            name
        );
    }
    assert!(!classify_comparison("unknown_fn"));
}

#[test]
fn test_literal_type_all_variants() {
    assert_eq!(literal_type(&IRLiteral::Bool(true)), IRType::Bool);
    assert_eq!(literal_type(&IRLiteral::UInt8(0)), IRType::UInt8);
    assert_eq!(literal_type(&IRLiteral::UInt16(0)), IRType::UInt16);
    assert_eq!(literal_type(&IRLiteral::UInt32(0)), IRType::UInt32);
    assert_eq!(literal_type(&IRLiteral::UInt64(0)), IRType::UInt64);
    assert_eq!(literal_type(&IRLiteral::USize(0)), IRType::USize);
    assert_eq!(literal_type(&IRLiteral::Float32(0.0)), IRType::Float32);
    assert_eq!(literal_type(&IRLiteral::Float64(0.0)), IRType::Float64);
}

#[test]
fn test_erased_arg_passthrough() {
    // Erased args should pass through try_unbox_args without blocking.
    let body = mk_vdecl(
        1,
        IRType::Object,
        mk_box(IRType::UInt64, 0),
        mk_vdecl(
            2,
            IRType::Object,
            mk_apply("Nat.add", vec![arg_var(1), IRArg::Erased]),
            mk_ret(2),
        ),
    );
    let decl = mk_simple_decl("test_fn", vec![(0, IRType::UInt64)], IRType::Object, body);
    let cfg = UnboxingConfig {
        specialize_returns: false,
        ..UnboxingConfig::new()
    };
    // Erased is fine, but the non-erased arg is boxed and the erased one
    // isn't, so it should still fail to fully unbox since we need ALL non-erased
    // args to be boxed.
    let (_, stats) = unbox_decls(&[decl], &cfg);
    // One arg is box, other is Erased — Erased passes through, only box arg
    // gets unwrapped. This should succeed.
    assert_eq!(stats.arithmetic_unboxed, 1);
}

// ---------------------------------------------------------------------------
// Passthrough variant coverage
//
// The unboxing pass dispatches VDecl/JDecl/Case in `optimize_body` and routes
// every other `IRBody` variant through `optimize_body_passthrough`, which must
// preserve each variant unchanged and recurse only into its `rest`. These tests
// exercise the in-place mutation / ref-count variants end to end and pin that
// they pass through without panicking. Without exhaustive arms, a future
// `IRBody` variant would silently hit the `unreachable!()` and crash here.
// ---------------------------------------------------------------------------

#[test]
fn test_unbox_passthrough_inc_dec_preserves_body() {
    // inc x0 2; dec x0; ret x0
    let body = IRBody::Inc {
        var: var(0),
        n: 2,
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(mk_ret(0)),
        }),
    };
    let decl = mk_simple_decl("f", vec![(0, IRType::Object)], IRType::Object, body.clone());
    let (result, _) = unbox_decls(&[decl], &UnboxingConfig::disabled());
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].body, body, "inc/dec must pass through unchanged");
}

#[test]
fn test_unbox_passthrough_set_settag_preserves_body() {
    // x0[0] := x1; setTag x0 3; ret x0
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::SetTag {
            var: var(0),
            tag: 3,
            rest: Box::new(mk_ret(0)),
        }),
    };
    let decl = mk_simple_decl(
        "f",
        vec![(0, IRType::Object), (1, IRType::Object)],
        IRType::Object,
        body.clone(),
    );
    let (result, _) = unbox_decls(&[decl], &UnboxingConfig::disabled());
    assert_eq!(
        result[0].body, body,
        "set/setTag must pass through unchanged"
    );
}

#[test]
fn test_unbox_passthrough_uset_sset_preserves_body() {
    // uset x0 0 := x1; sset x0 1 8 := x2 : UInt64; ret x0
    let body = IRBody::USet {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::SSet {
            var: var(0),
            n: 1,
            offset: 8,
            value: var(2),
            ty: IRType::UInt64,
            rest: Box::new(mk_ret(0)),
        }),
    };
    let decl = mk_simple_decl(
        "f",
        vec![(0, IRType::Object), (1, IRType::USize), (2, IRType::UInt64)],
        IRType::Object,
        body.clone(),
    );
    let (result, _) = unbox_decls(&[decl], &UnboxingConfig::disabled());
    assert_eq!(
        result[0].body, body,
        "uset/sset must pass through unchanged"
    );
}

#[test]
fn test_unbox_passthrough_unreachable_preserves_body() {
    // dec x0; unreachable
    let body = IRBody::Dec {
        var: var(0),
        rest: Box::new(IRBody::Unreachable),
    };
    let decl = mk_simple_decl("f", vec![(0, IRType::Object)], IRType::Object, body.clone());
    let (result, _) = unbox_decls(&[decl], &UnboxingConfig::disabled());
    assert_eq!(
        result[0].body, body,
        "unreachable must pass through unchanged"
    );
}

#[test]
fn test_unbox_passthrough_jmp_ret_terminals_preserve() {
    // jp0(x1): ret x1; jmp jp0(x0)
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(var(1), IRType::Object)],
        body: Box::new(mk_ret(1)),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![arg_var(0)],
        }),
    };
    let decl = mk_simple_decl("f", vec![(0, IRType::Object)], IRType::Object, body.clone());
    let (result, _) = unbox_decls(&[decl], &UnboxingConfig::disabled());
    assert_eq!(result[0].body, body, "jmp/ret terminals must pass through");
}
