// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended unboxing optimization pass.
//!
//! Part of #3083 — Extensibility (Lean 4 replacement compiler infrastructure).

use crate::ir::*;
use crate::unboxing_ext::*;
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}

fn var(n: u32) -> VarId {
    VarId(n)
}

fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}

fn mk_fn_id(s: &str) -> FnId {
    FnId(mk_name(s))
}

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

fn simple_decl(name: &str, params: Vec<(VarId, IRType)>, ret: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: mk_name(name),
        params,
        return_type: ret,
        body,
    }
}

// ---------------------------------------------------------------------------
// Scalar unboxing classification
// ---------------------------------------------------------------------------

#[test]
fn test_classify_scalar_uint8() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::UInt8),
        Some(IRType::UInt8)
    );
}

#[test]
fn test_classify_scalar_uint16() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::UInt16),
        Some(IRType::UInt16)
    );
}

#[test]
fn test_classify_scalar_uint32() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::UInt32),
        Some(IRType::UInt32)
    );
}

#[test]
fn test_classify_scalar_uint64() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::UInt64),
        Some(IRType::UInt64)
    );
}

#[test]
fn test_classify_scalar_float32() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::Float32),
        Some(IRType::Float32)
    );
}

#[test]
fn test_classify_scalar_float64() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::Float64),
        Some(IRType::Float64)
    );
}

#[test]
fn test_classify_scalar_bool() {
    assert_eq!(classify_scalar_unboxing(&IRType::Bool), Some(IRType::Bool));
}

#[test]
fn test_classify_scalar_usize() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::USize),
        Some(IRType::USize)
    );
}

#[test]
fn test_classify_scalar_object_returns_none() {
    assert_eq!(classify_scalar_unboxing(&IRType::Object), None);
}

#[test]
fn test_classify_scalar_struct_returns_none() {
    assert_eq!(
        classify_scalar_unboxing(&IRType::Struct(vec![IRType::UInt64])),
        None
    );
}

#[test]
fn test_is_already_unboxed_scalars() {
    assert!(is_already_unboxed(&IRType::UInt64));
    assert!(is_already_unboxed(&IRType::Bool));
    assert!(is_already_unboxed(&IRType::Float64));
}

#[test]
fn test_is_already_unboxed_objects() {
    assert!(!is_already_unboxed(&IRType::Object));
    assert!(!is_already_unboxed(&IRType::TObject));
}

// ---------------------------------------------------------------------------
// Structure unboxing
// ---------------------------------------------------------------------------

#[test]
fn test_classify_struct_single_field() {
    let ty = IRType::Struct(vec![IRType::UInt64]);
    assert_eq!(classify_struct_unboxing(&ty), Some(IRType::UInt64));
}

#[test]
fn test_classify_struct_multi_field_returns_none() {
    let ty = IRType::Struct(vec![IRType::UInt64, IRType::Bool]);
    assert_eq!(classify_struct_unboxing(&ty), None);
}

#[test]
fn test_classify_struct_empty_returns_none() {
    let ty = IRType::Struct(vec![]);
    assert_eq!(classify_struct_unboxing(&ty), None);
}

#[test]
fn test_classify_struct_non_struct_returns_none() {
    assert_eq!(classify_struct_unboxing(&IRType::Object), None);
    assert_eq!(classify_struct_unboxing(&IRType::UInt64), None);
}

#[test]
fn test_classify_struct_nested_single_field() {
    let inner = IRType::Struct(vec![IRType::Bool]);
    let outer = IRType::Struct(vec![inner.clone()]);
    assert_eq!(classify_struct_unboxing(&outer), Some(inner));
}

// ---------------------------------------------------------------------------
// Partial unboxing
// ---------------------------------------------------------------------------

#[test]
fn test_partial_unboxing_with_scalars() {
    let ty = IRType::Struct(vec![IRType::UInt64, IRType::Bool, IRType::Object]);
    let candidates = classify_partial_unboxing(&ty);
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0], (0, IRType::UInt64));
    assert_eq!(candidates[1], (1, IRType::Bool));
}

#[test]
fn test_partial_unboxing_no_scalars() {
    let ty = IRType::Struct(vec![IRType::Object, IRType::TObject]);
    let candidates = classify_partial_unboxing(&ty);
    assert!(candidates.is_empty());
}

#[test]
fn test_partial_unboxing_non_struct() {
    let candidates = classify_partial_unboxing(&IRType::Object);
    assert!(candidates.is_empty());
}

// ---------------------------------------------------------------------------
// Array unboxing
// ---------------------------------------------------------------------------

#[test]
fn test_classify_array_nat() {
    assert_eq!(classify_array_unboxing("Array.Nat"), Some(IRType::UInt64));
}

#[test]
fn test_classify_array_uint8() {
    assert_eq!(classify_array_unboxing("Array.UInt8"), Some(IRType::UInt8));
}

#[test]
fn test_classify_array_uint32() {
    assert_eq!(
        classify_array_unboxing("Array.UInt32"),
        Some(IRType::UInt32)
    );
}

#[test]
fn test_classify_array_uint64() {
    assert_eq!(
        classify_array_unboxing("Array.UInt64"),
        Some(IRType::UInt64)
    );
}

#[test]
fn test_classify_array_unknown_returns_none() {
    assert_eq!(classify_array_unboxing("Array.String"), None);
    assert_eq!(classify_array_unboxing("List.Nat"), None);
}

// ---------------------------------------------------------------------------
// Profitability analysis
// ---------------------------------------------------------------------------

#[test]
fn test_profitability_all_savings() {
    let cost = UnboxingCost {
        box_ops_saved: 3,
        unbox_ops_saved: 2,
        box_ops_added: 0,
        unbox_ops_added: 0,
    };
    assert!((cost.profitability() - 1.0).abs() < f64::EPSILON);
    assert!(cost.is_net_positive());
}

#[test]
fn test_profitability_all_overhead() {
    let cost = UnboxingCost {
        box_ops_saved: 0,
        unbox_ops_saved: 0,
        box_ops_added: 3,
        unbox_ops_added: 2,
    };
    assert!((cost.profitability() - 0.0).abs() < f64::EPSILON);
    assert!(!cost.is_net_positive());
}

#[test]
fn test_profitability_balanced() {
    let cost = UnboxingCost {
        box_ops_saved: 2,
        unbox_ops_saved: 0,
        box_ops_added: 2,
        unbox_ops_added: 0,
    };
    assert!((cost.profitability() - 0.5).abs() < f64::EPSILON);
    assert!(!cost.is_net_positive());
}

#[test]
fn test_profitability_zero_ops() {
    let cost = UnboxingCost {
        box_ops_saved: 0,
        unbox_ops_saved: 0,
        box_ops_added: 0,
        unbox_ops_added: 0,
    };
    assert!((cost.profitability() - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_analyze_param_unboxing_cost_with_unbox() {
    // let x1 : UInt64 = unbox(x0); ret x1
    let body = mk_vdecl(1, IRType::UInt64, mk_unbox(IRType::UInt64, 0), mk_ret(1));
    let cost = analyze_param_unboxing_cost(&body, var(0));
    assert_eq!(cost.unbox_ops_saved, 1);
    assert_eq!(cost.box_ops_saved, 0);
    assert_eq!(cost.box_ops_added, 0);
}

#[test]
fn test_analyze_param_unboxing_cost_with_call() {
    // let x1 : Object = f(x0); ret x1
    let body = mk_vdecl(
        1,
        IRType::Object,
        IRExpr::Apply {
            fn_id: mk_fn_id("f"),
            args: vec![arg_var(0)],
        },
        mk_ret(1),
    );
    let cost = analyze_param_unboxing_cost(&body, var(0));
    assert_eq!(cost.box_ops_added, 1);
}

// ---------------------------------------------------------------------------
// Propagation analysis
// ---------------------------------------------------------------------------

#[test]
fn test_analyze_propagation_candidates_finds_unboxed_param() {
    // fn f(x0 : Object) : Object = let x1 : UInt64 = unbox(x0); ...
    let decl = simple_decl(
        "f",
        vec![(var(0), IRType::Object)],
        IRType::Object,
        mk_vdecl(1, IRType::UInt64, mk_unbox(IRType::UInt64, 0), mk_ret(1)),
    );
    let candidates = analyze_propagation_candidates(&[decl]);
    assert_eq!(candidates.len(), 1);
    let f_candidates = &candidates["f"];
    assert_eq!(f_candidates.len(), 1);
    assert_eq!(f_candidates[0], (0, IRType::UInt64));
}

#[test]
fn test_analyze_propagation_candidates_scalar_param_skipped() {
    // fn f(x0 : UInt64) : UInt64 = ret x0
    let decl = simple_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        mk_ret(0),
    );
    let candidates = analyze_propagation_candidates(&[decl]);
    assert!(candidates.is_empty());
}

// ---------------------------------------------------------------------------
// Recursive type detection
// ---------------------------------------------------------------------------

#[test]
fn test_is_recursive_self_call() {
    let decl = simple_decl(
        "fact",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        mk_vdecl(
            1,
            IRType::UInt64,
            IRExpr::Apply {
                fn_id: mk_fn_id("fact"),
                args: vec![arg_var(0)],
            },
            mk_ret(1),
        ),
    );
    assert!(is_recursive(&decl));
}

#[test]
fn test_is_recursive_no_self_call() {
    let decl = simple_decl(
        "add",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        mk_vdecl(
            1,
            IRType::UInt64,
            IRExpr::Apply {
                fn_id: mk_fn_id("other"),
                args: vec![arg_var(0)],
            },
            mk_ret(1),
        ),
    );
    assert!(!is_recursive(&decl));
}

#[test]
fn test_is_mutually_recursive() {
    let decl_a = simple_decl(
        "even",
        vec![(var(0), IRType::UInt64)],
        IRType::Bool,
        mk_vdecl(
            1,
            IRType::Bool,
            IRExpr::Apply {
                fn_id: mk_fn_id("odd"),
                args: vec![arg_var(0)],
            },
            mk_ret(1),
        ),
    );
    let decl_b = simple_decl(
        "odd",
        vec![(var(0), IRType::UInt64)],
        IRType::Bool,
        mk_vdecl(
            1,
            IRType::Bool,
            IRExpr::Apply {
                fn_id: mk_fn_id("even"),
                args: vec![arg_var(0)],
            },
            mk_ret(1),
        ),
    );
    assert!(is_mutually_recursive(&[decl_a, decl_b]));
}

#[test]
fn test_is_not_mutually_recursive() {
    let decl_a = simple_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        mk_ret(0),
    );
    let decl_b = simple_decl(
        "g",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        mk_ret(0),
    );
    assert!(!is_mutually_recursive(&[decl_a, decl_b]));
}

// ---------------------------------------------------------------------------
// Top-level pass
// ---------------------------------------------------------------------------

#[test]
fn test_unbox_ext_decls_default_passthrough() {
    // Simple decl with no boxing => should pass through unchanged.
    let decl = simple_decl(
        "id",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        mk_ret(0),
    );
    let (result, stats) = unbox_ext_decls_default(&[decl]);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].return_type, IRType::UInt64);
    assert_eq!(stats.decls_processed, 1);
}

#[test]
fn test_unbox_ext_struct_return_unboxing() {
    // fn f() : Struct([UInt64]) = ...
    let decl = simple_decl(
        "wrap",
        vec![],
        IRType::Struct(vec![IRType::UInt64]),
        IRBody::Ret(IRArg::Erased),
    );
    let (result, stats) = unbox_ext_decls(&[decl], &UnboxingExtConfig::new());
    assert_eq!(result[0].return_type, IRType::UInt64);
    assert_eq!(stats.structs_unboxed, 1);
}

#[test]
fn test_unbox_ext_disabled_config_passthrough() {
    let decl = simple_decl(
        "wrap",
        vec![],
        IRType::Struct(vec![IRType::UInt64]),
        IRBody::Ret(IRArg::Erased),
    );
    let config = UnboxingExtConfig::disabled();
    let (result, stats) = unbox_ext_decls(&[decl], &config);
    // Disabled config should not optimize
    assert_eq!(result[0].return_type, IRType::Struct(vec![IRType::UInt64]));
    assert_eq!(stats.structs_unboxed, 0);
}

#[test]
fn test_unbox_ext_stats_total_optimizations() {
    let stats = UnboxingExtStats {
        scalars_unboxed: 2,
        structs_unboxed: 1,
        arrays_unboxed: 3,
        propagations: 4,
        partial_unboxes: 1,
        ..UnboxingExtStats::default()
    };
    assert_eq!(stats.total_optimizations(), 11);
}

// ---------------------------------------------------------------------------
// Statistics formatting
// ---------------------------------------------------------------------------

#[test]
fn test_format_stats_report_contains_all_fields() {
    let stats = UnboxingExtStats {
        scalars_unboxed: 5,
        structs_unboxed: 2,
        arrays_unboxed: 1,
        rejected_unprofitable: 3,
        propagations: 4,
        partial_unboxes: 0,
        decls_processed: 10,
    };
    let report = format_stats_report(&stats);
    assert!(report.contains("Scalars unboxed: 5"));
    assert!(report.contains("Structures unboxed: 2"));
    assert!(report.contains("Arrays unboxed: 1"));
    assert!(report.contains("Rejected (unprofitable): 3"));
    assert!(report.contains("Propagations: 4"));
    assert!(report.contains("Total optimizations: 12"));
    assert!(report.contains("Declarations processed: 10"));
}

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------

#[test]
fn test_config_default_all_enabled() {
    let cfg = UnboxingExtConfig::default();
    assert!(cfg.enable_scalar_unboxing);
    assert!(cfg.enable_struct_unboxing);
    assert!(cfg.enable_array_unboxing);
    assert!(cfg.enable_profitability_check);
    assert!(cfg.enable_propagation);
    assert!(cfg.enable_partial_unboxing);
    assert!((cfg.profitability_threshold - 0.5).abs() < f64::EPSILON);
}

#[test]
fn test_config_disabled_all_off() {
    let cfg = UnboxingExtConfig::disabled();
    assert!(!cfg.enable_scalar_unboxing);
    assert!(!cfg.enable_struct_unboxing);
    assert!(!cfg.enable_array_unboxing);
    assert!(!cfg.enable_profitability_check);
    assert!(!cfg.enable_propagation);
    assert!(!cfg.enable_partial_unboxing);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_empty_decls() {
    let (result, stats) = unbox_ext_decls_default(&[]);
    assert!(result.is_empty());
    assert_eq!(stats.decls_processed, 0);
    assert_eq!(stats.total_optimizations(), 0);
}

#[test]
fn test_already_unboxed_param_not_changed() {
    // fn f(x0 : UInt64) : UInt64 = ret x0
    let decl = simple_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        IRType::UInt64,
        mk_ret(0),
    );
    let (result, _) = unbox_ext_decls_default(&[decl]);
    assert_eq!(result[0].params[0].1, IRType::UInt64);
}

#[test]
fn test_multi_field_struct_not_unwrapped() {
    let decl = simple_decl(
        "pair",
        vec![],
        IRType::Struct(vec![IRType::UInt64, IRType::Bool]),
        IRBody::Ret(IRArg::Erased),
    );
    let (result, stats) = unbox_ext_decls_default(&[decl]);
    assert_eq!(
        result[0].return_type,
        IRType::Struct(vec![IRType::UInt64, IRType::Bool])
    );
    assert_eq!(stats.structs_unboxed, 0);
}

#[test]
fn test_struct_with_object_inner_not_unwrapped() {
    // Struct([Object]) — single field but inner is Object, not scalar
    let decl = simple_decl(
        "box_wrap",
        vec![],
        IRType::Struct(vec![IRType::Object]),
        IRBody::Ret(IRArg::Erased),
    );
    let (result, stats) = unbox_ext_decls_default(&[decl]);
    // Object inner is not scalar so struct unboxing should not apply
    assert_eq!(result[0].return_type, IRType::Struct(vec![IRType::Object]));
    assert_eq!(stats.structs_unboxed, 0);
}
