// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended boxing cache module.

use crate::boxing_cache_ext::*;
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_decl(name: &str, params: Vec<(VarId, IRType)>, ret: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: ret,
        body,
    }
}

fn ret_erased() -> IRBody {
    IRBody::Ret(IRArg::Erased)
}

fn ret_var(v: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(VarId(v)))
}

fn vdecl(var: u32, ty: IRType, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: VarId(var),
        ty,
        value,
        rest: Box::new(rest),
    }
}

fn box_expr(ty: IRType, v: u32) -> IRExpr {
    IRExpr::Box {
        ty,
        arg: IRArg::Var(VarId(v)),
    }
}

fn unbox_expr(ty: IRType, v: u32) -> IRExpr {
    IRExpr::Unbox {
        ty,
        arg: IRArg::Var(VarId(v)),
    }
}

fn apply_expr(name: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: FnId(Name::from_string(name)),
        args,
    }
}

// ---------------------------------------------------------------------------
// BoxingDecisionCache
// ---------------------------------------------------------------------------

#[test]
fn test_decision_cache_new_is_empty() {
    let cache = BoxingDecisionCache::new();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
    assert_eq!(cache.hits(), 0);
    assert_eq!(cache.misses(), 0);
}

#[test]
fn test_decision_cache_classify_scalar_unboxed() {
    let mut cache = BoxingDecisionCache::new();
    assert_eq!(*cache.decide(&IRType::UInt64), BoxingDecision::Unboxed);
    assert_eq!(*cache.decide(&IRType::Bool), BoxingDecision::Unboxed);
    assert_eq!(*cache.decide(&IRType::Float64), BoxingDecision::Unboxed);
}

#[test]
fn test_decision_cache_classify_object_boxed() {
    let mut cache = BoxingDecisionCache::new();
    assert_eq!(*cache.decide(&IRType::Object), BoxingDecision::Boxed);
    assert_eq!(*cache.decide(&IRType::TObject), BoxingDecision::Boxed);
}

#[test]
fn test_decision_cache_classify_erased_absent() {
    let mut cache = BoxingDecisionCache::new();
    assert_eq!(*cache.decide(&IRType::Erased), BoxingDecision::Absent);
    assert_eq!(*cache.decide(&IRType::Void), BoxingDecision::Absent);
}

#[test]
fn test_decision_cache_hit_tracking() {
    let mut cache = BoxingDecisionCache::new();
    let _ = cache.decide(&IRType::UInt64); // miss
    let _ = cache.decide(&IRType::UInt64); // hit
    let _ = cache.decide(&IRType::UInt64); // hit
    assert_eq!(cache.misses(), 1);
    assert_eq!(cache.hits(), 2);
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_decision_cache_invalidate_all() {
    let mut cache = BoxingDecisionCache::new();
    let _ = cache.decide(&IRType::UInt64);
    let _ = cache.decide(&IRType::Object);
    assert_eq!(cache.len(), 2);
    cache.invalidate_all();
    assert!(cache.is_empty());
    assert_eq!(cache.hits(), 0);
    assert_eq!(cache.misses(), 0);
}

#[test]
fn test_decision_cache_invalidate_one() {
    let mut cache = BoxingDecisionCache::new();
    let _ = cache.decide(&IRType::UInt64);
    let _ = cache.decide(&IRType::Object);
    assert_eq!(cache.len(), 2);
    cache.invalidate(&IRType::UInt64);
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_decision_cache_struct_classified_as_boxed() {
    let mut cache = BoxingDecisionCache::new();
    let st = IRType::Struct(vec![IRType::UInt64, IRType::Bool]);
    assert_eq!(*cache.decide(&st), BoxingDecision::Boxed);
}

#[test]
fn test_decision_cache_union_classified_as_boxed() {
    let mut cache = BoxingDecisionCache::new();
    let u = IRType::Union(vec![IRType::UInt32]);
    assert_eq!(*cache.decide(&u), BoxingDecision::Boxed);
}

// ---------------------------------------------------------------------------
// Scalar classification
// ---------------------------------------------------------------------------

#[test]
fn test_classify_scalar_integers() {
    assert_eq!(classify_scalar(&IRType::Bool), ScalarClass::Integer);
    assert_eq!(classify_scalar(&IRType::UInt8), ScalarClass::Integer);
    assert_eq!(classify_scalar(&IRType::UInt16), ScalarClass::Integer);
    assert_eq!(classify_scalar(&IRType::UInt32), ScalarClass::Integer);
    assert_eq!(classify_scalar(&IRType::UInt64), ScalarClass::Integer);
    assert_eq!(classify_scalar(&IRType::USize), ScalarClass::Integer);
}

#[test]
fn test_classify_scalar_floats() {
    assert_eq!(classify_scalar(&IRType::Float32), ScalarClass::Float);
    assert_eq!(classify_scalar(&IRType::Float64), ScalarClass::Float);
}

#[test]
fn test_classify_scalar_non_scalars() {
    assert_eq!(classify_scalar(&IRType::Object), ScalarClass::NonScalar);
    assert_eq!(classify_scalar(&IRType::TObject), ScalarClass::NonScalar);
    assert_eq!(classify_scalar(&IRType::Erased), ScalarClass::NonScalar);
    assert_eq!(classify_scalar(&IRType::Void), ScalarClass::NonScalar);
}

#[test]
fn test_is_unboxable_scalars() {
    assert!(is_unboxable(&IRType::UInt64));
    assert!(is_unboxable(&IRType::Bool));
    assert!(is_unboxable(&IRType::Float32));
}

#[test]
fn test_is_unboxable_erased_void() {
    assert!(is_unboxable(&IRType::Erased));
    assert!(is_unboxable(&IRType::Void));
}

#[test]
fn test_is_unboxable_object_not() {
    assert!(!is_unboxable(&IRType::Object));
    assert!(!is_unboxable(&IRType::TObject));
}

// ---------------------------------------------------------------------------
// Structure layout analysis
// ---------------------------------------------------------------------------

#[test]
fn test_struct_layout_empty() {
    assert_eq!(analyze_struct_layout(&[]), StructLayout::Empty);
}

#[test]
fn test_struct_layout_all_scalars_flat() {
    let fields = vec![IRType::UInt64, IRType::Bool];
    match analyze_struct_layout(&fields) {
        StructLayout::Flat { total_bytes } => assert_eq!(total_bytes, 9), // 8 + 1
        other => panic!("expected Flat, got {:?}", other),
    }
}

#[test]
fn test_struct_layout_with_object_heap() {
    let fields = vec![IRType::UInt64, IRType::Object];
    assert_eq!(analyze_struct_layout(&fields), StructLayout::HeapAllocated);
}

#[test]
fn test_struct_layout_single_scalar() {
    match analyze_struct_layout(&[IRType::UInt32]) {
        StructLayout::Flat { total_bytes } => assert_eq!(total_bytes, 4),
        other => panic!("expected Flat, got {:?}", other),
    }
}

#[test]
fn test_struct_layout_all_floats() {
    let fields = vec![IRType::Float32, IRType::Float64];
    match analyze_struct_layout(&fields) {
        StructLayout::Flat { total_bytes } => assert_eq!(total_bytes, 12), // 4 + 8
        other => panic!("expected Flat, got {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// Unboxing opportunity detection
// ---------------------------------------------------------------------------

#[test]
fn test_detect_redundant_box_unbox() {
    // let v1 = box(UInt64, v0); let v2 = unbox(UInt64, v1); ret v2
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt64, unbox_expr(IRType::UInt64, 1), ret_var(2)),
    );
    let decl = mk_decl("f", vec![(VarId(0), IRType::UInt64)], IRType::UInt64, body);
    let opps = detect_unbox_opportunities(&decl);
    assert_eq!(opps.len(), 1);
    assert_eq!(opps[0].var, VarId(1));
    assert_eq!(opps[0].reason, UnboxReason::RedundantBoxUnbox);
}

#[test]
fn test_detect_no_opportunities_simple_return() {
    let decl = mk_decl(
        "g",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    let opps = detect_unbox_opportunities(&decl);
    assert!(opps.is_empty());
}

#[test]
fn test_detect_unbox_type_mismatch_no_opportunity() {
    // box UInt64 then unbox UInt32 — not a redundant pair
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt32, unbox_expr(IRType::UInt32, 1), ret_var(2)),
    );
    let decl = mk_decl("h", vec![(VarId(0), IRType::UInt64)], IRType::UInt32, body);
    let opps = detect_unbox_opportunities(&decl);
    assert!(opps.is_empty());
}

// ---------------------------------------------------------------------------
// Boxing coercion insertion
// ---------------------------------------------------------------------------

#[test]
fn test_detect_coercions_box_needed() {
    // callee expects Object param, caller passes var
    let callee = mk_decl(
        "callee",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_var(0),
    );
    let caller_body = vdecl(
        1,
        IRType::Object,
        apply_expr("callee", vec![IRArg::Var(VarId(0))]),
        ret_var(1),
    );
    let caller = mk_decl(
        "caller",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        caller_body,
    );
    let coercions = detect_coercions(&[callee, caller]);
    assert!(coercions
        .iter()
        .any(|c| matches!(c, Coercion::BoxAt { var: VarId(0), .. })));
}

#[test]
fn test_detect_coercions_unbox_needed() {
    // callee expects UInt64 param
    let callee = mk_decl(
        "callee",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    let caller_body = vdecl(
        1,
        IRType::UInt64,
        apply_expr("callee", vec![IRArg::Var(VarId(0))]),
        ret_var(1),
    );
    let caller = mk_decl(
        "caller",
        vec![(VarId(0), IRType::Object)],
        IRType::UInt64,
        caller_body,
    );
    let coercions = detect_coercions(&[callee, caller]);
    assert!(coercions
        .iter()
        .any(|c| matches!(c, Coercion::UnboxAt { .. })));
}

#[test]
fn test_detect_coercions_no_decls() {
    let coercions = detect_coercions(&[]);
    assert!(coercions.is_empty());
}

// ---------------------------------------------------------------------------
// Function boxing signatures and propagation
// ---------------------------------------------------------------------------

#[test]
fn test_build_fn_boxing_sigs() {
    let decl = mk_decl(
        "f",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::UInt64)],
        IRType::Object,
        ret_var(0),
    );
    let sigs = build_fn_boxing_sigs(&[decl]);
    assert_eq!(sigs.len(), 1);
    assert_eq!(sigs[0].param_boxed, vec![true, false]);
    assert!(sigs[0].return_boxed);
}

#[test]
fn test_propagate_fn_boxing_no_change() {
    let decl = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    let decls = vec![decl];
    let mut sigs = build_fn_boxing_sigs(&decls);
    let changed = propagate_fn_boxing(&decls, &mut sigs);
    assert!(!changed);
}

#[test]
fn test_propagate_fn_boxing_callee_requires_boxed() {
    // callee takes Object; caller passes its own param
    let callee = mk_decl(
        "callee",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_var(0),
    );
    let caller_body = vdecl(
        1,
        IRType::Object,
        apply_expr("callee", vec![IRArg::Var(VarId(0))]),
        ret_var(1),
    );
    let caller = mk_decl(
        "caller",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        caller_body,
    );
    let decls = vec![callee, caller];
    let mut sigs = build_fn_boxing_sigs(&decls);
    // Initially caller param 0 is not boxed (UInt64)
    assert!(!sigs[1].param_boxed[0]);
    let changed = propagate_fn_boxing(&decls, &mut sigs);
    assert!(changed);
    assert!(sigs[1].param_boxed[0]);
}

// ---------------------------------------------------------------------------
// Polymorphic boxing
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_polymorphic_erased() {
    assert_eq!(resolve_polymorphic_type(&IRType::Erased), IRType::Object);
}

#[test]
fn test_resolve_polymorphic_void() {
    assert_eq!(resolve_polymorphic_type(&IRType::Void), IRType::Void);
}

#[test]
fn test_resolve_polymorphic_scalar() {
    assert_eq!(resolve_polymorphic_type(&IRType::UInt64), IRType::Object);
}

#[test]
fn test_resolve_polymorphic_object_unchanged() {
    assert_eq!(resolve_polymorphic_type(&IRType::Object), IRType::Object);
}

#[test]
fn test_count_polymorphic_params_none() {
    let decl = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    assert_eq!(count_polymorphic_params(&decl), 0);
}

#[test]
fn test_count_polymorphic_params_some() {
    let decl = mk_decl(
        "g",
        vec![
            (VarId(0), IRType::Erased),
            (VarId(1), IRType::UInt64),
            (VarId(2), IRType::Erased),
        ],
        IRType::Object,
        ret_erased(),
    );
    assert_eq!(count_polymorphic_params(&decl), 2);
}

// ---------------------------------------------------------------------------
// Boxing elimination
// ---------------------------------------------------------------------------

#[test]
fn test_eliminate_pairs_basic() {
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt64, unbox_expr(IRType::UInt64, 1), ret_var(2)),
    );
    let (new_body, result) = eliminate_boxing_pairs(&body);
    assert_eq!(result.pairs_eliminated, 1);
    // After elimination, the unbox should read from var 0 instead of var 1
    match &new_body {
        IRBody::VDecl { rest, .. } => match rest.as_ref() {
            IRBody::VDecl { value, .. } => match value {
                IRExpr::Unbox {
                    arg: IRArg::Var(v), ..
                } => assert_eq!(*v, VarId(0)),
                other => panic!("expected Unbox, got {:?}", other),
            },
            other => panic!("expected VDecl, got {:?}", other),
        },
        other => panic!("expected VDecl, got {:?}", other),
    }
}

#[test]
fn test_eliminate_pairs_no_pairs() {
    let body = ret_var(0);
    let (_, result) = eliminate_boxing_pairs(&body);
    assert_eq!(result.pairs_eliminated, 0);
}

#[test]
fn test_eliminate_pairs_type_mismatch_preserved() {
    // box UInt64 then unbox UInt32 — should NOT be eliminated
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt32, unbox_expr(IRType::UInt32, 1), ret_var(2)),
    );
    let (_, result) = eliminate_boxing_pairs(&body);
    assert_eq!(result.pairs_eliminated, 0);
}

// ---------------------------------------------------------------------------
// Signature tracker / cache invalidation
// ---------------------------------------------------------------------------

#[test]
fn test_signature_tracker_new_reports_changed() {
    let tracker = SignatureTracker::new();
    let decl = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    assert!(tracker.has_changed(&decl)); // never recorded => changed
}

#[test]
fn test_signature_tracker_recorded_not_changed() {
    let mut tracker = SignatureTracker::new();
    let decl = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    tracker.record(&decl);
    assert!(!tracker.has_changed(&decl));
}

#[test]
fn test_signature_tracker_changed_return_type() {
    let mut tracker = SignatureTracker::new();
    let decl_v1 = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    tracker.record(&decl_v1);
    let decl_v2 = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        ret_var(0),
    );
    assert!(tracker.has_changed(&decl_v2));
}

#[test]
fn test_signature_tracker_changed_param_type() {
    let mut tracker = SignatureTracker::new();
    let decl_v1 = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    tracker.record(&decl_v1);
    let decl_v2 = mk_decl(
        "f",
        vec![(VarId(0), IRType::Object)],
        IRType::UInt64,
        ret_var(0),
    );
    assert!(tracker.has_changed(&decl_v2));
}

#[test]
fn test_signature_tracker_clear() {
    let mut tracker = SignatureTracker::new();
    let decl = mk_decl("f", vec![], IRType::Void, ret_erased());
    tracker.record(&decl);
    assert!(!tracker.has_changed(&decl));
    tracker.clear();
    assert!(tracker.has_changed(&decl));
}

#[test]
fn test_signature_tracker_tracked_names() {
    let mut tracker = SignatureTracker::new();
    tracker.record(&mk_decl("alpha", vec![], IRType::Void, ret_erased()));
    tracker.record(&mk_decl("beta", vec![], IRType::Void, ret_erased()));
    let names = tracker.tracked_names();
    assert_eq!(names.len(), 2);
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

#[test]
fn test_collect_ext_stats_empty() {
    let stats = collect_ext_stats(&[]);
    assert_eq!(stats.decisions_cached, 0);
    assert_eq!(stats.pairs_eliminated, 0);
    assert_eq!(stats.coercions_detected, 0);
}

#[test]
fn test_collect_ext_stats_with_boxing() {
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt64, unbox_expr(IRType::UInt64, 1), ret_var(2)),
    );
    let decl = mk_decl("f", vec![(VarId(0), IRType::UInt64)], IRType::UInt64, body);
    let stats = collect_ext_stats(&[decl]);
    assert!(stats.decisions_cached > 0);
    assert_eq!(stats.pairs_eliminated, 1);
    assert_eq!(stats.unbox_opportunities, 1);
}

#[test]
fn test_stats_summary_format() {
    let stats = BoxingCacheExtStats {
        decisions_cached: 5,
        cache_hits: 3,
        cache_misses: 2,
        pairs_eliminated: 1,
        coercions_detected: 4,
        unbox_opportunities: 2,
        polymorphic_params: 1,
        flat_structs: 0,
        heap_structs: 1,
    };
    let s = stats.summary();
    assert!(s.contains("cached=5"));
    assert!(s.contains("elim=1"));
    assert!(s.contains("coerce=4"));
}

#[test]
fn test_collect_ext_stats_polymorphic() {
    let decl = mk_decl(
        "poly",
        vec![(VarId(0), IRType::Erased), (VarId(1), IRType::UInt64)],
        IRType::Object,
        ret_erased(),
    );
    let stats = collect_ext_stats(&[decl]);
    assert_eq!(stats.polymorphic_params, 1);
}

#[test]
fn test_collect_ext_stats_struct_layouts() {
    let body = vdecl(
        1,
        IRType::Struct(vec![IRType::UInt64, IRType::UInt32]),
        IRExpr::Lit(IRLiteral::UInt64(0)),
        ret_var(1),
    );
    let decl = mk_decl("s", vec![], IRType::Void, body);
    let stats = collect_ext_stats(&[decl]);
    assert_eq!(stats.flat_structs, 1);
}
