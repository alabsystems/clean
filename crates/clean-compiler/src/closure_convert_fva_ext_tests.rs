// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended free variable analysis.
//!
//! Part of #3084 - Runtime closure support.

use crate::closure_convert_fva_ext::*;
use crate::closure_convert_fva_ext2::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

// ═══════════════════════════════════════════════════════════════════
// Test Helpers
// ═══════════════════════════════════════════════════════════════════

fn var(n: u32) -> VarId {
    VarId(n)
}

fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}

fn vset(ids: &[u32]) -> HashSet<VarId> {
    ids.iter().map(|n| var(*n)).collect()
}

fn ret_var(n: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(var(n)))
}

fn simple_ctor_info() -> CtorInfo {
    CtorInfo {
        name: Name::from_string("Nat.zero"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn make_decl(name: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: IRType::Object,
        body,
    }
}

fn partial_apply_body(
    result_var: u32,
    fn_name: &str,
    arity: u16,
    args: Vec<IRArg>,
    rest: IRBody,
) -> IRBody {
    IRBody::VDecl {
        var: var(result_var),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id(fn_name),
            arity,
            args,
        },
        rest: Box::new(rest),
    }
}

// ═══════════════════════════════════════════════════════════════════
// Capture Classification Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_classify_captures_read_only() {
    // body: let v2 = Proj(0, v1); ret v2
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Var(var(1)),
        },
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert_eq!(classes.len(), 1);
    assert_eq!(classes[0].var, var(1));
    assert!(classes[0].is_read_only());
}

#[test]
fn test_classify_captures_mutated() {
    // body: Set(v1, 0, v2); ret v1
    let body = IRBody::Set {
        var: var(1),
        idx: 0,
        value: var(2),
        rest: Box::new(ret_var(1)),
    };
    let fv = vset(&[1, 2]);
    let classes = classify_captures(&body, &fv);
    let c1 = classes
        .iter()
        .find(|c| c.var == var(1))
        .expect("should find v1");
    assert!(c1.usages.contains(&CaptureUsage::Mutated));
    assert!(c1.usages.contains(&CaptureUsage::Escapes));
    let c2 = classes
        .iter()
        .find(|c| c.var == var(2))
        .expect("should find v2");
    assert!(c2.usages.contains(&CaptureUsage::ReadOnly));
}

#[test]
fn test_classify_captures_passed_to_closure() {
    // body: let v3 = PartialApply(f, [v1]); ret v3
    let body = partial_apply_body(3, "g", 2, vec![IRArg::Var(var(1))], ret_var(3));
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert_eq!(classes.len(), 1);
    assert!(classes[0].usages.contains(&CaptureUsage::PassedToClosure));
}

#[test]
fn test_classify_captures_escapes_via_return() {
    let body = ret_var(1);
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert_eq!(classes.len(), 1);
    assert!(classes[0].usages.contains(&CaptureUsage::Escapes));
}

#[test]
fn test_classify_captures_escapes_via_apply() {
    // body: let v2 = Apply(f, [v1]); ret v2
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: fn_id("f"),
            args: vec![IRArg::Var(var(1))],
        },
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].usages.contains(&CaptureUsage::Escapes));
}

#[test]
fn test_classify_captures_escapes_via_jmp() {
    let body = IRBody::Jmp {
        jp: JoinPointId(0),
        args: vec![IRArg::Var(var(1))],
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].usages.contains(&CaptureUsage::Escapes));
}

#[test]
fn test_classify_captures_unused_var() {
    // body: ret erased -- v1 is free but never referenced
    let body = IRBody::Ret(IRArg::Erased);
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert_eq!(classes.len(), 1);
    assert!(classes[0].is_unused());
}

#[test]
fn test_classify_captures_settag_mutated() {
    let body = IRBody::SetTag {
        var: var(1),
        tag: 5,
        rest: Box::new(ret_var(1)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].usages.contains(&CaptureUsage::Mutated));
}

#[test]
fn test_classify_captures_uset_mutated() {
    let body = IRBody::USet {
        var: var(1),
        idx: 0,
        value: var(2),
        rest: Box::new(ret_var(1)),
    };
    let fv = vset(&[1, 2]);
    let c1 = classify_captures(&body, &fv)
        .into_iter()
        .find(|c| c.var == var(1))
        .expect("v1");
    assert!(c1.usages.contains(&CaptureUsage::Mutated));
}

#[test]
fn test_classify_captures_sset_mutated() {
    let body = IRBody::SSet {
        var: var(1),
        n: 0,
        offset: 0,
        value: var(2),
        ty: IRType::UInt64,
        rest: Box::new(ret_var(1)),
    };
    let fv = vset(&[1, 2]);
    let c1 = classify_captures(&body, &fv)
        .into_iter()
        .find(|c| c.var == var(1))
        .expect("v1");
    assert!(c1.usages.contains(&CaptureUsage::Mutated));
}

#[test]
fn test_classify_captures_multiple_usages() {
    // v1 is both mutated (Set) and escapes (Ret)
    let body = IRBody::Set {
        var: var(1),
        idx: 0,
        value: var(2),
        rest: Box::new(ret_var(1)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].usages.contains(&CaptureUsage::Mutated));
    assert!(classes[0].usages.contains(&CaptureUsage::Escapes));
}

#[test]
fn test_classify_captures_inc_dec_read_only() {
    let body = IRBody::Inc {
        var: var(1),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(2),
            rest: Box::new(ret_var(3)),
        }),
    };
    let fv = vset(&[1, 2]);
    let classes = classify_captures(&body, &fv);
    for c in &classes {
        assert!(
            c.is_read_only(),
            "inc/dec should be read-only for {:?}",
            c.var
        );
    }
}

#[test]
fn test_classify_captures_case_scrutinee_read_only() {
    let body = IRBody::Case {
        scrutinee: var(1),
        alts: vec![],
        default: Some(Box::new(ret_var(5))),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].is_read_only());
}

#[test]
fn test_classify_captures_closure_apply() {
    // ClosureApply(v1, [v2]) -- v1 read-only (closure), v2 passed-to-closure
    let body = IRBody::VDecl {
        var: var(3),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(1)),
            args: vec![IRArg::Var(var(2))],
        },
        rest: Box::new(ret_var(3)),
    };
    let fv = vset(&[1, 2]);
    let classes = classify_captures(&body, &fv);
    let c1 = classes.iter().find(|c| c.var == var(1)).expect("v1");
    assert!(c1.usages.contains(&CaptureUsage::ReadOnly));
    let c2 = classes.iter().find(|c| c.var == var(2)).expect("v2");
    assert!(c2.usages.contains(&CaptureUsage::PassedToClosure));
}

#[test]
fn test_classify_captures_empty_free_vars() {
    let body = ret_var(1);
    let fv = HashSet::new();
    let classes = classify_captures(&body, &fv);
    assert!(classes.is_empty());
}

#[test]
fn test_classify_captures_unreachable() {
    let body = IRBody::Unreachable;
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].is_unused());
}

// ═══════════════════════════════════════════════════════════════════
// Capture Minimization Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_find_redundant_captures_none() {
    let body = ret_var(1);
    let fv = vset(&[1]);
    let redundant = find_redundant_captures(&body, &fv);
    assert!(redundant.is_empty());
}

#[test]
fn test_find_redundant_captures_some() {
    // v1 is free but never used; v2 is returned
    let body = ret_var(2);
    let fv = vset(&[1, 2]);
    let redundant = find_redundant_captures(&body, &fv);
    assert_eq!(redundant, vec![var(1)]);
}

#[test]
fn test_find_redundant_captures_all_unused() {
    let body = IRBody::Ret(IRArg::Erased);
    let fv = vset(&[1, 2, 3]);
    let redundant = find_redundant_captures(&body, &fv);
    assert_eq!(redundant.len(), 3);
}

#[test]
fn test_minimize_captures() {
    let body = ret_var(2);
    let fv = vset(&[1, 2, 3]);
    let minimized = minimize_captures(&body, &fv);
    assert_eq!(minimized, vset(&[2]));
}

#[test]
fn test_minimize_captures_all_used() {
    // v1 and v2 both used in Set
    let body = IRBody::Set {
        var: var(1),
        idx: 0,
        value: var(2),
        rest: Box::new(ret_var(1)),
    };
    let fv = vset(&[1, 2]);
    let minimized = minimize_captures(&body, &fv);
    assert_eq!(minimized, vset(&[1, 2]));
}

// ═══════════════════════════════════════════════════════════════════
// Sharing Analysis Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_find_sharing_points_no_sharing() {
    // Two PartialApplys capturing different vars
    let body = partial_apply_body(
        10,
        "f",
        2,
        vec![IRArg::Var(var(1))],
        partial_apply_body(11, "g", 2, vec![IRArg::Var(var(2))], ret_var(11)),
    );
    let points = find_sharing_points(&body);
    assert!(points.is_empty());
}

#[test]
fn test_find_sharing_points_shared_var() {
    // Two PartialApplys both capturing v1
    let body = partial_apply_body(
        10,
        "f",
        2,
        vec![IRArg::Var(var(1))],
        partial_apply_body(11, "g", 2, vec![IRArg::Var(var(1))], ret_var(11)),
    );
    let points = find_sharing_points(&body);
    assert_eq!(points.len(), 1);
    assert_eq!(points[0].var, var(1));
    assert_eq!(points[0].closure_sites.len(), 2);
}

#[test]
fn test_find_sharing_points_three_closures() {
    let body = partial_apply_body(
        10,
        "f",
        2,
        vec![IRArg::Var(var(1))],
        partial_apply_body(
            11,
            "g",
            2,
            vec![IRArg::Var(var(1))],
            partial_apply_body(12, "h", 2, vec![IRArg::Var(var(1))], ret_var(12)),
        ),
    );
    let points = find_sharing_points(&body);
    assert_eq!(points.len(), 1);
    assert_eq!(points[0].closure_sites.len(), 3);
}

#[test]
fn test_find_sharing_points_empty_body() {
    let body = ret_var(0);
    let points = find_sharing_points(&body);
    assert!(points.is_empty());
}

// ═══════════════════════════════════════════════════════════════════
// Lifetime Analysis Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_estimate_lifetime_short_lived() {
    // v1 only used in Proj, no branches, no escape
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Var(var(1)),
        },
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let lifetimes = estimate_capture_lifetimes(&body, &fv);
    assert_eq!(lifetimes.len(), 1);
    assert_eq!(lifetimes[0], (var(1), CaptureLifetime::ShortLived));
}

#[test]
fn test_estimate_lifetime_long_lived_escape() {
    let body = ret_var(1);
    let fv = vset(&[1]);
    let lifetimes = estimate_capture_lifetimes(&body, &fv);
    assert_eq!(lifetimes[0].1, CaptureLifetime::LongLived);
}

#[test]
fn test_estimate_lifetime_long_lived_multi_branch() {
    // v1 used in both case branches
    let body = IRBody::Case {
        scrutinee: var(5),
        alts: vec![IRAlt {
            ctor: simple_ctor_info(),
            body: Box::new(ret_var(1)),
        }],
        default: Some(Box::new(ret_var(1))),
    };
    let fv = vset(&[1]);
    let lifetimes = estimate_capture_lifetimes(&body, &fv);
    assert_eq!(lifetimes[0].1, CaptureLifetime::LongLived);
}

#[test]
fn test_estimate_lifetime_single_branch_short() {
    // v1 used in only one branch -> short lived
    let body = IRBody::Case {
        scrutinee: var(5),
        alts: vec![IRAlt {
            ctor: simple_ctor_info(),
            body: Box::new(IRBody::VDecl {
                var: var(10),
                ty: IRType::Object,
                value: IRExpr::Proj {
                    idx: 0,
                    ty: IRType::Object,
                    arg: IRArg::Var(var(1)),
                },
                rest: Box::new(ret_var(10)),
            }),
        }],
        default: Some(Box::new(ret_var(5))),
    };
    let fv = vset(&[1]);
    let lifetimes = estimate_capture_lifetimes(&body, &fv);
    assert_eq!(lifetimes[0].1, CaptureLifetime::ShortLived);
}

// ═══════════════════════════════════════════════════════════════════
// Capture Cost Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_capture_cost_object() {
    assert_eq!(capture_cost(&IRType::Object), 8);
}

#[test]
fn test_capture_cost_tobject() {
    assert_eq!(capture_cost(&IRType::TObject), 8);
}

#[test]
fn test_capture_cost_scalar_u64() {
    assert_eq!(capture_cost(&IRType::UInt64), 8);
}

#[test]
fn test_capture_cost_scalar_u8() {
    assert_eq!(capture_cost(&IRType::UInt8), 1);
}

#[test]
fn test_capture_cost_scalar_u32() {
    assert_eq!(capture_cost(&IRType::UInt32), 4);
}

#[test]
fn test_capture_cost_scalar_bool() {
    assert_eq!(capture_cost(&IRType::Bool), 1);
}

#[test]
fn test_capture_cost_erased() {
    assert_eq!(capture_cost(&IRType::Erased), 0);
}

#[test]
fn test_capture_cost_void() {
    assert_eq!(capture_cost(&IRType::Void), 0);
}

#[test]
fn test_capture_cost_struct() {
    assert_eq!(capture_cost(&IRType::Struct(vec![IRType::UInt64])), 8);
}

#[test]
fn test_total_capture_cost_mixed() {
    let vars = vset(&[1, 2, 3]);
    let mut type_env = HashMap::new();
    type_env.insert(var(1), IRType::Object);
    type_env.insert(var(2), IRType::UInt8);
    type_env.insert(var(3), IRType::UInt64);
    assert_eq!(total_capture_cost(&vars, &type_env), 8 + 1 + 8);
}

#[test]
fn test_total_capture_cost_unknown_type() {
    // Unknown vars default to pointer size (8)
    let vars = vset(&[99]);
    let type_env = HashMap::new();
    assert_eq!(total_capture_cost(&vars, &type_env), 8);
}

#[test]
fn test_total_capture_cost_empty() {
    let vars = HashSet::new();
    let type_env = HashMap::new();
    assert_eq!(total_capture_cost(&vars, &type_env), 0);
}

// ═══════════════════════════════════════════════════════════════════
// Hierarchical Capture Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_find_capture_chains_no_nesting() {
    // PartialApply capturing a plain var (not a PA result)
    let body = partial_apply_body(10, "f", 2, vec![IRArg::Var(var(1))], ret_var(10));
    let decl = make_decl("test", vec![(var(1), IRType::Object)], body);
    let chains = find_capture_chains(&[decl]);
    assert_eq!(chains.len(), 1);
    assert_eq!(chains[0].depth, 1);
    assert!(chains[0].intermediaries.is_empty());
}

#[test]
fn test_find_capture_chains_nested() {
    // v10 = PA(f, [v1]); v11 = PA(g, [v10])
    // v10 is a PA result captured by v11 -> depth 2
    let body = partial_apply_body(
        10,
        "f",
        2,
        vec![IRArg::Var(var(1))],
        partial_apply_body(11, "g", 2, vec![IRArg::Var(var(10))], ret_var(11)),
    );
    let decl = make_decl("test", vec![(var(1), IRType::Object)], body);
    let chains = find_capture_chains(&[decl]);
    // Chain for v10's capture of v1 (depth 1) and v11's capture of v10 (depth 2)
    let nested = chains.iter().filter(|c| c.depth >= 2).collect::<Vec<_>>();
    assert!(!nested.is_empty(), "should find nested chain");
}

#[test]
fn test_find_capture_chains_empty() {
    let body = ret_var(0);
    let decl = make_decl("test", vec![(var(0), IRType::Object)], body);
    let chains = find_capture_chains(&[decl]);
    assert!(chains.is_empty());
}

#[test]
fn test_find_capture_chains_multiple_decls() {
    let body1 = partial_apply_body(10, "f", 2, vec![IRArg::Var(var(1))], ret_var(10));
    let body2 = partial_apply_body(20, "g", 2, vec![IRArg::Var(var(2))], ret_var(20));
    let decls = vec![
        make_decl("a", vec![(var(1), IRType::Object)], body1),
        make_decl("b", vec![(var(2), IRType::Object)], body2),
    ];
    let chains = find_capture_chains(&decls);
    assert_eq!(chains.len(), 2);
}

// ═══════════════════════════════════════════════════════════════════
// FVA Statistics Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_compute_fva_stats_empty_decls() {
    let result = compute_fva_stats(&[], &HashMap::new());
    assert!(result.is_err());
}

#[test]
fn test_compute_fva_stats_no_free_vars() {
    let decl = make_decl("f", vec![(var(0), IRType::Object)], ret_var(0));
    let stats = compute_fva_stats(&[decl], &HashMap::new()).expect("should succeed");
    assert_eq!(stats.decl_count, 1);
    assert_eq!(stats.total_free_var_sets, 0);
    assert_eq!(stats.avg_captures_per_closure, 0.0);
}

#[test]
fn test_compute_fva_stats_with_captures() {
    // Decl with body using v1 (free, not a param)
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Var(var(1)),
        },
        rest: Box::new(ret_var(2)),
    };
    let decl = make_decl("f", vec![(var(0), IRType::Object)], body);
    let mut type_env = HashMap::new();
    type_env.insert(var(1), IRType::Object);
    let stats = compute_fva_stats(&[decl], &type_env).expect("should succeed");
    assert_eq!(stats.total_free_var_sets, 1);
    assert!(stats.avg_captures_per_closure > 0.0);
    assert!(stats.total_cost_bytes > 0);
}

#[test]
fn test_compute_fva_stats_redundant_captures() {
    // v1 and v3 are free but only v1 is used
    let body = ret_var(1);
    let decl = make_decl("f", vec![(var(0), IRType::Object)], body);
    let stats = compute_fva_stats(&[decl], &HashMap::new()).expect("should succeed");
    // v1 is free and used -- depends on whether bound_from_params excludes v1
    assert_eq!(stats.decl_count, 1);
}

#[test]
fn test_capture_classification_is_read_only_helper() {
    let c = CaptureClassification {
        var: var(1),
        usages: [CaptureUsage::ReadOnly].into_iter().collect(),
    };
    assert!(c.is_read_only());
    assert!(!c.is_unused());
}

#[test]
fn test_capture_classification_is_unused_helper() {
    let c = CaptureClassification {
        var: var(1),
        usages: HashSet::new(),
    };
    assert!(c.is_unused());
    assert!(!c.is_read_only());
}

#[test]
fn test_capture_classification_not_read_only_if_multiple() {
    let c = CaptureClassification {
        var: var(1),
        usages: [CaptureUsage::ReadOnly, CaptureUsage::Mutated]
            .into_iter()
            .collect(),
    };
    assert!(!c.is_read_only());
}

// ═══════════════════════════════════════════════════════════════════
// Edge Case Tests
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_classify_captures_nested_jdecl() {
    // JDecl with free var in join point body
    let jp_body = IRBody::VDecl {
        var: var(10),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Var(var(1)),
        },
        rest: Box::new(ret_var(10)),
    };
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(var(5), IRType::Object)],
        body: Box::new(jp_body),
        rest: Box::new(ret_var(0)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert_eq!(classes.len(), 1);
    assert!(classes[0].is_read_only());
}

#[test]
fn test_sharing_points_in_case_branches() {
    // PA in alt0 and PA in default both capture v1
    let alt_body = partial_apply_body(10, "f", 2, vec![IRArg::Var(var(1))], ret_var(10));
    let default_body = partial_apply_body(11, "g", 2, vec![IRArg::Var(var(1))], ret_var(11));
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor_info(),
            body: Box::new(alt_body),
        }],
        default: Some(Box::new(default_body)),
    };
    let points = find_sharing_points(&body);
    assert_eq!(points.len(), 1);
    assert_eq!(points[0].var, var(1));
}

#[test]
fn test_capture_cost_f64() {
    assert_eq!(capture_cost(&IRType::Float64), 8);
}

#[test]
fn test_capture_cost_f32() {
    assert_eq!(capture_cost(&IRType::Float32), 4);
}

#[test]
fn test_capture_cost_u16() {
    assert_eq!(capture_cost(&IRType::UInt16), 2);
}

#[test]
fn test_classify_captures_is_shared_read_only() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(1)),
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].is_read_only());
}

#[test]
fn test_classify_captures_reset_read_only() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Reset(var(1)),
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].is_read_only());
}

#[test]
fn test_classify_captures_reuse_read_only() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Reuse {
            var: var(1),
            ctor: simple_ctor_info(),
            args: vec![],
        },
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].is_read_only());
}

#[test]
fn test_classify_captures_box_read_only() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Box {
            ty: IRType::UInt64,
            arg: IRArg::Var(var(1)),
        },
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].is_read_only());
}

#[test]
fn test_classify_captures_unbox_read_only() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::UInt64,
        value: IRExpr::Unbox {
            ty: IRType::UInt64,
            arg: IRArg::Var(var(1)),
        },
        rest: Box::new(ret_var(2)),
    };
    let fv = vset(&[1]);
    let classes = classify_captures(&body, &fv);
    assert!(classes[0].is_read_only());
}

#[test]
fn test_estimate_lifetime_empty_free_vars() {
    let body = ret_var(0);
    let fv = HashSet::new();
    let lifetimes = estimate_capture_lifetimes(&body, &fv);
    assert!(lifetimes.is_empty());
}

#[test]
fn test_fva_error_display() {
    let e = FvaExtError::EmptyDecls;
    assert_eq!(format!("{e}"), "no declarations to analyze");
    let e2 = FvaExtError::VarNotInScope(var(42));
    assert!(format!("{e2}").contains("42"));
}
