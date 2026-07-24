// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended inlining pass (inline_pass_ext).
//!
//! Part of #3083 - Extensibility.

use crate::inline_pass::InlineAttr;
use crate::inline_pass_ext::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;
use std::collections::HashMap;

fn var(n: u32) -> VarId {
    VarId(n)
}
fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}
fn lit_u64(v: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(v))
}

fn make_decl(n: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(n),
        params,
        return_type: IRType::UInt64,
        body,
    }
}

fn simple_ctor() -> CtorInfo {
    CtorInfo {
        name: name("Unit.unit"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

// Small function: ret v0
fn ret_body() -> IRBody {
    IRBody::Ret(arg_var(0))
}

// Call body: let v1 := f(v0); ret v1
fn call_body(callee: &str, arg: u32, result: u32) -> IRBody {
    IRBody::VDecl {
        var: var(result),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id(callee),
            args: vec![arg_var(arg)],
        },
        rest: Box::new(IRBody::Ret(arg_var(result))),
    }
}

// ===== ExtInlineConfig tests =====

#[test]
fn test_ext_config_defaults() {
    let c = ExtInlineConfig::default();
    assert_eq!(c.max_inline_size, 20);
    assert_eq!(c.max_inline_depth, 4);
    assert_eq!(c.max_recursive_unroll, 2);
    assert!(c.enable_partial_inline);
    assert!(c.enable_cleanup);
}

#[test]
fn test_ext_config_custom() {
    let c = ExtInlineConfig {
        max_inline_size: 5,
        max_inline_depth: 2,
        max_recursive_unroll: 0,
        benefit_cost_ratio: 2.0,
        enable_partial_inline: false,
        enable_cleanup: false,
        max_growth_factor: 1.0,
    };
    assert_eq!(c.max_inline_size, 5);
    assert!(!c.enable_partial_inline);
}

// ===== InlineCostModel tests =====

#[test]
fn test_cost_model_defaults() {
    let m = InlineCostModel::default();
    assert_eq!(m.call_overhead, 5);
    assert_eq!(m.node_cost, 1);
}

#[test]
fn test_cost_model_benefit_single_call() {
    let m = InlineCostModel::default();
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], ret_body());
    let b = m.estimate_benefit(&d, 1);
    // call_overhead(5) + params(1) + size(1) = 7
    assert_eq!(b, 7);
}

#[test]
fn test_cost_model_benefit_multi_call() {
    let m = InlineCostModel::default();
    let d = make_decl(
        "f",
        vec![(var(0), IRType::UInt64), (var(1), IRType::UInt64)],
        ret_body(),
    );
    let b = m.estimate_benefit(&d, 3);
    // call_overhead(5) + params(2) = 7
    assert_eq!(b, 7);
}

#[test]
fn test_cost_model_cost_single_call_zero() {
    let m = InlineCostModel::default();
    let d = make_decl("f", vec![], ret_body());
    assert_eq!(m.estimate_cost(&d, 1), 0);
}

#[test]
fn test_cost_model_cost_multi_call() {
    let m = InlineCostModel::default();
    let d = make_decl("f", vec![], ret_body());
    // size(1) * node_cost(1) * (3-1) = 2
    assert_eq!(m.estimate_cost(&d, 3), 2);
}

// ===== CallSiteInfo / analyze_call_sites tests =====

#[test]
fn test_analyze_call_sites_empty() {
    assert!(analyze_call_sites(&[]).is_empty());
}

#[test]
fn test_analyze_call_sites_single_call() {
    let d = make_decl("main", vec![], call_body("helper", 0, 1));
    let sites = analyze_call_sites(&[d]);
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].callee, name("helper"));
    assert_eq!(sites[0].call_count, 1);
    assert!(!sites[0].in_case_branch);
    assert_eq!(sites[0].nesting_depth, 0);
}

#[test]
fn test_analyze_call_sites_multiple_calls() {
    // Two calls to "helper" in the same decl
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("helper"),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("helper"),
                args: vec![arg_var(1)],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };
    let d = make_decl("main", vec![(var(0), IRType::UInt64)], body);
    let sites = analyze_call_sites(&[d]);
    assert_eq!(sites.len(), 2);
    assert!(sites.iter().all(|s| s.call_count == 2));
}

#[test]
fn test_analyze_call_sites_in_case_branch() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(call_body("helper", 0, 1)),
        }],
        default: None,
    };
    let d = make_decl("main", vec![(var(0), IRType::UInt64)], body);
    let sites = analyze_call_sites(&[d]);
    assert_eq!(sites.len(), 1);
    assert!(sites[0].in_case_branch);
    assert_eq!(sites[0].nesting_depth, 1);
}

#[test]
fn test_analyze_call_sites_partial_apply_counted() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::PartialApply {
            fn_id: fn_id("f"),
            arity: 2,
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let d = make_decl("main", vec![(var(0), IRType::UInt64)], body);
    let sites = analyze_call_sites(&[d]);
    // PartialApply counted in count_calls but not collected as a call site by collect_sites
    assert_eq!(sites.len(), 0);
}

// ===== RecursiveInlineTracker tests =====

#[test]
fn test_recursive_tracker_initial_state() {
    let t = RecursiveInlineTracker::default();
    assert!(t.can_unroll(&name("f"), 2));
    assert_eq!(t.depth_of(&name("f")), 0);
}

#[test]
fn test_recursive_tracker_record_and_limit() {
    let mut t = RecursiveInlineTracker::default();
    let n = name("f");
    t.record_unroll(&n);
    assert_eq!(t.depth_of(&n), 1);
    assert!(t.can_unroll(&n, 2));
    t.record_unroll(&n);
    assert_eq!(t.depth_of(&n), 2);
    assert!(!t.can_unroll(&n, 2));
}

#[test]
fn test_recursive_tracker_independent_functions() {
    let mut t = RecursiveInlineTracker::default();
    t.record_unroll(&name("f"));
    t.record_unroll(&name("f"));
    assert_eq!(t.depth_of(&name("f")), 2);
    assert_eq!(t.depth_of(&name("g")), 0);
}

// ===== InlineDepthTracker tests =====

#[test]
fn test_depth_tracker_initial() {
    let t = InlineDepthTracker::default();
    assert!(t.check_depth(1));
    assert_eq!(t.max_depth_seen(), 0);
}

#[test]
fn test_depth_tracker_record_and_pop() {
    let mut t = InlineDepthTracker::default();
    t.record_inline();
    assert_eq!(t.max_depth_seen(), 1);
    assert!(t.check_depth(2));
    assert!(!t.check_depth(1));
    t.pop();
    assert!(t.check_depth(1));
    assert_eq!(t.max_depth_seen(), 1); // max preserved
}

#[test]
fn test_depth_tracker_distribution() {
    let mut t = InlineDepthTracker::default();
    t.record_inline(); // depth 1
    t.record_inline(); // depth 2
    t.pop();
    t.record_inline(); // depth 2 again
    let dist = t.depth_distribution();
    assert_eq!(dist.get(&1), Some(&1));
    assert_eq!(dist.get(&2), Some(&2));
}

#[test]
fn test_depth_tracker_pop_at_zero() {
    let mut t = InlineDepthTracker::default();
    t.pop(); // should saturate at 0
    assert_eq!(t.max_depth_seen(), 0);
    assert!(t.check_depth(1));
}

// ===== Partial inlining tests =====

#[test]
fn test_find_partial_candidates_empty() {
    assert!(find_partial_inline_candidates(&[], 5).is_empty());
}

#[test]
fn test_find_partial_candidates_non_case_ignored() {
    let d = make_decl("f", vec![], ret_body());
    assert!(find_partial_inline_candidates(&[d], 5).is_empty());
}

#[test]
fn test_find_partial_candidates_small_fast_path() {
    // Case with one small alt and body large enough (total > threshold)
    let big_rest = IRBody::VDecl {
        var: var(10),
        ty: IRType::UInt64,
        value: lit_u64(1),
        rest: Box::new(IRBody::VDecl {
            var: var(11),
            ty: IRType::UInt64,
            value: lit_u64(2),
            rest: Box::new(IRBody::VDecl {
                var: var(12),
                ty: IRType::UInt64,
                value: lit_u64(3),
                rest: Box::new(IRBody::Ret(arg_var(12))),
            }),
        }),
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: simple_ctor(),
                body: Box::new(IRBody::Ret(arg_var(0))),
            }, // small
            IRAlt {
                ctor: simple_ctor(),
                body: Box::new(big_rest),
            }, // big
        ],
        default: None,
    };
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], body);
    let cands = find_partial_inline_candidates(&[d], 2);
    assert_eq!(cands.len(), 1);
    assert_eq!(cands[0].fast_alt_idx, 0);
    assert_eq!(cands[0].fast_path_size, 1);
}

#[test]
fn test_find_partial_candidates_all_alts_too_big() {
    let big = IRBody::VDecl {
        var: var(10),
        ty: IRType::UInt64,
        value: lit_u64(1),
        rest: Box::new(IRBody::VDecl {
            var: var(11),
            ty: IRType::UInt64,
            value: lit_u64(2),
            rest: Box::new(IRBody::Ret(arg_var(11))),
        }),
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(big),
        }],
        default: Some(Box::new(IRBody::Ret(arg_var(0)))),
    };
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], body);
    // threshold=1 but alt body has 3 nodes
    let cands = find_partial_inline_candidates(&[d], 1);
    assert!(cands.is_empty());
}

#[test]
fn test_apply_partial_inline_success() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: simple_ctor(),
                body: Box::new(IRBody::Ret(arg_var(0))),
            },
            IRAlt {
                ctor: simple_ctor(),
                body: Box::new(IRBody::Ret(arg_var(1))),
            },
        ],
        default: None,
    };
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], body);
    let result = apply_partial_inline(&d, 0, var(99));
    assert!(result.is_some());
    if let Some(IRBody::Case { alts, default, .. }) = &result {
        assert_eq!(alts.len(), 1);
        assert!(default.is_some());
    }
}

#[test]
fn test_apply_partial_inline_non_case_returns_none() {
    let d = make_decl("f", vec![], ret_body());
    assert!(apply_partial_inline(&d, 0, var(99)).is_none());
}

#[test]
fn test_apply_partial_inline_invalid_index_returns_none() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(ret_body()),
        }],
        default: None,
    };
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], body);
    assert!(apply_partial_inline(&d, 5, var(99)).is_none());
}

// ===== InliningSummary / compute_inlining_summaries tests =====

#[test]
fn test_compute_summaries_empty() {
    assert!(compute_inlining_summaries(&[], &HashMap::new()).is_empty());
}

#[test]
fn test_compute_summaries_basic() {
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], ret_body());
    let mut attrs = HashMap::new();
    attrs.insert(name("f"), InlineAttr::Always);
    let sums = compute_inlining_summaries(&[d], &attrs);
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].name, name("f"));
    assert_eq!(sums[0].size, 1);
    assert_eq!(sums[0].attr, InlineAttr::Always);
    assert!(!sums[0].is_recursive);
    assert_eq!(sums[0].param_count, 1);
    assert!(!sums[0].is_case_dispatch);
}

#[test]
fn test_compute_summaries_recursive_detected() {
    // f calls itself
    let body = call_body("f", 0, 1);
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], body);
    let sums = compute_inlining_summaries(&[d], &HashMap::new());
    assert!(sums[0].is_recursive);
}

#[test]
fn test_compute_summaries_case_dispatch() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(ret_body()),
        }],
        default: None,
    };
    let d = make_decl("f", vec![(var(0), IRType::UInt64)], body);
    let sums = compute_inlining_summaries(&[d], &HashMap::new());
    assert!(sums[0].is_case_dispatch);
}

#[test]
fn test_compute_summaries_default_attr() {
    let d = make_decl("f", vec![], ret_body());
    let sums = compute_inlining_summaries(&[d], &HashMap::new());
    assert_eq!(sums[0].attr, InlineAttr::None);
}

// ===== Copy propagation tests =====

#[test]
fn test_propagate_copies_identity_removed() {
    // let v1 := _identity(v0); ret v1  =>  ret v0
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: FnId(Name::from_string("_identity")),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let result = propagate_copies(&body);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(v)) if v == var(0)));
}

#[test]
fn test_propagate_copies_non_identity_preserved() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("other"),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let result = propagate_copies(&body);
    assert!(matches!(result, IRBody::VDecl { .. }));
}

#[test]
fn test_propagate_copies_chained() {
    // let v1 := _identity(v0); let v2 := _identity(v1); ret v2  =>  ret v0
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: FnId(Name::from_string("_identity")),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: FnId(Name::from_string("_identity")),
                args: vec![arg_var(1)],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };
    let result = propagate_copies(&body);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(v)) if v == var(0)));
}

#[test]
fn test_propagate_copies_in_case() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: FnId(Name::from_string("_identity")),
                    args: vec![arg_var(0)],
                },
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }],
        default: None,
    };
    let result = propagate_copies(&body);
    if let IRBody::Case { alts, .. } = &result {
        assert!(matches!(&*alts[0].body, IRBody::Ret(IRArg::Var(v)) if *v == var(0)));
    } else {
        panic!("expected Case");
    }
}

// ===== Dead variable elimination tests =====

#[test]
fn test_eliminate_dead_pure_unused() {
    // let v1 := Lit(42); ret v0 => ret v0 (v1 unused, pure)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let result = eliminate_dead_vars(&body);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(v)) if v == var(0)));
}

#[test]
fn test_eliminate_dead_used_preserved() {
    // let v1 := Lit(42); ret v1 => preserved (v1 used)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let result = eliminate_dead_vars(&body);
    assert!(matches!(result, IRBody::VDecl { .. }));
}

#[test]
fn test_eliminate_dead_impure_preserved() {
    // let v1 := f(v0); ret v0 => preserved (Apply is impure)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("f"),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let result = eliminate_dead_vars(&body);
    assert!(matches!(result, IRBody::VDecl { .. }));
}

#[test]
fn test_eliminate_dead_in_case() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(IRBody::VDecl {
                var: var(5),
                ty: IRType::UInt64,
                value: lit_u64(99),
                rest: Box::new(IRBody::Ret(arg_var(0))),
            }),
        }],
        default: None,
    };
    let result = eliminate_dead_vars(&body);
    if let IRBody::Case { alts, .. } = &result {
        assert!(matches!(&*alts[0].body, IRBody::Ret(IRArg::Var(v)) if *v == var(0)));
    } else {
        panic!("expected Case");
    }
}

// ===== Extended statistics tests =====

#[test]
fn test_extended_stats_default() {
    let s = ExtendedInlineStats::default();
    assert_eq!(s.inlined_calls, 0);
    assert_eq!(s.code_size_before, 0);
    assert_eq!(s.code_size_after, 0);
    assert_eq!(s.skipped_by_cost, 0);
    assert_eq!(s.skipped_noinline, 0);
    assert_eq!(s.skipped_recursive, 0);
    assert_eq!(s.skipped_depth, 0);
}

// ===== run_extended_inline_pass tests =====

#[test]
fn test_extended_pass_no_calls() {
    let d = make_decl("f", vec![], ret_body());
    let (result, stats) =
        run_extended_inline_pass(&[d], &HashMap::new(), &ExtInlineConfig::default());
    assert_eq!(result.len(), 1);
    assert_eq!(stats.inlined_calls, 0);
    assert_eq!(stats.code_size_before, stats.code_size_after);
}

#[test]
fn test_extended_pass_simple_inline() {
    // helper: ret v0  (size 1, small enough to inline)
    let helper = make_decl("helper", vec![(var(0), IRType::UInt64)], ret_body());
    // main: let v1 := helper(v0); ret v1
    let main = make_decl(
        "main",
        vec![(var(0), IRType::UInt64)],
        call_body("helper", 0, 1),
    );
    let (result, stats) = run_extended_inline_pass(
        &[helper, main],
        &HashMap::new(),
        &ExtInlineConfig::default(),
    );
    assert!(stats.inlined_calls > 0);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_extended_pass_noinline_respected() {
    let helper = make_decl("helper", vec![(var(0), IRType::UInt64)], ret_body());
    let main = make_decl(
        "main",
        vec![(var(0), IRType::UInt64)],
        call_body("helper", 0, 1),
    );
    let mut attrs = HashMap::new();
    attrs.insert(name("helper"), InlineAttr::NoInline);
    let (_, stats) = run_extended_inline_pass(&[helper, main], &attrs, &ExtInlineConfig::default());
    assert_eq!(stats.inlined_calls, 0);
    assert!(stats.skipped_noinline > 0);
}

#[test]
fn test_extended_pass_always_inline() {
    let helper = make_decl("helper", vec![(var(0), IRType::UInt64)], ret_body());
    let main = make_decl(
        "main",
        vec![(var(0), IRType::UInt64)],
        call_body("helper", 0, 1),
    );
    let mut attrs = HashMap::new();
    attrs.insert(name("helper"), InlineAttr::Always);
    let (_, stats) = run_extended_inline_pass(&[helper, main], &attrs, &ExtInlineConfig::default());
    assert!(stats.inlined_calls > 0);
}

#[test]
fn test_extended_pass_recursive_skipped() {
    // f calls itself: should be skipped
    let f = make_decl("f", vec![(var(0), IRType::UInt64)], call_body("f", 0, 1));
    let (_, stats) = run_extended_inline_pass(&[f], &HashMap::new(), &ExtInlineConfig::default());
    assert!(stats.skipped_recursive > 0);
    assert_eq!(stats.inlined_calls, 0);
}

#[test]
fn test_extended_pass_depth_limit() {
    // With max_inline_depth=0, all inlining should be blocked
    let helper = make_decl("helper", vec![(var(0), IRType::UInt64)], ret_body());
    let main = make_decl(
        "main",
        vec![(var(0), IRType::UInt64)],
        call_body("helper", 0, 1),
    );
    let cfg = ExtInlineConfig {
        max_inline_depth: 0,
        ..ExtInlineConfig::default()
    };
    let (_, stats) = run_extended_inline_pass(&[helper, main], &HashMap::new(), &cfg);
    assert_eq!(stats.inlined_calls, 0);
    assert!(stats.skipped_depth > 0);
}

#[test]
fn test_extended_pass_cleanup_disabled() {
    let helper = make_decl("helper", vec![(var(0), IRType::UInt64)], ret_body());
    let main = make_decl(
        "main",
        vec![(var(0), IRType::UInt64)],
        call_body("helper", 0, 1),
    );
    let cfg = ExtInlineConfig {
        enable_cleanup: false,
        ..ExtInlineConfig::default()
    };
    let (result, stats) = run_extended_inline_pass(&[helper, main], &HashMap::new(), &cfg);
    // Should still inline but skip cleanup
    assert!(stats.inlined_calls > 0);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_extended_pass_code_size_tracking() {
    let d = make_decl(
        "f",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: lit_u64(1),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );
    let (_, stats) = run_extended_inline_pass(&[d], &HashMap::new(), &ExtInlineConfig::default());
    assert!(stats.code_size_before > 0);
    assert!(stats.code_size_after > 0);
}

#[test]
fn test_extended_pass_multiple_decls() {
    let f1 = make_decl("f1", vec![], ret_body());
    let f2 = make_decl("f2", vec![], ret_body());
    let f3 = make_decl("f3", vec![], ret_body());
    let (result, _) =
        run_extended_inline_pass(&[f1, f2, f3], &HashMap::new(), &ExtInlineConfig::default());
    assert_eq!(result.len(), 3);
}
