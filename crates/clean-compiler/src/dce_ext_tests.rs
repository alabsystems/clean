// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended dead code elimination analysis.
//!
//! Part of #3084 - IO/FFI/Native epic.

use super::dce_ext::*;
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;
use std::collections::HashSet;

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

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

fn simple_ctor() -> CtorInfo {
    CtorInfo {
        name: name("Unit.unit"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn trivial_body(v: u32, expr: IRExpr) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::UInt64,
        value: expr,
        rest: Box::new(IRBody::Ret(arg_var(v))),
    }
}

fn make_decl(n: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(n),
        params,
        return_type: IRType::UInt64,
        body,
    }
}

fn make_simple_decl(n: &str, body: IRBody) -> IRDecl {
    make_decl(n, vec![], body)
}

fn calling_body(callee: &str) -> IRBody {
    trivial_body(
        0,
        IRExpr::Apply {
            fn_id: fn_id(callee),
            args: vec![],
        },
    )
}

// =======================================================================
// Reachability analysis
// =======================================================================

#[test]
fn test_compute_reachable_single_entry() {
    let decls = vec![
        make_simple_decl("main", trivial_body(0, lit_u64(42))),
        make_simple_decl("dead", trivial_body(0, lit_u64(0))),
    ];
    let reachable = compute_reachable(&decls, &[name("main")]);
    assert!(reachable.contains(&name("main")));
    assert!(!reachable.contains(&name("dead")));
}

#[test]
fn test_compute_reachable_transitive_chain() {
    let decls = vec![
        make_simple_decl("a", calling_body("b")),
        make_simple_decl("b", calling_body("c")),
        make_simple_decl("c", trivial_body(0, lit_u64(1))),
        make_simple_decl("orphan", trivial_body(0, lit_u64(0))),
    ];
    let reachable = compute_reachable(&decls, &[name("a")]);
    assert_eq!(reachable.len(), 3);
    assert!(reachable.contains(&name("a")));
    assert!(reachable.contains(&name("b")));
    assert!(reachable.contains(&name("c")));
    assert!(!reachable.contains(&name("orphan")));
}

#[test]
fn test_compute_reachable_cycle() {
    let decls = vec![
        make_simple_decl("x", calling_body("y")),
        make_simple_decl("y", calling_body("x")),
    ];
    let reachable = compute_reachable(&decls, &[name("x")]);
    assert_eq!(reachable.len(), 2);
    assert!(reachable.contains(&name("x")));
    assert!(reachable.contains(&name("y")));
}

#[test]
fn test_compute_reachable_no_entries() {
    let decls = vec![make_simple_decl("a", trivial_body(0, lit_u64(1)))];
    let reachable = compute_reachable(&decls, &[]);
    assert!(reachable.is_empty());
}

#[test]
fn test_compute_reachable_multiple_entries() {
    let decls = vec![
        make_simple_decl("ep1", calling_body("shared")),
        make_simple_decl("ep2", trivial_body(0, lit_u64(2))),
        make_simple_decl("shared", trivial_body(0, lit_u64(3))),
        make_simple_decl("dead", trivial_body(0, lit_u64(0))),
    ];
    let reachable = compute_reachable(&decls, &[name("ep1"), name("ep2")]);
    assert_eq!(reachable.len(), 3);
    assert!(reachable.contains(&name("shared")));
    assert!(!reachable.contains(&name("dead")));
}

#[test]
fn test_compute_reachable_empty_decls() {
    let reachable = compute_reachable(&[], &[name("main")]);
    // Entry point is added to live set even without a decl
    assert!(reachable.contains(&name("main")));
}

// =======================================================================
// Validated reachability
// =======================================================================

#[test]
fn test_compute_reachable_validated_ok() {
    let decls = vec![make_simple_decl("main", trivial_body(0, lit_u64(1)))];
    let result = compute_reachable_validated(&decls, &[name("main")]);
    assert!(result.is_ok());
    assert!(result.unwrap().contains(&name("main")));
}

#[test]
fn test_compute_reachable_validated_no_entries() {
    let decls = vec![make_simple_decl("main", trivial_body(0, lit_u64(1)))];
    let result = compute_reachable_validated(&decls, &[]);
    assert_eq!(result, Err(DceExtError::NoEntryPoints));
}

#[test]
fn test_compute_reachable_validated_unknown_entry() {
    let decls = vec![make_simple_decl("main", trivial_body(0, lit_u64(1)))];
    let result = compute_reachable_validated(&decls, &[name("nonexistent")]);
    assert!(matches!(result, Err(DceExtError::UnknownEntryPoint(_))));
}

// =======================================================================
// Dead declaration detection
// =======================================================================

#[test]
fn test_find_dead_decls_basic() {
    let decls = vec![
        make_simple_decl("live", trivial_body(0, lit_u64(1))),
        make_simple_decl("dead", trivial_body(0, lit_u64(0))),
    ];
    let reachable: HashSet<Name> = [name("live")].into_iter().collect();
    let dead = find_dead_decls(&decls, &reachable);
    assert_eq!(dead.len(), 1);
    assert_eq!(dead[0].name, name("dead"));
}

#[test]
fn test_find_dead_decls_all_live() {
    let decls = vec![
        make_simple_decl("a", trivial_body(0, lit_u64(1))),
        make_simple_decl("b", trivial_body(0, lit_u64(2))),
    ];
    let reachable: HashSet<Name> = [name("a"), name("b")].into_iter().collect();
    let dead = find_dead_decls(&decls, &reachable);
    assert!(dead.is_empty());
}

#[test]
fn test_find_dead_decls_all_dead() {
    let decls = vec![
        make_simple_decl("a", trivial_body(0, lit_u64(1))),
        make_simple_decl("b", trivial_body(0, lit_u64(2))),
    ];
    let reachable: HashSet<Name> = HashSet::new();
    let dead = find_dead_decls(&decls, &reachable);
    assert_eq!(dead.len(), 2);
}

#[test]
fn test_find_dead_decls_estimated_size() {
    // A more complex body should have a larger size estimate
    let complex_body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(1),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: lit_u64(2),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::UInt64,
                value: lit_u64(3),
                rest: Box::new(IRBody::Ret(arg_var(2))),
            }),
        }),
    };
    let decls = vec![make_simple_decl("complex", complex_body)];
    let dead = find_dead_decls(&decls, &HashSet::new());
    assert_eq!(dead.len(), 1);
    assert!(
        dead[0].estimated_size > 3,
        "complex body should have >3 nodes"
    );
}

#[test]
fn test_find_dead_decls_empty_input() {
    let dead = find_dead_decls(&[], &HashSet::new());
    assert!(dead.is_empty());
}

// =======================================================================
// Dead parameter detection
// =======================================================================

#[test]
fn test_find_dead_params_unused_param() {
    // fn f(v0: u64) { ret 42 } -- v0 is unused
    let decls = vec![make_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        IRBody::Ret(IRArg::Erased),
    )];
    let dead = find_dead_params(&decls, DceMode::Aggressive);
    assert_eq!(dead.len(), 1);
    assert_eq!(dead[0].decl_name, name("f"));
    assert_eq!(dead[0].param_index, 0);
    assert_eq!(dead[0].var_id, var(0));
}

#[test]
fn test_find_dead_params_all_used() {
    // fn f(v0: u64) { ret v0 }
    let decls = vec![make_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        IRBody::Ret(arg_var(0)),
    )];
    let dead = find_dead_params(&decls, DceMode::Aggressive);
    assert!(dead.is_empty());
}

#[test]
fn test_find_dead_params_mixed() {
    // fn f(v0: u64, v1: u64, v2: u64) { ret v1 } -- v0 and v2 unused
    let decls = vec![make_decl(
        "f",
        vec![
            (var(0), IRType::UInt64),
            (var(1), IRType::UInt64),
            (var(2), IRType::UInt64),
        ],
        IRBody::Ret(arg_var(1)),
    )];
    let dead = find_dead_params(&decls, DceMode::Aggressive);
    assert_eq!(dead.len(), 2);
    let indices: Vec<usize> = dead.iter().map(|d| d.param_index).collect();
    assert!(indices.contains(&0));
    assert!(indices.contains(&2));
}

#[test]
fn test_find_dead_params_conservative_skips_called() {
    // fn main() { Apply(helper, []) }
    // fn helper(v0: u64) { ret Erased } -- v0 unused but helper is called
    let decls = vec![
        make_simple_decl("main", calling_body("helper")),
        make_decl(
            "helper",
            vec![(var(0), IRType::UInt64)],
            IRBody::Ret(IRArg::Erased),
        ),
    ];
    let conservative = find_dead_params(&decls, DceMode::Conservative);
    // Conservative should skip helper since it's called by main
    assert!(conservative.is_empty());

    let aggressive = find_dead_params(&decls, DceMode::Aggressive);
    // Aggressive should still find the dead param
    assert_eq!(aggressive.len(), 1);
    assert_eq!(aggressive[0].decl_name, name("helper"));
}

#[test]
fn test_find_dead_params_no_params() {
    let decls = vec![make_simple_decl("f", IRBody::Ret(IRArg::Erased))];
    let dead = find_dead_params(&decls, DceMode::Aggressive);
    assert!(dead.is_empty());
}

#[test]
fn test_find_dead_params_multiple_decls() {
    let decls = vec![
        make_decl(
            "f",
            vec![(var(0), IRType::UInt64)],
            IRBody::Ret(IRArg::Erased),
        ),
        make_decl(
            "g",
            vec![(var(0), IRType::Object)],
            IRBody::Ret(IRArg::Erased),
        ),
    ];
    let dead = find_dead_params(&decls, DceMode::Aggressive);
    assert_eq!(dead.len(), 2);
    let names: Vec<Name> = dead.iter().map(|d| d.decl_name.clone()).collect();
    assert!(names.contains(&name("f")));
    assert!(names.contains(&name("g")));
}

// =======================================================================
// IR node counting
// =======================================================================

#[test]
fn test_count_body_nodes_ret() {
    assert_eq!(count_body_nodes(&IRBody::Ret(IRArg::Erased)), 1);
}

#[test]
fn test_count_body_nodes_unreachable() {
    assert_eq!(count_body_nodes(&IRBody::Unreachable), 1);
}

#[test]
fn test_count_body_nodes_vdecl_chain() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    // 1 (VDecl) + 1 (Lit) + 1 (Ret) = 3
    assert_eq!(count_body_nodes(&body), 3);
}

#[test]
fn test_count_body_nodes_case() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(IRBody::Ret(IRArg::Erased)),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Erased))),
    };
    // 1 (Case) + 1 (alt ctor) + 1 (alt Ret) + 1 (default Ret) = 4
    assert_eq!(count_body_nodes(&body), 4);
}

#[test]
fn test_count_body_nodes_inc_dec() {
    let body = IRBody::Inc {
        var: var(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        }),
    };
    // 1 (Inc) + 1 (Dec) + 1 (Ret) = 3
    assert_eq!(count_body_nodes(&body), 3);
}

#[test]
fn test_count_decl_nodes_with_params() {
    let decl = make_decl(
        "f",
        vec![(var(0), IRType::UInt64), (var(1), IRType::Object)],
        IRBody::Ret(arg_var(0)),
    );
    // 2 (params) + 1 (Ret) = 3
    assert_eq!(count_decl_nodes(&decl), 3);
}

#[test]
fn test_count_body_nodes_jmp() {
    let body = IRBody::Jmp {
        jp: JoinPointId(0),
        args: vec![arg_var(0), arg_var(1)],
    };
    // 1 (Jmp) + 2 (args) = 3
    assert_eq!(count_body_nodes(&body), 3);
}

// =======================================================================
// Impact estimation
// =======================================================================

#[test]
fn test_estimate_impact_basic() {
    let decls = vec![
        make_simple_decl("live", trivial_body(0, lit_u64(1))),
        make_simple_decl("dead", trivial_body(0, lit_u64(0))),
    ];
    let dead_decls = vec![DeadDecl {
        name: name("dead"),
        estimated_size: count_decl_nodes(&decls[1]),
    }];
    let impact = estimate_impact(&decls, &dead_decls, &[]);
    assert_eq!(impact.removable_decls, 1);
    assert!(impact.removable_nodes > 0);
    assert!(impact.total_nodes > 0);
    assert!(impact.reduction_fraction() > 0.0);
    assert!(impact.reduction_fraction() < 1.0);
}

#[test]
fn test_estimate_impact_nothing_dead() {
    let decls = vec![make_simple_decl("live", trivial_body(0, lit_u64(1)))];
    let impact = estimate_impact(&decls, &[], &[]);
    assert_eq!(impact.removable_decls, 0);
    assert_eq!(impact.removable_nodes, 0);
    assert_eq!(impact.reduction_fraction(), 0.0);
}

#[test]
fn test_estimate_impact_empty_program() {
    let impact = estimate_impact(&[], &[], &[]);
    assert_eq!(impact.total_nodes, 0);
    assert_eq!(impact.reduction_fraction(), 0.0);
}

#[test]
fn test_estimate_impact_with_dead_params() {
    let decls = vec![make_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        IRBody::Ret(IRArg::Erased),
    )];
    let dead_params = vec![DeadParam {
        decl_name: name("f"),
        param_index: 0,
        var_id: var(0),
        param_type: IRType::UInt64,
    }];
    let impact = estimate_impact(&decls, &[], &dead_params);
    assert_eq!(impact.removable_params, 1);
    assert_eq!(impact.removable_decls, 0);
}

// =======================================================================
// DceExtStats
// =======================================================================

#[test]
fn test_dce_ext_stats_fractions_zero() {
    let stats = DceExtStats::default();
    assert_eq!(stats.dead_decl_fraction(), 0.0);
    assert_eq!(stats.dead_param_fraction(), 0.0);
    assert_eq!(stats.estimated_size_reduction(), 0.0);
}

#[test]
fn test_dce_ext_stats_fractions_half() {
    let stats = DceExtStats {
        total_decls: 10,
        reachable_decls: 5,
        dead_decls: 5,
        total_params: 20,
        dead_params: 10,
        dead_node_count: 50,
        total_node_count: 100,
    };
    assert!((stats.dead_decl_fraction() - 0.5).abs() < f64::EPSILON);
    assert!((stats.dead_param_fraction() - 0.5).abs() < f64::EPSILON);
    assert!((stats.estimated_size_reduction() - 0.5).abs() < f64::EPSILON);
}

// =======================================================================
// Full analysis (analyze_dce)
// =======================================================================

#[test]
fn test_analyze_dce_basic() {
    let decls = vec![
        make_simple_decl("main", calling_body("helper")),
        make_simple_decl("helper", trivial_body(0, lit_u64(1))),
        make_simple_decl("dead", trivial_body(0, lit_u64(0))),
    ];
    let report = analyze_dce(&decls, &[name("main")], DceMode::Conservative);
    assert_eq!(report.stats.total_decls, 3);
    assert_eq!(report.stats.dead_decls, 1);
    assert_eq!(report.dead_decls.len(), 1);
    assert_eq!(report.dead_decls[0].name, name("dead"));
    assert_eq!(report.mode, DceMode::Conservative);
}

#[test]
fn test_analyze_dce_no_dead() {
    let decls = vec![
        make_simple_decl("main", calling_body("helper")),
        make_simple_decl("helper", trivial_body(0, lit_u64(1))),
    ];
    let report = analyze_dce(&decls, &[name("main")], DceMode::Conservative);
    assert_eq!(report.stats.dead_decls, 0);
    assert!(report.dead_decls.is_empty());
}

#[test]
fn test_analyze_dce_empty_program() {
    let report = analyze_dce(&[], &[], DceMode::Conservative);
    assert_eq!(report.stats.total_decls, 0);
    assert_eq!(report.stats.dead_decls, 0);
}

#[test]
fn test_analyze_dce_aggressive_finds_dead_params() {
    let decls = vec![make_decl(
        "f",
        vec![(var(0), IRType::UInt64)],
        IRBody::Ret(IRArg::Erased),
    )];
    let report = analyze_dce(&decls, &[name("f")], DceMode::Aggressive);
    assert_eq!(report.dead_params.len(), 1);
    assert_eq!(report.stats.dead_params, 1);
}

// =======================================================================
// DceReport Display
// =======================================================================

#[test]
fn test_dce_report_display_nonempty() {
    let report = DceReport {
        stats: DceExtStats {
            total_decls: 3,
            reachable_decls: 2,
            dead_decls: 1,
            total_params: 5,
            dead_params: 2,
            dead_node_count: 10,
            total_node_count: 30,
        },
        dead_decls: vec![DeadDecl {
            name: name("dead_fn"),
            estimated_size: 10,
        }],
        dead_params: vec![DeadParam {
            decl_name: name("f"),
            param_index: 0,
            var_id: var(0),
            param_type: IRType::UInt64,
        }],
        mode: DceMode::Conservative,
    };
    let text = format!("{}", report);
    assert!(text.contains("conservative"));
    assert!(text.contains("1/3 dead"));
    assert!(text.contains("dead_fn"));
}

#[test]
fn test_dce_report_display_empty() {
    let report = DceReport {
        stats: DceExtStats::default(),
        dead_decls: vec![],
        dead_params: vec![],
        mode: DceMode::Aggressive,
    };
    let text = format!("{}", report);
    assert!(text.contains("aggressive"));
    assert!(text.contains("0/0 dead"));
}

// =======================================================================
// Call graph
// =======================================================================

#[test]
fn test_build_call_graph_basic() {
    let decls = vec![
        make_simple_decl("a", calling_body("b")),
        make_simple_decl("b", calling_body("c")),
        make_simple_decl("c", trivial_body(0, lit_u64(1))),
    ];
    let graph = build_call_graph(&decls);
    assert!(graph[&name("a")].contains(&name("b")));
    assert!(graph[&name("b")].contains(&name("c")));
    assert!(graph[&name("c")].is_empty());
}

#[test]
fn test_build_call_graph_partial_apply() {
    let body = trivial_body(
        0,
        IRExpr::PartialApply {
            fn_id: fn_id("target"),
            arity: 2,
            args: vec![arg_var(0)],
        },
    );
    let decls = vec![make_simple_decl("caller", body)];
    let graph = build_call_graph(&decls);
    assert!(graph[&name("caller")].contains(&name("target")));
}

#[test]
fn test_build_call_graph_empty() {
    let graph = build_call_graph(&[]);
    assert!(graph.is_empty());
}

// =======================================================================
// Uncalled declarations
// =======================================================================

#[test]
fn test_find_uncalled_decls_basic() {
    let decls = vec![
        make_simple_decl("main", calling_body("helper")),
        make_simple_decl("helper", trivial_body(0, lit_u64(1))),
        make_simple_decl("orphan", trivial_body(0, lit_u64(0))),
    ];
    let uncalled = find_uncalled_decls(&decls);
    // main and orphan are never called by anyone
    assert!(uncalled.contains(&name("main")));
    assert!(uncalled.contains(&name("orphan")));
    assert!(!uncalled.contains(&name("helper")));
}

#[test]
fn test_find_uncalled_decls_all_called_in_cycle() {
    let decls = vec![
        make_simple_decl("a", calling_body("b")),
        make_simple_decl("b", calling_body("a")),
    ];
    let uncalled = find_uncalled_decls(&decls);
    // Both call each other, so neither is uncalled
    assert!(uncalled.is_empty());
}

// =======================================================================
// collect_used_vars / is_param_used
// =======================================================================

#[test]
fn test_collect_used_vars_basic() {
    let body = IRBody::Ret(arg_var(5));
    let used = collect_used_vars(&body);
    assert!(used.contains(&var(5)));
}

#[test]
fn test_is_param_used_true() {
    let params = vec![(var(0), IRType::UInt64)];
    let body = IRBody::Ret(arg_var(0));
    assert!(is_param_used(&params, 0, &body));
}

#[test]
fn test_is_param_used_false() {
    let params = vec![(var(0), IRType::UInt64)];
    let body = IRBody::Ret(IRArg::Erased);
    assert!(!is_param_used(&params, 0, &body));
}

#[test]
fn test_is_param_used_out_of_bounds() {
    let params = vec![(var(0), IRType::UInt64)];
    let body = IRBody::Ret(arg_var(0));
    assert!(!is_param_used(&params, 5, &body));
}

// =======================================================================
// DceMode defaults
// =======================================================================

#[test]
fn test_dce_mode_default_is_conservative() {
    assert_eq!(DceMode::default(), DceMode::Conservative);
}

// =======================================================================
// Error formatting
// =======================================================================

#[test]
fn test_dce_ext_error_display() {
    let err = DceExtError::UnknownEntryPoint("foo".to_string());
    assert_eq!(err.to_string(), "unknown entry point: foo");

    let err2 = DceExtError::NoEntryPoints;
    assert_eq!(
        err2.to_string(),
        "no entry points specified for reachability analysis"
    );
}

// =======================================================================
// Edge cases
// =======================================================================

#[test]
fn test_reachability_with_case_branches_calling() {
    // main has a case arm that calls helper
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(trivial_body(
                1,
                IRExpr::Apply {
                    fn_id: fn_id("helper"),
                    args: vec![],
                },
            )),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Erased))),
    };
    let decls = vec![
        make_simple_decl("main", body),
        make_simple_decl("helper", trivial_body(0, lit_u64(1))),
        make_simple_decl("dead", trivial_body(0, lit_u64(0))),
    ];
    let reachable = compute_reachable(&decls, &[name("main")]);
    assert!(reachable.contains(&name("helper")));
    assert!(!reachable.contains(&name("dead")));
}

#[test]
fn test_dead_param_in_complex_body() {
    // fn f(v0, v1) { let v2 := Apply(g, v1); ret v2 } -- v0 dead
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("g"),
            args: vec![arg_var(1)],
        },
        rest: Box::new(IRBody::Ret(arg_var(2))),
    };
    let decls = vec![make_decl(
        "f",
        vec![(var(0), IRType::UInt64), (var(1), IRType::UInt64)],
        body,
    )];
    let dead = find_dead_params(&decls, DceMode::Aggressive);
    assert_eq!(dead.len(), 1);
    assert_eq!(dead[0].param_index, 0);
}

#[test]
fn test_impact_reduction_fraction_all_dead() {
    let decls = vec![make_simple_decl("only", trivial_body(0, lit_u64(1)))];
    let dead_decls = vec![DeadDecl {
        name: name("only"),
        estimated_size: count_decl_nodes(&decls[0]),
    }];
    let impact = estimate_impact(&decls, &dead_decls, &[]);
    assert!((impact.reduction_fraction() - 1.0).abs() < f64::EPSILON);
}
