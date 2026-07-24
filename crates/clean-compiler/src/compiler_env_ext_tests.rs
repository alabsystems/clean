// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `compiler_env_ext`: env stats, dependency analysis, diff,
//! search, validation, snapshot/restore, and summary.

use super::compiler_env_ext::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;
use std::collections::HashSet;

// ── Helpers ──────────────────────────────────────────────────────────────

fn mk_decl(name: &str, num_params: usize) -> IRDecl {
    let params: Vec<_> = (0..num_params)
        .map(|i| (VarId(i as u32), IRType::Object))
        .collect();
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: IRType::Object,
        body: IRBody::Unreachable,
    }
}

fn mk_decl_with_body(name: &str, num_params: usize, body: IRBody) -> IRDecl {
    let params: Vec<_> = (0..num_params)
        .map(|i| (VarId(i as u32), IRType::Object))
        .collect();
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: IRType::Object,
        body,
    }
}

/// Build a VDecl chain: `let v0 = lit 0; let v1 = lit 1; ...; ret v_last`
fn mk_chain_body(len: usize) -> IRBody {
    if len == 0 {
        return IRBody::Ret(IRArg::Var(VarId(0)));
    }
    let mut body = IRBody::Ret(IRArg::Var(VarId(len as u32 - 1)));
    for i in (0..len).rev() {
        body = IRBody::VDecl {
            var: VarId(i as u32),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(i as u64)),
            rest: Box::new(body),
        };
    }
    body
}

/// Build a body that calls `target` via Apply.
fn mk_call_body(target: &str) -> IRBody {
    IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: FnId(Name::from_string(target)),
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    }
}

/// Build a body with a Case node.
fn mk_case_body() -> IRBody {
    IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: CtorInfo {
                name: Name::from_string("C.mk"),
                tag: 0,
                num_scalars: 0,
                num_objects: 0,
                field_types: vec![],
            },
            body: Box::new(IRBody::Ret(IRArg::Erased)),
        }],
        default: Some(Box::new(IRBody::Unreachable)),
    }
}

// ── EnvStats tests ───────────────────────────────────────────────────────

#[test]
fn test_env_stats_empty() {
    let s = env_stats(&[]);
    assert_eq!(s.total_decls, 0);
    assert_eq!(s.nullary_decls, 0);
    assert_eq!(s.function_decls, 0);
    assert_eq!(s.unreachable_decls, 0);
    assert_eq!(s.total_ir_nodes, 0);
}

#[test]
fn test_env_stats_single_nullary() {
    let decls = vec![mk_decl("c", 0)];
    let s = env_stats(&decls);
    assert_eq!(s.total_decls, 1);
    assert_eq!(s.nullary_decls, 1);
    assert_eq!(s.function_decls, 0);
    assert_eq!(s.unreachable_decls, 1);
}

#[test]
fn test_env_stats_mixed() {
    let decls = vec![
        mk_decl("f", 2),
        mk_decl("c", 0),
        mk_decl_with_body("g", 1, mk_chain_body(3)),
    ];
    let s = env_stats(&decls);
    assert_eq!(s.total_decls, 3);
    assert_eq!(s.nullary_decls, 1);
    assert_eq!(s.function_decls, 2);
    assert_eq!(s.unreachable_decls, 2); // f and c
                                        // g has 3 VDecl + 1 Ret = 4 nodes; f and c have 1 Unreachable each
    assert_eq!(s.total_ir_nodes, 4 + 1 + 1);
}

#[test]
fn test_env_stats_total_ir_nodes_chain() {
    let body = mk_chain_body(5);
    let decls = vec![mk_decl_with_body("h", 0, body)];
    let s = env_stats(&decls);
    assert_eq!(s.total_ir_nodes, 6); // 5 VDecl + 1 Ret
}

#[test]
fn test_avg_function_size_empty() {
    assert_eq!(avg_function_size(&[]), 0);
}

#[test]
fn test_avg_function_size_single() {
    let decls = vec![mk_decl_with_body("f", 1, mk_chain_body(4))];
    assert_eq!(avg_function_size(&decls), 5); // 4 VDecl + 1 Ret
}

#[test]
fn test_avg_function_size_multiple() {
    let decls = vec![
        mk_decl_with_body("a", 0, mk_chain_body(2)), // 3 nodes
        mk_decl_with_body("b", 0, mk_chain_body(4)), // 5 nodes
    ];
    // average = (3 + 5) / 2 = 4
    assert_eq!(avg_function_size(&decls), 4);
}

// ── Dependency graph tests ───────────────────────────────────────────────

#[test]
fn test_dependency_graph_empty() {
    let g = dependency_graph(&[]);
    assert!(g.is_empty());
}

#[test]
fn test_dependency_graph_no_calls() {
    let decls = vec![mk_decl("f", 1), mk_decl("g", 2)];
    let g = dependency_graph(&decls);
    assert!(g[&Name::from_string("f")].is_empty());
    assert!(g[&Name::from_string("g")].is_empty());
}

#[test]
fn test_dependency_graph_simple_call() {
    let decls = vec![
        mk_decl_with_body("caller", 0, mk_call_body("callee")),
        mk_decl("callee", 1),
    ];
    let g = dependency_graph(&decls);
    assert!(g[&Name::from_string("caller")].contains(&Name::from_string("callee")));
    assert!(g[&Name::from_string("callee")].is_empty());
}

#[test]
fn test_dependency_graph_self_recursive() {
    let decls = vec![mk_decl_with_body("rec", 1, mk_call_body("rec"))];
    let g = dependency_graph(&decls);
    assert!(g[&Name::from_string("rec")].contains(&Name::from_string("rec")));
}

#[test]
fn test_dependency_graph_partial_apply() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: FnId(Name::from_string("target")),
            arity: 3,
            args: vec![IRArg::Var(VarId(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decls = vec![mk_decl_with_body("pa", 1, body), mk_decl("target", 3)];
    let g = dependency_graph(&decls);
    assert!(g[&Name::from_string("pa")].contains(&Name::from_string("target")));
}

// ── SCC tests ────────────────────────────────────────────────────────────

#[test]
fn test_scc_no_cycles() {
    let decls = vec![
        mk_decl_with_body("a", 0, mk_call_body("b")),
        mk_decl("b", 1),
    ];
    let g = dependency_graph(&decls);
    let sccs = strongly_connected_components(&g);
    // Each is its own SCC (no cycle).
    assert_eq!(sccs.len(), 2);
    for scc in &sccs {
        assert_eq!(scc.len(), 1);
    }
}

#[test]
fn test_scc_mutual_recursion() {
    let decls = vec![
        mk_decl_with_body("a", 1, mk_call_body("b")),
        mk_decl_with_body("b", 1, mk_call_body("a")),
    ];
    let g = dependency_graph(&decls);
    let sccs = strongly_connected_components(&g);
    // a and b form one SCC.
    let big: Vec<_> = sccs.iter().filter(|s| s.len() == 2).collect();
    assert_eq!(big.len(), 1);
    let names: HashSet<_> = big[0].iter().map(|n| n.to_string()).collect();
    assert!(names.contains("a"));
    assert!(names.contains("b"));
}

#[test]
fn test_scc_self_loop() {
    let decls = vec![mk_decl_with_body("r", 1, mk_call_body("r"))];
    let g = dependency_graph(&decls);
    let sccs = strongly_connected_components(&g);
    assert_eq!(sccs.len(), 1);
    assert_eq!(sccs[0].len(), 1);
}

#[test]
fn test_scc_diamond() {
    // a -> b, a -> c, b -> d, c -> d (no cycles)
    let decls = vec![
        mk_decl_with_body(
            "a",
            0,
            IRBody::VDecl {
                var: VarId(0),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(Name::from_string("b")),
                    args: vec![],
                },
                rest: Box::new(IRBody::VDecl {
                    var: VarId(1),
                    ty: IRType::Object,
                    value: IRExpr::Apply {
                        fn_id: FnId(Name::from_string("c")),
                        args: vec![],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
                }),
            },
        ),
        mk_decl_with_body("b", 0, mk_call_body("d")),
        mk_decl_with_body("c", 0, mk_call_body("d")),
        mk_decl("d", 0),
    ];
    let g = dependency_graph(&decls);
    let sccs = strongly_connected_components(&g);
    // All singleton SCCs.
    assert_eq!(sccs.len(), 4);
    for scc in &sccs {
        assert_eq!(scc.len(), 1);
    }
}

// ── EnvDiff tests ────────────────────────────────────────────────────────

#[test]
fn test_env_diff_identical() {
    let decls = vec![mk_decl("f", 1), mk_decl("g", 2)];
    let diff = env_diff(&decls, &decls);
    assert!(diff.is_empty());
    assert_eq!(diff.change_count(), 0);
}

#[test]
fn test_env_diff_added() {
    let old = vec![mk_decl("f", 1)];
    let new = vec![mk_decl("f", 1), mk_decl("g", 2)];
    let diff = env_diff(&old, &new);
    assert_eq!(diff.added.len(), 1);
    assert_eq!(diff.added[0].to_string(), "g");
    assert!(diff.removed.is_empty());
    assert!(diff.modified.is_empty());
}

#[test]
fn test_env_diff_removed() {
    let old = vec![mk_decl("f", 1), mk_decl("g", 2)];
    let new = vec![mk_decl("f", 1)];
    let diff = env_diff(&old, &new);
    assert!(diff.added.is_empty());
    assert_eq!(diff.removed.len(), 1);
    assert_eq!(diff.removed[0].to_string(), "g");
}

#[test]
fn test_env_diff_modified_arity() {
    let old = vec![mk_decl("f", 1)];
    let new = vec![mk_decl("f", 3)];
    let diff = env_diff(&old, &new);
    assert!(diff.added.is_empty());
    assert!(diff.removed.is_empty());
    assert_eq!(diff.modified.len(), 1);
    assert_eq!(diff.modified[0].to_string(), "f");
}

#[test]
fn test_env_diff_modified_body() {
    let old = vec![mk_decl("f", 1)]; // Unreachable = 1 node
    let new = vec![mk_decl_with_body("f", 1, mk_chain_body(3))]; // 4 nodes
    let diff = env_diff(&old, &new);
    assert_eq!(diff.modified.len(), 1);
}

#[test]
fn test_env_diff_combined() {
    let old = vec![mk_decl("a", 1), mk_decl("b", 2)];
    let new = vec![mk_decl("a", 1), mk_decl("c", 0)];
    let diff = env_diff(&old, &new);
    assert_eq!(diff.added, vec![Name::from_string("c")]);
    assert_eq!(diff.removed, vec![Name::from_string("b")]);
    assert!(diff.modified.is_empty());
    assert_eq!(diff.change_count(), 2);
}

#[test]
fn test_env_diff_empty_to_nonempty() {
    let diff = env_diff(&[], &[mk_decl("x", 0)]);
    assert_eq!(diff.added.len(), 1);
    assert!(diff.removed.is_empty());
}

#[test]
fn test_env_diff_nonempty_to_empty() {
    let diff = env_diff(&[mk_decl("x", 0)], &[]);
    assert!(diff.added.is_empty());
    assert_eq!(diff.removed.len(), 1);
}

// ── Search tests ─────────────────────────────────────────────────────────

#[test]
fn test_search_by_name_hit() {
    let decls = vec![
        mk_decl("List.map", 2),
        mk_decl("List.filter", 2),
        mk_decl("Nat.add", 2),
    ];
    let results = search_by_name(&decls, "List");
    assert_eq!(results.len(), 2);
}

#[test]
fn test_search_by_name_miss() {
    let decls = vec![mk_decl("foo", 1)];
    let results = search_by_name(&decls, "bar");
    assert!(results.is_empty());
}

#[test]
fn test_search_by_name_empty_pattern() {
    let decls = vec![mk_decl("f", 1), mk_decl("g", 2)];
    let results = search_by_name(&decls, "");
    assert_eq!(results.len(), 2); // empty pattern matches everything
}

#[test]
fn test_search_by_arity() {
    let decls = vec![
        mk_decl("a", 0),
        mk_decl("b", 2),
        mk_decl("c", 2),
        mk_decl("d", 3),
    ];
    let results = search_by_arity(&decls, 2);
    assert_eq!(results.len(), 2);
}

#[test]
fn test_search_by_arity_zero() {
    let decls = vec![mk_decl("a", 0), mk_decl("b", 1)];
    let results = search_by_arity(&decls, 0);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name.to_string(), "a");
}

#[test]
fn test_search_large_bodies() {
    let decls = vec![
        mk_decl_with_body("small", 0, mk_chain_body(1)), // 2 nodes
        mk_decl_with_body("large", 0, mk_chain_body(10)), // 11 nodes
    ];
    let results = search_large_bodies(&decls, 5);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name.to_string(), "large");
}

#[test]
fn test_search_large_bodies_none() {
    let decls = vec![mk_decl("f", 1)]; // 1 node (Unreachable)
    let results = search_large_bodies(&decls, 100);
    assert!(results.is_empty());
}

#[test]
fn test_search_with_cases_hit() {
    let decls = vec![
        mk_decl_with_body("matcher", 1, mk_case_body()),
        mk_decl("plain", 1),
    ];
    let results = search_with_cases(&decls);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name.to_string(), "matcher");
}

#[test]
fn test_search_with_cases_none() {
    let decls = vec![mk_decl("f", 1), mk_decl("g", 0)];
    let results = search_with_cases(&decls);
    assert!(results.is_empty());
}

// ── Validation tests ─────────────────────────────────────────────────────

#[test]
fn test_validate_env_clean() {
    let decls = vec![
        mk_decl_with_body("f", 0, mk_call_body("g")),
        mk_decl("g", 0),
    ];
    let errors = validate_env(&decls, &HashSet::new());
    assert!(errors.is_empty());
}

#[test]
fn test_validate_env_dangling_ref() {
    let decls = vec![mk_decl_with_body("f", 0, mk_call_body("missing"))];
    let errors = validate_env(&decls, &HashSet::new());
    assert_eq!(errors.len(), 1);
    assert!(matches!(errors[0], EnvValidationError::DanglingRef(..)));
}

#[test]
fn test_validate_env_dangling_ref_allowed_external() {
    let decls = vec![mk_decl_with_body("f", 0, mk_call_body("extern_fn"))];
    let mut ext = HashSet::new();
    ext.insert(Name::from_string("extern_fn"));
    let errors = validate_env(&decls, &ext);
    assert!(errors.is_empty());
}

#[test]
fn test_validate_env_duplicate_name() {
    let decls = vec![mk_decl("dup", 0), mk_decl("dup", 1)];
    let errors = validate_env(&decls, &HashSet::new());
    let dup_errors: Vec<_> = errors
        .iter()
        .filter(|e| matches!(e, EnvValidationError::DuplicateName(..)))
        .collect();
    assert_eq!(dup_errors.len(), 1);
}

#[test]
fn test_validate_env_unreachable_with_params() {
    let decls = vec![mk_decl("stub", 3)]; // Unreachable body with 3 params
    let errors = validate_env(&decls, &HashSet::new());
    let unr_errors: Vec<_> = errors
        .iter()
        .filter(|e| matches!(e, EnvValidationError::UnreachableWithParams(..)))
        .collect();
    assert_eq!(unr_errors.len(), 1);
}

#[test]
fn test_validate_env_unreachable_no_params_ok() {
    let decls = vec![mk_decl("const_val", 0)]; // Unreachable body, 0 params — OK
    let errors = validate_env(&decls, &HashSet::new());
    // No UnreachableWithParams error since params is empty.
    let unr: Vec<_> = errors
        .iter()
        .filter(|e| matches!(e, EnvValidationError::UnreachableWithParams(..)))
        .collect();
    assert!(unr.is_empty());
}

#[test]
fn test_validate_env_multiple_errors() {
    let decls = vec![
        mk_decl("dup", 0),
        mk_decl("dup", 2),
        mk_decl_with_body("caller", 0, mk_call_body("nonexistent")),
    ];
    let errors = validate_env(&decls, &HashSet::new());
    // At least: 1 duplicate + 1 dangling + 1 unreachable-with-params
    assert!(errors.len() >= 3);
}

// ── Snapshot / restore tests ─────────────────────────────────────────────

#[test]
fn test_snapshot_capture_empty() {
    let snap = EnvSnapshot::capture(&[]);
    assert!(snap.is_empty());
    assert_eq!(snap.len(), 0);
}

#[test]
fn test_snapshot_roundtrip() {
    let decls = vec![mk_decl("a", 1), mk_decl("b", 2)];
    let snap = EnvSnapshot::capture(&decls);
    assert_eq!(snap.len(), 2);
    let (restored, env) = snap.restore();
    assert_eq!(restored.len(), 2);
    assert_eq!(env.len(), 2);
    assert!(env.get_decl_index(&Name::from_string("a")).is_some());
    assert!(env.get_decl_index(&Name::from_string("b")).is_some());
}

#[test]
fn test_snapshot_independence() {
    let decls = vec![mk_decl("x", 0)];
    let snap = EnvSnapshot::capture(&decls);
    // Restoring twice yields independent copies.
    let (r1, _) = snap.restore();
    let (r2, _) = snap.restore();
    assert_eq!(r1.len(), r2.len());
}

// ── Summary tests ────────────────────────────────────────────────────────

#[test]
fn test_env_summary_empty() {
    let summary = env_summary(&[], 5);
    assert_eq!(summary.stats.total_decls, 0);
    assert_eq!(summary.scc_count, 0);
    assert_eq!(summary.recursive_sccs, 0);
    assert!(summary.largest_decls.is_empty());
}

#[test]
fn test_env_summary_basic() {
    let decls = vec![
        mk_decl_with_body("small", 0, mk_chain_body(1)),
        mk_decl_with_body("big", 0, mk_chain_body(10)),
    ];
    let summary = env_summary(&decls, 3);
    assert_eq!(summary.stats.total_decls, 2);
    // Largest should be "big" first.
    assert_eq!(summary.largest_decls[0].0, "big");
    assert_eq!(summary.largest_decls[0].1, 11); // 10 VDecl + 1 Ret
}

#[test]
fn test_env_summary_recursive_scc() {
    let decls = vec![mk_decl_with_body("r", 1, mk_call_body("r"))];
    let summary = env_summary(&decls, 5);
    assert_eq!(summary.scc_count, 1);
    assert_eq!(summary.recursive_sccs, 1);
}

#[test]
fn test_env_summary_display() {
    let decls = vec![mk_decl("f", 1)];
    let summary = env_summary(&decls, 5);
    let text = format!("{summary}");
    assert!(text.contains("Environment Summary"));
    assert!(text.contains("declarations: 1"));
}

#[test]
fn test_env_summary_top_n_limit() {
    let decls: Vec<_> = (0..10)
        .map(|i| mk_decl_with_body(&format!("f{i}"), 0, mk_chain_body(i + 1)))
        .collect();
    let summary = env_summary(&decls, 3);
    assert_eq!(summary.largest_decls.len(), 3);
    // Largest body size should be first.
    assert!(summary.largest_decls[0].1 >= summary.largest_decls[1].1);
    assert!(summary.largest_decls[1].1 >= summary.largest_decls[2].1);
}

// ── Error Display tests ──────────────────────────────────────────────────

#[test]
fn test_error_display_dangling_ref() {
    let e = EnvValidationError::DanglingRef("f".to_string(), "g".to_string());
    let msg = format!("{e}");
    assert!(msg.contains("f"));
    assert!(msg.contains("g"));
    assert!(msg.contains("undefined"));
}

#[test]
fn test_error_display_duplicate() {
    let e = EnvValidationError::DuplicateName("dup".to_string());
    assert!(format!("{e}").contains("dup"));
}

#[test]
fn test_error_display_unreachable_with_params() {
    let e = EnvValidationError::UnreachableWithParams("stub".to_string());
    assert!(format!("{e}").contains("stub"));
    assert!(format!("{e}").contains("Unreachable"));
}
