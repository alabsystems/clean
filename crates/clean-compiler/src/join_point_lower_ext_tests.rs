// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended join point optimization.
//!
//! Part of #3083 - Extensibility epic.

use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::join_point_lower_ext::{
    analyze_jp_params, detect_join_points, eliminate_dead_join_points, fuse_join_points,
    inline_small_join_points, run_join_point_ext, run_join_point_ext_decl,
    run_join_point_ext_default, validate_join_points, JpExtConfig, JpExtStats, JpValidationError,
};
use clean_kernel::Name;

// ── Helpers ────────────────────────────────────────────────────────────

fn var(n: u32) -> VarId {
    VarId(n)
}
fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}
fn var_arg(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}
fn ret_var(n: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(VarId(n)))
}
fn lit_u64(val: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(val))
}

fn vdecl(v: u32, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::UInt64,
        value,
        rest: Box::new(rest),
    }
}
fn jdecl(j: u32, params: Vec<(VarId, IRType)>, body: IRBody, rest: IRBody) -> IRBody {
    IRBody::JDecl {
        jp: jp(j),
        params,
        body: Box::new(body),
        rest: Box::new(rest),
    }
}
fn jmp(j: u32, args: Vec<IRArg>) -> IRBody {
    IRBody::Jmp { jp: jp(j), args }
}
fn inc(v: u32, n: u32, rest: IRBody) -> IRBody {
    IRBody::Inc {
        var: var(v),
        n,
        rest: Box::new(rest),
    }
}
fn dec(v: u32, rest: IRBody) -> IRBody {
    IRBody::Dec {
        var: var(v),
        rest: Box::new(rest),
    }
}
fn case(scrutinee: u32, alts: Vec<IRAlt>, default: Option<IRBody>) -> IRBody {
    IRBody::Case {
        scrutinee: var(scrutinee),
        alts,
        default: default.map(Box::new),
    }
}
fn alt(tag: u32, body: IRBody) -> IRAlt {
    IRAlt {
        ctor: CtorInfo {
            name: Name::from_string(&format!("C{}", tag)),
            tag,
            num_scalars: 0,
            num_objects: 0,
            field_types: vec![],
        },
        body: Box::new(body),
    }
}
fn mk_decl(name: &str, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt64,
        body,
    }
}

// ── Detection tests ────────────────────────────────────────────────────

#[test]
fn test_detect_no_join_points() {
    let body = ret_var(0);
    let info = detect_join_points(&body);
    assert!(info.is_empty());
}

#[test]
fn test_detect_single_join_point() {
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let info = detect_join_points(&body);
    assert_eq!(info.len(), 1);
    assert_eq!(info[0].jp, jp(0));
    assert_eq!(info[0].call_count, 1);
    assert!(!info[0].is_recursive);
}

#[test]
fn test_detect_multiple_join_points() {
    let body = jdecl(
        0,
        vec![],
        ret_var(1),
        jdecl(1, vec![], ret_var(2), jmp(0, vec![])),
    );
    let info = detect_join_points(&body);
    assert_eq!(info.len(), 2);
}

#[test]
fn test_detect_recursive_join_point() {
    // JP body jumps back to itself
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        jmp(0, vec![var_arg(1)]), // recursive
        jmp(0, vec![var_arg(2)]),
    );
    let info = detect_join_points(&body);
    assert_eq!(info.len(), 1);
    assert!(info[0].is_recursive);
}

#[test]
fn test_detect_unreferenced_join_point() {
    let body = jdecl(0, vec![], ret_var(1), ret_var(2));
    let info = detect_join_points(&body);
    assert_eq!(info[0].call_count, 0);
}

#[test]
fn test_detect_join_point_multiple_calls() {
    let body = jdecl(
        0,
        vec![],
        ret_var(1),
        case(
            0,
            vec![alt(0, jmp(0, vec![])), alt(1, jmp(0, vec![]))],
            None,
        ),
    );
    let info = detect_join_points(&body);
    assert_eq!(info[0].call_count, 2);
}

#[test]
fn test_detect_body_size() {
    // JP body: vdecl(1, ..., ret_var(1)) = 2 nodes
    let body = jdecl(0, vec![], vdecl(1, lit_u64(42), ret_var(1)), jmp(0, vec![]));
    let info = detect_join_points(&body);
    assert_eq!(info[0].body_size, 2);
}

// ── Parameter analysis tests ───────────────────────────────────────────

#[test]
fn test_analyze_params_all_used() {
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64), (var(2), IRType::UInt64)],
        inc(1, 1, ret_var(2)),
        jmp(0, vec![var_arg(3), var_arg(4)]),
    );
    let analysis = analyze_jp_params(&body);
    assert_eq!(analysis[&jp(0)], vec![true, true]);
}

#[test]
fn test_analyze_params_one_unused() {
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64), (var(2), IRType::UInt64)],
        ret_var(1), // only uses v1
        jmp(0, vec![var_arg(3), var_arg(4)]),
    );
    let analysis = analyze_jp_params(&body);
    assert_eq!(analysis[&jp(0)], vec![true, false]);
}

#[test]
fn test_analyze_params_none_used() {
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        ret_var(5), // uses v5, not v1
        jmp(0, vec![var_arg(3)]),
    );
    let analysis = analyze_jp_params(&body);
    assert_eq!(analysis[&jp(0)], vec![false]);
}

#[test]
fn test_analyze_params_empty_params() {
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let analysis = analyze_jp_params(&body);
    assert!(analysis[&jp(0)].is_empty());
}

// ── Inline tests ───────────────────────────────────────────────────────

#[test]
fn test_inline_single_use_small_jp() {
    // jdecl j0 [] { ret x1 }; jmp j0
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let (result, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(1)))));
}

#[test]
fn test_inline_with_param_substitution() {
    // jdecl j0 [(v1, u64)] { ret v1 }; jmp j0 [v2]
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        ret_var(1),
        jmp(0, vec![var_arg(2)]),
    );
    let (result, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 1);
    // After substitution: ret v2
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(2)))));
}

#[test]
fn test_inline_skips_multi_use_jp() {
    // JP called from two branches
    let body = jdecl(
        0,
        vec![],
        ret_var(1),
        case(
            0,
            vec![alt(0, jmp(0, vec![])), alt(1, jmp(0, vec![]))],
            None,
        ),
    );
    let (_, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 0);
}

#[test]
fn test_inline_skips_large_jp() {
    // JP body is larger than threshold
    let large_body = vdecl(
        1,
        lit_u64(1),
        vdecl(
            2,
            lit_u64(2),
            vdecl(
                3,
                lit_u64(3),
                vdecl(
                    4,
                    lit_u64(4),
                    vdecl(5, lit_u64(5), vdecl(6, lit_u64(6), ret_var(1))),
                ),
            ),
        ),
    );
    let body = jdecl(0, vec![], large_body, jmp(0, vec![]));
    let (_, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 0);
}

#[test]
fn test_inline_skips_recursive_jp() {
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        jmp(0, vec![var_arg(1)]),
        jmp(0, vec![var_arg(2)]),
    );
    let (_, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 0);
}

#[test]
fn test_inline_no_targets() {
    let body = ret_var(0);
    let (result, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 0);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(0)))));
}

// ── Fusion tests ───────────────────────────────────────────────────────

#[test]
fn test_fuse_forwarding_jp() {
    // jdecl j0 [] { jmp j1 [] }; jdecl j1 [] { ret x1 }; jmp j0 []
    let body = jdecl(
        0,
        vec![],
        jmp(1, vec![]),
        jdecl(1, vec![], ret_var(1), jmp(0, vec![])),
    );
    let (result, count) = fuse_join_points(&body);
    assert!(count >= 1);
    // j0 should be eliminated, jmp should go to j1
    let has_j0 = matches!(
        &result,
        IRBody::JDecl {
            jp: JoinPointId(0),
            ..
        }
    );
    assert!(!has_j0, "j0 should be removed after fusion");
}

#[test]
fn test_fuse_no_forwarding() {
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let (_, count) = fuse_join_points(&body);
    assert_eq!(count, 0);
}

#[test]
fn test_fuse_self_referential_not_fused() {
    // jdecl j0 [] { jmp j0 [] } — self-forwarding should not fuse
    let body = jdecl(0, vec![], jmp(0, vec![]), ret_var(1));
    let (_, count) = fuse_join_points(&body);
    assert_eq!(count, 0);
}

// ── Dead elimination tests ─────────────────────────────────────────────

#[test]
fn test_eliminate_dead_jp() {
    let body = jdecl(0, vec![], ret_var(1), ret_var(2));
    let (result, count) = eliminate_dead_join_points(&body);
    assert_eq!(count, 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(2)))));
}

#[test]
fn test_eliminate_keeps_live_jp() {
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let (result, count) = eliminate_dead_join_points(&body);
    assert_eq!(count, 0);
    assert!(matches!(result, IRBody::JDecl { .. }));
}

#[test]
fn test_eliminate_multiple_dead() {
    let body = jdecl(
        0,
        vec![],
        ret_var(1),
        jdecl(1, vec![], ret_var(2), ret_var(3)),
    );
    let (result, count) = eliminate_dead_join_points(&body);
    assert_eq!(count, 2);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(3)))));
}

#[test]
fn test_eliminate_dead_nested_in_case() {
    let jp_body = jdecl(0, vec![], ret_var(1), ret_var(2));
    let body = case(0, vec![alt(0, jp_body)], None);
    let (result, count) = eliminate_dead_join_points(&body);
    assert_eq!(count, 1);
}

// ── Validation tests ───────────────────────────────────────────────────

#[test]
fn test_validate_valid_body() {
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        ret_var(1),
        jmp(0, vec![var_arg(2)]),
    );
    assert!(validate_join_points(&body).is_ok());
}

#[test]
fn test_validate_undefined_target() {
    let body = jmp(99, vec![]);
    assert_eq!(
        validate_join_points(&body),
        Err(JpValidationError::UndefinedTarget { jp_id: 99 })
    );
}

#[test]
fn test_validate_arity_mismatch() {
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        ret_var(1),
        jmp(0, vec![var_arg(2), var_arg(3)]),
    ); // expects 1, gets 2
    assert_eq!(
        validate_join_points(&body),
        Err(JpValidationError::ArityMismatch {
            jp_id: 0,
            expected: 1,
            actual: 2
        })
    );
}

#[test]
fn test_validate_no_join_points() {
    let body = ret_var(0);
    assert!(validate_join_points(&body).is_ok());
}

#[test]
fn test_validate_nested_scoped() {
    // j0 scope contains j1
    let body = jdecl(
        0,
        vec![],
        jdecl(1, vec![], ret_var(1), jmp(1, vec![])),
        jmp(0, vec![]),
    );
    assert!(validate_join_points(&body).is_ok());
}

// ── Stats tests ────────────────────────────────────────────────────────

#[test]
fn test_stats_total() {
    let stats = JpExtStats {
        join_points_detected: 5,
        join_points_inlined: 2,
        join_points_fused: 1,
        join_points_eliminated: 3,
        join_points_hoisted: 1,
        recursive_join_points: 1,
        iterations: 2,
    };
    assert_eq!(stats.total(), 7);
}

#[test]
fn test_stats_default_zero() {
    let stats = JpExtStats::default();
    assert_eq!(stats.total(), 0);
    assert_eq!(stats.iterations, 0);
}

// ── Orchestration tests ────────────────────────────────────────────────

#[test]
fn test_run_disabled() {
    let body = jdecl(0, vec![], ret_var(1), ret_var(2));
    let config = JpExtConfig {
        enabled: false,
        ..Default::default()
    };
    let (_, stats) = run_join_point_ext(&body, &config);
    assert_eq!(stats.total(), 0);
}

#[test]
fn test_run_default_eliminates_dead() {
    let body = jdecl(0, vec![], ret_var(1), ret_var(2));
    let (result, stats) = run_join_point_ext_default(&body);
    assert!(stats.join_points_eliminated >= 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(2)))));
}

#[test]
fn test_run_inlines_then_eliminates() {
    // j0 is small (1 node), called once => inlined, then dead decl eliminated
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let (result, stats) = run_join_point_ext_default(&body);
    assert!(stats.join_points_inlined >= 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(1)))));
}

#[test]
fn test_run_decl() {
    let decl = mk_decl("foo", jdecl(0, vec![], ret_var(1), ret_var(2)));
    let config = JpExtConfig::default();
    let (new_decl, stats) = run_join_point_ext_decl(&decl, &config);
    assert!(stats.join_points_eliminated >= 1);
    assert!(matches!(new_decl.body, IRBody::Ret(IRArg::Var(VarId(2)))));
    assert_eq!(new_decl.name, Name::from_string("foo"));
}

#[test]
fn test_run_fixpoint_cascading() {
    // j0 forwards to j1 (fusion), then j0 becomes dead (elimination)
    let body = jdecl(
        0,
        vec![],
        jmp(1, vec![]),
        jdecl(1, vec![], ret_var(1), jmp(0, vec![])),
    );
    let (_, stats) = run_join_point_ext_default(&body);
    assert!(stats.total() >= 2, "expect at least fusion + elimination");
}

#[test]
fn test_run_max_iterations_respected() {
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let config = JpExtConfig {
        max_iterations: 1,
        ..Default::default()
    };
    let (_, stats) = run_join_point_ext(&body, &config);
    assert!(stats.iterations <= 1);
}

#[test]
fn test_run_no_join_points_single_iteration() {
    let body = ret_var(0);
    let (_, stats) = run_join_point_ext_default(&body);
    assert_eq!(stats.join_points_detected, 0);
    assert_eq!(stats.iterations, 1);
}

// ── Edge case tests ────────────────────────────────────────────────────

#[test]
fn test_inline_preserves_inc_dec() {
    // jdecl j0 [] { inc v1 1; ret v1 }; jmp j0
    let jp_body = inc(1, 1, ret_var(1));
    let body = jdecl(0, vec![], jp_body, jmp(0, vec![]));
    let (result, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 1);
    assert!(matches!(
        result,
        IRBody::Inc {
            var: VarId(1),
            n: 1,
            ..
        }
    ));
}

#[test]
fn test_inline_with_erased_arg() {
    let body = jdecl(
        0,
        vec![(var(1), IRType::Erased)],
        IRBody::Ret(IRArg::Erased),
        jmp(0, vec![IRArg::Erased]),
    );
    let (result, count) = inline_small_join_points(&body, 5);
    assert_eq!(count, 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Erased)));
}

#[test]
fn test_validate_after_inline() {
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let (result, _) = inline_small_join_points(&body, 5);
    assert!(validate_join_points(&result).is_ok());
}

#[test]
fn test_validate_after_dead_elimination() {
    let body = jdecl(0, vec![], ret_var(1), ret_var(2));
    let (result, _) = eliminate_dead_join_points(&body);
    assert!(validate_join_points(&result).is_ok());
}

#[test]
fn test_validate_after_full_pipeline() {
    let body = jdecl(
        0,
        vec![],
        jmp(1, vec![]),
        jdecl(1, vec![], ret_var(1), jmp(0, vec![])),
    );
    let (result, _) = run_join_point_ext_default(&body);
    assert!(validate_join_points(&result).is_ok());
}

#[test]
fn test_detect_jp_in_case_branch() {
    let alt_body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let body = case(0, vec![alt(0, alt_body)], None);
    let info = detect_join_points(&body);
    assert_eq!(info.len(), 1);
}

#[test]
fn test_detect_jp_in_default_branch() {
    let def_body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let body = case(0, vec![], Some(def_body));
    let info = detect_join_points(&body);
    assert_eq!(info.len(), 1);
}

#[test]
fn test_fuse_with_args() {
    // j0 forwards to j1 with args
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        jmp(1, vec![var_arg(1)]),
        jdecl(
            1,
            vec![(var(2), IRType::UInt64)],
            ret_var(2),
            jmp(0, vec![var_arg(3)]),
        ),
    );
    let (_, count) = fuse_join_points(&body);
    assert!(count >= 1);
}

#[test]
fn test_inline_threshold_boundary() {
    // JP body exactly at threshold (1 node = ret)
    let body = jdecl(0, vec![], ret_var(1), jmp(0, vec![]));
    let (_, count) = inline_small_join_points(&body, 1);
    assert_eq!(count, 1);
    // Now below threshold
    let body2 = jdecl(0, vec![], vdecl(1, lit_u64(1), ret_var(1)), jmp(0, vec![]));
    let (_, count2) = inline_small_join_points(&body2, 1);
    assert_eq!(count2, 0); // body_size=2, threshold=1
}

#[test]
fn test_config_fuse_disabled() {
    let body = jdecl(
        0,
        vec![],
        jmp(1, vec![]),
        jdecl(1, vec![], ret_var(1), jmp(0, vec![])),
    );
    let config = JpExtConfig {
        fuse_enabled: false,
        ..Default::default()
    };
    let (_, stats) = run_join_point_ext(&body, &config);
    assert_eq!(stats.join_points_fused, 0);
}

#[test]
fn test_unreachable_in_jp_body() {
    let body = jdecl(0, vec![], IRBody::Unreachable, jmp(0, vec![]));
    let info = detect_join_points(&body);
    assert_eq!(info[0].body_size, 1);
    assert!(validate_join_points(&body).is_ok());
}
