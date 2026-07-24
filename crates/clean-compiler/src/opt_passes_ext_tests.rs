// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended optimization passes.
//!
//! Part of #3083 - Compiler extensibility.

use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use crate::opt_passes_ext::{
    algebraic_simplify_expr, compute_inline_cost, compute_ir_size, cse_body, dead_store_eliminate,
    default_pass_order, detect_tail_calls, dump_ir_snapshot, find_hoistable_exprs,
    merge_pipeline_results, run_optimization_pipeline, run_optimization_pipeline_default,
    should_inline, should_run_pass, strength_reduce_expr, validate_pass_order, ExtOptPass,
    OptPassExtConfig, PassPipelineResult, PassStatistics,
};
use crate::pass_manager::Phase;
use clean_kernel::Name;

// --- Test helpers ---

fn make_decl(name: &str, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![],
        return_type: IRType::Object,
        body,
    }
}

fn ret_body() -> IRBody {
    IRBody::Ret(IRArg::Var(VarId(0)))
}

fn vdecl_ret_body() -> IRBody {
    IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    }
}

fn complex_body() -> IRBody {
    let ctor = CtorInfo {
        name: Name::from_string("Pair.mk"),
        tag: 0,
        num_scalars: 0,
        num_objects: 2,
        field_types: vec![IRType::Object, IRType::Object],
    };
    IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor,
            args: vec![IRArg::Var(VarId(0)), IRArg::Erased],
        },
        rest: Box::new(IRBody::Inc {
            var: VarId(1),
            n: 1,
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    }
}

fn make_decl_with_params(name: &str, n: usize) -> IRDecl {
    let params: Vec<(VarId, IRType)> = (0..n).map(|i| (VarId(i as u32), IRType::Object)).collect();
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: IRType::Object,
        body: vdecl_ret_body(),
    }
}

// --- compute_ir_size ---

#[test]
fn test_compute_ir_size_empty() {
    assert_eq!(compute_ir_size(&[]), 0);
}

#[test]
fn test_compute_ir_size_single_ret() {
    assert_eq!(compute_ir_size(&[make_decl("f", ret_body())]), 1);
}

#[test]
fn test_compute_ir_size_vdecl_ret() {
    assert_eq!(compute_ir_size(&[make_decl("f", vdecl_ret_body())]), 3);
}

#[test]
fn test_compute_ir_size_complex() {
    assert_eq!(compute_ir_size(&[make_decl("f", complex_body())]), 6);
}

#[test]
fn test_compute_ir_size_multiple() {
    let decls = vec![make_decl("f", ret_body()), make_decl("g", vdecl_ret_body())];
    assert_eq!(compute_ir_size(&decls), 4);
}

#[test]
fn test_compute_ir_size_case() {
    let ctor = CtorInfo {
        name: Name::from_string("B.t"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor,
            body: Box::new(ret_body()),
        }],
        default: Some(Box::new(IRBody::Unreachable)),
    };
    assert_eq!(compute_ir_size(&[make_decl("f", body)]), 3);
}

#[test]
fn test_compute_ir_size_dec() {
    let body = IRBody::Dec {
        var: VarId(0),
        rest: Box::new(ret_body()),
    };
    assert_eq!(compute_ir_size(&[make_decl("f", body)]), 2);
}

#[test]
fn test_compute_ir_size_jmp() {
    let body = IRBody::Jmp {
        jp: crate::ir::JoinPointId(0),
        args: vec![IRArg::Var(VarId(0))],
    };
    assert_eq!(compute_ir_size(&[make_decl("f", body)]), 1);
}

#[test]
fn test_compute_ir_size_unreachable() {
    assert_eq!(compute_ir_size(&[make_decl("f", IRBody::Unreachable)]), 1);
}

#[test]
fn test_compute_ir_size_set() {
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(ret_body()),
    };
    assert_eq!(compute_ir_size(&[make_decl("f", body)]), 2);
}

#[test]
fn test_compute_ir_size_jdecl() {
    let body = IRBody::JDecl {
        jp: crate::ir::JoinPointId(0),
        params: vec![(VarId(0), IRType::Object)],
        body: Box::new(ret_body()),
        rest: Box::new(ret_body()),
    };
    assert_eq!(compute_ir_size(&[make_decl("f", body)]), 3);
}

#[test]
fn test_compute_ir_size_apply() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: FnId(Name::from_string("g")),
            args: vec![IRArg::Var(VarId(1)), IRArg::Var(VarId(2))],
        },
        rest: Box::new(ret_body()),
    };
    assert_eq!(compute_ir_size(&[make_decl("f", body)]), 5);
}

// --- validate_pass_order ---

#[test]
fn test_validate_empty() {
    assert!(validate_pass_order(&[]).is_ok());
}

#[test]
fn test_validate_single() {
    assert!(validate_pass_order(&[ExtOptPass::new("a", Phase::Base, 10, false)]).is_ok());
}

#[test]
fn test_validate_correct() {
    let passes = vec![
        ExtOptPass::new("a", Phase::Base, 10, false),
        ExtOptPass::new("b", Phase::Mono, 10, false),
        ExtOptPass::new("c", Phase::Impure, 10, true),
    ];
    assert!(validate_pass_order(&passes).is_ok());
}

#[test]
fn test_validate_same_phase() {
    let passes = vec![
        ExtOptPass::new("a", Phase::Mono, 10, false),
        ExtOptPass::new("b", Phase::Mono, 20, false),
    ];
    assert!(validate_pass_order(&passes).is_ok());
}

#[test]
fn test_validate_backward_error() {
    let passes = vec![
        ExtOptPass::new("rc", Phase::Impure, 10, true),
        ExtOptPass::new("dce", Phase::Base, 10, false),
    ];
    let err = validate_pass_order(&passes).unwrap_err();
    assert_eq!(err.len(), 1);
    assert!(err[0].contains("dce"));
}

#[test]
fn test_validate_multiple_errors() {
    let passes = vec![
        ExtOptPass::new("a", Phase::Impure, 10, false),
        ExtOptPass::new("b", Phase::Mono, 20, false),
        ExtOptPass::new("c", Phase::Base, 30, false),
    ];
    assert_eq!(validate_pass_order(&passes).unwrap_err().len(), 2);
}

#[test]
fn test_validate_default_order() {
    validate_pass_order(&default_pass_order()).expect("default order valid");
}

// --- should_run_pass ---

#[test]
fn test_should_run_no_skips() {
    let p = ExtOptPass::new("dce", Phase::Base, 10, false);
    assert!(should_run_pass(&p, &OptPassExtConfig::default()));
}

#[test]
fn test_should_run_skipped() {
    let p = ExtOptPass::new("dce", Phase::Base, 10, false);
    let c = OptPassExtConfig {
        skip_passes: vec!["dce".to_owned()],
        ..Default::default()
    };
    assert!(!should_run_pass(&p, &c));
}

#[test]
fn test_should_run_required_not_skippable() {
    let p = ExtOptPass::new("rc", Phase::Impure, 10, true);
    let c = OptPassExtConfig {
        skip_passes: vec!["rc".to_owned()],
        ..Default::default()
    };
    assert!(should_run_pass(&p, &c));
}

#[test]
fn test_should_run_different_name() {
    let p = ExtOptPass::new("cse", Phase::Base, 30, false);
    let c = OptPassExtConfig {
        skip_passes: vec!["dce".to_owned()],
        ..Default::default()
    };
    assert!(should_run_pass(&p, &c));
}

// --- dump_ir_snapshot ---

#[test]
fn test_snapshot_empty() {
    let s = dump_ir_snapshot(&[], "dce");
    assert!(s.contains("After pass: dce") && s.contains("0 decl(s)"));
}

#[test]
fn test_snapshot_one_decl() {
    let s = dump_ir_snapshot(&[make_decl("foo", ret_body())], "simp");
    assert!(s.contains("foo") && s.contains("0 params") && s.contains("1 IR nodes"));
}

#[test]
fn test_snapshot_with_params() {
    let s = dump_ir_snapshot(&[make_decl_with_params("bar", 3)], "inline");
    assert!(s.contains("3 params"));
}

// --- merge_pipeline_results ---

#[test]
fn test_merge_empty() {
    let m = merge_pipeline_results(&[]);
    assert_eq!(m.total_duration_us, 0);
}

#[test]
fn test_merge_two() {
    let r1 = PassPipelineResult {
        pass_stats: vec![(
            "a".to_owned(),
            PassStatistics {
                cse_eliminated: 1,
                ..Default::default()
            },
        )],
        total_duration_us: 100,
        total_decls_modified: 1,
        passes_skipped: 0,
    };
    let r2 = PassPipelineResult {
        pass_stats: vec![("b".to_owned(), PassStatistics::default())],
        total_duration_us: 200,
        total_decls_modified: 2,
        passes_skipped: 1,
    };
    let m = merge_pipeline_results(&[r1, r2]);
    assert_eq!(m.total_duration_us, 300);
    assert_eq!(m.total_decls_modified, 3);
    assert_eq!(m.passes_skipped, 1);
    assert_eq!(m.pass_stats.len(), 2);
}

// --- default_pass_order ---

#[test]
fn test_default_nonempty() {
    assert!(!default_pass_order().is_empty());
}

#[test]
fn test_default_has_all_phases() {
    let p = default_pass_order();
    assert!(p.iter().any(|x| x.phase == Phase::Base));
    assert!(p.iter().any(|x| x.phase == Phase::Mono));
    assert!(p.iter().any(|x| x.phase == Phase::Impure));
}

#[test]
fn test_default_has_required() {
    assert!(default_pass_order().iter().any(|p| p.is_required));
}

#[test]
fn test_default_names_unique() {
    let p = default_pass_order();
    let mut names: Vec<&str> = p.iter().map(|x| x.name.as_str()).collect();
    let n = names.len();
    names.sort();
    names.dedup();
    assert_eq!(names.len(), n);
}

#[test]
fn test_default_has_new_passes() {
    let names: Vec<String> = default_pass_order()
        .iter()
        .map(|p| p.name.clone())
        .collect();
    assert!(names.contains(&"licm".to_owned()));
    assert!(names.contains(&"ir_cse".to_owned()));
    assert!(names.contains(&"dead_store_elim".to_owned()));
    assert!(names.contains(&"tail_call_detect".to_owned()));
    assert!(names.contains(&"algebraic_simp".to_owned()));
    assert!(names.contains(&"strength_reduce".to_owned()));
}

// --- CSE ---

#[test]
fn test_cse_no_duplicates() {
    let body = vdecl_ret_body();
    let (_, n) = cse_body(&body);
    assert_eq!(n, 0);
}

#[test]
fn test_cse_duplicate_literals() {
    // let v0 = 42; let v1 = 42; ret v1
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    };
    let (new_body, n) = cse_body(&body);
    assert_eq!(n, 1);
    // v1 should be replaced by v0 in the return
    if let IRBody::VDecl { rest, .. } = &new_body {
        if let IRBody::Ret(IRArg::Var(v)) = rest.as_ref() {
            assert_eq!(*v, VarId(0));
        } else {
            panic!("expected Ret after CSE");
        }
    } else {
        panic!("expected VDecl");
    }
}

#[test]
fn test_cse_different_literals_not_eliminated() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(99)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    };
    let (_, n) = cse_body(&body);
    assert_eq!(n, 0);
}

#[test]
fn test_cse_float_not_keyed() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Float64,
        value: IRExpr::Lit(IRLiteral::Float64(1.0)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Float64,
            value: IRExpr::Lit(IRLiteral::Float64(1.0)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    };
    let (_, n) = cse_body(&body);
    assert_eq!(n, 0, "floats should not be CSE'd");
}

#[test]
fn test_cse_string_dedup() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::String("hello".to_owned()),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::String("hello".to_owned()),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    };
    let (_, n) = cse_body(&body);
    assert_eq!(n, 1);
}

// --- Dead store elimination ---

#[test]
fn test_dse_no_dead_stores() {
    // Set v0[0] = v1; ret v0  -- v0 is read
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let (_, n) = dead_store_eliminate(&body);
    assert_eq!(n, 0);
}

#[test]
fn test_dse_dead_set_removed() {
    // Set v0[0] = v1; ret v2  -- v0 is NOT read
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
    };
    let (new_body, n) = dead_store_eliminate(&body);
    assert_eq!(n, 1);
    assert!(matches!(new_body, IRBody::Ret(_)));
}

#[test]
fn test_dse_dead_uset_removed() {
    let body = IRBody::USet {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
    };
    let (_, n) = dead_store_eliminate(&body);
    assert_eq!(n, 1);
}

#[test]
fn test_dse_chain() {
    // Set v0[0] = v1; Set v3[0] = v4; ret v5  -- both dead
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::Set {
            var: VarId(3),
            idx: 0,
            value: VarId(4),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(5)))),
        }),
    };
    let (_, n) = dead_store_eliminate(&body);
    assert_eq!(n, 2);
}

// --- Tail call detection ---

#[test]
fn test_tail_call_simple_ret() {
    let decl = make_decl("f", ret_body());
    assert!(!detect_tail_calls(&decl));
}

#[test]
fn test_tail_call_self_apply() {
    // let v1 = f(v0); ret v1
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: FnId(Name::from_string("f")),
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = make_decl("f", body);
    assert!(detect_tail_calls(&decl));
}

#[test]
fn test_tail_call_not_self() {
    // let v1 = g(v0); ret v1  -- calls g, not f
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: FnId(Name::from_string("g")),
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = make_decl("f", body);
    assert!(!detect_tail_calls(&decl));
}

// --- LICM ---

#[test]
fn test_licm_empty() {
    assert!(find_hoistable_exprs(&ret_body()).is_empty());
}

#[test]
fn test_licm_hoistable_proj() {
    // let v1 = proj(v0, 0); ret v1
    // v0 is a parameter (not locally defined), so v1 is hoistable
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Var(VarId(0)),
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let h = find_hoistable_exprs(&body);
    assert_eq!(h.len(), 1);
    assert_eq!(h[0], VarId(1));
}

#[test]
fn test_licm_not_hoistable_depends_on_local() {
    // let v1 = Lit(42); let v2 = Proj(v1, 0); ret v2
    // v2 depends on v1 which is locally defined
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: IRArg::Var(VarId(1)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        }),
    };
    let h = find_hoistable_exprs(&body);
    // v1 has no uses (literal), so not hoistable. v2 depends on v1, not hoistable.
    assert!(h.is_empty());
}

#[test]
fn test_licm_literal_not_hoistable() {
    // Literals have no variable uses, so they are not flagged as hoistable.
    let h = find_hoistable_exprs(&vdecl_ret_body());
    assert!(h.is_empty());
}

// --- Inlining heuristics ---

#[test]
fn test_inline_cost_small_fn() {
    let decl = make_decl("f", ret_body()); // 1 node
    let config = OptPassExtConfig::default();
    let cost = compute_inline_cost(&decl, &config);
    assert_eq!(cost.body_size, 1);
    assert!(!cost.is_recursive);
    assert!(should_inline(&cost, &config));
}

#[test]
fn test_inline_cost_recursive_not_inlined() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: FnId(Name::from_string("f")),
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = make_decl("f", body);
    let config = OptPassExtConfig::default();
    let cost = compute_inline_cost(&decl, &config);
    assert!(cost.is_recursive);
    assert!(!should_inline(&cost, &config));
}

#[test]
fn test_inline_cost_large_fn_not_inlined() {
    // Make a decl whose body is large
    let mut body: IRBody = ret_body();
    for i in 0..25 {
        body = IRBody::VDecl {
            var: VarId(100 + i),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(i as u64)),
            rest: Box::new(body),
        };
    }
    let decl = make_decl("big", body);
    let config = OptPassExtConfig {
        inline_threshold: 20,
        ..Default::default()
    };
    let cost = compute_inline_cost(&decl, &config);
    assert!(cost.body_size > 20);
    assert!(!should_inline(&cost, &config));
}

#[test]
fn test_inline_cost_params_increase_score() {
    let d1 = make_decl("f", ret_body());
    let d2 = make_decl_with_params("g", 5);
    let config = OptPassExtConfig::default();
    let c1 = compute_inline_cost(&d1, &config);
    let c2 = compute_inline_cost(&d2, &config);
    assert!(c2.score > c1.score, "more params should increase score");
}

// --- Algebraic simplification ---

#[test]
fn test_algebraic_simp_bool() {
    let (result, _) = algebraic_simplify_expr(&IRExpr::Lit(IRLiteral::Bool(true)));
    if let IRExpr::Lit(IRLiteral::Bool(v)) = result {
        assert!(v);
    } else {
        panic!("expected bool");
    }
}

#[test]
fn test_algebraic_simp_non_bool_passthrough() {
    let expr = IRExpr::Lit(IRLiteral::UInt64(42));
    let (result, _) = algebraic_simplify_expr(&expr);
    assert!(matches!(result, IRExpr::Lit(IRLiteral::UInt64(42))));
}

// --- Strength reduction ---

#[test]
fn test_strength_reduce_passthrough() {
    let expr = IRExpr::Lit(IRLiteral::UInt64(7));
    let (result, changed) = strength_reduce_expr(&expr);
    assert!(!changed);
    assert!(matches!(result, IRExpr::Lit(IRLiteral::UInt64(7))));
}

// --- Statistics ---

#[test]
fn test_statistics_total() {
    let s = PassStatistics {
        exprs_hoisted: 1,
        cse_eliminated: 2,
        strength_reductions: 3,
        algebraic_simplifications: 4,
        dead_stores_removed: 5,
        tail_calls_detected: 6,
        inline_candidates: 7,
        duration_us: 100,
    };
    assert_eq!(s.total_transforms(), 1 + 2 + 3 + 4 + 5);
}

#[test]
fn test_statistics_default_zero() {
    let s = PassStatistics::default();
    assert_eq!(s.total_transforms(), 0);
    assert_eq!(s.tail_calls_detected, 0);
    assert_eq!(s.inline_candidates, 0);
}

// --- Pipeline ---

#[test]
fn test_pipeline_empty_decls() {
    let mut decls: Vec<IRDecl> = vec![];
    let r = run_optimization_pipeline(
        &mut decls,
        &default_pass_order(),
        &OptPassExtConfig::default(),
    );
    assert_eq!(r.total_decls_modified, 0);
}

#[test]
fn test_pipeline_default() {
    let mut decls = vec![make_decl("f", vdecl_ret_body())];
    let r = run_optimization_pipeline_default(&mut decls);
    assert_eq!(decls.len(), 1);
    assert_eq!(r.passes_skipped, 0);
}

#[test]
fn test_pipeline_profiling() {
    let mut decls = vec![make_decl("f", vdecl_ret_body())];
    let config = OptPassExtConfig {
        enable_profiling: true,
        ..Default::default()
    };
    let r = run_optimization_pipeline(&mut decls, &default_pass_order(), &config);
    assert!(!r.pass_stats.is_empty());
    for (name, stats) in &r.pass_stats {
        assert!(!name.is_empty());
        let _ = stats.duration_us; // Just check it's accessible
    }
}

#[test]
fn test_pipeline_skip_pass() {
    let mut decls = vec![make_decl("f", ret_body())];
    let passes = vec![
        ExtOptPass::new("a", Phase::Base, 10, false),
        ExtOptPass::new("b", Phase::Base, 20, false),
    ];
    let config = OptPassExtConfig {
        skip_passes: vec!["a".to_owned()],
        ..Default::default()
    };
    let r = run_optimization_pipeline(&mut decls, &passes, &config);
    assert!(r.passes_skipped >= 1);
}

#[test]
fn test_pipeline_skip_required_still_runs() {
    let mut decls = vec![make_decl("f", ret_body())];
    let passes = vec![ExtOptPass::new("rc", Phase::Impure, 10, true)];
    let config = OptPassExtConfig {
        enable_profiling: true,
        skip_passes: vec!["rc".to_owned()],
        ..Default::default()
    };
    let r = run_optimization_pipeline(&mut decls, &passes, &config);
    assert_eq!(r.passes_skipped, 0);
    assert!(!r.pass_stats.is_empty());
}

#[test]
fn test_pipeline_cse_eliminates() {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    };
    let mut decls = vec![make_decl("f", body)];
    let passes = vec![ExtOptPass::new("ir_cse", Phase::Base, 20, false)];
    let config = OptPassExtConfig {
        enable_profiling: true,
        ..Default::default()
    };
    let r = run_optimization_pipeline(&mut decls, &passes, &config);
    assert!(r.total_decls_modified > 0);
}

#[test]
fn test_pipeline_dse_removes() {
    let body = IRBody::Set {
        var: VarId(0),
        idx: 0,
        value: VarId(1),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
    };
    let mut decls = vec![make_decl("f", body)];
    let passes = vec![ExtOptPass::new("dead_store_elim", Phase::Base, 30, false)];
    let config = OptPassExtConfig {
        enable_profiling: true,
        ..Default::default()
    };
    let r = run_optimization_pipeline(&mut decls, &passes, &config);
    assert!(r.total_decls_modified > 0);
}

#[test]
fn test_pipeline_dump_no_panic() {
    let mut decls = vec![make_decl("f", complex_body())];
    let config = OptPassExtConfig {
        dump_ir_after_pass: true,
        ..Default::default()
    };
    let _ = run_optimization_pipeline(&mut decls, &default_pass_order(), &config);
}

#[test]
fn test_pipeline_multiple_decls() {
    let mut decls = vec![
        make_decl("a", ret_body()),
        make_decl("b", vdecl_ret_body()),
        make_decl("c", complex_body()),
    ];
    let r = run_optimization_pipeline_default(&mut decls);
    assert_eq!(decls.len(), 3);
    let _ = r.total_duration_us;
}

// --- ExtOptPass construction ---

#[test]
fn test_ext_opt_pass_new() {
    let p = ExtOptPass::new("my_pass", Phase::Mono, 42, true);
    assert_eq!(p.name, "my_pass");
    assert_eq!(p.phase, Phase::Mono);
    assert_eq!(p.priority, 42);
    assert!(p.is_required);
}

// --- Config ---

#[test]
fn test_config_default() {
    let c = OptPassExtConfig::default();
    assert!(!c.enable_profiling);
    assert!(!c.dump_ir_after_pass);
    assert_eq!(c.max_pass_iterations, 3);
    assert!(c.skip_passes.is_empty());
    assert_eq!(c.inline_threshold, 20);
}

// --- Error type ---

#[test]
fn test_error_display() {
    let e = crate::opt_passes_ext::OptPassExtError::PassOrderViolation("test".to_owned());
    assert!(format!("{}", e).contains("test"));
    let e2 = crate::opt_passes_ext::OptPassExtError::InvalidConfig("bad".to_owned());
    assert!(format!("{}", e2).contains("bad"));
}
