// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended boxing analysis module.

use crate::boxing_ext::*;
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

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

// ---------------------------------------------------------------------------
// Boxing insertion analysis
// ---------------------------------------------------------------------------

#[test]
fn test_analyze_sites_box_scalar() {
    let body = vdecl(1, IRType::Object, box_expr(IRType::UInt64, 0), ret_var(1));
    let decl = mk_decl("f", vec![(VarId(0), IRType::UInt64)], IRType::Object, body);
    let sites = analyze_boxing_sites(&decl);
    assert_eq!(sites.len(), 1);
    assert_eq!(
        sites[0],
        BoxingSite::BoxScalar {
            var: VarId(1),
            ty: IRType::UInt64
        }
    );
}

#[test]
fn test_analyze_sites_unbox_object() {
    let body = vdecl(1, IRType::UInt64, unbox_expr(IRType::UInt64, 0), ret_var(1));
    let decl = mk_decl("g", vec![(VarId(0), IRType::Object)], IRType::UInt64, body);
    let sites = analyze_boxing_sites(&decl);
    assert_eq!(sites.len(), 1);
    assert_eq!(
        sites[0],
        BoxingSite::UnboxObject {
            var: VarId(1),
            target_ty: IRType::UInt64
        }
    );
}

#[test]
fn test_analyze_sites_no_boxing() {
    let body = ret_var(0);
    let decl = mk_decl("h", vec![(VarId(0), IRType::Object)], IRType::Object, body);
    assert!(analyze_boxing_sites(&decl).is_empty());
}

#[test]
fn test_analyze_sites_multiple() {
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt32, unbox_expr(IRType::UInt32, 1), ret_var(2)),
    );
    let decl = mk_decl("m", vec![(VarId(0), IRType::UInt64)], IRType::UInt32, body);
    assert_eq!(analyze_boxing_sites(&decl).len(), 2);
}

// ---------------------------------------------------------------------------
// Cross-function propagation
// ---------------------------------------------------------------------------

#[test]
fn test_build_boxing_summaries_scalar_params() {
    let decl = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    let sums = build_boxing_summaries(&[decl]);
    assert_eq!(sums.len(), 1);
    assert_eq!(sums[0].boxed_params, vec![false]);
    assert!(!sums[0].returns_boxed);
}

#[test]
fn test_build_boxing_summaries_object_params() {
    let decl = mk_decl(
        "g",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_var(0),
    );
    let sums = build_boxing_summaries(&[decl]);
    assert_eq!(sums[0].boxed_params, vec![true]);
    assert!(sums[0].returns_boxed);
}

#[test]
fn test_propagate_boxing_marks_caller_param() {
    // callee expects Object param; caller passes its own UInt64 param directly.
    let callee = mk_decl(
        "callee",
        vec![(VarId(0), IRType::Object)],
        IRType::Object,
        ret_var(0),
    );
    let caller_body = vdecl(
        1,
        IRType::Object,
        IRExpr::Apply {
            fn_id: FnId(Name::from_string("callee")),
            args: vec![IRArg::Var(VarId(0))],
        },
        ret_var(1),
    );
    let caller = mk_decl(
        "caller",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        caller_body,
    );
    let decls = vec![callee, caller];
    let sums = build_boxing_summaries(&decls);
    let propagated = propagate_boxing(&decls, &sums);
    // caller's param 0 should now be marked boxed
    let caller_sum = propagated
        .iter()
        .find(|s| s.fn_id.0 == Name::from_string("caller"))
        .unwrap();
    assert!(caller_sum.boxed_params[0]);
}

#[test]
fn test_propagate_boxing_no_change_when_types_match() {
    let f = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    let decls = vec![f];
    let sums = build_boxing_summaries(&decls);
    let propagated = propagate_boxing(&decls, &sums);
    assert!(!propagated[0].boxed_params[0]);
}

// ---------------------------------------------------------------------------
// Polymorphic boxing
// ---------------------------------------------------------------------------

#[test]
fn test_polymorphic_boxing_type_erased() {
    assert_eq!(polymorphic_boxing_type(&IRType::Erased), IRType::Object);
}

#[test]
fn test_polymorphic_boxing_type_scalar() {
    assert_eq!(polymorphic_boxing_type(&IRType::UInt64), IRType::Object);
    assert_eq!(polymorphic_boxing_type(&IRType::Bool), IRType::Object);
}

#[test]
fn test_polymorphic_boxing_type_object() {
    assert_eq!(polymorphic_boxing_type(&IRType::Object), IRType::Object);
}

#[test]
fn test_polymorphic_boxing_type_void() {
    assert_eq!(polymorphic_boxing_type(&IRType::Void), IRType::Void);
}

#[test]
fn test_has_polymorphic_params_true() {
    let d = mk_decl(
        "f",
        vec![(VarId(0), IRType::Erased)],
        IRType::Object,
        ret_erased(),
    );
    assert!(has_polymorphic_params(&d));
}

#[test]
fn test_has_polymorphic_params_false() {
    let d = mk_decl(
        "f",
        vec![(VarId(0), IRType::UInt64)],
        IRType::UInt64,
        ret_var(0),
    );
    assert!(!has_polymorphic_params(&d));
}

// ---------------------------------------------------------------------------
// Cost analysis
// ---------------------------------------------------------------------------

#[test]
fn test_cost_no_boxing() {
    let d = mk_decl("f", vec![], IRType::Object, ret_erased());
    let cost = estimate_boxing_cost(&d);
    assert_eq!(cost.box_count, 0);
    assert_eq!(cost.unbox_count, 0);
    assert_eq!(cost.total_overhead(), 0);
}

#[test]
fn test_cost_single_box() {
    let body = vdecl(1, IRType::Object, box_expr(IRType::UInt64, 0), ret_var(1));
    let d = mk_decl("f", vec![(VarId(0), IRType::UInt64)], IRType::Object, body);
    let cost = estimate_boxing_cost(&d);
    assert_eq!(cost.box_count, 1);
    assert_eq!(cost.unbox_count, 0);
    assert_eq!(cost.total_overhead(), 2);
}

#[test]
fn test_cost_box_and_unbox() {
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt64, unbox_expr(IRType::UInt64, 1), ret_var(2)),
    );
    let d = mk_decl("f", vec![(VarId(0), IRType::UInt64)], IRType::UInt64, body);
    let cost = estimate_boxing_cost(&d);
    assert_eq!(cost.box_count, 1);
    assert_eq!(cost.unbox_count, 1);
    assert_eq!(cost.total_overhead(), 3);
}

#[test]
fn test_cost_redundant_pair_detected() {
    // box then immediately unbox same type
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt64, unbox_expr(IRType::UInt64, 1), ret_var(2)),
    );
    let d = mk_decl("f", vec![(VarId(0), IRType::UInt64)], IRType::UInt64, body);
    let cost = estimate_boxing_cost(&d);
    assert_eq!(cost.redundant_pairs, 1);
    assert_eq!(cost.net_overhead(), 0);
}

#[test]
fn test_cost_net_overhead_calculation() {
    let cost = BoxingCost {
        box_count: 3,
        unbox_count: 2,
        redundant_pairs: 1,
    };
    assert_eq!(cost.total_overhead(), 8); // 3*2 + 2
    assert_eq!(cost.net_overhead(), 5); // 8 - 3
}

// ---------------------------------------------------------------------------
// Box-unbox elimination
// ---------------------------------------------------------------------------

#[test]
fn test_eliminate_redirects_unbox_source() {
    // let v1 = box(UInt64, v0); let v2 = unbox(UInt64, v1); ret v2
    // After elimination: unbox should read from v0 directly instead of v1.
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt64, unbox_expr(IRType::UInt64, 1), ret_var(2)),
    );
    let result = eliminate_redundant_boxing(&body);
    // v2's value should now be Unbox { UInt64, v0 } instead of Unbox { UInt64, v1 }
    if let IRBody::VDecl { rest, .. } = &result {
        if let IRBody::VDecl {
            value:
                IRExpr::Unbox {
                    arg: IRArg::Var(src),
                    ..
                },
            ..
        } = rest.as_ref()
        {
            assert_eq!(*src, VarId(0), "unbox should read from original source");
            return;
        }
    }
    panic!("expected rewritten unbox");
}

#[test]
fn test_eliminate_no_change_different_types() {
    // box UInt64, unbox UInt32 — should NOT be rewritten.
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::UInt32, unbox_expr(IRType::UInt32, 1), ret_var(2)),
    );
    let result = eliminate_redundant_boxing(&body);
    if let IRBody::VDecl { rest, .. } = &result {
        if let IRBody::VDecl {
            value:
                IRExpr::Unbox {
                    arg: IRArg::Var(src),
                    ..
                },
            ..
        } = rest.as_ref()
        {
            assert_eq!(*src, VarId(1), "type mismatch should prevent rewrite");
            return;
        }
    }
    panic!("expected original unbox preserved");
}

#[test]
fn test_eliminate_preserves_non_boxing() {
    let body = vdecl(
        0,
        IRType::UInt64,
        IRExpr::Lit(IRLiteral::UInt64(42)),
        ret_var(0),
    );
    let result = eliminate_redundant_boxing(&body);
    if let IRBody::VDecl { value, .. } = &result {
        assert!(matches!(value, IRExpr::Lit(IRLiteral::UInt64(42))));
    } else {
        panic!("expected VDecl");
    }
}

// ---------------------------------------------------------------------------
// Shared boxing
// ---------------------------------------------------------------------------

#[test]
fn test_shared_boxing_single_box_no_opportunity() {
    let body = vdecl(1, IRType::Object, box_expr(IRType::UInt64, 0), ret_var(1));
    assert!(find_shared_boxing_opportunities(&body).is_empty());
}

#[test]
fn test_shared_boxing_duplicate_box_detected() {
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(2, IRType::Object, box_expr(IRType::UInt64, 0), ret_var(1)),
    );
    let pairs = find_shared_boxing_opportunities(&body);
    assert_eq!(pairs.len(), 1);
    assert_eq!(pairs[0], (VarId(1), VarId(2)));
}

#[test]
fn test_shared_boxing_different_source_no_opportunity() {
    let body = vdecl(
        2,
        IRType::Object,
        box_expr(IRType::UInt64, 0),
        vdecl(3, IRType::Object, box_expr(IRType::UInt64, 1), ret_var(2)),
    );
    assert!(find_shared_boxing_opportunities(&body).is_empty());
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

#[test]
fn test_stats_empty_module() {
    let stats = collect_boxing_stats(&[]);
    assert_eq!(stats.total_functions, 0);
    assert_eq!(stats.functions_with_boxing, 0);
}

#[test]
fn test_stats_mixed_module() {
    let d1_body = vdecl(1, IRType::Object, box_expr(IRType::UInt64, 0), ret_var(1));
    let d1 = mk_decl(
        "box_fn",
        vec![(VarId(0), IRType::UInt64)],
        IRType::Object,
        d1_body,
    );
    let d2 = mk_decl("no_box", vec![], IRType::Object, ret_erased());
    let d3 = mk_decl(
        "poly",
        vec![(VarId(0), IRType::Erased)],
        IRType::Object,
        ret_erased(),
    );
    let stats = collect_boxing_stats(&[d1, d2, d3]);
    assert_eq!(stats.total_functions, 3);
    assert_eq!(stats.functions_with_boxing, 1);
    assert_eq!(stats.total_box_ops, 1);
    assert_eq!(stats.polymorphic_functions, 1);
}

#[test]
fn test_stats_summary_format() {
    let stats = BoxingStats {
        total_functions: 5,
        functions_with_boxing: 2,
        total_box_ops: 3,
        total_unbox_ops: 1,
        total_redundant_pairs: 0,
        total_shared_opportunities: 0,
        polymorphic_functions: 1,
    };
    let s = stats.summary();
    assert!(s.contains("funcs=2/5"));
    assert!(s.contains("box=3"));
    assert!(s.contains("poly=1"));
}

// ---------------------------------------------------------------------------
// RC compatibility
// ---------------------------------------------------------------------------

#[test]
fn test_rc_compat_clean() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(ret_var(0)),
    };
    let d = mk_decl("f", vec![(VarId(0), IRType::Object)], IRType::Object, body);
    assert!(check_rc_compatibility(&[d]).is_empty());
}

#[test]
fn test_rc_compat_inc_on_scalar() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(ret_var(0)),
    };
    let d = mk_decl("f", vec![(VarId(0), IRType::UInt64)], IRType::UInt64, body);
    let issues = check_rc_compatibility(&[d]);
    assert_eq!(issues.len(), 1);
    assert!(issues[0].1.contains("inc"));
    assert!(issues[0].1.contains("scalar"));
}

#[test]
fn test_rc_compat_dec_on_scalar() {
    let body = IRBody::Dec {
        var: VarId(0),
        rest: Box::new(ret_var(0)),
    };
    let d = mk_decl("f", vec![(VarId(0), IRType::UInt32)], IRType::UInt32, body);
    let issues = check_rc_compatibility(&[d]);
    assert_eq!(issues.len(), 1);
    assert!(issues[0].1.contains("dec"));
}

#[test]
fn test_rc_compat_multiple_issues() {
    let body = IRBody::Inc {
        var: VarId(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(ret_var(0)),
        }),
    };
    let d = mk_decl("f", vec![(VarId(0), IRType::Bool)], IRType::Bool, body);
    let issues = check_rc_compatibility(&[d]);
    assert_eq!(issues.len(), 2);
}

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------

#[test]
fn test_config_defaults() {
    let cfg = BoxingExtConfig::default();
    assert!(cfg.propagate_across_calls);
    assert!(cfg.eliminate_redundant);
    assert!(cfg.shared_boxing);
    assert_eq!(cfg.max_propagation_iters, 10);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_already_boxed_param_no_extra_site() {
    // Param is already Object — no box site should be reported.
    let body = ret_var(0);
    let d = mk_decl("f", vec![(VarId(0), IRType::Object)], IRType::Object, body);
    assert!(analyze_boxing_sites(&d).is_empty());
}

#[test]
fn test_identity_boxing_round_trip() {
    // box then unbox of same type is a redundant pair.
    let body = vdecl(
        1,
        IRType::Object,
        box_expr(IRType::Float64, 0),
        vdecl(
            2,
            IRType::Float64,
            unbox_expr(IRType::Float64, 1),
            ret_var(2),
        ),
    );
    let d = mk_decl(
        "id",
        vec![(VarId(0), IRType::Float64)],
        IRType::Float64,
        body,
    );
    let cost = estimate_boxing_cost(&d);
    assert_eq!(cost.redundant_pairs, 1);
    assert_eq!(cost.net_overhead(), 0);
}

#[test]
fn test_polymorphic_struct_keeps_type() {
    let ty = IRType::Struct(vec![IRType::UInt64, IRType::Bool]);
    assert_eq!(polymorphic_boxing_type(&ty), ty);
}

#[test]
fn test_polymorphic_tobject() {
    assert_eq!(polymorphic_boxing_type(&IRType::TObject), IRType::TObject);
}

#[test]
fn test_cost_net_overhead_saturates() {
    let cost = BoxingCost {
        box_count: 0,
        unbox_count: 0,
        redundant_pairs: 5,
    };
    assert_eq!(cost.net_overhead(), 0);
}

#[test]
fn test_eliminate_unreachable_body() {
    let result = eliminate_redundant_boxing(&IRBody::Unreachable);
    assert!(matches!(result, IRBody::Unreachable));
}

#[test]
fn test_shared_boxing_erased_arg_ignored() {
    // Box with Erased arg should not appear in shared opportunities.
    let body = vdecl(
        1,
        IRType::Object,
        IRExpr::Box {
            ty: IRType::UInt64,
            arg: IRArg::Erased,
        },
        ret_var(1),
    );
    assert!(find_shared_boxing_opportunities(&body).is_empty());
}

#[test]
fn test_analyze_sites_in_case_branch() {
    let branch = vdecl(1, IRType::Object, box_expr(IRType::UInt32, 0), ret_var(1));
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![crate::ir::IRAlt {
            ctor: crate::ir::CtorInfo {
                name: Name::from_string("Ctor"),
                tag: 0,
                num_scalars: 0,
                num_objects: 0,
                field_types: vec![],
            },
            body: Box::new(branch),
        }],
        default: None,
    };
    let d = mk_decl("f", vec![(VarId(0), IRType::Object)], IRType::Object, body);
    assert_eq!(analyze_boxing_sites(&d).len(), 1);
}
