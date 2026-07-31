// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for enhanced local dead code elimination.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::dce_local_ext::{
    compute_live_vars, detect_unused_params, eliminate_dead_locals_ext,
    eliminate_dead_locals_ext_default, validate_elimination, DceValidationError, ExtDceConfig,
    ExtDceStats,
};
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;

// -----------------------------------------------------------------------
// Test helpers
// -----------------------------------------------------------------------

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
            name: Name::from_string(&format!("Ctor{}", tag)),
            tag,
            num_scalars: 0,
            num_objects: 0,
            field_types: vec![],
        },
        body: Box::new(body),
    }
}

fn ctor_expr(tag: u32, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Ctor {
        info: CtorInfo {
            name: Name::from_string(&format!("Ctor{}", tag)),
            tag,
            num_scalars: 0,
            num_objects: 0,
            field_types: vec![],
        },
        args,
    }
}

fn apply_expr(name: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: FnId(Name::from_string(name)),
        args,
    }
}

// -----------------------------------------------------------------------
// Tests: Liveness analysis
// -----------------------------------------------------------------------

#[test]
fn test_compute_live_vars_simple_return() {
    // ret x0
    let body = ret_var(0);
    let live = compute_live_vars(&body);
    assert!(live.contains(&var(0)));
    assert!(!live.contains(&var(1)));
}

#[test]
fn test_compute_live_vars_let_chain() {
    // let x1 = 42; let x2 = 10; ret x1
    let body = vdecl(1, lit_u64(42), vdecl(2, lit_u64(10), ret_var(1)));
    let live = compute_live_vars(&body);
    assert!(live.contains(&var(1)), "x1 is used in return");
    // x2 is defined but not used in return
}

#[test]
fn test_compute_live_vars_inc_dec() {
    // inc x0 1; dec x1; ret x2
    let body = inc(0, 1, dec(1, ret_var(2)));
    let live = compute_live_vars(&body);
    assert!(live.contains(&var(0)));
    assert!(live.contains(&var(1)));
    assert!(live.contains(&var(2)));
}

// -----------------------------------------------------------------------
// Tests: Dead binding elimination
// -----------------------------------------------------------------------

#[test]
fn test_dead_binding_pure_expr_removed() {
    // let x1 = 42; ret x0  => ret x0
    let body = vdecl(1, lit_u64(42), ret_var(0));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.bindings_removed, 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(0)))));
}

#[test]
fn test_dead_binding_impure_expr_kept() {
    // let x1 = f(x0); ret x0  => kept (f may have side effects)
    let body = vdecl(1, apply_expr("f", vec![var_arg(0)]), ret_var(0));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.bindings_removed, 0);
    assert!(matches!(result, IRBody::VDecl { .. }));
}

#[test]
fn test_live_binding_kept() {
    // let x1 = 42; ret x1
    let body = vdecl(1, lit_u64(42), ret_var(1));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.bindings_removed, 0);
    assert!(matches!(result, IRBody::VDecl { var: VarId(1), .. }));
}

#[test]
fn test_chain_of_dead_bindings() {
    // let x1 = 1; let x2 = 2; let x3 = 3; ret x0
    let body = vdecl(
        1,
        lit_u64(1),
        vdecl(2, lit_u64(2), vdecl(3, lit_u64(3), ret_var(0))),
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.bindings_removed, 3);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(0)))));
}

#[test]
fn test_mixed_live_dead_bindings() {
    // let x1 = 42; let x2 = 99; ret x1
    let body = vdecl(1, lit_u64(42), vdecl(2, lit_u64(99), ret_var(1)));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.bindings_removed, 1);
    match &result {
        IRBody::VDecl {
            var: VarId(1),
            rest,
            ..
        } => {
            assert!(matches!(**rest, IRBody::Ret(IRArg::Var(VarId(1)))));
        }
        _ => panic!("expected VDecl for x1, got: {:?}", result),
    }
}

// -----------------------------------------------------------------------
// Tests: Dead join point elimination
// -----------------------------------------------------------------------

#[test]
fn test_dead_join_point_removed() {
    // jdecl j0 [] { ret x0 }; ret x1  => ret x1 (j0 never jumped to)
    let body = jdecl(0, vec![], ret_var(0), ret_var(1));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.joins_removed, 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(1)))));
}

#[test]
fn test_live_join_point_kept() {
    // jdecl j0 [] { ret x0 }; jmp j0
    let body = jdecl(
        0,
        vec![],
        ret_var(0),
        IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        },
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.joins_removed, 0);
    assert!(matches!(result, IRBody::JDecl { .. }));
}

// -----------------------------------------------------------------------
// Tests: Unreachable branch pruning
// -----------------------------------------------------------------------

#[test]
fn test_prune_unreachable_alt() {
    // case x0 { Ctor0 => ret x1, Ctor1 => unreachable } => single alt
    let body = case(
        0,
        vec![alt(0, ret_var(1)), alt(1, IRBody::Unreachable)],
        None,
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.branches_pruned >= 1);
    // After pruning Ctor1 (unreachable) and simplifying the single remaining alt
    assert!(
        matches!(&result, IRBody::Ret(IRArg::Var(VarId(1))))
            || matches!(&result, IRBody::Case { alts, .. } if alts.len() == 1)
    );
}

#[test]
fn test_prune_unreachable_default() {
    // case x0 { Ctor0 => ret x1 } default => unreachable
    let body = case(0, vec![alt(0, ret_var(1))], Some(IRBody::Unreachable));
    let (_result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.branches_pruned >= 1);
}

#[test]
fn test_unreachable_after_inc_dec_chain() {
    // case x0 { Ctor0 => inc x1 1; dec x2; unreachable }
    let unreach = inc(1, 1, dec(2, IRBody::Unreachable));
    let body = case(0, vec![alt(0, ret_var(1)), alt(1, unreach)], None);
    let (_result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.branches_pruned >= 1);
}

// -----------------------------------------------------------------------
// Tests: Known-tag branch folding
// -----------------------------------------------------------------------

#[test]
fn test_known_tag_folds_case() {
    // let x1 = Ctor0(); case x1 { Ctor0 => ret x2, Ctor1 => ret x3 }
    let body = vdecl(
        1,
        ctor_expr(0, vec![]),
        case(1, vec![alt(0, ret_var(2)), alt(1, ret_var(3))], None),
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.cases_folded >= 1);
    assert!(
        matches!(result, IRBody::Ret(IRArg::Var(VarId(2)))),
        "expected ret x2 after folding and fixpoint DCE, got: {:?}",
        result
    );
}

#[test]
fn test_known_tag_folds_to_default() {
    // let x1 = Ctor2(); case x1 { Ctor0 => ret x2 } default => ret x3
    let body = vdecl(
        1,
        ctor_expr(2, vec![]),
        case(1, vec![alt(0, ret_var(2))], Some(ret_var(3))),
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.cases_folded >= 1);
    assert!(
        matches!(result, IRBody::Ret(IRArg::Var(VarId(3)))),
        "expected ret x3 (default) after folding and fixpoint DCE, got: {:?}",
        result
    );
}

// -----------------------------------------------------------------------
// Tests: Inc/Dec cleanup
// -----------------------------------------------------------------------

#[test]
fn test_inc_on_unused_var_removed() {
    // inc x5 1; ret x0  => ret x0 (x5 not used after inc)
    let body = inc(5, 1, ret_var(0));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.rc_ops_removed >= 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(0)))));
}

#[test]
fn test_dec_on_globally_unused_var_removed() {
    // dec x5; ret x0  => ret x0 (x5 not used anywhere)
    // Only remove dec when var was never in used set at all
    let body = dec(5, ret_var(0));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.rc_ops_removed >= 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(0)))));
}

#[test]
fn test_inc_on_used_var_kept() {
    // inc x0 1; ret x0
    let body = inc(0, 1, ret_var(0));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.rc_ops_removed, 0);
    assert!(matches!(result, IRBody::Inc { .. }));
}

// -----------------------------------------------------------------------
// Tests: Chain simplification
// -----------------------------------------------------------------------

#[test]
fn test_single_alt_no_default_simplified() {
    // case x0 { Ctor0 => ret x1 }  => ret x1
    let body = case(0, vec![alt(0, ret_var(1))], None);
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.chains_simplified >= 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(1)))));
}

#[test]
fn test_no_alts_with_default_simplified() {
    // case x0 {} default => ret x1  => ret x1
    let body = case(0, vec![], Some(ret_var(1)));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert!(stats.chains_simplified >= 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(1)))));
}

#[test]
fn test_multiple_alts_not_simplified() {
    // case x0 { Ctor0 => ret x1, Ctor1 => ret x2 }  => kept
    let body = case(0, vec![alt(0, ret_var(1)), alt(1, ret_var(2))], None);
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.chains_simplified, 0);
    assert!(matches!(result, IRBody::Case { .. }));
}

// -----------------------------------------------------------------------
// Tests: Configuration control
// -----------------------------------------------------------------------

#[test]
fn test_config_disables_dead_bindings() {
    let body = vdecl(1, lit_u64(42), ret_var(0));
    let config = ExtDceConfig {
        eliminate_dead_bindings: false,
        ..ExtDceConfig::default()
    };
    let (result, stats) = eliminate_dead_locals_ext(&body, &config);
    assert_eq!(stats.bindings_removed, 0);
    assert!(matches!(result, IRBody::VDecl { .. }));
}

#[test]
fn test_config_disables_branch_pruning() {
    let body = case(
        0,
        vec![alt(0, ret_var(1)), alt(1, IRBody::Unreachable)],
        None,
    );
    let config = ExtDceConfig {
        prune_unreachable_branches: false,
        simplify_single_alt: false,
        ..ExtDceConfig::default()
    };
    let (result, stats) = eliminate_dead_locals_ext(&body, &config);
    assert_eq!(stats.branches_pruned, 0);
    match result {
        IRBody::Case { alts, .. } => assert_eq!(alts.len(), 2),
        _ => panic!("expected Case to remain"),
    }
}

// -----------------------------------------------------------------------
// Tests: Fixpoint iteration
// -----------------------------------------------------------------------

#[test]
fn test_fixpoint_cascading_dead_bindings() {
    // let x1 = x2; let x2 = 42; ret x0
    // First pass removes x1 (unused), second pass removes x2 (now unused)
    // Actually: x2 is used in x1's value. But x1 is dead, so after removing
    // x1, x2 becomes unused. Tests fixpoint.
    let body = vdecl(
        1,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::UInt64,
            arg: var_arg(2),
        },
        vdecl(2, lit_u64(42), ret_var(0)),
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    // Both x1 and x2 should be removed after fixpoint
    assert_eq!(stats.bindings_removed, 2);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(0)))));
}

#[test]
fn test_max_iterations_respected() {
    let body = vdecl(1, lit_u64(42), ret_var(0));
    let config = ExtDceConfig {
        max_iterations: 1,
        ..ExtDceConfig::default()
    };
    let (_, stats) = eliminate_dead_locals_ext(&body, &config);
    assert!(stats.iterations <= 1);
}

// -----------------------------------------------------------------------
// Tests: Edge cases
// -----------------------------------------------------------------------

#[test]
fn test_empty_case_unreachable() {
    // case x0 {} (no alts, no default) => stays as-is (degenerate)
    let body = case(0, vec![], None);
    let (result, _stats) = eliminate_dead_locals_ext_default(&body);
    assert!(matches!(result, IRBody::Case { .. }));
}

#[test]
fn test_return_erased() {
    let body = vdecl(1, lit_u64(42), IRBody::Ret(IRArg::Erased));
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.bindings_removed, 1);
    assert!(matches!(result, IRBody::Ret(IRArg::Erased)));
}

#[test]
fn test_unreachable_body() {
    let body = vdecl(1, lit_u64(42), IRBody::Unreachable);
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.bindings_removed, 1);
    assert!(matches!(result, IRBody::Unreachable));
}

#[test]
fn test_nested_case_in_join_point() {
    // jdecl j0 [] { case x0 { Ctor0 => ret x1 } }; jmp j0
    let jp_body = case(0, vec![alt(0, ret_var(1))], None);
    let body = jdecl(
        0,
        vec![],
        jp_body,
        IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        },
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    // The single-alt case inside the join point should be simplified
    assert!(stats.chains_simplified >= 1);
    match &result {
        IRBody::JDecl { body: jp_body, .. } => {
            assert!(
                matches!(**jp_body, IRBody::Ret(IRArg::Var(VarId(1)))),
                "expected join body to be simplified to ret x1"
            );
        }
        _ => panic!("expected JDecl, got: {:?}", result),
    }
}

#[test]
fn test_stats_total() {
    let stats = ExtDceStats {
        bindings_removed: 3,
        joins_removed: 1,
        branches_pruned: 2,
        cases_folded: 1,
        rc_ops_removed: 2,
        chains_simplified: 1,
        params_eliminated: 0,
        iterations: 2,
    };
    assert_eq!(stats.total(), 10);
}

#[test]
fn test_set_passthrough_preserved() {
    // set x0[0] = x1; ret x0
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(ret_var(0)),
    };
    let (result, _stats) = eliminate_dead_locals_ext_default(&body);
    assert!(matches!(result, IRBody::Set { .. }));
}

#[test]
fn test_jmp_with_args() {
    // jdecl j0 [(x1, UInt64)] { ret x1 }; jmp j0 [x0]
    let body = jdecl(
        0,
        vec![(var(1), IRType::UInt64)],
        ret_var(1),
        IRBody::Jmp {
            jp: jp(0),
            args: vec![var_arg(0)],
        },
    );
    let (result, stats) = eliminate_dead_locals_ext_default(&body);
    assert_eq!(stats.joins_removed, 0);
    assert!(matches!(result, IRBody::JDecl { .. }));
}

// -----------------------------------------------------------------------
// Tests: Unused parameter detection
// -----------------------------------------------------------------------

#[test]
fn test_detect_unused_params_all_used() {
    // fn(x0, x1) { let x2 = proj x0; ret x1 }
    let body = vdecl(
        2,
        IRExpr::Proj {
            idx: 0,
            ty: IRType::UInt64,
            arg: var_arg(0),
        },
        ret_var(1),
    );
    let params = vec![(var(0), IRType::Object), (var(1), IRType::UInt64)];
    let unused = detect_unused_params(&params, &body);
    assert!(unused.is_empty());
}

#[test]
fn test_detect_unused_params_one_unused() {
    // fn(x0, x1) { ret x0 } — x1 is unused
    let body = ret_var(0);
    let params = vec![(var(0), IRType::UInt64), (var(1), IRType::UInt64)];
    let unused = detect_unused_params(&params, &body);
    assert_eq!(unused, vec![1]);
}

#[test]
fn test_detect_unused_params_all_unused() {
    // fn(x0, x1, x2) { ret erased }
    let body = IRBody::Ret(IRArg::Erased);
    let params = vec![
        (var(0), IRType::UInt64),
        (var(1), IRType::UInt64),
        (var(2), IRType::Object),
    ];
    let unused = detect_unused_params(&params, &body);
    assert_eq!(unused, vec![0, 1, 2]);
}

#[test]
fn test_detect_unused_params_empty() {
    let body = ret_var(0);
    let params: Vec<(VarId, IRType)> = vec![];
    let unused = detect_unused_params(&params, &body);
    assert!(unused.is_empty());
}

#[test]
fn test_detect_unused_params_used_in_nested_case() {
    // fn(x0, x1) { case x0 { Ctor0 => ret x1 } }
    let body = case(0, vec![alt(0, ret_var(1))], None);
    let params = vec![(var(0), IRType::Object), (var(1), IRType::UInt64)];
    let unused = detect_unused_params(&params, &body);
    assert!(unused.is_empty());
}

// -----------------------------------------------------------------------
// Tests: Validation
// -----------------------------------------------------------------------

#[test]
fn test_validate_elimination_valid_body() {
    // let x1 = 42; ret x1 — valid: x1 is defined before use
    let body = vdecl(1, lit_u64(42), ret_var(1));
    let result = validate_elimination(
        &body,
        &std::collections::HashSet::new(),
        &std::collections::HashSet::new(),
    );
    result.expect("body should be valid");
}

#[test]
fn test_validate_elimination_dangling_var() {
    // ret x5 — invalid: x5 was never defined
    let body = ret_var(5);
    let result = validate_elimination(
        &body,
        &std::collections::HashSet::new(),
        &std::collections::HashSet::new(),
    );
    assert_eq!(result, Err(DceValidationError::DanglingVarRef(5)));
}

#[test]
fn test_validate_elimination_dangling_join() {
    // jmp j99 [] — invalid: j99 was never declared
    let body = IRBody::Jmp {
        jp: jp(99),
        args: vec![],
    };
    let result = validate_elimination(
        &body,
        &std::collections::HashSet::new(),
        &std::collections::HashSet::new(),
    );
    assert_eq!(result, Err(DceValidationError::DanglingJoinRef(99)));
}

#[test]
fn test_validate_elimination_with_initial_params() {
    // ret x0 — valid if x0 is in initial_vars (function parameter)
    let body = ret_var(0);
    let mut vars = std::collections::HashSet::new();
    vars.insert(var(0));
    let result = validate_elimination(&body, &vars, &std::collections::HashSet::new());
    result.expect("should be valid with param in scope");
}

#[test]
fn test_validate_elimination_join_in_scope() {
    // jdecl j0 [] { ret erased }; jmp j0 — valid
    let body = jdecl(
        0,
        vec![],
        IRBody::Ret(IRArg::Erased),
        IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        },
    );
    let result = validate_elimination(
        &body,
        &std::collections::HashSet::new(),
        &std::collections::HashSet::new(),
    );
    result.expect("join is declared before use");
}

#[test]
fn test_validate_elimination_after_dce() {
    // Run DCE then validate the result
    let body = vdecl(1, lit_u64(42), vdecl(2, lit_u64(99), ret_var(1)));
    let (result, _) = eliminate_dead_locals_ext_default(&body);
    let validation = validate_elimination(
        &result,
        &std::collections::HashSet::new(),
        &std::collections::HashSet::new(),
    );
    validation.expect("DCE result should have no dangling refs");
}

// -----------------------------------------------------------------------
// Tests: params_eliminated stat field
// -----------------------------------------------------------------------

#[test]
fn test_stats_total_includes_params() {
    let stats = ExtDceStats {
        bindings_removed: 1,
        joins_removed: 1,
        branches_pruned: 1,
        cases_folded: 1,
        rc_ops_removed: 1,
        chains_simplified: 1,
        params_eliminated: 3,
        iterations: 1,
    };
    assert_eq!(stats.total(), 9);
}

#[test]
fn test_stats_default_params_zero() {
    let stats = ExtDceStats::default();
    assert_eq!(stats.params_eliminated, 0);
    assert_eq!(stats.total(), 0);
}
