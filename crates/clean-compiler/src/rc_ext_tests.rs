// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended RC optimization pass.

use super::rc_ext::*;
use crate::ir::{CtorInfo, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

// ═══════════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════════

fn var(n: u32) -> VarId {
    VarId(n)
}

fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_ctor(tag: u32, n_objs: u32) -> CtorInfo {
    CtorInfo {
        name: name("Ctor"),
        tag,
        num_scalars: 0,
        num_objects: n_objs,
        field_types: vec![IRType::Object; n_objs as usize],
    }
}

/// Build a declaration with given params, return type, and body.
fn mk_decl(fname: &str, params: Vec<(VarId, IRType)>, ret: IRType, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(fname),
        params,
        return_type: ret,
        body,
    }
}

/// Identity function: one object param, returns it directly.
fn identity_decl() -> IRDecl {
    mk_decl(
        "id",
        vec![(var(0), IRType::Object)],
        IRType::Object,
        IRBody::Ret(arg_var(0)),
    )
}

/// Build inc x n; rest
fn inc(v: u32, n: u32, rest: IRBody) -> IRBody {
    IRBody::Inc {
        var: var(v),
        n,
        rest: Box::new(rest),
    }
}

/// Build dec x; rest
fn dec(v: u32, rest: IRBody) -> IRBody {
    IRBody::Dec {
        var: var(v),
        rest: Box::new(rest),
    }
}

/// Build a VDecl with Ctor value.
fn vdecl_ctor(v: u32, tag: u32, args: Vec<IRArg>, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: mk_ctor(tag, args.len() as u32),
            args,
        },
        rest: Box::new(rest),
    }
}

/// Build a VDecl with Proj value.
fn vdecl_proj(v: u32, idx: u32, src: u32, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx,
            ty: IRType::Object,
            arg: arg_var(src),
        },
        rest: Box::new(rest),
    }
}

/// Build a VDecl with Apply.
fn vdecl_apply(v: u32, fn_name: &str, args: Vec<IRArg>, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: crate::ir::FnId(name(fn_name)),
            args,
        },
        rest: Box::new(rest),
    }
}

/// Build a VDecl with a literal value.
fn vdecl_lit(v: u32, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(rest),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// RC Elision Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_elision_inc_dec_same_var() {
    // inc x 1; dec x; ret x  =>  ret x
    let body = inc(0, 1, dec(0, IRBody::Ret(arg_var(0))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        elision: true,
        ..Default::default()
    };
    let (opt, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_eliminated, 1);
    assert_eq!(stats.decs_eliminated, 1);
    assert!(matches!(opt.body, IRBody::Ret(_)));
}

#[test]
fn test_elision_no_match_different_vars() {
    // inc x 1; dec y; ret x  =>  inc x 1; dec y; ret x  (different vars, no elision)
    let body = inc(0, 1, dec(1, IRBody::Ret(arg_var(0))));
    let decl = mk_decl(
        "f",
        vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        IRType::Object,
        body,
    );
    let config = RcExtConfig {
        elision: true,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_remaining, 1);
    assert_eq!(stats.decs_remaining, 1);
}

#[test]
fn test_elision_inc_n_gt_1_no_elision() {
    // inc x 2; dec x; ret x  =>  no elision (n != 1)
    let body = inc(0, 2, dec(0, IRBody::Ret(arg_var(0))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        elision: true,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_remaining, 1);
    assert_eq!(stats.decs_remaining, 1);
}

#[test]
fn test_elision_disabled() {
    let body = inc(0, 1, dec(0, IRBody::Ret(arg_var(0))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        elision: false,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_remaining, 1);
    assert_eq!(stats.decs_remaining, 1);
}

// ═══════════════════════════════════════════════════════════════════════
// Borrowed Parameter Optimization Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_borrowed_param_proj_only() {
    // f(x) = let y = proj 0 x; ret y
    // x is only projected, so inc/dec of x should be eliminated.
    let body = inc(0, 1, vdecl_proj(1, 0, 0, dec(0, IRBody::Ret(arg_var(1)))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        borrowed_opt: true,
        ..Default::default()
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert!(
        stats.borrowed_skipped >= 2,
        "expected at least 2 borrowed skips, got {}",
        stats.borrowed_skipped
    );
}

#[test]
fn test_borrowed_param_consumed_in_ctor() {
    // f(x) = let y = Ctor(x); ret y
    // x is consumed (stored in ctor), so borrowed opt does NOT apply.
    let body = inc(
        0,
        1,
        vdecl_ctor(1, 0, vec![arg_var(0)], IRBody::Ret(arg_var(1))),
    );
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        borrowed_opt: true,
        elision: false,
        last_use: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.borrowed_skipped, 0);
}

#[test]
fn test_borrowed_param_scalar_ignored() {
    // Scalar params should not be affected by borrowed-param opt.
    let body = IRBody::Ret(arg_var(0));
    let decl = mk_decl("f", vec![(var(0), IRType::UInt64)], IRType::UInt64, body);
    let config = RcExtConfig::default();
    let (opt, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.borrowed_skipped, 0);
    assert!(matches!(opt.body, IRBody::Ret(_)));
}

#[test]
fn test_borrowed_disabled() {
    let body = inc(0, 1, vdecl_proj(1, 0, 0, dec(0, IRBody::Ret(arg_var(1)))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        borrowed_opt: false,
        elision: false,
        last_use: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.borrowed_skipped, 0);
    assert_eq!(stats.incs_remaining, 1);
}

// ═══════════════════════════════════════════════════════════════════════
// Last-Use Analysis Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_last_use_consuming_return() {
    // dec x; ret x  =>  dec eliminated (x is consumed by ret).
    let body = dec(0, IRBody::Ret(arg_var(0)));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        last_use: true,
        elision: false,
        borrowed_opt: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.last_use_skipped, 1);
    assert_eq!(stats.decs_eliminated, 1);
}

#[test]
fn test_last_use_consuming_ctor() {
    // dec x; let y = Ctor(x); ret y  =>  dec eliminated.
    let body = dec(
        0,
        vdecl_ctor(1, 0, vec![arg_var(0)], IRBody::Ret(arg_var(1))),
    );
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        last_use: true,
        elision: false,
        borrowed_opt: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.last_use_skipped, 1);
}

#[test]
fn test_last_use_non_consuming_proj() {
    // dec x; let y = proj 0 x; ret y  =>  dec NOT eliminated (proj is non-consuming).
    let body = dec(0, vdecl_proj(1, 0, 0, IRBody::Ret(arg_var(1))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        last_use: true,
        elision: false,
        borrowed_opt: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.last_use_skipped, 0);
    assert_eq!(stats.decs_remaining, 1);
}

#[test]
fn test_last_use_disabled() {
    let body = dec(0, IRBody::Ret(arg_var(0)));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        last_use: false,
        elision: false,
        borrowed_opt: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.last_use_skipped, 0);
    assert_eq!(stats.decs_remaining, 1);
}

// ═══════════════════════════════════════════════════════════════════════
// RC Sinking Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_sinking_dec_far_from_use() {
    // dec x; let y = lit 42; ret y
    // x is not used immediately after dec, so sinking is flagged.
    let body = dec(0, vdecl_lit(1, IRBody::Ret(arg_var(1))));
    let decl = mk_decl(
        "f",
        vec![(var(0), IRType::Object), (var(1), IRType::UInt64)],
        IRType::UInt64,
        body,
    );
    let config = RcExtConfig {
        sinking: true,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.decs_sunk, 1);
}

#[test]
fn test_sinking_dec_immediate_use() {
    // dec x; ret x  =>  dec IS immediately used, no sinking stat.
    let body = dec(0, IRBody::Ret(arg_var(0)));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        sinking: true,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.decs_sunk, 0);
}

#[test]
fn test_sinking_disabled() {
    let body = dec(0, vdecl_lit(1, IRBody::Ret(arg_var(1))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::UInt64, body);
    let config = RcExtConfig {
        sinking: false,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.decs_sunk, 0);
}

// ═══════════════════════════════════════════════════════════════════════
// RC Combining Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_combining_adjacent_incs() {
    // inc x 1; inc x 1; ret x  =>  inc x 2; ret x
    let body = inc(0, 1, inc(0, 1, IRBody::Ret(arg_var(0))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        combining: true,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        immutable_beans: false,
    };
    let (opt, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_combined, 1);
    if let IRBody::Inc { n, .. } = &opt.body {
        assert_eq!(*n, 2);
    } else {
        panic!("expected Inc at top");
    }
}

#[test]
fn test_combining_different_vars_no_combine() {
    // inc x 1; inc y 1; ret x  =>  no combining.
    let body = inc(0, 1, inc(1, 1, IRBody::Ret(arg_var(0))));
    let decl = mk_decl(
        "f",
        vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        IRType::Object,
        body,
    );
    let config = RcExtConfig {
        combining: true,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_combined, 0);
    assert_eq!(stats.incs_remaining, 2);
}

#[test]
fn test_combining_disabled() {
    let body = inc(0, 1, inc(0, 1, IRBody::Ret(arg_var(0))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let config = RcExtConfig {
        combining: false,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_combined, 0);
    assert_eq!(stats.incs_remaining, 2);
}

// ═══════════════════════════════════════════════════════════════════════
// Immutable Bean Optimization Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_beans_fresh_ctor_unique() {
    // let y = Ctor(); inc y 1; dec y; ret y
    // y is freshly allocated and not shared, so inc/dec can be elided.
    let body = vdecl_ctor(1, 0, vec![], inc(1, 1, dec(1, IRBody::Ret(arg_var(1)))));
    let decl = mk_decl("f", vec![], IRType::Object, body);
    let config = RcExtConfig {
        immutable_beans: true,
        elision: true,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        combining: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    // inc+dec pair elided first, then beans may also fire. At minimum,
    // at least 1 elimination should happen.
    assert!(stats.incs_eliminated >= 1 || stats.bean_elisions >= 1);
}

#[test]
fn test_beans_shared_via_apply() {
    // let y = Ctor(); let z = f(y); ret z
    // y is passed to f, so it is shared and beans opt does NOT apply.
    let body = vdecl_ctor(
        1,
        0,
        vec![],
        inc(
            1,
            1,
            vdecl_apply(2, "f", vec![arg_var(1)], IRBody::Ret(arg_var(2))),
        ),
    );
    let decl = mk_decl("g", vec![], IRType::Object, body);
    let config = RcExtConfig {
        immutable_beans: true,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        combining: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    // y is shared (passed to apply), so bean_elisions should NOT fire for y.
    // The inc of y=1 should remain.
    assert_eq!(stats.bean_elisions, 0);
    assert_eq!(stats.incs_remaining, 1);
}

#[test]
fn test_beans_disabled() {
    let body = vdecl_ctor(1, 0, vec![], inc(1, 1, IRBody::Ret(arg_var(1))));
    let decl = mk_decl("f", vec![], IRType::Object, body);
    let config = RcExtConfig {
        immutable_beans: false,
        elision: false,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        combining: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.bean_elisions, 0);
    assert_eq!(stats.incs_remaining, 1);
}

// ═══════════════════════════════════════════════════════════════════════
// Statistics Tracking Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_stats_no_rc_ops() {
    let decl = identity_decl();
    let (_, stats) = optimize_rc_ext_default(&decl);
    assert_eq!(stats.incs_eliminated, 0);
    assert_eq!(stats.decs_eliminated, 0);
    assert_eq!(stats.incs_remaining, 0);
    assert_eq!(stats.decs_remaining, 0);
}

#[test]
fn test_stats_track_remaining() {
    // inc x 1; inc y 1; dec z; ret x
    // With all opts disabled, all should remain.
    let body = inc(0, 1, inc(1, 1, dec(2, IRBody::Ret(arg_var(0)))));
    let decl = mk_decl(
        "f",
        vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
        ],
        IRType::Object,
        body,
    );
    let config = RcExtConfig {
        elision: false,
        borrowed_opt: false,
        last_use: false,
        sinking: false,
        combining: false,
        immutable_beans: false,
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert_eq!(stats.incs_remaining, 2);
    assert_eq!(stats.decs_remaining, 1);
}

#[test]
fn test_stats_default_is_zero() {
    let stats = RcExtStats::default();
    assert_eq!(stats.incs_eliminated, 0);
    assert_eq!(stats.decs_eliminated, 0);
    assert_eq!(stats.incs_remaining, 0);
    assert_eq!(stats.decs_remaining, 0);
    assert_eq!(stats.incs_combined, 0);
    assert_eq!(stats.decs_sunk, 0);
    assert_eq!(stats.borrowed_skipped, 0);
    assert_eq!(stats.last_use_skipped, 0);
    assert_eq!(stats.bean_elisions, 0);
}

// ═══════════════════════════════════════════════════════════════════════
// Correctness Validation Tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_validate_balanced_simple() {
    // inc x 1; dec x; ret x  =>  balance: x=0 (balanced).
    let body = inc(0, 1, dec(0, IRBody::Ret(arg_var(0))));
    let balance = validate_rc_balance(&body);
    assert_eq!(*balance.get(&var(0)).unwrap_or(&0), 0);
    assert!(is_rc_balanced(&body));
}

#[test]
fn test_validate_unbalanced_double_dec() {
    // dec x; dec x; ret erased  =>  balance: x=-2 (unbalanced).
    let body = dec(0, dec(0, IRBody::Ret(IRArg::Erased)));
    let balance = validate_rc_balance(&body);
    assert_eq!(*balance.get(&var(0)).unwrap_or(&0), -2);
    assert!(!is_rc_balanced(&body));
}

#[test]
fn test_validate_positive_balance() {
    // inc x 2; ret x  =>  balance: x=+2 (balanced, net positive OK).
    let body = inc(0, 2, IRBody::Ret(arg_var(0)));
    assert!(is_rc_balanced(&body));
    let balance = validate_rc_balance(&body);
    assert_eq!(*balance.get(&var(0)).unwrap_or(&0), 2);
}

#[test]
fn test_validate_empty_body() {
    let body = IRBody::Ret(IRArg::Erased);
    assert!(is_rc_balanced(&body));
    let balance = validate_rc_balance(&body);
    assert!(balance.is_empty());
}

#[test]
fn test_validate_after_optimization() {
    // inc x 1; dec x; ret x  =>  after elision, body is just ret x, balanced.
    let body = inc(0, 1, dec(0, IRBody::Ret(arg_var(0))));
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let (opt, _) = optimize_rc_ext_default(&decl);
    assert!(is_rc_balanced(&opt.body));
}

// ═══════════════════════════════════════════════════════════════════════
// Edge Cases
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_edge_unreachable() {
    let decl = mk_decl("f", vec![], IRType::Void, IRBody::Unreachable);
    let (opt, stats) = optimize_rc_ext_default(&decl);
    assert!(matches!(opt.body, IRBody::Unreachable));
    assert_eq!(stats.incs_eliminated, 0);
    assert_eq!(stats.decs_eliminated, 0);
}

#[test]
fn test_edge_case_analysis() {
    // case x of { alt0: inc x 1; dec x; ret x }
    let alt_body = inc(0, 1, dec(0, IRBody::Ret(arg_var(0))));
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: mk_ctor(0, 1),
            body: Box::new(alt_body),
        }],
        default: None,
    };
    let decl = mk_decl("f", vec![(var(0), IRType::Object)], IRType::Object, body);
    let (_, stats) = optimize_rc_ext_default(&decl);
    // Elision should work inside case branches.
    assert!(stats.incs_eliminated >= 1);
}

#[test]
fn test_edge_jdecl_optimization() {
    // JDecl with inc/dec in both body and rest.
    let jp_body = inc(0, 1, dec(0, IRBody::Ret(arg_var(0))));
    let rest = inc(
        1,
        1,
        dec(
            1,
            IRBody::Jmp {
                jp: crate::ir::JoinPointId(0),
                args: vec![arg_var(1)],
            },
        ),
    );
    let body = IRBody::JDecl {
        jp: crate::ir::JoinPointId(0),
        params: vec![(var(2), IRType::Object)],
        body: Box::new(jp_body),
        rest: Box::new(rest),
    };
    let decl = mk_decl(
        "f",
        vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        IRType::Object,
        body,
    );
    let (_, stats) = optimize_rc_ext_default(&decl);
    assert!(stats.incs_eliminated >= 2);
}

#[test]
fn test_edge_all_borrowed_params() {
    // f(x, y) = let a = proj 0 x; let b = proj 0 y; ret a
    // Both params are borrowed; any inc/dec on them should be eliminated.
    let body = inc(
        0,
        1,
        inc(
            1,
            1,
            vdecl_proj(
                2,
                0,
                0,
                vdecl_proj(3, 0, 1, dec(0, dec(1, IRBody::Ret(arg_var(2))))),
            ),
        ),
    );
    let decl = mk_decl(
        "f",
        vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        IRType::Object,
        body,
    );
    let config = RcExtConfig {
        borrowed_opt: true,
        ..Default::default()
    };
    let (_, stats) = optimize_rc_ext(&decl, &config);
    assert!(stats.borrowed_skipped >= 4);
}

#[test]
fn test_edge_recursive_body_set() {
    // set x[0] = y; ret x  — Set nodes should be traversed.
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let decl = mk_decl(
        "f",
        vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        IRType::Object,
        body,
    );
    let (opt, _) = optimize_rc_ext_default(&decl);
    assert!(matches!(opt.body, IRBody::Set { .. }));
}

#[test]
fn test_edge_no_params() {
    // Nullary function: let x = Ctor(); ret x
    let body = vdecl_ctor(0, 0, vec![], IRBody::Ret(arg_var(0)));
    let decl = mk_decl("f", vec![], IRType::Object, body);
    let (opt, stats) = optimize_rc_ext_default(&decl);
    assert!(matches!(opt.body, IRBody::VDecl { .. }));
    assert_eq!(stats.incs_eliminated, 0);
}

#[test]
fn test_config_default_all_enabled() {
    let config = RcExtConfig::default();
    assert!(config.elision);
    assert!(config.borrowed_opt);
    assert!(config.last_use);
    assert!(config.sinking);
    assert!(config.combining);
    assert!(config.immutable_beans);
}

#[test]
fn test_optimize_rc_ext_default_wrapper() {
    let decl = identity_decl();
    let (opt, stats) = optimize_rc_ext_default(&decl);
    assert!(matches!(opt.body, IRBody::Ret(_)));
    assert_eq!(stats, RcExtStats::default());
}
