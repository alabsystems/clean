// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Optimization and edge case tests for extended tail call optimization.
//!
//! Split from tail_call_ext_tests.rs for file-size compliance.
//! Part of #3084 - IO/FFI/Native epic.

use super::tail_call_ext::*;
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;

// -----------------------------------------------------------------------
// Helpers (shared with tail_call_ext_tests.rs)
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

fn apply_expr(fname: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: fn_id(fname),
        args,
    }
}

fn bool_ctor(tag: u32, ctor_name: &str) -> CtorInfo {
    CtorInfo {
        name: Name::from_string(ctor_name),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn make_decl(fname: &str, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body,
    }
}

// -----------------------------------------------------------------------
// Tests: optimize_tail_calls_ext — direct TCO
// -----------------------------------------------------------------------

#[test]
fn test_optimize_direct_tco() {
    // f: let v1 = f(v0); ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", body)];
    let stats = optimize_tail_calls_ext(&mut decls, &TailCallExtConfig::default());
    assert_eq!(stats.direct_tco, 1);
}

#[test]
fn test_optimize_no_tail_calls() {
    // f: ret v0
    let mut decls = vec![make_decl("f", IRBody::Ret(arg_var(0)))];
    let stats = optimize_tail_calls_ext(&mut decls, &TailCallExtConfig::default());
    assert_eq!(stats.direct_tco, 0);
    assert_eq!(stats.accumulator_tco, 0);
    assert_eq!(stats.mutual_tco, 0);
}

#[test]
fn test_optimize_multiple_direct() {
    // f: let v1 = f(v0); ret v1
    // g: let v1 = g(v0); ret v1
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let g_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", f_body), make_decl("g", g_body)];
    let stats = optimize_tail_calls_ext(&mut decls, &TailCallExtConfig::default());
    assert_eq!(stats.direct_tco, 2);
}

#[test]
fn test_optimize_direct_tco_with_dec() {
    // f: let v1 = f(v0); dec v0; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let mut decls = vec![make_decl("f", body)];
    let stats = optimize_tail_calls_ext(&mut decls, &TailCallExtConfig::default());
    assert_eq!(stats.direct_tco, 1);
}

// -----------------------------------------------------------------------
// Tests: optimize_tail_calls_ext — mutual TCO
// -----------------------------------------------------------------------

#[test]
fn test_optimize_mutual_tco() {
    // f: let v1 = g(v0); ret v1
    // g: let v1 = f(v0); ret v1
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let g_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", f_body), make_decl("g", g_body)];
    let stats = optimize_tail_calls_ext(&mut decls, &TailCallExtConfig::default());
    assert_eq!(stats.mutual_tco, 1);
}

#[test]
fn test_optimize_mutual_disabled() {
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let g_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", f_body), make_decl("g", g_body)];
    let config = TailCallExtConfig {
        enable_mutual_tco: false,
        ..TailCallExtConfig::default()
    };
    let stats = optimize_tail_calls_ext(&mut decls, &config);
    assert_eq!(stats.mutual_tco, 0);
}

// -----------------------------------------------------------------------
// Tests: optimize_tail_calls_ext_default
// -----------------------------------------------------------------------

#[test]
fn test_optimize_default_wrapper() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", body)];
    let stats = optimize_tail_calls_ext_default(&mut decls);
    assert_eq!(stats.direct_tco, 1);
}

// -----------------------------------------------------------------------
// Tests: edge cases
// -----------------------------------------------------------------------

#[test]
fn test_unreachable_body() {
    let body = IRBody::Unreachable;
    let positions = detect_tail_positions(&body);
    assert!(positions.is_empty());
    assert!(!is_tail_recursive(&body, &fn_id("f")));
}

#[test]
fn test_empty_decls() {
    let mut decls: Vec<IRDecl> = vec![];
    let stats = optimize_tail_calls_ext(&mut decls, &TailCallExtConfig::default());
    assert_eq!(stats.direct_tco, 0);
    assert_eq!(stats.failed, 0);
}

#[test]
fn test_closure_apply_not_detected() {
    // let v1 = closure_apply(v0, [v0]); ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: arg_var(0),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let positions = detect_tail_positions(&body);
    assert!(positions.is_empty());
}

#[test]
fn test_partial_apply_not_detected() {
    // let v1 = partial_apply f [v0]; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id("f"),
            arity: 2,
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let positions = detect_tail_positions(&body);
    assert!(positions.is_empty());
}

#[test]
fn test_tail_position_in_join_point() {
    // jp(0) { let v1 = f(v0); ret v1 }
    // jmp jp(0) []
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
        rest: Box::new(IRBody::Jmp {
            jp: JoinPointId(0),
            args: vec![],
        }),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("f"));
}

#[test]
fn test_all_branches_tail_recursive() {
    // case v0 of
    //   | True => let v1 = f(v0); ret v1
    //   | False => let v2 = f(v0); ret v2
    //   | default => let v3 = f(v0); ret v3
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: bool_ctor(1, "Bool.true"),
                body: Box::new(IRBody::VDecl {
                    var: var(1),
                    ty: IRType::UInt64,
                    value: apply_expr("f", vec![arg_var(0)]),
                    rest: Box::new(IRBody::Ret(arg_var(1))),
                }),
            },
            IRAlt {
                ctor: bool_ctor(0, "Bool.false"),
                body: Box::new(IRBody::VDecl {
                    var: var(2),
                    ty: IRType::UInt64,
                    value: apply_expr("f", vec![arg_var(0)]),
                    rest: Box::new(IRBody::Ret(arg_var(2))),
                }),
            },
        ],
        default: Some(Box::new(IRBody::VDecl {
            var: var(3),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(3))),
        })),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 3);
    assert!(is_tail_recursive(&body, &fn_id("f")));
}

#[test]
fn test_detect_tail_through_set_tag() {
    // let v1 = f(v0); setTag v2 0; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::SetTag {
            var: var(2),
            tag: 0,
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
}

#[test]
fn test_ret_erased_not_tail() {
    // let v1 = f(v0); ret Erased
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(IRArg::Erased)),
    };
    let positions = detect_tail_positions(&body);
    assert!(positions.is_empty());
}

#[test]
fn test_return_different_var_not_tail() {
    // let v1 = f(v0); ret v0
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let positions = detect_tail_positions(&body);
    assert!(positions.is_empty());
}

#[test]
fn test_optimize_with_all_disabled() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", body)];
    let config = TailCallExtConfig {
        max_accumulator_params: 0,
        enable_mutual_tco: false,
        enable_accumulator_passing: false,
        enable_continuation_passing: false,
    };
    let stats = optimize_tail_calls_ext(&mut decls, &config);
    // Direct TCO always runs (not gated by config flag).
    assert_eq!(stats.direct_tco, 1);
    assert_eq!(stats.accumulator_tco, 0);
    assert_eq!(stats.mutual_tco, 0);
    assert_eq!(stats.continuation_tco, 0);
}

#[test]
fn test_optimize_continuation_on_tail_call() {
    // f: let v1 = f(v0); ret v1  — already a tail call,
    // continuation pass wraps with ret-JP.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", body)];
    let config = TailCallExtConfig {
        enable_continuation_passing: true,
        enable_mutual_tco: false,
        enable_accumulator_passing: false,
        ..TailCallExtConfig::default()
    };
    let stats = optimize_tail_calls_ext(&mut decls, &config);
    // Direct TCO fires first, then continuation should also fire
    // on the rewritten body (which still has a tail Apply).
    assert_eq!(stats.direct_tco, 1);
    // After direct TCO, the tail Apply is replaced with Jmp,
    // so continuation should find no more tail Applies.
    assert_eq!(stats.continuation_tco, 0);
}

#[test]
fn test_optimize_erased_return_continuation_fails() {
    // f: let v1 = g(v0); ret Erased  — not a tail call (returns Erased, not v1).
    // But after adding a non-erased-return tail call:
    // f: let v1 = g(v0); ret v1  + erased return elsewhere
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: bool_ctor(1, "Bool.true"),
            body: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::UInt64,
                value: apply_expr("g", vec![arg_var(0)]),
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Erased))),
    };
    let mut decls = vec![make_decl("f", body)];
    let config = TailCallExtConfig {
        enable_mutual_tco: false,
        enable_accumulator_passing: false,
        enable_continuation_passing: true,
        ..TailCallExtConfig::default()
    };
    let stats = optimize_tail_calls_ext(&mut decls, &config);
    // Contains erased return, so continuation should fail.
    assert!(stats.failed > 0);
}

#[test]
fn test_direct_tco_rewrites_body_to_loop() {
    // After direct TCO, the body should contain a JDecl (loop).
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", body)];
    let stats = optimize_tail_calls_ext(
        &mut decls,
        &TailCallExtConfig {
            enable_mutual_tco: false,
            enable_accumulator_passing: false,
            enable_continuation_passing: false,
            ..TailCallExtConfig::default()
        },
    );
    assert_eq!(stats.direct_tco, 1);
    // The rewritten body should be a JDecl (loop structure).
    assert!(matches!(decls[0].body, IRBody::JDecl { .. }));
}

#[test]
fn test_mutual_trampoline_rewrites_both_decls() {
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let g_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decl_f = make_decl("f", f_body);
    let mut decl_g = make_decl("g", g_body);
    let result = transform_mutual_to_trampoline(&mut decl_f, &mut decl_g);
    assert!(result);
    // Both should be rewritten to JDecl-based trampoline bodies.
    assert!(matches!(decl_f.body, IRBody::JDecl { .. }));
    assert!(matches!(decl_g.body, IRBody::JDecl { .. }));
}

#[test]
fn test_tail_position_struct_fields() {
    // Verify TailPosition struct fields.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    let tp = &positions[0];
    assert_eq!(tp.fn_id, fn_id("f"));
    assert_eq!(tp.args, vec![var(0)]);
    // Without context (current fn), these are false by default.
    assert!(!tp.is_self_recursive);
    assert!(!tp.is_mutual);
}

#[test]
fn test_error_display() {
    let err = TailCallExtError::IncompatibleMutualReturn;
    assert!(err.to_string().contains("equivalent return types"));

    let err2 = TailCallExtError::UnsupportedErasedReturn;
    assert!(err2.to_string().contains("erased"));
}
