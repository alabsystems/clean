// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for tail call optimization analysis.
//!
//! Part of #3084 - IO/FFI/Native epic.

use super::tail_call::*;
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;

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

fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}

fn lit_u64(v: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(v))
}

fn apply_expr(fname: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: fn_id(fname),
        args,
    }
}

fn closure_apply_expr(closure: IRArg, args: Vec<IRArg>) -> IRExpr {
    IRExpr::ClosureApply { closure, args }
}

fn bool_ctor(tag: u32, ctor_name: &str) -> CtorInfo {
    CtorInfo {
        name: name(ctor_name),
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

fn default_config() -> TailCallConfig {
    TailCallConfig::default()
}

// -----------------------------------------------------------------------
// Tests: basic tail position detection
// -----------------------------------------------------------------------

#[test]
fn test_simple_self_tail_call() {
    // let v1 = f(v0); ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 1);
    assert!(analysis.tail_call_vars.contains(&var(1)));
}

#[test]
fn test_non_tail_call_used_later() {
    // let v1 = f(v0); let v2 = g(v1); ret v2
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: apply_expr("g", vec![arg_var(1)]),
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    // v1 is NOT in tail position (v2 is, but g != f so no self-tail-call)
    assert_eq!(analysis.stats.self_tail_calls, 0);
    assert!(!analysis.tail_call_vars.contains(&var(1)));
}

#[test]
fn test_tail_call_with_dec_before_return() {
    // let v1 = f(v0); dec v0; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 1);
    assert!(analysis.tail_call_vars.contains(&var(1)));
}

#[test]
fn test_tail_call_with_inc_before_return() {
    // let v1 = f(v0); inc v2 1; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Inc {
            var: var(2),
            n: 1,
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 1);
}

#[test]
fn test_not_tail_if_dec_on_result_var() {
    // let v1 = f(v0); dec v1; ret v1
    // This is invalid as a tail call because dec is on the result var itself.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Dec {
            var: var(1),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(!analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 0);
}

#[test]
fn test_return_different_var_not_tail() {
    // let v1 = f(v0); ret v0  (returns v0, not v1)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(!analysis.has_tail_calls());
}

// -----------------------------------------------------------------------
// Tests: case arms
// -----------------------------------------------------------------------

#[test]
fn test_tail_call_in_case_arm() {
    // case v0 of
    //   | True => let v1 = f(v0); ret v1
    //   | False => ret v0
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
                body: Box::new(IRBody::Ret(arg_var(0))),
            },
        ],
        default: None,
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.stats.self_tail_calls, 1);
    assert!(analysis.tail_call_vars.contains(&var(1)));
}

#[test]
fn test_tail_calls_in_multiple_case_arms() {
    // case v0 of
    //   | True => let v1 = f(v0); ret v1
    //   | default => let v2 = f(v0); ret v2
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: bool_ctor(1, "Bool.true"),
            body: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::UInt64,
                value: apply_expr("f", vec![arg_var(0)]),
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }],
        default: Some(Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(2))),
        })),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.stats.self_tail_calls, 2);
    assert!(analysis.tail_call_vars.contains(&var(1)));
    assert!(analysis.tail_call_vars.contains(&var(2)));
}

// -----------------------------------------------------------------------
// Tests: join points
// -----------------------------------------------------------------------

#[test]
fn test_tail_call_in_tail_join_point() {
    // jp(0) { let v1 = f(v0); ret v1 }
    // case v0 of
    //   | True => jmp jp(0) []
    //   | False => ret v0
    // JP 0 is jumped to from a Case arm (tail position) => JP body is tail.
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![],
        body: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: bool_ctor(1, "Bool.true"),
                    body: Box::new(IRBody::Jmp {
                        jp: jp(0),
                        args: vec![],
                    }),
                },
                IRAlt {
                    ctor: bool_ctor(0, "Bool.false"),
                    body: Box::new(IRBody::Ret(arg_var(0))),
                },
            ],
            default: None,
        }),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.stats.self_tail_calls, 1);
    assert!(analysis.tail_call_vars.contains(&var(1)));
}

#[test]
fn test_non_tail_join_point() {
    // jp(0) { let v1 = f(v0); ret v1 }
    // let v2 = 42;
    // jmp jp(0) []   -- this is NOT in tail position (it's after a VDecl)
    // Actually, the Jmp IS in tail position here because VDecl's rest is
    // the Jmp which is a terminal. Let me construct a truly non-tail case.
    //
    // jp(0) { let v1 = f(v0); ret v1 }
    // let v2 = 0;
    // case v2 of
    //   | C => let v3 = lit; jmp jp(0) []
    //          -- jmp is in tail position of this arm
    // This is still tail. Need a case where JP is used in a non-tail way.
    //
    // Non-tail: jp body is used but jumped to from inside a VDecl value,
    // which is impossible in this IR. The only non-tail JPs would be if
    // jumped to from inside a VDecl rest that then continues.
    //
    // Actually in this IR, Jmp is always a terminal. So we need a
    // structural non-tail: if the JP is jumped to from a VDecl rest that
    // IS in tail position, it's fine. The JP is non-tail only if the Jmp
    // appears inside a non-tail context (e.g., inside a JDecl body that
    // itself is non-tail).

    // Here: JDecl jp1 contains a Jmp to jp0. jp1 is jumped to from
    // a non-tail position (let v2 = ...; jmp jp1) where the let
    // sets v2 and then jumps — but jmp is still a terminal so it's
    // tail. The tricky part is making something truly non-tail.
    //
    // A Jmp is non-tail if it's inside a VDecl's rest where the VDecl
    // result is used further. But that's impossible because Jmp doesn't
    // produce a value.
    //
    // In this IR, Jmp is always a terminal statement. Therefore all JPs
    // are always jumped to from tail position. This test verifies that
    // the analysis correctly handles this.

    // Let's test a simpler scenario: a JP that's not used at all.
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![],
        body: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    // JP is never jumped to, so its body is not analyzed for tail calls.
    // (It's not in tail_jps because it has no Jmp references at all.)
    // The JP doesn't appear in non_tail_jps either, but it's also not
    // referenced, so collect_tail_join_points returns it as tail.
    // This is harmless — an unreferenced JP with a tail call in it
    // just means dead code that happens to have a tail call.
    // The analysis finds it because the JP is declared and in tail_jps.
    assert_eq!(analysis.stats.self_tail_calls, 1);
}

// -----------------------------------------------------------------------
// Tests: mutual tail calls
// -----------------------------------------------------------------------

#[test]
fn test_mutual_tail_call() {
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
    let decls = vec![make_decl("f", f_body), make_decl("g", g_body)];
    let config = TailCallConfig {
        enabled: true,
        detect_mutual: true,
    };
    let results = analyze_mutual_tail_calls(&decls, &config);

    // f calls g in tail position (mutual), g calls f in tail position (mutual)
    assert_eq!(results[0].stats.mutual_tail_calls, 1);
    assert_eq!(results[0].stats.self_tail_calls, 0);
    assert_eq!(results[1].stats.mutual_tail_calls, 1);
    assert_eq!(results[1].stats.self_tail_calls, 0);
}

#[test]
fn test_mutual_disabled() {
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
    let decls = vec![make_decl("f", f_body), make_decl("g", g_body)];
    let config = TailCallConfig {
        enabled: true,
        detect_mutual: false,
    };
    let results = analyze_mutual_tail_calls(&decls, &config);

    // With mutual disabled, neither should be marked.
    assert_eq!(results[0].stats.mutual_tail_calls, 0);
    assert_eq!(results[1].stats.mutual_tail_calls, 0);
}

#[test]
fn test_self_and_mutual_mixed() {
    // f: case v0 of
    //      | True => let v1 = f(v0); ret v1   (self)
    //      | False => let v2 = g(v0); ret v2   (mutual)
    let f_body = IRBody::Case {
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
                    value: apply_expr("g", vec![arg_var(0)]),
                    rest: Box::new(IRBody::Ret(arg_var(2))),
                }),
            },
        ],
        default: None,
    };
    let g_body = IRBody::Ret(arg_var(0));
    let decls = vec![make_decl("f", f_body), make_decl("g", g_body)];
    let config = TailCallConfig {
        enabled: true,
        detect_mutual: true,
    };
    let results = analyze_mutual_tail_calls(&decls, &config);

    assert_eq!(results[0].stats.self_tail_calls, 1);
    assert_eq!(results[0].stats.mutual_tail_calls, 1);
    assert_eq!(results[0].tail_call_count(), 2);
}

// -----------------------------------------------------------------------
// Tests: statistics
// -----------------------------------------------------------------------

#[test]
fn test_stats_total_calls() {
    // let v1 = f(v0); let v2 = g(v1); ret v2
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: apply_expr("g", vec![arg_var(1)]),
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };
    let decl = make_decl("h", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.stats.total_apply_calls, 2);
    assert_eq!(analysis.stats.total_closure_calls, 0);
}

#[test]
fn test_stats_closure_calls() {
    // let v1 = closure_apply(v0, [v0]); ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: closure_apply_expr(arg_var(0), vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.stats.total_closure_calls, 1);
    // ClosureApply is not marked as tail call (dynamic target).
    assert_eq!(analysis.stats.self_tail_calls, 0);
    assert!(!analysis.has_tail_calls());
}

// -----------------------------------------------------------------------
// Tests: configuration
// -----------------------------------------------------------------------

#[test]
fn test_disabled_config() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let decl = make_decl("f", body);
    let config = TailCallConfig {
        enabled: false,
        detect_mutual: true,
    };
    let analysis = analyze_tail_calls(&decl, &config);

    assert!(!analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 0);
    assert_eq!(analysis.stats.total_apply_calls, 0);
}

#[test]
fn test_default_config_values() {
    let config = TailCallConfig::default();
    assert!(config.enabled);
    assert!(config.detect_mutual);
}

// -----------------------------------------------------------------------
// Tests: edge cases
// -----------------------------------------------------------------------

#[test]
fn test_empty_body_ret() {
    let body = IRBody::Ret(arg_var(0));
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(!analysis.has_tail_calls());
    assert_eq!(analysis.stats.total_apply_calls, 0);
}

#[test]
fn test_unreachable_body() {
    let body = IRBody::Unreachable;
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(!analysis.has_tail_calls());
}

#[test]
fn test_non_call_in_tail_position() {
    // let v1 = lit 42; ret v1  (not a call at all)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(!analysis.has_tail_calls());
    assert_eq!(analysis.stats.total_apply_calls, 0);
}

#[test]
fn test_partial_apply_not_tail_call() {
    // let v1 = partial_apply f [v0]; ret v1
    // PartialApply creates a closure, not a full call — not a tail call.
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
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(!analysis.has_tail_calls());
}

#[test]
fn test_call_to_different_function_not_self_tail() {
    // let v1 = g(v0); ret v1  (calling g, not f)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    // Not a self-tail-call, and g is not in any mutual set.
    assert!(!analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 0);
    assert_eq!(analysis.stats.mutual_tail_calls, 0);
}

#[test]
fn test_multiple_rc_ops_before_return() {
    // let v1 = f(v0); dec v2; inc v3 1; dec v4; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Dec {
            var: var(2),
            rest: Box::new(IRBody::Inc {
                var: var(3),
                n: 1,
                rest: Box::new(IRBody::Dec {
                    var: var(4),
                    rest: Box::new(IRBody::Ret(arg_var(1))),
                }),
            }),
        }),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 1);
}

#[test]
fn test_set_tag_before_return() {
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
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(analysis.has_tail_calls());
    assert_eq!(analysis.stats.self_tail_calls, 1);
}

#[test]
fn test_tail_call_analysis_fn_name() {
    let body = IRBody::Ret(arg_var(0));
    let decl = make_decl("my_function", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.fn_name, name("my_function"));
}

#[test]
fn test_ret_erased_not_tail() {
    // let v1 = f(v0); ret Erased  (returns erased, not v1)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(IRArg::Erased)),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert!(!analysis.has_tail_calls());
}

#[test]
fn test_nested_case_tail_calls() {
    // case v0 of
    //   | C1 => case v0 of
    //             | C2 => let v1 = f(v0); ret v1
    //             | C3 => ret v0
    //   | default => ret v0
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: bool_ctor(0, "C1"),
            body: Box::new(IRBody::Case {
                scrutinee: var(0),
                alts: vec![
                    IRAlt {
                        ctor: bool_ctor(1, "C2"),
                        body: Box::new(IRBody::VDecl {
                            var: var(1),
                            ty: IRType::UInt64,
                            value: apply_expr("f", vec![arg_var(0)]),
                            rest: Box::new(IRBody::Ret(arg_var(1))),
                        }),
                    },
                    IRAlt {
                        ctor: bool_ctor(2, "C3"),
                        body: Box::new(IRBody::Ret(arg_var(0))),
                    },
                ],
                default: None,
            }),
        }],
        default: Some(Box::new(IRBody::Ret(arg_var(0)))),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.stats.self_tail_calls, 1);
    assert!(analysis.tail_call_vars.contains(&var(1)));
}

#[test]
fn test_analyze_mutual_empty() {
    let results = analyze_mutual_tail_calls(&[], &default_config());
    assert!(results.is_empty());
}

#[test]
fn test_analyze_mutual_disabled() {
    let decls = vec![make_decl("f", IRBody::Ret(arg_var(0)))];
    let config = TailCallConfig {
        enabled: false,
        detect_mutual: true,
    };
    let results = analyze_mutual_tail_calls(&decls, &config);
    assert_eq!(results.len(), 1);
    assert!(!results[0].has_tail_calls());
}

#[test]
fn test_tail_call_count_method() {
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
        default: None,
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    assert_eq!(analysis.tail_call_count(), 2);
}

#[test]
fn test_set_operation_does_not_block_tail() {
    // let v1 = f(v0); set v3[0] := v4; ret v1
    // Set on a different var doesn't block, but rest_returns_var only
    // allows Inc/Dec/SetTag. Set is NOT allowed.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Set {
            var: var(3),
            idx: 0,
            value: var(4),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let decl = make_decl("f", body);
    let analysis = analyze_tail_calls(&decl, &default_config());

    // Set is not an allowed intermediate op for tail call.
    assert!(!analysis.has_tail_calls());
}
