// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended tail call optimization — analysis and detection.
//!
//! Optimization and edge case tests are in tail_call_ext_opt_tests.rs.
//! Part of #3084 - IO/FFI/Native epic.

use super::tail_call_ext::*;
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

// -----------------------------------------------------------------------
// Tests: TailCallExtConfig
// -----------------------------------------------------------------------

#[test]
fn test_default_config() {
    let config = TailCallExtConfig::default();
    assert_eq!(config.max_accumulator_params, 4);
    assert!(config.enable_mutual_tco);
    assert!(config.enable_accumulator_passing);
    assert!(config.enable_continuation_passing);
}

#[test]
fn test_custom_config() {
    let config = TailCallExtConfig {
        max_accumulator_params: 2,
        enable_mutual_tco: false,
        enable_accumulator_passing: true,
        enable_continuation_passing: false,
    };
    assert_eq!(config.max_accumulator_params, 2);
    assert!(!config.enable_mutual_tco);
    assert!(config.enable_accumulator_passing);
    assert!(!config.enable_continuation_passing);
}

// -----------------------------------------------------------------------
// Tests: TailCallExtStats
// -----------------------------------------------------------------------

#[test]
fn test_stats_default() {
    let stats = TailCallExtStats::default();
    assert_eq!(stats.direct_tco, 0);
    assert_eq!(stats.accumulator_tco, 0);
    assert_eq!(stats.mutual_tco, 0);
    assert_eq!(stats.continuation_tco, 0);
    assert_eq!(stats.failed, 0);
}

#[test]
fn test_stats_equality() {
    let a = TailCallExtStats {
        direct_tco: 1,
        accumulator_tco: 2,
        mutual_tco: 3,
        continuation_tco: 4,
        failed: 5,
        ..TailCallExtStats::default()
    };
    let b = TailCallExtStats {
        direct_tco: 1,
        accumulator_tco: 2,
        mutual_tco: 3,
        continuation_tco: 4,
        failed: 5,
        ..TailCallExtStats::default()
    };
    assert_eq!(a, b);
}

#[test]
fn test_stats_inequality() {
    let a = TailCallExtStats::default();
    let b = TailCallExtStats {
        direct_tco: 1,
        ..TailCallExtStats::default()
    };
    assert_ne!(a, b);
}

// -----------------------------------------------------------------------
// Tests: detect_tail_positions — simple return
// -----------------------------------------------------------------------

#[test]
fn test_detect_tail_simple_return() {
    // let v1 = f(v0); ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("f"));
    assert_eq!(positions[0].args, vec![var(0)]);
}

#[test]
fn test_detect_tail_no_call() {
    // let v1 = lit 42; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let positions = detect_tail_positions(&body);
    assert!(positions.is_empty());
}

#[test]
fn test_detect_tail_non_tail_call() {
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
    let positions = detect_tail_positions(&body);
    // Only g is in tail position, f is not.
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("g"));
}

// -----------------------------------------------------------------------
// Tests: detect_tail_positions — through let bindings
// -----------------------------------------------------------------------

#[test]
fn test_detect_tail_through_let_binding() {
    // let v1 = lit 0; let v2 = f(v1); ret v2
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(0),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(1)]),
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("f"));
}

#[test]
fn test_detect_tail_with_rc_ops_before_return() {
    // let v1 = f(v0); dec v0; inc v3 1; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Inc {
                var: var(3),
                n: 1,
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("f"));
}

// -----------------------------------------------------------------------
// Tests: detect_tail_positions — through case branches
// -----------------------------------------------------------------------

#[test]
fn test_detect_tail_in_case_branches() {
    // case v0 of
    //   | True => let v1 = f(v0); ret v1
    //   | False => let v2 = g(v0); ret v2
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
                    value: apply_expr("g", vec![arg_var(0)]),
                    rest: Box::new(IRBody::Ret(arg_var(2))),
                }),
            },
        ],
        default: None,
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 2);
    let fn_ids: Vec<FnId> = positions.iter().map(|p| p.fn_id.clone()).collect();
    assert!(fn_ids.contains(&fn_id("f")));
    assert!(fn_ids.contains(&fn_id("g")));
}

#[test]
fn test_detect_tail_in_case_default() {
    // case v0 of
    //   | True => ret v0
    //   | default => let v1 = f(v0); ret v1
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: bool_ctor(1, "Bool.true"),
            body: Box::new(IRBody::Ret(arg_var(0))),
        }],
        default: Some(Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        })),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("f"));
}

#[test]
fn test_detect_tail_nested_case() {
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
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("f"));
}

// -----------------------------------------------------------------------
// Tests: is_tail_recursive
// -----------------------------------------------------------------------

#[test]
fn test_is_tail_recursive_true() {
    // let v1 = f(v0); ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(is_tail_recursive(&body, &fn_id("f")));
}

#[test]
fn test_is_tail_recursive_false_different_fn() {
    // let v1 = g(v0); ret v1  (calls g, not f)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(!is_tail_recursive(&body, &fn_id("f")));
}

#[test]
fn test_is_tail_recursive_no_calls() {
    let body = IRBody::Ret(arg_var(0));
    assert!(!is_tail_recursive(&body, &fn_id("f")));
}

#[test]
fn test_is_tail_recursive_non_tail_position() {
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
    // f is not in tail position.
    assert!(!is_tail_recursive(&body, &fn_id("f")));
}

#[test]
fn test_is_tail_recursive_in_case_arm() {
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
    assert!(is_tail_recursive(&body, &fn_id("f")));
}

// -----------------------------------------------------------------------
// Tests: detect_mutual_tail_calls
// -----------------------------------------------------------------------

#[test]
fn test_detect_mutual_pair() {
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
    let pairs = detect_mutual_tail_calls(&decls);
    assert_eq!(pairs.len(), 1);
    let (a, b) = &pairs[0];
    let names: Vec<&Name> = vec![&a.0, &b.0];
    assert!(names.contains(&&name("f")));
    assert!(names.contains(&&name("g")));
}

#[test]
fn test_detect_mutual_no_mutual() {
    // f: let v1 = g(v0); ret v1
    // g: ret v0  (does NOT call f back)
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let g_body = IRBody::Ret(arg_var(0));
    let decls = vec![make_decl("f", f_body), make_decl("g", g_body)];
    let pairs = detect_mutual_tail_calls(&decls);
    assert!(pairs.is_empty());
}

#[test]
fn test_detect_mutual_self_recursive_not_mutual() {
    // f: let v1 = f(v0); ret v1  (self-recursive, not mutual)
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let decls = vec![make_decl("f", f_body)];
    let pairs = detect_mutual_tail_calls(&decls);
    assert!(pairs.is_empty());
}

#[test]
fn test_detect_mutual_empty_decls() {
    let pairs = detect_mutual_tail_calls(&[]);
    assert!(pairs.is_empty());
}

// -----------------------------------------------------------------------
// Tests: transform_accumulator_passing
// -----------------------------------------------------------------------

#[test]
fn test_accumulator_passing_empty_params() {
    // Empty accum_params should return false.
    let body = IRBody::Ret(arg_var(0));
    let mut decl = make_decl("f", body);
    let result = transform_accumulator_passing(&mut decl, &[]);
    assert!(!result);
}

// -----------------------------------------------------------------------
// Tests: transform_mutual_to_trampoline
// -----------------------------------------------------------------------

#[test]
fn test_trampoline_basic() {
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
    let mut decl_f = make_decl("f", f_body);
    let mut decl_g = make_decl("g", g_body);
    let result = transform_mutual_to_trampoline(&mut decl_f, &mut decl_g);
    assert!(result);
}

#[test]
fn test_trampoline_no_mutual() {
    // f: ret v0
    // g: ret v0
    let mut decl_f = make_decl("f", IRBody::Ret(arg_var(0)));
    let mut decl_g = make_decl("g", IRBody::Ret(arg_var(0)));
    let result = transform_mutual_to_trampoline(&mut decl_f, &mut decl_g);
    assert!(!result);
}

#[test]
fn test_trampoline_one_direction_only() {
    // f: let v1 = g(v0); ret v1
    // g: ret v0  (no call to f)
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decl_f = make_decl("f", f_body);
    let mut decl_g = make_decl("g", IRBody::Ret(arg_var(0)));
    let result = transform_mutual_to_trampoline(&mut decl_f, &mut decl_g);
    assert!(!result);
}

#[test]
fn test_trampoline_incompatible_types() {
    // f returns UInt64, g returns Object — should fail.
    let f_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("g", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let g_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decl_f = make_decl("f", f_body);
    let mut decl_g = IRDecl {
        name: name("g"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: g_body,
    };
    let result = transform_mutual_to_trampoline(&mut decl_f, &mut decl_g);
    // UInt64 vs Object are not eqv_types, so should fail.
    assert!(!result);
}

// -----------------------------------------------------------------------
// Tests: erased args in tail position detection
// -----------------------------------------------------------------------

#[test]
fn test_erased_args_produces_tail_position_with_filtered_args() {
    // detect_tail_positions uses filter_map: Erased args are skipped in the
    // args vec but the TailPosition is still created.
    // let v1 = f(v0, Erased); ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("f"),
            args: vec![arg_var(0), IRArg::Erased],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    // Only non-erased args appear in the args vec.
    assert_eq!(positions[0].args, vec![var(0)]);
}

// -----------------------------------------------------------------------
// Tests: has_observable_side_effects — conservative analysis
// -----------------------------------------------------------------------

#[test]
fn test_no_side_effects_simple_tail_call() {
    // let v1 = f(v0); ret v1 — no mutation, safe to optimize.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(!has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_side_effects_set_before_tail_call() {
    // set v0[0] = v2; let v1 = f(v0); ret v1
    // v0 is mutated then passed to f — observable side effect.
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(2),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    assert!(has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_side_effects_uset_before_tail_call() {
    // uset v0[0] = v2; let v1 = f(v0); ret v1
    let body = IRBody::USet {
        var: var(0),
        idx: 0,
        value: var(2),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    assert!(has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_side_effects_sset_before_tail_call() {
    // sset v0[0,0] = v2 : UInt64; let v1 = f(v0); ret v1
    let body = IRBody::SSet {
        var: var(0),
        n: 0,
        offset: 0,
        value: var(2),
        ty: IRType::UInt64,
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    assert!(has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_no_side_effects_set_different_var() {
    // set v3[0] = v2; let v1 = f(v0); ret v1
    // v3 is mutated but v0 is passed to f — no conflict.
    let body = IRBody::Set {
        var: var(3),
        idx: 0,
        value: var(2),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    assert!(!has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_no_side_effects_no_tail_call() {
    // set v0[0] = v2; let v1 = g(v0); ret v1
    // Mutation + call to g, not f — no conflict for f.
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(2),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("g", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    assert!(!has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_no_side_effects_return_only() {
    let body = IRBody::Ret(arg_var(0));
    assert!(!has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_no_side_effects_unreachable() {
    let body = IRBody::Unreachable;
    assert!(!has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_side_effects_in_case_branch() {
    // case v0 of
    //   | True => set v0[0] = v2; let v1 = f(v0); ret v1
    //   | False => ret v0
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: bool_ctor(1, "Bool.true"),
                body: Box::new(IRBody::Set {
                    var: var(0),
                    idx: 0,
                    value: var(2),
                    rest: Box::new(IRBody::VDecl {
                        var: var(1),
                        ty: IRType::UInt64,
                        value: apply_expr("f", vec![arg_var(0)]),
                        rest: Box::new(IRBody::Ret(arg_var(1))),
                    }),
                }),
            },
            IRAlt {
                ctor: bool_ctor(0, "Bool.false"),
                body: Box::new(IRBody::Ret(arg_var(0))),
            },
        ],
        default: None,
    };
    assert!(has_observable_side_effects(&body, &fn_id("f")));
}

#[test]
fn test_no_side_effects_mutation_after_call() {
    // let v1 = f(v0); set v3[0] = v2; ret v1
    // Mutation happens after the call — this is NOT a tail call anyway
    // since the rest does not immediately return v1.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Set {
            var: var(3),
            idx: 0,
            value: var(2),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    // Not a side-effect issue because there's no mutation BEFORE the tail call.
    assert!(!has_observable_side_effects(&body, &fn_id("f")));
}

// -----------------------------------------------------------------------
// Tests: TailCallExtStats — enhanced fields
// -----------------------------------------------------------------------

#[test]
fn test_stats_total_optimized() {
    let stats = TailCallExtStats {
        direct_tco: 2,
        accumulator_tco: 1,
        mutual_tco: 3,
        continuation_tco: 1,
        failed: 0,
        tail_positions_found: 10,
        join_point_propagations: 5,
        conservative_skips: 0,
    };
    assert_eq!(stats.total_optimized(), 7);
}

#[test]
fn test_stats_enhanced_fields_default() {
    let stats = TailCallExtStats::default();
    assert_eq!(stats.tail_positions_found, 0);
    assert_eq!(stats.join_point_propagations, 0);
    assert_eq!(stats.conservative_skips, 0);
}

#[test]
fn test_stats_tail_positions_counted() {
    // f: let v1 = f(v0); ret v1  — 1 tail position
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let mut decls = vec![make_decl("f", body)];
    let config = TailCallExtConfig {
        enable_mutual_tco: false,
        enable_accumulator_passing: false,
        enable_continuation_passing: false,
        ..TailCallExtConfig::default()
    };
    let stats = optimize_tail_calls_ext(&mut decls, &config);
    assert_eq!(stats.tail_positions_found, 1);
}

#[test]
fn test_stats_conservative_skips_counted() {
    // set v0[0] = v2; let v1 = f(v0); ret v1 — should be skipped
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(2),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let mut decls = vec![make_decl("f", body)];
    let config = TailCallExtConfig {
        enable_mutual_tco: false,
        enable_accumulator_passing: false,
        enable_continuation_passing: false,
        ..TailCallExtConfig::default()
    };
    let stats = optimize_tail_calls_ext(&mut decls, &config);
    assert_eq!(stats.conservative_skips, 1);
    assert_eq!(stats.direct_tco, 0); // Skipped due to side effects.
}

#[test]
fn test_stats_join_point_propagations_with_jp() {
    // jp(0) { let v1 = f(v0); ret v1 } jmp jp(0) []
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![],
        body: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply_expr("f", vec![arg_var(0)]),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![],
        }),
    };
    let mut decls = vec![make_decl("f", body)];
    let config = TailCallExtConfig {
        enable_mutual_tco: false,
        enable_accumulator_passing: false,
        enable_continuation_passing: false,
        ..TailCallExtConfig::default()
    };
    let stats = optimize_tail_calls_ext(&mut decls, &config);
    // JP 0 is in tail position (its only use is the final jmp).
    assert!(stats.join_point_propagations >= 1);
}

// -----------------------------------------------------------------------
// Tests: detect_tail_positions — through inc/dec/set ops
// -----------------------------------------------------------------------

#[test]
fn test_detect_tail_through_inc_and_dec() {
    // let v1 = f(v0); inc v3 2; dec v4; ret v1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: apply_expr("f", vec![arg_var(0)]),
        rest: Box::new(IRBody::Inc {
            var: var(3),
            n: 2,
            rest: Box::new(IRBody::Dec {
                var: var(4),
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }),
    };
    let positions = detect_tail_positions(&body);
    assert_eq!(positions.len(), 1);
    assert_eq!(positions[0].fn_id, fn_id("f"));
}
