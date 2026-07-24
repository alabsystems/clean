// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR function inlining pass.
//!
//! Part of #3084 - IO/FFI/Native epic.

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
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

fn lit_u64(v: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(v))
}

fn make_decl(n: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(n),
        params,
        return_type: IRType::UInt64,
        body,
    }
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

// =======================================================================
// Size estimation tests
// =======================================================================

#[test]
fn test_estimate_size_ret() {
    let body = IRBody::Ret(arg_var(0));
    assert_eq!(estimate_size(&body), 1);
}

#[test]
fn test_estimate_size_unreachable() {
    assert_eq!(estimate_size(&IRBody::Unreachable), 1);
}

#[test]
fn test_estimate_size_vdecl_chain() {
    // let v0 := 1; let v1 := 2; ret v1
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(1),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: lit_u64(2),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    assert_eq!(estimate_size(&body), 3);
}

#[test]
fn test_estimate_size_case() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(IRBody::Ret(arg_var(1))),
        }],
        default: Some(Box::new(IRBody::Ret(arg_var(2)))),
    };
    // 1 (case) + 1 (alt body) + 1 (default) = 3
    assert_eq!(estimate_size(&body), 3);
}

#[test]
fn test_estimate_size_inc_dec() {
    let body = IRBody::Inc {
        var: var(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        }),
    };
    // inc + dec + ret = 3
    assert_eq!(estimate_size(&body), 3);
}

#[test]
fn test_estimate_size_jdecl() {
    let body = IRBody::JDecl {
        jp: crate::ir::JoinPointId(0),
        params: vec![],
        body: Box::new(IRBody::Ret(arg_var(0))),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    // 1 (jdecl) + 1 (jp body) + 1 (rest) = 3
    assert_eq!(estimate_size(&body), 3);
}

// =======================================================================
// Call counting tests
// =======================================================================

#[test]
fn test_call_counts_empty() {
    let counts = compute_call_counts(&[]);
    assert!(counts.is_empty());
}

#[test]
fn test_call_counts_single_call() {
    let decl = make_decl(
        "main",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("helper"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );
    let counts = compute_call_counts(&[decl]);
    assert_eq!(counts.get(&name("helper")), Some(&1));
}

#[test]
fn test_call_counts_multiple_calls() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("f"),
            args: vec![],
        },
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("f"),
                args: vec![],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: fn_id("g"),
                    args: vec![],
                },
                rest: Box::new(IRBody::Ret(arg_var(2))),
            }),
        }),
    };
    let decl = make_decl("main", vec![], body);
    let counts = compute_call_counts(&[decl]);
    assert_eq!(counts.get(&name("f")), Some(&2));
    assert_eq!(counts.get(&name("g")), Some(&1));
}

// =======================================================================
// Inline decision tests
// =======================================================================

#[test]
fn test_should_inline_always_attr() {
    let decl = make_decl("f", vec![], IRBody::Ret(arg_var(0)));
    let decision = should_inline(&decl, &InlineAttr::Always, 5, &InlinePassConfig::default());
    assert_eq!(decision, InlineDecision::Always);
}

#[test]
fn test_should_inline_noinline_attr() {
    let decl = make_decl("f", vec![], IRBody::Ret(arg_var(0)));
    let decision = should_inline(
        &decl,
        &InlineAttr::NoInline,
        5,
        &InlinePassConfig::default(),
    );
    assert_eq!(decision, InlineDecision::No);
}

#[test]
fn test_should_inline_inline_attr() {
    let decl = make_decl("f", vec![], IRBody::Ret(arg_var(0)));
    let decision = should_inline(&decl, &InlineAttr::Inline, 5, &InlinePassConfig::default());
    assert_eq!(decision, InlineDecision::Yes);
}

#[test]
fn test_should_inline_once_used() {
    // Big function (size > threshold) but called once
    let mut body = IRBody::Ret(arg_var(50));
    for i in (0..50).rev() {
        body = IRBody::VDecl {
            var: var(i),
            ty: IRType::UInt64,
            value: lit_u64(i as u64),
            rest: Box::new(body),
        };
    }
    let decl = make_decl("big_fn", vec![], body);
    let decision = should_inline(&decl, &InlineAttr::None, 1, &InlinePassConfig::default());
    assert_eq!(decision, InlineDecision::OnceOnly);
}

#[test]
fn test_should_inline_small_auto() {
    // Small function, no annotation, called multiple times
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let decl = make_decl("f", vec![], body);
    let decision = should_inline(&decl, &InlineAttr::None, 5, &InlinePassConfig::default());
    assert_eq!(decision, InlineDecision::Yes);
}

#[test]
fn test_should_inline_too_large() {
    let mut body = IRBody::Ret(arg_var(30));
    for i in (0..30).rev() {
        body = IRBody::VDecl {
            var: var(i),
            ty: IRType::UInt64,
            value: lit_u64(i as u64),
            rest: Box::new(body),
        };
    }
    let decl = make_decl("big", vec![], body);
    let config = InlinePassConfig {
        inline_once_used: false,
        ..InlinePassConfig::default()
    };
    let decision = should_inline(&decl, &InlineAttr::None, 3, &config);
    assert_eq!(decision, InlineDecision::No);
}

#[test]
fn test_should_inline_recursive_rejected() {
    // f calls itself
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("rec_fn"),
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let decl = make_decl("rec_fn", vec![], body);
    let decision = should_inline(&decl, &InlineAttr::None, 5, &InlinePassConfig::default());
    assert_eq!(decision, InlineDecision::No);
}

#[test]
fn test_should_inline_annotations_disabled() {
    let decl = make_decl("f", vec![], IRBody::Ret(arg_var(0)));
    let config = InlinePassConfig {
        respect_annotations: false,
        ..InlinePassConfig::default()
    };
    // Always attr should be ignored, falls through to size heuristic
    let decision = should_inline(&decl, &InlineAttr::Always, 5, &config);
    assert_eq!(decision, InlineDecision::Yes); // small enough
}

// =======================================================================
// Argument substitution tests
// =======================================================================

#[test]
fn test_substitute_args_simple() {
    // Body: ret v0 (param)
    // Call: f(v10)
    // Result: ret v10
    let body = IRBody::Ret(arg_var(0));
    let params = vec![(var(0), IRType::UInt64)];
    let args = vec![arg_var(10)];
    let result = substitute_args(&body, &params, &args, 100);
    assert!(matches!(result, IRBody::Ret(IRArg::Var(VarId(10)))));
}

#[test]
fn test_substitute_args_with_local() {
    // Body: let v1 := 42; ret v1
    // Params: v0
    // Args: v10
    // Result: let v101 := 42; ret v101 (local shifted by offset)
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let params = vec![(var(0), IRType::UInt64)];
    let args = vec![arg_var(10)];
    let result = substitute_args(&body, &params, &args, 100);
    // Local v1 should be shifted to v101
    if let IRBody::VDecl { var: v, rest, .. } = &result {
        assert_eq!(v.0, 101, "local var should be shifted");
        assert!(matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(VarId(101)))));
    } else {
        panic!("expected VDecl");
    }
}

#[test]
fn test_substitute_args_erased() {
    let body = IRBody::Ret(IRArg::Erased);
    let params = vec![(var(0), IRType::UInt64)];
    let args = vec![arg_var(10)];
    let result = substitute_args(&body, &params, &args, 100);
    assert!(matches!(result, IRBody::Ret(IRArg::Erased)));
}

#[test]
fn test_substitute_args_expr_apply() {
    // Body: let v1 := g(v0); ret v1
    // Param v0, arg v10
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Apply {
            fn_id: fn_id("g"),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let result = substitute_args(&body, &[(var(0), IRType::UInt64)], &[arg_var(10)], 100);
    if let IRBody::VDecl { value, .. } = &result {
        if let IRExpr::Apply { args, .. } = value {
            assert_eq!(args[0], IRArg::Var(VarId(10)));
        } else {
            panic!("expected Apply");
        }
    } else {
        panic!("expected VDecl");
    }
}

// =======================================================================
// Full pass tests
// =======================================================================

#[test]
fn test_run_inline_pass_simple_inline() {
    // helper: let v0 := 42; ret v0
    let helper = make_decl(
        "helper",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: lit_u64(42),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    // main: let v0 := helper(); ret v0
    let main_fn = make_decl(
        "main",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("helper"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig::default();
    let (result, stats) = run_inline_pass(&[helper, main_fn], &attrs, &config);

    assert_eq!(stats.inlined_calls, 1, "should inline the helper call");
    // The main function should no longer contain a call to "helper"
    let main_body = &result
        .iter()
        .find(|d| d.name == name("main"))
        .expect("main")
        .body;
    assert!(
        !body_references_name(main_body, &name("helper")),
        "helper call should be inlined away"
    );
}

#[test]
fn test_run_inline_pass_noinline_respected() {
    let helper = make_decl("noinline_fn", vec![], IRBody::Ret(arg_var(0)));

    let main_fn = make_decl(
        "main",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("noinline_fn"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let mut attrs = HashMap::new();
    attrs.insert(name("noinline_fn"), InlineAttr::NoInline);
    let config = InlinePassConfig::default();
    let (_, stats) = run_inline_pass(&[helper, main_fn], &attrs, &config);

    assert_eq!(stats.inlined_calls, 0);
    assert_eq!(stats.skipped_noinline, 1);
}

#[test]
fn test_run_inline_pass_always_inline() {
    // Large function but always_inline
    let mut big_body = IRBody::Ret(arg_var(30));
    for i in (0..30).rev() {
        big_body = IRBody::VDecl {
            var: var(i),
            ty: IRType::UInt64,
            value: lit_u64(i as u64),
            rest: Box::new(big_body),
        };
    }
    let helper = make_decl("always_fn", vec![], big_body);

    let main_fn = make_decl(
        "main",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("always_fn"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let mut attrs = HashMap::new();
    attrs.insert(name("always_fn"), InlineAttr::Always);
    let config = InlinePassConfig {
        inline_once_used: false,
        ..InlinePassConfig::default()
    };
    let (_, stats) = run_inline_pass(&[helper, main_fn], &attrs, &config);

    assert_eq!(stats.inlined_calls, 1, "always_inline should override size");
}

#[test]
fn test_run_inline_pass_recursive_skipped() {
    // rec_fn: let v0 := rec_fn(); ret v0
    let rec_fn = make_decl(
        "rec_fn",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("rec_fn"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let main_fn = make_decl(
        "main",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("rec_fn"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig::default();
    let (_, stats) = run_inline_pass(&[rec_fn, main_fn], &attrs, &config);

    assert!(
        stats.skipped_recursive > 0,
        "recursive calls should be skipped"
    );
    assert_eq!(stats.inlined_calls, 0);
}

#[test]
fn test_run_inline_pass_depth_limit() {
    // Chain: a calls b calls c calls d
    // With depth limit 1, only one level should inline
    let d_fn = make_decl(
        "d",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: lit_u64(99),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let c_fn = make_decl(
        "c",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("d"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let b_fn = make_decl(
        "b",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("c"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let a_fn = make_decl(
        "a",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("b"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig {
        max_inline_depth: 1,
        ..InlinePassConfig::default()
    };
    let (_, stats) = run_inline_pass(&[d_fn, c_fn, b_fn, a_fn], &attrs, &config);

    // Depth limit 1 means only the first level of inlining succeeds per decl
    assert!(
        stats.inlined_calls >= 1,
        "at least one call should be inlined"
    );
}

#[test]
fn test_run_inline_pass_with_args() {
    // add(x, y): let v2 := Nat.add(x, y); ret v2
    let add_fn = make_decl(
        "add",
        vec![(var(0), IRType::UInt64), (var(1), IRType::UInt64)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("Nat.add"),
                args: vec![arg_var(0), arg_var(1)],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        },
    );

    // main: let v0 := add(v10, v11); ret v0
    let main_fn = make_decl(
        "main",
        vec![(var(10), IRType::UInt64), (var(11), IRType::UInt64)],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("add"),
                args: vec![arg_var(10), arg_var(11)],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig::default();
    let (result, stats) = run_inline_pass(&[add_fn, main_fn], &attrs, &config);

    assert_eq!(stats.inlined_calls, 1);
    // After inlining, main should call Nat.add directly (not add)
    let main_body = &result
        .iter()
        .find(|d| d.name == name("main"))
        .expect("main")
        .body;
    assert!(
        !body_references_name(main_body, &name("add")),
        "add call should be inlined"
    );
    assert!(
        body_references_name(main_body, &name("Nat.add")),
        "Nat.add should appear in inlined body"
    );
}

#[test]
fn test_run_inline_pass_stats_tracking() {
    let small_fn = make_decl("small", vec![], IRBody::Ret(arg_var(0)));

    let big_body = {
        let mut b = IRBody::Ret(arg_var(30));
        for i in (0..30).rev() {
            b = IRBody::VDecl {
                var: var(i),
                ty: IRType::UInt64,
                value: lit_u64(i as u64),
                rest: Box::new(b),
            };
        }
        b
    };
    let big_fn = make_decl("big", vec![], big_body);

    // main calls small (inlined) and big (skipped)
    let main_fn = make_decl(
        "main",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("small"),
                args: vec![],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: fn_id("big"),
                    args: vec![],
                },
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig {
        inline_once_used: false,
        ..InlinePassConfig::default()
    };
    let (_, stats) = run_inline_pass(&[small_fn, big_fn, main_fn], &attrs, &config);

    assert_eq!(stats.inlined_calls, 1, "small should be inlined");
    assert_eq!(stats.skipped_too_large, 1, "big should be skipped");
}

#[test]
fn test_run_inline_pass_empty_decls() {
    let attrs = HashMap::new();
    let config = InlinePassConfig::default();
    let (result, stats) = run_inline_pass(&[], &attrs, &config);
    assert!(result.is_empty());
    assert_eq!(stats, InlineStats::default());
}

#[test]
fn test_run_inline_pass_no_calls() {
    let decl = make_decl(
        "leaf",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: lit_u64(42),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig::default();
    let (result, stats) = run_inline_pass(&[decl], &attrs, &config);
    assert_eq!(result.len(), 1);
    assert_eq!(stats.inlined_calls, 0);
}

#[test]
fn test_run_inline_pass_unknown_callee() {
    // Calls a function not in the decl set
    let main_fn = make_decl(
        "main",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("external"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig::default();
    let (result, stats) = run_inline_pass(&[main_fn], &attrs, &config);
    assert_eq!(stats.inlined_calls, 0);
    // Should preserve the call
    let main_body = &result[0].body;
    assert!(body_references_name(main_body, &name("external")));
}

#[test]
fn test_inline_in_case_branch() {
    let helper = make_decl(
        "helper",
        vec![],
        IRBody::VDecl {
            var: var(0),
            ty: IRType::UInt64,
            value: lit_u64(1),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    );

    let main_fn = make_decl(
        "main",
        vec![(var(10), IRType::Object)],
        IRBody::Case {
            scrutinee: var(10),
            alts: vec![IRAlt {
                ctor: simple_ctor(),
                body: Box::new(IRBody::VDecl {
                    var: var(0),
                    ty: IRType::UInt64,
                    value: IRExpr::Apply {
                        fn_id: fn_id("helper"),
                        args: vec![],
                    },
                    rest: Box::new(IRBody::Ret(arg_var(0))),
                }),
            }],
            default: None,
        },
    );

    let attrs = HashMap::new();
    let config = InlinePassConfig::default();
    let (result, stats) = run_inline_pass(&[helper, main_fn], &attrs, &config);

    assert_eq!(stats.inlined_calls, 1, "should inline inside case branch");
    let main_body = &result
        .iter()
        .find(|d| d.name == name("main"))
        .expect("main")
        .body;
    assert!(
        !body_references_name(main_body, &name("helper")),
        "helper should be inlined in case branch"
    );
}

#[test]
fn test_config_default_values() {
    let config = InlinePassConfig::default();
    assert_eq!(config.max_inline_size, 20);
    assert_eq!(config.max_inline_depth, 3);
    assert!(config.respect_annotations);
    assert!(config.inline_once_used);
}

#[test]
fn test_inline_attr_eq() {
    assert_eq!(InlineAttr::Always, InlineAttr::Always);
    assert_ne!(InlineAttr::Always, InlineAttr::NoInline);
    assert_ne!(InlineAttr::Inline, InlineAttr::None);
}

#[test]
fn test_call_counts_in_case_branches() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: fn_id("branch_fn"),
                    args: vec![],
                },
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }],
        default: Some(Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("branch_fn"),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        })),
    };
    let decl = make_decl("main", vec![(var(0), IRType::Object)], body);
    let counts = compute_call_counts(&[decl]);
    assert_eq!(counts.get(&name("branch_fn")), Some(&2));
}
