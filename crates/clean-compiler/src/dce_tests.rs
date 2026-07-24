// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR dead code elimination.
//!
//! Part of #3084 - IO/FFI/Native epic.

use super::*;
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

fn simple_ctor() -> CtorInfo {
    CtorInfo {
        name: name("Unit.unit"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

/// Build a trivial function body: `let v0 := <expr>; ret v0`
fn trivial_body(v: u32, expr: IRExpr) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::UInt64,
        value: expr,
        rest: Box::new(IRBody::Ret(arg_var(v))),
    }
}

fn make_decl(n: &str, body: IRBody) -> IRDecl {
    IRDecl {
        name: name(n),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }
}

// =======================================================================
// Local DCE tests
// =======================================================================

#[test]
fn test_dce_local_unused_binding_removed() {
    // let v0 := 42; let v1 := 99 (unused); ret v0
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: lit_u64(99),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        }),
    };

    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 1, "should remove 1 dead binding");
    // v0 should still be present
    assert!(matches!(result, IRBody::VDecl { var: VarId(0), .. }));
    // The rest should be Ret, not another VDecl
    if let IRBody::VDecl { rest, .. } = &result {
        assert!(matches!(**rest, IRBody::Ret(_)));
    }
}

#[test]
fn test_dce_local_all_used_kept() {
    // let v0 := 42; let v1 := Apply(f, v0); ret v1
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("f"),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0, "no dead bindings to remove");
}

#[test]
fn test_dce_local_chain_of_dead() {
    // let v0 := 1; let v1 := Apply(f, v0); let v2 := Apply(g, v1); ret Erased
    // v0, v1, v2 all dead because return uses Erased
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(1),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: fn_id("f"),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: fn_id("g"),
                    args: vec![arg_var(1)],
                },
                rest: Box::new(IRBody::Ret(IRArg::Erased)),
            }),
        }),
    };

    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 3, "all three dead bindings removed");
    assert!(matches!(result, IRBody::Ret(IRArg::Erased)));
}

#[test]
fn test_dce_local_single_used_binding() {
    // let v0 := 42; ret v0
    let body = trivial_body(0, lit_u64(42));
    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0);
}

#[test]
fn test_dce_local_empty_body_ret() {
    let body = IRBody::Ret(arg_var(0));
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0);
    assert!(matches!(result, IRBody::Ret(_)));
}

#[test]
fn test_dce_local_unreachable() {
    let body = IRBody::Unreachable;
    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0);
    assert!(matches!(result, IRBody::Unreachable));
}

#[test]
fn test_dce_local_preserves_inc_dec() {
    // inc v0; dec v0; ret v0
    // v0 is used by inc, dec, and ret -> nothing removed
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Inc {
            var: var(0),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: var(0),
                rest: Box::new(IRBody::Ret(arg_var(0))),
            }),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0);
}

#[test]
fn test_dce_local_dead_binding_before_inc() {
    // let v0 := 42; let v1 := 99 (unused); inc v0 1; ret v0
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: lit_u64(99),
            rest: Box::new(IRBody::Inc {
                var: var(0),
                n: 1,
                rest: Box::new(IRBody::Ret(arg_var(0))),
            }),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 1, "v1 is dead");
}

#[test]
fn test_dce_local_case_scrutinee_is_used() {
    // let v0 := 42; case v0 of { ... }
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: simple_ctor(),
                body: Box::new(IRBody::Ret(IRArg::Erased)),
            }],
            default: None,
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0, "scrutinee keeps v0 live");
}

#[test]
fn test_dce_local_dead_in_case_arms() {
    // case v0 of { Ctor => let v1 := 99 (dead); ret Erased }
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::UInt64,
                value: lit_u64(99),
                rest: Box::new(IRBody::Ret(IRArg::Erased)),
            }),
        }],
        default: None,
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 1, "v1 dead inside case arm");
}

#[test]
fn test_dce_local_jmp_keeps_jp_alive() {
    // jdecl jp0(v1) { ret v1 }; jmp jp0(v0)
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(1), IRType::UInt64)],
        body: Box::new(IRBody::Ret(arg_var(1))),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![arg_var(0)],
        }),
    };

    let (result, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0);
    assert!(matches!(result, IRBody::JDecl { .. }));
}

#[test]
fn test_dce_local_dead_join_point_removed() {
    // jdecl jp0(v1) { ret v1 }; ret v0  -- jp0 never jumped to
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(1), IRType::UInt64)],
        body: Box::new(IRBody::Ret(arg_var(1))),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };

    let (result, removed) = eliminate_dead_locals(&body);
    // Dead JP removed. No VDecls inside, so removed_locals count is 0.
    assert_eq!(removed, 0, "no VDecls removed, but JP dropped");
    assert!(matches!(result, IRBody::Ret(_)));
}

#[test]
fn test_dce_local_set_uses_both_vars() {
    // let v0 := Ctor(); let v1 := 42; set v0[0] = v1; ret v0
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: simple_ctor(),
            args: vec![],
        },
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: lit_u64(42),
            rest: Box::new(IRBody::Set {
                var: var(0),
                idx: 0,
                value: var(1),
                rest: Box::new(IRBody::Ret(arg_var(0))),
            }),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0, "both v0 and v1 used by Set");
}

#[test]
fn test_dce_local_closure_apply_args() {
    // let v0 := ...; let v1 := ClosureApply(v0, v2); ret v1
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: lit_u64(0),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: arg_var(0),
                args: vec![arg_var(2)],
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0, "v0 used in ClosureApply");
}

#[test]
fn test_dce_local_proj_keeps_arg_alive() {
    // let v0 := ...; let v1 := Proj(0, v0); ret v1
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: simple_ctor(),
            args: vec![],
        },
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::UInt64,
                arg: arg_var(0),
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0, "v0 used transitively via Proj");
}

#[test]
fn test_dce_local_multiple_dead_interleaved() {
    // let v0 := 1 (dead); let v1 := 2; let v2 := 3 (dead); ret v1
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(1),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: lit_u64(2),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::UInt64,
                value: lit_u64(3),
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 2, "v0 and v2 are dead");
}

// =======================================================================
// Global DCE (liveness) tests
// =======================================================================

#[test]
fn test_dce_global_single_entry_point() {
    let decls = vec![
        make_decl("main", trivial_body(0, lit_u64(42))),
        make_decl("dead_fn", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("main")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, name("main"));
    assert_eq!(stats.removed_globals, 1);
}

#[test]
fn test_dce_global_transitive_reachability() {
    // main -> helper -> leaf; orphan is unreachable
    let decls = vec![
        make_decl(
            "main",
            trivial_body(
                0,
                IRExpr::Apply {
                    fn_id: fn_id("helper"),
                    args: vec![],
                },
            ),
        ),
        make_decl(
            "helper",
            trivial_body(
                0,
                IRExpr::Apply {
                    fn_id: fn_id("leaf"),
                    args: vec![],
                },
            ),
        ),
        make_decl("leaf", trivial_body(0, lit_u64(1))),
        make_decl("orphan", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("main")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 3);
    let names: HashSet<Name> = result.iter().map(|d| d.name.clone()).collect();
    assert!(names.contains(&name("main")));
    assert!(names.contains(&name("helper")));
    assert!(names.contains(&name("leaf")));
    assert!(!names.contains(&name("orphan")));
    assert_eq!(stats.removed_globals, 1);
}

#[test]
fn test_dce_global_multiple_entry_points() {
    let decls = vec![
        make_decl("ep1", trivial_body(0, lit_u64(1))),
        make_decl("ep2", trivial_body(0, lit_u64(2))),
        make_decl("dead", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("ep1"), name("ep2")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 2);
    assert_eq!(stats.removed_globals, 1);
}

#[test]
fn test_dce_global_cyclic_call_graph() {
    // a -> b -> c -> a (cycle); orphan dead
    let decls = vec![
        make_decl(
            "a",
            trivial_body(
                0,
                IRExpr::Apply {
                    fn_id: fn_id("b"),
                    args: vec![],
                },
            ),
        ),
        make_decl(
            "b",
            trivial_body(
                0,
                IRExpr::Apply {
                    fn_id: fn_id("c"),
                    args: vec![],
                },
            ),
        ),
        make_decl(
            "c",
            trivial_body(
                0,
                IRExpr::Apply {
                    fn_id: fn_id("a"),
                    args: vec![],
                },
            ),
        ),
        make_decl("orphan", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("a")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 3, "cycle keeps all 3 alive");
    assert_eq!(stats.removed_globals, 1);
    assert!(stats.live_definitions.contains(&name("a")));
    assert!(stats.live_definitions.contains(&name("b")));
    assert!(stats.live_definitions.contains(&name("c")));
}

#[test]
fn test_dce_global_empty_program() {
    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("main")],
    };

    let (result, stats) = run_dce(&[], &config);
    assert!(result.is_empty());
    assert_eq!(stats.removed_globals, 0);
}

#[test]
fn test_dce_global_no_entry_points_removes_all() {
    let decls = vec![
        make_decl("a", trivial_body(0, lit_u64(1))),
        make_decl("b", trivial_body(0, lit_u64(2))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert!(result.is_empty(), "no entry points means all dead");
    assert_eq!(stats.removed_globals, 2);
}

#[test]
fn test_dce_global_partial_apply_keeps_callee() {
    // main does a partial application of helper
    let decls = vec![
        make_decl(
            "main",
            trivial_body(
                0,
                IRExpr::PartialApply {
                    fn_id: fn_id("helper"),
                    arity: 2,
                    args: vec![arg_var(0)],
                },
            ),
        ),
        make_decl("helper", trivial_body(0, lit_u64(1))),
        make_decl("dead", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("main")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 2);
    let names: HashSet<Name> = result.iter().map(|d| d.name.clone()).collect();
    assert!(names.contains(&name("main")));
    assert!(names.contains(&name("helper")));
    assert_eq!(stats.removed_globals, 1);
}

// =======================================================================
// Combined (local + global) tests
// =======================================================================

#[test]
fn test_dce_combined_local_and_global() {
    // main: let v0 := 42; let v1 := 99 (dead); ret v0
    // dead_fn: unreachable from main
    let decls = vec![
        make_decl(
            "main",
            IRBody::VDecl {
                var: var(0),
                ty: IRType::UInt64,
                value: lit_u64(42),
                rest: Box::new(IRBody::VDecl {
                    var: var(1),
                    ty: IRType::UInt64,
                    value: lit_u64(99),
                    rest: Box::new(IRBody::Ret(arg_var(0))),
                }),
            },
        ),
        make_decl("dead_fn", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: true,
        eliminate_globals: true,
        entry_points: vec![name("main")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 1, "dead_fn removed");
    assert_eq!(stats.removed_locals, 1, "v1 removed from main");
    assert_eq!(stats.removed_globals, 1);
}

#[test]
fn test_dce_config_locals_only() {
    let decls = vec![
        make_decl(
            "main",
            IRBody::VDecl {
                var: var(0),
                ty: IRType::UInt64,
                value: lit_u64(42),
                rest: Box::new(IRBody::VDecl {
                    var: var(1),
                    ty: IRType::UInt64,
                    value: lit_u64(99),
                    rest: Box::new(IRBody::Ret(arg_var(0))),
                }),
            },
        ),
        make_decl("dead_fn", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: true,
        eliminate_globals: false,
        entry_points: vec![],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 2, "global DCE disabled, both kept");
    assert_eq!(stats.removed_locals, 1, "v1 still removed locally");
    assert_eq!(stats.removed_globals, 0);
}

#[test]
fn test_dce_config_globals_only() {
    let decls = vec![
        make_decl(
            "main",
            IRBody::VDecl {
                var: var(0),
                ty: IRType::UInt64,
                value: lit_u64(42),
                rest: Box::new(IRBody::VDecl {
                    var: var(1),
                    ty: IRType::UInt64,
                    value: lit_u64(99),
                    rest: Box::new(IRBody::Ret(arg_var(0))),
                }),
            },
        ),
        make_decl("dead_fn", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("main")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 1, "dead_fn removed");
    assert_eq!(stats.removed_locals, 0, "local DCE disabled");
    assert_eq!(stats.removed_globals, 1);
}

#[test]
fn test_dce_default_config() {
    let config = DceConfig::default();
    assert!(config.eliminate_locals);
    assert!(config.eliminate_globals);
    assert!(config.entry_points.is_empty());
}

// =======================================================================
// Liveness analyzer unit tests
// =======================================================================

#[test]
fn test_liveness_analyzer_no_entries() {
    let analyzer = LivenessAnalyzer::new();
    let live = analyzer.compute_live_set();
    assert!(live.is_empty());
}

#[test]
fn test_liveness_analyzer_entry_with_no_callees() {
    let mut analyzer = LivenessAnalyzer::new();
    analyzer.add_entry_point(&name("main"));
    // Don't add any decl for "main" -- no call graph edges
    let live = analyzer.compute_live_set();
    assert_eq!(live.len(), 1);
    assert!(live.contains(&name("main")));
}

#[test]
fn test_liveness_analyzer_transitive() {
    let mut analyzer = LivenessAnalyzer::new();
    analyzer.add_entry_point(&name("a"));
    analyzer.analyze_decl(&make_decl(
        "a",
        trivial_body(
            0,
            IRExpr::Apply {
                fn_id: fn_id("b"),
                args: vec![],
            },
        ),
    ));
    analyzer.analyze_decl(&make_decl(
        "b",
        trivial_body(
            0,
            IRExpr::Apply {
                fn_id: fn_id("c"),
                args: vec![],
            },
        ),
    ));
    analyzer.analyze_decl(&make_decl("c", trivial_body(0, lit_u64(0))));

    let live = analyzer.compute_live_set();
    assert_eq!(live.len(), 3);
    assert!(live.contains(&name("a")));
    assert!(live.contains(&name("b")));
    assert!(live.contains(&name("c")));
}

#[test]
fn test_dce_local_reset_reuse_keeps_var() {
    // let v0 := Reset(v1); let v2 := Reuse(v0, ctor, []); ret v2
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Reset(var(1)),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: var(0),
                ctor: simple_ctor(),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0, "Reset/Reuse chain keeps v0 and v1 alive");
}

#[test]
fn test_dce_local_is_shared_keeps_var() {
    // let v0 := IsShared(v1); ret v0
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(1)),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };

    let (_, removed) = eliminate_dead_locals(&body);
    assert_eq!(removed, 0, "IsShared keeps v1 alive");
}

#[test]
fn test_dce_global_call_in_case_body() {
    // main has a case arm that calls helper
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(),
            body: Box::new(trivial_body(
                1,
                IRExpr::Apply {
                    fn_id: fn_id("helper"),
                    args: vec![],
                },
            )),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Erased))),
    };

    let decls = vec![
        make_decl("main", body),
        make_decl("helper", trivial_body(0, lit_u64(1))),
        make_decl("dead", trivial_body(0, lit_u64(0))),
    ];

    let config = DceConfig {
        eliminate_locals: false,
        eliminate_globals: true,
        entry_points: vec![name("main")],
    };

    let (result, stats) = run_dce(&decls, &config);
    assert_eq!(result.len(), 2);
    let names: HashSet<Name> = result.iter().map(|d| d.name.clone()).collect();
    assert!(
        names.contains(&name("helper")),
        "call in case arm keeps helper"
    );
    assert_eq!(stats.removed_globals, 1);
}
