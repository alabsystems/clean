// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR closure conversion pass.
//!
//! Part of #3084 - Runtime closure support.

use super::*;
use crate::closure_convert_fva::{bound_from_params, free_vars_body};
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;
use std::collections::HashSet;

// ════════════════════════════════════════════════════════════════════════════
// Test helpers
// ════════════════════════════════════════════════════════════════════════════

fn var(n: u32) -> VarId {
    VarId(n)
}

fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}

fn ret_var(n: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(var(n)))
}

fn simple_ctor_info() -> CtorInfo {
    CtorInfo {
        name: Name::from_string("Nat.zero"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn make_decl(name: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: IRType::Object,
        body,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Free variable analysis tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_free_vars_ret_var_unbound() {
    let body = ret_var(5);
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(5)));
    assert_eq!(free.len(), 1);
}

#[test]
fn test_free_vars_ret_var_bound() {
    let body = ret_var(5);
    let mut bound = HashSet::new();
    bound.insert(var(5));
    let free = free_vars_body(&body, &bound);
    assert!(free.is_empty());
}

#[test]
fn test_free_vars_ret_erased() {
    let body = IRBody::Ret(IRArg::Erased);
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.is_empty());
}

#[test]
fn test_free_vars_vdecl_binds_var() {
    // let x1 = lit 42; return x1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(ret_var(1)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    // x1 is bound by VDecl, so it is not free
    assert!(free.is_empty());
}

#[test]
fn test_free_vars_vdecl_value_has_free() {
    // let x1 = apply f(x2); return x1
    // x2 is free
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: fn_id("f"),
            args: vec![IRArg::Var(var(2))],
        },
        rest: Box::new(ret_var(1)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(2)));
    assert!(!free.contains(&var(1)));
}

#[test]
fn test_free_vars_inc_dec() {
    // inc x1 1; dec x2; return x3
    let body = IRBody::Inc {
        var: var(1),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(2),
            rest: Box::new(ret_var(3)),
        }),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(1)));
    assert!(free.contains(&var(2)));
    assert!(free.contains(&var(3)));
    assert_eq!(free.len(), 3);
}

#[test]
fn test_free_vars_case() {
    // case x1 of
    //   ctor => return x2
    //   default => return x3
    let body = IRBody::Case {
        scrutinee: var(1),
        alts: vec![IRAlt {
            ctor: simple_ctor_info(),
            body: Box::new(ret_var(2)),
        }],
        default: Some(Box::new(ret_var(3))),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(1)));
    assert!(free.contains(&var(2)));
    assert!(free.contains(&var(3)));
}

#[test]
fn test_free_vars_jmp() {
    let body = IRBody::Jmp {
        jp: crate::ir::JoinPointId(0),
        args: vec![IRArg::Var(var(5)), IRArg::Erased],
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(5)));
    assert_eq!(free.len(), 1);
}

#[test]
fn test_free_vars_unreachable() {
    let body = IRBody::Unreachable;
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.is_empty());
}

#[test]
fn test_free_vars_jdecl_params_bound() {
    // jp (x1 : Object) { return x1 }; return x2
    let body = IRBody::JDecl {
        jp: crate::ir::JoinPointId(0),
        params: vec![(var(1), IRType::Object)],
        body: Box::new(ret_var(1)),
        rest: Box::new(ret_var(2)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    // x1 is bound within jp body, x2 is free in rest
    assert!(!free.contains(&var(1)));
    assert!(free.contains(&var(2)));
}

#[test]
fn test_free_vars_partial_apply() {
    // let x1 = partial_apply f [x2, x3]; return x1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id("f"),
            arity: 3,
            args: vec![IRArg::Var(var(2)), IRArg::Var(var(3))],
        },
        rest: Box::new(ret_var(1)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(2)));
    assert!(free.contains(&var(3)));
}

#[test]
fn test_free_vars_closure_apply() {
    // let x1 = closure_apply x2 [x3]; return x1
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(2)),
            args: vec![IRArg::Var(var(3))],
        },
        rest: Box::new(ret_var(1)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(2)));
    assert!(free.contains(&var(3)));
}

// ════════════════════════════════════════════════════════════════════════════
// ClosureLayout tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_closure_layout_empty_captures() {
    let layout = ClosureLayout {
        fn_id: fn_id("f"),
        arity: 3,
        captures: vec![],
    };
    assert_eq!(layout.capture_count(), 0);
    assert_eq!(layout.remaining_arity(), 3);
    let ctor = layout.ctor_info();
    assert_eq!(ctor.num_objects, 0);
    assert_eq!(ctor.tag, 0);
}

#[test]
fn test_closure_layout_with_captures() {
    let layout = ClosureLayout {
        fn_id: fn_id("g"),
        arity: 4,
        captures: vec![
            IRCapture {
                var: var(10),
                env_index: 0,
                ty: IRType::Object,
            },
            IRCapture {
                var: var(20),
                env_index: 1,
                ty: IRType::UInt64,
            },
        ],
    };
    assert_eq!(layout.capture_count(), 2);
    assert_eq!(layout.remaining_arity(), 2);
    let ctor = layout.ctor_info();
    assert_eq!(ctor.num_objects, 2);
    // UInt64 gets boxed to Object in field_types
    assert_eq!(ctor.field_types, vec![IRType::Object, IRType::Object]);
}

#[test]
fn test_closure_layout_remaining_arity_saturated() {
    let layout = ClosureLayout {
        fn_id: fn_id("h"),
        arity: 2,
        captures: vec![
            IRCapture {
                var: var(1),
                env_index: 0,
                ty: IRType::Object,
            },
            IRCapture {
                var: var(2),
                env_index: 1,
                ty: IRType::Object,
            },
        ],
    };
    assert_eq!(layout.remaining_arity(), 0);
}

// ════════════════════════════════════════════════════════════════════════════
// Conversion tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_convert_decl_no_closures() {
    // def f (x : Object) := return x
    let decl = make_decl("f", vec![(var(1), IRType::Object)], ret_var(1));
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 0);
    assert_eq!(output.stats.closure_applies_lowered, 0);
    assert_eq!(output.decls.len(), 1);
    assert!(output.hoisted.is_empty());
}

#[test]
fn test_convert_partial_apply_with_captures() {
    // def f (x : Object) :=
    //   let c = partial_apply g [x]  -- captures x
    //   return c
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 3,
                args: vec![IRArg::Var(var(1))],
            },
            rest: Box::new(ret_var(2)),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 1);
    assert_eq!(output.stats.total_captures, 1);

    // The PartialApply should be converted to a Ctor
    match &output.decls[0].body {
        IRBody::VDecl { value, .. } => {
            assert!(
                matches!(value, IRExpr::Ctor { .. }),
                "PartialApply with captures should become Ctor"
            );
        }
        _ => panic!("Expected VDecl"),
    }
}

#[test]
fn test_convert_partial_apply_zero_captures_hoists() {
    // def f () :=
    //   let c = partial_apply g []  -- no captures
    //   return c
    let decl = make_decl(
        "f",
        vec![],
        IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 2,
                args: vec![],
            },
            rest: Box::new(ret_var(1)),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.functions_hoisted, 1);
    assert_eq!(output.stats.closures_created, 0);

    // Zero-capture partial apply should remain as PartialApply
    match &output.decls[0].body {
        IRBody::VDecl { value, .. } => {
            assert!(
                matches!(value, IRExpr::PartialApply { .. }),
                "Zero-capture PartialApply should be kept as-is"
            );
        }
        _ => panic!("Expected VDecl"),
    }
}

#[test]
fn test_convert_closure_apply_tracked() {
    // def f (c : Object) :=
    //   let r = closure_apply c [x1]
    //   return r
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object), (var(2), IRType::Object)],
        IRBody::VDecl {
            var: var(3),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(1)),
                args: vec![IRArg::Var(var(2))],
            },
            rest: Box::new(ret_var(3)),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closure_applies_lowered, 1);
}

#[test]
fn test_convert_multiple_partial_applies() {
    // def f (x y : Object) :=
    //   let c1 = partial_apply g [x]
    //   let c2 = partial_apply h [x, y]
    //   return c2
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object), (var(2), IRType::Object)],
        IRBody::VDecl {
            var: var(3),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 3,
                args: vec![IRArg::Var(var(1))],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(4),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: fn_id("h"),
                    arity: 4,
                    args: vec![IRArg::Var(var(1)), IRArg::Var(var(2))],
                },
                rest: Box::new(ret_var(4)),
            }),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 2);
    assert_eq!(output.stats.total_captures, 3); // 1 + 2
}

#[test]
fn test_convert_preserves_non_closure_exprs() {
    // def f (x : Object) :=
    //   let y = lit 42u64
    //   return y
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(ret_var(2)),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 0);
    assert_eq!(output.stats.closure_applies_lowered, 0);

    // Body should be identical
    match &output.decls[0].body {
        IRBody::VDecl { value, .. } => {
            assert!(matches!(value, IRExpr::Lit(IRLiteral::UInt64(42))));
        }
        _ => panic!("Expected VDecl"),
    }
}

#[test]
fn test_convert_nested_in_case() {
    // def f (x : Object) :=
    //   case x of
    //     ctor => let c = partial_apply g [x]; return c
    //     default => return x
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::Case {
            scrutinee: var(1),
            alts: vec![IRAlt {
                ctor: simple_ctor_info(),
                body: Box::new(IRBody::VDecl {
                    var: var(2),
                    ty: IRType::Object,
                    value: IRExpr::PartialApply {
                        fn_id: fn_id("g"),
                        arity: 2,
                        args: vec![IRArg::Var(var(1))],
                    },
                    rest: Box::new(ret_var(2)),
                }),
            }],
            default: Some(Box::new(ret_var(1))),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 1);
}

#[test]
fn test_convert_in_join_point() {
    // def f (x : Object) :=
    //   jp j0 (y : Object) { let c = partial_apply g [y]; return c }
    //   return x
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::JDecl {
            jp: crate::ir::JoinPointId(0),
            params: vec![(var(2), IRType::Object)],
            body: Box::new(IRBody::VDecl {
                var: var(3),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: fn_id("g"),
                    arity: 3,
                    args: vec![IRArg::Var(var(2))],
                },
                rest: Box::new(ret_var(3)),
            }),
            rest: Box::new(ret_var(1)),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 1);
}

#[test]
fn test_convert_preserves_inc_dec() {
    // def f (x : Object) :=
    //   inc x 1
    //   dec x
    //   return x
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::Inc {
            var: var(1),
            n: 1,
            rest: Box::new(IRBody::Dec {
                var: var(1),
                rest: Box::new(ret_var(1)),
            }),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 0);
    // Structure preserved
    match &output.decls[0].body {
        IRBody::Inc { rest, .. } => match rest.as_ref() {
            IRBody::Dec { rest, .. } => {
                assert!(matches!(rest.as_ref(), IRBody::Ret(_)));
            }
            _ => panic!("Expected Dec"),
        },
        _ => panic!("Expected Inc"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Hoisting tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_find_hoistable_empty_args() {
    let decl = make_decl(
        "f",
        vec![],
        IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 2,
                args: vec![],
            },
            rest: Box::new(ret_var(1)),
        },
    );
    let hoistable = find_hoistable_closures(&[decl]);
    assert_eq!(hoistable.len(), 1);
    assert_eq!(hoistable[0], fn_id("g"));
}

#[test]
fn test_find_hoistable_with_captures_excluded() {
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 3,
                args: vec![IRArg::Var(var(1))],
            },
            rest: Box::new(ret_var(2)),
        },
    );
    let hoistable = find_hoistable_closures(&[decl]);
    assert!(hoistable.is_empty());
}

// ════════════════════════════════════════════════════════════════════════════
// Counting utility tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_count_partial_applies_none() {
    let decl = make_decl("f", vec![], ret_var(0));
    assert_eq!(count_partial_applies(&[decl]), 0);
}

#[test]
fn test_count_partial_applies_multiple() {
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 2,
                args: vec![IRArg::Var(var(1))],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(3),
                ty: IRType::Object,
                value: IRExpr::PartialApply {
                    fn_id: fn_id("h"),
                    arity: 3,
                    args: vec![],
                },
                rest: Box::new(ret_var(3)),
            }),
        },
    );
    assert_eq!(count_partial_applies(&[decl]), 2);
}

#[test]
fn test_count_closure_applies() {
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(1)),
                args: vec![],
            },
            rest: Box::new(ret_var(2)),
        },
    );
    assert_eq!(count_closure_applies(&[decl]), 1);
}

// ════════════════════════════════════════════════════════════════════════════
// bound_from_params tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_bound_from_params_empty() {
    let decl = make_decl("f", vec![], ret_var(0));
    let bound = bound_from_params(&decl);
    assert!(bound.is_empty());
}

#[test]
fn test_bound_from_params_multiple() {
    let decl = make_decl(
        "f",
        vec![
            (var(1), IRType::Object),
            (var(2), IRType::UInt64),
            (var(3), IRType::Bool),
        ],
        ret_var(1),
    );
    let bound = bound_from_params(&decl);
    assert_eq!(bound.len(), 3);
    assert!(bound.contains(&var(1)));
    assert!(bound.contains(&var(2)));
    assert!(bound.contains(&var(3)));
}

// ════════════════════════════════════════════════════════════════════════════
// Stats tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_stats_default() {
    let stats = ClosureConvertStats::default();
    assert_eq!(stats.closures_created, 0);
    assert_eq!(stats.total_captures, 0);
    assert_eq!(stats.closure_applies_lowered, 0);
    assert_eq!(stats.functions_hoisted, 0);
}

#[test]
fn test_convert_decls_multiple() {
    let decl1 = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 3,
                args: vec![IRArg::Var(var(1))],
            },
            rest: Box::new(ret_var(2)),
        },
    );
    let decl2 = make_decl(
        "h",
        vec![(var(10), IRType::Object)],
        IRBody::VDecl {
            var: var(11),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(var(10)),
                args: vec![],
            },
            rest: Box::new(ret_var(11)),
        },
    );
    let output = closure_convert_decls(&[decl1, decl2]);
    assert_eq!(output.decls.len(), 2);
    assert_eq!(output.stats.closures_created, 1);
    assert_eq!(output.stats.closure_applies_lowered, 1);
}

// ════════════════════════════════════════════════════════════════════════════
// Edge case: erased args in partial apply
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_convert_partial_apply_erased_args_filtered() {
    // partial_apply with mix of Var and Erased args
    let decl = make_decl(
        "f",
        vec![(var(1), IRType::Object)],
        IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 4,
                args: vec![IRArg::Var(var(1)), IRArg::Erased, IRArg::Var(var(1))],
            },
            rest: Box::new(ret_var(2)),
        },
    );
    let output = closure_convert_decl(&decl);
    assert_eq!(output.stats.closures_created, 1);
    // Only non-erased args count as captures
    assert_eq!(output.stats.total_captures, 2);

    // The Ctor should have 2 args (the two Var captures)
    match &output.decls[0].body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Ctor { args, info } => {
                assert_eq!(args.len(), 2);
                assert_eq!(info.num_objects, 2);
            }
            _ => panic!("Expected Ctor"),
        },
        _ => panic!("Expected VDecl"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Free variable analysis for IR expressions
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_free_vars_set_body() {
    // set x1[0] := x2; return x3
    let body = IRBody::Set {
        var: var(1),
        idx: 0,
        value: var(2),
        rest: Box::new(ret_var(3)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(1)));
    assert!(free.contains(&var(2)));
    assert!(free.contains(&var(3)));
}

#[test]
fn test_free_vars_sproj() {
    // let x2 = sproj(x1, n=0, offset=0); return x2
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::UInt64,
        value: IRExpr::SProj {
            n: 0,
            offset: 0,
            var: var(1),
            ty: IRType::UInt64,
        },
        rest: Box::new(ret_var(2)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(1)));
    assert!(!free.contains(&var(2)));
}

#[test]
fn test_free_vars_is_shared() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(1)),
        rest: Box::new(ret_var(2)),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(1)));
}

#[test]
fn test_free_vars_reset_reuse() {
    // let x2 = reset x1; let x3 = reuse x2 ctor [x4]; return x3
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::Reset(var(1)),
        rest: Box::new(IRBody::VDecl {
            var: var(3),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: var(2),
                ctor: simple_ctor_info(),
                args: vec![IRArg::Var(var(4))],
            },
            rest: Box::new(ret_var(3)),
        }),
    };
    let bound = HashSet::new();
    let free = free_vars_body(&body, &bound);
    assert!(free.contains(&var(1))); // free in reset
    assert!(!free.contains(&var(2))); // bound by first VDecl
    assert!(!free.contains(&var(3))); // bound by second VDecl
    assert!(free.contains(&var(4))); // free in reuse args
}
