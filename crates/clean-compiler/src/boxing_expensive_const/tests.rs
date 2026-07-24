// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

fn mk_ctor(name: &str, tag: u32, num_objects: u32) -> CtorInfo {
    CtorInfo {
        name: Name::from_string(name),
        tag,
        num_scalars: 0,
        num_objects,
        field_types: (0..num_objects).map(|_| IRType::Object).collect(),
    }
}

fn mk_decl(name: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: IRType::Object,
        body,
    }
}

/// Walk body to find the terminal Ret and return the VarId it references.
fn find_ret_var(body: &IRBody) -> Option<VarId> {
    match body {
        IRBody::Ret(IRArg::Var(v)) => Some(*v),
        IRBody::VDecl { rest, .. }
        | IRBody::JDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => find_ret_var(rest),
        _ => None,
    }
}

#[test]
fn test_no_expensive_exprs_unchanged() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt32,
        value: IRExpr::Lit(IRLiteral::UInt32(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = mk_decl("f", vec![(VarId(0), IRType::Object)], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 0);
}

#[test]
fn test_single_ctor_hoisted() {
    let ctor = mk_ctor("Pair.mk", 0, 2);
    let body = IRBody::VDecl {
        var: VarId(2),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor,
            args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
    };
    let decl = mk_decl(
        "mk_pair",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        body,
    );
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 1);

    // Top-level should be a VDecl with the hoisted Ctor.
    match &result.decl.body {
        IRBody::VDecl { var, value, .. } => {
            assert!(var.0 > 2, "hoisted var should be fresh");
            match value {
                IRExpr::Ctor { info, args } => {
                    assert_eq!(info.tag, 0);
                    assert_eq!(args.len(), 2);
                }
                other => panic!("expected Ctor, got {:?}", other),
            }
        }
        other => panic!("expected VDecl at top, got {:?}", other),
    }
}

#[test]
fn test_duplicate_ctor_deduped() {
    let ctor = mk_ctor("Unit.unit", 0, 1);
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor.clone(),
            args: vec![IRArg::Erased],
        },
        rest: Box::new(IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor,
                args: vec![IRArg::Erased],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        }),
    };
    let decl = mk_decl("dup_unit", vec![(VarId(0), IRType::Object)], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 1, "identical ctors should dedup to 1");
}

#[test]
fn test_different_ctors_not_deduped() {
    let ctor_a = mk_ctor("A.mk", 0, 1);
    let ctor_b = mk_ctor("B.mk", 1, 1);
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor_a,
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor_b,
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        }),
    };
    let decl = mk_decl("two_ctors", vec![(VarId(0), IRType::Object)], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 2);
}

#[test]
fn test_string_literal_hoisted() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::String("hello world".to_string()),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = mk_decl("str_fn", vec![(VarId(0), IRType::Object)], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 1);
}

#[test]
fn test_min_args_threshold() {
    let ctor = mk_ctor("Wrap.mk", 0, 1);
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor,
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = mk_decl("wrap", vec![(VarId(0), IRType::Object)], body);
    let config = ExpensiveConstConfig { min_args: 2 };
    let result = box_expensive_constants(&decl, &config);
    assert_eq!(result.hoisted_count, 0, "below threshold, should not hoist");
}

#[test]
fn test_substitution_in_ret() {
    let ctor = mk_ctor("Pair.mk", 0, 2);
    let body = IRBody::VDecl {
        var: VarId(2),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor,
            args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
    };
    let decl = mk_decl(
        "mk_pair",
        vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        body,
    );
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    let ret_var = find_ret_var(&result.decl.body).expect("should have Ret");
    assert!(
        ret_var.0 > 2,
        "Ret should reference hoisted var, got {}",
        ret_var.0
    );
}

#[test]
fn test_expensive_in_case_branch_hoisted() {
    let ctor = mk_ctor("Some.mk", 1, 1);
    let alt_ctor = mk_ctor("Bool.true", 1, 0);
    let body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![IRAlt {
            ctor: alt_ctor,
            body: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: ctor,
                    args: vec![IRArg::Var(VarId(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            }),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Erased))),
    };
    let decl = mk_decl("case_fn", vec![(VarId(0), IRType::Object)], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 1);
    match &result.decl.body {
        IRBody::VDecl { rest, .. } => match rest.as_ref() {
            IRBody::Case { .. } => {}
            other => panic!("expected Case after hoisted VDecl, got {:?}", other),
        },
        other => panic!("expected VDecl at top, got {:?}", other),
    }
}

#[test]
fn test_large_literal_hoisted() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(999_999_999)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = mk_decl("big_lit", vec![(VarId(0), IRType::Object)], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 1);
}

#[test]
fn test_small_literal_not_hoisted() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt32,
        value: IRExpr::Lit(IRLiteral::UInt32(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = mk_decl("small_lit", vec![(VarId(0), IRType::Object)], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 0);
}

#[test]
fn test_empty_body() {
    let body = IRBody::Ret(IRArg::Erased);
    let decl = mk_decl("empty", vec![], body);
    let result = box_expensive_constants(&decl, &ExpensiveConstConfig::default());
    assert_eq!(result.hoisted_count, 0);
}

#[test]
fn test_default_convenience_fn() {
    let body = IRBody::Ret(IRArg::Erased);
    let decl = mk_decl("trivial", vec![], body);
    let result = box_expensive_constants_default(&decl);
    assert_eq!(result.hoisted_count, 0);
}

#[test]
fn test_normalize_ctor_below_threshold() {
    let ctor = mk_ctor("Unit", 0, 0);
    let expr = IRExpr::Ctor {
        info: ctor,
        args: vec![],
    };
    assert!(normalize_expr(&expr, &ExpensiveConstConfig { min_args: 1 }).is_none());
}

#[test]
fn test_normalize_ctor_at_threshold() {
    let ctor = mk_ctor("Some", 1, 1);
    let expr = IRExpr::Ctor {
        info: ctor,
        args: vec![IRArg::Erased],
    };
    assert!(normalize_expr(&expr, &ExpensiveConstConfig { min_args: 1 }).is_some());
}

#[test]
fn test_normalize_string() {
    let expr = IRExpr::String("test".to_string());
    let key = normalize_expr(&expr, &ExpensiveConstConfig::default());
    assert_eq!(key, Some(ExprKey::String("test".to_string())));
}

#[test]
fn test_apply_not_expensive() {
    let expr = IRExpr::Apply {
        fn_id: FnId(Name::from_string("foo")),
        args: vec![IRArg::Var(VarId(0))],
    };
    assert!(normalize_expr(&expr, &ExpensiveConstConfig::default()).is_none());
}
