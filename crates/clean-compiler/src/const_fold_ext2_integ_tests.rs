// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for ext2 constant folding: full-pass, config, edge cases.

use crate::const_fold_ext2::*;
use crate::ir::*;
use clean_kernel::Name;

fn name(s: &str) -> Name {
    s.parse().unwrap()
}
fn fn_id(s: &str) -> FnId {
    FnId(name(s))
}
fn var(id: u32) -> VarId {
    VarId(id)
}
fn var_arg(id: u32) -> IRArg {
    IRArg::Var(var(id))
}
fn lit_u64(v: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(v))
}
fn lit_bool(v: bool) -> IRExpr {
    IRExpr::Lit(IRLiteral::Bool(v))
}
fn str_expr(s: &str) -> IRExpr {
    IRExpr::String(s.to_owned())
}
fn apply(op: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: fn_id(op),
        args,
    }
}
fn simple_ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name("Test.ctor"),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}
fn chain_lets(bindings: Vec<(u32, IRExpr)>, ret_var: u32) -> IRBody {
    let mut body = IRBody::Ret(var_arg(ret_var));
    for (vid, expr) in bindings.into_iter().rev() {
        body = IRBody::VDecl {
            var: var(vid),
            ty: IRType::UInt64,
            value: expr,
            rest: Box::new(body),
        };
    }
    body
}
fn make_decl(body: IRBody) -> IRDecl {
    IRDecl {
        name: name("test_fn"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }
}
fn extract_last_vdecl_value(body: &IRBody) -> &IRExpr {
    match body {
        IRBody::VDecl { value, rest, .. } => match rest.as_ref() {
            IRBody::VDecl { .. } => extract_last_vdecl_value(rest),
            _ => value,
        },
        other => panic!("expected VDecl chain, got {other:?}"),
    }
}

// -- Dead branch folding -----------------------------------------------------

#[test]
fn test_dead_branch_fold_known_ctor() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: simple_ctor(1),
            args: vec![],
        },
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: simple_ctor(0),
                    body: Box::new(IRBody::Ret(var_arg(10))),
                },
                IRAlt {
                    ctor: simple_ctor(1),
                    body: Box::new(IRBody::Ret(var_arg(42))),
                },
            ],
            default: None,
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.dead_branch_folds >= 1, "got {stats:?}");
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => assert!(
            matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(VarId(42)))),
            "got {rest:?}"
        ),
        o => panic!("expected VDecl, got {o:?}"),
    }
}

#[test]
fn test_dead_branch_fold_known_bool_true() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Bool,
        value: lit_bool(true),
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: simple_ctor(0),
                    body: Box::new(IRBody::Ret(var_arg(10))),
                },
                IRAlt {
                    ctor: simple_ctor(1),
                    body: Box::new(IRBody::Ret(var_arg(20))),
                },
            ],
            default: None,
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.dead_branch_folds >= 1);
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => assert!(
            matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(VarId(20)))),
            "got {rest:?}"
        ),
        o => panic!("expected VDecl, got {o:?}"),
    }
}

#[test]
fn test_dead_branch_fold_known_bool_false() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Bool,
        value: lit_bool(false),
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: simple_ctor(0),
                    body: Box::new(IRBody::Ret(var_arg(10))),
                },
                IRAlt {
                    ctor: simple_ctor(1),
                    body: Box::new(IRBody::Ret(var_arg(20))),
                },
            ],
            default: None,
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.dead_branch_folds >= 1);
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => assert!(
            matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(VarId(10)))),
            "got {rest:?}"
        ),
        o => panic!("expected VDecl, got {o:?}"),
    }
}

// -- Constant propagation through chains -------------------------------------

#[test]
fn test_propagation_through_chain() {
    let body = chain_lets(
        vec![
            (0, lit_u64(2)),
            (1, lit_u64(3)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
            (3, lit_u64(10)),
            (4, apply("Nat.mul", vec![var_arg(2), var_arg(3)])),
        ],
        4,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.arithmetic_folds >= 2, "got {stats:?}");
    let val = extract_last_vdecl_value(&decls[0].body);
    assert!(
        matches!(val, IRExpr::Lit(IRLiteral::UInt64(50))),
        "got {val:?}"
    );
}

#[test]
fn test_propagation_disabled() {
    let body = chain_lets(
        vec![
            (0, lit_u64(2)),
            (1, lit_u64(3)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let config = ConstFoldExt2Config {
        propagate_constants: false,
        ..Default::default()
    };
    let stats = fold_constants_ext2(&mut decls, &config);
    assert_eq!(stats.arithmetic_folds, 0);
    assert_eq!(stats.propagations, 0);
}

// -- Config toggles ----------------------------------------------------------

#[test]
fn test_config_disable_arithmetic() {
    let body = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(4)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(
        &mut decls,
        &ConstFoldExt2Config {
            fold_arithmetic: false,
            ..Default::default()
        },
    );
    assert_eq!(stats.arithmetic_folds, 0);
}

#[test]
fn test_config_disable_boolean() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Bool,
        value: lit_bool(true),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Bool,
            value: lit_bool(false),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Bool,
                value: apply("Bool.and", vec![var_arg(0), var_arg(1)]),
                rest: Box::new(IRBody::Ret(var_arg(2))),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(
        &mut decls,
        &ConstFoldExt2Config {
            fold_boolean: false,
            ..Default::default()
        },
    );
    assert_eq!(stats.boolean_folds, 0);
}

#[test]
fn test_config_disable_string() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: str_expr("a"),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: str_expr("b"),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: apply("String.append", vec![var_arg(0), var_arg(1)]),
                rest: Box::new(IRBody::Ret(var_arg(2))),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(
        &mut decls,
        &ConstFoldExt2Config {
            fold_string: false,
            ..Default::default()
        },
    );
    assert_eq!(stats.string_folds, 0);
}

#[test]
fn test_config_disable_comparisons() {
    let body = chain_lets(
        vec![
            (0, lit_u64(5)),
            (1, lit_u64(5)),
            (2, apply("Nat.beq", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(
        &mut decls,
        &ConstFoldExt2Config {
            fold_comparisons: false,
            ..Default::default()
        },
    );
    assert_eq!(stats.comparison_folds, 0);
}

#[test]
fn test_config_disable_dead_branches() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: simple_ctor(1),
            args: vec![],
        },
        rest: Box::new(IRBody::Case {
            scrutinee: var(0),
            alts: vec![
                IRAlt {
                    ctor: simple_ctor(0),
                    body: Box::new(IRBody::Ret(var_arg(10))),
                },
                IRAlt {
                    ctor: simple_ctor(1),
                    body: Box::new(IRBody::Ret(var_arg(20))),
                },
            ],
            default: None,
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(
        &mut decls,
        &ConstFoldExt2Config {
            fold_dead_branches: false,
            ..Default::default()
        },
    );
    assert_eq!(stats.dead_branch_folds, 0);
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => assert!(matches!(rest.as_ref(), IRBody::Case { .. })),
        o => panic!("expected VDecl, got {o:?}"),
    }
}

// -- Fixpoint and edge cases -------------------------------------------------

#[test]
fn test_fixpoint_converges() {
    let body = chain_lets(
        vec![
            (0, lit_u64(1)),
            (1, lit_u64(2)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.iterations <= 3);
}

#[test]
fn test_max_iterations_respected() {
    let body = chain_lets(
        vec![
            (0, lit_u64(1)),
            (1, lit_u64(2)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(
        &mut decls,
        &ConstFoldExt2Config {
            max_iterations: 1,
            ..Default::default()
        },
    );
    assert_eq!(stats.iterations, 1);
}

#[test]
fn test_empty_decls() {
    let mut decls: Vec<IRDecl> = vec![];
    let stats = fold_constants_ext2_default(&mut decls);
    assert_eq!(stats.total_folds(), 0);
    assert_eq!(stats.iterations, 1);
}

#[test]
fn test_no_foldable_ops() {
    let mut decls = vec![make_decl(IRBody::Ret(var_arg(0)))];
    let stats = fold_constants_ext2_default(&mut decls);
    assert_eq!(stats.total_folds(), 0);
}

#[test]
fn test_unreachable_body() {
    let mut decls = vec![make_decl(IRBody::Unreachable)];
    assert_eq!(fold_constants_ext2_default(&mut decls).total_folds(), 0);
}

#[test]
fn test_jmp_body() {
    let mut decls = vec![make_decl(IRBody::Jmp {
        jp: JoinPointId(0),
        args: vec![var_arg(0)],
    })];
    assert_eq!(fold_constants_ext2_default(&mut decls).total_folds(), 0);
}

#[test]
fn test_join_point_scope_isolation() {
    let jp_body = chain_lets(vec![(10, lit_u64(99))], 10);
    let rest = chain_lets(
        vec![
            (0, lit_u64(1)),
            (1, lit_u64(2)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(jp_body),
        rest: Box::new(rest),
    };
    let mut decls = vec![make_decl(body)];
    assert!(fold_constants_ext2_default(&mut decls).arithmetic_folds >= 1);
}

#[test]
fn test_inc_dec_passthrough() {
    let inner = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(7)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let body = IRBody::Inc {
        var: var(99),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(98),
            rest: Box::new(inner),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.arithmetic_folds >= 1);
    assert!(matches!(&decls[0].body, IRBody::Inc { .. }));
}

#[test]
fn test_multiple_decls() {
    let b1 = chain_lets(
        vec![
            (0, lit_u64(10)),
            (1, lit_u64(20)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let b2 = chain_lets(
        vec![
            (0, lit_u64(5)),
            (1, lit_u64(5)),
            (2, apply("Nat.beq", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(b1), make_decl(b2)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.arithmetic_folds >= 1);
    assert!(stats.comparison_folds >= 1);
}

#[test]
fn test_default_config_matches() {
    let body = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(4)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut d1 = vec![make_decl(body.clone())];
    let mut d2 = vec![make_decl(body)];
    let s1 = fold_constants_ext2_default(&mut d1);
    let s2 = fold_constants_ext2(&mut d2, &ConstFoldExt2Config::default());
    assert_eq!(s1.total_folds(), s2.total_folds());
    assert_eq!(s1.iterations, s2.iterations);
}

#[test]
fn test_case_with_default_preserved() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: simple_ctor(0),
            body: Box::new(IRBody::Ret(var_arg(10))),
        }],
        default: Some(Box::new(IRBody::Ret(var_arg(99)))),
    };
    let mut decls = vec![make_decl(body)];
    assert_eq!(fold_constants_ext2_default(&mut decls).dead_branch_folds, 0);
    assert!(matches!(
        &decls[0].body,
        IRBody::Case {
            default: Some(_),
            ..
        }
    ));
}

#[test]
fn test_set_settag_uset_sset_passthrough() {
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::SetTag {
            var: var(0),
            tag: 1,
            rest: Box::new(IRBody::USet {
                var: var(0),
                idx: 0,
                value: var(2),
                rest: Box::new(IRBody::SSet {
                    var: var(0),
                    n: 0,
                    offset: 0,
                    value: var(3),
                    ty: IRType::UInt64,
                    rest: Box::new(IRBody::Ret(var_arg(0))),
                }),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    assert_eq!(fold_constants_ext2_default(&mut decls).total_folds(), 0);
}

#[test]
fn test_string_is_empty_integration() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: str_expr(""),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Bool,
            value: apply("String.isEmpty", vec![var_arg(0)]),
            rest: Box::new(IRBody::Ret(var_arg(1))),
        }),
    };
    let mut decls = vec![make_decl(body)];
    assert!(fold_constants_ext2_default(&mut decls).string_folds >= 1);
}

#[test]
fn test_string_length_integration() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: str_expr("hello"),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: apply("String.length", vec![var_arg(0)]),
            rest: Box::new(IRBody::Ret(var_arg(1))),
        }),
    };
    let mut decls = vec![make_decl(body)];
    assert!(fold_constants_ext2_default(&mut decls).string_folds >= 1);
}

#[test]
fn test_bool_not_integration() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Bool,
        value: lit_bool(true),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Bool,
            value: apply("Bool.not", vec![var_arg(0)]),
            rest: Box::new(IRBody::Ret(var_arg(1))),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.boolean_folds >= 1);
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => match rest.as_ref() {
            IRBody::VDecl { value, .. } => assert!(
                matches!(value, IRExpr::Lit(IRLiteral::Bool(false))),
                "got {value:?}"
            ),
            o => panic!("expected VDecl, got {o:?}"),
        },
        o => panic!("expected VDecl, got {o:?}"),
    }
}

#[test]
fn test_partial_eval_pure_function() {
    let body = chain_lets(
        vec![
            (0, lit_u64(10)),
            (1, lit_u64(3)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    assert!(fold_constants_ext2_default(&mut decls).arithmetic_folds >= 1);
}

#[test]
fn test_string_append_integration() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: str_expr("foo"),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: str_expr("bar"),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: apply("String.append", vec![var_arg(0), var_arg(1)]),
                rest: Box::new(IRBody::Ret(var_arg(2))),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    assert!(fold_constants_ext2_default(&mut decls).string_folds >= 1);
}

// -- Partial evaluation: actual folding of pure calls ------------------------

/// Config where the typed sub-folds are off, so a recognized pure/total call
/// is only reachable through the partial-eval branch. This isolates and pins
/// that the partial-eval entry point itself computes the result.
fn partial_eval_only_config() -> ConstFoldExt2Config {
    ConstFoldExt2Config {
        fold_arithmetic: false,
        fold_boolean: false,
        fold_string: false,
        fold_comparisons: false,
        ..Default::default()
    }
}

#[test]
fn test_partial_eval_arith_constant_args_folds_to_constant() {
    let body = chain_lets(
        vec![
            (0, lit_u64(10)),
            (1, lit_u64(3)),
            (2, apply("Nat.add", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert!(stats.partial_eval_folds >= 1, "got {stats:?}");
    assert_eq!(stats.arithmetic_folds, 0, "typed arith disabled: {stats:?}");
    assert!(
        matches!(
            extract_last_vdecl_value(&decls[0].body),
            IRExpr::Lit(IRLiteral::UInt64(13))
        ),
        "got {:?}",
        extract_last_vdecl_value(&decls[0].body)
    );
}

#[test]
fn test_partial_eval_cmp_constant_args_folds_to_bool() {
    let body = chain_lets(
        vec![
            (0, lit_u64(5)),
            (1, lit_u64(5)),
            (2, apply("Nat.beq", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert!(stats.partial_eval_folds >= 1, "got {stats:?}");
    assert!(
        matches!(
            extract_last_vdecl_value(&decls[0].body),
            IRExpr::Lit(IRLiteral::Bool(true))
        ),
        "got {:?}",
        extract_last_vdecl_value(&decls[0].body)
    );
}

#[test]
fn test_partial_eval_bool_constant_args_folds_to_bool() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Bool,
        value: lit_bool(true),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Bool,
            value: lit_bool(true),
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Bool,
                value: apply("Bool.and", vec![var_arg(0), var_arg(1)]),
                rest: Box::new(IRBody::Ret(var_arg(2))),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert!(stats.partial_eval_folds >= 1, "got {stats:?}");
    assert!(
        matches!(
            extract_last_vdecl_value(&decls[0].body),
            IRExpr::Lit(IRLiteral::Bool(true))
        ),
        "got {:?}",
        extract_last_vdecl_value(&decls[0].body)
    );
}

#[test]
fn test_partial_eval_unknown_pure_function_does_not_fold() {
    // `Nat.`-prefixed (so `is_pure_function` is true) but not a recognized
    // total operation: must be left untouched.
    let call = apply("Nat.frobnicate", vec![var_arg(0), var_arg(1)]);
    let body = chain_lets(
        vec![(0, lit_u64(10)), (1, lit_u64(3)), (2, call.clone())],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert_eq!(stats.partial_eval_folds, 0, "got {stats:?}");
    assert_eq!(
        extract_last_vdecl_value(&decls[0].body),
        &call,
        "unknown pure function must be preserved"
    );
}

#[test]
fn test_partial_eval_non_pure_function_does_not_fold() {
    // Not in the pure-function namespace: `is_pure_function` is false.
    let call = apply("My.effectfulFn", vec![var_arg(0), var_arg(1)]);
    let body = chain_lets(
        vec![(0, lit_u64(10)), (1, lit_u64(3)), (2, call.clone())],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert_eq!(stats.partial_eval_folds, 0, "got {stats:?}");
    assert_eq!(
        extract_last_vdecl_value(&decls[0].body),
        &call,
        "non-pure function must be preserved"
    );
}

#[test]
fn test_partial_eval_non_constant_arg_does_not_fold() {
    // Only one operand is a known constant; the other (var 0) is never bound,
    // so the call must not fold.
    let call = apply("Nat.add", vec![var_arg(0), var_arg(1)]);
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(3),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: call.clone(),
            rest: Box::new(IRBody::Ret(var_arg(2))),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert_eq!(stats.partial_eval_folds, 0, "got {stats:?}");
    assert_eq!(
        extract_last_vdecl_value(&decls[0].body),
        &call,
        "call with non-constant arg must be preserved"
    );
}

#[test]
fn test_partial_eval_int_div_by_zero_does_not_fold() {
    // `Int.div` by zero is guarded in `fold_arith` (`if rhs != 0`, returns
    // None); partial eval must not fabricate a result. (`Nat.div` by zero, by
    // contrast, is *total* and folds to 0 — see the test just below.)
    let call = apply("Int.div", vec![var_arg(0), var_arg(1)]);
    let body = chain_lets(
        vec![(0, lit_u64(10)), (1, lit_u64(0)), (2, call.clone())],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert_eq!(stats.partial_eval_folds, 0, "got {stats:?}");
    assert_eq!(
        extract_last_vdecl_value(&decls[0].body),
        &call,
        "Int div-by-zero must be preserved"
    );
}

#[test]
fn test_partial_eval_nat_div_by_zero_folds_to_zero() {
    // Lean `Nat` division is total: `n / 0 = 0`. Partial eval folds it to the
    // constant 0, matching the elaborator simproc `Nat.reduceDiv` and the
    // runtime `eval_int_binop`.
    let body = chain_lets(
        vec![
            (0, lit_u64(10)),
            (1, lit_u64(0)),
            (2, apply("Nat.div", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(&mut decls, &partial_eval_only_config());
    assert!(stats.partial_eval_folds >= 1, "got {stats:?}");
    assert!(
        matches!(
            extract_last_vdecl_value(&decls[0].body),
            IRExpr::Lit(IRLiteral::UInt64(0))
        ),
        "got {:?}",
        extract_last_vdecl_value(&decls[0].body)
    );
}

#[test]
fn test_partial_eval_disabled_does_not_fold() {
    // With both typed arith and partial-eval off, nothing folds the call.
    let call = apply("Nat.add", vec![var_arg(0), var_arg(1)]);
    let body = chain_lets(
        vec![(0, lit_u64(10)), (1, lit_u64(3)), (2, call.clone())],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2(
        &mut decls,
        &ConstFoldExt2Config {
            fold_partial_eval: false,
            ..partial_eval_only_config()
        },
    );
    assert_eq!(stats.partial_eval_folds, 0, "got {stats:?}");
    assert_eq!(
        extract_last_vdecl_value(&decls[0].body),
        &call,
        "partial-eval disabled: call must be preserved"
    );
}
