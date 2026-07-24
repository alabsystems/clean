// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Alt, Arg, Cases, DeclValue, LetDecl, LetValue, Param};
use clean_kernel::{Expr, FVarId, Name};

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

fn list_type() -> Expr {
    Expr::const_str("List")
}

fn pair_type() -> Expr {
    Expr::const_str("Pair")
}

fn uint64_type() -> Expr {
    Expr::const_str("UInt64")
}

fn code_body(decl: &Decl) -> &Code {
    let DeclValue::Code(body) = &decl.body else {
        panic!("expected code declaration");
    };
    body
}

fn count_ops(code: &Code, op_name: &str) -> usize {
    match code {
        Code::Let(decl, body) => {
            let matches_op = matches!(
                &decl.value,
                LetValue::Const { name, .. } if name.to_string() == op_name
            );
            (if matches_op { 1 } else { 0 }) + count_ops(body, op_name)
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            count_ops(&fun_decl.body, op_name) + count_ops(body, op_name)
        }
        Code::Cases(cases) => cases
            .alts
            .iter()
            .map(|alt| match alt {
                Alt::Ctor { body, .. } => count_ops(body, op_name),
                Alt::Default(body) => count_ops(body, op_name),
            })
            .sum(),
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 0,
    }
}

fn count_ops_on_fvar(code: &Code, op_name: &str, target: FVarId) -> usize {
    match code {
        Code::Let(decl, body) => {
            let matches_op = matches!(
                &decl.value,
                LetValue::Const { name, args, .. }
                    if name.to_string() == op_name
                        && matches!(args.first(), Some(Arg::FVar(id)) if *id == target)
            );
            (if matches_op { 1 } else { 0 }) + count_ops_on_fvar(body, op_name, target)
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            count_ops_on_fvar(&fun_decl.body, op_name, target)
                + count_ops_on_fvar(body, op_name, target)
        }
        Code::Cases(cases) => cases
            .alts
            .iter()
            .map(|alt| match alt {
                Alt::Ctor { body, .. } => count_ops_on_fvar(body, op_name, target),
                Alt::Default(body) => count_ops_on_fvar(body, op_name, target),
            })
            .sum(),
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 0,
    }
}

fn count_join_points(code: &Code) -> usize {
    match code {
        Code::Let(_, body) => count_join_points(body),
        Code::Fun(fun_decl, body) => count_join_points(&fun_decl.body) + count_join_points(body),
        Code::JoinPoint(fun_decl, body) => {
            1 + count_join_points(&fun_decl.body) + count_join_points(body)
        }
        Code::Cases(cases) => cases
            .alts
            .iter()
            .map(|alt| match alt {
                Alt::Ctor { body, .. } => count_join_points(body),
                Alt::Default(body) => count_join_points(body),
            })
            .sum(),
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 0,
    }
}

fn count_native_reuse(code: &Code) -> usize {
    match code {
        Code::Let(decl, body) => {
            let reuse_here = usize::from(matches!(&decl.value, LetValue::Reuse { .. }));
            reuse_here + count_native_reuse(body)
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            count_native_reuse(&fun_decl.body) + count_native_reuse(body)
        }
        Code::Cases(cases) => cases
            .alts
            .iter()
            .map(|alt| match alt {
                Alt::Ctor { body, .. } => count_native_reuse(body),
                Alt::Default(body) => count_native_reuse(body),
            })
            .sum(),
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 0,
    }
}

fn make_branching_reuse_decl() -> Decl {
    let alt_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("newHead"),
            nat_type(),
            LetValue::Const {
                name: name("f"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(1))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("rebuilt"),
                list_type(),
                LetValue::Ctor {
                    name: name("List.cons"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(11)),
        ),
    );
    let code = Code::Cases(Cases {
        type_name: name("List"),
        result_type: list_type(),
        scrutinee: fvar(0),
        alts: vec![
            Alt::Ctor {
                ctor_name: name("List.cons"),
                params: vec![
                    Param::new(fvar(1), name("h"), nat_type()),
                    Param::new(fvar(2), name("t"), list_type()),
                ],
                body: Box::new(alt_body),
            },
            Alt::Default(Box::new(Code::ret(fvar(0)))),
        ],
    });
    Decl::new(
        name("mapHead"),
        vec![],
        list_type(),
        vec![Param::new(fvar(0), name("xs"), list_type())],
        code,
        false,
    )
}

fn make_projection_reuse_decl() -> Decl {
    let alt_body = Code::let_bind(
        LetDecl::new(
            fvar(10),
            name("p0"),
            nat_type(),
            LetValue::Proj {
                type_name: name("Pair"),
                idx: 0,
                structure: fvar(0),
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(11),
                name("p1"),
                nat_type(),
                LetValue::Proj {
                    type_name: name("Pair"),
                    idx: 1,
                    structure: fvar(0),
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(12),
                    name("rebuilt"),
                    pair_type(),
                    LetValue::Ctor {
                        name: name("Pair.mk"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(10)), Arg::FVar(fvar(11))],
                    },
                ),
                Code::ret(fvar(12)),
            ),
        ),
    );
    let code = Code::Cases(Cases {
        type_name: name("Pair"),
        result_type: pair_type(),
        scrutinee: fvar(0),
        alts: vec![Alt::Ctor {
            ctor_name: name("Pair.mk"),
            params: vec![
                Param::new(fvar(1), name("a"), nat_type()),
                Param::new(fvar(2), name("b"), nat_type()),
            ],
            body: Box::new(alt_body),
        }],
    });
    Decl::new(
        name("clonePair"),
        vec![],
        pair_type(),
        vec![Param::new(fvar(0), name("p"), pair_type())],
        code,
        false,
    )
}

#[test]
fn test_config_default() {
    let config = RCConfig::default();
    assert!(config.enable_reset_reuse);
    assert!(!config.cross_family_reuse);
    assert!(config.expand_reset_reuse);
}

#[test]
fn test_config_minimal() {
    let config = RCConfig::minimal();
    assert!(!config.enable_reset_reuse);
    assert!(!config.cross_family_reuse);
    assert!(!config.expand_reset_reuse);
}

#[test]
fn test_transform_simple_identity() {
    // def id (x : Nat) : Nat := return x
    let decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let config = RCConfig::minimal();
    let result = transform_decl(&decl, &config);

    // Should have minimal transformation
    assert_eq!(result.name, name("id"));
}

#[test]
fn test_transform_with_constructor() {
    // def wrap (x : Nat) : Box Nat :=
    //   let _1 := Box.mk x
    //   return _1
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Box.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );

    let decl = Decl::new(
        name("wrap"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        code,
        false,
    );

    let config = RCConfig::default();
    let result = transform_decl(&decl, &config);

    // Should have RC operations
    let s = format!("{:?}", result);
    // Verify transformation completed (specific content depends on phases)
    assert!(s.contains("wrap") || s.contains("Box.mk"));
}

#[test]
fn test_transform_batch() {
    let decl1 = Decl::new(
        name("f1"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(1)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let decl2 = Decl::new(
        name("f2"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(2)),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let config = RCConfig::default();
    let results = transform(&[decl1, decl2], &config);

    assert_eq!(results.len(), 2);
    assert_eq!(results[0].name, name("f1"));
    assert_eq!(results[1].name, name("f2"));
}

#[test]
fn test_transform_code_standalone() {
    let code = Code::let_bind(
        LetDecl::new(fvar(1), name("_1"), nat_type(), LetValue::nat(42)),
        Code::ret(fvar(1)),
    );

    let config = RCConfig::minimal();
    let result = transform_code(&code, &config);

    // Should pass through with minimal changes
    match result {
        Code::Let(decl, _) => {
            assert_eq!(decl.fvar_id, fvar(1));
        }
        _ => panic!("Expected Let"),
    }
}

#[test]
fn test_full_pipeline_branching_reuse_expands_to_runtime_control_flow() {
    let result = transform_decl(&make_branching_reuse_decl(), &RCConfig::default());
    let body = code_body(&result);
    let rendered = format!("{body:?}");

    assert_eq!(
        count_ops(body, "_isShared"),
        1,
        "full pipeline should materialize one runtime share check: {rendered}"
    );
    assert!(
        count_join_points(body) >= 1,
        "expanded reset/reuse should create a shared join point: {rendered}"
    );
    assert_eq!(
        count_native_reuse(body),
        0,
        "expand phase should eliminate native reuse nodes: {rendered}"
    );
    assert_eq!(
        count_ops(body, "_reset"),
        0,
        "expand phase should eliminate reset pseudo-ops: {rendered}"
    );
    assert!(
        count_ops(body, "_set") >= 1,
        "fast path should reuse storage via field updates: {rendered}"
    );
    assert!(
        count_ops(body, "_dec") >= 1,
        "slow path should still release the original object once: {rendered}"
    );
}

#[test]
fn test_full_pipeline_projection_reuse_moves_masked_incs_to_slow_path() {
    let result = transform_decl(&make_projection_reuse_decl(), &RCConfig::default());
    let body = code_body(&result);
    let rendered = format!("{body:?}");

    assert_eq!(
        count_ops(body, "_isShared"),
        1,
        "projection reuse should still expand through one isShared branch: {rendered}"
    );
    assert_eq!(
        count_native_reuse(body),
        0,
        "full pipeline should consume native reuse nodes: {rendered}"
    );
    assert_eq!(
        count_ops(body, "_set"),
        0,
        "self-set projections should be elided from the fast path: {rendered}"
    );
    assert_eq!(
        count_ops_on_fvar(body, "_inc", fvar(10)),
        2,
        "the first projected field should be kept alive by exactly two targeted increments: {rendered}"
    );
    assert_eq!(
        count_ops_on_fvar(body, "_inc", fvar(11)),
        2,
        "the second projected field should be kept alive by exactly two targeted increments: {rendered}"
    );
    assert_eq!(
        count_ops_on_fvar(body, "_dec", fvar(0)),
        2,
        "the original pair should be released on the two expanded reuse paths: {rendered}"
    );
    assert_eq!(
        count_ops_on_fvar(body, "_dec", fvar(1)),
        1,
        "the first case-bound Pair field should see exactly one cleanup decrement from insert RC: {rendered}"
    );
    assert_eq!(
        count_ops_on_fvar(body, "_dec", fvar(2)),
        1,
        "the second case-bound Pair field should see exactly one cleanup decrement from insert RC: {rendered}"
    );
}

#[test]
fn test_full_pipeline_scalar_only_function_has_zero_rc_ops() {
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            pair_type(),
            LetValue::Ctor {
                name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );
    let decl = Decl::new(
        name("dupScalar"),
        vec![],
        pair_type(),
        vec![Param::new(fvar(0), name("x"), uint64_type())],
        code,
        false,
    );

    let result = transform_decl(&decl, &RCConfig::default());
    let body = code_body(&result);
    let rendered = format!("{body:?}");

    assert_eq!(
        count_ops(body, "_inc"),
        0,
        "scalar parameters should not acquire increments in the full pipeline: {rendered}"
    );
    assert_eq!(
        count_ops(body, "_dec"),
        0,
        "scalar-only code should not acquire decrements in the full pipeline: {rendered}"
    );
    assert_eq!(
        count_ops(body, "_isShared"),
        0,
        "scalar-only code should not trigger reset/reuse expansion: {rendered}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// FVarIdAllocator tests (Part of #1106)
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_fvar_allocator_monotonic() {
    let mut alloc = FVarIdAllocator::new(100);
    let id1 = alloc.fresh().unwrap();
    let id2 = alloc.fresh().unwrap();
    let id3 = alloc.fresh().unwrap();

    assert_eq!(id1.as_u64(), 100);
    assert_eq!(id2.as_u64(), 101);
    assert_eq!(id3.as_u64(), 102);
    assert!(id3.as_u64() > id2.as_u64());
    assert!(id2.as_u64() > id1.as_u64());
}

#[test]
fn test_fvar_allocator_pass_ranges() {
    let expand = FVarIdAllocator::for_expand_reset();
    let reset = FVarIdAllocator::for_reset_reuse();
    let insert = FVarIdAllocator::for_insert_rc();

    // Each pass starts in its reserved range
    assert_eq!(expand.current(), fvar_ranges::EXPAND_RESET_START);
    assert_eq!(reset.current(), fvar_ranges::RESET_REUSE_START);
    assert_eq!(insert.current(), fvar_ranges::INSERT_RC_START);

    // Ranges are disjoint (compile-time check)
    const { assert!(fvar_ranges::EXPAND_RESET_START < fvar_ranges::RESET_REUSE_START) };
    const { assert!(fvar_ranges::RESET_REUSE_START < fvar_ranges::INSERT_RC_START) };
}

#[test]
fn test_fvar_allocator_overflow_protection() {
    // Create allocator near the limit
    let mut alloc = FVarIdAllocator::new(fvar_ranges::MAX_FVAR_ID);

    // Should return None at limit
    assert_eq!(alloc.fresh(), None, "expected None at fvar limit");
}

#[test]
fn test_fvar_allocator_near_limit() {
    // Create allocator just before the limit
    let mut alloc = FVarIdAllocator::new(fvar_ranges::MAX_FVAR_ID - 2);

    // Can allocate twice — verify allocated IDs
    let id1 = alloc.fresh().expect("first allocation should succeed");
    assert_eq!(id1.as_u64(), fvar_ranges::MAX_FVAR_ID - 2);
    let id2 = alloc.fresh().expect("second allocation should succeed");
    assert_eq!(id2.as_u64(), fvar_ranges::MAX_FVAR_ID - 1);

    // Third allocation hits limit
    assert_eq!(alloc.fresh(), None, "expected None at fvar limit");
}

#[test]
fn test_fvar_allocator_default() {
    let mut alloc = FVarIdAllocator::default();
    assert_eq!(alloc.current(), 0);

    let id = alloc.fresh().unwrap();
    assert_eq!(id.as_u64(), 0);
}
