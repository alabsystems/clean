// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-coverage tests for constructor scalar field handling.
//!
//! These tests verify edge cases in `split_scalar_ctor_args` and
//! `partition_ctor_fields` introduced by the #1993 fix. Specifically:
//!
//! 1. Reuse + scalar fields (previously untested path)
//! 2. All-scalar constructors (num_objects = 0)
//! 3. Erased field before scalar field (documents #1994 alignment bug)
//!
//! Part of #1993, #1994.

use std::collections::HashMap;

use clean_compiler::ir::{IRBody, IRExpr, IRType, VarId};
use clean_compiler::lcnf::{Arg, Code, Decl, LetDecl, LetValue, Param};
use clean_compiler::to_ir::lower_decl_with_env;
use clean_compiler::to_ir::CtorMeta;
use clean_kernel::{Expr, FVarId, Name};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

/// Lower a Decl with the given ctor_env and return the IRDecl.
fn lower_with_ctors(decl: &Decl, ctor_env: &HashMap<Name, CtorMeta>) -> IRBody {
    let (ir_decl, _warnings) =
        lower_decl_with_env(decl, &HashMap::new(), ctor_env, &HashMap::new())
            .expect("lowering should succeed");
    ir_decl.expect("lowering should succeed").body
}

/// Assert an SSet node matches expected (var, n, offset, ty) and return the rest.
fn assert_sset(body: &IRBody, var: VarId, n: u32, offset: u32, ty: IRType) -> &IRBody {
    match body {
        IRBody::SSet {
            var: v,
            n: sn,
            offset: so,
            ty: st,
            rest,
            ..
        } => {
            assert_eq!(*v, var, "SSet var mismatch");
            assert_eq!(*sn, n, "SSet n mismatch");
            assert_eq!(*so, offset, "SSet offset mismatch");
            assert_eq!(*st, ty, "SSet ty mismatch");
            rest.as_ref()
        }
        other => panic!("Expected SSet, got {:?}", other),
    }
}

/// Reuse with scalar fields generates SSet (proof_coverage).
///
/// `split_scalar_ctor_args` handles both Ctor and Reuse, but prior inline
/// tests only exercised Ctor. This test verifies Reuse produces equivalent SSet.
#[test]
fn test_reuse_scalar_field_generates_sset() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("WithScalar.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt64, IRType::Object],
            num_scalars: 1,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("reuse_scalar"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("slot"), nat_type()),
            Param::new(fvar(1), name("u64_val"), Expr::const_str("UInt64")),
            Param::new(fvar(2), name("obj"), nat_type()),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(3),
                name("_1"),
                nat_type(),
                LetValue::Reuse {
                    slot: fvar(0),
                    ctor_name: name("WithScalar.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                },
            ),
            Code::ret(fvar(3)),
        ),
        false,
    );

    let body = lower_with_ctors(&decl, &ctor_env);
    match &body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            match value {
                IRExpr::Reuse { ctor, args, .. } => {
                    assert_eq!(ctor.num_scalars, 1);
                    assert_eq!(args.len(), 1, "Reuse.args should only contain object args");
                }
                other => panic!("Expected Reuse, got {:?}", other),
            }
            assert_sset(rest, *ctor_var, 1, 0, IRType::UInt64);
        }
        _ => panic!("Expected VDecl"),
    }
}

/// All-scalar constructor (num_objects=0, num_scalars>0).
///
/// `partition_ctor_fields` must handle the case where ALL fields are scalar
/// and no object args remain. Ctor.args should be empty.
#[test]
fn test_ctor_all_scalar_no_objects() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Packed.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            field_types: vec![IRType::UInt32, IRType::UInt64],
            num_scalars: 2,
            num_objects: 0,
        },
    );

    let decl = Decl::new(
        name("mk_packed"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(0), name("a"), Expr::const_str("UInt32")),
            Param::new(fvar(1), name("b"), Expr::const_str("UInt64")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Packed.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let body = lower_with_ctors(&decl, &ctor_env);
    match &body {
        IRBody::VDecl {
            var: ctor_var,
            value,
            rest,
            ..
        } => {
            match value {
                IRExpr::Ctor { info, args } => {
                    assert_eq!(info.num_objects, 0);
                    assert_eq!(info.num_scalars, 2);
                    assert_eq!(args.len(), 0, "all-scalar Ctor should have empty args");
                }
                other => panic!("Expected Ctor, got {:?}", other),
            }
            // SSet chain: UInt32 at (n=0, off=0), then UInt64 at (n=0, off=4)
            let rest2 = assert_sset(rest, *ctor_var, 0, 0, IRType::UInt32);
            assert_sset(rest2, *ctor_var, 0, 4, IRType::UInt64);
        }
        _ => panic!("Expected VDecl"),
    }
}

/// Ctor with erased (proof) arg preceding scalar field (documents #1994 bug).
///
/// When #1994 is fixed, this test will fail — update it to verify correct
/// SSet generation.
#[test]
fn test_ctor_erased_before_scalar_misalignment() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("ProofFirst.mk"),
        CtorMeta {
            num_params: 0,
            tag: 0,
            // Proof field mapped to Object by expr_to_ir_type, then UInt64.
            field_types: vec![IRType::Object, IRType::UInt64],
            num_scalars: 1,
            num_objects: 1,
        },
    );

    let decl = Decl::new(
        name("mk_proof_first"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("data"), Expr::const_str("UInt64"))],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_1"),
                nat_type(),
                LetValue::Ctor {
                    name: name("ProofFirst.mk"),
                    levels: vec![],
                    args: vec![Arg::Erased, Arg::FVar(fvar(0))],
                },
            ),
            Code::ret(fvar(1)),
        ),
        false,
    );

    let body = lower_with_ctors(&decl, &ctor_env);
    match &body {
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Ctor { info, args } => {
                    // After alignment fix (#2123): field_types excludes erased proof field.
                    assert_eq!(info.field_types, vec![IRType::UInt64]);
                    assert_eq!(info.num_scalars, 1);
                    assert_eq!(info.num_objects, 0);
                    assert_eq!(args.len(), 0, "UInt64 data extracted as scalar, not object");
                }
                other => panic!("Expected Ctor, got {:?}", other),
            }
            // SSet generated for the UInt64 scalar field.
            let has_sset = matches!(rest.as_ref(), IRBody::SSet { .. });
            assert!(has_sset, "SSet should be generated for UInt64 scalar field");
        }
        _ => panic!("Expected VDecl"),
    }
}
