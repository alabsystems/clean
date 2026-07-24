// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use clean_compiler::ir::{IRArg, IRBody, VarId};
use clean_compiler::lcnf::{Arg, Cases, Code, Decl, FunDecl, LetDecl, LetValue, Param};
use clean_compiler::to_ir::{lower_decl, lower_decl_with_env};
use clean_compiler::CompilerError;
use clean_compiler::CtorMeta;
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

#[test]
fn test_lower_decl_rejects_unbound_case_scrutinee() {
    let decl = Decl::new(
        name("absurd_match"),
        vec![],
        nat_type(),
        vec![],
        Code::Cases(Cases::new(name("Nat"), nat_type(), fvar(99), vec![])),
        false,
    );

    let err = lower_decl(&decl).expect_err("unbound scrutinee must fail closed");
    assert!(matches!(
        err,
        CompilerError::UnboundToIrVar { fvar: actual_fvar } if actual_fvar == fvar(99)
    ));
}

// Part of #1976 - Lambda lifting eliminates Code::Fun before IR lowering
#[test]
fn test_lower_decl_lifts_local_function() {
    let local_fn = FunDecl {
        fvar_id: fvar(10),
        name: name("g"),
        params: vec![Param::new(fvar(1), name("y"), nat_type())],
        ty: nat_type(),
        body: Box::new(Code::ret(fvar(1))),
    };

    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::fun(local_fn, Code::ret(fvar(0))),
        false,
    );

    // Lambda lifting converts Code::Fun to a top-level declaration, so
    // lower_decl succeeds where it previously failed with UnexpectedLocalFunction.
    let ir_decl = lower_decl(&decl)
        .expect("lower_decl succeeds after lambda lifting")
        .expect("decl is not extern");
    assert_eq!(ir_decl.name, name("f"));
    assert!(matches!(ir_decl.body, IRBody::Ret(IRArg::Var(VarId(0)))));
}

#[test]
fn test_lower_decl_rejects_reuse_with_unbound_slot() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("x"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("_1"),
                nat_type(),
                LetValue::Reuse {
                    slot: fvar(99),
                    ctor_name: name("Box.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let err = lower_decl(&decl).expect_err("reuse with unbound slot must fail closed");
    assert!(matches!(
        err,
        CompilerError::UnboundToIrVar { fvar: actual_fvar } if actual_fvar == fvar(99)
    ));
}

#[test]
fn test_lower_decl_with_env_lowers_set_tag_using_ctor_metadata() {
    let mut ctor_env = HashMap::new();
    ctor_env.insert(
        name("Color.blue"),
        CtorMeta {
            num_params: 0,
            tag: 1,
            field_types: vec![],
            num_scalars: 0,
            num_objects: 0,
        },
    );

    let decl = Decl::new(
        name("retag"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("obj"), nat_type())],
        Code::let_bind(
            LetDecl::new(
                fvar(1),
                name("_setTag"),
                Expr::const_str("_"),
                LetValue::Const {
                    name: name("_setTag"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(0)), Arg::Type(Expr::const_str("Color.blue"))],
                },
            ),
            Code::ret(fvar(0)),
        ),
        false,
    );

    let (ir_opt, _warnings) =
        lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &HashMap::new())
            .expect("lowering should succeed");
    let ir = ir_opt.expect("decl is not extern");

    match &ir.body {
        IRBody::SetTag { var, tag, rest } => {
            assert_eq!(*var, VarId(0));
            assert_eq!(*tag, 1);
            assert!(matches!(rest.as_ref(), IRBody::Ret(IRArg::Var(VarId(0)))));
        }
        other => panic!("expected SetTag, got {other:?}"),
    }
}
