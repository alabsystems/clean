// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A constructor field whose declared type is a universe (`α : Type`) is a
//! type: erased at runtime, its slot an object holding `clean_box(0)`
//! (`types::ctor_field_ir_type`). Before it, `build_ctor_env` refused the WHOLE
//! environment's constructor table at the first such field, so every program
//! elaborated over `import Lean` was refused at lowering. The end-to-end row,
//! with Lean's own output as the oracle, is
//! `crates/clean/tests/sort_typed_ctor_field_cli.rs`.

use super::*;
use crate::error::CompilerError;
use crate::ir::{IRArg, IRBody, IRExpr, IRType, VarId};
use crate::lcnf::{Arg, Code, Decl, LetDecl, LetValue, Param};
use clean_kernel::{BinderInfo, ConstructorVal, Expr, ExprKind, FVarId, Level, Name};
use std::collections::HashMap;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// `Box.mk : (α : Type) → Nat → Bool → Nat → Box` -- the shape of
/// `structure Box where α : Type; n : Nat; b : Bool; m : Nat`.
fn box_mk() -> ConstructorVal {
    let field = |domain: Expr, rest: Expr| Expr::pi(BinderInfo::Default, domain, rest);
    ConstructorVal {
        name: name("Box.mk"),
        inductive_name: name("Box"),
        level_params: vec![],
        type_: field(
            Expr::type_(),
            field(
                Expr::const_str("Nat"),
                field(
                    Expr::const_str("Bool"),
                    field(Expr::const_str("Nat"), Expr::const_str("Box")),
                ),
            ),
        ),
        num_params: 0,
        num_fields: 4,
        constructor_idx: 0,
    }
}

fn single_field_ctor(ctor: &str, domain: Expr) -> ConstructorVal {
    ConstructorVal {
        name: name(ctor),
        inductive_name: name(ctor.rsplit_once('.').map_or(ctor, |(ind, _)| ind)),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, domain, Expr::const_str("T")),
        num_params: 0,
        num_fields: 1,
        constructor_idx: 0,
    }
}

#[test]
fn sort_typed_field_is_an_object_slot() {
    let ctor = box_mk();
    let (ctor_env, inductive_env) =
        build_ctor_env(&[&ctor]).expect("a Sort-typed field must not refuse the table");
    let meta = &ctor_env[&name("Box.mk")];
    assert_eq!(
        meta.field_types,
        vec![IRType::Object, IRType::Object, IRType::Bool, IRType::Object]
    );
    assert_eq!((meta.num_objects, meta.num_scalars), (3, 1));
    assert_eq!(inductive_env[&name("Box")].field_types, meta.field_types);
}

#[test]
fn every_universe_spelling_is_a_type_field() {
    for (ctor, domain) in [
        ("Sp.mk", Expr::prop()),
        ("Su.mk", Expr::sort(Level::param(name("u")))),
        ("Ss.mk", Expr::sort(Level::succ(Level::param(name("v"))))),
        ("Sx.mk", Expr::from_kind(ExprKind::SProp)),
    ] {
        let ctor = single_field_ctor(ctor, domain);
        let (ctor_env, _) = build_ctor_env(&[&ctor]).unwrap_or_else(|error| {
            panic!("{}: a universe-typed field refused: {error}", ctor.name)
        });
        assert_eq!(ctor_env[&ctor.name].field_types, vec![IRType::Object]);
    }
}

#[test]
fn a_field_type_with_no_runtime_reading_is_still_refused_and_names_its_constructor() {
    // A literal is not a type at all: the refusal stays, and it now says
    // WHICH constructor -- the alphabetically first of the refused ones, so
    // the message no longer depends on the environment's hash order.
    let later = single_field_ctor("Zed.mk", Expr::nat_lit(3));
    let earlier = single_field_ctor("Alpha.mk", Expr::nat_lit(4));
    let fine = box_mk();
    for order in [[&later, &fine, &earlier], [&earlier, &later, &fine]] {
        let error = build_ctor_env(&order).expect_err("a literal field type has no IR type");
        assert!(
            matches!(&error, CompilerError::UnsupportedIrType { expr } if expr.contains("constructor Alpha.mk")),
            "{error}"
        );
    }
}

/// `mkBox (k : Nat) (b : Bool) : Box := Box.mk Nat k b k`, then the read of
/// field 3 (`m`). The type argument is erased by LCNF (`Arg::Type`) and fills
/// the object slot it owns, so `m` is object 2 and `b` is the scalar byte
/// after three object slots -- the same counting every reader does.
#[test]
fn erased_type_argument_fills_its_slot_and_later_fields_keep_their_index() {
    let ctor = box_mk();
    let (ctor_env, inductive_env) = build_ctor_env(&[&ctor]).expect("table");
    let fvar = FVarId::new;
    let decl = Decl::new(
        name("mkBoxM"),
        vec![],
        Expr::const_str("Nat"),
        vec![
            Param::new(fvar(0), name("k"), Expr::const_str("Nat")),
            Param::new(fvar(1), name("b"), Expr::const_str("Bool")),
        ],
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("x"),
                Expr::const_str("Box"),
                LetValue::Ctor {
                    name: name("Box.mk"),
                    levels: vec![],
                    args: vec![
                        Arg::Type(Expr::const_str("Nat")),
                        Arg::FVar(fvar(0)),
                        Arg::FVar(fvar(1)),
                        Arg::FVar(fvar(0)),
                    ],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("m"),
                    Expr::const_str("Nat"),
                    LetValue::Proj {
                        type_name: name("Box"),
                        idx: 3,
                        structure: fvar(2),
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
        false,
    );
    let (ir, _warnings) = lower_decl_with_env(&decl, &HashMap::new(), &ctor_env, &inductive_env)
        .expect("lowering a Box with an erased type field");
    let ir = ir.expect("not an extern");
    let IRBody::VDecl {
        value: IRExpr::Ctor { info, args },
        rest,
        ..
    } = &ir.body
    else {
        panic!("expected the constructor first, got {:?}", ir.body);
    };
    assert_eq!((info.num_objects, info.num_scalars), (3, 1));
    assert!(
        matches!(
            args.as_slice(),
            [IRArg::Erased, IRArg::Var(_), IRArg::Var(_)]
        ),
        "the erased type fills object slot 0 and the two Nats slots 1 and 2: {args:?}"
    );
    let mut body = rest.as_ref();
    let projection = loop {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                if let IRExpr::Proj { .. } = value {
                    break value;
                }
                body = rest;
            }
            IRBody::SSet { rest, .. } | IRBody::USet { rest, .. } => body = rest,
            other => panic!("no projection of `m` found: {other:?}"),
        }
    };
    assert!(
        matches!(
            projection,
            IRExpr::Proj {
                idx: 2,
                ty: IRType::Object,
                arg: IRArg::Var(VarId(_))
            }
        ),
        "`m` is object 2 (after the type slot and `n`): {projection:?}"
    );
    let (scalar, _) = compute_proj_expr(
        &name("Box"),
        &ctor_env[&name("Box.mk")].field_types,
        2,
        IRArg::Var(VarId(0)),
    )
    .expect("project `b`");
    assert!(
        matches!(
            scalar,
            IRExpr::SProj {
                n: 3,
                offset: 0,
                ty: IRType::Bool,
                ..
            }
        ),
        "`b` is the first scalar byte after three object slots: {scalar:?}"
    );
}
