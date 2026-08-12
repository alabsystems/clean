// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended derive handlers: Fintype, Countable, ToExpr,
//! OfScientific, composition, validation, diagnostics, and registry.

use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, ExprKind, InductiveDecl,
    InductiveType, Level, Name,
};

use crate::derive::DeriveError;
use crate::derive_ext_handlers2::{CtorInfo2, DerivedDecl2, ExtDeriveHandler2};
use crate::derive_handlers_ext::{
    ComposedDeriveHandler, DeriveCountable, DeriveDiagnostic, DeriveDiagnosticSeverity,
    DeriveFintype, DeriveOfScientific, DerivePreconditionChecker, DeriveToExpr,
    ExtendedDeriveRegistry,
};

// ---------------------------------------------------------------------------
// Test data helpers
// ---------------------------------------------------------------------------

fn color_ctors() -> Vec<CtorInfo2> {
    vec![
        CtorInfo2 {
            name: Name::from_string("Color.Red"),
            fields: vec![],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("Color.Blue"),
            fields: vec![],
            is_recursive: false,
        },
    ]
}

fn point_ctors() -> Vec<CtorInfo2> {
    let nat = Expr::const_str("Nat");
    vec![CtorInfo2 {
        name: Name::from_string("Point.mk"),
        fields: vec![
            (Name::from_string("x"), nat.clone()),
            (Name::from_string("y"), nat),
        ],
        is_recursive: false,
    }]
}

fn empty_ctors() -> Vec<CtorInfo2> {
    vec![]
}

fn recursive_ctors() -> Vec<CtorInfo2> {
    vec![CtorInfo2 {
        name: Name::from_string("Tree.node"),
        fields: vec![
            (Name::from_string("left"), Expr::const_str("Tree")),
            (Name::from_string("right"), Expr::const_str("Tree")),
        ],
        is_recursive: true,
    }]
}

fn single_nullary_ctor() -> Vec<CtorInfo2> {
    vec![CtorInfo2 {
        name: Name::from_string("Unit.unit"),
        fields: vec![],
        is_recursive: false,
    }]
}

// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#[allow(dead_code)]
fn many_field_ctor() -> Vec<CtorInfo2> {
    let fields: Vec<(Name, Expr)> = (0..20)
        .map(|i| (Name::from_string(&format!("f{i}")), Expr::const_str("Nat")))
        .collect();
    vec![CtorInfo2 {
        name: Name::from_string("Big.mk"),
        fields,
        is_recursive: false,
    }]
}

fn wrapper_ctor() -> Vec<CtorInfo2> {
    vec![CtorInfo2 {
        name: Name::from_string("Wrapper.mk"),
        fields: vec![(Name::from_string("val"), Expr::const_str("Nat"))],
        is_recursive: false,
    }]
}

fn type_expr() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

/// Bare prelude environment. The handlers in this module (Fintype, Countable,
/// ToExpr, OfScientific, and the composed/registry dispatchers) do not resolve
/// field instances, so they ignore `env`; this fixture satisfies the parameter.
fn derive_env() -> Environment {
    Environment::with_prelude()
}

fn assert_unsupported<T: std::fmt::Debug>(result: Result<T, DeriveError>, class_name: &str) {
    match result {
        Err(DeriveError::Unsupported {
            class_name: got, ..
        }) => assert_eq!(got, class_name),
        other => panic!("expected Unsupported for {class_name}, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// DeriveFintype tests
// ---------------------------------------------------------------------------

#[test]
fn test_fintype_enum_produces_instance() {
    let handler = DeriveFintype;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("Fintype should succeed for enum");
    assert_eq!(decls.len(), 1);
    assert!(decls.iter().any(|d| d.is_instance));
    assert!(decls.iter().any(|d| d.name.to_string().contains("Fintype")));
}

#[test]
fn test_fintype_recursive_rejected() {
    let handler = DeriveFintype;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported { class_name, .. } => assert_eq!(class_name, "Fintype"),
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_fintype_empty_type_rejected() {
    let handler = DeriveFintype;
    let tn = Name::from_string("Empty");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_fintype_single_ctor() {
    let handler = DeriveFintype;
    let tn = Name::from_string("Unit");
    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &single_nullary_ctor(),
            0,
            &[],
        )
        .expect("Fintype for Unit should succeed");
    assert!(decls.iter().any(|d| d.is_instance));
}

#[test]
fn test_fintype_struct_with_fields_rejected() {
    // Fintype requires nullary constructors per PreconditionSpec
    let handler = DeriveFintype;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// DeriveCountable tests
// ---------------------------------------------------------------------------

#[test]
fn test_countable_enum_fails_closed() {
    let handler = DeriveCountable;
    let tn = Name::from_string("Color");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[]);
    assert_unsupported(result, "Countable");
}

#[test]
fn test_countable_recursive_rejected() {
    let handler = DeriveCountable;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_countable_empty_rejected() {
    let handler = DeriveCountable;
    let tn = Name::from_string("Empty");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_countable_nullary_single_ctor_fails_closed() {
    let handler = DeriveCountable;
    let tn = Name::from_string("Unit");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &single_nullary_ctor(),
        0,
        &[],
    );
    assert_unsupported(result, "Countable");
}

// ---------------------------------------------------------------------------
// DeriveToExpr tests
// ---------------------------------------------------------------------------

#[test]
fn test_to_expr_enum() {
    let handler = DeriveToExpr;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("ToExpr should succeed");
    assert_eq!(decls.len(), 1);
    assert!(decls.iter().any(|d| d.is_instance));
}

#[test]
fn test_to_expr_struct_without_field_instance_fails_closed() {
    let handler = DeriveToExpr;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert_unsupported(result, "ToExpr");
}

#[test]
fn test_to_expr_single_ctor() {
    let handler = DeriveToExpr;
    let tn = Name::from_string("Unit");
    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &single_nullary_ctor(),
            0,
            &[],
        )
        .expect("ToExpr for Unit");
    assert!(decls.iter().any(|d| d.is_instance));
}

#[test]
fn test_to_expr_empty_rejected() {
    // ToExpr PreconditionSpec requires min_ctors=1
    let handler = DeriveToExpr;
    let tn = Name::from_string("Empty");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// DeriveToExpr soundness tests (sorry-free for the nullary-enum shape)
// ---------------------------------------------------------------------------
//
// `expr_any` / `expr_contains_sorry` are defined with the OfScientific
// soundness tests above and reused here.

#[test]
fn test_to_expr_nullary_enum_value_is_sorry_free() {
    let handler = DeriveToExpr;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("ToExpr should succeed for nullary enum");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "nullary-enum ToExpr instance value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The genuine instance reflects each constructor through Lean.Expr.const
    // and dispatches via the enum recursor.
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Const(name, _) if name.to_string() == "Lean.Expr.const"
        )),
        "instance value should reflect constructors via Lean.Expr.const"
    );
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Const(name, _) if name.to_string() == "Color.rec"
        )),
        "instance value should dispatch through the enum recursor Color.rec"
    );
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Const(name, _) if name.to_string() == "Lean.ToExpr.mk"
        )),
        "instance value should use Lean.ToExpr.mk"
    );
}

#[test]
fn test_to_expr_single_nullary_ctor_is_sorry_free() {
    let handler = DeriveToExpr;
    let tn = Name::from_string("Unit");
    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &single_nullary_ctor(),
            0,
            &[],
        )
        .expect("ToExpr should succeed for single nullary ctor");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "single nullary ctor ToExpr value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
}

#[test]
fn test_to_expr_struct_with_fields_fails_closed() {
    let handler = DeriveToExpr;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert_unsupported(result, "ToExpr");
}

#[test]
fn test_to_expr_parametric_enum_fails_closed() {
    let handler = DeriveToExpr;
    let tn = Name::from_string("PColor");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 1, &[]);
    assert_unsupported(result, "ToExpr");
}

/// Build an environment with the reflection inductives the derived `ToExpr`
/// instance refers to (`Lean.Name`, `Lean.Level`, `Lean.Expr`, `Lean.ToExpr`)
/// plus a `Color` nullary enum, then return it.
///
/// `Nat`, `String`, `Bool`, and `List` come from the prelude. The shapes here
/// mirror the level-less constants the handler emits.
fn make_to_expr_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let string = Expr::const_str("String");

    // Lean.Name : Type
    let name_name = Name::from_string("Lean.Name");
    let name_const = || Expr::const_(name_name.clone(), vec![]);
    let anon_ty = name_const();
    let str_ty = Expr::pi(
        BinderInfo::Default,
        name_const(),
        Expr::pi(BinderInfo::Default, string.clone(), name_const()),
    );
    let num_ty = Expr::pi(
        BinderInfo::Default,
        name_const(),
        Expr::pi(BinderInfo::Default, nat.clone(), name_const()),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name_name.clone(),
            type_: type0.clone(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Lean.Name.anonymous"),
                    type_: anon_ty,
                },
                Constructor {
                    name: Name::from_string("Lean.Name.str"),
                    type_: str_ty,
                },
                Constructor {
                    name: Name::from_string("Lean.Name.num"),
                    type_: num_ty,
                },
            ],
        }],
    })
    .expect("should add Lean.Name");

    // Lean.Level : Type (carrier only; one nullary ctor keeps it nonempty).
    let level_name = Name::from_string("Lean.Level");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: level_name.clone(),
            type_: type0.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Lean.Level.zero"),
                type_: Expr::const_(level_name.clone(), vec![]),
            }],
        }],
    })
    .expect("should add Lean.Level");

    // Lean.Expr : Type with const : Lean.Name → List Lean.Level → Lean.Expr.
    let expr_name = Name::from_string("Lean.Expr");
    let list_level = Expr::app(
        Expr::const_str_levels("List", vec![Level::zero()]),
        Expr::const_(level_name.clone(), vec![]),
    );
    let expr_const_ty = Expr::pi(
        BinderInfo::Default,
        name_const(),
        Expr::pi(
            BinderInfo::Default,
            list_level,
            Expr::const_(expr_name.clone(), vec![]),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: expr_name.clone(),
            type_: type0.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Lean.Expr.const"),
                type_: expr_const_ty,
            }],
        }],
    })
    .expect("should add Lean.Expr");

    // Lean.ToExpr : Type → Type with
    // mk : {α : Type} → (α → Lean.Expr) → Lean.Expr → Lean.ToExpr α.
    let toexpr_name = Name::from_string("Lean.ToExpr");
    let toexpr_ty = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    let expr_c = Expr::const_(expr_name.clone(), vec![]);
    let toexpr_mk_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), expr_c.clone()),
            Expr::pi(
                BinderInfo::Default,
                expr_c.clone(),
                Expr::app(Expr::const_(toexpr_name.clone(), vec![]), Expr::bvar(2)),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: toexpr_name,
            type_: toexpr_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Lean.ToExpr.mk"),
                type_: toexpr_mk_ty,
            }],
        }],
    })
    .expect("should add Lean.ToExpr");

    // Color : Type with nullary ctors Color.Red, Color.Blue.
    let color_name = Name::from_string("Color");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: color_name.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("Color.Red"),
                    type_: Expr::const_(color_name.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("Color.Blue"),
                    type_: Expr::const_(color_name.clone(), vec![]),
                },
            ],
        }],
    })
    .expect("should add Color");

    env
}

#[test]
fn test_to_expr_nullary_enum_passes_strict_kernel_check() {
    let mut env = make_to_expr_env();
    let handler = DeriveToExpr;
    let tn = Name::from_string("Color");

    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("ToExpr should succeed for nullary enum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // Strict kernel type check: add_decl runs the full kernel checker on the
    // concrete reflected term. A sorry body would still pass (sorryAx is an
    // axiom), so the no-sorry guard test above is what proves genuineness; this
    // test proves kernel acceptance of the concrete recursor/reflection term.
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived ToExpr instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived ToExpr instance should be registered in the environment"
    );
}

// ---------------------------------------------------------------------------
// DeriveToExpr single-ctor struct soundness tests
// (sorry-free reflected `mkAppN (.const ``C []) #[toExpr f0, …]` via the
// left-nested `Lean.Expr.app` constructor; each field reflection resolves the
// field type's own `Lean.ToExpr` instance from the environment)
// ---------------------------------------------------------------------------

/// Build an environment with the reflection inductives the derived struct
/// `Lean.ToExpr` instance refers to (`Lean.Name`, `Lean.Level`, `Lean.Expr`
/// with both `const` and `app` constructors, `Lean.ToExpr`), a
/// `Lean.ToExpr.toExpr` projection accessor, a `Lean.ToExpr Nat` instance
/// (`instToExprNat`) registered both as a kernel def and a class instance, and a
/// single-ctor struct `Point.mk : Nat → Nat → Point`. The kernel auto-generates
/// `Point.rec` and `Lean.ToExpr.rec`, which the synthesized instance dispatches
/// through.
fn make_to_expr_struct_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let string = Expr::const_str("String");

    // Lean.Name : Type with anonymous / str / num (as in make_to_expr_env).
    let name_name = Name::from_string("Lean.Name");
    let name_const = || Expr::const_(name_name.clone(), vec![]);
    let str_ty = Expr::pi(
        BinderInfo::Default,
        name_const(),
        Expr::pi(BinderInfo::Default, string.clone(), name_const()),
    );
    let num_ty = Expr::pi(
        BinderInfo::Default,
        name_const(),
        Expr::pi(BinderInfo::Default, nat.clone(), name_const()),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name_name.clone(),
            type_: type0.clone(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Lean.Name.anonymous"),
                    type_: name_const(),
                },
                Constructor {
                    name: Name::from_string("Lean.Name.str"),
                    type_: str_ty,
                },
                Constructor {
                    name: Name::from_string("Lean.Name.num"),
                    type_: num_ty,
                },
            ],
        }],
    })
    .expect("should add Lean.Name");

    // Lean.Level : Type (carrier only).
    let level_name = Name::from_string("Lean.Level");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: level_name.clone(),
            type_: type0.clone(),
            constructors: vec![Constructor {
                name: Name::from_string("Lean.Level.zero"),
                type_: Expr::const_(level_name.clone(), vec![]),
            }],
        }],
    })
    .expect("should add Lean.Level");

    // Lean.Expr : Type with
    //   const : Lean.Name → List Lean.Level → Lean.Expr
    //   app   : Lean.Expr → Lean.Expr → Lean.Expr   (the reflected application
    //           node the struct instance nests `mkAppN` through).
    let expr_name = Name::from_string("Lean.Expr");
    let expr_c = || Expr::const_(expr_name.clone(), vec![]);
    let list_level = Expr::app(
        Expr::const_str_levels("List", vec![Level::zero()]),
        Expr::const_(level_name.clone(), vec![]),
    );
    let expr_const_ty = Expr::pi(
        BinderInfo::Default,
        name_const(),
        Expr::pi(BinderInfo::Default, list_level, expr_c()),
    );
    let expr_app_ty = Expr::pi(
        BinderInfo::Default,
        expr_c(),
        Expr::pi(BinderInfo::Default, expr_c(), expr_c()),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: expr_name.clone(),
            type_: type0.clone(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Lean.Expr.const"),
                    type_: expr_const_ty,
                },
                Constructor {
                    name: Name::from_string("Lean.Expr.app"),
                    type_: expr_app_ty,
                },
            ],
        }],
    })
    .expect("should add Lean.Expr");

    // Lean.ToExpr : Type → Type with
    // mk : {α : Type} → (α → Lean.Expr) → Lean.Expr → Lean.ToExpr α.
    let toexpr_name = Name::from_string("Lean.ToExpr");
    let toexpr_ty = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    let toexpr_mk_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), expr_c()),
            Expr::pi(
                BinderInfo::Default,
                expr_c(),
                Expr::app(Expr::const_(toexpr_name.clone(), vec![]), Expr::bvar(2)),
            ),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: toexpr_name.clone(),
            type_: toexpr_ty,
            constructors: vec![Constructor {
                name: Name::from_string("Lean.ToExpr.mk"),
                type_: toexpr_mk_ty,
            }],
        }],
    })
    .expect("should add Lean.ToExpr");

    // Lean.ToExpr.toExpr : {α : Type} → Lean.ToExpr α → α → Lean.Expr, projecting
    // the `toExpr` field via Lean.ToExpr.rec (mirrors the `Hashable.hash`
    // accessor in make_hashable_env at the concrete universe `α : Type 0`).
    let to_expr_accessor_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(toexpr_name.clone(), vec![]), Expr::bvar(0)),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), expr_c()),
        ),
    );
    // value: fun {α} (inst) => @Lean.ToExpr.rec.{1} α (fun _ => α → Lean.Expr)
    //          (fun (toE : α → Lean.Expr) (_toTy : Lean.Expr) => toE) inst
    // motive (constant): fun (_ : Lean.ToExpr α) => α → Lean.Expr, α = bvar 1.
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::app(Expr::const_(toexpr_name.clone(), vec![]), Expr::bvar(1)),
        Expr::pi(BinderInfo::Default, Expr::bvar(2), expr_c()),
    );
    // minor: fun (toE : α → Lean.Expr) (_toTy : Lean.Expr) => toE, α = bvar 1
    // outside the minor binders (the `mk` fields are `toExpr` then `toTypeExpr`).
    let minor = Expr::lam(
        BinderInfo::Default,
        Expr::pi(BinderInfo::Default, Expr::bvar(1), expr_c()),
        Expr::lam(BinderInfo::Default, expr_c(), Expr::bvar(1)),
    );
    let rec_body = Expr::apps(
        Expr::const_(
            Name::from_string("Lean.ToExpr.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::bvar(1), motive, minor, Expr::bvar(0)],
    );
    let to_expr_accessor_val = Expr::lam(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(Expr::const_(toexpr_name.clone(), vec![]), Expr::bvar(0)),
            rec_body,
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Lean.ToExpr.toExpr"),
        level_params: vec![],
        type_: to_expr_accessor_ty,
        value: to_expr_accessor_val,
        is_reducible: true,
    })
    .expect("should add Lean.ToExpr.toExpr accessor");

    // instToExprNat := @Lean.ToExpr.mk Nat (fun (_ : Nat) => Lean.Expr.const
    //   ``Nat.placeholder []) (Lean.Expr.const ``Nat []) — a total, axiom-free
    // stand-in. (ToExpr is data-only; the no-sorry guard, not the reflected
    // shape's semantics, is what proves genuineness.)
    let empty_levels = Expr::app(
        Expr::const_str_levels("List.nil", vec![Level::zero()]),
        Expr::const_(level_name.clone(), vec![]),
    );
    let nat_reflected = Expr::apps(
        Expr::const_str("Lean.Expr.const"),
        [
            Expr::apps(
                Expr::const_str("Lean.Name.str"),
                [Expr::const_str("Lean.Name.anonymous"), Expr::str_lit("Nat")],
            ),
            empty_levels,
        ],
    );
    let to_expr_nat = Expr::lam(BinderInfo::Default, nat.clone(), nat_reflected.clone());
    let inst_to_expr_nat_ty = Expr::app(Expr::const_str("Lean.ToExpr"), nat.clone());
    let inst_to_expr_nat_val = Expr::apps(
        Expr::const_str("Lean.ToExpr.mk"),
        [nat.clone(), to_expr_nat, nat_reflected],
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("instToExprNat"),
        level_params: vec![],
        type_: inst_to_expr_nat_ty,
        value: inst_to_expr_nat_val,
        is_reducible: true,
    })
    .expect("should add instToExprNat");
    env.register_instance(clean_kernel::KernelInstanceInfo {
        name: Name::from_string("instToExprNat"),
        class_name: Name::from_string("Lean.ToExpr"),
        priority: 100,
        type_: None,
        value: None,
    });

    // Point.mk : Nat → Nat → Point.
    let point_name = Name::from_string("Point");
    let point_mk_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::const_(point_name.clone(), vec![]),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: point_name.clone(),
            type_: type0,
            constructors: vec![Constructor {
                name: Name::from_string("Point.mk"),
                type_: point_mk_ty,
            }],
        }],
    })
    .expect("should add Point struct");
    env
}

#[test]
fn test_to_expr_struct_resolvable_fields_value_is_sorry_free() {
    // `Point.mk : Nat → Nat → Point` has fields whose `Lean.ToExpr` instance the
    // env resolves (`instToExprNat`), so the handler reflects the applied
    // constructor via Lean.Expr.app + each field's toExpr, with no placeholder
    // fallback.
    let env = make_to_expr_struct_env();
    let handler = DeriveToExpr;
    let tn = Name::from_string("Point");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("ToExpr should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "resolvable-field struct ToExpr value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // Fields are projected via the struct recursor, reflected via
    // Lean.ToExpr.toExpr, and nested into the applied constructor via
    // Lean.Expr.app, reusing the field type's resolved instance.
    assert!(
        expr_mentions_const(&decls[0].value, "Point.rec"),
        "struct ToExpr must project fields via the recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Lean.ToExpr.toExpr"),
        "struct ToExpr must reflect fields via Lean.ToExpr.toExpr: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Lean.Expr.app"),
        "struct ToExpr must build the applied ctor via Lean.Expr.app: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instToExprNat"),
        "struct ToExpr must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
}

#[test]
fn test_to_expr_struct_resolvable_fields_passes_strict_kernel_check() {
    let mut env = make_to_expr_struct_env();
    let handler = DeriveToExpr;
    let tn = Name::from_string("Point");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("ToExpr should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; this strict kernel type check proves the
    // concrete field-projection / reflection term is accepted by the full kernel
    // checker (correct universe levels, no sorryAx smuggling).
    assert!(
        !expr_contains_sorry(&value),
        "struct ToExpr value must be sorry-free before the kernel check: {value:?}"
    );
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived struct ToExpr instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived struct ToExpr instance should be registered in the environment"
    );
}

#[test]
fn test_to_expr_struct_unresolvable_field_fails_closed() {
    // A single-ctor struct whose field type has no resolvable `Lean.ToExpr`
    // instance cannot ground a real reflection. The bare prelude
    // `derive_env()` has no `Lean.ToExpr Nat` instance.
    let handler = DeriveToExpr;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert_unsupported(result, "ToExpr");
}

// ---------------------------------------------------------------------------
// DeriveOfScientific tests
// ---------------------------------------------------------------------------

#[test]
fn test_of_scientific_wrapper() {
    let handler = DeriveOfScientific;
    let tn = Name::from_string("Wrapper");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &wrapper_ctor(), 0, &[])
        .expect("OfScientific should succeed for wrapper");
    assert_eq!(decls.len(), 1);
    assert!(decls.iter().any(|d| d.is_instance));
}

#[test]
fn test_of_scientific_empty_rejected() {
    let handler = DeriveOfScientific;
    let tn = Name::from_string("Empty");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_of_scientific_enum_rejected() {
    // OfScientific requires single-constructor single-field wrapper
    let handler = DeriveOfScientific;
    let tn = Name::from_string("Color");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_of_scientific_multi_field_rejected() {
    let handler = DeriveOfScientific;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// DeriveOfScientific soundness tests (sorry-free for the Nat-wrapper shape)
// ---------------------------------------------------------------------------

/// Recursively test whether any sub-expression satisfies `pred`.
fn expr_any(expr: &Expr, pred: &impl Fn(&Expr) -> bool) -> bool {
    if pred(expr) {
        return true;
    }
    match expr.kind() {
        ExprKind::App(f, a) => expr_any(f, pred) || expr_any(a, pred),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_any(ty, pred) || expr_any(body, pred)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_any(ty, pred) || expr_any(val, pred) || expr_any(body, pred)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => expr_any(inner, pred),
        _ => false,
    }
}

/// True if `expr` mentions a `sorry`/`sorryAx` constant anywhere.
fn expr_contains_sorry(expr: &Expr) -> bool {
    expr_any(expr, &|sub| {
        matches!(sub.kind(), ExprKind::Const(name, _)
            if name.to_string() == "sorry" || name.to_string() == "sorryAx")
    })
}

/// True if `expr` references the constant named `target` anywhere.
fn expr_mentions_const(expr: &Expr, target: &str) -> bool {
    expr_any(
        expr,
        &|sub| matches!(sub.kind(), ExprKind::Const(name, _) if name.to_string() == target),
    )
}

/// A `Nat`-wrapping single-field ctor (`NatWrapper.mk : Nat → NatWrapper`).
fn nat_wrapper_ctor() -> Vec<CtorInfo2> {
    vec![CtorInfo2 {
        name: Name::from_string("NatWrapper.mk"),
        fields: vec![(Name::from_string("val"), Expr::const_str("Nat"))],
        is_recursive: false,
    }]
}

/// A wrapper whose single field is NOT `Nat` (`StrWrapper.mk : String → ...`).
fn string_wrapper_ctor() -> Vec<CtorInfo2> {
    vec![CtorInfo2 {
        name: Name::from_string("StrWrapper.mk"),
        fields: vec![(Name::from_string("val"), Expr::const_str("String"))],
        is_recursive: false,
    }]
}

#[test]
fn test_of_scientific_nat_wrapper_value_is_sorry_free() {
    let handler = DeriveOfScientific;
    let tn = Name::from_string("NatWrapper");
    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &nat_wrapper_ctor(),
            0,
            &[],
        )
        .expect("OfScientific should succeed for Nat wrapper");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "Nat-wrapper OfScientific instance value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The genuine instance projects through OfScientific.mk and the wrapper ctor.
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Const(name, _) if name.to_string() == "OfScientific.mk"
        )),
        "instance value should use OfScientific.mk"
    );
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Const(name, _) if name.to_string() == "NatWrapper.mk"
        )),
        "instance value should apply the wrapper constructor"
    );
}

#[test]
fn test_of_scientific_non_nat_wrapper_fails_closed() {
    // A non-Nat field has no canonical value constructible without an
    // OfScientific instance for the field type, so the handler rejects it.
    let handler = DeriveOfScientific;
    let tn = Name::from_string("StrWrapper");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &string_wrapper_ctor(),
        0,
        &[],
    );
    assert_unsupported(result, "OfScientific");
}

#[test]
fn test_of_scientific_parametric_wrapper_fails_closed() {
    // For a parametric wrapper (np > 0) we cannot soundly fix a value for the
    // field, so the handler rejects the shape.
    let handler = DeriveOfScientific;
    let tn = Name::from_string("Box");
    let ctors = vec![CtorInfo2 {
        name: Name::from_string("Box.mk"),
        fields: vec![(Name::from_string("val"), Expr::bvar(0))],
        is_recursive: false,
    }];
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 1, &[]);
    assert_unsupported(result, "OfScientific");
}

/// Build an environment with `Nat`, `Bool`, an `OfScientific` class, and a
/// `NatWrapper` single-field wrapper inductive, then return the wrapper ctor.
///
/// `OfScientific : Type → Type` (monomorphic, level-less, matching the
/// level-less `Expr::const_str("OfScientific")` the handler emits) with
/// `OfScientific.mk : {α : Type} → (Nat → Bool → Nat → α) → OfScientific α`.
fn make_of_scientific_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let bool_ = Expr::const_str("Bool");

    // OfScientific : Type → Type
    let ofsci_name = Name::from_string("OfScientific");
    let ofsci_type = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    // OfScientific.mk : {α : Type} → (Nat → Bool → Nat → α) → OfScientific α
    // With α = bvar(0) under the implicit binder, the function type binders push
    // α deeper: inside `Nat → Bool → Nat → α`, α is bvar(3).
    let fn_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            bool_,
            Expr::pi(BinderInfo::Default, nat.clone(), Expr::bvar(3)),
        ),
    );
    let ofsci_mk_type = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            fn_ty,
            Expr::app(Expr::const_(ofsci_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: ofsci_name.clone(),
            type_: ofsci_type,
            constructors: vec![Constructor {
                name: Name::from_string("OfScientific.mk"),
                type_: ofsci_mk_type,
            }],
        }],
    })
    .expect("should add OfScientific class");

    // NatWrapper : Type with NatWrapper.mk : Nat → NatWrapper
    let wrapper_name = Name::from_string("NatWrapper");
    let wrapper_mk_type = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::const_(wrapper_name.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: wrapper_name,
            type_: type0,
            constructors: vec![Constructor {
                name: Name::from_string("NatWrapper.mk"),
                type_: wrapper_mk_type,
            }],
        }],
    })
    .expect("should add NatWrapper inductive");

    env
}

#[test]
fn test_of_scientific_nat_wrapper_passes_strict_kernel_check() {
    let mut env = make_of_scientific_env();
    let handler = DeriveOfScientific;
    let tn = Name::from_string("NatWrapper");

    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &nat_wrapper_ctor(),
            0,
            &[],
        )
        .expect("OfScientific should succeed for Nat wrapper");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // Strict kernel type check: add_decl runs the full kernel checker. A sorry
    // body would still pass (sorryAx is an axiom), so the no-sorry guard test
    // above is what proves genuineness; this test proves kernel acceptance of
    // the concrete term.
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived OfScientific instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived OfScientific instance should be registered in the environment"
    );
}

// ---------------------------------------------------------------------------
// DeriveCountable soundness tests (sorry-free for the Nat-wrapper shape)
// ---------------------------------------------------------------------------

#[test]
fn test_countable_nat_wrapper_value_is_sorry_free() {
    let handler = DeriveCountable;
    let tn = Name::from_string("NatWrapper");
    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &nat_wrapper_ctor(),
            0,
            &[],
        )
        .expect("Countable should succeed for Nat wrapper");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "Nat-wrapper Countable instance value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The genuine instance projects the Nat field through Countable.mk and the
    // wrapper recursor.
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Const(name, _) if name.to_string() == "Countable.mk"
        )),
        "instance value should use Countable.mk"
    );
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Const(name, _) if name.to_string() == "NatWrapper.rec"
        )),
        "instance value should project the field via the wrapper recursor"
    );
}

#[test]
fn test_countable_non_nat_wrapper_fails_closed() {
    // A non-Nat field has no canonical encode-to-Nat constructible without a
    // Countable instance for the field type, so the handler rejects it.
    let handler = DeriveCountable;
    let tn = Name::from_string("StrWrapper");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &string_wrapper_ctor(),
        0,
        &[],
    );
    assert_unsupported(result, "Countable");
}

#[test]
fn test_countable_enum_fails_closed_without_fallback() {
    let handler = DeriveCountable;
    let tn = Name::from_string("Color");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[]);
    assert_unsupported(result, "Countable");
}

#[test]
fn test_countable_parametric_wrapper_fails_closed() {
    // For a parametric wrapper (np > 0) we cannot soundly fix an encode, so the
    // handler rejects the shape.
    let handler = DeriveCountable;
    let tn = Name::from_string("Box");
    let ctors = vec![CtorInfo2 {
        name: Name::from_string("Box.mk"),
        fields: vec![(Name::from_string("val"), Expr::const_str("Nat"))],
        is_recursive: false,
    }];
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 1, &[]);
    assert_unsupported(result, "Countable");
}

/// Build an environment with `Nat` (from the prelude), a `Countable` class, and
/// a `NatWrapper` single-field wrapper inductive (whose `.rec` the encode uses).
///
/// `Countable : Type → Type` (monomorphic, level-less, matching the level-less
/// `Expr::const_str("Countable")` the handler emits) with
/// `Countable.mk : {α : Type} → (α → Nat) → Countable α`. This models the
/// encode-to-`Nat` injection *data* that witnesses countability — the genuine,
/// kernel-checkable shape the handler produces.
fn make_countable_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");

    // Countable : Type → Type
    let cnt_name = Name::from_string("Countable");
    let cnt_type = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    // Countable.mk : {α : Type} → (α → Nat) → Countable α
    // With α = bvar(0) under the implicit binder, inside `α → Nat` α is bvar(1).
    let encode_ty = Expr::pi(BinderInfo::Default, Expr::bvar(0), nat.clone());
    let cnt_mk_type = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            encode_ty,
            Expr::app(Expr::const_(cnt_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: cnt_name.clone(),
            type_: cnt_type,
            constructors: vec![Constructor {
                name: Name::from_string("Countable.mk"),
                type_: cnt_mk_type,
            }],
        }],
    })
    .expect("should add Countable class");

    // NatWrapper : Type with NatWrapper.mk : Nat → NatWrapper
    let wrapper_name = Name::from_string("NatWrapper");
    let wrapper_mk_type = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::const_(wrapper_name.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: wrapper_name,
            type_: type0,
            constructors: vec![Constructor {
                name: Name::from_string("NatWrapper.mk"),
                type_: wrapper_mk_type,
            }],
        }],
    })
    .expect("should add NatWrapper inductive");

    env
}

#[test]
fn test_countable_nat_wrapper_passes_strict_kernel_check() {
    let mut env = make_countable_env();
    let handler = DeriveCountable;
    let tn = Name::from_string("NatWrapper");

    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &nat_wrapper_ctor(),
            0,
            &[],
        )
        .expect("Countable should succeed for Nat wrapper");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // Strict kernel type check: add_decl runs the full kernel checker on the
    // concrete encode term (Countable.mk + the wrapper recursor projection). A
    // sorry body would still pass (sorryAx is an axiom), so the no-sorry guard
    // test above is what proves genuineness; this test proves kernel acceptance
    // of the concrete projection term.
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived Countable instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived Countable instance should be registered in the environment"
    );
}

// ---------------------------------------------------------------------------
// Handler class_name tests
// ---------------------------------------------------------------------------

#[test]
fn test_handler_class_names() {
    assert_eq!(DeriveFintype.class_name(), "Fintype");
    assert_eq!(DeriveCountable.class_name(), "Countable");
    assert_eq!(DeriveToExpr.class_name(), "ToExpr");
    assert_eq!(DeriveOfScientific.class_name(), "OfScientific");
}

// ---------------------------------------------------------------------------
// ComposedDeriveHandler tests
// ---------------------------------------------------------------------------

#[test]
fn test_composed_handler_empty() {
    let composed = ComposedDeriveHandler::new("Combined", vec![]);
    let tn = Name::from_string("Color");
    let decls = composed
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("empty composed should succeed");
    assert!(decls.is_empty());
}

#[test]
fn test_composed_handler_single() {
    let composed = ComposedDeriveHandler::new("Combined", vec![Box::new(DeriveToExpr)]);
    let tn = Name::from_string("Color");
    let decls = composed
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("single handler composed");
    assert_eq!(decls.len(), 1);
}

#[test]
fn test_composed_handler_multiple() {
    let composed = ComposedDeriveHandler::new(
        "Combined",
        vec![Box::new(DeriveFintype), Box::new(DeriveToExpr)],
    );
    let tn = Name::from_string("Color");
    let decls = composed
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("multiple composed");
    assert_eq!(decls.len(), 2);
}

#[test]
fn test_composed_handler_stops_on_error() {
    let composed = ComposedDeriveHandler::new(
        "Combined",
        vec![Box::new(DeriveFintype), Box::new(DeriveToExpr)],
    );
    let tn = Name::from_string("Tree");
    let result = composed.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_composed_handler_class_name() {
    let composed = ComposedDeriveHandler::new("MyComposed", vec![]);
    assert_eq!(composed.class_name(), "MyComposed");
}

#[test]
fn test_composed_handler_debug() {
    let composed = ComposedDeriveHandler::new("Combined", vec![]);
    let debug = format!("{composed:?}");
    assert!(debug.contains("ComposedDeriveHandler"));
    assert!(debug.contains("Combined"));
}

// ---------------------------------------------------------------------------
// DerivePreconditionChecker tests
// ---------------------------------------------------------------------------

#[test]
fn test_precondition_diagnostics_recursive_fintype() {
    let tn = Name::from_string("Tree");
    let diags =
        DerivePreconditionChecker::diagnostics("Fintype", &tn, &type_expr(), &recursive_ctors());
    assert!(!diags.is_empty());
    assert!(diags
        .iter()
        .any(|d| d.severity == DeriveDiagnosticSeverity::Error));
}

#[test]
fn test_precondition_diagnostics_fintype_empty() {
    let tn = Name::from_string("Empty");
    let diags =
        DerivePreconditionChecker::diagnostics("Fintype", &tn, &type_expr(), &empty_ctors());
    assert!(diags
        .iter()
        .any(|d| d.severity == DeriveDiagnosticSeverity::Error));
}

#[test]
fn test_precondition_check_ok_enum() {
    let tn = Name::from_string("Color");
    let result = DerivePreconditionChecker::check("Fintype", &tn, &type_expr(), &color_ctors());
    assert!(result.is_ok());
}

#[test]
fn test_precondition_check_fails_recursive() {
    let tn = Name::from_string("Tree");
    let result = DerivePreconditionChecker::check("Fintype", &tn, &type_expr(), &recursive_ctors());
    assert!(result.is_err());
}

#[test]
fn test_precondition_diagnostics_countable_ok() {
    let tn = Name::from_string("Color");
    let diags =
        DerivePreconditionChecker::diagnostics("Countable", &tn, &type_expr(), &color_ctors());
    assert!(diags
        .iter()
        .all(|d| d.severity != DeriveDiagnosticSeverity::Error));
}

#[test]
fn test_precondition_diagnostics_of_scientific_needs_wrapper() {
    let tn = Name::from_string("Color");
    let diags =
        DerivePreconditionChecker::diagnostics("OfScientific", &tn, &type_expr(), &color_ctors());
    assert!(diags
        .iter()
        .any(|d| d.severity == DeriveDiagnosticSeverity::Error));
}

#[test]
fn test_precondition_diagnostics_of_scientific_wrapper_ok() {
    let tn = Name::from_string("Wrapper");
    let diags =
        DerivePreconditionChecker::diagnostics("OfScientific", &tn, &type_expr(), &wrapper_ctor());
    assert!(diags
        .iter()
        .all(|d| d.severity != DeriveDiagnosticSeverity::Error));
}

// ---------------------------------------------------------------------------
// DeriveDiagnostic tests
// ---------------------------------------------------------------------------

#[test]
fn test_diagnostic_new() {
    let d = DeriveDiagnostic::new(
        DeriveDiagnosticSeverity::Error,
        "BEq",
        "bad type",
        vec!["try manual impl".to_owned()],
    );
    assert_eq!(d.severity, DeriveDiagnosticSeverity::Error);
    assert_eq!(d.class_name, "BEq");
    assert_eq!(d.message, "bad type");
    assert_eq!(d.suggestions.len(), 1);
}

#[test]
fn test_diagnostic_warning_creation() {
    let d = DeriveDiagnostic::new(
        DeriveDiagnosticSeverity::Warning,
        "Ord",
        "large type",
        vec![],
    );
    assert_eq!(d.severity, DeriveDiagnosticSeverity::Warning);
    assert!(d.suggestions.is_empty());
}

#[test]
fn test_diagnostic_default() {
    let d = DeriveDiagnostic::default();
    assert_eq!(d.severity, DeriveDiagnosticSeverity::Error);
    assert!(d.class_name.is_empty());
    assert!(d.message.is_empty());
    assert!(d.suggestions.is_empty());
}

#[test]
fn test_diagnostic_equality() {
    let d1 = DeriveDiagnostic::new(DeriveDiagnosticSeverity::Error, "X", "msg", vec![]);
    let d2 = DeriveDiagnostic::new(DeriveDiagnosticSeverity::Error, "X", "msg", vec![]);
    assert_eq!(d1, d2);
}

#[test]
fn test_diagnostic_inequality_on_severity() {
    let d1 = DeriveDiagnostic::new(DeriveDiagnosticSeverity::Error, "X", "msg", vec![]);
    let d2 = DeriveDiagnostic::new(DeriveDiagnosticSeverity::Warning, "X", "msg", vec![]);
    assert_ne!(d1, d2);
}

#[test]
fn test_diagnostic_severity_ordering() {
    assert!(DeriveDiagnosticSeverity::Error < DeriveDiagnosticSeverity::Warning);
    assert!(DeriveDiagnosticSeverity::Warning < DeriveDiagnosticSeverity::Info);
    assert!(DeriveDiagnosticSeverity::Info < DeriveDiagnosticSeverity::Hint);
}

// ---------------------------------------------------------------------------
// ExtendedDeriveRegistry tests
// ---------------------------------------------------------------------------

#[test]
fn test_extended_registry_default_has_4_handlers() {
    let reg = ExtendedDeriveRegistry::default_registry();
    assert_eq!(reg.registered_classes().len(), 4);
    assert!(reg.has_handler("Fintype"));
    assert!(reg.has_handler("Countable"));
    assert!(reg.has_handler("ToExpr"));
    assert!(reg.has_handler("OfScientific"));
}

#[test]
fn test_extended_registry_no_handler() {
    let reg = ExtendedDeriveRegistry::new();
    assert!(!reg.has_handler("Fintype"));
}

#[test]
fn test_extended_registry_custom_handler() {
    let mut reg = ExtendedDeriveRegistry::new();
    reg.register(50, &[], Box::new(DeriveFintype));
    assert!(reg.has_handler("Fintype"));
    assert!(!reg.has_handler("Countable"));
}

#[test]
fn test_extended_registry_derive_all_color() {
    let reg = ExtendedDeriveRegistry::default_registry();
    let tn = Name::from_string("Color");
    let classes = vec![Name::from_string("Fintype"), Name::from_string("ToExpr")];
    let decls = reg
        .derive_all(
            &derive_env(),
            &tn,
            &type_expr(),
            &color_ctors(),
            &classes,
            0,
            &[],
        )
        .expect("derive_all should succeed");
    assert_eq!(decls.len(), 2);
}

#[test]
fn test_extended_registry_derive_all_unknown_class_error() {
    let reg = ExtendedDeriveRegistry::default_registry();
    let tn = Name::from_string("Color");
    let classes = vec![Name::from_string("Functor")];
    let result = reg.derive_all(
        &derive_env(),
        &tn,
        &type_expr(),
        &color_ctors(),
        &classes,
        0,
        &[],
    );
    assert!(result.is_err());
}

#[test]
fn test_extended_registry_derive_all_stops_on_error() {
    let reg = ExtendedDeriveRegistry::default_registry();
    let tn = Name::from_string("Tree");
    let classes = vec![Name::from_string("Fintype")];
    let result = reg.derive_all(
        &derive_env(),
        &tn,
        &type_expr(),
        &recursive_ctors(),
        &classes,
        0,
        &[],
    );
    assert!(result.is_err());
}

#[test]
fn test_extended_registry_derive_all_empty_classes() {
    let reg = ExtendedDeriveRegistry::default_registry();
    let tn = Name::from_string("Color");
    let decls = reg
        .derive_all(
            &derive_env(),
            &tn,
            &type_expr(),
            &color_ctors(),
            &[],
            0,
            &[],
        )
        .expect("empty classes");
    assert!(decls.is_empty());
}

#[test]
fn test_extended_registry_dependencies_for() {
    let reg = ExtendedDeriveRegistry::default_registry();
    let deps = reg.dependencies_for("Countable");
    assert!(deps.iter().any(|d| d.to_string() == "Fintype"));
}

#[test]
fn test_extended_registry_dependencies_for_unknown() {
    let reg = ExtendedDeriveRegistry::new();
    let deps = reg.dependencies_for("Nonexistent");
    assert!(deps.is_empty());
}

#[test]
fn test_extended_registry_default_trait() {
    let reg = ExtendedDeriveRegistry::default();
    assert_eq!(reg.registered_classes().len(), 4);
}

#[test]
fn test_extended_registry_debug() {
    let reg = ExtendedDeriveRegistry::default_registry();
    let debug = format!("{reg:?}");
    assert!(debug.contains("ExtendedDeriveRegistry"));
}

// ---------------------------------------------------------------------------
// ExtDeriveHandler2Adapter end-to-end tests (canonical dispatch via run_derive)
//
// These exercise the actual registered path: the adapter builds CtorInfo2 from
// the environment's InductiveVal, invokes the batch-2 handler, rejects any
// sorry-bearing instance with a hard DeriveError, and otherwise forwards a
// kernel-checked Declaration through `run_derive`/`add_decl`.
// ---------------------------------------------------------------------------

use crate::derive::DeriveRegistry;
use crate::derive_ext::register_all_handlers;

/// The canonical dispatch wires the two sound data classes (and only those two
/// of the four batch-2 candidates).
#[test]
fn test_register_all_handlers_wires_to_expr_and_of_scientific() {
    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);
    assert!(registry.has_handler("ToExpr"));
    assert!(registry.has_handler("OfScientific"));
    // `Fintype` IS wired via the batch-2 adapter (sorry-free: it emits a real
    // `Fintype.mk` for the nullary-enum shape and ERRORS up front on any other
    // shape, so it never registers a sorry-backed instance). `Countable` stays
    // unwired (its batch-2 handler has no genuine proof path).
    assert!(registry.has_handler("Fintype"));
    assert!(!registry.has_handler("Countable"));
}

/// OfScientific on a `Nat`-field wrapper derives a genuine, sorry-free instance
/// through the adapter and the full `run_derive` kernel check.
#[test]
fn test_run_derive_of_scientific_nat_wrapper_kernel_checked_sorry_free() {
    let mut env = make_of_scientific_env();
    let ind = env
        .get_inductive(&Name::from_string("NatWrapper"))
        .expect("NatWrapper should be in env")
        .clone();

    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    registry
        .run_derive("OfScientific", &ind, &mut env)
        .expect("deriving OfScientific on a Nat wrapper should succeed");

    let inst_name = Name::from_string("instOfScientificNatWrapper");
    let registered = env
        .get_const(&inst_name)
        .expect("derived OfScientific instance should be registered");
    assert!(
        !registered.value.as_ref().is_some_and(Expr::has_sorry),
        "registered OfScientific instance value must be sorry-free"
    );
    assert!(
        !registered.type_.has_sorry(),
        "registered OfScientific instance type must be sorry-free"
    );
}

/// OfScientific on a NON-`Nat` wrapper has no genuine construction path, so the
/// adapter ERRORS (faithful to Lean) rather than registering a sorry instance.
#[test]
fn test_run_derive_of_scientific_non_nat_wrapper_errors_no_sorry() {
    // `make_of_scientific_env` provides the OfScientific class; add a String
    // wrapper whose field has no canonical OfScientific value.
    let mut env = make_of_scientific_env();
    let wrapper_name = Name::from_string("StrWrapper");
    let wrapper_mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("String"),
        Expr::const_(wrapper_name.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: wrapper_name.clone(),
            type_: Expr::sort(Level::succ(Level::zero())),
            constructors: vec![Constructor {
                name: Name::from_string("StrWrapper.mk"),
                type_: wrapper_mk_ty,
            }],
        }],
    })
    .expect("should add StrWrapper");
    let ind = env
        .get_inductive(&wrapper_name)
        .expect("StrWrapper should be in env")
        .clone();

    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    let result = registry.run_derive("OfScientific", &ind, &mut env);
    match result {
        Err(DeriveError::Unsupported { class_name, .. }) => {
            assert_eq!(class_name, "OfScientific");
        }
        other => panic!("expected Unsupported error, got {other:?}"),
    }
    // No sorry-backed instance leaked into the environment.
    assert!(
        env.get_const(&Name::from_string("instOfScientificStrWrapper"))
            .is_none(),
        "no sorry-backed OfScientific instance must be registered on failure"
    );
}

/// ToExpr on a nullary enum derives a genuine, sorry-free reflection instance
/// through the adapter and the full `run_derive` kernel check.
#[test]
fn test_run_derive_to_expr_nullary_enum_kernel_checked_sorry_free() {
    let mut env = make_to_expr_env();
    let ind = env
        .get_inductive(&Name::from_string("Color"))
        .expect("Color should be in env")
        .clone();

    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    registry
        .run_derive("ToExpr", &ind, &mut env)
        .expect("deriving ToExpr on a nullary enum should succeed");

    let inst_name = Name::from_string("instToExprColor");
    let registered = env
        .get_const(&inst_name)
        .expect("derived ToExpr instance should be registered");
    assert!(
        !registered.value.as_ref().is_some_and(Expr::has_sorry),
        "registered ToExpr instance value must be sorry-free"
    );
}

/// ToExpr on a single-ctor struct whose field instances resolve derives a
/// genuine, sorry-free reflection instance through the adapter + run_derive.
#[test]
fn test_run_derive_to_expr_resolvable_struct_kernel_checked_sorry_free() {
    let mut env = make_to_expr_struct_env();
    let ind = env
        .get_inductive(&Name::from_string("Point"))
        .expect("Point should be in env")
        .clone();

    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    registry
        .run_derive("ToExpr", &ind, &mut env)
        .expect("deriving ToExpr on a resolvable struct should succeed");

    let inst_name = Name::from_string("instToExprPoint");
    let registered = env
        .get_const(&inst_name)
        .expect("derived ToExpr instance should be registered");
    assert!(
        !registered.value.as_ref().is_some_and(Expr::has_sorry),
        "registered struct ToExpr instance value must be sorry-free"
    );
}

/// ToExpr on a single-ctor struct whose field type has NO resolvable
/// `Lean.ToExpr` instance cannot be genuinely reflected, so the adapter ERRORS
/// rather than registering a placeholder implementation.
#[test]
fn test_run_derive_to_expr_unresolvable_struct_errors_no_sorry() {
    // `make_to_expr_env` has the reflection inductives + Lean.ToExpr but NO
    // `Lean.ToExpr Nat` instance, so a Nat-field struct returns a typed error.
    let mut env = make_to_expr_env();
    let point_name = Name::from_string("Point");
    let nat = Expr::const_str("Nat");
    let point_mk_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::const_(point_name.clone(), vec![]),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: point_name.clone(),
            type_: Expr::sort(Level::succ(Level::zero())),
            constructors: vec![Constructor {
                name: Name::from_string("Point.mk"),
                type_: point_mk_ty,
            }],
        }],
    })
    .expect("should add Point");
    let ind = env
        .get_inductive(&point_name)
        .expect("Point should be in env")
        .clone();

    let mut registry = DeriveRegistry::new();
    register_all_handlers(&mut registry);

    let result = registry.run_derive("ToExpr", &ind, &mut env);
    match result {
        Err(DeriveError::Unsupported { class_name, .. }) => {
            assert_eq!(class_name, "ToExpr");
        }
        other => panic!("expected Unsupported error, got {other:?}"),
    }
    assert!(
        env.get_const(&Name::from_string("instToExprPoint"))
            .is_none(),
        "no sorry-backed ToExpr instance must be registered on failure"
    );
}

#[test]
fn test_extended_registry_register_with_deps() {
    let mut reg = ExtendedDeriveRegistry::new();
    reg.register(100, &[Name::from_string("BEq")], Box::new(DeriveCountable));
    let deps = reg.dependencies_for("Countable");
    assert_eq!(deps.len(), 1);
    assert_eq!(deps[0].to_string(), "BEq");
}
