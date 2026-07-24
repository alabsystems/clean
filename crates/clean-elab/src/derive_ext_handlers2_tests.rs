// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for batch-2 extended derive handler registry, handlers, and statistics.

use clean_kernel::{
    BinderInfo, Constructor, Declaration, Environment, Expr, ExprKind, InductiveDecl,
    InductiveType, Level, Literal, Name, TypeChecker,
};

use crate::derive::DeriveError;
use crate::derive_ext_handlers2::{
    CtorInfo2, DeriveBEq2, DeriveDecidableEq2, DeriveHandlerRegistry2, DeriveHashable2,
    DeriveInhabited2, DeriveNonempty2, DeriveOrd2, DeriveRepr2, DeriveSizeOf2, DerivedDecl2,
    ExtDeriveHandler2, HandlerStatsSnapshot,
};

// ---------------------------------------------------------------------------
// Test helpers
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

/// A single-ctor struct `Point.mk : Opaque → Opaque → Point` whose field type
/// `Opaque` has no structural class instance in the environment. Field-instance
/// resolution therefore fails, exercising the handlers' fail-closed path.
///
/// Since Task NN bootstraps `Repr Nat`/`Hashable Nat` into the prelude, a
/// `Nat`-fielded struct now resolves and renders via the recursor; these
/// negative tests instead use `Opaque` to keep the original test intent
/// (verify typed rejection) valid. Pair with [`derive_env_with_opaque`].
fn point_ctors_opaque() -> Vec<CtorInfo2> {
    let opaque = Expr::const_str("Opaque");
    vec![CtorInfo2 {
        name: Name::from_string("Point.mk"),
        fields: vec![
            (Name::from_string("x"), opaque.clone()),
            (Name::from_string("y"), opaque),
        ],
        is_recursive: false,
    }]
}

/// Prelude env extended with a nullary inductive `Opaque : Type` that has NO
/// typeclass instances, so `resolve_field_instance(_, _, Opaque)` returns
/// `None`. Used by the fallback shape tests (see [`point_ctors_opaque`]).
fn derive_env_with_opaque() -> Environment {
    let mut env = Environment::with_prelude();
    let opaque = Name::from_string("Opaque");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: opaque.clone(),
            type_: Expr::sort(Level::succ(Level::zero())),
            constructors: vec![Constructor {
                name: Name::from_string("Opaque.mk"),
                type_: Expr::const_(opaque, vec![]),
            }],
        }],
    })
    .expect("should add Opaque");
    env
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

fn type_expr() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

/// Bare prelude environment for shape-only tests that do not exercise field
/// instance resolution. Handlers that ignore `env` (everything except the
/// single-ctor struct branches of `DeriveBEq2`/`DeriveRepr2`) accept this.
fn derive_env() -> Environment {
    Environment::with_prelude()
}

fn assert_unsupported(result: Result<Vec<DerivedDecl2>, DeriveError>, class_name: &str) {
    match result {
        Err(DeriveError::Unsupported {
            class_name: got, ..
        }) => assert_eq!(got, class_name),
        other => panic!("expected Unsupported for {class_name}, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Registry tests
// ---------------------------------------------------------------------------

#[test]
fn test_default_registry_has_all_8_handlers() {
    let reg = DeriveHandlerRegistry2::default_registry();
    assert!(reg.has_handler("BEq"));
    assert!(reg.has_handler("Hashable"));
    assert!(reg.has_handler("Repr"));
    assert!(reg.has_handler("Ord"));
    assert!(reg.has_handler("DecidableEq"));
    assert!(reg.has_handler("Inhabited"));
    assert!(reg.has_handler("Nonempty"));
    assert!(reg.has_handler("SizeOf"));
}

#[test]
fn test_default_registry_handler_count() {
    let reg = DeriveHandlerRegistry2::default_registry();
    assert_eq!(reg.registered_classes().len(), 8);
}

#[test]
fn test_empty_registry_has_no_handlers() {
    let reg = DeriveHandlerRegistry2::new();
    assert!(!reg.has_handler("BEq"));
    assert!(!reg.has_handler("Functor"));
}

#[test]
fn test_registry_register_custom() {
    let mut reg = DeriveHandlerRegistry2::new();
    reg.register("BEq", Box::new(DeriveBEq2));
    assert!(reg.has_handler("BEq"));
    assert!(!reg.has_handler("Hashable"));
}

#[test]
fn test_registry_derive_all_unknown_class_error() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Color");
    let te = type_expr();
    let result = reg.derive_all(
        &derive_env(),
        &tn,
        &te,
        &color_ctors(),
        &[Name::from_string("Functor")],
        0,
        &[],
    );
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::NoHandler(name) => assert_eq!(name, "Functor"),
        other => panic!("expected NoHandler, got {other:?}"),
    }
}

#[test]
fn test_registry_derive_all_multiple_classes() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Color");
    let te = type_expr();
    let classes = vec![
        Name::from_string("BEq"),
        Name::from_string("Repr"),
        Name::from_string("DecidableEq"),
    ];
    let decls = reg
        .derive_all(&derive_env(), &tn, &te, &color_ctors(), &classes, 0, &[])
        .expect("derive_all should succeed");
    assert_eq!(decls.len(), 3);
    let names: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();
    assert!(names.contains(&"instBEqColor".to_string()));
    assert!(names.contains(&"instReprColor".to_string()));
    assert!(names.contains(&"instDecidableEqColor".to_string()));
}

#[test]
fn test_registry_derive_all_empty_classes() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Color");
    let te = type_expr();
    let decls = reg
        .derive_all(&derive_env(), &tn, &te, &color_ctors(), &[], 0, &[])
        .expect("empty classes should succeed");
    assert!(decls.is_empty());
}

#[test]
fn test_registry_debug_format() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let debug_str = format!("{reg:?}");
    assert!(debug_str.contains("DeriveHandlerRegistry2"));
}

// ---------------------------------------------------------------------------
// Statistics tests
// ---------------------------------------------------------------------------

#[test]
fn test_stats_initially_zero() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let snap = reg.stats_for("BEq").expect("BEq stats should exist");
    assert_eq!(
        snap,
        HandlerStatsSnapshot {
            invocations: 0,
            successes: 0,
            failures: 0,
        }
    );
}

#[test]
fn test_stats_success_increments() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Color");
    let te = type_expr();
    reg.derive_all(
        &derive_env(),
        &tn,
        &te,
        &color_ctors(),
        &[Name::from_string("BEq")],
        0,
        &[],
    )
    .unwrap();
    let snap = reg.stats_for("BEq").unwrap();
    assert_eq!(snap.invocations, 1);
    assert_eq!(snap.successes, 1);
    assert_eq!(snap.failures, 0);
}

#[test]
fn test_stats_failure_increments() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Empty");
    let te = type_expr();
    let _ = reg.derive_all(
        &derive_env(),
        &tn,
        &te,
        &empty_ctors(),
        &[Name::from_string("Inhabited")],
        0,
        &[],
    );
    let snap = reg.stats_for("Inhabited").unwrap();
    assert_eq!(snap.invocations, 1);
    assert_eq!(snap.successes, 0);
    assert_eq!(snap.failures, 1);
}

#[test]
fn test_stats_multiple_invocations() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Color");
    let te = type_expr();
    for _ in 0..3 {
        reg.derive_all(
            &derive_env(),
            &tn,
            &te,
            &color_ctors(),
            &[Name::from_string("Repr")],
            0,
            &[],
        )
        .unwrap();
    }
    let snap = reg.stats_for("Repr").unwrap();
    assert_eq!(snap.invocations, 3);
    assert_eq!(snap.successes, 3);
}

#[test]
fn test_all_stats_returns_all_handlers() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let all = reg.all_stats();
    assert_eq!(all.len(), 8);
    assert!(all.contains_key("BEq"));
    assert!(all.contains_key("SizeOf"));
}

#[test]
fn test_stats_for_unknown_returns_none() {
    let reg = DeriveHandlerRegistry2::default_registry();
    assert!(reg.stats_for("Functor").is_none());
}

// ---------------------------------------------------------------------------
// DeriveBEq2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_beq2_enum_produces_instance() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("Color");
    let te = type_expr();
    let decls = handler
        .derive(&derive_env(), &tn, &te, &color_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instBEqColor");
    assert!(decls[0].is_instance);
}

#[test]
fn test_beq2_single_nullary_ctor() {
    let handler = DeriveBEq2;
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
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instBEqUnit");
}

#[test]
fn test_beq2_empty_type() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("Empty");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls.len(), 1);
}

#[test]
fn test_beq2_recursive_rejected() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported { class_name, .. } => assert_eq!(class_name, "BEq"),
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_beq2_struct_with_fields() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("Point");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instBEqPoint");
}

// ---------------------------------------------------------------------------
// DeriveHashable2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_hashable2_enum() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instHashableColor");
    assert!(decls[0].is_instance);
}

#[test]
fn test_hashable2_recursive_rejected() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// DeriveRepr2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_repr2_enum() {
    let handler = DeriveRepr2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instReprColor");
    assert!(decls[0].is_instance);
}

#[test]
fn test_repr2_recursive_fails_closed() {
    let handler = DeriveRepr2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert_unsupported(result, "Repr");
}

// ---------------------------------------------------------------------------
// DeriveOrd2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_ord2_nonempty_enum_fails_closed() {
    let handler = DeriveOrd2;
    let tn = Name::from_string("Color");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[]);
    assert_unsupported(result, "Ord");
}

#[test]
fn test_ord2_empty_type() {
    let handler = DeriveOrd2;
    let tn = Name::from_string("Empty");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls.len(), 1);
}

#[test]
fn test_ord2_recursive_rejected() {
    let handler = DeriveOrd2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported { class_name, .. } => assert_eq!(class_name, "Ord"),
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// DeriveDecidableEq2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_deceq2_enum() {
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instDecidableEqColor");
    assert!(decls[0].is_instance);
}

#[test]
fn test_deceq2_recursive_rejected() {
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_deceq2_struct() {
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Point");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instDecidableEqPoint");
}

// ---------------------------------------------------------------------------
// DeriveInhabited2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_inhabited2_enum() {
    let handler = DeriveInhabited2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instInhabitedColor");
    assert!(decls[0].is_instance);
}

#[test]
fn test_inhabited2_no_ctors_error() {
    let handler = DeriveInhabited2;
    let tn = Name::from_string("Empty");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported {
            class_name, reason, ..
        } => {
            assert_eq!(class_name, "Inhabited");
            assert!(reason.contains("no constructors"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_inhabited2_struct_with_fields_fails_closed() {
    let handler = DeriveInhabited2;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert_unsupported(result, "Inhabited");
}

#[test]
fn test_inhabited2_recursive_field_ctor_fails_closed() {
    let handler = DeriveInhabited2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert_unsupported(result, "Inhabited");
}

// ---------------------------------------------------------------------------
// DeriveNonempty2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_nonempty2_enum() {
    let handler = DeriveNonempty2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .unwrap();
    assert_eq!(decls[0].name.to_string(), "instNonemptyColor");
    assert!(decls[0].is_instance);
}

#[test]
fn test_nonempty2_no_ctors_error() {
    let handler = DeriveNonempty2;
    let tn = Name::from_string("Empty");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported {
            class_name, reason, ..
        } => {
            assert_eq!(class_name, "Nonempty");
            assert!(reason.contains("no constructors"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_nonempty2_struct_with_fields_fails_closed() {
    let handler = DeriveNonempty2;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert_unsupported(result, "Nonempty");
}

#[test]
fn test_nonempty2_recursive_field_ctor_fails_closed() {
    let handler = DeriveNonempty2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert_unsupported(result, "Nonempty");
}

// ---------------------------------------------------------------------------
// DeriveSizeOf2 tests
// ---------------------------------------------------------------------------

#[test]
fn test_sizeof2_enum_fails_closed() {
    let handler = DeriveSizeOf2;
    let tn = Name::from_string("Color");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[]);
    assert_unsupported(result, "SizeOf");
}

#[test]
fn test_sizeof2_empty_type_fails_closed() {
    let handler = DeriveSizeOf2;
    let tn = Name::from_string("Empty");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert_unsupported(result, "SizeOf");
}

#[test]
fn test_sizeof2_struct_fails_closed() {
    let handler = DeriveSizeOf2;
    let tn = Name::from_string("Point");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[]);
    assert_unsupported(result, "SizeOf");
}

#[test]
fn test_sizeof2_recursive_fails_closed() {
    let handler = DeriveSizeOf2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert_unsupported(result, "SizeOf");
}

// ---------------------------------------------------------------------------
// Handler class_name tests
// ---------------------------------------------------------------------------

#[test]
fn test_handler_class_names() {
    assert_eq!(DeriveBEq2.class_name(), "BEq");
    assert_eq!(DeriveHashable2.class_name(), "Hashable");
    assert_eq!(DeriveRepr2.class_name(), "Repr");
    assert_eq!(DeriveOrd2.class_name(), "Ord");
    assert_eq!(DeriveDecidableEq2.class_name(), "DecidableEq");
    assert_eq!(DeriveInhabited2.class_name(), "Inhabited");
    assert_eq!(DeriveNonempty2.class_name(), "Nonempty");
    assert_eq!(DeriveSizeOf2.class_name(), "SizeOf");
}

// ---------------------------------------------------------------------------
// Batch derive integration tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_all_complete_classes_for_enum() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Color");
    let te = type_expr();
    let classes = vec![
        Name::from_string("BEq"),
        Name::from_string("Hashable"),
        Name::from_string("Repr"),
        Name::from_string("DecidableEq"),
        Name::from_string("Inhabited"),
        Name::from_string("Nonempty"),
    ];
    let decls = reg
        .derive_all(&derive_env(), &tn, &te, &color_ctors(), &classes, 0, &[])
        .expect("all complete enum derives should succeed");
    assert_eq!(decls.len(), 6);
    assert!(decls.iter().all(|d| d.is_instance));
}

#[test]
fn test_derive_all_stops_on_first_error() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Empty");
    let te = type_expr();
    let classes = vec![Name::from_string("BEq"), Name::from_string("Inhabited")];
    let result = reg.derive_all(&derive_env(), &tn, &te, &empty_ctors(), &classes, 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_derived_decl_name_convention() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("MyType");
    let te = type_expr();
    let classes = vec![
        Name::from_string("BEq"),
        Name::from_string("Hashable"),
        Name::from_string("Repr"),
        Name::from_string("DecidableEq"),
        Name::from_string("Inhabited"),
        Name::from_string("Nonempty"),
    ];
    let decls = reg
        .derive_all(
            &derive_env(),
            &tn,
            &te,
            &single_nullary_ctor(),
            &classes,
            0,
            &[],
        )
        .unwrap();
    let names: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();
    assert!(names.contains(&"instBEqMyType".to_string()));
    assert!(names.contains(&"instHashableMyType".to_string()));
    assert!(names.contains(&"instReprMyType".to_string()));
    assert!(names.contains(&"instDecidableEqMyType".to_string()));
    assert!(names.contains(&"instInhabitedMyType".to_string()));
    assert!(names.contains(&"instNonemptyMyType".to_string()));
}

#[test]
fn test_derive_all_struct_subset() {
    let reg = DeriveHandlerRegistry2::default_registry();
    let tn = Name::from_string("Point");
    let te = type_expr();
    let classes = vec![
        Name::from_string("BEq"),
        Name::from_string("Hashable"),
        Name::from_string("Repr"),
        Name::from_string("DecidableEq"),
    ];
    let decls = reg
        .derive_all(&derive_env(), &tn, &te, &point_ctors(), &classes, 0, &[])
        .expect("should derive subset for Point");
    assert_eq!(decls.len(), 4);
}

// ---------------------------------------------------------------------------
// DeriveRepr2 soundness tests (sorry-free recursor render for nullary enums)
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

#[test]
fn test_repr2_nullary_enum_value_is_sorry_free() {
    let handler = DeriveRepr2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("Repr should succeed for nullary enum");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "nullary-enum Repr instance value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The genuine instance dispatches via the enum recursor and renders each
    // constructor name as a String literal under `Repr.mk`.
    assert!(
        expr_mentions_const(&decls[0].value, "Color.rec"),
        "instance value should dispatch through the enum recursor Color.rec: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Repr.mk"),
        "instance value should use Repr.mk: {:?}",
        decls[0].value
    );
    // Each constructor name must appear as a String literal in the body.
    for ctor in color_ctors() {
        let rendered = ctor.name.to_string();
        assert!(
            expr_any(&decls[0].value, &|sub| matches!(
                sub.kind(),
                ExprKind::Lit(Literal::String(s)) if s.as_ref() == rendered
            )),
            "constructor name {rendered:?} must be rendered as a String literal"
        );
    }
}

#[test]
fn test_repr2_single_nullary_ctor_is_sorry_free() {
    let handler = DeriveRepr2;
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
        .expect("Repr should succeed for single nullary ctor");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "single nullary ctor Repr value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Unit.rec"),
        "single-ctor instance should dispatch through Unit.rec"
    );
}

#[test]
fn test_repr2_struct_with_unresolvable_fields_fails_closed() {
    // An instance-less field type cannot be rendered structurally. The handler
    // must return a typed rejection instead of manufacturing a constant result.
    let handler = DeriveRepr2;
    let tn = Name::from_string("Point");
    let result = handler.derive(
        &derive_env_with_opaque(),
        &tn,
        &type_expr(),
        &point_ctors_opaque(),
        0,
        &[],
    );
    assert_unsupported(result, "Repr");
}

#[test]
fn test_repr2_recursive_fails_closed_without_fallback() {
    let handler = DeriveRepr2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert_unsupported(result, "Repr");
}

#[test]
fn test_repr2_parametric_enum_fails_closed_without_fallback() {
    let handler = DeriveRepr2;
    let tn = Name::from_string("PColor");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 1, &[]);
    assert_unsupported(result, "Repr");
}

/// Build an environment with a `Repr` class plus a `Color` nullary enum, then
/// return it. `Nat` and `String` come from the prelude (the motive eliminates
/// into `String : Type`). The `Repr` class shape mirrors the in-tree
/// `reprPrec : α → Nat → String` convention used by the sibling `DeriveRepr`.
fn make_repr_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let string = Expr::const_str("String");

    // Repr : Type → Type with
    // mk : {α : Type} → (α → Nat → String) → Repr α.
    let repr_name = Name::from_string("Repr");
    let repr_ty = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    // reprPrec field type: α → Nat → String, where α = bvar(0) under the
    // implicit binder (pushed deeper by the Nat/String binders).
    let repr_prec_ty = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(BinderInfo::Default, nat, string),
    );
    let repr_mk_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            repr_prec_ty,
            Expr::app(Expr::const_(repr_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    // `with_prelude` now bootstraps a real `Repr` class with the same
    // `reprPrec : α → Nat → String` shape (Task NN). Only declare the test's
    // stand-in `Repr` when the prelude did not already provide one, so this
    // helper stays idempotent against the richer prelude.
    if env.get_inductive(&repr_name).is_none() {
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: repr_name,
                type_: repr_ty,
                constructors: vec![Constructor {
                    name: Name::from_string("Repr.mk"),
                    type_: repr_mk_ty,
                }],
            }],
        })
        .expect("should add Repr class");
    }

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
fn test_repr2_nullary_enum_passes_strict_kernel_check() {
    let mut env = make_repr_env();
    let handler = DeriveRepr2;
    let tn = Name::from_string("Color");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("Repr should succeed for nullary enum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // Strict kernel type check: add_decl runs the full kernel checker on the
    // concrete recursor/String-literal term. The no-sorry guard above is what
    // proves genuineness; this proves kernel acceptance of the concrete term.
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived Repr instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived Repr instance should be registered in the environment"
    );
}

/// Extend [`make_repr_env`] with a `Repr Nat` instance (`instReprNat`) and a
/// single-ctor struct `Point.mk : Nat → Nat → Point`. The `Repr Nat` instance is
/// registered both as a kernel definition (so its declared type is `Repr Nat`)
/// and as a class instance (so the struct handler can resolve it). `String` and
/// `String.append` come from the prelude; the kernel auto-generates `Point.rec`
/// and `Repr.rec`, which the synthesized struct `Repr` instance dispatches
/// through (the latter to extract each field's `reprPrec`).
fn make_repr_struct_env() -> Environment {
    let mut env = make_repr_env();
    let nat = Expr::const_str("Nat");
    let string = Expr::const_str("String");

    // The prelude now declares a real axiom-free `String.append`
    // (`String → String → String`). For environments built before that change
    // (or minimal ones), fall back to declaring a total stand-in of the same
    // signature so the derived struct `Repr` term — which concatenates its
    // rendered parts via `String.append` — passes the strict kernel check.
    // (Repr is data-only; the no-sorry guard, not the append semantics, is what
    // proves genuineness.)
    if env.get_const(&Name::from_string("String.append")).is_none() {
        let append_ty = Expr::pi(
            BinderInfo::Default,
            string.clone(),
            Expr::pi(BinderInfo::Default, string.clone(), string.clone()),
        );
        let append_val = Expr::lam(
            BinderInfo::Default,
            string.clone(),
            Expr::lam(BinderInfo::Default, string.clone(), Expr::bvar(1)),
        );
        env.add_decl(Declaration::Definition {
            name: Name::from_string("String.append"),
            level_params: vec![],
            type_: append_ty,
            value: append_val,
            is_reducible: true,
        })
        .expect("should add String.append stand-in");
    }

    let repr_nat_ty = Expr::app(Expr::const_str("Repr"), nat.clone());
    // instReprNat := @Repr.mk Nat (fun (_ : Nat) (_ : Nat) => "Nat").
    let repr_prec = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::str_lit("Nat")),
    );
    let repr_nat_val = Expr::apps(Expr::const_str("Repr.mk"), [nat.clone(), repr_prec]);
    // `with_prelude` now provides `instReprNat`; only add the test stand-in when
    // it is absent (Task NN idempotence).
    if env.get_const(&Name::from_string("instReprNat")).is_none() {
        env.add_decl(Declaration::Definition {
            name: Name::from_string("instReprNat"),
            level_params: vec![],
            type_: repr_nat_ty,
            value: repr_nat_val,
            is_reducible: true,
        })
        .expect("should add instReprNat");
        env.register_instance(clean_kernel::KernelInstanceInfo {
            name: Name::from_string("instReprNat"),
            class_name: Name::from_string("Repr"),
            priority: 100,
            type_: None,
            value: None,
        });
    }

    // Point.mk : Nat → Nat → Point.
    let type0 = Expr::sort(Level::succ(Level::zero()));
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
fn test_repr2_struct_resolvable_fields_value_is_sorry_free() {
    // `Point.mk : Nat → Nat → Point` has fields whose `Repr` instance the env
    // resolves (`instReprNat`), so the handler renders the struct via the
    // recursor + each field's `reprPrec`, with NO sorry and NO constant fallback.
    let env = make_repr_struct_env();
    let handler = DeriveRepr2;
    let tn = Name::from_string("Point");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("Repr should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "resolvable-field struct Repr value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Point.rec"),
        "struct Repr must project fields via the struct recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Repr.rec"),
        "struct Repr must extract each field's reprPrec via the Repr recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "String.append"),
        "struct Repr must concatenate the rendered parts via String.append: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instReprNat"),
        "struct Repr must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
}

#[test]
fn test_repr2_struct_resolvable_fields_passes_strict_kernel_check() {
    let mut env = make_repr_struct_env();
    let handler = DeriveRepr2;
    let tn = Name::from_string("Point");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("Repr should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "struct Repr value must be sorry-free before the kernel check: {value:?}"
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
        "derived struct Repr instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived struct Repr instance should be registered in the environment"
    );
}

#[test]
fn test_repr2_struct_unresolvable_field_fails_closed() {
    let handler = DeriveRepr2;
    let tn = Name::from_string("Opaque");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &unresolvable_field_ctor(),
        0,
        &[],
    );
    assert_unsupported(result, "Repr");
}

// ---------------------------------------------------------------------------
// DeriveDecidableEq2 soundness tests
// (sorry-free recursor + noConfusion dispatch for nullary enums)
// ---------------------------------------------------------------------------

/// Build an environment with the full prelude (which supplies `Eq`, `Eq.refl`,
/// `Decidable`, `Decidable.isTrue`, `Decidable.isFalse`, `DecidableEq`, `Not`,
/// and `False`) plus a `Color` nullary enum (`Color.Red`, `Color.Blue`). The
/// kernel auto-generates `Color.rec` and `Color.noConfusion` on `add_inductive`,
/// both of which the synthesized `DecidableEq` instance dispatches through.
fn make_deceq_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
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
    .expect("should add Color enum");
    env
}

#[test]
fn test_deceq2_nullary_enum_value_is_sorry_free() {
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for nullary enum");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "nullary-enum DecidableEq instance value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The genuine instance dispatches via the enum recursor (outer + inner) and
    // discharges the off-diagonal via Color.noConfusion + Decidable.isFalse, and
    // the diagonal via Decidable.isTrue + Eq.refl.
    assert!(
        expr_mentions_const(&decls[0].value, "Color.rec"),
        "instance value should dispatch through the enum recursor Color.rec: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Color.noConfusion"),
        "distinct-ctor case should use Color.noConfusion: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.isTrue"),
        "diagonal case should use Decidable.isTrue: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.isFalse"),
        "off-diagonal case should use Decidable.isFalse: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Eq.refl"),
        "diagonal proof should be Eq.refl: {:?}",
        decls[0].value
    );
}

#[test]
fn test_deceq2_single_nullary_ctor_is_sorry_free() {
    // A single nullary constructor is the degenerate nullary-enum case: the only
    // pair is the diagonal, so the body is Decidable.isTrue + Eq.refl with no
    // off-diagonal noConfusion branch.
    let handler = DeriveDecidableEq2;
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
        .expect("DecidableEq should succeed for single nullary ctor");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "single nullary ctor DecidableEq value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Unit.rec"),
        "single-ctor instance should dispatch through Unit.rec"
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.isTrue"),
        "single-ctor diagonal should use Decidable.isTrue"
    );
    assert!(
        !expr_mentions_const(&decls[0].value, "Unit.noConfusion"),
        "single-ctor instance has no off-diagonal, so no noConfusion: {:?}",
        decls[0].value
    );
}

#[test]
fn test_deceq2_struct_unresolvable_field_fails_closed() {
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Opaque");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &unresolvable_field_ctor(),
        0,
        &[],
    );
    assert_unsupported(result, "DecidableEq");
}

#[test]
fn test_deceq2_recursive_fails_closed() {
    // Recursive constructors are rejected outright by reject_recursive, before
    // the nullary-enum construction is even attempted.
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(
        result.is_err(),
        "recursive ctors must be rejected, not synthesized"
    );
}

#[test]
fn test_deceq2_parametric_enum_fails_closed() {
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("PColor");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 1, &[]);
    assert_unsupported(result, "DecidableEq");
}

#[test]
fn test_deceq2_nullary_enum_passes_strict_kernel_check() {
    let mut env = make_deceq_env();
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Color");

    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for nullary enum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; this strict kernel type check proves
    // the concrete recursor/noConfusion/isTrue/isFalse term is accepted by the
    // full kernel checker (no sorryAx smuggling, correct universe levels).
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived DecidableEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived DecidableEq instance should be registered in the environment"
    );
}

#[test]
fn test_deceq2_nullary_enum_decides_equal_ctors_true() {
    // The diagonal (Color.Red, Color.Red) must reduce to Decidable.isTrue. We
    // build the kernel-checked instance, then whnf-reduce its application to a
    // matching constructor pair and confirm the head is `Decidable.isTrue`.
    let mut env = make_deceq_env();
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for nullary enum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let red = Expr::const_(Name::from_string("Color.Red"), vec![]);
    // (instDecidableEqColor Color.Red Color.Red) : Decidable (Color.Red = Color.Red)
    let app = Expr::apps(
        Expr::const_(name.clone(), vec![]),
        [red.clone(), red.clone()],
    );
    let reduced = TypeChecker::new(&env).whnf(&app);
    let head = reduced.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Decidable.isTrue"),
        "equal ctors must decide isTrue, got head: {:?}",
        head
    );
}

#[test]
fn test_deceq2_nullary_enum_decides_distinct_ctors_false() {
    // The off-diagonal (Color.Red, Color.Blue) must reduce to Decidable.isFalse.
    let mut env = make_deceq_env();
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for nullary enum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let red = Expr::const_(Name::from_string("Color.Red"), vec![]);
    let blue = Expr::const_(Name::from_string("Color.Blue"), vec![]);
    let app = Expr::apps(Expr::const_(name.clone(), vec![]), [red, blue]);
    let reduced = TypeChecker::new(&env).whnf(&app);
    let head = reduced.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Decidable.isFalse"),
        "distinct ctors must decide isFalse, got head: {:?}",
        head
    );
}

// ---------------------------------------------------------------------------
// DeriveDecidableEq2 struct soundness tests
// (sorry-free per-field Decidable.rec dispatch + congrArg/Eq.trans for the
// single-ctor struct shape; the diagonal closes by the kernel's structure-eta)
// ---------------------------------------------------------------------------

/// A single-ctor struct `Pair.mk : Color → Color → Pair` whose field type
/// (`Color`) has a resolvable `DecidableEq` instance in `make_deceq_struct_env`.
fn pair_ctors() -> Vec<CtorInfo2> {
    let color = Expr::const_str("Color");
    vec![CtorInfo2 {
        name: Name::from_string("Pair.mk"),
        fields: vec![
            (Name::from_string("fst"), color.clone()),
            (Name::from_string("snd"), color),
        ],
        is_recursive: false,
    }]
}

/// Build the full prelude plus a `Color` nullary enum with a genuine, sorry-free
/// `DecidableEq Color` instance (synthesized via the already-pinned nullary-enum
/// path and registered both as a kernel definition and as a class instance), then
/// a single-ctor struct `Pair.mk : Color → Color → Pair`. The struct
/// `DecidableEq` handler resolves `DecidableEq Color` for each field and composes
/// the field decisions; the kernel auto-generates `Pair.rec`, `Color.rec`,
/// `Color.noConfusion`, and `Decidable.rec`, all of which the synthesized
/// instance dispatches through.
fn make_deceq_struct_env() -> Environment {
    let mut env = make_deceq_env();

    // Synthesize and register the genuine `DecidableEq Color` field instance.
    let color = Name::from_string("Color");
    let color_decls = DeriveDecidableEq2
        .derive(&env, &color, &type_expr(), &color_ctors(), 0, &[])
        .expect("DecidableEq Color should synthesize");
    let DerivedDecl2 {
        name: color_inst_name,
        type_: color_inst_ty,
        value: color_inst_val,
        ..
    } = color_decls.into_iter().next().expect("one Color decl");
    env.add_decl(Declaration::Definition {
        name: color_inst_name.clone(),
        level_params: vec![],
        type_: color_inst_ty,
        value: color_inst_val,
        is_reducible: true,
    })
    .expect("instDecidableEqColor should kernel-check");
    env.register_instance(clean_kernel::KernelInstanceInfo {
        name: color_inst_name,
        class_name: Name::from_string("DecidableEq"),
        priority: 100,
        type_: None,
        value: None,
    });

    // Pair.mk : Color → Color → Pair.
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let color_const = Expr::const_(color, vec![]);
    let pair_name = Name::from_string("Pair");
    let pair_mk_ty = Expr::pi(
        BinderInfo::Default,
        color_const.clone(),
        Expr::pi(
            BinderInfo::Default,
            color_const,
            Expr::const_(pair_name.clone(), vec![]),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: type0,
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: pair_mk_ty,
            }],
        }],
    })
    .expect("should add Pair struct");
    env
}

#[test]
fn test_deceq2_struct_resolvable_fields_value_is_sorry_free() {
    // `Pair.mk : Color → Color → Pair` has fields whose `DecidableEq` instance the
    // env resolves (`instDecidableEqColor`), so the handler composes the per-field
    // decisions via `Decidable.rec`, with NO sorry and NO fallback.
    let env = make_deceq_struct_env();
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Pair");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &pair_ctors(), 0, &[])
        .expect("DecidableEq should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "resolvable-field struct DecidableEq value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // Each field decision is dispatched via Decidable.rec; the off-diagonal lifts
    // the field disequality through the projection via congrArg; the diagonal
    // proves a = b by an Eq.trans congruence chain over the constructor and wraps
    // it in Decidable.isTrue. Fields are projected with the kernel `Proj`
    // primitive so the constructor form is the struct-eta expansion of a/b.
    assert!(
        expr_any(&decls[0].value, &|sub| matches!(
            sub.kind(),
            ExprKind::Proj(n, _, _) if n.to_string() == "Pair"
        )),
        "struct DecidableEq must project fields via the kernel Proj primitive: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Pair.mk"),
        "struct DecidableEq diagonal must rebuild the value via the constructor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Eq.trans"),
        "struct DecidableEq diagonal must chain the field congruences via Eq.trans: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.rec"),
        "struct DecidableEq must dispatch each field decision via Decidable.rec: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "congrArg"),
        "struct DecidableEq must lift field (dis)equalities via congrArg: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.isTrue"),
        "struct DecidableEq diagonal must build Decidable.isTrue: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.isFalse"),
        "struct DecidableEq off-diagonal must build Decidable.isFalse: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instDecidableEqColor"),
        "struct DecidableEq must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
}

#[test]
fn test_deceq2_struct_resolvable_fields_passes_strict_kernel_check() {
    let mut env = make_deceq_struct_env();
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Pair");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &pair_ctors(), 0, &[])
        .expect("DecidableEq should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; this strict kernel type check proves the
    // concrete Decidable.rec / congrArg / Eq.trans term — including the diagonal
    // isTrue proof that relies on the kernel's structure-eta — is accepted by the
    // full kernel checker (correct universe levels, no sorryAx smuggling).
    assert!(
        !expr_contains_sorry(&value),
        "struct DecidableEq value must be sorry-free before the kernel check: {value:?}"
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
        "derived struct DecidableEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived struct DecidableEq instance should be registered in the environment"
    );
}

#[test]
fn test_deceq2_struct_decides_equal_pairs_true() {
    // (Pair.mk Red Red, Pair.mk Red Red) — all fields equal — must decide isTrue.
    let mut env = make_deceq_struct_env();
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Pair");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &pair_ctors(), 0, &[])
        .expect("DecidableEq should succeed for resolvable struct");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let red = Expr::const_(Name::from_string("Color.Red"), vec![]);
    let mk = Expr::const_(Name::from_string("Pair.mk"), vec![]);
    let p = Expr::apps(mk, [red.clone(), red]);
    // (instDecidableEqPair p p) : Decidable (p = p) must reduce to isTrue.
    let app = Expr::apps(Expr::const_(name, vec![]), [p.clone(), p]);
    let reduced = TypeChecker::new(&env).whnf(&app);
    let head = reduced.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Decidable.isTrue"),
        "equal pairs must decide isTrue, got head: {head:?}"
    );
}

#[test]
fn test_deceq2_struct_decides_differing_pairs_false() {
    // (Pair.mk Red Red, Pair.mk Red Blue) — second field differs — must decide
    // isFalse via the off-diagonal congrArg-projection lift.
    let mut env = make_deceq_struct_env();
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Pair");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &pair_ctors(), 0, &[])
        .expect("DecidableEq should succeed for resolvable struct");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let red = Expr::const_(Name::from_string("Color.Red"), vec![]);
    let blue = Expr::const_(Name::from_string("Color.Blue"), vec![]);
    let mk = Expr::const_(Name::from_string("Pair.mk"), vec![]);
    let p1 = Expr::apps(mk.clone(), [red.clone(), red.clone()]);
    let p2 = Expr::apps(mk, [red, blue]);
    let app = Expr::apps(Expr::const_(name, vec![]), [p1, p2]);
    let reduced = TypeChecker::new(&env).whnf(&app);
    let head = reduced.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Decidable.isFalse"),
        "differing pairs must decide isFalse, got head: {head:?}"
    );
}

// ---------------------------------------------------------------------------
// DeriveDecidableEq2 multi-ctor-with-fields soundness tests
// (the union of the nullary-enum per-ctor dispatch and the single-ctor-struct
// per-field decide+compose: >= 2 ctors, some/all carrying fields, np == 0,
// non-recursive — e.g. Either<Color,Color>, Result<Color,Color>, mixed).
//
// `DecidableEq` field instances are NOT registered as class instances by the
// prelude (unlike `BEq`/`Hashable`, whose `instBEqNat`/`instHashableNat` the
// prelude supplies). So these tests mirror `make_deceq_struct_env`: the field
// type is `Color`, whose genuine sorry-free `DecidableEq Color` instance is
// synthesized via the already-pinned nullary-enum path and registered both as a
// kernel definition and as a class instance, then the multi-ctor sum is built
// over `Color` fields.
// ---------------------------------------------------------------------------

/// Monomorphic `Either<Color, Color>` constructors: `ECol.left : Color → ECol`
/// and `ECol.right : Color → ECol`. Both carry a single `Color` field.
fn either_color_ctors() -> Vec<CtorInfo2> {
    let color = Expr::const_str("Color");
    vec![
        CtorInfo2 {
            name: Name::from_string("ECol.left"),
            fields: vec![(Name::from_string("a"), color.clone())],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("ECol.right"),
            fields: vec![(Name::from_string("b"), color)],
            is_recursive: false,
        },
    ]
}

/// Monomorphic `Result<Color, Color>` constructors: `RCol.ok : Color → RCol`
/// and `RCol.err : Color → RCol`.
fn result_color_ctors() -> Vec<CtorInfo2> {
    let color = Expr::const_str("Color");
    vec![
        CtorInfo2 {
            name: Name::from_string("RCol.ok"),
            fields: vec![(Name::from_string("v"), color.clone())],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("RCol.err"),
            fields: vec![(Name::from_string("e"), color)],
            is_recursive: false,
        },
    ]
}

/// A mixed sum: one nullary ctor and one `Color`-field ctor (`Maybe`-like).
/// `MCol.none : MCol` and `MCol.some : Color → MCol`. Exercises the 0-field
/// diagonal (short-circuit to `Eq.refl`) alongside a field-carrying diagonal.
fn maybe_color_ctors() -> Vec<CtorInfo2> {
    let color = Expr::const_str("Color");
    vec![
        CtorInfo2 {
            name: Name::from_string("MCol.none"),
            fields: vec![],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("MCol.some"),
            fields: vec![(Name::from_string("v"), color)],
            is_recursive: false,
        },
    ]
}

/// Build `make_deceq_struct_env`'s prelude+`Color`+`instDecidableEqColor` base,
/// then add a monomorphic single-`Color`-field sum `sum_name` with two
/// constructors (`ctor0`, `ctor1`). Returns the environment; the kernel
/// auto-generates `<sum>.rec` and `<sum>.noConfusion`, which the synthesized
/// multi-ctor `DecidableEq` instance dispatches through.
fn make_deceq_color_sum_env(sum_name: &str, ctor0: &str, ctor1: &str) -> Environment {
    let mut env = make_deceq_struct_env();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let color = Expr::const_str("Color");
    let sname = Name::from_string(sum_name);
    let field_to_sum = |s: &Name| {
        Expr::pi(
            BinderInfo::Default,
            color.clone(),
            Expr::const_(s.clone(), vec![]),
        )
    };
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: sname.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string(ctor0),
                    type_: field_to_sum(&sname),
                },
                Constructor {
                    name: Name::from_string(ctor1),
                    type_: field_to_sum(&sname),
                },
            ],
        }],
    })
    .expect("should add Color-field sum");
    env
}

/// `make_deceq_struct_env` base plus a mixed `Maybe Color` sum `MCol`
/// (`MCol.none : MCol`, `MCol.some : Color → MCol`).
fn make_deceq_maybe_color_env() -> Environment {
    let mut env = make_deceq_struct_env();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let color = Expr::const_str("Color");
    let mname = Name::from_string("MCol");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: mname.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MCol.none"),
                    type_: Expr::const_(mname.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("MCol.some"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        color,
                        Expr::const_(mname.clone(), vec![]),
                    ),
                },
            ],
        }],
    })
    .expect("should add MCol (Maybe Color) sum");
    env
}

#[test]
fn test_deceq2_multi_ctor_fields_value_is_sorry_free() {
    // `Either<Color,Color>` (ECol.left : Color → ECol, ECol.right : Color → ECol)
    // has fields whose `DecidableEq` instance the env resolves
    // (`instDecidableEqColor`), so the handler composes the per-field decisions
    // via Decidable.rec, with NO sorry and NO fallback.
    let env = make_deceq_color_sum_env("ECol", "ECol.left", "ECol.right");
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("ECol");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for multi-ctor sum with resolvable fields");
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instDecidableEqECol");
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "multi-ctor-with-fields DecidableEq value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // Dispatch is through the type's recursor; the diagonal decides each field
    // via Decidable.rec (reusing instDecidableEqColor), proves equality via the
    // congruence chain (Eq.trans + congrArg + Decidable.isTrue) and disproves via
    // same-ctor noConfusion; the off-diagonal is Decidable.isFalse via cross-ctor
    // noConfusion.
    assert!(
        expr_mentions_const(&decls[0].value, "ECol.rec"),
        "multi-ctor DecidableEq must dispatch through the recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "ECol.noConfusion"),
        "multi-ctor DecidableEq must discharge inequality via noConfusion: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.rec"),
        "diagonal must dispatch each field decision via Decidable.rec: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instDecidableEqColor"),
        "diagonal must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.isTrue"),
        "diagonal all-equal must build Decidable.isTrue: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Decidable.isFalse"),
        "off-diagonal / differing field must build Decidable.isFalse: {:?}",
        decls[0].value
    );
    // Single-field constructors yield a one-step congruence (no Eq.trans needed);
    // the >= 2-field Eq.trans chain is exercised by
    // `test_deceq2_multi_ctor_two_field_passes_strict_kernel_check`.
    assert!(
        expr_mentions_const(&decls[0].value, "congrArg"),
        "diagonal proof must lift field equalities via congrArg: {:?}",
        decls[0].value
    );
}

#[test]
fn test_deceq2_multi_ctor_fields_passes_strict_kernel_check() {
    let mut env = make_deceq_color_sum_env("ECol", "ECol.left", "ECol.right");
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("ECol");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for multi-ctor sum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; the strict kernel type check proves the
    // concrete nested-recursor / Decidable.rec / noConfusion / congrArg / Eq.trans
    // term — including the diagonal isTrue congruence proof and both the
    // same-ctor (diagonal) and cross-ctor (off-diagonal) noConfusion disproofs —
    // is accepted by the full kernel checker (correct universe levels, no sorryAx
    // smuggling).
    assert!(
        !expr_contains_sorry(&value),
        "multi-ctor DecidableEq value must be sorry-free before the kernel check: {value:?}"
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
        "derived multi-ctor DecidableEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived multi-ctor DecidableEq instance should be registered in the environment"
    );
}

/// Build the kernel-checked `instDecidableEqECol`, then return the whnf head
/// symbol name of `instDecidableEqECol <lhs> <rhs>` (the decision).
fn deceq_ecol_reduce_head(lhs: Expr, rhs: Expr) -> String {
    let mut env = make_deceq_color_sum_env("ECol", "ECol.left", "ECol.right");
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("ECol");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for multi-ctor sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let app = Expr::apps(Expr::const_(name, vec![]), [lhs, rhs]);
    let reduced = TypeChecker::new(&env).whnf(&app);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(n, _) => n.to_string(),
        other => panic!("expected a Const head after whnf, got {other:?}"),
    }
}

#[test]
fn test_deceq2_multi_ctor_fields_diagonal_equal_fields_true() {
    // left Red == left Red -> isTrue: same ctor, equal field (via field DecidableEq).
    let left = |c: &str| {
        Expr::app(
            Expr::const_(Name::from_string("ECol.left"), vec![]),
            Expr::const_(Name::from_string(c), vec![]),
        )
    };
    assert_eq!(
        deceq_ecol_reduce_head(left("Color.Red"), left("Color.Red")),
        "Decidable.isTrue",
        "left Red == left Red must decide isTrue"
    );
}

#[test]
fn test_deceq2_multi_ctor_fields_diagonal_distinct_fields_false() {
    // left Red == left Blue -> isFalse: same ctor, fields differ (field DecidableEq
    // disproves; the same-ctor noConfusion lifts the field disequality).
    let left = |c: &str| {
        Expr::app(
            Expr::const_(Name::from_string("ECol.left"), vec![]),
            Expr::const_(Name::from_string(c), vec![]),
        )
    };
    assert_eq!(
        deceq_ecol_reduce_head(left("Color.Red"), left("Color.Blue")),
        "Decidable.isFalse",
        "left Red == left Blue must decide isFalse via the differing-field branch"
    );
}

#[test]
fn test_deceq2_multi_ctor_fields_off_diagonal_false() {
    // left Red == right Red -> isFalse: distinct ctors are never equal,
    // regardless of field payload (off-diagonal cross-ctor noConfusion arm).
    let left = Expr::app(
        Expr::const_(Name::from_string("ECol.left"), vec![]),
        Expr::const_(Name::from_string("Color.Red"), vec![]),
    );
    let right = Expr::app(
        Expr::const_(Name::from_string("ECol.right"), vec![]),
        Expr::const_(Name::from_string("Color.Red"), vec![]),
    );
    assert_eq!(
        deceq_ecol_reduce_head(left, right),
        "Decidable.isFalse",
        "left Red == right Red must decide isFalse via the off-diagonal arm"
    );
}

#[test]
fn test_deceq2_result_color_multi_ctor_fields_passes_strict_kernel_check() {
    // Result<Color,Color> as a second monomorphic multi-ctor sum: confirms the
    // construction is not specific to the Either naming and kernel-checks.
    let mut env = make_deceq_color_sum_env("RCol", "RCol.ok", "RCol.err");
    let handler = DeriveDecidableEq2;
    let rname = Name::from_string("RCol");
    let decls = handler
        .derive(&env, &rname, &type_expr(), &result_color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for Result<Color,Color> sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "Result DecidableEq value must be sorry-free: {value:?}"
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
        "derived Result DecidableEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
}

#[test]
fn test_deceq2_multi_ctor_two_field_passes_strict_kernel_check() {
    // A multi-ctor sum whose first constructor carries TWO Color fields exercises
    // the diagonal `Eq.trans` congruence chain (>= 2 fields) and the multi-field
    // same-ctor noConfusion eliminator (the deepest de Bruijn path). `T2Col.pair :
    // Color → Color → T2Col`, `T2Col.single : Color → T2Col`.
    let mut env = make_deceq_struct_env();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let color = Expr::const_str("Color");
    let tname = Name::from_string("T2Col");
    let pair_ty = Expr::pi(
        BinderInfo::Default,
        color.clone(),
        Expr::pi(
            BinderInfo::Default,
            color.clone(),
            Expr::const_(tname.clone(), vec![]),
        ),
    );
    let single_ty = Expr::pi(
        BinderInfo::Default,
        color.clone(),
        Expr::const_(tname.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: tname.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("T2Col.pair"),
                    type_: pair_ty,
                },
                Constructor {
                    name: Name::from_string("T2Col.single"),
                    type_: single_ty,
                },
            ],
        }],
    })
    .expect("should add T2Col sum");

    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("T2Col.pair"),
            fields: vec![
                (Name::from_string("x"), color.clone()),
                (Name::from_string("y"), color.clone()),
            ],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("T2Col.single"),
            fields: vec![(Name::from_string("z"), color)],
            is_recursive: false,
        },
    ];
    let handler = DeriveDecidableEq2;
    let decls = handler
        .derive(&env, &tname, &type_expr(), &ctors, 0, &[])
        .expect("DecidableEq should succeed for two-field multi-ctor sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "two-field multi-ctor DecidableEq value must be sorry-free: {value:?}"
    );
    // The two-field pair diagonal genuinely chains its two field congruences.
    assert!(
        expr_mentions_const(&value, "Eq.trans"),
        "two-field diagonal proof must chain congruences via Eq.trans: {value:?}"
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
        "derived two-field multi-ctor DecidableEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );

    // pair Red Blue == pair Red Blue -> isTrue (both fields equal, trans chain);
    // pair Red Blue == pair Red Red -> isFalse (second field differs).
    let pair = |c0: &str, c1: &str| {
        Expr::apps(
            Expr::const_(Name::from_string("T2Col.pair"), vec![]),
            [
                Expr::const_(Name::from_string(c0), vec![]),
                Expr::const_(Name::from_string(c1), vec![]),
            ],
        )
    };
    let dec = |lhs: Expr, rhs: Expr| {
        let app = Expr::apps(Expr::const_(name.clone(), vec![]), [lhs, rhs]);
        match TypeChecker::new(&env).whnf(&app).get_app_fn().kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => panic!("expected a Const head, got {other:?}"),
        }
    };
    assert_eq!(
        dec(
            pair("Color.Red", "Color.Blue"),
            pair("Color.Red", "Color.Blue")
        ),
        "Decidable.isTrue",
        "pair Red Blue == pair Red Blue must decide isTrue (two-field trans chain)"
    );
    assert_eq!(
        dec(
            pair("Color.Red", "Color.Blue"),
            pair("Color.Red", "Color.Red")
        ),
        "Decidable.isFalse",
        "pair Red Blue == pair Red Red must decide isFalse (second field differs)"
    );
}

#[test]
fn test_deceq2_mixed_nullary_and_field_ctor_passes_strict_kernel_check() {
    // A mixed sum (one 0-field ctor, one Color-field ctor): the 0-field diagonal
    // short-circuits to Eq.refl, the field-carrying diagonal decides one Color
    // field, and the off-diagonal is cross-ctor noConfusion.
    let mut env = make_deceq_maybe_color_env();
    let handler = DeriveDecidableEq2;
    let mname = Name::from_string("MCol");
    let decls = handler
        .derive(&env, &mname, &type_expr(), &maybe_color_ctors(), 0, &[])
        .expect("DecidableEq should succeed for mixed nullary/field sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "mixed-sum DecidableEq value must be sorry-free: {value:?}"
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
        "derived mixed-sum DecidableEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );

    // none == none -> isTrue (0-field diagonal); none == some Red -> isFalse.
    let none = Expr::const_(Name::from_string("MCol.none"), vec![]);
    let some = |c: &str| {
        Expr::app(
            Expr::const_(Name::from_string("MCol.some"), vec![]),
            Expr::const_(Name::from_string(c), vec![]),
        )
    };
    let dec = |lhs: Expr, rhs: Expr| {
        let app = Expr::apps(Expr::const_(name.clone(), vec![]), [lhs, rhs]);
        match TypeChecker::new(&env).whnf(&app).get_app_fn().kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => panic!("expected a Const head, got {other:?}"),
        }
    };
    assert_eq!(
        dec(none.clone(), none.clone()),
        "Decidable.isTrue",
        "none == none must decide isTrue (0-field diagonal)"
    );
    assert_eq!(
        dec(none, some("Color.Red")),
        "Decidable.isFalse",
        "none == some Red must decide isFalse (off-diagonal)"
    );
    assert_eq!(
        dec(some("Color.Red"), some("Color.Red")),
        "Decidable.isTrue",
        "some Red == some Red must decide isTrue (field diagonal)"
    );
    assert_eq!(
        dec(some("Color.Red"), some("Color.Blue")),
        "Decidable.isFalse",
        "some Red == some Blue must decide isFalse (differing field)"
    );
}

#[test]
fn test_deceq2_multi_ctor_fields_unresolvable_field_fails_closed() {
    let nat = Expr::const_str("Nat");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("Mix.a"),
            fields: vec![(Name::from_string("x"), nat)],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("Mix.b"),
            fields: vec![(Name::from_string("w"), Expr::const_str("Widget"))],
            is_recursive: false,
        },
    ];
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("Mix");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert_unsupported(result, "DecidableEq");
}

#[test]
fn test_deceq2_multi_ctor_fields_recursive_stays_rejected() {
    // A multi-ctor sum with a recursive constructor is rejected outright by
    // reject_recursive, before the multi-ctor construction is attempted.
    let color = Expr::const_str("Color");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("RList.nil"),
            fields: vec![],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("RList.cons"),
            fields: vec![
                (Name::from_string("head"), color),
                (Name::from_string("tail"), Expr::const_str("RList")),
            ],
            is_recursive: true,
        },
    ];
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("RList");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert!(
        result.is_err(),
        "recursive multi-ctor sum must be rejected, not synthesized"
    );
}

#[test]
fn test_deceq2_multi_ctor_fields_parametric_fails_closed() {
    let handler = DeriveDecidableEq2;
    let tn = Name::from_string("PEither");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &either_color_ctors(),
        1,
        &[],
    );
    assert_unsupported(result, "DecidableEq");
}

// ---------------------------------------------------------------------------
// DeriveBEq2 soundness tests
// (sorry-free nested-recursor Bool dispatch for nullary enums)
// ---------------------------------------------------------------------------

/// Build an environment with the full prelude (which supplies `Bool`,
/// `Bool.true`, `Bool.false`, and the `BEq`/`BEq.mk` typeclass) plus a `Color`
/// nullary enum (`Color.Red`, `Color.Blue`). The kernel auto-generates
/// `Color.rec` on `add_inductive`, which the synthesized `BEq` instance
/// dispatches through. `BEq` returns a plain `Bool`, so no `noConfusion`/`Eq`
/// machinery is required.
fn make_beq_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
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
    .expect("should add Color enum");
    env
}

#[test]
fn test_beq2_nullary_enum_value_is_sorry_free() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("BEq should succeed for nullary enum");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "nullary-enum BEq instance value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The genuine instance dispatches via the enum recursor (outer + inner) and
    // returns Bool.true on the diagonal, Bool.false off-diagonal — no proof
    // terms (no Eq.refl / noConfusion), since beq returns a plain Bool.
    assert!(
        expr_mentions_const(&decls[0].value, "Color.rec"),
        "instance value should dispatch through the enum recursor Color.rec: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "BEq.mk"),
        "instance value should use BEq.mk: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Bool.true"),
        "diagonal case should yield Bool.true: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Bool.false"),
        "off-diagonal case should yield Bool.false: {:?}",
        decls[0].value
    );
    // BEq carries no proof obligation, so the diagonal needs no Eq.refl and the
    // off-diagonal needs no noConfusion (contrast with DecidableEq).
    assert!(
        !expr_mentions_const(&decls[0].value, "Eq.refl"),
        "BEq instance must not fabricate proof terms (Eq.refl): {:?}",
        decls[0].value
    );
    assert!(
        !expr_mentions_const(&decls[0].value, "Color.noConfusion"),
        "BEq instance must not fabricate proof terms (noConfusion): {:?}",
        decls[0].value
    );
}

#[test]
fn test_beq2_single_nullary_ctor_value_is_sorry_free() {
    // A single nullary constructor is the degenerate nullary-enum case: the only
    // pair is the diagonal, so the body returns Bool.true with no off-diagonal
    // Bool.false branch, still dispatched through the recursor.
    let handler = DeriveBEq2;
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
        .expect("BEq should succeed for single nullary ctor");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "single nullary ctor BEq value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Unit.rec"),
        "single-ctor instance should dispatch through Unit.rec: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Bool.true"),
        "single-ctor diagonal should yield Bool.true: {:?}",
        decls[0].value
    );
    assert!(
        !expr_mentions_const(&decls[0].value, "Bool.false"),
        "single-ctor instance has no off-diagonal, so no Bool.false: {:?}",
        decls[0].value
    );
}

/// A single-ctor struct `Opaque.mk : Widget → Opaque` whose field type `Widget`
/// has no `BEq`/`Repr` instance in the prelude. Used for the negative path: the
/// field instance is unresolvable, so the struct handlers reject the shape.
fn unresolvable_field_ctor() -> Vec<CtorInfo2> {
    vec![CtorInfo2 {
        name: Name::from_string("Opaque.mk"),
        fields: vec![(Name::from_string("w"), Expr::const_str("Widget"))],
        is_recursive: false,
    }]
}

#[test]
fn test_beq2_struct_unresolvable_field_fails_closed() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("Opaque");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &unresolvable_field_ctor(),
        0,
        &[],
    );
    assert_unsupported(result, "BEq");
}

#[test]
fn test_beq2_struct_resolvable_fields_value_is_sorry_free() {
    // `Point.mk : Nat → Nat → Point` has fields whose `BEq` instances
    // (`instBEqNat`) the prelude supplies, so the handler synthesizes a genuine,
    // sorry-free `beq` that conjoins per-field comparisons.
    let handler = DeriveBEq2;
    let tn = Name::from_string("Point");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("BEq should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "resolvable-field struct BEq value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // Fields are projected via the struct recursor, compared via BEq.beq, and
    // conjoined via Bool.and.
    assert!(
        expr_mentions_const(&decls[0].value, "Point.rec"),
        "struct BEq must project fields via the recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "BEq.beq"),
        "struct BEq must compare fields via BEq.beq: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Bool.and"),
        "struct BEq must conjoin field comparisons via Bool.and: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instBEqNat"),
        "struct BEq must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
}

#[test]
fn test_beq2_recursive_stays_rejected() {
    // Recursive constructors are rejected outright by reject_recursive, before
    // the nullary-enum construction is even attempted.
    let handler = DeriveBEq2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(
        result.is_err(),
        "recursive ctors must be rejected, not synthesized"
    );
}

#[test]
fn test_beq2_parametric_enum_fails_closed() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("PColor");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 1, &[]);
    assert_unsupported(result, "BEq");
}

#[test]
fn test_beq2_nullary_enum_passes_strict_kernel_check() {
    let mut env = make_beq_env();
    let handler = DeriveBEq2;
    let tn = Name::from_string("Color");

    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("BEq should succeed for nullary enum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; this strict kernel type check proves
    // the concrete nested-recursor / Bool-literal term is accepted by the full
    // kernel checker (no sorryAx smuggling, correct universe levels).
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived BEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived BEq instance should be registered in the environment"
    );
}

#[test]
fn test_beq2_nullary_enum_beq_equal_ctors_true() {
    // The diagonal (Color.Red, Color.Red) must reduce to Bool.true. We build the
    // kernel-checked instance, then whnf-reduce the applied `beq` projection on a
    // matching constructor pair and confirm it computes to `Bool.true`.
    let mut env = make_beq_env();
    let handler = DeriveBEq2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("BEq should succeed for nullary enum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let color = Expr::const_(Name::from_string("Color"), vec![]);
    let red = Expr::const_(Name::from_string("Color.Red"), vec![]);
    let inst = Expr::const_(name.clone(), vec![]);
    // @BEq.beq Color instColorBEq Color.Red Color.Red : Bool
    let app = Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
        [color, inst, red.clone(), red],
    );
    let reduced = TypeChecker::new(&env).whnf(&app);
    let head = reduced.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool.true"),
        "equal ctors must beq to Bool.true, got head: {:?}",
        head
    );
}

#[test]
fn test_beq2_nullary_enum_beq_distinct_ctors_false() {
    // The off-diagonal (Color.Red, Color.Blue) must reduce to Bool.false.
    let mut env = make_beq_env();
    let handler = DeriveBEq2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("BEq should succeed for nullary enum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let color = Expr::const_(Name::from_string("Color"), vec![]);
    let red = Expr::const_(Name::from_string("Color.Red"), vec![]);
    let blue = Expr::const_(Name::from_string("Color.Blue"), vec![]);
    let inst = Expr::const_(name.clone(), vec![]);
    let app = Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
        [color, inst, red, blue],
    );
    let reduced = TypeChecker::new(&env).whnf(&app);
    let head = reduced.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool.false"),
        "distinct ctors must beq to Bool.false, got head: {:?}",
        head
    );
}

/// Build a prelude environment plus a single-ctor struct `Point.mk : Nat → Nat →
/// Point`. The prelude supplies `BEq`, `BEq.beq`, `Bool.and`, and `instBEqNat`;
/// the kernel auto-generates `Point.rec` on `add_inductive`, which the
/// synthesized struct `BEq` instance projects fields through.
fn make_beq_struct_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let point_name = Name::from_string("Point");
    // Point.mk : Nat → Nat → Point.
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
fn test_beq2_struct_resolvable_fields_passes_strict_kernel_check() {
    let mut env = make_beq_struct_env();
    let handler = DeriveBEq2;
    let tn = Name::from_string("Point");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("BEq should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; this strict kernel type check proves the
    // concrete field-projection / BEq.beq / Bool.and term is accepted by the full
    // kernel checker (correct universe levels, no sorryAx smuggling).
    assert!(
        !expr_contains_sorry(&value),
        "struct BEq value must be sorry-free before the kernel check: {value:?}"
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
        "derived struct BEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived struct BEq instance should be registered in the environment"
    );
}

// ---------------------------------------------------------------------------
// DeriveBEq2 multi-ctor-with-fields soundness tests
// (the union of the nullary-enum per-ctor dispatch and the single-ctor-struct
// field composition: >= 2 ctors, some/all carrying fields, np == 0,
// non-recursive — e.g. Either<Nat,Nat>, Result<Nat,Nat>)
// ---------------------------------------------------------------------------

/// Monomorphic `Either<Nat, Nat>` constructors: `ENat.left : Nat → ENat` and
/// `ENat.right : Nat → ENat`. Both carry a single `Nat` field whose `BEq`
/// instance (`instBEqNat`) the prelude supplies.
fn either_nat_ctors() -> Vec<CtorInfo2> {
    let nat = Expr::const_str("Nat");
    vec![
        CtorInfo2 {
            name: Name::from_string("ENat.left"),
            fields: vec![(Name::from_string("a"), nat.clone())],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("ENat.right"),
            fields: vec![(Name::from_string("b"), nat)],
            is_recursive: false,
        },
    ]
}

/// Monomorphic `Result<Nat, Nat>` constructors: `RNat.ok : Nat → RNat` and
/// `RNat.err : Nat → RNat`.
fn result_nat_ctors() -> Vec<CtorInfo2> {
    let nat = Expr::const_str("Nat");
    vec![
        CtorInfo2 {
            name: Name::from_string("RNat.ok"),
            fields: vec![(Name::from_string("v"), nat.clone())],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("RNat.err"),
            fields: vec![(Name::from_string("e"), nat)],
            is_recursive: false,
        },
    ]
}

/// A mixed sum: one nullary ctor and one field-carrying ctor (`Maybe`-like).
/// `MNat.none : MNat` and `MNat.some : Nat → MNat`. Exercises the 0-field
/// diagonal collapsing to `Bool.true` alongside a field-carrying diagonal.
fn maybe_nat_ctors() -> Vec<CtorInfo2> {
    let nat = Expr::const_str("Nat");
    vec![
        CtorInfo2 {
            name: Name::from_string("MNat.none"),
            fields: vec![],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("MNat.some"),
            fields: vec![(Name::from_string("v"), nat)],
            is_recursive: false,
        },
    ]
}

/// Build a prelude environment plus a monomorphic `Either<Nat,Nat>` inductive
/// `ENat` with `ENat.left : Nat → ENat` and `ENat.right : Nat → ENat`. The
/// kernel auto-generates `ENat.rec` on `add_inductive`, which the synthesized
/// multi-ctor BEq instance dispatches through; the prelude supplies `BEq`,
/// `BEq.beq`, `Bool.and`, and `instBEqNat`.
fn make_either_nat_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let ename = Name::from_string("ENat");
    let field_to_e = |e: &Name| {
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::const_(e.clone(), vec![]),
        )
    };
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ename.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("ENat.left"),
                    type_: field_to_e(&ename),
                },
                Constructor {
                    name: Name::from_string("ENat.right"),
                    type_: field_to_e(&ename),
                },
            ],
        }],
    })
    .expect("should add ENat (Either Nat Nat) sum");
    env
}

#[test]
fn test_beq2_multi_ctor_fields_value_is_sorry_free() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("ENat");
    let decls = handler
        .derive(
            &derive_env(),
            &tn,
            &type_expr(),
            &either_nat_ctors(),
            0,
            &[],
        )
        .expect("BEq should succeed for multi-ctor sum with resolvable fields");
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instBEqENat");
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "multi-ctor-with-fields BEq value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The diagonal conjoins per-field BEq.beq via Bool.and (reusing instBEqNat);
    // the off-diagonal is Bool.false. Dispatch is through the type's recursor.
    assert!(
        expr_mentions_const(&decls[0].value, "ENat.rec"),
        "multi-ctor BEq must dispatch through the recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "BEq.beq"),
        "diagonal must compare fields via BEq.beq: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Bool.and"),
        "diagonal must conjoin field comparisons via Bool.and: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instBEqNat"),
        "diagonal must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Bool.false"),
        "off-diagonal pairs must yield Bool.false: {:?}",
        decls[0].value
    );
    // BEq returns a plain Bool, so no proof terms are fabricated.
    assert!(
        !expr_mentions_const(&decls[0].value, "Eq.refl"),
        "multi-ctor BEq must not fabricate proof terms (Eq.refl): {:?}",
        decls[0].value
    );
    assert!(
        !expr_mentions_const(&decls[0].value, "ENat.noConfusion"),
        "multi-ctor BEq must not fabricate proof terms (noConfusion): {:?}",
        decls[0].value
    );
}

#[test]
fn test_beq2_multi_ctor_fields_unresolvable_field_fails_closed() {
    let nat = Expr::const_str("Nat");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("Mix.a"),
            fields: vec![(Name::from_string("x"), nat)],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("Mix.b"),
            fields: vec![(Name::from_string("w"), Expr::const_str("Widget"))],
            is_recursive: false,
        },
    ];
    let handler = DeriveBEq2;
    let tn = Name::from_string("Mix");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert_unsupported(result, "BEq");
}

#[test]
fn test_beq2_multi_ctor_fields_recursive_stays_rejected() {
    // A multi-ctor sum with a recursive constructor is rejected outright by
    // reject_recursive, before the multi-ctor construction is attempted.
    let nat = Expr::const_str("Nat");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("RList.nil"),
            fields: vec![],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("RList.cons"),
            fields: vec![
                (Name::from_string("head"), nat),
                (Name::from_string("tail"), Expr::const_str("RList")),
            ],
            is_recursive: true,
        },
    ];
    let handler = DeriveBEq2;
    let tn = Name::from_string("RList");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert!(
        result.is_err(),
        "recursive multi-ctor sum must be rejected, not synthesized"
    );
}

#[test]
fn test_beq2_multi_ctor_fields_parametric_fails_closed() {
    let handler = DeriveBEq2;
    let tn = Name::from_string("PEither");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &either_nat_ctors(),
        1,
        &[],
    );
    assert_unsupported(result, "BEq");
}

#[test]
fn test_beq2_multi_ctor_fields_passes_strict_kernel_check() {
    let mut env = make_either_nat_env();
    let handler = DeriveBEq2;
    let tn = Name::from_string("ENat");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_nat_ctors(), 0, &[])
        .expect("BEq should succeed for multi-ctor sum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; the strict kernel type check proves the
    // concrete nested-recursor / field-projection / Bool.and term is accepted by
    // the full kernel checker (correct universe levels, no sorryAx smuggling).
    assert!(
        !expr_contains_sorry(&value),
        "multi-ctor BEq value must be sorry-free before the kernel check: {value:?}"
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
        "derived multi-ctor BEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived multi-ctor BEq instance should be registered in the environment"
    );
}

/// Build the kernel-checked `instBEqENat`, then return the whnf head symbol name
/// of `@BEq.beq ENat inst <lhs> <rhs>`.
fn beq_enat_reduce_head(lhs: Expr, rhs: Expr) -> String {
    let mut env = make_either_nat_env();
    let handler = DeriveBEq2;
    let tn = Name::from_string("ENat");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_nat_ctors(), 0, &[])
        .expect("BEq should succeed for multi-ctor sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let enat = Expr::const_(Name::from_string("ENat"), vec![]);
    let inst = Expr::const_(name, vec![]);
    let app = Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
        [enat, inst, lhs, rhs],
    );
    let reduced = TypeChecker::new(&env).whnf(&app);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(n, _) => n.to_string(),
        other => panic!("expected a Const head after whnf, got {other:?}"),
    }
}

#[test]
fn test_beq2_multi_ctor_fields_diagonal_equal_fields_true() {
    // left 1 == left 1 -> Bool.true: same ctor, equal fields (via field BEq).
    let left = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("ENat.left"), vec![]),
            Expr::nat_lit(n),
        )
    };
    assert_eq!(
        beq_enat_reduce_head(left(1), left(1)),
        "Bool.true",
        "left 1 == left 1 must beq to Bool.true"
    );
}

#[test]
fn test_beq2_multi_ctor_fields_diagonal_distinct_fields_false() {
    // left 1 == left 2 -> Bool.false: same ctor, fields differ (via field BEq).
    let left = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("ENat.left"), vec![]),
            Expr::nat_lit(n),
        )
    };
    assert_eq!(
        beq_enat_reduce_head(left(1), left(2)),
        "Bool.false",
        "left 1 == left 2 must beq to Bool.false via the field BEq comparison"
    );
}

#[test]
fn test_beq2_multi_ctor_fields_off_diagonal_false() {
    // left 1 == right 1 -> Bool.false: distinct ctors are never equal,
    // regardless of field payload (off-diagonal arm).
    let left = Expr::app(
        Expr::const_(Name::from_string("ENat.left"), vec![]),
        Expr::nat_lit(1),
    );
    let right = Expr::app(
        Expr::const_(Name::from_string("ENat.right"), vec![]),
        Expr::nat_lit(1),
    );
    assert_eq!(
        beq_enat_reduce_head(left, right),
        "Bool.false",
        "left 1 == right 1 must beq to Bool.false via the off-diagonal arm"
    );
}

#[test]
fn test_beq2_result_nat_multi_ctor_fields_passes_strict_kernel_check() {
    // Result<Nat,Nat> as a second monomorphic multi-ctor sum: RNat.ok : Nat →
    // RNat, RNat.err : Nat → RNat. Confirms the construction is not specific to
    // the Either naming and kernel-checks.
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let rname = Name::from_string("RNat");
    let field_to_r = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::const_(rname.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: rname.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("RNat.ok"),
                    type_: field_to_r.clone(),
                },
                Constructor {
                    name: Name::from_string("RNat.err"),
                    type_: field_to_r,
                },
            ],
        }],
    })
    .expect("should add RNat (Result Nat Nat) sum");

    let handler = DeriveBEq2;
    let decls = handler
        .derive(&env, &rname, &type_expr(), &result_nat_ctors(), 0, &[])
        .expect("BEq should succeed for Result<Nat,Nat> sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "Result BEq value must be sorry-free: {value:?}"
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
        "derived Result BEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
}

#[test]
fn test_beq2_mixed_nullary_and_field_ctor_passes_strict_kernel_check() {
    // A mixed sum (one 0-field ctor, one field-carrying ctor): the 0-field
    // diagonal collapses to Bool.true (empty conjunction), the field-carrying
    // diagonal conjoins one BEq.beq, off-diagonal is Bool.false.
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let mname = Name::from_string("MNat");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: mname.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MNat.none"),
                    type_: Expr::const_(mname.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("MNat.some"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        nat,
                        Expr::const_(mname.clone(), vec![]),
                    ),
                },
            ],
        }],
    })
    .expect("should add MNat (Maybe Nat) sum");

    let handler = DeriveBEq2;
    let decls = handler
        .derive(&env, &mname, &type_expr(), &maybe_nat_ctors(), 0, &[])
        .expect("BEq should succeed for mixed nullary/field sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "mixed-sum BEq value must be sorry-free: {value:?}"
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
        "derived mixed-sum BEq instance must pass strict kernel type check: {:?}",
        add_result.err()
    );

    // none == none -> Bool.true (0-field diagonal), none == some 0 -> Bool.false.
    let none = Expr::const_(Name::from_string("MNat.none"), vec![]);
    let some0 = Expr::app(
        Expr::const_(Name::from_string("MNat.some"), vec![]),
        Expr::nat_lit(0),
    );
    let inst = Expr::const_(name, vec![]);
    let mnat = Expr::const_(mname, vec![]);
    let beq = |lhs: Expr, rhs: Expr| {
        let app = Expr::apps(
            Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]),
            [mnat.clone(), inst.clone(), lhs, rhs],
        );
        match TypeChecker::new(&env).whnf(&app).get_app_fn().kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => panic!("expected Const head, got {other:?}"),
        }
    };
    assert_eq!(
        beq(none.clone(), none.clone()),
        "Bool.true",
        "none == none must beq to Bool.true (empty conjunction on the 0-field diagonal)"
    );
    assert_eq!(
        beq(none, some0),
        "Bool.false",
        "none == some 0 must beq to Bool.false (off-diagonal)"
    );
}

// ---------------------------------------------------------------------------
// DeriveHashable2 soundness tests
// (sorry-free recursor dispatch into per-constructor Nat hashes for nullary
// enums; Clean's in-tree `Hashable` hashes into `Nat`, not `UInt64`)
// ---------------------------------------------------------------------------

/// True iff `expr` is the natural number `n`, accepting either the peano form
/// (`Nat.succ`-chain over `Nat.zero`) or the kernel's native literal form
/// (`Lit(Nat n)`). `whnf` may leave either representation depending on whether
/// the native Nat reducer fired.
fn nat_value_is(expr: &Expr, n: u64) -> bool {
    if *expr == Expr::nat_lit(n) {
        return true;
    }
    // Peano walk: strip `n` `Nat.succ` applications, then expect `Nat.zero`.
    let mut curr = expr;
    let mut remaining = n;
    loop {
        let head = curr.get_app_fn();
        let args = curr.get_app_args();
        match head.kind() {
            ExprKind::Const(name, _) if name.to_string() == "Nat.succ" && args.len() == 1 => {
                if remaining == 0 {
                    return false;
                }
                remaining -= 1;
                curr = args[0];
            }
            ExprKind::Const(name, _) if name.to_string() == "Nat.zero" && args.is_empty() => {
                return remaining == 0;
            }
            _ => return false,
        }
    }
}

/// Build an environment with a `Hashable` class (`hash : α → Nat`, matching the
/// in-tree `init_hashable` shape — Clean uses `Nat`, not `UInt64`), a
/// `Hashable.hash` accessor that projects the field via `Hashable.rec`, and a
/// `Color` nullary enum (`Color.Red`, `Color.Blue`). `Nat` comes from the
/// prelude (the motive eliminates into `Nat : Type`). The kernel auto-generates
/// `Color.rec` and `Hashable.rec` on `add_inductive`, which the synthesized
/// instance and the accessor dispatch through respectively.
fn make_hashable_env() -> Environment {
    let mut env = Environment::with_prelude();
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");

    // Hashable : Type → Type with mk : {α : Type} → (α → Nat) → Hashable α.
    let hashable_name = Name::from_string("Hashable");
    let hashable_ty = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    // hash field type: α → Nat, where α = bvar(0) under the implicit binder.
    let hash_field_ty = Expr::pi(BinderInfo::Default, Expr::bvar(0), nat.clone());
    let hashable_mk_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            hash_field_ty,
            Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    // `with_prelude` now bootstraps a real `Hashable` class with the same
    // `hash : α → Nat` shape (Task NN); only declare the stand-in when absent.
    if env.get_inductive(&hashable_name).is_none() {
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: hashable_name.clone(),
                type_: hashable_ty,
                constructors: vec![Constructor {
                    name: Name::from_string("Hashable.mk"),
                    type_: hashable_mk_ty,
                }],
            }],
        })
        .expect("should add Hashable class");
    }

    // Hashable.hash : {α : Type} → Hashable α → α → Nat, projecting the field
    // via Hashable.rec (mirrors the in-tree `init_hashable` accessor at the
    // concrete universe `α : Type 0`, so `Hashable.rec.{1, 0}`).
    let hash_accessor_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(0)),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), nat.clone()),
        ),
    );
    // value: fun {α} (inst) => @Hashable.rec.{1} α (fun _ => α → Nat)
    //          (fun f => f) inst
    // This monomorphic `Hashable` has no level params, so its auto-generated
    // recursor takes a single level (the motive universe `1`, since the motive
    // eliminates into `α → Nat : Type 0 = Sort 1`).
    // motive (constant): fun (_ : Hashable α) => α → Nat, with α = bvar 1 here.
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(1)),
        Expr::pi(BinderInfo::Default, Expr::bvar(2), nat.clone()),
    );
    // minor: fun (f : α → Nat) => f, with α = bvar 1 outside the minor binder.
    let minor = Expr::lam(
        BinderInfo::Default,
        Expr::pi(BinderInfo::Default, Expr::bvar(1), nat.clone()),
        Expr::bvar(0),
    );
    let rec_body = Expr::apps(
        Expr::const_(
            Name::from_string("Hashable.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::bvar(1), motive, minor, Expr::bvar(0)],
    );
    let hash_accessor_val = Expr::lam(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(0)),
            rec_body,
        ),
    );
    // `with_prelude` now provides `Hashable.hash`; only add the stand-in when
    // absent (Task NN idempotence).
    if env.get_const(&Name::from_string("Hashable.hash")).is_none() {
        env.add_decl(Declaration::Definition {
            name: Name::from_string("Hashable.hash"),
            level_params: vec![],
            type_: hash_accessor_ty,
            value: hash_accessor_val,
            is_reducible: true,
        })
        .expect("should add Hashable.hash accessor");
    }

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
    .expect("should add Color enum");
    env
}

#[test]
fn test_hashable2_nullary_enum_value_is_sorry_free() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("Hashable should succeed for nullary enum");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "nullary-enum Hashable instance value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // The genuine instance dispatches via the enum recursor and maps each
    // constructor to a distinct Nat (peano) hash under Hashable.mk.
    assert!(
        expr_mentions_const(&decls[0].value, "Color.rec"),
        "instance value should dispatch through the enum recursor Color.rec: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Hashable.mk"),
        "instance value should use Hashable.mk: {:?}",
        decls[0].value
    );
    // Hashes into Nat (not UInt64): the per-ctor minors are Nat peano numerals,
    // so Nat.zero appears and the fallback `sorry` does not.
    assert!(
        expr_mentions_const(&decls[0].value, "Nat.zero"),
        "per-ctor hashes should be Nat peano numerals (Nat.zero present): {:?}",
        decls[0].value
    );
    assert!(
        !expr_mentions_const(&decls[0].value, "UInt64"),
        "in-tree Hashable hashes into Nat, not UInt64: {:?}",
        decls[0].value
    );
}

#[test]
fn test_hashable2_single_nullary_ctor_value_is_sorry_free() {
    // A single nullary constructor maps to the hash `0` (Nat.zero), still
    // dispatched through the recursor.
    let handler = DeriveHashable2;
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
        .expect("Hashable should succeed for single nullary ctor");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "single nullary ctor Hashable value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Unit.rec"),
        "single-ctor instance should dispatch through Unit.rec: {:?}",
        decls[0].value
    );
}

#[test]
fn test_hashable2_struct_with_unresolvable_fields_fails_closed() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("Point");
    let result = handler.derive(
        &derive_env_with_opaque(),
        &tn,
        &type_expr(),
        &point_ctors_opaque(),
        0,
        &[],
    );
    assert_unsupported(result, "Hashable");
}

#[test]
fn test_hashable2_recursive_stays_rejected() {
    // Recursive constructors are rejected outright by reject_recursive, before
    // the nullary-enum construction is even attempted.
    let handler = DeriveHashable2;
    let tn = Name::from_string("Tree");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &recursive_ctors(), 0, &[]);
    assert!(
        result.is_err(),
        "recursive ctors must be rejected, not synthesized"
    );
}

#[test]
fn test_hashable2_empty_type_fails_closed() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("Void");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &empty_ctors(), 0, &[]);
    assert_unsupported(result, "Hashable");
}

#[test]
fn test_hashable2_parametric_enum_fails_closed() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("PColor");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 1, &[]);
    assert_unsupported(result, "Hashable");
}

#[test]
fn test_hashable2_nullary_enum_passes_strict_kernel_check() {
    let mut env = make_hashable_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("Color");

    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("Hashable should succeed for nullary enum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; this strict kernel type check proves
    // the concrete recursor / Nat-numeral term is accepted by the full kernel
    // checker (no sorryAx smuggling, correct universe levels, hash : α → Nat).
    let add_result = env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    });
    assert!(
        add_result.is_ok(),
        "derived Hashable instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived Hashable instance should be registered in the environment"
    );
}

#[test]
fn test_hashable2_nullary_enum_hashes_first_ctor_to_zero() {
    // The first constructor (Color.Red) must hash to 0 (Nat.zero). We build the
    // kernel-checked instance, then whnf-reduce `@Hashable.hash Color inst
    // Color.Red` and confirm it computes to the peano numeral 0.
    let mut env = make_hashable_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("Hashable should succeed for nullary enum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let color = Expr::const_(Name::from_string("Color"), vec![]);
    let red = Expr::const_(Name::from_string("Color.Red"), vec![]);
    let inst = Expr::const_(name.clone(), vec![]);
    // @Hashable.hash Color inst Color.Red : Nat
    let app = Expr::apps(
        Expr::const_(Name::from_string("Hashable.hash"), vec![Level::zero()]),
        [color, inst, red],
    );
    let reduced = TypeChecker::new(&env).whnf(&app);
    // The first ctor hashes to 0. `whnf` reduces through
    // Hashable.hash -> Hashable.rec -> Color.rec to the value; the kernel's
    // native Nat reducer may render it as either `Nat.zero` or the literal `0`.
    assert!(
        nat_value_is(&reduced, 0),
        "first ctor Color.Red must hash to 0, got: {reduced:?}"
    );
}

#[test]
fn test_hashable2_nullary_enum_hashes_second_ctor_to_one() {
    // The second constructor (Color.Blue) must hash to 1 (Nat.succ Nat.zero),
    // distinct from the first — the instance is collision-free over the nullary
    // constructors, not a constant stub.
    let mut env = make_hashable_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("Color");
    let decls = handler
        .derive(&derive_env(), &tn, &type_expr(), &color_ctors(), 0, &[])
        .expect("Hashable should succeed for nullary enum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let color = Expr::const_(Name::from_string("Color"), vec![]);
    let blue = Expr::const_(Name::from_string("Color.Blue"), vec![]);
    let inst = Expr::const_(name.clone(), vec![]);
    // @Hashable.hash Color inst Color.Blue : Nat
    let app = Expr::apps(
        Expr::const_(Name::from_string("Hashable.hash"), vec![Level::zero()]),
        [color, inst, blue],
    );
    let reduced = TypeChecker::new(&env).whnf(&app);
    // The second ctor hashes to 1, distinct from the first ctor's 0
    // (collision-free over nullary ctors). The kernel's native Nat reducer may
    // render it as either `Nat.succ Nat.zero` or the literal `1`.
    assert!(
        nat_value_is(&reduced, 1),
        "second ctor Color.Blue must hash to 1, got: {reduced:?}"
    );
}

// ---------------------------------------------------------------------------
// DeriveHashable2 single-ctor struct soundness tests
// (sorry-free Nat.add fold over per-field Hashable.hash projections; each field
// hash resolves the field type's own `Hashable` instance from the environment)
// ---------------------------------------------------------------------------

/// Install the in-tree-shaped `Hashable` class (`hash : α → Nat`) plus its
/// `Hashable.hash` projection accessor (via `Hashable.rec`) into `env`. Mirrors
/// the class/accessor setup in [`make_hashable_env`] without committing to a
/// particular value type, so it can be shared by both the nullary-enum and the
/// single-ctor struct fixtures.
fn install_hashable_class(env: &mut Environment) {
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");

    // Hashable : Type → Type with mk : {α : Type} → (α → Nat) → Hashable α.
    let hashable_name = Name::from_string("Hashable");
    let hashable_ty = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    let hash_field_ty = Expr::pi(BinderInfo::Default, Expr::bvar(0), nat.clone());
    let hashable_mk_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            hash_field_ty,
            Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    // `with_prelude` now bootstraps a real `Hashable` class with the same
    // `hash : α → Nat` shape (Task NN); only declare the stand-in when absent.
    if env.get_inductive(&hashable_name).is_none() {
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: hashable_name.clone(),
                type_: hashable_ty,
                constructors: vec![Constructor {
                    name: Name::from_string("Hashable.mk"),
                    type_: hashable_mk_ty,
                }],
            }],
        })
        .expect("should add Hashable class");
    }

    // Hashable.hash : {α : Type} → Hashable α → α → Nat (projects the field via
    // Hashable.rec — see make_hashable_env for the full derivation).
    let hash_accessor_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(0)),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), nat.clone()),
        ),
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(1)),
        Expr::pi(BinderInfo::Default, Expr::bvar(2), nat.clone()),
    );
    let minor = Expr::lam(
        BinderInfo::Default,
        Expr::pi(BinderInfo::Default, Expr::bvar(1), nat.clone()),
        Expr::bvar(0),
    );
    let rec_body = Expr::apps(
        Expr::const_(
            Name::from_string("Hashable.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::bvar(1), motive, minor, Expr::bvar(0)],
    );
    let hash_accessor_val = Expr::lam(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(Expr::const_(hashable_name.clone(), vec![]), Expr::bvar(0)),
            rec_body,
        ),
    );
    // `with_prelude` now provides `Hashable.hash`; only add the stand-in when
    // absent (Task NN idempotence).
    if env.get_const(&Name::from_string("Hashable.hash")).is_none() {
        env.add_decl(Declaration::Definition {
            name: Name::from_string("Hashable.hash"),
            level_params: vec![],
            type_: hash_accessor_ty,
            value: hash_accessor_val,
            is_reducible: true,
        })
        .expect("should add Hashable.hash accessor");
    }
}

/// Build a prelude environment with the `Hashable` class/accessor, a
/// `Hashable Nat` instance (`instHashableNat`, hashing every `Nat` to `0`), and
/// a single-ctor struct `Point.mk : Nat → Nat → Point`. The instance is
/// registered both as a kernel definition and as a class instance so the struct
/// handler can resolve each field's `Hashable Nat`. `Nat.add` (the genuine
/// combiner) and `Nat` come from the prelude; the kernel auto-generates
/// `Point.rec` and `Hashable.rec`, which the synthesized struct instance
/// dispatches through.
fn make_hashable_struct_env() -> Environment {
    let mut env = Environment::with_prelude();
    install_hashable_class(&mut env);
    let nat = Expr::const_str("Nat");

    // instHashableNat := @Hashable.mk Nat (fun (_ : Nat) => Nat.zero).
    let hashable_nat_ty = Expr::app(Expr::const_str("Hashable"), nat.clone());
    let hash_nat = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::const_str("Nat.zero"),
    );
    let hashable_nat_val = Expr::apps(Expr::const_str("Hashable.mk"), [nat.clone(), hash_nat]);
    // `with_prelude` now provides `instHashableNat`; only add the stand-in when
    // absent (Task NN idempotence).
    if env
        .get_const(&Name::from_string("instHashableNat"))
        .is_none()
    {
        env.add_decl(Declaration::Definition {
            name: Name::from_string("instHashableNat"),
            level_params: vec![],
            type_: hashable_nat_ty,
            value: hashable_nat_val,
            is_reducible: true,
        })
        .expect("should add instHashableNat");
        env.register_instance(clean_kernel::KernelInstanceInfo {
            name: Name::from_string("instHashableNat"),
            class_name: Name::from_string("Hashable"),
            priority: 100,
            type_: None,
            value: None,
        });
    }

    // Point.mk : Nat → Nat → Point.
    let type0 = Expr::sort(Level::succ(Level::zero()));
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
fn test_hashable2_struct_resolvable_fields_value_is_sorry_free() {
    // `Point.mk : Nat → Nat → Point` has fields whose `Hashable` instance the env
    // resolves (`instHashableNat`), so the handler folds per-field hashes via
    // `Nat.add`, with NO sorry and NO constant fallback.
    let env = make_hashable_struct_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("Point");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("Hashable should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "resolvable-field struct Hashable value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    // Fields are projected via the struct recursor, hashed via Hashable.hash, and
    // folded via the in-tree Nat.add combiner (Nat.mixHash is not an in-tree
    // const), reusing the field type's resolved instance.
    assert!(
        expr_mentions_const(&decls[0].value, "Point.rec"),
        "struct Hashable must project fields via the recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Hashable.hash"),
        "struct Hashable must hash fields via Hashable.hash: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Nat.add"),
        "struct Hashable must fold field hashes via Nat.add: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instHashableNat"),
        "struct Hashable must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
}

#[test]
fn test_hashable2_struct_resolvable_fields_passes_strict_kernel_check() {
    let mut env = make_hashable_struct_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("Point");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("Hashable should succeed for resolvable struct");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");

    // No-sorry guard proves genuineness; this strict kernel type check proves the
    // concrete field-projection / Hashable.hash / Nat.add term is accepted by the
    // full kernel checker (correct universe levels, no sorryAx smuggling).
    assert!(
        !expr_contains_sorry(&value),
        "struct Hashable value must be sorry-free before the kernel check: {value:?}"
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
        "derived struct Hashable instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived struct Hashable instance should be registered in the environment"
    );
}

#[test]
fn test_hashable2_struct_unresolvable_field_fails_closed() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("Opaque");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &unresolvable_field_ctor(),
        0,
        &[],
    );
    assert_unsupported(result, "Hashable");
}

#[test]
fn test_hashable2_struct_resolvable_fields_hashes_via_nat_add() {
    // The synthesized `hash (Point.mk a b)` reduces through the struct recursor:
    // each field hashes to 0 (instHashableNat), folded with Nat.add seeded at the
    // ctor index 0, so `Nat.add (Nat.add 0 0) 0` reduces to 0.
    let mut env = make_hashable_struct_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("Point");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &point_ctors(), 0, &[])
        .expect("Hashable should succeed for resolvable struct");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let point = Expr::const_(Name::from_string("Point"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    // Point.mk Nat.zero Nat.zero : Point.
    let pt = Expr::apps(
        Expr::const_(Name::from_string("Point.mk"), vec![]),
        [zero.clone(), zero],
    );
    let inst = Expr::const_(name.clone(), vec![]);
    // @Hashable.hash Point inst (Point.mk 0 0) : Nat.
    let app = Expr::apps(
        Expr::const_(Name::from_string("Hashable.hash"), vec![Level::zero()]),
        [point, inst, pt],
    );
    let reduced = TypeChecker::new(&env).whnf(&app);
    // Both fields hash to 0; Nat.add (Nat.add 0 0) 0 = 0. The kernel's native Nat
    // reducer may render this as `Nat.zero` or the literal `0`.
    assert!(
        nat_value_is(&reduced, 0),
        "Point.mk 0 0 must hash to 0, got: {reduced:?}"
    );
}

// ---------------------------------------------------------------------------
// DeriveRepr2 multi-ctor-with-fields soundness tests
// (single @T.rec dispatch rendering the matched ctor name + space-separated
// per-field reprPrec: >= 2 ctors, some/all carrying fields, np == 0,
// non-recursive — e.g. Either<Nat,Nat>, Result<Nat,Nat>, mixed nullary+field)
// ---------------------------------------------------------------------------

/// Add the in-tree-shaped `Repr` class, a `String.append` stand-in, and an
/// `instReprNat` instance (registered both as a kernel def and a class instance)
/// to `env`. Mirrors the `Repr`/`String.append`/`instReprNat` plumbing in
/// [`make_repr_struct_env`] without committing to a particular inductive, so the
/// multi-ctor fixtures can install their own sum types on top.
fn install_repr_class_and_nat(env: &mut Environment) {
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let string = Expr::const_str("String");

    // Repr : Type → Type with mk : {α : Type} → (α → Nat → String) → Repr α.
    let repr_name = Name::from_string("Repr");
    let repr_ty = Expr::pi(BinderInfo::Implicit, type0.clone(), type0.clone());
    let repr_prec_ty = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(BinderInfo::Default, nat.clone(), string.clone()),
    );
    let repr_mk_ty = Expr::pi(
        BinderInfo::Implicit,
        type0.clone(),
        Expr::pi(
            BinderInfo::Default,
            repr_prec_ty,
            Expr::app(Expr::const_(repr_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    // `with_prelude` now bootstraps a real `Repr` class with the same
    // `reprPrec : α → Nat → String` shape (Task NN). Only declare the test's
    // stand-in `Repr` when the prelude did not already provide one, so this
    // helper stays idempotent against the richer prelude.
    if env.get_inductive(&repr_name).is_none() {
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: repr_name,
                type_: repr_ty,
                constructors: vec![Constructor {
                    name: Name::from_string("Repr.mk"),
                    type_: repr_mk_ty,
                }],
            }],
        })
        .expect("should add Repr class");
    }

    // String.append stand-in `fun (a _b : String) => a`. The prelude now
    // declares a real `String.append`; only register the stand-in when the
    // constant is absent. See make_repr_struct_env.
    if env.get_const(&Name::from_string("String.append")).is_none() {
        let append_ty = Expr::pi(
            BinderInfo::Default,
            string.clone(),
            Expr::pi(BinderInfo::Default, string.clone(), string.clone()),
        );
        let append_val = Expr::lam(
            BinderInfo::Default,
            string.clone(),
            Expr::lam(BinderInfo::Default, string.clone(), Expr::bvar(1)),
        );
        env.add_decl(Declaration::Definition {
            name: Name::from_string("String.append"),
            level_params: vec![],
            type_: append_ty,
            value: append_val,
            is_reducible: true,
        })
        .expect("should add String.append stand-in");
    }

    // instReprNat := @Repr.mk Nat (fun (_ : Nat) (_ : Nat) => "Nat").
    let repr_nat_ty = Expr::app(Expr::const_str("Repr"), nat.clone());
    let repr_prec = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::str_lit("Nat")),
    );
    let repr_nat_val = Expr::apps(Expr::const_str("Repr.mk"), [nat, repr_prec]);
    // `with_prelude` now provides `instReprNat`; only add the test stand-in when
    // it is absent (Task NN idempotence).
    if env.get_const(&Name::from_string("instReprNat")).is_none() {
        env.add_decl(Declaration::Definition {
            name: Name::from_string("instReprNat"),
            level_params: vec![],
            type_: repr_nat_ty,
            value: repr_nat_val,
            is_reducible: true,
        })
        .expect("should add instReprNat");
        env.register_instance(clean_kernel::KernelInstanceInfo {
            name: Name::from_string("instReprNat"),
            class_name: Name::from_string("Repr"),
            priority: 100,
            type_: None,
            value: None,
        });
    }
}

/// Add a monomorphic `Either<Nat,Nat>` sum `ENat` (`ENat.left : Nat → ENat`,
/// `ENat.right : Nat → ENat`) to `env`. The kernel auto-generates `ENat.rec`.
fn add_enat_sum(env: &mut Environment) {
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let ename = Name::from_string("ENat");
    let field_to_e = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::const_(ename.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ename.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("ENat.left"),
                    type_: field_to_e.clone(),
                },
                Constructor {
                    name: Name::from_string("ENat.right"),
                    type_: field_to_e,
                },
            ],
        }],
    })
    .expect("should add ENat (Either Nat Nat) sum");
}

/// Add a mixed `Maybe<Nat>` sum `MNat` (`MNat.none : MNat`, `MNat.some : Nat →
/// MNat`) to `env`, exercising a 0-field arm alongside a field-carrying arm.
fn add_mnat_sum(env: &mut Environment) {
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let mname = Name::from_string("MNat");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: mname.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MNat.none"),
                    type_: Expr::const_(mname.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("MNat.some"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        nat,
                        Expr::const_(mname.clone(), vec![]),
                    ),
                },
            ],
        }],
    })
    .expect("should add MNat (Maybe Nat) sum");
}

/// Prelude + `Repr` class/`String.append`/`instReprNat` + `ENat` sum.
fn make_repr_multi_ctor_env() -> Environment {
    let mut env = Environment::with_prelude();
    install_repr_class_and_nat(&mut env);
    add_enat_sum(&mut env);
    env
}

#[test]
fn test_repr2_multi_ctor_fields_value_is_sorry_free() {
    // `Either<Nat,Nat>` (ENat.left : Nat → ENat, ENat.right : Nat → ENat) has
    // fields whose `Repr` instance the env resolves (instReprNat), so the handler
    // renders each arm's ctor name + per-field reprPrec via a single recursor
    // dispatch, with NO sorry and NO constant fallback.
    let env = make_repr_multi_ctor_env();
    let handler = DeriveRepr2;
    let tn = Name::from_string("ENat");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_nat_ctors(), 0, &[])
        .expect("Repr should succeed for multi-ctor sum with resolvable fields");
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instReprENat");
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "multi-ctor-with-fields Repr value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "ENat.rec"),
        "multi-ctor Repr must dispatch through the recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Repr.rec"),
        "multi-ctor Repr must extract each field's reprPrec via the Repr recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "String.append"),
        "multi-ctor Repr must concatenate rendered parts via String.append: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instReprNat"),
        "multi-ctor Repr must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
}

#[test]
fn test_repr2_multi_ctor_fields_passes_strict_kernel_check() {
    let mut env = make_repr_multi_ctor_env();
    let handler = DeriveRepr2;
    let tn = Name::from_string("ENat");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_nat_ctors(), 0, &[])
        .expect("Repr should succeed for multi-ctor sum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "multi-ctor Repr value must be sorry-free before the kernel check: {value:?}"
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
        "derived multi-ctor Repr instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived multi-ctor Repr instance should be registered in the environment"
    );
}

#[test]
fn test_repr2_result_nat_multi_ctor_fields_passes_strict_kernel_check() {
    // Result<Nat,Nat> as a second monomorphic multi-ctor sum (RNat.ok : Nat →
    // RNat, RNat.err : Nat → RNat); confirms the construction is not specific to
    // the Either naming and kernel-checks.
    let mut env = Environment::with_prelude();
    install_repr_class_and_nat(&mut env);
    let type0 = Expr::sort(Level::succ(Level::zero()));
    let nat = Expr::const_str("Nat");
    let rname = Name::from_string("RNat");
    let field_to_r = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::const_(rname.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: rname.clone(),
            type_: type0,
            constructors: vec![
                Constructor {
                    name: Name::from_string("RNat.ok"),
                    type_: field_to_r.clone(),
                },
                Constructor {
                    name: Name::from_string("RNat.err"),
                    type_: field_to_r,
                },
            ],
        }],
    })
    .expect("should add RNat (Result Nat Nat) sum");

    let handler = DeriveRepr2;
    let decls = handler
        .derive(&env, &rname, &type_expr(), &result_nat_ctors(), 0, &[])
        .expect("Repr should succeed for Result<Nat,Nat> sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "Result Repr value must be sorry-free: {value:?}"
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
        "derived Result Repr instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
}

#[test]
fn test_repr2_mixed_nullary_and_field_ctor_passes_strict_kernel_check() {
    // A mixed sum (one 0-field ctor, one field-carrying ctor): the 0-field arm
    // renders just the ctor name, the field-carrying arm renders name + one
    // reprPrec. Both must kernel-check under the single recursor dispatch.
    let mut env = Environment::with_prelude();
    install_repr_class_and_nat(&mut env);
    add_mnat_sum(&mut env);

    let handler = DeriveRepr2;
    let mname = Name::from_string("MNat");
    let decls = handler
        .derive(&env, &mname, &type_expr(), &maybe_nat_ctors(), 0, &[])
        .expect("Repr should succeed for mixed nullary/field sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "mixed-sum Repr value must be sorry-free: {value:?}"
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
        "derived mixed-sum Repr instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
}

#[test]
fn test_repr2_multi_ctor_fields_unresolvable_field_fails_closed() {
    let nat = Expr::const_str("Nat");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("Mix.a"),
            fields: vec![(Name::from_string("x"), nat)],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("Mix.b"),
            fields: vec![(Name::from_string("w"), Expr::const_str("Widget"))],
            is_recursive: false,
        },
    ];
    let handler = DeriveRepr2;
    let tn = Name::from_string("Mix");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert_unsupported(result, "Repr");
}

#[test]
fn test_repr2_multi_ctor_fields_recursive_fails_closed() {
    let nat = Expr::const_str("Nat");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("RList.nil"),
            fields: vec![],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("RList.cons"),
            fields: vec![
                (Name::from_string("head"), nat),
                (Name::from_string("tail"), Expr::const_str("RList")),
            ],
            is_recursive: true,
        },
    ];
    let handler = DeriveRepr2;
    let tn = Name::from_string("RList");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert_unsupported(result, "Repr");
}

#[test]
fn test_repr2_multi_ctor_fields_parametric_fails_closed() {
    let handler = DeriveRepr2;
    let tn = Name::from_string("PEither");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &either_nat_ctors(),
        1,
        &[],
    );
    assert_unsupported(result, "Repr");
}

// ---------------------------------------------------------------------------
// DeriveHashable2 multi-ctor-with-fields soundness tests
// (single @T.rec dispatch seeding each arm with its ctor index then mixing
// per-field Hashable.hash via Nat.add: >= 2 ctors, some/all carrying fields,
// np == 0, non-recursive — e.g. Either<Nat,Nat>, mixed nullary+field)
// ---------------------------------------------------------------------------

/// Add an `instHashableNat` instance (hashing every `Nat` to `0`), registered
/// both as a kernel def and a class instance, to `env`. Assumes the `Hashable`
/// class/accessor is already installed (via [`install_hashable_class`]).
fn install_hashable_nat(env: &mut Environment) {
    let nat = Expr::const_str("Nat");
    let hashable_nat_ty = Expr::app(Expr::const_str("Hashable"), nat.clone());
    let hash_nat = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::const_str("Nat.zero"),
    );
    let hashable_nat_val = Expr::apps(Expr::const_str("Hashable.mk"), [nat, hash_nat]);
    // `with_prelude` now provides `instHashableNat`; only add the stand-in when
    // absent (Task NN idempotence).
    if env
        .get_const(&Name::from_string("instHashableNat"))
        .is_none()
    {
        env.add_decl(Declaration::Definition {
            name: Name::from_string("instHashableNat"),
            level_params: vec![],
            type_: hashable_nat_ty,
            value: hashable_nat_val,
            is_reducible: true,
        })
        .expect("should add instHashableNat");
        env.register_instance(clean_kernel::KernelInstanceInfo {
            name: Name::from_string("instHashableNat"),
            class_name: Name::from_string("Hashable"),
            priority: 100,
            type_: None,
            value: None,
        });
    }
}

/// Prelude + `Hashable` class/accessor + `instHashableNat` + `ENat` sum.
fn make_hashable_multi_ctor_env() -> Environment {
    let mut env = Environment::with_prelude();
    install_hashable_class(&mut env);
    install_hashable_nat(&mut env);
    add_enat_sum(&mut env);
    env
}

#[test]
fn test_hashable2_multi_ctor_fields_value_is_sorry_free() {
    // `Either<Nat,Nat>` has fields whose `Hashable` instance the env resolves
    // (instHashableNat), so the handler seeds each arm with its ctor index then
    // folds per-field hashes via Nat.add through a single recursor dispatch, with
    // NO sorry and NO honest fallback.
    let env = make_hashable_multi_ctor_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("ENat");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_nat_ctors(), 0, &[])
        .expect("Hashable should succeed for multi-ctor sum with resolvable fields");
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instHashableENat");
    assert!(
        !expr_contains_sorry(&decls[0].value),
        "multi-ctor-with-fields Hashable value must contain NO sorry/sorryAx: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "ENat.rec"),
        "multi-ctor Hashable must dispatch through the recursor: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Hashable.hash"),
        "multi-ctor Hashable must hash fields via Hashable.hash: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "Nat.add"),
        "multi-ctor Hashable must fold field hashes via Nat.add: {:?}",
        decls[0].value
    );
    assert!(
        expr_mentions_const(&decls[0].value, "instHashableNat"),
        "multi-ctor Hashable must reuse the field type's resolved instance: {:?}",
        decls[0].value
    );
}

#[test]
fn test_hashable2_multi_ctor_fields_passes_strict_kernel_check() {
    let mut env = make_hashable_multi_ctor_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("ENat");

    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_nat_ctors(), 0, &[])
        .expect("Hashable should succeed for multi-ctor sum");
    assert_eq!(decls.len(), 1);

    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "multi-ctor Hashable value must be sorry-free before the kernel check: {value:?}"
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
        "derived multi-ctor Hashable instance must pass strict kernel type check: {:?}",
        add_result.err()
    );
    assert!(
        env.get_const(&name).is_some(),
        "derived multi-ctor Hashable instance should be registered in the environment"
    );
}

/// Build the kernel-checked `instHashableENat`, then whnf-reduce
/// `@Hashable.hash ENat inst <value>` and return its `Nat` value (peano or
/// native literal accepted via [`nat_value_is`] at the call site).
fn hashable_enat_reduce(value: Expr) -> Expr {
    let mut env = make_hashable_multi_ctor_env();
    let handler = DeriveHashable2;
    let tn = Name::from_string("ENat");
    let decls = handler
        .derive(&env, &tn, &type_expr(), &either_nat_ctors(), 0, &[])
        .expect("Hashable should succeed for multi-ctor sum");
    let DerivedDecl2 {
        name,
        type_,
        value: inst_val,
        ..
    } = decls.into_iter().next().expect("one decl");
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_,
        value: inst_val,
        is_reducible: true,
    })
    .expect("instance should kernel-check");

    let enat = Expr::const_(Name::from_string("ENat"), vec![]);
    let inst = Expr::const_(name, vec![]);
    let app = Expr::apps(
        Expr::const_(Name::from_string("Hashable.hash"), vec![Level::zero()]),
        [enat, inst, value],
    );
    let tc = TypeChecker::new(&env);
    tc.whnf(&app)
}

#[test]
fn test_hashable2_multi_ctor_fields_distinct_ctors_hash_differently() {
    // The prelude `instHashableNat` is the identity (`hash n = n`, Task NN), so
    // the per-field hash contributes the payload value, and the hash is
    // `Nat.add <ctorIndex> <fieldValue>`. The first ctor (ENat.left, index 0)
    // hashes `left 7` to `0 + 7 = 7`; the second (ENat.right, index 1) hashes
    // `right 7` to `1 + 7 = 8` — distinct, proving the instance is not a
    // constant stub and that the ctor index seed shifts the result.
    let left = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("ENat.left"), vec![]),
            Expr::nat_lit(n),
        )
    };
    let right = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("ENat.right"), vec![]),
            Expr::nat_lit(n),
        )
    };
    let left_hash = hashable_enat_reduce(left(7));
    let right_hash = hashable_enat_reduce(right(7));
    assert!(
        nat_value_is(&left_hash, 7),
        "ENat.left (index 0) must hash to 7 (Nat.add 0 (hash 7 = 7)), got: {left_hash:?}"
    );
    assert!(
        nat_value_is(&right_hash, 8),
        "ENat.right (index 1) must hash to 8 (Nat.add 1 (hash 7 = 7)), got: {right_hash:?}"
    );
}

#[test]
fn test_hashable2_mixed_nullary_and_field_ctor_passes_strict_kernel_check() {
    // A mixed sum (one 0-field ctor, one field-carrying ctor): the 0-field arm
    // hashes to just its index, the field-carrying arm folds one Hashable.hash
    // into the index seed. none (index 0) -> 0, some 0 (index 1) -> 1.
    let mut env = Environment::with_prelude();
    install_hashable_class(&mut env);
    install_hashable_nat(&mut env);
    add_mnat_sum(&mut env);

    let handler = DeriveHashable2;
    let mname = Name::from_string("MNat");
    let decls = handler
        .derive(&env, &mname, &type_expr(), &maybe_nat_ctors(), 0, &[])
        .expect("Hashable should succeed for mixed nullary/field sum");
    let DerivedDecl2 {
        name, type_, value, ..
    } = decls.into_iter().next().expect("one decl");
    assert!(
        !expr_contains_sorry(&value),
        "mixed-sum Hashable value must be sorry-free: {value:?}"
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
        "derived mixed-sum Hashable instance must pass strict kernel type check: {:?}",
        add_result.err()
    );

    // none (index 0) hashes to 0; some 0 (index 1, field hash 0) hashes to 1.
    let none = Expr::const_(Name::from_string("MNat.none"), vec![]);
    let some0 = Expr::app(
        Expr::const_(Name::from_string("MNat.some"), vec![]),
        Expr::nat_lit(0),
    );
    let inst = Expr::const_(name, vec![]);
    let mnat = Expr::const_(mname, vec![]);
    let hash = |v: Expr| {
        let app = Expr::apps(
            Expr::const_(Name::from_string("Hashable.hash"), vec![Level::zero()]),
            [mnat.clone(), inst.clone(), v],
        );
        TypeChecker::new(&env).whnf(&app)
    };
    let none_hash = hash(none);
    let some_hash = hash(some0);
    assert!(
        nat_value_is(&none_hash, 0),
        "MNat.none (0-field arm, index 0) must hash to 0, got: {none_hash:?}"
    );
    assert!(
        nat_value_is(&some_hash, 1),
        "MNat.some 0 (index 1 + field hash 0) must hash to 1, got: {some_hash:?}"
    );
}

#[test]
fn test_hashable2_multi_ctor_fields_unresolvable_field_fails_closed() {
    let nat = Expr::const_str("Nat");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("Mix.a"),
            fields: vec![(Name::from_string("x"), nat)],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("Mix.b"),
            fields: vec![(Name::from_string("w"), Expr::const_str("Widget"))],
            is_recursive: false,
        },
    ];
    let handler = DeriveHashable2;
    let tn = Name::from_string("Mix");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert_unsupported(result, "Hashable");
}

#[test]
fn test_hashable2_multi_ctor_fields_recursive_stays_rejected() {
    // A multi-ctor sum with a recursive constructor is rejected outright by
    // reject_recursive, before the multi-ctor construction is attempted.
    let nat = Expr::const_str("Nat");
    let ctors = vec![
        CtorInfo2 {
            name: Name::from_string("RList.nil"),
            fields: vec![],
            is_recursive: false,
        },
        CtorInfo2 {
            name: Name::from_string("RList.cons"),
            fields: vec![
                (Name::from_string("head"), nat),
                (Name::from_string("tail"), Expr::const_str("RList")),
            ],
            is_recursive: true,
        },
    ];
    let handler = DeriveHashable2;
    let tn = Name::from_string("RList");
    let result = handler.derive(&derive_env(), &tn, &type_expr(), &ctors, 0, &[]);
    assert!(
        result.is_err(),
        "recursive multi-ctor sum must be rejected, not synthesized"
    );
}

#[test]
fn test_hashable2_multi_ctor_fields_parametric_fails_closed() {
    let handler = DeriveHashable2;
    let tn = Name::from_string("PEither");
    let result = handler.derive(
        &derive_env(),
        &tn,
        &type_expr(),
        &either_nat_ctors(),
        1,
        &[],
    );
    assert_unsupported(result, "Hashable");
}
