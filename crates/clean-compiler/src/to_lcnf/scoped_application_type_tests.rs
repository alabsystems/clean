// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Open application types come from checked declarations and active binders.

use super::lower::expr_to_let_value;
use super::scoped_application_type::infer_scoped_const_application;
use super::LcnfContext;
use crate::lcnf::LetValue;
use crate::rc_repair::e2e_support::elaborated_env_with;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, ExprKind, Level, Name};

fn scalar_env() -> Environment {
    elaborated_env_with("")
}

fn bit_app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

#[test]
fn open_application_nested_mask_keeps_each_actual_scalar_result() {
    let env = scalar_env();
    let mut ctx = LcnfContext::new(&env);
    let u = Expr::const_str("UInt32");
    ctx.push_typed_binder(&u);
    ctx.push_typed_binder(&u);
    let inner = bit_app("UInt32.land", [Expr::bvar(1), Expr::bvar(0)]);
    let expr = bit_app("UInt32.lor", [inner, Expr::bvar(1)]);
    assert_eq!(infer_scoped_const_application(&ctx, &expr), Some(u.clone()));
    let (_, result) = expr_to_let_value(&mut ctx, &expr).expect("the actual LCNF funnel");
    assert_eq!(result, u);
    let bindings = ctx.take_lets();
    let inner = bindings
        .iter()
        .find(|decl| {
            matches!(&decl.value, LetValue::Const { name, .. } if *name == Name::from_string("UInt32.land"))
        })
        .expect("nested land must be bound, not skipped");
    assert_eq!(inner.ty, Expr::const_str("UInt32"));
}

fn dependent_env() -> Environment {
    let mut env = Environment::default();
    let universe = Name::from_string("u");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("scopedId"),
        level_params: vec![universe.clone()],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::param(universe)),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
    })
    .expect("the polymorphic dependent declaration kernel-checks");
    env
}

#[test]
fn open_application_instantiates_universes_and_dependent_binders_without_capture() {
    let env = dependent_env();
    let mut ctx = LcnfContext::new(&env);
    let original = ctx.push_typed_binder(&Expr::type_());
    ctx.push_typed_binder(&Expr::type_());
    ctx.push_typed_binder(&Expr::bvar(1));
    let expr = Expr::apps(
        Expr::const_(
            Name::from_string("scopedId"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::bvar(2), Expr::bvar(0)],
    );
    assert_eq!(
        infer_scoped_const_application(&ctx, &expr),
        Some(Expr::fvar(original))
    );
    let wrong_levels = Expr::apps(Expr::const_str("scopedId"), [Expr::bvar(2), Expr::bvar(0)]);
    assert!(infer_scoped_const_application(&ctx, &wrong_levels).is_none());
}

#[test]
fn open_application_refuses_partial_oversaturated_and_unknown_spines() {
    let env = scalar_env();
    let mut ctx = LcnfContext::new(&env);
    ctx.push_typed_binder(&Expr::const_str("UInt32"));
    for expr in [
        bit_app("UInt32.land", [Expr::bvar(0)]),
        bit_app("UInt32.land", [Expr::bvar(0), Expr::bvar(0), Expr::bvar(0)]),
        bit_app("notDeclared.land", [Expr::bvar(0), Expr::bvar(0)]),
        bit_app("UInt32.land", [Expr::bvar(99), Expr::bvar(0)]),
    ] {
        assert!(
            infer_scoped_const_application(&ctx, &expr).is_none(),
            "{expr:?}"
        );
        let result = expr_to_let_value(&mut ctx, &expr);
        match result {
            Ok((_, ty)) => assert!(
                matches!(ty.kind(), ExprKind::Const(name, _) if *name == Name::from_string("_"))
            ),
            Err(_) => assert!(expr.has_loose_bvar(99)),
        }
    }
}

#[test]
fn open_application_checks_argument_types_instead_of_infer_only_guessing() {
    let env = scalar_env();
    let mut ctx = LcnfContext::new(&env);
    ctx.push_typed_binder(&Expr::const_str("String"));
    ctx.push_typed_binder(&Expr::const_str("UInt32"));
    let expr = bit_app("UInt32.land", [Expr::bvar(1), Expr::bvar(0)]);
    assert!(infer_scoped_const_application(&ctx, &expr).is_none());
    let (_, ty) = expr_to_let_value(&mut ctx, &expr).expect("typing refusal remains a placeholder");
    assert!(matches!(ty.kind(), ExprKind::Const(name, _) if *name == Name::from_string("_")));
}

#[test]
fn open_application_does_not_resurrect_popped_or_untyped_local_types() {
    let env = scalar_env();
    let mut ctx = LcnfContext::new(&env);
    let old = ctx.push_typed_binder(&Expr::const_str("UInt32"));
    ctx.pop_binder();
    ctx.push_typed_binder(&Expr::const_str("UInt32"));
    let stale = bit_app("UInt32.land", [Expr::fvar(old), Expr::bvar(0)]);
    assert!(
        ctx.local_type(old).is_some(),
        "exercise the retained old type"
    );
    assert!(infer_scoped_const_application(&ctx, &stale).is_none());
    ctx.push_binder();
    let missing = bit_app("UInt32.land", [Expr::bvar(1), Expr::bvar(1)]);
    assert!(infer_scoped_const_application(&ctx, &missing).is_none());
}
