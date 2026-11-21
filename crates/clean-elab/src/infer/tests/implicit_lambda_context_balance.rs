// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A FAILED implicit-lambda wrap must leave the local context as it found it.
//!
//! `elab_implicit_lambda` introduces one local per leading non-explicit binder
//! of the expected type before elaborating the term against what remains. An
//! application path can recover from elaboration failure and reuse the same
//! `ElabCtx` — so a local left on the stack, or worse a local
//! INSTANCE left on the instance stack, would be visible to whatever runs next
//! and could make an unrelated goal resolve or a later `abstract_fvar` rewrite
//! the wrong variable.
//!
//! The per-binder code this module's subject replaced popped before
//! propagating (`elab_core.rs`, `pop_local()` above `let inner = inner_result?`);
//! the first port of it abstracted and popped in one step AFTER `?`, so the
//! error path never popped at all.

use super::*;

/// `Nat`, and `P : Nat → Prop`, with nothing that could resolve the term below.
fn env_with_predicate() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("Nat axiom must register");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::prop(),
        ),
    })
    .expect("P axiom must register");
    env
}

/// `{α : Type} → {x : Nat} → P x` — two leading implicit binders, so a leak
/// shows as a count of two rather than one.
fn two_implicit_binders() -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let p_of_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));
    Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(BinderInfo::Implicit, nat, p_of_x),
    )
}

#[test]
fn test_failed_implicit_lambda_wrap_leaves_the_local_context_balanced() {
    let env = env_with_predicate();
    let mut ctx = ElabCtx::new(&env);
    let locals_before = ctx.locals.len();
    let instances_before = ctx.local_instances.len();

    // An ordinary identifier triggers the wrap (Lean's `blockImplicitLambda`
    // blocks `@`, holes, `by`, ascriptions and `fun {…}` — not an ident), and
    // this one resolves to nothing, so the elaboration inside the wrap fails.
    let term = parse_expr("thisNameResolvesToNothing").expect("fixture must parse");
    let err = ctx
        .elaborate_with_expected_type(&term, Some(two_implicit_binders()))
        .expect_err("an unresolvable identifier must fail inside the wrap");
    let msg = format!("{err}");
    assert!(
        msg.contains("thisNameResolvesToNothing"),
        "the failure must be the INNER elaboration's, not the wrap's: {msg}"
    );

    assert_eq!(
        ctx.locals.len(),
        locals_before,
        "a failed implicit-lambda wrap left {} local(s) on the stack",
        ctx.locals.len() - locals_before
    );
    assert_eq!(
        ctx.local_instances.len(),
        instances_before,
        "a failed implicit-lambda wrap left a local instance on the stack"
    );
}

#[test]
fn test_successful_implicit_lambda_wrap_leaves_the_local_context_balanced() {
    // The control: the balanced-on-success half was always true, and it must
    // stay true, or the assertion above would pass vacuously on a wrap that
    // never opened a binder.
    let mut env = env_with_predicate();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let p_of_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("anyP"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Implicit, nat, p_of_x),
    })
    .expect("anyP axiom must register");

    let mut ctx = ElabCtx::new(&env);
    let locals_before = ctx.locals.len();
    let term = parse_expr("anyP").expect("fixture must parse");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let p_of_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));
    let expected = Expr::pi(BinderInfo::Implicit, nat, p_of_x);
    let built = ctx
        .elaborate_with_expected_type(&term, Some(expected))
        .expect("`anyP` against `{x : Nat} → P x` must elaborate");
    assert!(
        matches!(built.kind(), ExprKind::Lam(..)),
        "the wrap must have produced a lambda, or this test's subject was never reached: {built:?}"
    );
    assert_eq!(
        ctx.locals.len(),
        locals_before,
        "a successful implicit-lambda wrap must also balance the local context"
    );
}
