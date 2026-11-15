// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for grind's funext bridge: Prop-valued function equalities
//! reaching the propositional closure, and the pi-arity guard that keeps
//! non-Prop function equalities untouched.
//!
//! Split from grind_tests.rs for file size; same imports.

use super::super::grind::grind;
use super::*;
use clean_kernel::level::Level;
use clean_kernel::name::Name;

// ============================================================================
// funext + propext bridge (Prop-valued function equalities)
// ============================================================================

/// `@Eq.{1} ty lhs rhs` — every type in these tests lives in `Sort 1`
/// (`Prop → … → Prop` and `A → A` with `A : Type` both do).
fn mk_eq1(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

#[test]
fn test_pi_arity_into_prop_accepts_only_prop_codomain_chains() {
    let prop = Expr::prop();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop_to_prop = Expr::arrow(prop.clone(), prop.clone());
    let nat_prop_prop = Expr::arrow(nat.clone(), Expr::arrow(prop.clone(), prop.clone()));
    let nat_to_nat = Expr::arrow(nat.clone(), nat);
    let prop_to_type = Expr::arrow(prop.clone(), Expr::type_());

    // Bare Prop: the plain propext bridge's goal, not this one's.
    assert_eq!(pi_arity_into_prop(&prop), None);
    // Chains ending in Prop, homogeneous and mixed-domain.
    assert_eq!(pi_arity_into_prop(&prop_to_prop), Some(1));
    assert_eq!(pi_arity_into_prop(&nat_prop_prop), Some(2));
    // Non-Prop codomains must not trigger the bridge.
    assert_eq!(pi_arity_into_prop(&nat_to_nat), None);
    assert_eq!(pi_arity_into_prop(&prop_to_type), None);
}

/// The bridge itself must rewrite `@Eq (Prop → Prop) f g` into a pointwise
/// `Iff` goal with the binder intro'd — pinned separately from full `grind`
/// closure so a future closer learning the raw `Eq` shape cannot mask a
/// bridge regression. `f`/`g` are unprovably-distinct axioms: only the
/// TRANSFORMATION is asserted here, closure is a later phase's job.
#[test]
fn test_grind_funext_bridge_rewrites_to_pointwise_iff() {
    use clean_kernel::env::{Declaration, Environment};

    let mut env = Environment::with_prelude();
    env.init_funext().expect("funext registers on the prelude");
    env.init_propext()
        .expect("propext registers on the prelude");

    let prop_to_prop = Expr::arrow(Expr::prop(), Expr::prop());
    for name in ["f", "g"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop_to_prop.clone(),
        })
        .expect("Prop-valued function axiom registers");
    }

    let target = mk_eq1(
        prop_to_prop,
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("g"), vec![]),
    );
    let mut state = ProofState::new(env, target);

    try_funext_propext_bridge(&mut state)
        .expect("bridge should fire on a Prop-valued function equality");

    let goal = state
        .current_goal()
        .expect("bridge must leave the pointwise goal open")
        .clone();
    let pointwise = state.metas.instantiate(&goal.target);
    assert!(
        matches!(pointwise.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "Iff"),
        "bridge must hand the closer fan a pointwise Iff, got {pointwise:?}"
    );
    assert!(
        goal.local_ctx
            .iter()
            .any(|d| d.name.name() == &Name::anon().str("x_grind_funext").num(0)),
        "bridge must intro the pointwise binder"
    );
}

/// `(fun p q : Prop => p ∧ q) = (fun p q : Prop => q ∧ p)` — measured on the
/// release binary 2026-08-21 (prelude env): `grind` alone failed with
/// NoProgress while `funext p; funext q; apply propext; tauto` closed it.
/// The bridge folds that hand route into preprocessing (including the
/// multi-binder loop), so `grind` must close it and the proof must
/// kernel-check. This is the unit-level control for the Logic/Basic
/// `xor_false` / `xor_true` targets.
#[test]
fn test_grind_funext_bridge_closes_prop_valued_fun_equality() {
    use clean_kernel::env::Environment;
    use clean_kernel::{BinderInfo, TypeChecker};

    let mut env = Environment::with_prelude();
    env.init_funext().expect("funext registers on the prelude");
    env.init_propext()
        .expect("propext registers on the prelude");

    let prop = Expr::prop();
    let and_ = Expr::const_(Name::from_string("And"), vec![]);
    let lam2 = |body: Expr| {
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::prop(), body),
        )
    };
    // fun (p q : Prop) => p ∧ q   /   fun (p q : Prop) => q ∧ p
    let and_pq = Expr::app(Expr::app(and_.clone(), Expr::bvar(1)), Expr::bvar(0));
    let and_qp = Expr::app(Expr::app(and_, Expr::bvar(0)), Expr::bvar(1));
    let lhs = lam2(and_pq);
    let rhs = lam2(and_qp);
    let fn_ty = Expr::arrow(prop.clone(), Expr::arrow(prop.clone(), prop));
    let target = mk_eq1(fn_ty, lhs, rhs);

    let mut state = ProofState::new(env.clone(), target.clone());
    grind(&mut state)
        .expect("grind should close an ∧-comm function equality via the funext bridge");
    assert!(state.is_complete(), "grind success must close the goal");

    let proof = state
        .closed_proof()
        .expect("bridged proof must close (not ProofNotProduced)");
    TypeChecker::new(&env)
        .check_type(&proof, &target)
        .expect("kernel must re-check the bridged funext+propext proof term");
}

/// Guard: a NON-Prop-valued function equality (`f = g` with `f g : A → A`)
/// must not trigger the bridge — no funext application, error out, goal
/// bit-identical.
#[test]
fn test_grind_funext_bridge_leaves_non_prop_fun_equality_untouched() {
    use clean_kernel::env::{Declaration, Environment};

    let mut env = Environment::new();
    env.init_eq().expect("Eq registers");
    env.init_funext().expect("funext registers");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("A registers");
    let a = Expr::const_(Name::from_string("A"), vec![]);
    for name in ["f", "g"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::arrow(a.clone(), a.clone()),
        })
        .expect("function axiom registers");
    }

    let target = mk_eq1(
        Expr::arrow(a.clone(), a),
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("g"), vec![]),
    );
    let mut state = ProofState::new(env, target.clone());

    let result = try_funext_propext_bridge(&mut state);
    assert!(
        matches!(&result, Err(TacticError::NoProgress { tactic, .. }) if tactic == "grind/funext"),
        "non-Prop codomain must not trigger the funext bridge, got {result:?}"
    );

    let goal = state
        .current_goal()
        .expect("goal must survive the no-op")
        .clone();
    assert_eq!(
        format!("{:?}", state.metas.instantiate(&goal.target)),
        format!("{target:?}"),
        "guard must leave a non-Prop function equality untouched"
    );
    assert!(
        goal.local_ctx.is_empty(),
        "guard must not intro any pointwise binder"
    );
}
