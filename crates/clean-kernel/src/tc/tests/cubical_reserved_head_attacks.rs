// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ATTACKS on the cubical layer's name-keyed rules
//! (`docs/issues/2026-09-26-kernel-native-fold-by-name.md`). The Σ-iota and
//! the `Equiv.fwd` projection (`tc/reduction/kan.rs`) match `Sigma.elim` /
//! `Sigma.mk` and `Equiv.fwd` / `Equiv.mk` by NAME. They are justified by the
//! kernel's own axioms for those names and by nothing else, yet they fired for
//! whatever the environment declared: a user `Sigma.elim := fun … => a0`
//! computed `a1` at a `Sigma.mk`, beside its own δ answer `a0` — two opaque
//! points identified. Each attack was ACCEPTED before the cubical authority
//! gate (`tc/cubical_authority.rs`); each has a positive control showing the
//! kernel's own axioms still compute.
//!
//! Written against the kernel's public surface plus the registrars, so the
//! same file compiles on the pre-authority kernel (the RED half).

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;
use crate::tc::reduction::kan::{
    register_glue_axioms, register_kan_system_axioms, register_sigma_axioms,
};
use crate::tc::TypeChecker;
use std::sync::Arc;

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::<Level>::new())
}

fn arrows(n: usize) -> Expr {
    (0..n).fold(cst("A"), |acc, _| Expr::arrow(cst("A"), acc))
}

fn lams(n: usize, body: Expr) -> Expr {
    (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, cst("A"), acc))
}

/// `Path (λ _ : I. A) left right`.
fn path_ty(left: Expr, right: Expr) -> Expr {
    let family = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        cst("A"),
    );
    Expr::from_kind(ExprKind::CubicalPath {
        ty: Arc::new(family),
        left: Arc::new(left),
        right: Arc::new(right),
    })
}

/// `<i> a` — the constant path.
fn refl(a: Expr) -> Expr {
    Expr::from_kind(ExprKind::CubicalPathLam { body: Arc::new(a) })
}

/// A Cubical environment with `A : Type` and two opaque points `a0 a1 : A`.
fn points_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    for (name, ty) in [("A", Expr::type_()), ("a0", cst("A")), ("a1", cst("A"))] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .unwrap_or_else(|e| panic!("{name} should register: {e:?}"));
    }
    env
}

fn user_def(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("user {name} should register: {e:?}"));
}

fn user_axiom(env: &mut Environment, name: &str, ty: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
    .unwrap_or_else(|e| panic!("user {name} should register: {e:?}"));
}

/// The two judgments that together identify `a0` and `a1`: the user's own
/// definition says `redex(p) = a0` for EVERY `p` (δ at a variable), and the
/// kernel's rule says `redex(mk … a1) = a1`.
fn delta_and_rule(
    env: &Environment,
    redex_at: impl Fn(Expr) -> Expr,
    witness: Expr,
) -> (Result<(), String>, bool) {
    let tc = TypeChecker::with_mode(env, CleanMode::Cubical);
    let for_all_p = Expr::pi(
        BinderInfo::Default,
        cst("A"),
        path_ty(redex_at(Expr::bvar(0)), cst("a0")),
    );
    let delta = tc
        .check_type(
            &Expr::lam(BinderInfo::Default, cst("A"), refl(cst("a0"))),
            &for_all_p,
        )
        .map(|_| ())
        .map_err(|e| format!("{e:?}"));
    let rule = tc
        .check_type(&refl(cst("a1")), &path_ty(redex_at(witness), cst("a1")))
        .is_ok();
    (delta, rule)
}

/// `Sigma.elim a0 a0 a0 (λ a b. b) p` over a user `Sigma.elim := λ … => a0`
/// and a user `Sigma.mk` axiom.
#[test]
fn attack_cubical_user_sigma_elim_rule() {
    let mut env = points_env();
    // Sigma.elim : A → A → A → (A → A → A) → A → A := λ _ _ _ _ _. a0
    let elim_ty = Expr::arrow(
        cst("A"),
        Expr::arrow(
            cst("A"),
            Expr::arrow(cst("A"), Expr::arrow(arrows(2), arrows(1))),
        ),
    );
    let elim_val = lams(
        3,
        Expr::lam(
            BinderInfo::Default,
            arrows(2),
            Expr::lam(BinderInfo::Default, cst("A"), cst("a0")),
        ),
    );
    user_def(&mut env, "Sigma.elim", elim_ty, elim_val);
    user_axiom(&mut env, "Sigma.mk", arrows(4));
    let snd = lams(2, Expr::bvar(0));
    let redex_at = |p: Expr| {
        Expr::apps(
            cst("Sigma.elim"),
            [cst("a0"), cst("a0"), cst("a0"), snd.clone(), p],
        )
    };
    let pair = Expr::apps(
        cst("Sigma.mk"),
        [cst("a0"), cst("a0"), cst("a0"), cst("a1")],
    );
    let (delta, rule) = delta_and_rule(&env, redex_at, pair);
    if let Err(e) = delta {
        panic!("control: the user's own δ must still hold: {e}");
    }
    assert!(
        !rule,
        "ATTACK ACCEPTED: the Sigma rule fired for a user Sigma.elim (a0 and a1 identified)"
    );
}

/// `Equiv.fwd a0 a0 e` over a user `Equiv.fwd := λ _ _ _. a0` and a user
/// six-argument `Equiv.mk` axiom (the rule projects argument 2).
#[test]
fn attack_cubical_user_equiv_fwd_rule() {
    let mut env = points_env();
    user_def(&mut env, "Equiv.fwd", arrows(3), lams(3, cst("a0")));
    user_axiom(&mut env, "Equiv.mk", arrows(6));
    let redex_at = |e: Expr| Expr::apps(cst("Equiv.fwd"), [cst("a0"), cst("a0"), e]);
    let mk = Expr::apps(
        cst("Equiv.mk"),
        [
            cst("a0"),
            cst("a0"),
            cst("a1"),
            cst("a0"),
            cst("a0"),
            cst("a0"),
        ],
    );
    let (delta, rule) = delta_and_rule(&env, redex_at, mk);
    if let Err(e) = delta {
        panic!("control: the user's own δ must still hold: {e}");
    }
    assert!(
        !rule,
        "ATTACK ACCEPTED: the Equiv.fwd rule fired for a user Equiv.fwd (a0 and a1 identified)"
    );
}

/// Positive control: over the kernel's OWN axioms the Σ-iota still fires,
/// including when the environment adds unrelated declarations of its own.
#[test]
fn control_canonical_sigma_iota_still_fires() {
    let mut env = points_env();
    register_kan_system_axioms(&mut env).expect("kan system axioms");
    register_glue_axioms(&mut env).expect("glue axioms");
    register_sigma_axioms(&mut env).expect("sigma axioms");
    user_axiom(&mut env, "unrelated", cst("A"));
    let level = Level::succ(Level::zero());
    let bfam = Expr::lam(BinderInfo::Default, cst("A"), cst("A"));
    let sigma = Expr::apps(
        Expr::const_(Name::from_string("Sigma"), vec![level.clone()]),
        [cst("A"), bfam.clone()],
    );
    let pair = Expr::apps(
        Expr::const_(Name::from_string("Sigma.mk"), vec![level.clone()]),
        [cst("A"), bfam.clone(), cst("a0"), cst("a1")],
    );
    let motive = Expr::lam(BinderInfo::Default, sigma, cst("A"));
    let redex = Expr::apps(
        Expr::const_(Name::from_string("Sigma.elim"), vec![level]),
        [cst("A"), bfam, motive, lams(2, Expr::bvar(0)), pair],
    );
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    if let Err(e) = tc.check_type(&refl(cst("a1")), &path_ty(redex, cst("a1"))) {
        panic!("the canonical Σ-iota must still project the second component: {e:?}");
    }
}
