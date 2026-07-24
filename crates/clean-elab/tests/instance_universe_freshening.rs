// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: instance resolution must FRESHEN a candidate's universe-level
//! parameters instead of unifying with the instance constant's raw declared
//! names.
//!
//! The stored instance type/term carry the instance constant's declared
//! level-param names verbatim (Lean core's `instHAdd.{u_1}` is the canonical
//! example — its parameter is literally named `u_1`). Before the fix,
//! resolving such an instance pinned that NAME in the declaration-wide,
//! Name-keyed level union-find, where it collided with
//!
//!   (a) the elaborator's own fresh universe params — `fresh_universe_param()`
//!       also generates `u_1`, `u_2`, … — and
//!   (b) the same-named declared param of every other resolution of the same
//!       (or another) polymorphic instance in the same declaration.
//!
//! Observed failure (the trust-ir data-loop bridge blocker): a `Nat`-typed
//! `k + 1` resolved `instHAdd`, committing `u_1 := Zero`; the statement's own
//! fresh `u_1` (an `Eq` whose carrier is a `Type`, needing `Succ Zero`) then
//! died with `TypeMismatch { .. "universe level conflict: Zero vs
//! Succ(Zero)" }` — on a statement real Lean 4.8.0 accepts.
//!
//! This test captures invariant (b) directly, with no `.olean` dependency: one
//! polymorphic instance whose constant declares the level param `u_1`, resolved
//! at `Type 0` and then at `Type 1` inside the SAME `ElabCtx`. Pre-fix the
//! second resolution fails (the committed `u_1 := Zero` conflicts with the
//! required `Succ Zero`); post-fix both succeed.

use clean_elab::ElabCtx;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, KernelClassInfo, KernelInstanceInfo, Level, Name,
};

/// Build an env with:
///   MyC.{u_1}    : Type u_1 → Type u_1            (class carrier, axiom)
///   myInst.{u_1} : {β : Type u_1} → MyC.{u_1} β   (the polymorphic instance)
/// registered as a class + instance, exactly as an `.olean` import registers
/// Lean core's `instHAdd.{u_1}`.
fn env_with_u1_instance() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let u1 = Name::from_string("u_1");
    let type_u1 = Expr::sort(Level::succ(Level::param(u1.clone())));

    // MyC : Type u_1 → Type u_1
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("MyC"),
        level_params: vec![u1.clone()],
        type_: Expr::pi(BinderInfo::Default, type_u1.clone(), type_u1.clone()),
    })
    .expect("MyC should declare");

    // myInst : {β : Type u_1} → MyC β
    let myc_beta = Expr::app(
        Expr::const_(Name::from_string("MyC"), vec![Level::param(u1.clone())]),
        Expr::bvar(0),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myInst"),
        level_params: vec![u1.clone()],
        type_: Expr::pi(BinderInfo::Implicit, type_u1, myc_beta),
    })
    .expect("myInst should declare");

    env.register_class(KernelClassInfo {
        name: Name::from_string("MyC"),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("myInst"),
        class_name: Name::from_string("MyC"),
        priority: 100,
        type_: None,
        value: None,
    });
    env
}

#[test]
fn test_same_instance_resolves_at_two_universes_in_one_ctx() {
    let env = env_with_u1_instance();
    let mut ctx = ElabCtx::new(&env);

    // Goal 1: MyC.{0} Nat — resolving pins the instance's universe to Zero.
    let goal_nat = Expr::app(
        Expr::const_(Name::from_string("MyC"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let first = ctx.resolve_instance(&goal_nat);
    assert!(
        first.is_some(),
        "MyC Nat should resolve via the polymorphic myInst"
    );

    // Goal 2: MyC.{1} (Type 0) — the SAME instance at universe Succ Zero.
    // Pre-fix, resolution unified the raw declared name `u_1`, and the
    // committed `u_1 := Zero` from goal 1 made this second resolution fail
    // with a universe level conflict inside the candidate check.
    let goal_type0 = Expr::app(
        Expr::const_(Name::from_string("MyC"), vec![Level::succ(Level::zero())]),
        Expr::type_(),
    );
    let second = ctx.resolve_instance(&goal_type0);
    assert!(
        second.is_some(),
        "MyC (Type 0) must still resolve in the same ElabCtx: the candidate's \
         universe params must be freshened per attempt, not pinned by name \
         (raw `u_1` committed at Zero by the first resolution)"
    );
}

#[test]
fn test_instance_universe_does_not_poison_ctx_level_state() {
    // Invariant (a): after resolving the instance at Type 0, the shared level
    // union-find must NOT have committed a concrete pin on the raw declared
    // name `u_1` — the elaborator's own second fresh universe param is also
    // named `u_1` (the Eq-over-a-Type-carrier collision from the trust-ir
    // bridge). Pre-fix, `instantiate_level(Param(u_1))` resolved to Zero here.
    let env = env_with_u1_instance();
    let mut ctx = ElabCtx::new(&env);

    let goal_nat = Expr::app(
        Expr::const_(Name::from_string("MyC"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    // The resolved instance term itself is not under test here — only the
    // ctx-wide level union-find state it must NOT have poisoned (below).
    let _resolved_inst = ctx
        .resolve_instance(&goal_nat)
        .expect("MyC Nat should resolve");

    let raw = Level::param(Name::from_string("u_1"));
    let resolved = ctx.metas().instantiate_level(&raw);
    assert_eq!(
        resolved, raw,
        "resolving a polymorphic instance must not pin the constant's raw \
         declared level-param name (`u_1`) in the ctx-wide union-find; \
         found it resolved to {resolved:?}"
    );
}
