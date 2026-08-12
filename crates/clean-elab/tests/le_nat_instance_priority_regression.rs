// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: `LE Nat` must resolve to `instLENat`, not to a general
//! `{α} → [LT α] → LE α` instance that arrives from the `.olean` import at
//! Lean's real priority.
//!
//! ## Why this row specifically
//!
//! `instLENat` is the sibling of `instLTNat` (`066a1173f`), and a prior sweep
//! deliberately LEFT it at `DEFAULT_INSTANCE_PRIORITY` (100) after measuring
//! that the observable behavior looked the same either way. The mechanical
//! census settles it: the shipped `Init/Prelude.olean` serializes `instLENat`
//! into `Lean.Meta.instanceExtension` at **1000** (Lean declares it
//! unannotated), so 100 was simply not Lean's value —
//! `data/prelude_instance_priority_census.json`. "Behaves the same against the
//! instances that happen to be loaded" is not the same claim as "carries Lean's
//! priority", and only the second one survives a new `LE` instance landing.
//!
//! ## What this test pins
//!
//! The decoy is registered exactly the way the `.olean` import registers a
//! general order instance: an **`Axiom`-kind constant with NO value** — nothing
//! can be δ-unfolded to rescue the match, which is the non-reducible shape every
//! imported instance has — whose conclusion is the fully general `LE α`, at
//! Lean's decoded priority 1000.
//!
//!  - PRE-FIX: `instLENat` at 100 loses the priority comparison outright and
//!    `resolve_instance` returns the decoy.
//!  - POST-FIX: both sit at 1000, so `candidate_order`'s head-specificity
//!    tie-break decides and the concrete `LE Nat` instance wins.
//!
//! A test that omitted the decoy would pass either way (nothing to lose to);
//! a decoy registered at 100 would also pass either way (the tie-break already
//! covers that case); and a `@[reducible]` decoy would let the unifier unfold
//! its way out. Only a value-less `Axiom` decoy at Lean's real 1000 is RED
//! without the fix.

use clean_elab::ElabCtx;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, KernelInstanceInfo, Level, Name,
};

/// A plausible general instance name of the kind the import actually brings in.
const DECOY: &str = "Std.PreorderPackage.toLE";

/// Full prelude (so `LE`, `Nat` and the genuine `instLENat` are present as they
/// are in a real run) plus a general `{α : Type} → [LT α] → LE α` decoy
/// registered at Lean's decoded default priority, 1000.
fn env_with_general_le_decoy() -> Environment {
    let mut env = Environment::with_prelude();

    let le = Name::from_string("LE");
    let lt = Name::from_string("LT");
    let type_ = Expr::type_();

    // `LE.{u} : {α : Type u} → Type u` and `LT.{u}` likewise, so the decoy is
    // stated monomorphically at `u := 0` — the universe `LE Nat` lives at.
    let lt_alpha = Expr::app(
        Expr::const_(lt, vec![Level::zero()]),
        Expr::bvar(0), // α
    );
    let le_alpha = Expr::app(
        Expr::const_(le.clone(), vec![Level::zero()]),
        Expr::bvar(1), // α, under the [LT α] binder
    );
    let decoy_ty = Expr::pi(
        BinderInfo::Implicit,
        type_,
        Expr::pi(BinderInfo::InstImplicit, lt_alpha, le_alpha),
    );

    // Declared as an `Axiom`: no value, exactly like every instance the `.olean`
    // import registers.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(DECOY),
        level_params: vec![],
        type_: decoy_ty,
    })
    .expect("the general LE decoy should declare");

    env.register_instance(KernelInstanceInfo {
        name: Name::from_string(DECOY),
        class_name: le,
        priority: 1000,
        type_: None,
        value: None,
    });
    env
}

fn le_nat_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), Vec::<Level>::new()),
    )
}

fn head_name(e: &Expr) -> Name {
    match e.get_app_fn().kind() {
        ExprKind::Const(n, _) => n.clone(),
        other => panic!("expected a constant-headed instance witness, got {other:?}"),
    }
}

/// CORE REGRESSION: with a general `LE α` instance present at Lean's real
/// priority, `LE Nat` must still resolve to `instLENat`.
#[test]
fn test_le_nat_resolves_to_instlenat_over_a_general_le_instance() {
    let env = env_with_general_le_decoy();
    let mut ctx = ElabCtx::new(&env);

    let witness = ctx
        .resolve_instance(&le_nat_goal())
        .expect("`LE Nat` must resolve");

    assert_eq!(
        head_name(&witness),
        Name::from_string("instLENat"),
        "`LE Nat` must resolve to the concrete `instLENat`, not to the general \
         `{{α}} [LT α] : LE α` instance. Pre-fix `instLENat` was registered at \
         priority 100 (Lean's `low`) while the imported general instance carries \
         Lean's real 1000, and priority dominates candidate ordering."
    );
}

/// CONTROL: the decoy is genuinely ranked at Lean's 1000 — at anything lower the
/// core regression above would pass without the fix and diagnose nothing.
#[test]
fn test_the_general_le_decoy_sits_at_leans_decoded_priority() {
    let env = env_with_general_le_decoy();
    let priority = env
        .get_class_instances(&Name::from_string("LE"))
        .iter()
        .find(|i| i.name == Name::from_string(DECOY))
        .map(|i| i.priority)
        .expect("the decoy must be registered as an LE instance");
    assert_eq!(priority, 1000);
}

/// CONTROL: the decoy has no value, so nothing downstream can δ-unfold it. A
/// `@[reducible]` stand-in would let the unifier rescue the match and the core
/// regression would pass with or without the fix.
#[test]
fn test_the_general_le_decoy_is_a_value_less_axiom() {
    let env = env_with_general_le_decoy();
    let info = env
        .get_const(&Name::from_string(DECOY))
        .expect("decoy constant");
    assert!(
        info.value.is_none(),
        "the decoy must have NO value — that is the imported shape"
    );
    assert_eq!(format!("{:?}", info.kind), "Axiom");
}

/// The prelude side of the census, stated where a reader of this file will see
/// it: `instLENat` carries the priority the shipped `.olean` serializes.
#[test]
fn test_instlenat_carries_leans_serialized_priority() {
    let env = Environment::with_prelude();
    let priority = env
        .get_class_instances(&Name::from_string("LE"))
        .iter()
        .find(|i| i.name == Name::from_string("instLENat"))
        .map(|i| i.priority)
        .expect("instLENat must be registered as an LE instance");
    assert_eq!(
        priority, 1000,
        "instLENat must use Lean's unannotated-instance default priority (1000, \
         as serialized in Init/Prelude.olean), not `low` (100)"
    );
}
