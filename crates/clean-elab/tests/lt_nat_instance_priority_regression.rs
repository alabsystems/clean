// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: `LT Nat` must resolve to `instLTNat`, not to a general
//! `{α} → [LE α] → LT α` instance that arrives from the `.olean` import at
//! Lean's real priority.
//!
//! ## The bug
//!
//! Clean's prelude hand-registered `instLTNat` at `DEFAULT_INSTANCE_PRIORITY`
//! (100 — Lean's `low`). Lean declares it unannotated
//! (`Init/Prelude.lean:1901`, `instance instLTNat : LT Nat where …`), so its
//! real priority is 1000, and the shipped `Init/Prelude.olean` serializes
//! exactly that.
//!
//! Priority DOMINATES `candidate_order`
//! (`clean-elab/src/infer/instance.rs` sorts on `Reverse(priority)` before the
//! head-specificity tie-break), so at 100 `instLTNat` ranked below EVERY
//! imported `LT` instance — all of which carry 1000. Measured under real
//! `import Init` (93,249 constants), the winner for `LT Nat` was
//! `Classical.Order.instLT`, which `Init/Data/Order/Lemmas.lean:252` declares
//! `public scoped instance` and Lean would not consider at all without
//! `open scoped Classical.Order`.
//!
//! ## Why it mattered beyond cosmetics
//!
//! `Classical.Order.instLT`'s `lt` field is `a ≤ b ∧ ¬ b ≤ a`, whereas
//! `instLTNat`'s is `Nat.lt`. They are NOT definitionally equal, so a
//! Clean-elaborated hypothesis `h : 0 < n` could not discharge the `0 < n`
//! side condition of an imported lemma stated with Lean's `<`. Measured under
//! `import Init`: `Nat.div_self`, `Nat.succ_pred_eq_of_pos` and
//! `Nat.zero_pow_of_pos` all failed under `simp only [...]` AND under `exact`
//! (the `exact` error read `rigid head/arity mismatch: And vs Nat.le`), and
//! `(0 : Nat) < 5 := by decide` failed too.
//!
//! ## What this test pins
//!
//! The decoy is registered exactly the way the `.olean` import registers
//! `Classical.Order.instLT`: an `Axiom`-kind constant (no value, so nothing can
//! be δ-unfolded to rescue the match — the same non-reducible shape every
//! imported instance has) whose conclusion is the fully general `LT α`, at
//! Lean's decoded priority 1000.
//!
//!  - PRE-FIX: `instLTNat` at 100 loses the priority comparison outright and
//!    `resolve_instance` returns the decoy.
//!  - POST-FIX: both sit at 1000, so `candidate_order`'s head-specificity
//!    tie-break decides and the concrete `LT Nat` instance wins.
//!
//! A test that omitted the decoy would pass either way (there is nothing to
//! lose to), and a decoy registered at 100 would also pass either way (the
//! tie-break already covers that case). Only a decoy at Lean's real 1000 is
//! RED without the fix.

use clean_elab::ElabCtx;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, KernelInstanceInfo, Level, Name,
};

/// The name the real `.olean` import brings in for the general instance.
const DECOY: &str = "Classical.Order.instLT";

/// Full prelude (so `LT`, `Nat` and the genuine `instLTNat` are present as they
/// are in a real run) plus a general `{α : Type} → [LE α] → LT α` decoy
/// registered at Lean's decoded default priority, 1000.
fn env_with_general_lt_decoy() -> Environment {
    let mut env = Environment::with_prelude();

    let lt = Name::from_string("LT");
    let le = Name::from_string("LE");
    let type_ = Expr::type_();

    // Classical.Order.instLT : {α : Type} → [LE α] → LT α
    //
    // Declared as an `Axiom`: it has no value, exactly like every instance the
    // `.olean` import registers (`type_`/`value` are `None` there and the
    // constant itself is served with Lean's own non-reducible definition). A
    // `@[reducible]` stand-in would let the unifier δ-unfold its way out and the
    // fixture would pass with or without the fix.
    // `LT.{u} : {α : Type u} → Type u` and `LE.{u}` likewise, so the decoy is
    // stated monomorphically at `u := 0` — the universe `LT Nat` lives at.
    let le_alpha = Expr::app(
        Expr::const_(le, vec![Level::zero()]),
        Expr::bvar(0), // α
    );
    let lt_alpha = Expr::app(
        Expr::const_(lt.clone(), vec![Level::zero()]),
        Expr::bvar(1), // α, under the [LE α] binder
    );
    let decoy_ty = Expr::pi(
        BinderInfo::Implicit,
        type_,
        Expr::pi(BinderInfo::InstImplicit, le_alpha, lt_alpha),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(DECOY),
        level_params: vec![],
        type_: decoy_ty,
    })
    .expect("the general LT decoy should declare");

    env.register_instance(KernelInstanceInfo {
        name: Name::from_string(DECOY),
        class_name: lt,
        priority: 1000,
        type_: None,
        value: None,
    });
    env
}

fn lt_nat_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), Vec::<Level>::new()),
    )
}

fn head_name(e: &Expr) -> Name {
    match e.get_app_fn().kind() {
        ExprKind::Const(n, _) => n.clone(),
        other => panic!("expected a constant-headed instance witness, got {other:?}"),
    }
}

/// CORE REGRESSION: with a general `LT α` instance present at Lean's real
/// priority, `LT Nat` must still resolve to `instLTNat`.
#[test]
fn test_lt_nat_resolves_to_instltnat_over_a_general_lt_instance() {
    let env = env_with_general_lt_decoy();
    let mut ctx = ElabCtx::new(&env);

    let witness = ctx
        .resolve_instance(&lt_nat_goal())
        .expect("`LT Nat` must resolve");

    assert_eq!(
        head_name(&witness),
        Name::from_string("instLTNat"),
        "`LT Nat` must resolve to the concrete `instLTNat`, not to the general \
         `{{α}} [LE α] : LT α` instance. Pre-fix `instLTNat` was registered at \
         priority 100 (Lean's `low`) while the imported general instance \
         carries Lean's real 1000, and priority dominates candidate ordering."
    );
}

/// The decoy is genuinely reachable — i.e. the test above is not passing
/// because the decoy could never resolve at all. `LT Unit` has no concrete
/// instance, so the general one must win it.
#[test]
fn test_the_general_lt_decoy_is_reachable_for_a_carrier_with_no_concrete_instance() {
    let env = env_with_general_lt_decoy();
    let mut ctx = ElabCtx::new(&env);

    let unit_goal = Expr::app(
        Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Unit"), Vec::<Level>::new()),
    );

    // `[LE Unit]` has no instance either, so resolution legitimately fails —
    // what must NOT happen is the decoy being invisible/unranked. Assert on the
    // registry instead, which is what `candidate_order` reads.
    let _ = ctx.resolve_instance(&unit_goal);
    let entry = env
        .get_class_instances(&Name::from_string("LT"))
        .iter()
        .find(|i| i.name == Name::from_string(DECOY))
        .map(|i| i.priority)
        .expect("the decoy must be registered as an LT instance");
    assert_eq!(
        entry, 1000,
        "the decoy must sit at Lean's decoded priority; at anything lower the \
         core regression above would pass without the fix"
    );
}
