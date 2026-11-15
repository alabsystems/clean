// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.11 / F-106: argument proofs are compared as proofs.
//!
//! The terms are the exact shape `clean check` produced for
//! `(18446744073709551615 : UInt64) * 2 = 18446744073709551614 := rfl`:
//! `Fin.ofNat (2^64 - 1) v`, with `v` the UNWRAPPED product on one side and the
//! literal on the other. Every test that could reach the old runaway runs under
//! a small ambient declaration budget, so a regression FAILS (the budget cuts
//! the `Nat.rec` grind short and the comparison falls back to a mismatch) in
//! well under a second instead of growing without bound.
//!
//! These probes were written (2026-09-19) against WS6.11's own rule, a kernel
//! `is_def_eq` over ground theorem-headed pairs. Main independently landed
//! the same fix as Lean's `isDefEqProofIrrel` (013ce8352, `proof_irrel.rs`:
//! a quick proof's PROPOSITION is unified), so at the 2026-10-14 rebase the
//! rule here is main's and these probes run against it, through
//! [`Unifier::try_unify_proof_args`] (`taken` = `Some(Success)`).

use super::super::*;
use crate::unify::MetaState;
use clean_kernel::env::ConstantKind;
use clean_kernel::tc::{clear_declaration_budget, set_declaration_budget};

/// `2^64 - 1`, the `n` of `Fin.ofNat n : Nat → Fin (n + 1)` for `UInt64`.
const U64_PRED: u128 = 18_446_744_073_709_551_615;
/// `(2^64 - 1) * 2`, the product before it is reduced mod `2^64`.
const WRAPPED: u128 = 36_893_488_147_419_103_230;
/// `(2^64 - 1) * 2 mod 2^64`.
const REDUCED: u128 = 18_446_744_073_709_551_614;
/// Ticks for one comparison. The proof-irrelevant decision spends a few
/// hundred; the `Nat.rec` over `WRAPPED` would need billions. Kept small
/// because a tick of that grind is not free in memory: a 2,000,000-tick budget
/// let an unfixed elaboration reach 35 GB before it ran out.
const BUDGET: u64 = 20_000;

fn lit(n: u128) -> Expr {
    Expr::nat_lit_u128(n)
}

fn fin_of_nat(n: u128, v: u128) -> Expr {
    Expr::app(Expr::app(Expr::const_str("Fin.ofNat"), lit(n)), lit(v))
}

/// `Nat.mod_lt v (Nat.succ n) (Nat.zero_lt_succ n) : v % (n + 1) < n + 1` —
/// the proof field `Fin.ofNat n v` unfolds to.
fn mod_lt(n: u128, v: u128) -> Expr {
    let succ_n = Expr::app(Expr::const_str("Nat.succ"), lit(n));
    let pos = Expr::app(Expr::const_str("Nat.zero_lt_succ"), lit(n));
    Expr::app(
        Expr::app(Expr::app(Expr::const_str("Nat.mod_lt"), lit(v)), succ_n),
        pos,
    )
}

/// Unify under the ambient budget, restoring the thread's default after.
fn unify_bounded(env: &Environment, left: &Expr, right: &Expr) -> UnifyResult {
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, env, LocalContext::new());
    set_declaration_budget(BUDGET);
    let result = unifier.unify(left, right);
    eprintln!(
        "ws611 unify spent {} ticks",
        clean_kernel::tc::declaration_budget_used()
    );
    clear_declaration_budget();
    result
}

/// Whether the proof-irrelevance rule alone (no fallback path) closes the pair.
fn taken(unifier: &mut Unifier<'_>, left: &Expr, right: &Expr) -> bool {
    matches!(
        unifier.try_unify_proof_args(left, right),
        Some(UnifyResult::Success)
    )
}

#[test]
fn ws611_the_proof_field_is_a_quick_proof() {
    // The gate this rule rides on. If `Nat.mod_lt` ever stopped being a
    // syntactic proof (its declared type ending in a proposition after one
    // `∀` per argument), the rule would silently stop firing on this shape.
    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string("Nat.mod_lt"))
        .expect("the prelude registers Nat.mod_lt");
    assert_eq!(info.kind, ConstantKind::Theorem);
    let mut metas = MetaState::new();
    let unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(unifier.is_proof_quick(&mod_lt(U64_PRED, WRAPPED)));
}

#[test]
fn ws611_wrapped_fin_values_unify_without_unfolding_their_proofs() {
    // POSITIVE, through the App arm: `Fin.ofNat` is a definition, so the entry
    // WHNF exposes `Fin.mk (n+1) (v % (n+1)) (Nat.mod_lt v …)` on both sides;
    // the values reduce to the same literal and the proofs differ.
    let env = Environment::with_prelude();
    let result = unify_bounded(
        &env,
        &fin_of_nat(U64_PRED, WRAPPED),
        &fin_of_nat(U64_PRED, REDUCED),
    );
    assert!(
        matches!(result, UnifyResult::Success),
        "wrapped and reduced Fin values must unify: {result:?}"
    );
}

#[test]
fn ws611_two_proofs_of_one_proposition_unify_at_the_entry() {
    // POSITIVE, at the `unify` entry: the pair IS the two proofs, so the
    // leading WHNF would unfold `Nat.mod_lt` before any arm ran.
    let env = Environment::with_prelude();
    let result = unify_bounded(&env, &mod_lt(U64_PRED, WRAPPED), &mod_lt(U64_PRED, REDUCED));
    assert!(
        matches!(result, UnifyResult::Success),
        "proofs of `v % 2^64 < 2^64` for congruent v must unify: {result:?}"
    );
}

#[test]
fn ws611_off_by_one_value_is_refused_by_name() {
    // NEGATIVE TWIN: the value is off by one, so the refusal must come from
    // the VALUE comparison — named — and never from the proofs.
    let env = Environment::with_prelude();
    let result = unify_bounded(
        &env,
        &fin_of_nat(U64_PRED, WRAPPED),
        &fin_of_nat(U64_PRED, REDUCED + 1),
    );
    match result {
        UnifyResult::Failure(reason) => assert!(
            reason.contains("Nat literal mismatch"),
            "the refusal must name the value mismatch, got: {reason}"
        ),
        other => panic!("an off-by-one value must be refused, got {other:?}"),
    }
}

#[test]
fn ws611_proofs_of_different_propositions_are_not_identified() {
    // MUTATION CONTROL. A rule that trusted the theorem HEAD — "two
    // `Nat.mod_lt` applications are proofs, so they are equal" — would accept
    // this pair: `7 % 5 < 5` and `9 % 5 < 5` are different propositions
    // (`2 < 5` vs `4 < 5`). Only a rule that compares the PROPOSITIONS refuses
    // it. Small values keep the historical fallback cheap.
    let env = Environment::with_prelude();
    let result = unify_bounded(&env, &mod_lt(4, 7), &mod_lt(4, 9));
    assert!(
        !matches!(result, UnifyResult::Success),
        "proofs of different propositions must not unify"
    );
}

#[test]
fn ws611_a_metavariable_argument_declines_the_shortcut() {
    // A pair whose type cannot be inferred (here: a metavariable inside the
    // proof) must DECLINE — leaving it to the historical path — and must not
    // touch the metavariable state while doing so (`proof_irrel.rs`: an
    // inference failure is rolled back exactly).
    let env = Environment::with_prelude();
    let mut metas = MetaState::new();
    let id = metas.fresh(Expr::const_str("Nat"));
    let meta = Expr::fvar(MetaState::to_fvar(id));
    let succ_n = Expr::app(Expr::const_str("Nat.succ"), lit(4));
    let pos = Expr::app(Expr::const_str("Nat.zero_lt_succ"), lit(4));
    let flex = Expr::app(
        Expr::app(Expr::app(Expr::const_str("Nat.mod_lt"), meta), succ_n),
        pos,
    );
    let generation = metas.generation();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(
        unifier.try_unify_proof_args(&flex, &mod_lt(4, 7)).is_none(),
        "a pair mentioning an unsolved metavariable must decline"
    );
    drop(unifier);
    assert_eq!(
        metas.generation(),
        generation,
        "no metavariable state may move"
    );
    assert!(!metas.is_assigned(id));

    // Control: with no metavariable anywhere, the same shape is taken
    // (`7 % 5` and `12 % 5` are both `2`, so this is one proposition).
    let mut ground = MetaState::new();
    let mut unifier = Unifier::with_env(&mut ground, &env, LocalContext::new());
    assert!(taken(&mut unifier, &mod_lt(4, 7), &mod_lt(4, 12)));
}

/// Ask the rule alone (no fallback path) under the ambient budget, and report
/// what it spent, so a test can pin the query's COST as well as its answer.
fn shortcut_bounded(env: &Environment, left: &Expr, right: &Expr) -> (bool, u64) {
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, env, LocalContext::new());
    set_declaration_budget(BUDGET);
    let was_taken = taken(&mut unifier, left, right);
    let spent = clean_kernel::tc::declaration_budget_used();
    clear_declaration_budget();
    eprintln!("ws611 shortcut -> {was_taken} after {spent} ticks");
    (was_taken, spent)
}

#[test]
fn ws611_adv_proofs_of_distinct_wrapped_propositions_are_refused() {
    // ADVERSARIAL (review): the large-value twin of the mutation control.
    // `WRAPPED % 2^64 = REDUCED`, so these are proofs of `REDUCED < 2^64` and
    // `REDUCED + 1 < 2^64` — different propositions at the exact F-106 scale.
    // A rule that compared the proofs' VALUES modulo the bound, or that
    // trusted the head, would accept; a proposition check must not.
    let env = Environment::with_prelude();
    let left = mod_lt(U64_PRED, WRAPPED);
    let right = mod_lt(U64_PRED, REDUCED + 1);
    let (was_taken, _) = shortcut_bounded(&env, &left, &right);
    assert!(
        !was_taken,
        "proofs of different propositions must not be taken"
    );
    let result = unify_bounded(&env, &left, &right);
    assert!(
        !matches!(result, UnifyResult::Success),
        "proofs of different propositions must not unify: {result:?}"
    );
}

#[test]
fn ws611_adv_loose_bound_variable_declines() {
    // ADVERSARIAL (review): the unifier compares some bodies with loose
    // `BVar`s still in them (e.g. the cubical path-lambda arm). A loose bound
    // variable has no type in any context, so the pair must be declined —
    // never a panic, never an accept, and without spending the budget.
    let env = Environment::with_prelude();
    let succ_n = Expr::app(Expr::const_str("Nat.succ"), lit(4));
    let pos = Expr::app(Expr::const_str("Nat.zero_lt_succ"), lit(4));
    let open = |v: Expr| {
        Expr::app(
            Expr::app(Expr::app(Expr::const_str("Nat.mod_lt"), v), succ_n.clone()),
            pos.clone(),
        )
    };
    let (was_taken, spent) = shortcut_bounded(&env, &open(Expr::bvar(0)), &open(Expr::bvar(1)));
    assert!(!was_taken, "a pair with loose bound variables must decline");
    assert_eq!(spent, 0, "declining must not spend the declaration budget");
}

#[test]
fn ws611_adv_local_hypothesis_against_a_wrapped_proof() {
    // ADVERSARIAL (review): only ONE side is a theorem application; the other
    // is a local hypothesis `h : REDUCED % 2^64 < 2^64` from the context. The
    // historical path WHNF'd the theorem side here exactly as in F-106 (a
    // hypothesis FVar gives it nothing to match structurally), so the rule
    // must fire on either side and accept the pair from the context entry's
    // type.
    let env = Environment::with_prelude();
    let prop = TypeChecker::new(&env)
        .infer_type(&mod_lt(U64_PRED, REDUCED))
        .expect("the proof field is well-typed");
    let mut ctx = LocalContext::new();
    let h = ctx.push(
        Name::from_string("h"),
        prop,
        clean_kernel::BinderData::default(),
    );
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, ctx);
    set_declaration_budget(BUDGET);
    let was_taken = taken(&mut unifier, &Expr::fvar(h), &mod_lt(U64_PRED, WRAPPED));
    let spent = clean_kernel::tc::declaration_budget_used();
    clear_declaration_budget();
    assert!(
        was_taken,
        "a hypothesis of the same proposition must be taken"
    );
    assert!(spent < BUDGET / 4, "the pair must be cheap: {spent} ticks");
    // Twin: a hypothesis of a DIFFERENT proposition (`REDUCED + 1`) is not.
    let other = TypeChecker::new(&env)
        .infer_type(&mod_lt(U64_PRED, REDUCED + 1))
        .expect("well-typed");
    let mut ctx = LocalContext::new();
    let h = ctx.push(
        Name::from_string("h"),
        other,
        clean_kernel::BinderData::default(),
    );
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, ctx);
    set_declaration_budget(BUDGET);
    let was_taken = taken(&mut unifier, &Expr::fvar(h), &mod_lt(U64_PRED, WRAPPED));
    clear_declaration_budget();
    assert!(
        !was_taken,
        "a hypothesis of another proposition must not be taken"
    );
}

// ---------------------------------------------------------------------------
// Adversarial review (WS6.11 review pass). Each probe is an input the
// implementer did not write, aimed at one of: a FALSE claim still accepted, a
// LEGITIMATE pair wrongly refused, or a panic on ill-formed ground input.
// ---------------------------------------------------------------------------

/// An environment in which `WS611.dataTheorem : Nat -> Nat` is registered with
/// `ConstantKind::Theorem` even though its type is DATA, not a proposition.
///
/// WS6.11's own rule keyed its cost gate on the head's declaration KIND; main's
/// keys on the declared TYPE (`is_proof_quick`). Either way this is the shape
/// that tests whether the rule ever concludes "theorem-headed, therefore equal"
/// without consulting the proposition.
fn env_with_data_kinded_theorem() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    let nat = Expr::const_str("Nat");
    let mut info = clean_kernel::env::ConstantInfo::new(
        Name::from_string("WS611.dataTheorem"),
        vec![],
        Expr::pi(clean_kernel::BinderInfo::Default, nat.clone(), nat),
        None,
        false,
    );
    info.kind = ConstantKind::Theorem;
    env.add_constant_unchecked_for_test(info);
    (env, Expr::const_str("WS611.dataTheorem"))
}

#[test]
fn ws611_adv_theorem_kind_at_a_data_type_is_not_blessed() {
    // ADVERSARIAL: a FALSE claim. `WS611.dataTheorem 3` and
    // `WS611.dataTheorem 4` are theorem-HEADED but their type is `Nat`, not a
    // `Prop`. A rule that read the head's kind as a verdict would identify two
    // distinct Nats.
    let (env, head) = env_with_data_kinded_theorem();
    assert!(
        env.get_const(&Name::from_string("WS611.dataTheorem"))
            .is_some_and(|i| i.kind == ConstantKind::Theorem),
        "the fixture must really be theorem-kinded, or this proves nothing"
    );
    let three = Expr::app(head.clone(), lit(3));
    let four = Expr::app(head, lit(4));
    let (was_taken, spent) = shortcut_bounded(&env, &three, &four);
    assert!(
        !was_taken,
        "two distinct Nats must never be identified as proofs"
    );
    assert!(
        spent < BUDGET / 4,
        "the decline must be cheap: {spent} ticks"
    );
    assert!(
        !matches!(unify_bounded(&env, &three, &four), UnifyResult::Success),
        "and the whole unification must still refuse them"
    );
}

#[test]
fn ws611_adv_underapplied_theorem_with_distinct_statements_is_refused() {
    // ADVERSARIAL: a FALSE claim at a Pi-into-Prop type. `Nat.mod_lt 7` and
    // `Nat.mod_lt 9` are both theorem-headed and ground, and both inhabit a
    // PROPOSITION (`forall y, 0 < y -> v % y < y` is a Prop by
    // impredicativity), so proof irrelevance is reachable — but the two
    // propositions differ under a SYMBOLIC modulus, where no literal reduction
    // can close the gap. It must be refused.
    let env = Environment::with_prelude();
    let under = |v: u128| Expr::app(Expr::const_str("Nat.mod_lt"), lit(v));
    let (was_taken, spent) = shortcut_bounded(&env, &under(7), &under(9));
    assert!(
        !was_taken,
        "proofs of two different (partially applied) statements must not unify"
    );
    assert!(
        spent < BUDGET / 4,
        "the decline must be cheap: {spent} ticks"
    );
    // Control: the SAME partial application is taken (one proposition).
    let (was_taken, _) = shortcut_bounded(&env, &under(7), &under(7));
    assert!(was_taken, "one proposition must still be taken");
}

#[test]
fn ws611_adv_distinct_moduli_at_f106_scale_are_refused_cheaply() {
    // ADVERSARIAL: the F-106 shape where the two propositions differ in the
    // MODULUS rather than the value — `WRAPPED % 2^64 < 2^64` against
    // `WRAPPED % (2^64-1) < 2^64-1`. Both sides need a big-literal `Nat.mod`
    // before they can be told apart, so this is the decline that could
    // plausibly have been expensive. It must be refused, and it must not eat
    // the budget: a declining query that burned ticks would turn the fix into
    // a NEW way for a legitimate module to hit the declaration budget.
    let env = Environment::with_prelude();
    let left = mod_lt(U64_PRED, WRAPPED);
    let right = mod_lt(U64_PRED - 1, WRAPPED);
    let (was_taken, spent) = shortcut_bounded(&env, &left, &right);
    assert!(!was_taken, "different moduli are different propositions");
    assert!(
        spent < BUDGET / 4,
        "a declining query must stay cheap: {spent} ticks"
    );
    assert!(
        !matches!(unify_bounded(&env, &left, &right), UnifyResult::Success),
        "and the whole unification must refuse them"
    );
}

#[test]
fn ws611_adv_ill_formed_ground_terms_decline_without_panicking() {
    // ADVERSARIAL: the rule's quick-proof gate only inspects the HEAD, so an
    // argument can be an undeclared constant or the application can be
    // over-applied. Neither may panic; both must decline (the historical path
    // then reports the real error).
    let env = Environment::with_prelude();
    let succ_n = Expr::app(Expr::const_str("Nat.succ"), lit(4));
    let pos = Expr::app(Expr::const_str("Nat.zero_lt_succ"), lit(4));
    let well_formed = mod_lt(4, 7);

    let unknown_arg = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_str("Nat.mod_lt"),
                Expr::const_str("WS611.noSuchConstant"),
            ),
            succ_n.clone(),
        ),
        pos.clone(),
    );
    let (was_taken, _) = shortcut_bounded(&env, &unknown_arg, &well_formed);
    assert!(
        !was_taken,
        "an undeclared constant must decline, not be blessed"
    );

    let over_applied = Expr::app(Expr::app(mod_lt(4, 7), lit(5)), lit(6));
    let (was_taken, _) = shortcut_bounded(&env, &over_applied, &well_formed);
    assert!(!was_taken, "an over-applied theorem must decline");

    // A `Proj` out of a non-structure is ill-typed the same way.
    let bad_proj = Expr::proj(Name::from_string("Prod"), 0, well_formed.clone());
    let (was_taken, _) = shortcut_bounded(&env, &bad_proj, &well_formed);
    assert!(!was_taken, "an ill-typed projection must decline");
}

#[test]
fn ws611_adv_a_theorem_against_a_data_term_declines_cheaply() {
    // ADVERSARIAL: the gate fires when EITHER side is a quick proof, so a
    // proof compared against an ordinary data term reaches the rule. It must
    // decline, cheaply, and must not change the unification's answer.
    let env = Environment::with_prelude();
    let proof = mod_lt(U64_PRED, WRAPPED);
    let data = lit(5);
    let (was_taken, spent) = shortcut_bounded(&env, &proof, &data);
    assert!(!was_taken, "a proof and a Nat are not definitionally equal");
    assert!(
        spent < BUDGET / 4,
        "the decline must be cheap: {spent} ticks"
    );
}

#[test]
fn ws611_adv_the_legacy_unifier_without_an_environment_declines() {
    // ADVERSARIAL: `Unifier::new` has no checker and no environment. The rule
    // must be inert there rather than reaching for a `None`.
    let env = Environment::with_prelude();
    let mut metas = MetaState::new();
    let mut unifier = Unifier::new(&mut metas);
    assert!(
        unifier
            .try_unify_proof_args(&mod_lt(4, 7), &mod_lt(4, 12))
            .is_none(),
        "the legacy (no-environment) unifier must decline"
    );
    drop(unifier);
    // Control: the same pair IS taken once an environment is present.
    let mut metas = MetaState::new();
    let mut unifier = Unifier::with_env(&mut metas, &env, LocalContext::new());
    assert!(taken(&mut unifier, &mod_lt(4, 7), &mod_lt(4, 12)));
}
