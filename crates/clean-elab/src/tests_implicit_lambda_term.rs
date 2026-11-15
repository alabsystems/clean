// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Implicit-lambda introduction is decided ONCE per term, and applies to terms
//! that are not `fun`s.
//!
//! Two halves of one Lean rule (`Lean/Elab/Term/TermElabM.lean`
//! `blockImplicitLambda` :1684, `useImplicitLambda` :1711, `elabImplicitLambda`
//! :1774, dispatched at :1806):
//!
//! * a NON-lambda term facing `∀ {x y}, T` was unified with the `Pi` instead of
//!   being wrapped, so `Function.Injective.preorder f .rfl .rfl`
//!   (`Mathlib/Order/Basic.lean` `Preorder.lift` / `PartialOrder.lift`) left
//!   the `{x y}` as metavariables nothing constrains;
//! * the decision was re-taken at EVERY surface binder inside `elab_lambda`,
//!   so an explicit binder facing an implicit expected binder bound a synthetic
//!   one and recursed with the surface binder unconsumed, stranding the rest of
//!   the lambda with no expected type (`Mathlib/Logic/Basic.lean`
//!   `eq_iff_eq_cancel_left` / `_right`, where a `by rw [h]` body then faced a
//!   fresh unassigned metavariable).
//!
//! Lean's `propagateExpectedType` (`Lean/Elab/Binders.lean`:410, the arm
//! `| .forallE _ d b _ =>` at :416) peels one `forallE` per user binder and
//! IGNORES its binder info. That is why it accepts `fun h a => …` here and
//! REJECTS `fun n x => x : Nat → {α : Type} → α → α` — which Clean used to
//! ACCEPT, a silent-acceptance hole pinned as a refusal below.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

const BASE: &str = "axiom A : Type\n\
                    axiom fA : A → A\n\
                    axiom bA : A\n\
                    axiom cA : A\n\
                    axiom PA : A → Prop\n";

// ---------------------------------------------------------------------------
// The non-lambda wrap.
// ---------------------------------------------------------------------------

#[test]
fn test_non_lambda_term_is_wrapped_against_an_implicit_expected_binder() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}axiom needs : (∀ {{x : A}}, fA x = fA x) → Nat\n\
         def viaRfl : Nat := needs rfl\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`rfl` against `∀ {{x}}, fA x = fA x` must be wrapped: {e}");
    }
}

#[test]
fn test_leading_dot_term_is_wrapped_against_an_implicit_expected_binder() {
    let mut env = Environment::with_prelude();
    // The spelling the `Preorder.lift` rows use: the leading dot is resolved
    // through the wrapped expected type's BODY, which only exists after the
    // wrap — before it, the expected type is the `Pi` and `.mk` names nothing.
    let src = format!(
        "{BASE}inductive Wrap (a : A) : Prop where\n\
         \x20 | mk\n\
         axiom needs2 : (∀ {{x : A}}, Wrap (fA x)) → Nat\n\
         def viaDot : Nat := needs2 .mk\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`.mk` against `∀ {{x}}, Wrap (fA x)` must be wrapped: {e}");
    }
}

#[test]
fn test_two_implicit_binders_are_both_introduced() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}axiom needs3 : (∀ {{x y : A}}, fA x = fA x) → Nat\n\
         def viaTwo : Nat := needs3 rfl\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("both `{{x y}}` must be introduced: {e}");
    }
}

#[test]
fn test_explicit_at_marker_blocks_the_wrap() {
    let mut env = Environment::with_prelude();
    // Lean's `blockImplicitLambda` refuses to wrap an `@`-term. `@rfl` must
    // therefore still be a plain application that does NOT type-check here.
    let src = format!(
        "{BASE}axiom needs4 : (∀ {{x : A}}, fA x = fA x) → Nat\n\
         def viaAt : Nat := needs4 (@rfl A bA)\n"
    );
    assert!(
        elab(&mut env, &src).is_some(),
        "`@rfl A bA` must NOT be wrapped into `fun {{x}} => …`"
    );
}

#[test]
fn test_strict_implicit_expected_binder_does_not_trigger_the_wrap() {
    let mut env = Environment::with_prelude();
    // Lean's own remark: `useImplicitLambda` triggers on implicit and
    // instance-implicit only — a strict-implicit `⦃x⦄` leading binder does
    // not, so this stays a refusal in Clean exactly as it is in Lean.
    let src = format!(
        "{BASE}axiom needs5 : (∀ ⦃x : A⦄, fA x = fA x) → Nat\n\
         def viaStrict : Nat := needs5 rfl\n"
    );
    assert!(
        elab(&mut env, &src).is_some(),
        "a strict-implicit leading binder must not trigger implicit-lambda introduction"
    );
}

// ---------------------------------------------------------------------------
// The once-per-term decision.
// ---------------------------------------------------------------------------

#[test]
fn test_explicit_binder_binds_a_later_implicit_expected_binder() {
    let mut env = Environment::with_prelude();
    // The `eq_iff_eq_cancel_left` shape: the expected type leads with an
    // EXPLICIT arrow, so no wrap is taken; the second surface binder then
    // legitimately binds the implicit `{a}`, and the rest of the lambda keeps
    // its expected type.
    let src = format!("{BASE}def tJ : bA = cA → ∀ {{a : A}}, PA a → PA a := fun h a pa => pa\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("an explicit surface binder must be able to bind `{{a}}`: {e}");
    }
}

#[test]
fn test_a_by_block_under_such_a_binder_still_has_its_expected_type() {
    let mut env = Environment::with_prelude();
    // The row's own vehicle: the body is a tactic block, which under the
    // per-binder rule faced a fresh unassigned metavariable
    // (`searched for fvar#1 in fvar#9223372036854775809`).
    let src = format!(
        "{BASE}def tI : bA = cA → ∀ {{a : A}}, PA a → PA a := fun h a => by\n\
         \x20 intro pa\n\
         \x20 exact pa\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the `by` block must face the real goal, not a fresh metavar: {e}");
    }
}

#[test]
fn test_explicit_then_implicit_is_refused_as_lean_refuses_it() {
    let mut env = Environment::with_prelude();
    // SILENT-ACCEPTANCE PIN. Clean used to accept this and pinned the
    // acceptance in `lean4_corpus_tests::test_implicit_lambda_explicit_then_implicit`.
    // The pinned v4.30.0-rc2 binary rejects it: "x has type Type of sort
    // `Type 1` but is expected to have type x → x" — `x` binds the implicit
    // `{α}`, and the body `x` cannot inhabit `α → α`.
    let src = "def f7 : Nat -> {α : Type} -> α -> α := fun n x => x\n";
    assert!(
        elab(&mut env, src).is_some(),
        "`fun n x => x : Nat → {{α}} → α → α` must be REFUSED, as Lean refuses it"
    );
}

#[test]
fn test_head_position_implicit_lambda_still_fires() {
    let mut env = Environment::with_prelude();
    // The entry decision must keep doing what the per-binder rule did at the
    // head, including the `@` / named-implicit opt-outs.
    let src = "def fil : {α : Type} -> α -> α := fun x => x\n\
               def f2i : {α β : Type} -> (α -> β) -> α -> β := fun f x => f x\n\
               def g1 : {α : Type} -> α -> α := fun {α} x => x\n\
               def g2 : {α : Type} -> α -> α := @fun α x => x\n\
               def g3 : Nat -> Nat := fun x => x\n\
               theorem fil_ok : fil (5 : Nat) = 5 := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("head-position implicit lambdas and their opt-outs must stay green: {e}");
    }
}

#[test]
fn test_instance_implicit_expected_binder_is_introduced_as_a_local_instance() {
    let mut env = Environment::with_prelude();
    // An inserted `[inst]` must still be registered as a local instance, or the
    // body cannot resolve the class it was introduced for. The value is NOT a
    // lambda: `elabImplicitLambda` consumes every non-explicit binder, so a
    // `fun _ =>` here has nothing left to bind and the pinned binary rejects
    // it — "the following variables have been introduced by the implicit
    // lambda feature: α✝ : Type, inst✝ : Cw α✝".
    let src = "class Cw (α : Type) where\n\
               \x20 w : α\n\
               def pick : {α : Type} -> [Cw α] -> α := Cw.w\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("an inserted `[inst]` must be a local instance: {e}");
    }
}

// ---------------------------------------------------------------------------
// Review additions, 2026-09-20. Each fixture below was ground-truthed on the
// pinned v4.30.0-rc2 binary, refusals included, and each was measured to fail
// before its repair.
// ---------------------------------------------------------------------------

#[test]
fn test_strict_implicit_lambda_binder_does_not_block_the_wrap() {
    let mut env = Environment::with_prelude();
    // Lean's `isLambdaWithImplicit` (`TermElabM.lean`:1648-1651) names exactly
    // `implicitBinder` and `instBinder`, so a STRICT-implicit `⦃β⦄` surface
    // binder does NOT block the wrap. The term is therefore wrapped and then
    // refused:
    //
    //   fun ⦃β⦄ x => x has type ⦃β : α✝⦄ → ?m → ?m
    //   but is expected to have type α✝ → α✝
    //
    // Blocking on every non-explicit binder instead let `⦃β⦄` bind the
    // expected `{α}` and the declaration was ACCEPTED — a term Lean refuses.
    let src = "def sl1 : {α : Type} -> α -> α := fun ⦃β⦄ x => x\n";
    assert!(
        elab(&mut env, src).is_some(),
        "`fun ⦃β⦄ x => x : {{α}} → α → α` must be REFUSED, as Lean refuses it"
    );
}

#[test]
fn test_named_implicit_lambda_binder_still_blocks_the_wrap() {
    // The control for the test above: `{β}` and `[inst]` DO block, so the
    // surface binder binds the expected implicit directly and this stays green.
    let mut env = Environment::with_prelude();
    let src = "def sl2 : {α : Type} -> α -> α := fun {β} x => x\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a NAMED implicit surface binder must still block the wrap: {e}");
    }
}

/// OPEN, pinned as a refusal: a bare `fun | … => …` DEFINITION BODY under a
/// declared type whose leading binder is implicit.
///
/// The pinned v4.30.0-rc2 binary ACCEPTS
/// `def h : {α : Type} → MyL α → Nat := fun | .nil => 0 | .cons _ _ => 1`
/// (`fun | …` is not the quotation `fun $binders* => $_`, so
/// `isLambdaWithImplicit` does not block it and it is wrapped like any other
/// term). Clean refuses it — "constructor pattern requires an inductive
/// scrutinee type".
///
/// IT IS NOT THIS MODULE'S SUBJECT, and the two controls below are what prove
/// that. Wrapping this shape WAS implemented and measured on 2026-09-20: the
/// binders really are introduced — the refusal moves to `expected MyL fvar#0 →
/// Nat, got Nat`, naming the introduced `α✝` — and the declaration still does
/// not elaborate, because `elab_pattern_lambda`'s curried peel returns the arm
/// BODY where the lambda is owed. That is a second, independent root cause, so
/// the wrap was reverted rather than landed half-closed, and this pin fails
/// loudly the day either half moves.
#[test]
fn test_pattern_lambda_definition_body_is_refused_under_an_implicit_binder() {
    let mut env = Environment::with_prelude();
    let src = "inductive MyL (α : Type) where\n\
               \x20 | nil : MyL α\n\
               \x20 | cons : α -> MyL α -> MyL α\n\
               def plh : {α : Type} -> MyL α -> Nat := fun\n\
               \x20 | MyL.nil => 0\n\
               \x20 | MyL.cons _ _ => 1\n";
    let err = elab(&mut env, src).expect("OPEN class: this must still be refused");
    assert!(
        err.contains("inductive scrutinee"),
        "the refusal must still be the pattern-match one, not something new: {err}"
    );
}

#[test]
fn test_pattern_lambda_in_an_argument_slot_is_wrapped() {
    // CONTROL 1 for the pin above, and a positive test of this module's
    // subject: the SAME pattern lambda, against the SAME expected type, in an
    // ARGUMENT slot — where the decision is taken at
    // `elaborate_with_expected_type` — is wrapped and elaborates.
    let mut env = Environment::with_prelude();
    let src = "inductive MyLa (α : Type) where\n\
               \x20 | nil : MyLa α\n\
               \x20 | cons : α -> MyLa α -> MyLa α\n\
               axiom needsPL : ({α : Type} -> MyLa α -> Nat) -> Nat\n\
               def viaArg : Nat := needsPL (fun\n\
               \x20 | MyLa.nil => 0\n\
               \x20 | MyLa.cons _ _ => 1)\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a pattern lambda in an argument slot must be wrapped: {e}");
    }
}

#[test]
fn test_parenthesised_pattern_lambda_definition_body_is_wrapped() {
    // CONTROL 2: the same term as the pin, parenthesised. `(fun | …)` is not
    // the bare `PatternMatchLambda` the definition-body entry hands to
    // `elaborate`'s bypass, so it takes the wrap and PASSES — which is what
    // places the residual failure in the pattern-lambda lowering rather than in
    // the implicit-lambda decision.
    let mut env = Environment::with_prelude();
    let src = "inductive MyLb (α : Type) where\n\
               \x20 | nil : MyLb α\n\
               \x20 | cons : α -> MyLb α -> MyLb α\n\
               def plp : {α : Type} -> MyLb α -> Nat := (fun\n\
               \x20 | MyLb.nil => 0\n\
               \x20 | MyLb.cons _ _ => 1)\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the parenthesised pattern lambda must be wrapped: {e}");
    }
}

#[test]
fn test_pattern_lambda_explicit_leading_binder_control_still_elaborates() {
    // The control that isolates the class: with the implicit written as a
    // binder on the declaration, the pattern lambda always worked.
    let mut env = Environment::with_prelude();
    let src = "inductive MyL2 (α : Type) where\n\
               \x20 | nil : MyL2 α\n\
               \x20 | cons : α -> MyL2 α -> MyL2 α\n\
               def plc {α : Type} : MyL2 α -> Nat := fun\n\
               \x20 | MyL2.nil => 0\n\
               \x20 | MyL2.cons _ _ => 1\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the explicit-binder pattern-lambda control must stay green: {e}");
    }
}

#[test]
fn test_non_fun_definition_body_is_wrapped_against_an_implicit_expected_binder() {
    let mut env = Environment::with_prelude();
    // `elab_def_body` does not route through `elaborate_with_expected_type`,
    // so a body that is not a `fun` never met the implicit-lambda decision.
    // `theorem t : ∀ {a}, P a := <term>` is the Mathlib-shaped one.
    let src = format!(
        "{BASE}axiom ppA : ∀ (x : A), PA x\n\
         theorem thmA : ∀ {{x : A}}, PA x := ppA _\n\
         def litA : {{α : Type}} -> Nat := 0\n\
         def identA : {{α : Type}} -> A := bA\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("a non-`fun` definition body must be wrapped: {e}");
    }
}

#[test]
fn test_ordinary_definition_bodies_are_unaffected_by_the_body_wrap() {
    // The must-not-break control: a declared type with an EXPLICIT leading
    // binder, and one with no binder at all, keep their existing route —
    // including the `Nat`-literal-with-expected arm the wrap must not steal.
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}def plainA : A := bA\n\
         def arrowA : A -> A := fun x => x\n\
         def u8A : UInt8 := 1\n\
         def appliedA : A := fA bA\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("ordinary definition bodies must be unchanged: {e}");
    }
}

// ---------------------------------------------------------------------------
// A `match` whose every alternative binds the implicit position itself.
// ---------------------------------------------------------------------------

#[test]
fn test_match_whose_alternatives_bind_the_implicit_is_refused_as_lean_refuses() {
    // `blockImplicitLambda`'s `isLambdaWithImplicit` reads one syntax node and
    // does not look through `match`, so Lean wraps each of these bodies: an
    // `α✝` is introduced around the whole `match`, every alternative faces the
    // REMAINING type `α✝ → Nat`, and a `fun {α : Type} (x : α)` alternative is
    // a type mismatch. Pinned lean v4.30.0-rc2 refuses all three ("fun {A} x
    // => acc has type {A : Type} → A → Nat … but is expected to have type A✝ →
    // Nat"). Clean declined the wrap for this shape from bb3b6ffe6 and accepted
    // it; decision D2 (2026-10-02, docs/DECISIONS.md) is that Clean never
    // accepts what Lean rejects, so each is refused. `pickR` is recursive and
    // takes the per-alternative placement, which refuses it by name;
    // `pickM` and `pickN` take Lean's route and fail at the alternative.
    let cases = [
        (
            "pickM",
            "def pickM (n : Nat) : {α : Type} -> α -> Nat := match n with\n\
             | Nat.zero => fun {α : Type} (x : α) => 0\n\
             | Nat.succ k => fun {α : Type} (x : α) => k\n",
        ),
        (
            "pickR",
            "def pickR (acc : Nat) (n : Nat) : {α : Type} -> α -> Nat := match n with\n\
             | Nat.zero => fun {α : Type} (x : α) => acc\n\
             | Nat.succ k => fun {α : Type} (x : α) => pickR (Nat.succ acc) k x\n",
        ),
        (
            "pickN",
            "def pickN (n : Nat) : {α : Type} -> α -> Nat := match n with\n\
             | Nat.zero => (fun {α : Type} (x : α) => 0)\n\
             | Nat.succ k => (match k with | Nat.zero => fun {α : Type} (x : α) => 1 | Nat.succ j => fun {α : Type} (x : α) => j)\n",
        ),
    ];
    for (name, src) in cases {
        let mut env = Environment::with_prelude();
        assert!(
            elab(&mut env, src).is_some(),
            "{name}: a `match` whose alternatives bind the implicit is refused by pinned Lean \
             and must be refused here (D2)"
        );
        assert!(
            env.get_const(&clean_kernel::Name::from_string(name))
                .is_none(),
            "{name}: a refused definition must not be registered"
        );
    }
}

#[test]
fn test_match_whose_alternatives_do_not_bind_the_implicit_is_still_wrapped() {
    // The control: alternatives that bind only the EXPLICIT position keep the
    // wrap, and each `fun x` then faces `α✝ → Nat` exactly as Lean's
    // `elabImplicitLambda` arranges.
    let mut env = Environment::with_prelude();
    let src = "def pickW (n : Nat) : {α : Type} -> α -> Nat := match n with\n\
               | Nat.zero => fun x => 0\n\
               | Nat.succ k => fun x => k\n\
               theorem pickW_ok : pickW 2 (5 : Nat) = 1 := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a `match` with explicit-only alternatives must still be wrapped: {e}");
    }
}
