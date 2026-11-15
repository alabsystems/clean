// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `refine <f> (fun x => ?_)` — a hole that IS the whole body of a lambda in an
//! argument slot, whose type mentions the lambda's binder.
//!
//! `fun x => ?_` elaborates to `Lam(T, ?m)`: `?m`'s recorded TYPE mentions the
//! binder's fvar, but the TERM does not, and a metavariable is a leaf that
//! `abstract_fvar` has nothing to rewrite. `infer_type` on the finished lambda
//! then pushes a FRESH fvar for the binder, reads `?m`'s type back with the OLD
//! one still free, and abstracts the fresh one out of a body that never
//! mentions it — inferring `Pi(T, P fvar#old)` where `Pi(T, P bvar0)` is
//! expected. The `Pi`/`Pi` arm opens both with one more fresh fvar and reports
//! the pair: `Type mismatch: expected (x : α) → f₁ x = f₂ x, got fvar mismatch:
//! fvar#6 vs fvar#14` — `Mathlib/Logic/Function/Basic.lean`
//! `Function.extend_injective`.
//!
//! Lean expresses the dependence at construction time: `mkLambdaFVars` runs
//! `elimMVarDeps`, which replaces `?m` by `?n x` and DELAYED-assigns `?n` to
//! `fun x => ?m`, so the term's type is right while the tactic goal stays `?m`
//! with `x` in its own local context. The pinned v4.30.0-rc2 binary accepts
//! every fixture below.
//!
//! OPEN, pinned as a refusal. The discriminators are the point: only this
//! exact shape fails, and the NON-dependent twin passes, which isolates the
//! mechanism to the ABSTRACTION rather than to the `refine` bridge — the
//! correction this pin records, because the first diagnosis of the class
//! placed it in the bridge's hole handling.
//!
//! TWO TERM-SHAPE REPAIRS WERE MEASURED AND REVERTED, 2026-09-20. Both make
//! the dependence explicit in the term at `elab_lambda`'s abstraction —
//! `(fun a : T => a) ?m`, and then `@id T ?m` to avoid adding a binder layer —
//! and both get PAST the `fvar mismatch` (the inferred type is then right) only
//! to fail at the finished proof's type check, AND to regress
//! `refine fun n => ?_`, which is green today. The reason is the other half of
//! the contract: `import_pending_goals`
//! (`tactic/term_close/refine_bridge.rs`) mints a FRESH tactic fvar for every
//! captured local, so the moment the hole's TYPE is materialised into the TERM
//! it carries the elaborator's fvar while the solution carries the tactic's.
//!
//! Lean does not have that problem because `elimMVarDeps` pairs the term
//! rewrite with a DELAYED assignment: `?n` (over the outer context) is
//! delayed-assigned to `fun x => ?m`, so the term's type is right while the
//! tactic goal stays `?m` with `x` in its own local context — which is why
//! Lean displays `x : α ⊢ f₁ x = f₂ x`. Clean's `MetaState` has no delayed
//! assignment; adding one is the increment this class needs, and it is not a
//! patch to either site alone.

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
                    axiom f1 : Nat → A\n\
                    axiom f2 : Nat → A\n\
                    axiom PP : Prop\n\
                    axiom funext' : (∀ x : Nat, f1 x = f2 x) → f1 = f2\n\
                    axiom nondep : (∀ x : Nat, PP) → f1 = f2\n";

#[test]
fn test_refine_hole_under_a_lambda_in_an_argument_slot() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}theorem viaRefine (hg : ∀ x : Nat, f1 x = f2 x) : f1 = f2 := by\n\
         \x20 refine funext' fun x => ?_\n\
         \x20 exact hg x\n"
    );
    let err = elab(&mut env, &src).expect(
        "PINNED GAP: `refine funext' fun x => ?_` still fails. The day it elaborates, \
         delete this pin and assert success instead.",
    );
    assert!(
        err.contains("fvar mismatch"),
        "the pinned failure is the binder's fvar surviving free in the lambda's inferred \
         type; a DIFFERENT failure here means the class moved and the pin is stale: {err}"
    );
}

#[test]
fn test_refine_hole_under_a_lambda_with_a_named_hole() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}theorem viaNamed (hg : ∀ x : Nat, f1 x = f2 x) : f1 = f2 := by\n\
         \x20 refine funext' fun x => ?a\n\
         \x20 exact hg x\n"
    );
    let err =
        elab(&mut env, &src).expect("PINNED GAP: a NAMED hole under the lambda fails identically");
    assert!(
        err.contains("fvar mismatch"),
        "the hole's NAME is not part of the mechanism: {err}"
    );
}

#[test]
fn test_refine_hole_under_a_lambda_with_an_explicit_binder_type() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}theorem viaTyped (hg : ∀ x : Nat, f1 x = f2 x) : f1 = f2 := by\n\
         \x20 refine funext' fun (x : Nat) => ?_\n\
         \x20 exact hg x\n"
    );
    let err =
        elab(&mut env, &src).expect("PINNED GAP: an explicitly typed binder fails identically");
    assert!(
        err.contains("fvar mismatch"),
        "writing the binder's type is not part of the mechanism: {err}"
    );
}

#[test]
fn test_non_dependent_hole_under_a_lambda_still_elaborates() {
    let mut env = Environment::with_prelude();
    // The discriminator: the hole's type does NOT mention the binder, so the
    // abstraction never lost anything and this was green all along.
    let src = format!(
        "{BASE}theorem viaNondep (hp : PP) : f1 = f2 := by\n\
         \x20 refine nondep fun x => ?_\n\
         \x20 exact hp\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the non-dependent control must stay green: {e}");
    }
}

#[test]
fn test_refine_controls_stay_green() {
    let mut env = Environment::with_prelude();
    // The three shapes that were already green and must stay byte-identical:
    // a hole under a TOP-LEVEL lambda, a hole in an argument slot with no
    // lambda, and the hole-free term.
    let src = format!(
        "{BASE}theorem topLevel (hg : ∀ x : Nat, f1 x = f2 x) : ∀ n : Nat, f1 n = f2 n := by\n\
         \x20 refine fun n => ?_\n\
         \x20 exact hg n\n\
         theorem argSlot (hg : ∀ x : Nat, f1 x = f2 x) : f1 = f2 := by\n\
         \x20 refine funext' ?_\n\
         \x20 intro x\n\
         \x20 exact hg x\n\
         theorem noHole (hg : ∀ x : Nat, f1 x = f2 x) : f1 = f2 :=\n\
         \x20 funext' fun x => hg x\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the refine controls must stay green: {e}");
    }
}
