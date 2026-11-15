// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `congr` is Lean's `MVarId.congrN`; every fixture here was ground-truthed
//! on the pinned v4.30.0-rc2 `lean` binary (2026-09-12): the accepted ones
//! elaborate there as written, and `leftAlone` is the one where Lean's
//! `congr` leaves `f a = g a` untouched (it does not reduce to `f = g`).

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

#[test]
fn test_congr_splits_and_closes_by_assumption_recursively() {
    let mut env = Environment::with_prelude();
    let src = "theorem one (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by congr\n\
               theorem nested (f : Nat → Nat) (a b : Nat) (h : a = b) : f (f a) = f (f b) := by congr\n\
               theorem two (f : Nat → Nat → Nat) (a b c : Nat) (h : a = b) : f a c = f b c := by\n\
               \x20 congr\n\
               theorem depthOne (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by congr 1\n\
               theorem plain (p : Prop) (h : p) : p := by congr\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`congr` must split and close these as Lean does: {e}");
    }
}

#[test]
fn test_congr_depth_one_leaves_the_argument_goal() {
    let mut env = Environment::with_prelude();
    let src = "theorem addComm (f : Nat → Nat) (a b : Nat) : f (a + b) = f (b + a) := by\n\
               \x20 congr 1\n\
               \x20 exact Nat.add_comm a b\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`congr 1` must leave exactly `a + b = b + a`: {e}");
    }
}

#[test]
fn test_congr_casts_proof_arguments_that_depend_on_a_changed_argument() {
    let mut env = Environment::with_prelude();
    // `⟨x, hx⟩ = ⟨y, rfl⟩`: `x = y` by assumption, the proofs by irrelevance.
    let src = "theorem subtypeEq (y : Nat) : ∀ z : { x // x = y }, z = ⟨y, rfl⟩ :=\n\
               \x20 fun ⟨x, hx⟩ => by congr\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`congr` must treat the Subtype proof as a cast: {e}");
    }
}

#[test]
fn test_congr_splits_implications() {
    let mut env = Environment::with_prelude();
    let src = "theorem imp (a b : Nat) (h : a = b) : (a = 0 → True) = (b = 0 → True) := by congr\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`congr` must split an implication equality: {e}");
    }
}

#[test]
fn test_congr_leaves_a_goal_whose_heads_differ() {
    let mut env = Environment::with_prelude();
    let src = "theorem leftAlone (f g : Nat → Nat) (a : Nat) (h : f = g) : f a = g a := by\n\
               \x20 congr\n\
               \x20 exact congrFun h a\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`congr` must leave `f a = g a` untouched (Lean does): {e}");
    }
}

#[test]
fn test_congr_closes_decidable_instances_by_subsingleton() {
    let mut env = Environment::with_prelude();
    // The two constants `congr` uses, `Subsingleton.elim` and
    // `instSubsingletonDecidable`, are Lean 4.8.0 `Init` constants a file may
    // not declare; the prelude supplies them (`clean_kernel`'s
    // `lean_core_supply`). Lean 4.8.0 proves `diteInst` by `congr` as
    // written (measured 2026-09-27).
    let src = "theorem diteInst (c : Prop) (i1 i2 : Decidable c) (t : c → Nat) (e : ¬c → Nat) :\n\
               \x20   @dite Nat c i1 t e = @dite Nat c i2 t e := by congr\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`congr` must close differing `Decidable` instances: {e}");
    }
}
