// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed rcases patterns `p : t` (Lean's `rcasesPatLo`, `Init/RCases.lean:
//! 70,86,88`; applied by `rcasesCore`'s `.typed` case,
//! `Lean/Elab/Tactic/RCases.lean:290-298`).
//!
//! Ground-truthed on the pinned v4.30.0-rc2 `lean` binary (2026-09-12): the
//! accepted fixtures elaborate there as written, and `rc_wrong` is refused
//! there ("Tactic `rcases` failed: scrutinee has type a = f b but is expected
//! to have type a = b").

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

fn accepts(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, src) {
        panic!("{what}: {e}");
    }
}

/// `rcases … with ⟨f, rfl : r = _⟩` (Mathlib `Logic/Function/Basic.lean:
/// 1044`): the `_` is solved from the component's type, then `rfl`
/// substitutes.
#[test]
fn test_rcases_typed_component_solves_its_hole_then_substitutes() {
    accepts(
        "theorem rc_typed (a b : Nat) (h : ∃ f : Nat → Nat, a = f b) : \
         ∃ f : Nat → Nat, a = f b := by\n\
         \x20 rcases h with ⟨f, rfl : a = _⟩\n\
         \x20 exact ⟨f, rfl⟩\n",
        "`⟨f, rfl : a = _⟩` must type the component and substitute it",
    );
}

#[test]
fn test_obtain_and_rintro_typed_components() {
    accepts(
        "theorem ob_typed (p : Nat → Prop) (h : ∃ x, p x) : ∃ x, p x := by\n\
         \x20 obtain ⟨x, hx : p x⟩ := h\n\
         \x20 exact ⟨x, hx⟩\n\
         theorem ob_unfold (p : Nat → Prop) (h : ∃ x, (fun y => p y) x) : ∃ x, p x := by\n\
         \x20 obtain ⟨x, hx : p x⟩ := h\n\
         \x20 exact ⟨x, hx⟩\n\
         theorem ri_typed (p q : Prop) : p ∧ q → q := by\n\
         \x20 rintro ⟨_, (hq : q)⟩\n\
         \x20 exact hq\n\
         theorem ri_top (p : Prop) : p → p := by\n\
         \x20 rintro (hp : p)\n\
         \x20 exact hp\n",
        "typed components of `obtain` and `rintro` patterns must elaborate",
    );
}

/// Fail-closed: the written type must be definitionally equal to the
/// component's.
#[test]
fn test_rcases_typed_component_refuses_a_different_type() {
    let mut env = Environment::with_prelude();
    let src = "theorem rc_wrong (a b : Nat) (h : ∃ f : Nat → Nat, a = f b) : True := by\n\
               \x20 rcases h with ⟨f, hf : a = b⟩\n\
               \x20 trivial\n";
    assert!(
        elab(&mut env, src).is_some(),
        "`hf : a = b` must not be accepted for a component of type `a = f b`"
    );
}
