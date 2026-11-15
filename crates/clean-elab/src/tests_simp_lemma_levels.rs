// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How `simp` instantiates a lemma it is about to rewrite with: its universe
//! parameters and the binders the left-hand-side match leaves open.
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12): each accepted declaration elaborates there as written, and
//! each refused one fails there with "`simp` made no progress".

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

/// Elaborate `setup`, then `theorem`, and return the theorem's error —
/// asserting it is simp's own "no progress" refusal and NOT the kernel
/// aborting on a loose de Bruijn index.
fn expect_simp_refusal(setup: &str, theorem: &str) {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, setup) {
        panic!("fixture setup must elaborate: {e}");
    }
    let err = elab(&mut env, theorem)
        .unwrap_or_else(|| panic!("Lean refuses this rewrite (no progress); so must Clean"));
    assert!(
        !err.contains("Unbound variable"),
        "the rewrite must be refused by simp, not by the kernel on a loose binder: {err}"
    );
    assert!(
        err.contains("NoProgress") || err.contains("no progress"),
        "the refusal must be simp's own 'no progress': {err}"
    );
}

/// An `Iff` lemma whose instance binder the LHS does not determine, for a
/// class with no instance at all — monomorphic (`lemK2`) or
/// universe-polymorphic (`lemK4`, which only became reachable once the
/// template's levels are instantiated) — has no proof simp could build, and
/// neither does one whose DATA binder no side mentions (`lemD`): Lean refuses
/// each rewrite ("`simp` made no progress"). The work package measured the
/// instance shape aborting a whole declaration with "type check failed:
/// Unbound variable index: 1" (a `propext` template still holding the
/// binder's loose de Bruijn index); here each is refused by simp itself.
#[test]
fn test_simp_iff_lemma_with_an_undetermined_binder_fails_closed() {
    let setup = "axiom PP {α : Type} : α → Prop\n\
                 axiom lemD {α : Type} (x : Nat) (y : α) : PP x ↔ True\n\
                 class Inh2 (α : Type) where\n\
                 \x20 pt : α\n\
                 axiom lemK2 {α : Type} [Inh2 α] (x : α) : PP x ↔ True\n\
                 class Inh4 (α : Sort u) where\n\
                 \x20 pt : α\n\
                 axiom QQ {α : Sort u} : α → Prop\n\
                 axiom lemK4 {α : Sort u} [Inh4 α] (x : α) : QQ x ↔ True\n";
    expect_simp_refusal(
        setup,
        "theorem tK2 (n : Nat) : PP n := by simp only [lemK2]\n",
    );
    expect_simp_refusal(
        setup,
        "theorem tK4 (n : Nat) : QQ n := by simp only [lemK4]\n",
    );
    expect_simp_refusal(
        setup,
        "theorem tD (n : Nat) : PP n := by simp only [lemD]\n",
    );
}

/// Lean's `SimpTheorem.getValue` gives every USE of a universe-polymorphic
/// theorem fresh level metavariables, so an `Iff` lemma fires exactly like its
/// `Eq` twin — on a concrete universe, on the goal's own universe whatever its
/// name (including the SAME name as the lemma's, Mathlib's ubiquitous
/// `u_1`), under a `Type u` (`Sort (u+1)`) binder, and for a level that only a
/// binder's type mentions, which matching alone cannot solve.
#[test]
fn test_simp_only_fires_universe_polymorphic_iff_lemmas() {
    let mut env = Environment::with_prelude();
    let src = "axiom my_exists_eq_E {α : Sort v} {a' : α} : (∃ a, a = a') = True\n\
               axiom my_exists_eq_I {α : Sort v} {a' : α} : (∃ a, a = a') ↔ True\n\
               theorem sE (b : Nat) : ∃ a, a = b := by simp only [my_exists_eq_E]\n\
               theorem sI (b : Nat) : ∃ a, a = b := by simp only [my_exists_eq_I]\n\
               theorem sIw {β : Sort w} (b : β) : ∃ a, a = b := by simp only [my_exists_eq_I]\n\
               theorem sIv {β : Sort v} (b : β) : ∃ a, a = b := by simp only [my_exists_eq_I]\n\
               axiom my_exists_eq_T {α : Type u} {a' : α} : (∃ a, a = a') ↔ True\n\
               theorem sTu {β : Type u} (b : β) : ∃ a, a = b := by simp only [my_exists_eq_T]\n\
               theorem sTv {β : Type v} (b : β) : ∃ a, a = b := by simp only [my_exists_eq_T]\n\
               axiom my_imp_true {α : Sort u} : (α → True) ↔ True\n\
               theorem bN : Nat → True := by simp only [my_imp_true]\n\
               theorem bW {γ : Sort w} : γ → True := by simp only [my_imp_true]\n\
               axiom my_eq_comm {α : Sort u} {a b : α} : a = b ↔ b = a\n\
               theorem pT {α : Type} (a b : α) : (b = a) = (a = b) := by\n\
               \x20 simp only [my_eq_comm]\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("universe-polymorphic `Iff` simp lemmas must fire as Lean's do: {e}");
    }
}
