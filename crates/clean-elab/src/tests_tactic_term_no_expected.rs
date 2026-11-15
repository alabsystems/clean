// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A tactic term that has no expected type of its own is elaborated with NO
//! expected type — not against whatever the enclosing TERM elaboration left
//! armed.
//!
//! `TacticEval::elaborate` is a bare `ElabCtx::elaborate`, which does not clear
//! `current_expected_type`. So `cases <term>` and `have h := <term>` elaborated
//! their argument against the ambient expected type: under a pattern lambda
//! over `Wrp α p`, `SS.elim x y`'s implicit carrier was fixed to `Wrp α p`
//! before its explicit `x : α` was checked — `expected Wrp fvar#0 fvar#2, got
//! cannot unify a free variable with an application: fvar#0 vs Wrp fvar#0
//! fvar#2`, the face of `Mathlib/Logic/Basic.lean`'s
//! `instance [Subsingleton α] (p) : Subsingleton (Subtype p)`.
//!
//! Lean elaborates both with `expectedType? = none`:
//! `Lean/Elab/Tactic/Induction.lean`:895 `elabTerm view.term none` (and :1040
//! for `induction`), and `have h := e` with no ascription goes through
//! `elabTermEnsuringType` with `none`. The fixtures below are accepted by the
//! pinned v4.30.0-rc2 binary.
//!
//! Scope, measured: this does NOT close the Mathlib row. Behind it is a second
//! wall — `rfl` cannot close an equality of two structure values differing only
//! in a PROOF field — so the `cases … ; rfl` spelling stays red for a different
//! reason and is not pinned here.

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

const BASE: &str = "class SS (α : Type) where\n\
                    \x20 elim : ∀ (a b : α), a = b\n\
                    structure Wrp (α : Type) (p : α → Prop) where\n\
                    \x20 val : α\n\
                    \x20 prop : p val\n\
                    axiom mkSS : ∀ {β : Type}, (∀ a b : β, a = b) → SS β\n\
                    axiom wrpEq : ∀ {α : Type} {p : α → Prop} (x y : α) (hx : p x) (hy : p y),\n\
                    \x20 x = y → Wrp.mk x hx = Wrp.mk y hy\n\
                    structure Wrp2 (α : Type) (q : Prop) where\n\
                    \x20 val : α\n\
                    \x20 prop : q\n\
                    axiom wrpEq2 : ∀ {α : Type} {q : Prop} (x y : α) (hx : q) (hy : q),\n\
                    \x20 x = y → Wrp2.mk x hx = Wrp2.mk y hy\n";

#[test]
fn test_have_without_ascription_elaborates_with_no_expected_type() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}instance instWrpH {{α : Type}} [SS α] (p : α → Prop) : SS (Wrp α p) :=\n\
         \x20 mkSS (fun ⟨x, hx⟩ ⟨y, hy⟩ => by\n\
         \x20   have hh := SS.elim x y\n\
         \x20   exact wrpEq x y hx hy hh)\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`have hh := SS.elim x y` must not inherit the ambient expected type: {e}");
    }
}

#[test]
fn test_cases_on_a_term_elaborates_with_no_expected_type() {
    let mut env = Environment::with_prelude();
    // `Wrp2`'s second field does NOT depend on the first. The dependent
    // spelling (`Wrp`, and Mathlib's own `Subtype`) hits a SECOND, unrelated
    // wall behind this one — `cases <TERM>` on an equation does not substitute
    // dependent HYPOTHESES the way `cases <hyp-name>` does — which is a
    // separate root cause and is not what this test is about.
    let src = format!(
        "{BASE}instance instWrp2C {{α : Type}} [SS α] (q : Prop) : SS (Wrp2 α q) :=\n\
         \x20 mkSS (fun ⟨x, hx⟩ ⟨y, hy⟩ => by\n\
         \x20   cases SS.elim x y\n\
         \x20   exact wrpEq2 x x hx hy (Eq.refl x))\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`cases SS.elim x y` must not inherit the ambient expected type: {e}");
    }
}

#[test]
fn test_have_with_an_ascription_still_uses_it() {
    let mut env = Environment::with_prelude();
    // The must-not-break: `have h : T := e` keeps elaborating `e` against `T`,
    // which is the only way a polymorphic `rfl` is pinned.
    let src = "theorem asc (n : Nat) : n + 0 = n := by\n\
               \x20 have h : n + 0 = n := rfl\n\
               \x20 exact h\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`have h : T := e` must keep its ascription as the expected type: {e}");
    }
}

#[test]
fn test_cases_on_a_named_hypothesis_still_works() {
    let mut env = Environment::with_prelude();
    // The identifier discriminant never went through this path and must not
    // start to.
    let src = "theorem viaName (p q : Prop) (h : p ∨ q) : q ∨ p := by\n\
               \x20 cases h with\n\
               \x20 | inl hp => exact Or.inr hp\n\
               \x20 | inr hq => exact Or.inl hq\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`cases <hypothesis>` must stay green: {e}");
    }
}
