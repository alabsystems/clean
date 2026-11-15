// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Sort*` / `Type*` bind a fresh RIGID universe parameter, never an
//! assignable level metavariable — Mathlib's `Mathlib/Tactic/TypeStar.lean`:
//! `elab "Sort*" : term => return .sort <| ← mkFreshLevelParam`.
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12) with that elaborator (and its `Type*` twin) copied verbatim
//! into an `import Lean` file: the accepted declarations elaborate there as
//! written, `@A.extend` registers at `{α : Sort u_1} → {β : Sort u_2} →
//! {γ : Sort u_3}`, and `n4`/`n5` fail with `Application type mismatch … of
//! sort `Type u_1` but is expected to have type Prop`.

use crate::test_support::file_verdicts::{run_file, verdict_of};

const PROP_ONLY: &str = "universe u\n\
                         axiom chooseX {α : Sort u} {p : α → Prop} (h : Exists p) : α\n\
                         axiom propDec (p : Prop) : Decidable p\n\
                         attribute [instance 10] propDec\n\
                         axiom exists_prop_decidable' {p : Prop} (P : p → Prop) [Decidable p]\n\
                         \x20   [∀ h, Decidable (P h)] : Decidable (∃ h, P h)\n\
                         attribute [instance] exists_prop_decidable'\n";

/// `Mathlib/Logic/Function/Basic.lean`'s `Function.extend` over `variable {α
/// β γ : Sort*}`: instance search for `Decidable (∃ a, f a = b)` tried the
/// Prop-only `exists_prop_decidable` (`Exists.{0}`), whose level check
/// assigned `Sort*`'s level `:= 0` — so `extend` was ACCEPTED, registered at
/// `α : Prop`, and every later use at a `Type` carrier failed `universe level
/// conflict: 0 vs 1` (`extend_id`, `Injective.surjective_comp_right'`). With
/// the parameter rigid the candidate's level check fails and the search moves
/// on, as in Lean. `B` (explicit `universe u1 u2 u3`) is the control that
/// always passed.
#[test]
fn test_sort_star_prop_only_instance_does_not_narrow_the_carrier() {
    let verdicts = run_file(&format!(
        "{PROP_ONLY}\
         namespace A\n\
         variable {{α β γ : Sort*}}\n\
         noncomputable def extend (f : α → β) (g : α → γ) (j : β → γ) : β → γ := fun b ↦\n\
         \x20 if h : ∃ a, f a = b then g (chooseX h) else j b\n\
         end A\n\
         theorem chkA {{α β γ : Type}} (f : α → β) (g : α → γ) (j : β → γ) : True :=\n\
         \x20 (fun _ => True.intro) (A.extend f g j)\n\
         theorem chkAP {{α : Prop}} {{β γ : Type}} (f : α → β) (g : α → γ) (j : β → γ) : True :=\n\
         \x20 (fun _ => True.intro) (A.extend f g j)\n\
         namespace B\n\
         universe u1 u2 u3\n\
         variable {{α : Sort u1}} {{β : Sort u2}} {{γ : Sort u3}}\n\
         noncomputable def extend (f : α → β) (g : α → γ) (j : β → γ) : β → γ := fun b ↦\n\
         \x20 if h : ∃ a, f a = b then g (chooseX h) else j b\n\
         end B\n\
         theorem chkB {{α β γ : Type}} (f : α → β) (g : α → γ) (j : β → γ) : True :=\n\
         \x20 (fun _ => True.intro) (B.extend f g j)\n\
         noncomputable def ext2 {{α β : Type*}} (f : α → β) (b : β) : Option α :=\n\
         \x20 if h : ∃ a, f a = b then some (chooseX h) else none\n"
    ));
    for name in ["A.extend", "chkA", "chkAP", "B.extend", "chkB", "ext2"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}` elaborates in Lean with `Sort*` a rigid parameter: {e}");
        }
    }
}

/// A `Sort*` / `Type*` parameter can never be solved away: `Not α` needs
/// `α : Prop`, which Lean refuses for both spellings. The level HOLE `Sort _`
/// is a metavariable and still narrows (Lean: `@n6 : {α : Prop} → Prop`).
#[test]
fn test_sort_star_parameter_is_never_assigned() {
    let verdicts = run_file(
        "def n4 {α : Sort*} : Prop := Not α\n\
         def n5 {α : Type*} : Prop := Not α\n\
         def n6 {α : Sort _} : Prop := Not α\n",
    );
    for name in ["n4", "n5"] {
        assert!(
            verdict_of(&verdicts, name).is_err(),
            "`{name}`: a `*` universe is a rigid parameter; Lean refuses `Not α` here"
        );
    }
    if let Err(e) = verdict_of(&verdicts, "n6") {
        panic!("`n6`: a `Sort _` hole is a metavariable and may be solved to 0: {e}");
    }
}
