// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial shapes for the section-variable selection
//! (`crate::section_var_selection`, `crate::infer::section_prune`): shadowing
//! in every position, the telescope a use must supply (`@f …`), and the
//! refusals Lean makes once the phantom binders are gone. Each fixture was run
//! on the pinned v4.30.0-rc2 `lean` binary (2026-09-20): it is accepted there
//! unless the test says which declarations Lean refuses. Driven through the
//! same preprocess-then-elaborate loop `clean check` runs.

use crate::tests_section_variable_inclusion::{assert_all_accepted, run, verdict_of};

/// The `Mathlib/Order/Basic.lean` row `instance : LinearOrder Empty :=
/// .ofSubsingleton` (and `PEmpty`, `PUnit`): `abbrev
/// LinearOrder.ofSubsingleton {α : Type*} [Subsingleton α] : LinearOrder α
/// where …` has a `by` field, so under the file's `variable {ι α β : Type*}
/// {π : ι → Type*}` it was registered with all four section variables — its
/// own `{α}` SHADOWING the section's — and every `.ofSubsingleton` left
/// `unsolved metavariables ?[0, 1, 2, 3]`, one per phantom binder. Lean:
/// `@LO.ofSub : {α : Type} → [Sub1 α] → LO α`.
#[test]
fn test_section_vars_abbrev_shadowing_own_binder_with_tactic_field_takes_no_section_variable() {
    let src = r"namespace Lead1
class Sub1 (α : Type) : Prop where
  allEq : ∀ a b : α, a = b
class LO (α : Type) where
  le : α → α → Prop
  le_refl : ∀ a, le a a
inductive E0 : Type
instance : Sub1 E0 := ⟨fun a _ => nomatch a⟩
instance : Sub1 Unit := ⟨fun _ _ => rfl⟩
section S
variable {ι α β : Type} {π : ι → Type}
abbrev LO.ofSub {α : Type} [Sub1 α] : LO α where
  le _ _ := True
  le_refl _ := by exact True.intro
instance : LO E0 := .ofSub
instance instLOUnit : LO Unit := .ofSub
def viaAt : LO Unit := @LO.ofSub Unit _
end S
def viaAtOutside : LO E0 := @LO.ofSub E0 _
theorem le_unit : @LO.le Unit instLOUnit () () := True.intro
end Lead1
";
    assert_all_accepted(src, "the `LinearOrder.ofSubsingleton` shape");
}

/// The same row with the section variables in their own universes, as
/// `Type*` makes them: the dropped binders take their universe parameters
/// with them, so `.ofSub` has exactly the abbrev's own level to solve.
#[test]
fn test_section_vars_abbrev_shadowing_own_binder_drops_the_section_universes() {
    let src = r"namespace Lead2
universe u v w x
class Sub1 (α : Type u) : Prop where
  allEq : ∀ a b : α, a = b
class LO (α : Type u) where
  le : α → α → Prop
  le_refl : ∀ a, le a a
instance : Sub1 PUnit.{u+1} := ⟨fun _ _ => rfl⟩
instance : Sub1 PEmpty.{u+1} := ⟨fun a _ => nomatch a⟩
section S
variable {ι : Type u} {α : Type v} {β : Type w} {π : ι → Type x}
abbrev LO.ofSub {α : Type u} [Sub1 α] : LO α where
  le _ _ := True
  le_refl _ := by exact True.intro
instance : LO PEmpty := .ofSub
instance instLOPUnit : LO PUnit := .ofSub
end S
def viaAtOutside : LO PUnit.{u+1} := @LO.ofSub.{u} PUnit.{u+1} _
end Lead2
";
    assert_all_accepted(src, "the `LinearOrder.ofSubsingleton` shape over universes");
}

/// A telescope binds left to right: in `(h : a = a) (a : Bool)` the `a` of
/// `h`'s type is the SECTION variable, and the declaration's own `a` shadows
/// it only from there on. Lean: `@shadow_late : ∀ (a : Nat), a = a → ∀ (a :
/// Bool), a = a`, `@shadow_dflt : (a : Nat) → optParam Nat a → Bool → Bool`.
/// Removing own-binder names from the used set by name alone dropped the
/// section `a`: `shadow_late` died `unsolved metavariables ?[0]` (its `a`
/// auto-bound at an unknown sort) and `shadow_dflt` registered with an
/// auto-bound IMPLICIT `a`, so `@shadow_dflt 3 3 true` was refused.
#[test]
fn test_section_vars_mention_before_the_shadowing_binder_keeps_the_section_variable() {
    let src = r"namespace B1
section S
variable (a : Nat) {α : Type} (x : α)
theorem shadow_late (h : a = a) (a : Bool) : a = a := rfl
theorem shadow_late_by (h : a = a) (a : Bool) : a = a := by exact Eq.refl a
def shadow_dflt (n : Nat := a) (a : Bool) : Bool := a
def shadow_by (h : a = a) (a : Bool) : Bool := by exact a
end S
theorem u1 : true = true := shadow_late 3 rfl true
theorem u1at : true = true := @shadow_late 3 rfl true
theorem u2at : true = true := @shadow_late_by 3 rfl true
def u3at : Bool := @shadow_dflt 3 3 true
def u4at : Bool := @shadow_by 3 rfl true
end B1
";
    assert_all_accepted(
        src,
        "a section variable named before an own binder shadows it",
    );
}

/// A binder INSIDE the value that shadows a section variable — `fun a`, a
/// `match` pattern variable, `let a`, the hypothesis of `if a : c` — is not a
/// use of it, while a use in the condition or in one branch only is. Lean:
/// `@lam_shadow : Nat → Nat`, `@dif_shadow : Nat → Nat`, `@dif_uses : Nat →
/// Nat → Nat`, `@dif_else : (Nat → Nat) → Nat → Nat`, `@by_f : (Nat → Nat) →
/// Nat → Nat`, `by_none : Nat`.
#[test]
fn test_section_vars_value_binders_shadowing_a_section_variable_do_not_use_it() {
    let src = r"namespace B1b
section S
variable (a : Nat) {α : Type} (x : α) (f : Nat → Nat)
def lam_shadow : Nat → Nat := fun a => a
def match_shadow (n : Nat) : Nat := match n with
  | 0 => 0
  | a + 1 => a
def let_shadow : Nat := let a := 5; a
def by_none : Nat := by exact 7
def by_f (n : Nat) : Nat := by exact f n
def dif_shadow (n : Nat) : Nat := if a : n = 0 then 0 else n
def dif_uses (n : Nat) : Nat := if h : n = a then 0 else n
def dif_else (n : Nat) : Nat := if h : n = 0 then 0 else f n
end S
def u_lam_at : Nat → Nat := @lam_shadow
def u_match_at : Nat := @match_shadow 3
def u_let : Nat := let_shadow
def u_by_none : Nat := by_none
def u_by_f_at : Nat := @by_f (fun n => n) 2
def u_dif_shadow_at : Nat := @dif_shadow 3
def u_dif_uses_at : Nat := @dif_uses 1 3
def u_dif_else_at : Nat := @dif_else (fun n => n) 3
end B1b
";
    assert_all_accepted(src, "value-level binders shadowing a section variable");
}

/// The refusal half of the pruning: once the phantom binders are gone, a use
/// that still supplies them is ill-typed — Lean refuses `bad1` … `bad6`
/// (`Application type mismatch` / `Function expected`) and accepts the rest.
/// A pruning that only ever made more things pass would not notice a
/// telescope it failed to shorten.
#[test]
fn test_section_vars_pruned_telescope_refuses_the_phantom_slots() {
    let src = r"namespace R2
section S
variable {α : Type} {β : Type} (a : α) (b : β) [Inhabited β]
theorem tby (x : α) : x = x := by exact Eq.refl x
def dby (x : α) : α := by exact x
def dif (n : Nat) : Nat := if h : n = 0 then 0 else n
abbrev aby : α := by exact a
end S
theorem bad1 : (1 : Nat) = 1 := @tby Nat Bool 1
theorem bad2 : (1 : Nat) = 1 := tby 1 true 1
def bad3 : Nat := @dby Nat Bool 1
def bad4 : Nat := @dif Nat 1
def bad5 : Nat := @aby Nat Bool 1 true
def bad6 : Nat := dby 1 true
theorem ok1 : (1 : Nat) = 1 := @tby Nat 1
def ok3 : Nat := @dby Nat 1
def ok4 : Nat := @dif 1
def ok5 : Nat := @aby Nat 1
end R2
";
    let verdicts = run(src);
    for bad in ["bad1", "bad2", "bad3", "bad4", "bad5", "bad6"] {
        assert!(
            verdict_of(&verdicts, &format!("R2.{bad}")).is_err(),
            "Lean refuses `{bad}` — it supplies a section variable the declaration \
             does not take: {verdicts:#?}"
        );
    }
    for ok in ["tby", "dby", "dif", "aby", "ok1", "ok3", "ok4", "ok5"] {
        assert!(
            verdict_of(&verdicts, &format!("R2.{ok}")).is_ok(),
            "Lean accepts `{ok}`: {verdicts:#?}"
        );
    }
}

/// A theorem's proof is elaborated in the context its header selects, however
/// the proof is spelled. Lean refuses all three (`Unknown identifier 'hp'`
/// twice, then `assumption` failing with only `p : Prop` in context), and
/// `@konst2 Nat _ 0` because `konst2` takes no instance; it keeps `[Inhabited
/// α]` on the theorem `good`, so `@good Nat 0` is refused and `@good Nat _ 0`
/// accepted.
#[test]
fn test_section_vars_theorem_proof_cannot_reach_an_omitted_variable_by_any_spelling() {
    let src = r"namespace R1
section S
variable {α : Type} (a : α) {p : Prop} (hp : p) [inst : Inhabited α]
theorem bad_term : p := hp
theorem bad_by : p := by exact hp
theorem bad_assume : p := by assumption
def konst2 (x : α) : α := x
theorem good (x : α) : x = x := rfl
end S
def bad_use : Nat := @konst2 Nat _ 0
theorem good_use : (0 : Nat) = 0 := @good Nat _ 0
theorem bad_good_use : (0 : Nat) = 0 := @good Nat 0
end R1
";
    let verdicts = run(src);
    for bad in [
        "bad_term",
        "bad_by",
        "bad_assume",
        "bad_use",
        "bad_good_use",
    ] {
        assert!(
            verdict_of(&verdicts, &format!("R1.{bad}")).is_err(),
            "Lean refuses `{bad}`: {verdicts:#?}"
        );
    }
    for ok in ["konst2", "good", "good_use"] {
        assert!(
            verdict_of(&verdicts, &format!("R1.{ok}")).is_ok(),
            "Lean accepts `{ok}`: {verdicts:#?}"
        );
    }
}

/// Nested sections: an inner declaration with a `by` body is handed the
/// variables of BOTH sections and keeps only what it uses, whichever section
/// declared it; the inner variables are gone after `end Inner`. Lean:
/// `@outer_only : {α : Type} → α → α`, `@both_vars : {α : Type} → α → {β :
/// Type} → β → α × β`, `@outer_thm : ∀ {α : Type} (a : α), a = a`, `@autob :
/// {k : Nat} → Fin k → Nat` (an auto-bound implicit ahead of the pruned
/// telescope), `@after_inner : {α : Type} → α → α`.
#[test]
fn test_section_vars_nested_sections_keep_only_the_used_variables_of_each() {
    let src = r"namespace A3
section Outer
variable {α : Type} (a : α)
section Inner
variable {β : Type} (b : β) (h : a = a)
def outer_only : α := by exact a
def both_vars : α × β := by exact (a, b)
theorem outer_thm : a = a := by exact Eq.refl a
def autob (x : Fin k) : Nat := by exact x.val
end Inner
def after_inner : α := by exact a
end Outer
def u1at : Nat := @outer_only Nat 3
def u2 : Nat × Bool := both_vars 3 true
def u2at : Nat × Bool := @both_vars Nat 3 Bool true
theorem u3at : (3 : Nat) = 3 := @outer_thm Nat 3
def u4 (y : Fin 2) : Nat := autob y
def u4at (y : Fin 2) : Nat := @autob 2 y
def u5at : Nat := @after_inner Nat 3
end A3
";
    assert_all_accepted(src, "nested sections");
}

/// A dropped section variable takes its universe parameter with it: the
/// explicit level lists below have exactly the length Lean's have
/// (`onlyA.{u}`, `pairAB.{u, v}`, `thmC.{w}`, `idA.{u}`), and a named argument
/// still reaches a kept section variable of a `by` definition.
#[test]
fn test_section_vars_pruned_binders_take_their_universe_parameters_along() {
    let src = r"namespace B4
universe u v w
section S
variable {α : Type u} {β : Type v} {γ : Sort w} (a : α) (b : β) (c : γ)
def onlyA : α := by exact a
def onlyB (n : Nat) : β × Nat := by exact (b, n)
def pairAB : α × β := by exact (a, b)
theorem thmC : c = c := by exact Eq.refl c
def nothing : Nat := by exact 3
abbrev idA (x : α) : α := by exact x
end S
def u1at : Nat := @onlyA.{0} Nat 3
def u2named : Bool × Nat := onlyB (n := 1) (b := true)
def u3 : Nat × Bool := @pairAB.{0, 0} Nat Bool 1 true
theorem u4at : (1 : Nat) = 1 := @thmC.{1} Nat 1
def u5 : Nat := nothing
def u6 : Nat := @idA.{0} Nat 3
end B4
";
    assert_all_accepted(src, "universe parameters of pruned section variables");
}
