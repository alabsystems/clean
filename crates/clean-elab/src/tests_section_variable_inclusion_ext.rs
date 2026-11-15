// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial near-misses of [`crate::tests_section_variable_inclusion`]:
//! the section-variable selection meets an `outParam` the header fills through
//! a section instance, named arguments over a pruned telescope, a dependent
//! `if` whose hypothesis shadows a section variable, and a tactic body or
//! instance field that reaches a section instance only through resolution or
//! through an anonymous binder. Each fixture was ground-truthed on the pinned
//! v4.30.0-rc2 `lean` binary (2026-09-13) and is accepted there; the
//! `@`-applications pin the telescope Lean prints with `#check @…`.

use crate::tests_section_variable_inclusion::assert_all_accepted;

/// RC1, the instance rule reads the ELABORATED header. `get_congr`'s header
/// names only `F`, but `Get.get f` elaborates to `@Get.get F β inst f` — `β`
/// is an `outParam` filled from the section instance — so Lean keeps `β` and
/// `[Get F β]`, then `[Inhabited β]` by the instance rule, and drops `γ` and
/// `[C2 F γ]`: `@get_congr : ∀ {F β : Type} [inst : Get F β] [Inhabited β]
/// (f g : F), f = g → Get.get f = Get.get g` (pinned v4.30.0-rc2, 2026-09-13),
/// for the `by` proof and the term proof alike. Deciding the instance rule on
/// the surface header prepended `F` alone and both theorems failed —
/// `failed to synthesize instance Get fvar#0 ?1` and a `Type mismatch`.
/// Before 2026-09-12 they elaborated with every section variable, and the
/// phantom `{γ} [C2 F γ]` broke each use (`failed to synthesize instance C2
/// Nat ?13`). The `@`-applications pin Lean's telescope; `[C2 F γ]` must not
/// survive into it.
#[test]
fn test_section_vars_theorem_out_param_instance_is_kept_from_the_elaborated_header() {
    let src = "namespace T7\n\
               class Get (F : Type) (β : outParam Type) where\n\
               \x20 get : F → β\n\
               instance : Get Nat Bool := ⟨fun n => n == 0⟩\n\
               class C2 (α β : Type) where\n\
               \x20 x : Nat\n\
               section\n\
               variable {F β : Type} [Get F β] [Inhabited β] {γ : Type} [C2 F γ]\n\
               theorem get_congr (f g : F) (h : f = g) : Get.get f = Get.get g := by rw [h]\n\
               theorem get_congr_term (f g : F) (h : f = g) : Get.get f = Get.get g := congrArg Get.get h\n\
               end\n\
               theorem use_by : Get.get (3 : Nat) = Get.get (3 : Nat) := get_congr 3 3 rfl\n\
               theorem use_term : Get.get (3 : Nat) = Get.get (3 : Nat) := get_congr_term 3 3 rfl\n\
               theorem by_arity : Get.get (3 : Nat) = Get.get (3 : Nat) :=\n\
               \x20 @get_congr Nat Bool _ ⟨true⟩ 3 3 rfl\n\
               theorem term_arity : Get.get (3 : Nat) = Get.get (3 : Nat) :=\n\
               \x20 @get_congr_term Nat Bool _ ⟨true⟩ 3 3 rfl\n\
               end T7\n";
    assert_all_accepted(src, "a section instance whose `outParam` the header fills");
}

/// The deferred instance rule drops what the elaborated header does not name
/// (`γ`, `[C3 F γ]`) from the registered telescope AND from the recorded
/// parameter names, so named arguments land on Lean's binders. Lean:
/// `@get2_congr : ∀ {F β : Type} [inst : Get2 F β] (f g : F), f = g → …`, and
/// `get2_congr (g := 3) (f := 3) rfl` elaborates. Before the deferral the
/// theorem did not elaborate at all; before 2026-09-12 (every section variable
/// for a `by` proof) it registered eight binders, and both uses below failed.
/// Top level: parameter names are recorded under the unqualified name.
#[test]
fn test_section_vars_deferred_theorem_named_arguments_follow_the_pruned_telescope() {
    let src = "class Get2 (F : Type) (β : outParam Type) where\n\
               \x20 get : F → β\n\
               instance : Get2 Nat Bool := ⟨fun n => n == 0⟩\n\
               class C3 (α β : Type) where\n\
               \x20 x : Nat\n\
               section\n\
               variable {F β : Type} [Get2 F β] {γ : Type} [C3 F γ]\n\
               theorem get2_congr (f g : F) (h : f = g) : Get2.get f = Get2.get g := by rw [h]\n\
               end\n\
               theorem get2_named : Get2.get (3 : Nat) = Get2.get (3 : Nat) :=\n\
               \x20 get2_congr (g := 3) (f := 3) rfl\n\
               theorem get2_arity : Get2.get (3 : Nat) = Get2.get (3 : Nat) :=\n\
               \x20 @get2_congr Nat Bool _ 3 3 rfl\n";
    assert_all_accepted(src, "named arguments of a theorem the deferred rule pruned");
}

/// RC2, the hypothesis of a dependent `if` shadows a section variable of the
/// same name in BOTH branches, and a section variable in the CONDITION is
/// used. Lean: `dif1 : (c : Prop) → [Decidable c] → Nat` (the section `n` is
/// not bound — each branch's `n` is the hypothesis) and `dif2 : Nat → Nat`.
#[test]
fn test_section_vars_dependent_if_hypothesis_shadows_a_section_variable() {
    let src = "namespace T11\n\
               section\n\
               variable (n : Nat) {β : Type}\n\
               def dif1 (c : Prop) [Decidable c] : Nat := if n : c then (fun _ => 1) n else (fun _ => 0) n\n\
               def dif2 : Nat := if hh : n = 0 then 1 else 0\n\
               end\n\
               theorem dif1_arity : @dif1 True instDecidableTrue = 1 := rfl\n\
               theorem dif2_arity : @dif2 0 = 1 := rfl\n\
               end T11\n";
    assert_all_accepted(
        src,
        "a dependent `if` whose hypothesis shadows a section variable",
    );
}

/// RC3 reads the ELABORATED value: a tactic body that reaches a section
/// instance only through instance resolution keeps it, although the surface
/// never names it. Lean: `@dnat : [inst : Inhabited Nat] → Nat`. Before the
/// pruning, the unused `β` made `dnat_arity` `unsolved metavariables ?[1]`.
#[test]
fn test_section_vars_def_tactic_body_keeps_a_local_instance_resolution_picked() {
    let src = "namespace T10\n\
               section\n\
               variable [inst : Inhabited Nat] {β : Type}\n\
               def dnat : Nat := by exact default\n\
               end\n\
               theorem dnat_arity : @dnat ⟨5⟩ = 5 := rfl\n\
               end T10\n";
    assert_all_accepted(src, "a local instance a tactic body resolves to");
}

/// RC3 for an instance in a section whose instance-implicit variable is
/// ANONYMOUS: the pruning matches its request on the binders' local names,
/// and an anonymous `[Inhabited α]` must match too. Lean: `instHT : HasTrue
/// Nat`. Unpruned it was `failed to synthesize instance T9.HasTrue Nat`.
#[test]
fn test_section_vars_instance_with_tactic_field_drops_an_anonymous_section_instance() {
    let src = "namespace T9\n\
               class HasTrue (α : Type) : Prop where\n\
               \x20 t : True\n\
               section\n\
               variable {α : Type} [Inhabited α] {β : Type}\n\
               instance instHT : HasTrue Nat where\n\
               \x20 t := by trivial\n\
               end\n\
               theorem useHT : HasTrue Nat := inferInstance\n\
               theorem instHT_arity : HasTrue Nat := @instHT\n\
               end T9\n";
    assert_all_accepted(
        src,
        "an instance whose section has an anonymous instance variable",
    );
}

/// RC3's theorem half end to end: a HEADER the surface cannot scan (a named
/// argument) prepends every section variable, and `withHeaderSecVars` over
/// the elaborated statement keeps the `include`d `hα` and, through its type,
/// `α`, while the unused `β` and `[Inhabited β]` go. Lean: `@tinc : ∀ {α :
/// Type}, Nonempty α → ∀ (x : Nat), fnb x 0 = x`. Top level: named arguments
/// resolve through parameter names recorded under the unqualified name.
#[test]
fn test_section_vars_unscannable_theorem_header_keeps_included_variables() {
    let src = "def fnb (n m : Nat) : Nat := n + m\n\
               section\n\
               variable {α : Type} (hα : Nonempty α) {β : Type} [Inhabited β]\n\
               include hα\n\
               theorem tinc (x : Nat) : fnb (n := x) 0 = x := by exact Nat.add_zero x\n\
               end\n\
               theorem tinc_arity : fnb (n := 3) 0 = 3 := @tinc Nat ⟨0⟩ 3\n";
    assert_all_accepted(src, "an unscannable theorem header under `include`");
}

/// Every anonymous instance binder is named `_`, and the dependency closure
/// used to key on names: activating `[Inhabited α]` put `_` in the used set,
/// which reached `[Inhabited β]` — and through its type the unused `β`. The
/// phantom `{β}` then made every use `failed to synthesize instance Inhabited
/// ?3` (before this branch and on it). Lean: `@dflt : {α : Type} →
/// [Inhabited α] → α → α`.
#[test]
fn test_section_vars_anonymous_instance_does_not_reach_another_anonymous_instance() {
    let src = "namespace U2\n\
               section\n\
               variable {α : Type} [Inhabited α] {β : Type} [Inhabited β]\n\
               def dflt (x : α) : α := default\n\
               end\n\
               theorem dflt_use : dflt (3 : Nat) = 0 := rfl\n\
               theorem dflt_arity : @dflt Nat ⟨7⟩ 3 = 7 := rfl\n\
               end U2\n";
    assert_all_accepted(src, "a section with two anonymous instance variables");
}
