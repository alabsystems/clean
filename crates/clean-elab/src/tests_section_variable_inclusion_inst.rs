// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A section instance variable is a parameter of a `def` / `abbrev` /
//! `instance` only when the ELABORATED declaration uses it — Lean's
//! `removeUnusedVars` (`Lean/Elab/MutualDef.lean:593-609`). The surface
//! selection activates `[C α]` as soon as `α` is kept, because it cannot see
//! whether instance resolution reached it; kept unconditionally, every
//! definition of a `variable {α} [DecidableEq α]` section demanded a
//! `DecidableEq` instance at each use. Each fixture was ground-truthed on the
//! pinned v4.30.0-rc2 `lean` binary (2026-09-20) and is accepted there unless
//! the test says Lean refuses it; the `@`-applications pin the telescope Lean
//! prints with `#check @…`.

use crate::tests_section_variable_inclusion::{assert_all_accepted, run, verdict_of};

/// Lean: `@konst : {α : Type} → α → α`, `@pick : {α : Type} → [DecidableEq α]
/// → α → α → α`, `@both : {α β : Type} → [Inhabited β] → α → β → α × β`,
/// `@instMarker : {α : Type} → Marker (Option α)`. `NoDec` has no
/// `DecidableEq` instance, so `konst x`, `both x 1` and the `Marker (Option
/// NoDec)` search each fail while the phantom `[DecidableEq α]` is a parameter.
#[test]
fn test_section_vars_def_unused_activated_instance_is_not_a_parameter() {
    let src = "namespace D2\n\
               structure NoDec where\n\
               \x20 f : Nat → Nat\n\
               class Marker (α : Type) where\n\
               \x20 n : Nat\n\
               section S\n\
               variable {α : Type} [DecidableEq α] {β : Type} [Inhabited β]\n\
               def konst (a : α) : α := a\n\
               def pick (a b : α) : α := if a = b then a else b\n\
               def both (x : α) (y : β) : α × β := (x, default)\n\
               instance instMarker : Marker (Option α) := ⟨0⟩\n\
               end S\n\
               theorem konst_nodec (x : NoDec) : konst x = x := rfl\n\
               theorem konst_arity : @konst Nat 0 = 0 := rfl\n\
               theorem pick_arity : @pick Nat _ 1 1 = 1 := rfl\n\
               theorem both_arity (x : NoDec) : @both NoDec Nat _ x 1 = (x, 0) := rfl\n\
               def marker_nodec : Marker (Option NoDec) := inferInstance\n\
               theorem inst_arity : (@instMarker NoDec).n = 0 := rfl\n\
               end D2\n";
    assert_all_accepted(src, "a def keeps only the section instances its value uses");
}

/// The recorded parameter names follow the pruned telescope (`konst (a := 0)`),
/// an `abbrev` and a `by` body take the same rule, and an instance the value
/// DOES use stays. Lean: `@konstA : {α : Type} → α → α`, `@viaBy : {α : Type}
/// → α → α`, `@usesDec : {α : Type} → [DecidableEq α] → α → α → Bool`. Top
/// level: parameter names are recorded under the unqualified name.
#[test]
fn test_section_vars_def_pruned_instance_keeps_named_arguments_aligned() {
    let src = "section S\n\
               variable {α : Type} [DecidableEq α]\n\
               def konst (a : α) : α := a\n\
               abbrev konstA (a : α) : α := a\n\
               def viaBy (a : α) : α := by exact a\n\
               def usesDec (a b : α) : Bool := decide (a = b)\n\
               end S\n\
               theorem named : konst (a := 0) = 0 := rfl\n\
               theorem abbrev_arity : @konstA Nat 0 = 0 := rfl\n\
               theorem by_arity : @viaBy Nat 0 = 0 := rfl\n\
               theorem dec_arity : @usesDec Nat _ 0 0 = true := rfl\n";
    assert_all_accepted(src, "named arguments over a def whose instance was pruned");
}

/// The theorem rule is NOT this one: `withHeaderSecVars` keeps an
/// instance-implicit variable over kept variables whether or not anything
/// uses it. Lean: `@tkeep : ∀ {α : Type} [DecidableEq α] (a : α), a = a`
/// (with the `unusedSectionVars` linter naming `[DecidableEq α]`).
#[test]
fn test_section_vars_theorem_keeps_the_unused_instance_a_def_drops() {
    let src = "namespace D4\n\
               section S\n\
               variable {α : Type} [DecidableEq α]\n\
               theorem tkeep (a : α) : a = a := rfl\n\
               end S\n\
               theorem tkeep_arity : @tkeep Nat _ 0 = @tkeep Nat _ 0 := rfl\n\
               end D4\n";
    assert_all_accepted(src, "a theorem keeps the instance over its kept variable");
}

/// The refusal Lean makes: with `[DecidableEq α]` gone, `@konst Nat _ 0`
/// applies `konst` to one argument too many (pinned v4.30.0-rc2: `Function
/// expected at konst ?m.1 but this term has type Nat`). Clean accepted it
/// while the phantom instance parameter stood in that slot.
#[test]
fn test_section_vars_def_phantom_instance_slot_is_refused() {
    let src = "namespace D5\n\
               section S\n\
               variable {α : Type} [DecidableEq α]\n\
               def konst (a : α) : α := a\n\
               end S\n\
               theorem phantom_slot : @konst Nat _ 0 = 0 := rfl\n\
               end D5\n";
    let verdicts = run(src);
    assert!(
        verdict_of(&verdicts, "D5.konst").is_ok(),
        "the definition itself elaborates: {verdicts:#?}"
    );
    assert!(
        verdict_of(&verdicts, "D5.phantom_slot").is_err(),
        "`@konst Nat _ 0` has one argument too many; Lean refuses it: {verdicts:#?}"
    );
}

/// An auto-bound implicit (`γ`) is closed OUTSIDE the section binders, so the
/// pruning runs at an offset; the instance is still dropped from `konstAuto`
/// and kept by `pickAuto`. Lean: `@konstAuto : {α : Type} → {γ : Type u_1} →
/// α → List γ → α`, `@pickAuto : {α : Type} → [DecidableEq α] → {γ : Type u_1}
/// → α → α → List γ → α`. The uses are positional only: where Clean places an
/// auto-bound implicit in the telescope is a separate matter.
#[test]
fn test_section_vars_def_auto_bound_implicit_does_not_shift_the_pruning() {
    let src = "namespace D6\n\
               structure NoDec where\n\
               \x20 f : Nat → Nat\n\
               section S\n\
               variable {α : Type} [DecidableEq α]\n\
               def konstAuto (a : α) (l : List γ) : α := a\n\
               def pickAuto (a b : α) (l : List γ) : α := if a = b then a else b\n\
               end S\n\
               theorem auto_nodec (x : NoDec) : konstAuto x ([] : List Nat) = x := rfl\n\
               theorem auto_pick : pickAuto 1 1 ([] : List Nat) = 1 := rfl\n\
               end D6\n";
    assert_all_accepted(src, "pruning under an auto-bound implicit");
}
