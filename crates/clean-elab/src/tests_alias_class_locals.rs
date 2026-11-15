// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A local whose type is a REDUCIBLE ALIAS of a class is a local instance, as
//! Lean's `isClass?` reads it (`Lean/Meta/Basic.lean`: `isClassQuick?` defers
//! any non-class definition head to `isClassExpensive?`, which is
//! `withReducible do forallTelescopeReducing type … isClassApp?`). So
//! `(h : DecidableLE α)`, `{h : DecidableLT α}`, `(h : DecidableEq α)` and —
//! above all — the class FIELD `toDecidableLE : DecidableLE α` that Mathlib's
//! `LinearOrder` declares and then uses two fields later
//! (`min_def : ∀ a b, min a b = if a ≤ b then a else b`) answer `Decidable`
//! goals without being written `[…]`.
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-20): the accepted declarations elaborate there as written
//! (warnings only), and every declaration asserted refused here fails there
//! with `failed to synthesize instance of type class Decidable (…)`.

use crate::test_support::file_verdicts::{
    assert_all_accepted, is_synthesis_failure, run_file, verdict_of,
};

const ALIASES: &str = "universe u\n\
                       abbrev MyDecRel {α : Sort u} (r : α → α → Prop) :=\n\
                       \x20 (a b : α) → Decidable (r a b)\n\
                       abbrev MyDecLT (α : Type u) [LT α] := MyDecRel (α := α) (· < ·)\n\
                       abbrev MyDecLE (α : Type u) [LE α] := MyDecRel (α := α) (· ≤ ·)\n";

/// An explicit or implicit BINDER of alias type is a local instance: `k1`
/// (a user alias of `Decidable` over `≤`), `k2` (implicit binder, `<`), `k3`
/// (the prelude's own `DecidableEq`), and `k5`, the control whose binder is
/// already spelled as the unfolded telescope.
#[test]
fn test_alias_typed_binder_is_local_instance_accepted() {
    let verdicts = run_file(&format!(
        "{ALIASES}\
         def k1 {{α : Type u}} [LE α] (h : MyDecLE α) (a b : α) : Nat := if a ≤ b then 0 else 1\n\
         def k2 {{α : Type u}} [LT α] {{h : MyDecLT α}} (a b : α) : Decidable (a < b) :=\n\
         \x20 inferInstance\n\
         def k3 {{α : Type u}} (h : DecidableEq α) (a b : α) : Nat := if a = b then 0 else 1\n\
         def k5 {{α : Type u}} [LE α] (h : (a b : α) → Decidable (a ≤ b)) (a b : α) : Nat :=\n\
         \x20 if a ≤ b then 0 else 1\n"
    ));
    for name in ["k1", "k2", "k3", "k5"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: an alias-typed binder must answer its `Decidable` goal: {e}");
        }
    }
    assert_all_accepted(&verdicts, "the whole fixture elaborates in Lean");
}

/// The alias-typed local is still MATCHED against the goal, never grabbed: a
/// `MyDecLE α` local does not answer `Decidable (a < b)` (another relation),
/// nor `Decidable (a ≤ b)` at another carrier.
#[test]
fn test_alias_typed_binder_wrong_relation_or_carrier_is_refused() {
    let verdicts = run_file(&format!(
        "{ALIASES}\
         def bad1 {{α : Type u}} [LE α] [LT α] (h : MyDecLE α) (a b : α) : Nat :=\n\
         \x20 if a < b then 0 else 1\n\
         def bad2 {{α β : Type u}} [LE α] [LE β] (h : MyDecLE α) (a b : β) : Nat :=\n\
         \x20 if a ≤ b then 0 else 1\n"
    ));
    for name in ["bad1", "bad2"] {
        let bad = verdict_of(&verdicts, name)
            .as_ref()
            .expect_err("Lean fails `failed to synthesize Decidable (…)` here too");
        assert!(
            is_synthesis_failure(bad),
            "`{name}`: the refusal must be an instance-synthesis failure: {bad}"
        );
    }
}

const FIELD_CLASSES: &str = "class MyLO (α : Type u) extends LE α, Min α where\n\
     \x20 toDecidableLE : MyDecLE α\n\
     \x20 toDecidableEq : DecidableEq α\n\
     \x20 min_def : ∀ a b : α, min a b = if a ≤ b then a else b\n\
     \x20 eq_def : ∀ a b : α, (if a = b then a else b) = b\n\
     structure Picker (α : Type u) [LE α] where\n\
     \x20 dec : MyDecLE α\n\
     \x20 pick : α → α → α := fun a b => if a ≤ b then a else b\n\
     class D1 (α : Type u) extends LE α where\n\
     \x20 dec : (a b : α) → Decidable (a ≤ b)\n\
     \x20 h : ∀ a b : α, (if a ≤ b then a else b) = a\n";

/// A class FIELD of alias type (and one spelled as the unfolded telescope) is
/// a local instance for every LATER field — the shape of Mathlib's
/// `LinearOrder` (`toDecidableLE : DecidableLE α`, then `min_def`).
///
/// The `use*` declarations pin the classes' UNIVERSE PARAMETERS as well. The
/// field's `Decidable (a ≤ b)` goal is answered by the local only after every
/// global candidate was tried and rolled back, and each universe-polymorphic
/// candidate leaves its freshened level names in `universe_params`; the
/// structure's self-occurrence carries all of them, and counting it as a USE
/// registered `D1.{u, ?u_1, …}`. `by exact inst` then died on `cannot assign
/// rigid universe parameter ?u_1 := ?u_3`. Lean registers `D1.{u}`.
#[test]
fn test_alias_typed_class_field_is_local_instance_for_later_fields() {
    let verdicts = run_file(&format!(
        "{ALIASES}{FIELD_CLASSES}\
         def useLO {{α : Type u}} [inst : MyLO α] : MyLO α := by exact inst\n\
         def useD1 {{α : Type u}} [inst : D1 α] : D1 α := by exact inst\n\
         def usePicker {{α : Type u}} [LE α] (s : Picker α) : Picker α := by exact s\n"
    ));
    for name in ["useLO", "useD1", "usePicker"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: the class must elaborate at exactly its declared universe: {e}");
        }
    }
    assert_all_accepted(&verdicts, "the whole fixture elaborates in Lean");
}

/// The field is matched, not grabbed: a `MyDecLE α` field does not answer a
/// later field's `Decidable (a < b)`.
#[test]
fn test_alias_typed_class_field_wrong_relation_is_refused() {
    let verdicts = run_file(&format!(
        "{ALIASES}\
         class BadLT (α : Type u) extends LE α, LT α where\n\
         \x20 toDecidableLE : MyDecLE α\n\
         \x20 bad : ∀ a b : α, (if a < b then a else b) = b\n"
    ));
    let bad = verdict_of(&verdicts, "BadLT")
        .as_ref()
        .expect_err("Lean fails `failed to synthesize Decidable (a < b)` here too");
    assert!(
        is_synthesis_failure(bad),
        "the refusal must be an instance-synthesis failure: {bad}"
    );
}
