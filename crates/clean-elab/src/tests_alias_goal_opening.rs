// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An ALIAS goal (`DecidableEq α`, `DecidablePred p`) is opened the way Lean
//! opens every instance goal (`Lean/Meta/SynthInstance.lean`, `preprocess` /
//! `getInstances`: `forallTelescopeReducing`) once its own bucket has no
//! answer, and `infer_instance` is Lean's `exact inferInstance`
//! (`Init/Tactics.lean`).
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12): the accepted declarations elaborate there as written, and
//! each declaration asserted refused here fails there with `failed to
//! synthesize instance`.

use crate::test_support::file_verdicts::{
    assert_all_accepted, is_synthesis_failure, run_file, verdict_of,
};

const MY_CLASSICAL: &str = "universe u\n\
                            abbrev MyDecPred {α : Sort u} (p : α → Prop) := (a : α) → Decidable (p a)\n\
                            abbrev MyDecRel {α : Sort u} (r : α → α → Prop) :=\n\
                            \x20 (a b : α) → Decidable (r a b)\n\
                            axiom natZeroDec : MyDecPred (fun n : Nat => n = 0)\n\
                            attribute [instance] natZeroDec\n\
                            axiom natEqDec : MyDecRel (fun a b : Nat => a = b)\n\
                            attribute [instance] natEqDec\n\
                            namespace MyClassical\n\
                            axiom propDec (p : Prop) : Decidable p\n\
                            noncomputable scoped instance (priority := low) myPropDecidable\n\
                            \x20   (p : Prop) : Decidable p := propDec p\n";

/// An ALIAS GOAL no alias-filed instance answers is opened as Lean opens every
/// goal (`forallTelescopeReducing`) and its conclusion searched as the final
/// class. `MyDecPred`/`MyDecRel` are registered as classes by the instance
/// filed under each, exactly as `clean-olean` registers Mathlib's
/// `DecidablePred`/`DecidableRel`; their goals and `DecidableEq α` then
/// resolve from a scoped `Decidable p` instance — Mathlib's
/// `Classical.decPred`/`decRel`/`decEq := by infer_instance` inside
/// `namespace Classical` (`Mathlib/Logic/Basic.lean`) — and `DecidableEq α`
/// from a local `[∀ a b, Decidable (a = b)]`. Lean: `b3` is
/// `fun a b => MyClassical.myPropDecidable (a = b)` and `k4` is `inst`.
/// `b0`–`b3` and `k4t` go through the `infer_instance` TACTIC, which never
/// called the resolver before.
#[test]
fn test_alias_goal_is_opened_when_its_bucket_fails() {
    let verdicts = run_file(&format!(
        "{MY_CLASSICAL}\
         noncomputable def b0 (p : Prop) : Decidable p := by infer_instance\n\
         noncomputable def b1 {{α : Sort u}} (p : α → Prop) : MyDecPred p := by\n\
         \x20 infer_instance\n\
         noncomputable def b2 {{α : Sort u}} (r : α → α → Prop) : MyDecRel r := by\n\
         \x20 infer_instance\n\
         noncomputable def b3 (α : Sort u) : DecidableEq α := by infer_instance\n\
         noncomputable def b3t (α : Sort u) : DecidableEq α := inferInstance\n\
         noncomputable def b3x (α : Sort u) : DecidableEq α := by exact inferInstance\n\
         end MyClassical\n\
         def k4 {{α : Type}} [inst : ∀ a b : α, Decidable (a = b)] : DecidableEq α :=\n\
         \x20 inferInstance\n\
         def k4t {{α : Type}} [inst : ∀ a b : α, Decidable (a = b)] : DecidableEq α := by\n\
         \x20 infer_instance\n"
    ));
    for name in ["b0", "b1", "b2", "b3", "b3t", "b3x", "k4", "k4t"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: an alias goal must be opened and searched as `Decidable`: {e}");
        }
    }
    assert_all_accepted(&verdicts, "the whole fixture elaborates in Lean");
}

/// Opening the alias goal invents nothing: with the scoped instance closed
/// there is still no `Decidable (a = b)` for an arbitrary `α`, by term or by
/// tactic, and the `MyDecPred` instance at `Nat` does not answer an arbitrary
/// predicate.
#[test]
fn test_alias_goal_opening_with_no_instance_is_refused() {
    let verdicts = run_file(&format!(
        "{MY_CLASSICAL}\
         end MyClassical\n\
         noncomputable def bad1 (α : Sort u) : DecidableEq α := inferInstance\n\
         noncomputable def bad2 (α : Sort u) : DecidableEq α := by infer_instance\n\
         noncomputable def bad3 {{α : Sort u}} (p : α → Prop) : MyDecPred p := by\n\
         \x20 infer_instance\n"
    ));
    for name in ["bad1", "bad2", "bad3"] {
        let err = verdict_of(&verdicts, name)
            .as_ref()
            .expect_err("the scoped instance is closed; Lean refuses this");
        assert!(
            is_synthesis_failure(err),
            "`{name}`: the refusal must be an instance-synthesis failure: {err}"
        );
    }
}
