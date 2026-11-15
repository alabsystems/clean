// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instances filed under a reducible class ALIAS (`DecidableEq`,
//! `DecidableLT`, …) answer goals the way Lean's instance index does
//! (`Lean/Meta/Instances.lean` `mkInstanceKey`, `Lean/Meta/SynthInstance.lean`
//! `getInstances`/`tryResolve`/`consume`).
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12): the accepted declarations elaborate there as written
//! (warnings only), and every declaration asserted refused here fails there
//! with `failed to synthesize instance`.

use crate::test_support::file_verdicts::{
    assert_all_accepted, is_synthesis_failure, run_file, verdict_of,
};

const MY_OPT: &str = "inductive MyOpt (α : Type) where\n\
                      \x20 | none : MyOpt α\n\
                      \x20 | some : α → MyOpt α\n\
                      axiom myOptDecEq {α : Type} [DecidableEq α] : DecidableEq (MyOpt α)\n\
                      attribute [instance] myOptDecEq\n\
                      def useDE {α : Type} [DecidableEq α] (a : α) : Nat := 0\n";

/// A PARAMETRIC instance filed under the alias answers the alias goal it is
/// filed under. The candidate loop used to whnf the instance's conclusion
/// `DecidableEq (MyOpt ?α)` through the alias to `Decidable (?a = ?b)` and
/// then reject it on `class head Decidable ≠ DecidableEq` — the face of
/// `Function._root_.Option.rec_update` / `curry_update` on
/// `Mathlib/Logic/Function/Basic.lean` (`Option.instDecidableEq`,
/// `instDecidableEqProd`). Lean: `s3` is `fun a b => @myOptDecEq α inst a b`.
#[test]
fn test_instance_alias_parametric_decidable_eq_answers_alias_goal() {
    let verdicts = run_file(&format!(
        "{MY_OPT}\
         noncomputable def s1 {{α : Type}} [DecidableEq α] (x : MyOpt α) : Nat := useDE x\n\
         noncomputable def s2 (x : MyOpt Nat) : Nat := useDE x\n\
         noncomputable def s3 {{α : Type}} [DecidableEq α] : DecidableEq (MyOpt α) := inferInstance\n\
         noncomputable def s4 {{α : Type}} [DecidableEq α] (x y : MyOpt α) : Decidable (x = y) :=\n\
         \x20 inferInstance\n\
         noncomputable def s5 {{α : Type}} [DecidableEq α] : DecidableEq (MyOpt (MyOpt α)) :=\n\
         \x20 inferInstance\n"
    ));
    for name in ["s1", "s2", "s3", "s4", "s5"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: a parametric instance filed under `DecidableEq` must answer: {e}");
        }
    }
    assert_all_accepted(&verdicts, "the whole fixture elaborates in Lean");
}

/// The alias-filed instance is still unified against the goal: at a carrier
/// with no `DecidableEq` its `[DecidableEq α]` premise fails and nothing is
/// committed.
#[test]
fn test_instance_alias_wrong_carrier_is_refused() {
    let verdicts = run_file(&format!(
        "{MY_OPT}\
         inductive NoDec where\n\
         \x20 | a\n\
         \x20 | b\n\
         noncomputable def bad (x : MyOpt NoDec) : Nat := useDE x\n"
    ));
    let bad = verdict_of(&verdicts, "bad")
        .as_ref()
        .expect_err("`DecidableEq (MyOpt NoDec)` has no instance; Lean refuses it too");
    assert!(
        is_synthesis_failure(bad),
        "the refusal must be an instance-synthesis failure: {bad}"
    );
}

const MY_DEC_LT: &str = "universe u\n\
                         abbrev MyDecRel {α : Sort u} (r : α → α → Prop) :=\n\
                         \x20 (a b : α) → Decidable (r a b)\n\
                         abbrev MyDecLT (α : Type) [LT α] := MyDecRel (α := α) (· < ·)\n\
                         abbrev MyDecLE (α : Type) [LE α] := MyDecRel (α := α) (· ≤ ·)\n\
                         def needsDec (p : Prop) [Decidable p] : Nat := 0\n";

/// Candidates filed under an alias of `Decidable` answer `Decidable` goals:
/// the shape of Mathlib's `LinearOrder.toDecidableLT/LE` (a class field whose
/// type is `DecidableLT α`, made an instance). The `[self : MyLO α]` premise is
/// fixed by unifying the conclusion, as Lean's `consume` expects. Rows:
/// `min_def_lt`, `max_def_lt`, `LinearOrder.lift`, `LinearOrder.liftWithOrd`
/// (`Decidable (a < b)`, `Decidable (f x ≤ f y)`) and `not_lt_iff_eq_or_lt`
/// (`DecidableLE α`) on `Mathlib/Order/Basic.lean`. Lean: `c1` is
/// `needsDec (a < b) (@MyLO.decLT α inst a b)`, `c3` is `@MyLO.decLT α inst`,
/// `c4` is `@MyLO.decLE β inst (f x) (f y)`.
#[test]
fn test_instance_alias_lt_le_instances_answer_decidable_goals() {
    let verdicts = run_file(&format!(
        "{MY_DEC_LT}\
         class MyLO (α : Type) extends LT α, LE α where\n\
         \x20 decLT : MyDecLT α\n\
         \x20 decLE : MyDecLE α\n\
         attribute [instance] MyLO.decLT\n\
         attribute [instance] MyLO.decLE\n\
         def c1 {{α : Type}} [MyLO α] (a b : α) : Nat := needsDec (a < b)\n\
         def c2 {{α : Type}} [MyLO α] (a b : α) : Nat := if a < b then 0 else 1\n\
         def c3 {{α : Type}} [MyLO α] : MyDecLT α := inferInstance\n\
         def c4 {{α β : Type}} [MyLO β] (f : α → β) (x y : α) : Decidable (f x ≤ f y) :=\n\
         \x20 inferInstance\n\
         def c5 {{α : Type}} [MyLO α] : MyDecLE α := inferInstance\n"
    ));
    for name in ["c1", "c2", "c3", "c4", "c5"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: an instance filed under `MyDecLT`/`MyDecLE` must answer: {e}");
        }
    }
    assert_all_accepted(&verdicts, "the whole fixture elaborates in Lean");
}

/// The alias-filed `Decidable` candidate is still matched against the goal:
/// a `MyDecLT Foo` instance answers `Decidable (a < b)` at `Foo` and nothing
/// at `Bar`.
#[test]
fn test_instance_alias_lt_instance_at_other_carrier_is_refused() {
    let verdicts = run_file(&format!(
        "{MY_DEC_LT}\
         axiom Foo : Type\n\
         axiom fooLt : Foo → Foo → Prop\n\
         instance : LT Foo := ⟨fooLt⟩\n\
         axiom Bar : Type\n\
         axiom barLt : Bar → Bar → Prop\n\
         instance : LT Bar := ⟨barLt⟩\n\
         axiom fooDecLT : MyDecLT Foo\n\
         attribute [instance] fooDecLT\n\
         noncomputable def good (a b : Foo) : Nat := needsDec (a < b)\n\
         noncomputable def bad (a b : Bar) : Nat := needsDec (a < b)\n"
    ));
    if let Err(e) = verdict_of(&verdicts, "good") {
        panic!("`fooDecLT` must answer `Decidable (a < b)` at `Foo`: {e}");
    }
    let bad = verdict_of(&verdicts, "bad")
        .as_ref()
        .expect_err("no instance decides `<` on `Bar`; Lean refuses this");
    assert!(
        is_synthesis_failure(bad),
        "the refusal must be an instance-synthesis failure: {bad}"
    );
}

/// A SOURCE `instance` whose type is a reducible alias (`instance : MyDecLT
/// Foo`, the shape of every `instance : DecidableEq T` and Mathlib's
/// `DecidableLT` instances) is accepted — Lean's `addInstance` reads the
/// class through a reducible telescope — filed under the alias, and answers
/// both the alias goal and `Decidable (a < b)`. It invents nothing at a
/// carrier it does not cover (`bad`: no instance decides `≤` on `Bar`).
#[test]
fn test_instance_alias_source_instance_of_alias_is_filed_and_answers() {
    let verdicts = run_file(&format!(
        "{MY_DEC_LT}\
         axiom Foo : Type\n\
         axiom fooLt : Foo → Foo → Prop\n\
         instance : LT Foo := ⟨fooLt⟩\n\
         axiom fooLtDec (a b : Foo) : Decidable (a < b)\n\
         noncomputable instance fooDecLT : MyDecLT Foo := fooLtDec\n\
         noncomputable def good (a b : Foo) : Nat := needsDec (a < b)\n\
         noncomputable def good2 : MyDecLT Foo := inferInstance\n\
         axiom Bar : Type\n\
         axiom barLe : Bar → Bar → Prop\n\
         instance : LE Bar := ⟨barLe⟩\n\
         noncomputable def bad (a b : Bar) : Nat := needsDec (a ≤ b)\n"
    ));
    for name in ["fooDecLT", "good", "good2"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!(
                "`{name}`: a source instance of a reducible alias must register and answer: {e}"
            );
        }
    }
    let bad = verdict_of(&verdicts, "bad")
        .as_ref()
        .expect_err("no instance decides `≤` on `Bar`; Lean refuses this");
    assert!(
        is_synthesis_failure(bad),
        "the refusal must be an instance-synthesis failure: {bad}"
    );
}
