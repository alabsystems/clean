// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `alias ⟨fwd, rev⟩ := t` reads `t`'s type WITHOUT reduction. Batteries'
//! `mkIffMpApp` (`Batteries/Tactic/Alias.lean`, revision 66e46918, the copy
//! under `reports/header-inference-2026-11-12/upstream/`) opens the telescope
//! with `Meta.forallTelescope` (no whnf) and matches the body with
//! `Expr.iff?` (syntactic), so an `Iff` or a binder hidden behind a `def` OR
//! an `abbrev` is refused with "Target theorem must have the form
//! `∀ x y z, a ↔ b`".
//!
//! Ground truth (2026-11-13): that Batteries module built with the pinned
//! v4.36.0-rc2 `lean` and run on these fixtures refuses all four hidden
//! shapes (def- and abbrev-hidden `Iff`, def- and abbrev-hidden `∀`) and
//! accepts the syntactic control (`a5 : ∀ (p : Prop), p → p`).

use crate::test_support::file_verdicts::run_file;

fn assert_refused(header: &str, theorem: &str) {
    let src = format!("{header}\n{theorem}\nalias ⟨a, b⟩ := t\n");
    let verdicts = run_file(&src);
    assert!(
        verdicts.iter().any(|(_, verdict)| verdict
            .as_ref()
            .is_err_and(|e| e.contains("Target theorem must have the form"))),
        "Lean refuses an alias whose Iff or binder hides behind a definition: {verdicts:?}"
    );
}

#[test]
fn test_alias_iff_behind_def_is_refused() {
    assert_refused(
        "def MyIff (p : Prop) := p ↔ p",
        "theorem t (p : Prop) : MyIff p := Iff.rfl",
    );
}

#[test]
fn test_alias_iff_behind_abbrev_is_refused() {
    assert_refused(
        "abbrev MyIff (p : Prop) := p ↔ p",
        "theorem t (p : Prop) : MyIff p := Iff.rfl",
    );
}

#[test]
fn test_alias_forall_behind_def_is_refused() {
    assert_refused(
        "def AllIff := ∀ p : Prop, p ↔ p",
        "theorem t : AllIff := fun _ => Iff.rfl",
    );
}

#[test]
fn test_alias_forall_behind_abbrev_is_refused() {
    assert_refused(
        "abbrev AllIff := ∀ p : Prop, p ↔ p",
        "theorem t : AllIff := fun _ => Iff.rfl",
    );
}

/// Positive control: a syntactic `∀ …, a ↔ b`, in binder or in `∀` form,
/// still aliases both directions, and the directions have Lean's types.
#[test]
fn test_alias_syntactic_iff_telescope_is_accepted() {
    let verdicts = run_file(
        "theorem t5 (p : Prop) : p ↔ p := Iff.rfl\n\
         alias ⟨a5, b5⟩ := t5\n\
         theorem t6 : ∀ p q : Prop, (p ∧ q) ↔ (q ∧ p) :=\n\
         \x20 fun _ _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩\n\
         alias ⟨a6, b6⟩ := t6\n\
         example (p : Prop) : p → p := a5 p\n\
         example (p q : Prop) : q ∧ p → p ∧ q := b6 p q\n",
    );
    let failed: Vec<_> = verdicts.iter().filter(|(_, v)| v.is_err()).collect();
    assert!(failed.is_empty(), "Lean accepts these aliases: {failed:#?}");
    assert!(
        verdicts.len() >= 4,
        "every command must report: {verdicts:?}"
    );
}
