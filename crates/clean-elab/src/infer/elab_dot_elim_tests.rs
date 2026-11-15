// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Field notation on an explicit-motive eliminator (`elab_dot_elim.rs`).
//! Every source below was run through the pinned Lean v4.30.0-rc2 binary
//! (2026-11-13); the comment on each case records Lean's verdict.

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DriverOptions, EnvironmentSetup, ModuleReport, VerdictKind,
};
use std::path::Path;

fn check_module(source: &str) -> ModuleReport {
    let _lock = module_elaboration_lock();
    let path = Path::new("DotElimFixture.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("check environment");
    let _budget = DeclBudgetScope::enter(0);
    let parsed = parse_module(path, source).1.expect("fixture parses");
    let mut file_ctx = module_file_context(path);
    elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut file_ctx,
        DriverOptions::default(),
        &mut (),
    )
}

/// The verdict of the LAST declaration of `source` (fixtures may declare an
/// inductive first).
fn last_verdict(source: &str) -> (VerdictKind, String) {
    let report = check_module(source);
    let v = report
        .verdicts
        .last()
        .unwrap_or_else(|| panic!("no verdict for {source:?}"));
    (v.kind.clone(), v.detail.clone().unwrap_or_default())
}

fn assert_passes(source: &str) {
    let (kind, detail) = last_verdict(source);
    assert_eq!(kind, VerdictKind::Passed, "must pass: {source}\n{detail}");
}

fn assert_refused(source: &str, needle: &str) {
    let (kind, detail) = last_verdict(source);
    assert_ne!(kind, VerdictKind::Passed, "must be refused: {source}");
    assert!(
        detail.contains(needle),
        "refusal of {source:?} must mention {needle:?}; got: {detail}"
    );
}

const NO_EXPECTED: &str = "none was handed to this term";

/// `tests/elab/codeBindUnreachIssue.lean` (Lean accepts): the parser gives
/// `let g (_ : Unit) : Nat → Nat := x.casesOn` the ascription `(x.casesOn :
/// Nat → Nat)`, so the motive is `fun _ => Nat → Nat`.
#[test]
fn test_dot_elim_code_bind_unreach_issue_passes() {
    assert_passes(
        "set_option trace.Compiler.result true\n\
         def f (x : Empty) (y : Nat) : Nat :=\n  \
         let g (_ : Unit) : Nat → Nat := x.casesOn\n  \
         let aux := g ()\n  \
         y + aux y\n",
    );
}

/// Written ascriptions Lean accepts.
#[test]
fn test_dot_elim_written_ascription_passes() {
    for source in [
        "def q (x : Empty) : Nat := (x.casesOn : Nat)\n",
        "def q (x : Empty) : Nat := ((x.casesOn) : Nat)\n",
        "def q (x : Empty) : Nat → Nat := (x.casesOn : Nat → Nat)\n",
        "theorem q (h : False) : 1 = 2 := (h.casesOn : 1 = 2)\n",
        "theorem q (h : False) : 1 = 2 := (h.rec : 1 = 2)\n",
        "theorem q (x : Empty) : 1 = 2 := (x.recOn : 1 = 2)\n",
        "theorem q (x : Empty) : x = x := (x.casesOn : x = x)\n",
        "def q (h : False) : Nat := (h.casesOn : Nat)\n",
        "def q (x : Empty) : Type := (x.casesOn : Type)\n",
        "inductive E (α : Type) : Type\ndef q (x : E Nat) : Nat := (x.casesOn : Nat)\n",
        "theorem q (h : False) : 1 = 2 := by exact (h.casesOn : 1 = 2)\n",
        "def q (x : Empty) : Nat := by let y := (x.casesOn : Nat); exact y\n",
    ] {
        assert_passes(source);
    }
}

/// A positional motive other than `_`: Lean's ordinary application, which
/// the lambda path reproduces up to β (Lean accepts).
#[test]
fn test_dot_elim_positional_motive_passes() {
    assert_passes("def q (x : Empty) : Nat := x.casesOn (fun _ => Nat)\n");
}

/// Round 2's refutation (1): under a tactic `let`/`obtain` the ambient
/// expected type is the block's goal, which Lean does not pass. Lean rejects
/// each: "failed to elaborate eliminator, expected type is not available".
#[test]
fn test_dot_elim_tactic_let_obtain_stale_goal_refused() {
    for source in [
        "def q (x : Empty) : Nat := by let y := x.casesOn; exact y\n",
        "def q (x : Empty) : Nat := by\n  let y := x.casesOn\n  exact y\n",
        "example (x : Empty) : Nat := by let y := x.casesOn; exact y\n",
        "def q (x : Empty) : Nat := by obtain y := x.casesOn; exact y\n",
        "theorem q (x : Empty) : 1 = 2 := by let y := x.casesOn; exact y\n",
        "theorem q (x : Empty) : (1 : Nat) = 2 := by obtain h := x.casesOn; exact h\n",
    ] {
        assert_refused(source, NO_EXPECTED);
    }
}

/// Round 2's refutation (2): the lambda the old path built was accepted
/// wherever its type went unused or unified. Lean rejects each.
#[test]
fn test_dot_elim_no_expected_type_refused() {
    for source in [
        "def q (x : Empty) : Nat := by let y := x.casesOn; exact 0\n",
        "def q (x : Empty) : Nat := by have y := x.casesOn; exact 0\n",
        "def k5 (x : Empty) := x.casesOn\n",
        "def k (x : Empty) := id x.casesOn\n",
        "def k (x : Empty) : Nat := let y := x.casesOn; 0\n",
        "def k (x : Empty) := x.rec\n",
        "theorem q (h : False) : 1 = 2 := by apply h.casesOn\n",
    ] {
        assert_refused(source, NO_EXPECTED);
    }
}

/// A parenthesized head is a term of its own with no expected type, so
/// Lean rejects `(x.casesOn) (fun _ => Nat)` although the motive is given.
#[test]
fn test_dot_elim_parenthesized_head_refused() {
    assert_refused(
        "def k (x : Empty) : Nat := (x.casesOn) (fun _ => Nat)\n",
        NO_EXPECTED,
    );
}

/// An expected type DERIVED from a stale ambient one is not trusted: a `let`
/// body, `if` branches, and an ascription `_` completed from the context.
/// Lean rejects each.
#[test]
fn test_dot_elim_derived_expected_type_refused() {
    for source in [
        "def q (x : Empty) : Nat := by let y := (let z := 0; x.casesOn); exact y\n",
        "theorem q (h : False) : 1 = 2 := by let y := if True then h.casesOn else h.casesOn; exact y\n",
        "def q (x : Empty) : Nat := by refine (x.casesOn : _)\n",
        "def q (x : Empty) : Nat := by exact (x.casesOn : _)\n",
        "def q (x : Empty) : Nat := by let y := (x.casesOn : _); exact y\n",
    ] {
        assert_refused(source, NO_EXPECTED);
    }
}

/// An expected type whose universe Lean cannot settle (Lean: "failed to
/// infer universe levels in `let` declaration type").
#[test]
fn test_dot_elim_flexible_universe_refused() {
    for source in [
        "def q (x : Empty) : Nat := let y := (x.casesOn : PUnit); 0\n",
        "def q (x : Empty) : Nat := let y := (x.casesOn : Sort _); 0\n",
    ] {
        assert_refused(source, "universe levels are not known yet");
    }
}

/// `recOn` at a non-proposition: Lean's code generator rejects the
/// declaration ("Failed to find LCNF signature").
#[test]
fn test_dot_elim_recursor_at_data_refused() {
    assert_refused(
        "def h (x : Empty) : Nat := (x.recOn : Nat)\n",
        "modelled only at a proposition",
    );
}

/// The motive `fun t => h = h` is not type-correct (`h : x = x`); Lean
/// rejects ("motive is not type correct").
#[test]
fn test_dot_elim_motive_mentioning_dependent_local_refused() {
    assert_refused(
        "theorem q (x : Empty) (h : x = x) : h = h := (x.casesOn : h = h)\n",
        "mentions a local other than the receiver",
    );
}

/// `Empty.rec x` passes `x` as the explicit MOTIVE; Lean rejects all three
/// with an application type mismatch, and so does Clean once the recursor
/// reroute declines an explicit motive.
#[test]
fn test_dot_elim_qualified_recursor_takes_motive_first() {
    for source in [
        "def h (x : Empty) : Nat := Empty.rec x\n",
        "def h (x : Empty) : Nat := Empty.recOn x\n",
        "theorem t (h : False) : 1 = 2 := False.rec h\n",
    ] {
        let (kind, detail) = last_verdict(source);
        assert_ne!(
            kind,
            VerdictKind::Passed,
            "must be refused: {source}\n{detail}"
        );
    }
}

/// Inner field notation in a chain gets no expected type (Lean rejects).
#[test]
fn test_dot_elim_inner_chain_refused() {
    assert_refused(
        "def k (x : Empty) : Nat := (x.casesOn.succ : Nat)\n",
        NO_EXPECTED,
    );
}

/// Known gaps, pinned as refusals so they fail loudly the day they close.
/// Lean ACCEPTS each.
#[test]
fn test_dot_elim_known_gaps_refused() {
    // The declaration body's expected type is not a written ascription here.
    assert_refused("def f (x : Empty) : Nat := x.casesOn\n", NO_EXPECTED);
    // A `_` motive with an expected type.
    assert_refused(
        "def f (x : Empty) : Nat := (x.casesOn _ : Nat)\n",
        "only a positional motive other than `_`",
    );
    // A named motive.
    assert_refused(
        "def f (x : Empty) : Nat := x.casesOn (motive := fun _ => Nat)\n",
        "only a positional motive other than `_`",
    );
    // `rec` at data compiles in Lean; not modelled.
    assert_refused(
        "def q (x : Empty) : Nat := (x.rec : Nat)\n",
        "modelled only at a proposition",
    );
    // A motive mentioning another local (`fun _ => n = n`).
    assert_refused(
        "theorem q (x : Empty) (n : Nat) : n = n := (x.casesOn : n = n)\n",
        "mentions a local other than the receiver",
    );
}
