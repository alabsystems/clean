// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G28 / ledger class (98): an un-annotated lambda argument whose binder type
//! is pinned only by a LATER argument is postponed, as Lean postpones the
//! field notation inside it. Every source here was run through the pinned
//! Lean 4.8.0 binary (2026-10-08): the `*_passes` sources are accepted, and
//! every declaration asserted refused is refused by Lean too.

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DeclVerdict, DriverOptions, EnvironmentSetup, ModuleReport,
    VerdictKind,
};
use std::path::Path;

fn check_module(source: &str) -> ModuleReport {
    let _lock = module_elaboration_lock();
    let path = Path::new("PostponeLambdaFixture.lean");
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

fn verdict<'r>(report: &'r ModuleReport, name: &str) -> &'r DeclVerdict {
    report
        .verdicts
        .iter()
        .find(|v| v.name == name)
        .unwrap_or_else(|| panic!("no verdict for `{name}` in {:#?}", report.verdicts))
}

fn assert_passed(report: &ModuleReport, name: &str) {
    let v = verdict(report, name);
    assert_eq!(v.kind, VerdictKind::Passed, "`{name}` must pass: {v:#?}");
}

/// Refused; returns the detail for the target assertion.
fn refused_detail(report: &ModuleReport, name: &str) -> String {
    let v = verdict(report, name);
    assert_ne!(
        v.kind,
        VerdictKind::Passed,
        "`{name}` must be refused: {v:#?}"
    );
    v.detail.clone().unwrap_or_default()
}

const S_PRELUDE: &str = "structure S where\n  n : Nat\n\
def S.bump (s : S) (k : Nat) : S := ⟨s.n + k⟩\n";

const VM_PRELUDE: &str = "def VM := Nat → Option Nat\n\
def VM.set (m : VM) (k v : Nat) : VM := fun i => if i = k then some v else m i\n\
def VM.get (m : VM) (k : Nat) : Option Nat := m k\n\
def VM.empty : VM := fun _ => none\n";

/// The trust-ir shape (triage L): `let r := ps.foldl (fun acc p => acc.bump
/// p) m` with no expected type, then a TRUE statement about it by `rfl`.
#[test]
fn test_postpone_lambda_unannotated_let_foldl_passes() {
    let src = format!(
        "{S_PRELUDE}def sumInto (ps : List Nat) (m : S) : S :=\n  \
         let r := ps.foldl (fun acc p => acc.bump p) m\n  r\n\
         theorem sumInto_val : (sumInto [1, 2] ⟨0⟩).n = 3 := rfl\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "sumInto");
    assert_passed(&report, "sumInto_val");
}

/// Negative twin: the same definition elaborates and computes `3`, so the
/// FALSE `= 4` is refused (Lean: `type mismatch`).
#[test]
fn test_postpone_lambda_false_value_refused() {
    let src = format!(
        "{S_PRELUDE}def sumInto (ps : List Nat) (m : S) : S :=\n  \
         let r := ps.foldl (fun acc p => acc.bump p) m\n  r\n\
         theorem sumInto_val : (sumInto [1, 2] ⟨0⟩).n = 4 := rfl\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "sumInto");
    let detail = refused_detail(&report, "sumInto_val");
    assert!(
        detail.contains("mismatch") || detail.contains("not definitionally equal"),
        "the false value is refused as a type mismatch: {detail}"
    );
}

/// The same postponement with no `let` (a bare body with an inferred result
/// type) and under `have`.
#[test]
fn test_postpone_lambda_bare_body_and_have_pass() {
    let src = format!(
        "{S_PRELUDE}def k2 (ps : List Nat) (m : S) :=\n  ps.foldl (fun acc p => acc.bump p) m\n\
         def k4 (ps : List Nat) (m : S) : S :=\n  \
         have r := ps.foldl (fun acc p => acc.bump p) m\n  r\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "k2");
    assert_passed(&report, "k4");
}

/// A `def`-alias carrier (`VM := Nat → Option Nat`) and an index projection
/// `p.1` on a binder whose type is open (`List.foldl … m ps`: `ps` comes last,
/// so `p`'s type is unknown when the lambda is reached even under an expected
/// type). Right value accepted, wrong value refused.
#[test]
fn test_postpone_lambda_alias_carrier_and_index_projection() {
    let src = format!(
        "{VM_PRELUDE}def j1 (ps : List (Nat × Nat)) (m : VM) : VM :=\n  \
         let l' := ps.foldl (fun acc p => acc.set p.1 p.2) m\n  l'\n\
         def bind2 (ps : List (Nat × Nat)) (m : VM) : VM :=\n  \
         List.foldl (fun acc p => acc.set p.1 p.2) m ps\n\
         theorem j1_right : (j1 [(1, 5)] VM.empty).get 1 = some 5 := rfl\n\
         theorem j1_wrong : (j1 [(1, 5)] VM.empty).get 1 = some 6 := rfl\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "j1");
    assert_passed(&report, "bind2");
    assert_passed(&report, "j1_right");
    let detail = refused_detail(&report, "j1_wrong");
    assert!(
        detail.contains("mismatch") || detail.contains("not definitionally equal"),
        "the wrong value is refused as a type mismatch: {detail}"
    );
}

/// Nested: the inner lambda's receiver type is pinned only once the OUTER
/// lambda is postponed (its `acc` pinned by `m`).
#[test]
fn test_postpone_lambda_nested_passes_and_false_value_refused() {
    let src = format!(
        "{S_PRELUDE}def nest (pss : List (List Nat)) (m : S) : S :=\n  \
         let r := pss.foldl (fun acc ps => ps.foldl (fun a p => a.bump p) acc) m\n  r\n\
         theorem nest_val : (nest [[1], [2, 3]] ⟨0⟩).n = 6 := rfl\n\
         theorem nest_wrong : (nest [[1], [2, 3]] ⟨0⟩).n = 7 := rfl\n"
    );
    let report = check_module(&src);
    assert_passed(&report, "nest");
    assert_passed(&report, "nest_val");
    refused_detail(&report, "nest_wrong");
}

/// Nothing pins the binder type: Lean refuses ("invalid field notation, type
/// is not of the form (C ...)"), and Clean refuses with the error the eager
/// attempt reported before postponement existed.
#[test]
fn test_postpone_lambda_unpinned_receiver_refused_with_original_error() {
    let src = format!("{S_PRELUDE}def bad (ps : List Nat) := ps.foldl (fun acc p => acc.bump p)\n");
    let report = check_module(&src);
    let detail = refused_detail(&report, "bad");
    assert!(
        detail.contains("dot notation `.bump`"),
        "the original eager-attempt error is reported: {detail}"
    );
}

/// The later argument pins the binder to a type with no such field: Lean
/// refuses (`Nat.bump` does not exist), and so does Clean.
#[test]
fn test_postpone_lambda_pinned_to_wrong_type_refused() {
    let src = format!(
        "{S_PRELUDE}def bad2 (ps : List Nat) :=\n  \
         let r := ps.foldl (fun acc p => acc.bump p) (0 : Nat)\n  r\n"
    );
    let report = check_module(&src);
    let detail = refused_detail(&report, "bad2");
    assert!(detail.contains("bump"), "refused at the field: {detail}");
}

/// The postponed lambda's TYPE is checked against its slot when the drain
/// assigns it: `acc.bump p` is pinned to `S` by `m`, but the body projects
/// `.n : Nat`, so the lambda is `S → Nat → Nat` against `S → Nat → S`. Lean
/// says "type mismatch"; Clean must refuse in the ELABORATOR, never hand the
/// ill-typed application to the kernel. The postponed retry fails on that
/// mismatch, so the refusal carries the eager attempt's error (R51 choice 1).
#[test]
fn test_postpone_lambda_body_type_mismatch_refused_by_elaborator() {
    let src = format!(
        "{S_PRELUDE}def go (ps : List Nat) (m : S) :=\n  \
         (ps.foldl (fun acc p => (acc.bump p).n) m)\n"
    );
    let report = check_module(&src);
    let detail = refused_detail(&report, "go");
    assert_eq!(
        verdict(&report, "go").kind,
        VerdictKind::ElaborationFailed,
        "refused by the elaborator, not the kernel: {detail}"
    );
    assert!(
        detail.contains("dot notation `.bump`") && !detail.contains("Kernel"),
        "the eager attempt's error, not a kernel failure: {detail}"
    );
}

/// G28 companion: unification now assigns a bare metavariable the other side
/// AS WRITTEN, so `b = c` with `b c : Behavior` (`def Behavior := Nat → Nat`)
/// keeps the folded `Behavior` as its `Eq` type. The `funext` tactic must see
/// through it the way Lean's `apply funext` does (pinned Lean 4.8.0 accepts
/// both theorems); a false pointwise hypothesis is still refused.
#[test]
fn test_funext_tactic_through_def_alias_carrier_passes() {
    let report = check_module(
        "def Behavior := Nat → Nat\n\
         theorem t (b c : Behavior) (h : ∀ k, b k = c k) : b = c := by\n  \
           funext k\n  exact h k\n\
         def Pred := Nat → Prop\n\
         theorem t6 (p q : Pred) (h : ∀ k, p k ↔ q k) : p = q := by\n  \
           funext k\n  exact propext (h k)\n\
         theorem bad (b c : Behavior) (h : ∀ k, b k = c (k + 1)) : b = c := by\n  \
           funext k\n  exact h k\n",
    );
    assert_passed(&report, "t");
    assert_passed(&report, "t6");
    refused_detail(&report, "bad");
}
