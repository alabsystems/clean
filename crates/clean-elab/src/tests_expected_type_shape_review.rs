// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boundaries of lane X's widenings (G31, G34), through the module driver
//! every frontend runs, from the r4 review (2026-10-09).
//!
//! Every source here was run through the pinned Lean 4.8.0 binary
//! (`~/.elan/toolchains/leanprover--lean4---v4.8.0/bin/lean`):
//!
//! * **G34 reducibility.** Lean's `coerceToSort` reaches `boolToSort` through
//!   instance resolution, so `Bool` and its `abbrev` / `@[reducible]` aliases
//!   coerce and a semireducible `def MyBool := Bool` does NOT ("type
//!   expected"). Clean decided "is Bool" at default transparency until this
//!   review and accepted every shape below.
//! * **G34 instance binders.** `[h : b]` is refused by Lean ("invalid binder
//!   annotation, type is not a class instance") after its ordinary type coercion.
//! * **G31 gate.** A folded branch type headed by a semireducible `def` no
//!   instance keys on is not handed on until G47 lands, so `def M := StateT …`
//!   with a `pure ()` / `throw err` branch stays refused as Lean refuses it.
//! * **Known false acceptances** next to the changed code (open, filed in
//!   ledger (117) and (118)): each fails the day it closes, then becomes a
//!   refusal pin.

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DeclVerdict, DriverOptions, EnvironmentSetup, ModuleReport,
    VerdictKind,
};
use std::path::Path;

fn check_module(source: &str) -> ModuleReport {
    let _lock = module_elaboration_lock();
    let path = Path::new("ExpectedTypeShapeReview.lean");
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

/// `name` is refused and its detail contains every one of `needles`.
fn assert_refused_with(report: &ModuleReport, name: &str, needles: &[&str]) {
    let v = verdict(report, name);
    assert_ne!(
        v.kind,
        VerdictKind::Passed,
        "`{name}` must be refused: {v:#?}"
    );
    let detail = v.detail.as_deref().unwrap_or_default();
    for needle in needles {
        assert!(
            detail.contains(needle),
            "`{name}`'s refusal must mention `{needle}`: {detail}"
        );
    }
}

/// The refusal says the term is not a sort, whichever check saw it first
/// (the elaborator's `ExpectedSort(…)` or the kernel's `Expected sort, got:`).
fn assert_not_a_sort(report: &ModuleReport, name: &str, alias: &str) {
    let v = verdict(report, name);
    assert_ne!(
        v.kind,
        VerdictKind::Passed,
        "`{name}` must be refused: {v:#?}"
    );
    let detail = v.detail.as_deref().unwrap_or_default();
    assert!(
        detail.contains(&format!("ExpectedSort({alias}"))
            || detail.contains(&format!("Expected sort, got: {alias}")),
        "`{name}` is refused because `{alias}` is not a sort: {detail}"
    );
}

const DEF_BOOL: &str = "def MyBool := Bool\ndef x : MyBool := true\n";

#[test]
fn test_g34_semireducible_bool_alias_is_not_coerced_in_any_type_position() {
    let report = check_module(&format!(
        "{DEF_BOOL}\
         theorem k1 (b : MyBool) (h : b) : True := True.intro\n\
         def k3 : Prop := x → True\n\
         def k8 : Prop := ∀ (_ : True), x\n\
         def k9 (b : MyBool) := fun (h : b) => (0 : Nat)\n"
    ));
    assert_passed(&report, "MyBool");
    assert_passed(&report, "x");
    for name in ["k1", "k3", "k8", "k9"] {
        assert_not_a_sort(&report, name, "MyBool");
    }
}

#[test]
fn test_g34_semireducible_bool_alias_result_type_is_refused() {
    // `theorem k4 : x` keeps the uncoerced `x` as its statement; `rfl` cannot
    // inhabit it (Lean: "type expected").
    let report = check_module(&format!("{DEF_BOOL}theorem k4 : x := rfl\n"));
    assert_refused_with(&report, "k4", &["expected x"]);
}

#[test]
fn test_g34_semireducible_bool_alias_variable_binder_is_refused() {
    let report = check_module(&format!(
        "{DEF_BOOL}variable (b : MyBool) (h : b)\ntheorem k7 : True := True.intro\n"
    ));
    let refused = report
        .verdicts
        .iter()
        .find(|v| v.kind != VerdictKind::Passed && v.line == Some(3))
        .unwrap_or_else(|| panic!("the `variable` line is refused: {:#?}", report.verdicts));
    let detail = refused.detail.as_deref().unwrap_or_default();
    assert!(detail.contains("ExpectedSort(MyBool)"), "{detail}");
}

#[test]
fn test_g34_semireducible_type_and_family_aliases_are_refused() {
    let report = check_module(
        "def T : Type := Bool\ndef u : T := true\ndef k14 (h : u) : Nat := 0\n\
         def B (n : Nat) : Type := match n with | 0 => Bool | _ => Nat\n\
         def y : B 0 := true\ntheorem u3 (h : y) : True := True.intro\n",
    );
    assert_not_a_sort(&report, "k14", "T");
    assert_not_a_sort(&report, "u3", "B 0");
}

#[test]
fn test_g34_reducible_bool_aliases_still_coerce() {
    // Lean accepts both: `abbrev` and `@[reducible] def` are seen through by
    // instance resolution. A `Bool`-valued function behind a semireducible
    // type alias still applies to a `Bool`.
    let report = check_module(
        "abbrev ABool := Bool\ntheorem k2 (b : ABool) (h : b) : b = true := h\n\
         @[reducible] def RBool := Bool\ntheorem u2 (b : RBool) (h : b) : b = true := h\n\
         def Pred := Nat → Bool\ndef p : Pred := fun n => n == 0\ntheorem k13 : p 0 := rfl\n",
    );
    for name in ["k2", "u2", "k13"] {
        assert_passed(&report, name);
    }
}

#[test]
fn test_g34_instance_binder_bool_is_rejected_as_a_non_class() {
    // Lean: "invalid binder annotation, type is not a class instance".
    let report = check_module("theorem k5 (b : Bool) [h : b] : True := True.intro\n");
    assert_refused_with(
        &report,
        "k5",
        &["invalid binder annotation", "not a class instance"],
    );
}

/// Lean's header annotation check refuses non-class instance binders.
#[test]
fn test_instance_binder_of_non_class_is_refused() {
    let report = check_module("theorem r7 [h : True] : True := h\n");
    assert_refused_with(
        &report,
        "r7",
        &["invalid binder annotation", "not a class instance"],
    );
}

const DEF_M: &str = "def M (α : Type) := StateT Nat (Except String) α\n";

#[test]
fn test_g31_def_alias_monad_if_else_pure_is_refused() {
    // Lean: "failed to synthesize instance" at `pure ()` (`Pure M` through a
    // semireducible def). The folded `M Unit` is not handed on (G31 gate).
    let report = check_module(&format!(
        "{DEF_M}def r10 (b : Bool) (x : M Unit) := if b then x else pure ()\n"
    ));
    assert_refused_with(&report, "r10", &["failed to synthesize instance `Pure"]);
}

#[test]
fn test_g31_def_alias_monad_match_throw_is_refused() {
    // Lean: "failed to synthesize instance" at `throw err`. Clean refuses at
    // the motive (the pre-G31 reason) until G47 lands; this pins the refusal.
    let report = check_module(&format!(
        "{DEF_M}def r9 (e : Except String Nat) (onOk : Nat → M Nat) := match e with\n  \
         | .ok v => onOk v\n  | .error err => throw err\n"
    ));
    assert_refused_with(&report, "r9", &["Match arm 1 has type"]);
}

#[test]
fn test_g31_abbrev_monad_still_folds_through_the_gate() {
    let report = check_module(
        "abbrev Sem (α : Type) := StateT Nat (Except String) α\n\
         def a1 (b : Bool) (x : Sem Unit) := if b then x else pure ()\n\
         def a2 (e : Except String Nat) (onOk : Nat → Sem Nat) := match e with\n  \
         | .ok v => onOk v\n  | .error err => throw err\n\
         def a3 (b : Bool) (x : StateT Nat (Except String) Unit) := if b then x else pure ()\n",
    );
    for name in ["a1", "a2", "a3"] {
        assert_passed(&report, name);
    }
}

#[test]
fn test_g31_ill_typed_later_branch_refused_for_the_right_reason() {
    // No expected type: these reach G31's path. integ/r2 refused them for the
    // wrong reason (`Pure ?3` / `Match arm 1 has type`); the right reason is
    // the payload mismatch (Lean: "application type mismatch" at `pure true`).
    let report = check_module(
        "abbrev Sem (α : Type) := StateT Nat (Except String) α\n\
         def c4 (b : Bool) (x : Sem Unit) := if b then x else pure true\n\
         def c3 (e : Except String Nat) (onOk : Nat → Sem Nat) := match e with\n  \
         | .ok v => onOk v\n  | .error _ => pure true\n",
    );
    assert_refused_with(&report, "c4", &["Type mismatch", "Bool vs PUnit"]);
    assert_refused_with(&report, "c3", &["Type mismatch", "Bool vs Nat"]);
}

/// KNOWN FALSE ACCEPTANCES, OPEN (G47, ledger (117)): a numeric literal
/// branch at a semireducible alias type. Lean: "failed to synthesize
/// instance OfNat MyNat 0". Clean's instance search sees through the def.
#[test]
fn test_numeral_branch_at_def_alias_known_false_acceptance() {
    let report = check_module(
        "def MyNat := Nat\n\
         def q3 (b : Bool) (x : MyNat) := if b then x else 0\n\
         def q4 (n : Nat) (x : MyNat) := match n with\n  | 0 => x\n  | _ => 5\n",
    );
    assert_passed(&report, "q3");
    assert_passed(&report, "q4");
}

/// Resolved false acceptances (ledger (118)): a declaration with no
/// expected type whose value or result type leaves an unresolved `_`. Lean
/// refuses all three: `m6` ("invalid occurrence of universe level"), `m7`
/// ("don't know how to synthesize implicit argument") and `s1` ("failed to
/// infer definition type").
#[test]
fn test_unresolved_hole_without_declared_type_is_refused() {
    let report = check_module(
        "def m6 := List.length ([] : List _)\n\
         def m7 (n : Nat) := if n = 0 then [] else []\n\
         def s1 (x : Nat) : _ := x + 1\n",
    );
    for name in ["m6", "m7", "s1"] {
        assert_refused_with(&report, name, &["unresolved"]);
    }
}
