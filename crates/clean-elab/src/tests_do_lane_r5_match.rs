// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[match_pattern]` in patterns and `do`-block `match` shapes (round 5,
//! lane D: trust-ir gaps G29, G42, G35 and G51), through the module driver.
//!
//! Every source here was run through the pinned Lean 4.8.0 binary on
//! 2026-10-16; each positive fixture is accepted by it with the values
//! asserted, each `_bad` theorem is refused ("type mismatch" on `rfl`), and
//! each incomplete match is refused ("missing cases" / "failed to compile
//! pattern matching").
//!
//! * **G29** `@[match_pattern] def two : Nat := 2`; `| two => true | _ =>
//!   false` tests the literal. Clean read `two` as a binder and proved
//!   `isTwo 3 = true`. `()` / `Unit.unit` in a pattern were "Unknown
//!   identifier".
//! * **G42** a three-discriminant do-match lost its bindings ("Unknown
//!   identifier: x").
//! * **G35** a nested constructor pattern spelled `Nat.succ k` /
//!   `Option.none` was reported non-exhaustive.
//! * **G51** a `String` literal pattern in a do-match was refused.

use crate::module_driver::VerdictKind;
use crate::tests_do_lane_r5_lift::{assert_passed, check_module, verdict};

fn assert_not_passed(report: &crate::module_driver::ModuleReport, name: &str) {
    let v = verdict(report, name);
    assert_ne!(v.kind, VerdictKind::Passed, "Lean refuses `{name}`: {v:#?}");
}

const MATCH_PATTERN_DEFS: &str = "@[match_pattern] def two : Nat := 2\n\n\
def isTwo : Nat → Bool\n  | two => true\n  | _ => false\n\n\
@[match_pattern] def mySucc (n : Nat) : Nat := n + 1\n\n\
def pred2 : Nat → Nat\n  | mySucc k => k\n  | 0 => 0\n\n";

#[test]
fn test_match_pattern_def_unfolds_in_patterns() {
    let report = check_module(&format!(
        "{MATCH_PATTERN_DEFS}theorem isTwo_two : isTwo 2 = true := rfl\n\
         theorem isTwo_three : isTwo 3 = false := rfl\n\n\
         def isTwoM (n : Nat) : Bool :=\n  match n with\n  | two => true\n  | _ => false\n\n\
         theorem isTwoM_three : isTwoM 3 = false := rfl\n\
         theorem pred2_five : pred2 5 = 4 := rfl\n"
    ));
    for name in [
        "isTwo",
        "isTwo_two",
        "isTwo_three",
        "isTwoM",
        "isTwoM_three",
        "pred2",
        "pred2_five",
    ] {
        assert_passed(&report, name);
    }
}

#[test]
fn test_match_pattern_def_never_a_binder() {
    // The pre-fix reading: `two` a catch-all binder, `isTwo 3 = true`.
    let report = check_module(&format!(
        "{MATCH_PATTERN_DEFS}theorem isTwo_bad : isTwo 3 = true := rfl\n\
         theorem pred2_bad : pred2 5 = 5 := rfl\n\n\
         def onlyTwo : Nat → Bool\n  | two => true\n"
    ));
    assert_not_passed(&report, "isTwo_bad");
    assert_not_passed(&report, "pred2_bad");
    // Lean: "missing cases" — `two` covers only `2`.
    assert_not_passed(&report, "onlyTwo");
}

#[test]
fn test_match_pattern_unit_patterns_pass() {
    let report = check_module(
        "def u1 : Unit → Nat\n  | () => 1\n\ndef u2 : Unit → Nat\n  | Unit.unit => 2\n\n\
         theorem u1_v : u1 () = 1 := rfl\ntheorem u2_v : u2 () = 2 := rfl\n",
    );
    for name in ["u1", "u2", "u1_v", "u2_v"] {
        assert_passed(&report, name);
    }
}

const G42: &str = "def g42a (a b c : Nat) : Id Nat := do\n  match a, b, c with\n  | x, y, z => return x + 2 * y + 3 * z\n\n\
def g42b (a b c : Option Nat) : Id Nat := do\n  match a, b, c with\n  | some x, some y, some z => return x + 2 * y + 3 * z\n  | _, _, _ => return 0\n\n";

#[test]
fn test_do_match_three_discriminants_keep_bindings() {
    let report = check_module(&format!(
        "{G42}theorem g42a_v : g42a 1 2 3 = 14 := rfl\n\
         theorem g42b_v : g42b (some 1) (some 2) (some 3) = 14 := rfl\n\
         theorem g42b_n : g42b none (some 2) (some 3) = 0 := rfl\n\n\
         def g42c (a b c : Nat) : Id Nat := do\n  match a, b, c with\n  | x, y, z => pure ()\n  return a + b + c\n\n\
         theorem g42c_v : g42c 1 2 3 = 6 := rfl\n"
    ));
    for name in [
        "g42a", "g42b", "g42a_v", "g42b_v", "g42b_n", "g42c", "g42c_v",
    ] {
        assert_passed(&report, name);
    }
}

#[test]
fn test_do_match_three_discriminants_wrong_value_refused() {
    let report = check_module(&format!("{G42}theorem g42a_bad : g42a 1 2 3 = 6 := rfl\n"));
    assert_passed(&report, "g42a");
    assert_not_passed(&report, "g42a_bad");
}

const G35: &str = "def g35c (a : Nat) (o : Option Nat) : Id Nat := do\n  match a, o with\n  | 0, _ => return 0\n  | Nat.succ k, some x => return k + x\n  | Nat.succ k, Option.none => return k\n\n";

#[test]
fn test_do_match_nested_ctor_column_split_passes() {
    let report = check_module(&format!(
        "{G35}theorem g35c_v : g35c 3 none = 2 := rfl\n\
         theorem g35c_s : g35c 3 (some 4) = 6 := rfl\n\n\
         def g35d (o : Option (Option Nat)) : Id Nat := do\n  match o with\n  | some (some x) => return x\n  | some Option.none => return 1\n  | none => return 2\n\n\
         theorem g35d_v : g35d (some none) = 1 := rfl\n\n\
         def g35e (o : Option Nat) : Id Nat := do\n  match o with\n  | some 0 => return 10\n  | some (Nat.succ k) => return k\n  | Option.none => return 2\n\n\
         theorem g35e_v : g35e (some 5) = 4 := rfl\n"
    ));
    for name in [
        "g35c", "g35c_v", "g35c_s", "g35d", "g35d_v", "g35e", "g35e_v",
    ] {
        assert_passed(&report, name);
    }
}

#[test]
fn test_do_match_nested_ctor_wrong_or_missing_refused() {
    let report = check_module(&format!(
        "{G35}theorem g35c_bad : g35c 3 none = 3 := rfl\n\n\
         def g35x (o : Option (Option Nat)) : Id Nat := do\n  match o with\n  | some (some x) => return x\n  | none => return 2\n"
    ));
    assert_passed(&report, "g35c");
    assert_not_passed(&report, "g35c_bad");
    // Lean: "missing cases" (`some none`).
    assert_not_passed(&report, "g35x");
}

const G51: &str = "def g51a (s : String) : Id Nat := do\n  match s with\n  | \"a\" => return 1\n  | \"b\" => return 2\n  | _ => return 0\n\n";

#[test]
fn test_do_match_string_literal_patterns_pass() {
    let report = check_module(&format!(
        "{G51}theorem g51a_b : Id.run (g51a \"b\") = 2 := rfl\n\
         theorem g51a_c : Id.run (g51a \"c\") = 0 := rfl\n"
    ));
    for name in ["g51a", "g51a_b", "g51a_c"] {
        assert_passed(&report, name);
    }
}

#[test]
fn test_do_match_string_literal_wrong_or_missing_refused() {
    let report = check_module(&format!(
        "{G51}theorem g51a_bad : Id.run (g51a \"b\") = 1 := rfl\n\n\
         def g51x (s : String) : Id Nat := do\n  match s with\n  | \"a\" => return 1\n"
    ));
    assert_passed(&report, "g51a");
    assert_not_passed(&report, "g51a_bad");
    // Lean: "failed to compile pattern matching" (no catch-all).
    assert_not_passed(&report, "g51x");
}

#[test]
fn test_term_if_let_irrefutable_pattern_refused_as_lean() {
    // Pinned Lean 4.8.0: "redundant alternative" for `il1` and `il2`.
    let report = check_module(
        "def il1 (p : Nat × Nat) : Nat :=\n  if let (a, b) := p then a + b else 0\n\n\
         def il2 (n : Nat) : Nat :=\n  if let x := n then x else 0\n\n\
         def il3 (o : Option Nat) : Nat :=\n  if let some x := o then x else 0\n\n\
         theorem il3_v : il3 (some 4) = 4 := rfl\n",
    );
    assert_not_passed(&report, "il1");
    assert_not_passed(&report, "il2");
    assert_passed(&report, "il3");
    assert_passed(&report, "il3_v");
}
