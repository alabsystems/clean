// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `do`-block nested actions, `return` placement and `try`/`catch` scoping
//! (round 5, lane D: trust-ir gaps G52, G54, G53, G30 and G61), through the
//! module driver every frontend runs.
//!
//! Every Lean verdict quoted here was measured by running the source through
//! the pinned Lean 4.8.0 binary
//! (`~/.elan/toolchains/leanprover--lean4---v4.8.0/bin/lean`) on 2026-10-16:
//!
//! * **G52** `let rec k : Nat := (← pure 1) + 1` inside `do` and
//!   `let g := fun x => x + (← pure 1)`: "cannot lift `(<- ...)` over a
//!   binder, …". Clean hoisted the first out of the recursive value.
//! * **G54** `try (if b then return ()); pure 2 catch _ => pure 3` in
//!   `Except String Nat`: "application type mismatch … Unit … Nat";
//!   `return 1; pure 2`: "must be last element in a `do` sequence". Clean
//!   accepted both.
//! * **G61** `catch e => pure e` under an outer `e`: Lean returns the caught
//!   value (`cb "outer" = .ok "inner"` by `rfl`). Clean elaborated the
//!   handler before binding `e` and returned the outer one.
//! * **G30** a `(← e)` in an `if` branch, a `for` body, a `try` body and
//!   `match ← e`: accepted by Lean with the values asserted below.
//! * **G53** `while (← c) do …` is Lean's `repeat if (← c) then … else
//!   break` (the pre-pass shape is pinned in `infer/tests/action_lifting.rs`);
//!   no `while` elaborates on the builtin prelude yet (G63).

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DeclVerdict, DriverOptions, EnvironmentSetup, ModuleReport,
    VerdictKind,
};
use std::path::Path;

pub(crate) fn check_module(source: &str) -> ModuleReport {
    let _lock = module_elaboration_lock();
    let path = Path::new("DoLaneR5.lean");
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

pub(crate) fn verdict<'r>(report: &'r ModuleReport, name: &str) -> &'r DeclVerdict {
    report
        .verdicts
        .iter()
        .find(|v| v.name == name)
        .unwrap_or_else(|| panic!("no verdict for `{name}` in {:#?}", report.verdicts))
}

pub(crate) fn assert_passed(report: &ModuleReport, name: &str) {
    let v = verdict(report, name);
    assert_eq!(v.kind, VerdictKind::Passed, "`{name}` must pass: {v:#?}");
}

/// `name` is refused and its detail contains every one of `needles`.
pub(crate) fn assert_refused_with(report: &ModuleReport, name: &str, needles: &[&str]) {
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

const LIFT_OVER_BINDER: &str = "cannot lift `(<- ...)` over a binder";

#[test]
fn test_do_let_rec_value_lift_refused_as_lean() {
    let report = check_module(
        "def g52 : Id Nat := do\n  let rec k : Nat := (← pure 1) + 1\n  return k\n\n\
         def g52fun : Id Nat := do\n  let g := fun (x : Nat) => x + (← pure 1)\n  return g 1\n\n\
         def g52bind : Id Nat := do\n  let rec go (n : Nat) : Nat := n + (← pure 1)\n  return go 3\n",
    );
    assert_refused_with(&report, "g52", &[LIFT_OVER_BINDER]);
    assert_refused_with(&report, "g52fun", &[LIFT_OVER_BINDER]);
    assert_refused_with(&report, "g52bind", &[LIFT_OVER_BINDER]);
}

#[test]
fn test_do_let_rec_nested_do_lift_passes() {
    // The `do` inside the recursive value is a lift delimiter: Lean accepts.
    let report = check_module(
        "def g52ok : Id Nat := do\n  let rec go (n : Nat) : Id Nat := do return n + (← pure 1)\n  go 3\n\n\
         theorem g52ok_v : g52ok = 4 := rfl\n",
    );
    assert_passed(&report, "g52ok");
    assert_passed(&report, "g52ok_v");
}

#[test]
fn test_do_return_not_last_refused_as_lean() {
    let report = check_module(
        "def rl : Id Nat := do\n  return 1\n  pure 2\n\n\
         def g54h : Except String Nat := do\n  try\n    return 1\n    pure 2\n  catch _ => pure 3\n\n\
         def brk (xs : List Nat) : Id Unit := do\n  for _ in xs do\n    break\n    pure ()\n",
    );
    for name in ["rl", "g54h", "brk"] {
        assert_refused_with(&report, name, &["must be last element in a `do` sequence"]);
    }
}

#[test]
fn test_do_try_terminal_early_return_type_checked() {
    // G54: the early `return ()` is checked against the block's `Nat`.
    let report = check_module(
        "def g54f (b : Bool) : Except String Nat := do\n  try\n    if b then return ()\n    pure 2\n  catch _ => pure 3\n",
    );
    let v = verdict(&report, "g54f");
    assert_ne!(v.kind, VerdictKind::Passed, "Lean refuses g54f: {v:#?}");
}

/// Still OPEN in ledger (124): an early `return` through a terminal `try`
/// that Lean ACCEPTS (`g54e true = .ok 1`, `g54e false = .ok 3`, measured
/// with pinned Lean 4.8.0) now takes the transformer-stack lane, whose result
/// is not unwrapped ("Type mismatch: … Except String (Except Nat …)"). Before
/// G54 it was refused too, by the kernel (`expected Unit, got Nat`). Flip to
/// `assert_passed` when it closes.
#[test]
fn test_do_try_terminal_early_return_through_stack_known_gap() {
    let report = check_module(
        "def g54e (b : Bool) : Except String Nat := do\n  try\n    if b then return 1\n    throw \"boom\"\n  catch _ => pure 3\n",
    );
    assert_refused_with(&report, "g54e", &["Type mismatch"]);
}

#[test]
fn test_do_catch_binder_in_scope_passes() {
    let report = check_module(
        "def cb (e : String) : Except String String := do\n  try\n    throw \"inner\"\n  catch e => pure e\n\n\
         theorem cb_inner : cb \"outer\" = .ok \"inner\" := rfl\n\n\
         def cb2 : Except String String := do\n  try\n    throw \"boom\"\n  catch err => pure (err ++ \"!\")\n\n\
         theorem cb2_v : cb2 = .ok \"boom!\" := rfl\n",
    );
    assert_passed(&report, "cb");
    assert_passed(&report, "cb_inner");
    assert_passed(&report, "cb2");
    assert_passed(&report, "cb2_v");
}

#[test]
fn test_do_catch_binder_outer_capture_refused() {
    // G61's false acceptance: the handler returned the OUTER `e`.
    let report = check_module(
        "def cb (e : String) : Except String String := do\n  try\n    throw \"inner\"\n  catch e => pure e\n\n\
         theorem cb_outer : cb \"outer\" = .ok \"outer\" := rfl\n",
    );
    assert_passed(&report, "cb");
    let v = verdict(&report, "cb_outer");
    assert_ne!(v.kind, VerdictKind::Passed, "Lean refuses cb_outer: {v:#?}");
}

#[test]
fn test_do_nested_sequence_lifts_pass() {
    let report = check_module(
        "def g30a (b : Bool) : Id Nat := do\n  if b then\n    let x := (← pure 1) + 1\n    return x\n  else\n    return 0\n\n\
         theorem g30a_v : g30a true = 2 := rfl\n\n\
         def g30b : Id Nat := do\n  match ← pure (some 3) with\n  | some x => return x\n  | none => return 0\n\n\
         theorem g30b_v : g30b = 3 := rfl\n\n\
         def g30e (b : Bool) : Except String Nat := do\n  try\n    let y := (← if b then pure 4 else throw \"no\") + 1\n    return y\n  catch _ => return 0\n\n\
         theorem g30e_t : g30e true = .ok 5 := rfl\n\
         theorem g30e_f : g30e false = .ok 0 := rfl\n",
    );
    for name in [
        "g30a", "g30a_v", "g30b", "g30b_v", "g30e", "g30e_t", "g30e_f",
    ] {
        assert_passed(&report, name);
    }
}

#[test]
fn test_do_nested_sequence_lift_wrong_values_refused() {
    let report = check_module(
        "def g30a (b : Bool) : Id Nat := do\n  if b then\n    let x := (← pure 1) + 1\n    return x\n  else\n    return 0\n\n\
         theorem g30a_bad : g30a true = 1 := rfl\n\n\
         def g30b : Id Nat := do\n  match ← pure (some 3) with\n  | some x => return x\n  | none => return 0\n\n\
         theorem g30b_bad : g30b = 0 := rfl\n\n\
         def g30t (b : Bool) : Id Nat := do\n  let x := if b then (← pure 1) else 0\n  return x\n",
    );
    for name in ["g30a_bad", "g30b_bad"] {
        let v = verdict(&report, name);
        assert_ne!(v.kind, VerdictKind::Passed, "Lean refuses {name}: {v:#?}");
    }
    // A lift in a TERM `if` branch is not lifted (Lean: "invalid use of
    // `(<- ...)`, must be nested inside a 'do' expression").
    let v = verdict(&report, "g30t");
    assert_ne!(v.kind, VerdictKind::Passed, "Lean refuses g30t: {v:#?}");
}

/// G63 (ledger (133)): the builtin prelude has no `Lean.Loop`, so no
/// `while`/`repeat` loop elaborates; pinned Lean 4.8.0 accepts this source.
/// Flip to `assert_passed` when it closes (and add G53's semantic check:
/// with a fuel-bounded `ForIn m Lean.Loop Unit` instance Lean's `rfl`
/// computes `(StateT.run g53 0).2 = 3` and refuses `5`).
#[test]
fn test_do_while_loop_without_lean_loop_known_gap() {
    let report = check_module(
        "def g53 : StateT Nat Id Unit := do\n  while (← StateT.get) < 3 do\n    StateT.modifyGet fun s => ((), s + 1)\n",
    );
    assert_refused_with(&report, "g53", &["Lean.Loop"]);
}

/// KNOWN FALSE ACCEPTANCE (trust-ir ID G65, ledger (132), OPEN): `try …
/// finally` in a monad with no `MonadFinally` instance. Pinned Lean 4.8.0
/// refuses `fin2` ("failed to synthesize instance MonadFinally (Except
/// String)", measured 2026-10-16); Clean's builtin `tryFinally` is an
/// instance-free axiom, so the block is accepted. This pin fails the day it
/// closes: then assert the refusal instead.
#[test]
fn test_do_finally_without_monad_finally_known_false_acceptance() {
    let report = check_module(
        "def fin2 : Except String Nat := do\n  try return 1 catch _ => return 2 finally pure ()\n",
    );
    assert_passed(&report, "fin2");
}
