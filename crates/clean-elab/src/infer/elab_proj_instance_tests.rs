// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G37 / ledger class (107) and G47 / ledger class (117), which co-land.
//!
//! G37: generalized field notation `ids.mapM look` queues the `[Monad ?m]`
//! goal its receiver does not pin, instead of dropping it.
//! G47: instance synthesis runs at Lean's `.instances` transparency, so a
//! semireducible `def M a := Option a` is not `Option` to it — without G47,
//! G37 alone turns `neg_dot` below into a FALSE ACCEPTANCE.
//!
//! Every source was run through the pinned Lean 4.8.0 binary (2026-10-08):
//! declarations asserted refused here are refused there ("failed to
//! synthesize instance Monad M", or `type mismatch` for a false value).

use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DeclVerdict, DriverOptions, EnvironmentSetup, ModuleReport,
    VerdictKind,
};
use std::path::Path;

fn check_module(source: &str) -> ModuleReport {
    let _lock = module_elaboration_lock();
    let path = Path::new("DotReceiverInstanceFixture.lean");
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

fn refused_detail(report: &ModuleReport, name: &str) -> String {
    let v = verdict(report, name);
    assert_ne!(
        v.kind,
        VerdictKind::Passed,
        "`{name}` must be refused: {v:#?}"
    );
    v.detail.clone().unwrap_or_default()
}

/// G37, the minimized trust-ir shape: `ids.mapM look` at `Option`, where only
/// `look` pins the monad. A true value checks; a false one is refused.
#[test]
fn test_dot_receiver_monad_goal_pinned_by_later_argument_passes() {
    let report = check_module(
        "def look (i : Nat) : Option Nat := some i\n\
         def br (ids : List Nat) : Option (List Nat) := ids.mapM look\n\
         theorem br_val : br [1, 2] = some [1, 2] := rfl\n\
         theorem br_wrong : br [1, 2] = some [2, 1] := rfl\n",
    );
    assert_passed(&report, "br");
    assert_passed(&report, "br_val");
    refused_detail(&report, "br_wrong");
}

/// G37 through an `abbrev`'d monad stack (trust-ir's `Sem`): `@[reducible]`
/// unfolds at `.instances` transparency, so the instance is found.
#[test]
fn test_dot_receiver_monad_goal_through_abbrev_stack_passes() {
    let report = check_module(
        "abbrev Sem (a : Type) := StateT Nat (Except String) a\n\
         def look (i : Nat) : Sem Nat := pure (i + 1)\n\
         def br (ids : List Nat) : Sem (List Nat) := do\n  \
           let xs ← ids.mapM look\n  pure xs\n",
    );
    assert_passed(&report, "br");
}

/// `abbrev M a := Option a`: reducible, so both spellings find
/// `Monad Option`; a false value is refused.
#[test]
fn test_instance_search_unfolds_reducible_alias() {
    let report = check_module(
        "abbrev M (a : Type) := Option a\n\
         def look (i : Nat) : M Nat := (some i : Option Nat)\n\
         def br (ids : List Nat) : M (List Nat) := List.mapM look ids\n\
         def br2 (ids : List Nat) : M (List Nat) := ids.mapM look\n\
         theorem br2_val : br2 [1, 2] = some [1, 2] := rfl\n\
         theorem br2_wrong : br2 [1, 2] = some [1, 3] := rfl\n",
    );
    assert_passed(&report, "br");
    assert_passed(&report, "br2");
    assert_passed(&report, "br2_val");
    refused_detail(&report, "br2_wrong");
}

/// G47, the FALSE ACCEPTANCE: `def M a := Option a` is semireducible, so
/// Lean's instance search does not see `Option` through it ("failed to
/// synthesize instance Monad M"). Clean accepted `List.mapM look ids` by
/// delta-unfolding `M` while matching `instMonadOption`. Both spellings are
/// refused: the dot form must stay refused once G37 queues its goal.
#[test]
fn test_instance_search_does_not_unfold_semireducible_def_refused() {
    let report = check_module(
        "def M (a : Type) := Option a\n\
         def look (i : Nat) : M Nat := (some i : Option Nat)\n\
         def brc (ids : List Nat) : M (List Nat) := List.mapM look ids\n\
         def brd (ids : List Nat) : M (List Nat) := ids.mapM look\n",
    );
    assert_passed(&report, "look");
    for name in ["brc", "brd"] {
        let detail = refused_detail(&report, name);
        assert!(
            detail.contains("Monad"),
            "`{name}` is refused on the `Monad M` goal: {detail}"
        );
    }
}

/// G47 through a LOCAL instance: `[inst : Foo Nat]` does not answer the goal
/// `Foo (Wrap Nat)` for a semireducible `def Wrap α := α` (pinned Lean 4.8.0:
/// "failed to synthesize instance Foo (Wrap Nat)" for both `g` and `g3`),
/// while an `abbrev` alias does, and the plain `Foo Nat` goal keeps its local.
#[test]
fn test_local_instance_not_matched_through_semireducible_def() {
    let report = check_module(
        "class Foo (α : Type) where\n  x : α\n\
         def Wrap (α : Type) := α\n\
         abbrev AWrap (α : Type) := α\n\
         def g [inst : Foo Nat] : Foo (Wrap Nat) := inferInstance\n\
         def g3 [inst : Foo Nat] : Wrap Nat := @Foo.x (Wrap Nat) _\n\
         def ga [inst : Foo Nat] : AWrap Nat := @Foo.x (AWrap Nat) _\n\
         def h [inst : Foo Nat] : Nat := Foo.x\n",
    );
    for name in ["g", "g3"] {
        let detail = refused_detail(&report, name);
        assert!(
            detail.contains("Foo"),
            "`{name}` refused on the `Foo (Wrap Nat)` goal: {detail}"
        );
    }
    assert_passed(&report, "ga");
    assert_passed(&report, "h");
}

/// CLOSED 2026-10-24 (pinned as a known divergence 2026-10-08): with the
/// RESULT type `Wrap Nat` of a `def` signature as the expected type, `Foo.x`'s
/// `?α` was solved from the expected type after it had been reduced to `Nat`,
/// so the goal was `Foo Nat` and the local instance answered it. Both pinned
/// Leans (4.8.0, 4.30.0-rc2; re-measured 2026-10-24) solve `?α := Wrap Nat` and
/// refuse ("failed to synthesize instance Foo (Wrap Nat)"). The round-6
/// review's X2 fix (`unify_carrier_with_expected`, DECISIONS R70's note: a
/// bare-metavariable carrier is unified with the expected type as written when
/// its head is not reducible) closed it. The `abbrev` and plain-`Nat` controls
/// pass in `test_local_instance_not_matched_through_semireducible_def`.
#[test]
fn test_expected_type_is_not_reduced_before_instance_goal() {
    let report = check_module(
        "class Foo (α : Type) where\n  x : α\n\
         def Wrap (α : Type) := α\n\
         def g [inst : Foo Nat] : Wrap Nat := Foo.x\n",
    );
    let detail = refused_detail(&report, "g");
    assert!(
        detail.contains("Foo (Wrap Nat)"),
        "`g` refused on the `Foo (Wrap Nat)` goal: {detail}"
    );
}

/// G47 must not cut an instance DECLARED on a semireducible wrapper:
/// `instance [C α] : C (Wrap α)` answers `C (Wrap Nat)` through its subgoal
/// `C Nat` (Mathlib's `OrderDual`/`Multiplicative` idiom; pinned Lean 4.8.0
/// accepts `w1` and `y2`, refuses `y3`). The instance-search cycle key once
/// normalized class arguments at DEFAULT transparency, so `C Nat` collided
/// with `C (Wrap Nat)` and was cut off as a cycle.
#[test]
fn test_instance_declared_on_semireducible_wrapper_passes() {
    let report = check_module(
        "def Wrap (α : Type) := α\n\
         instance [Inhabited α] : Inhabited (Wrap α) := ⟨(default : α)⟩\n\
         def w1 : Inhabited (Wrap Nat) := inferInstance\n\
         def w3 : Inhabited (Wrap (Wrap Nat)) := inferInstance\n\
         class C (α : Type) where c : Nat\n\
         instance : C Nat := ⟨1⟩\n\
         instance instW {α : Type} [C α] : C (Wrap α) := ⟨C.c α + 10⟩\n\
         theorem y2 : C.c (Wrap Nat) = 11 := rfl\n\
         theorem y3 : C.c (Wrap Nat) = 1 := rfl\n",
    );
    for name in ["w1", "w3", "y2"] {
        assert_passed(&report, name);
    }
    refused_detail(&report, "y3");
}

/// KNOWN DIVERGENCE, OPEN — ACCEPTED, LEAN REFUSES (pinned 2026-10-08): the
/// numeric-literal, binop and coercion shapes of the G47 class. Through a
/// semireducible `def MyNat := Nat`, Clean still finds `OfNat Nat`/`HAdd Nat`
/// (`b1`, `b2`) and the `Nat → Int` coercion (`a7`); pinned Lean 4.8.0 refuses
/// all three ("failed to synthesize instance", "type mismatch"). Fails the day
/// it closes — then turn it into a refusal pin.
#[test]
fn test_literal_binop_coercion_through_semireducible_def_known_divergence() {
    let report = check_module(
        "def MyNat := Nat\n\
         def b1 (a : MyNat) : MyNat := a + 1\n\
         def b2 : MyNat := 0\n\
         def a7 (a : MyNat) : Int := a\n",
    );
    for name in ["b1", "b2", "a7"] {
        assert_passed(&report, name);
    }
}
