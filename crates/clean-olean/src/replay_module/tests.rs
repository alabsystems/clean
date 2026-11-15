// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay`'s engine against `leanchecker`'s verdicts.
//!
//! The `.olean`s are the `replay_forged` fixture family, minted by the pinned
//! Lean (`GenReplayForged.lean`); each module's `leanchecker` verdict is in the
//! family's README, measured with the pinned v4.30.0-rc2 binary. Every forged
//! module must be refused with the declaration named, and every honest one
//! admitted in full.

use std::path::PathBuf;

use super::*;
use crate::test_support::compiled_fixture_dir;
use crate::ImportError;

const FAMILY: &str = "replay_forged";

fn search() -> Vec<PathBuf> {
    replay_search_path(
        &[compiled_fixture_dir(FAMILY)],
        None,
        crate::pinned_lean_lib_path(),
    )
    .unwrap_or_else(|e| panic!("the replay fixtures need the pinned toolchain: {e}"))
}

fn replay(module: &str, mode: ReplayMode) -> ModuleReplayRecord {
    replay_module(module, mode, &search(), 0)
}

fn assert_admitted(record: &ModuleReplayRecord, checked: usize) {
    assert!(
        record.ok && record.load_error.is_none() && record.refusals.is_empty(),
        "{}: {record:?}",
        record.module
    );
    assert_eq!(record.constants_checked, checked, "{record:?}");
    assert_eq!(record.admitted, checked, "{record:?}");
}

fn assert_refused(record: &ModuleReplayRecord, constant: &str, needle: &str) {
    assert!(!record.ok, "{}: must be refused: {record:?}", record.module);
    assert!(record.first_refusal.is_some(), "{record:?}");
    let refusal = record
        .refusals
        .iter()
        .find(|r| r.constant == constant)
        .unwrap_or_else(|| panic!("`{constant}` must be refused: {:?}", record.refusals));
    assert!(
        refusal.reason.contains(needle),
        "`{constant}` refused without `{needle}`: {}",
        refusal.reason
    );
}

#[test]
fn test_replay_module_self_reference_and_cycle_are_refused() {
    let record = replay("ReplayForged3", ReplayMode::ImportsTrusted);
    assert_eq!(record.constants_checked, 3, "{record:?}");
    assert_eq!(record.admitted, 0, "{record:?}");
    assert_refused(&record, "forged3_self", "refers to itself");
    assert_refused(&record, "forged3_cycB", "dependency cycle");
    assert_refused(&record, "forged3_cycA", "depends on `forged3_cycB`");

    let record = replay("ReplayForged", ReplayMode::ImportsTrusted);
    assert_refused(&record, "forged_self", "refers to itself");
    assert_refused(&record, "forged_bad", "TypeMismatch");
}

/// `leanchecker ReplayForged4`: `(kernel) declaration type mismatch` — the
/// platform queries are `@[extern] opaque` and stuck in Lean's kernel.
#[test]
fn test_replay_module_platform_booleans_are_stuck_as_in_lean() {
    let record = replay("ReplayForged4", ReplayMode::ImportsTrusted);
    assert_eq!(record.admitted, 0, "{record:?}");
    for name in [
        "forged4_osx",
        "forged4_not_osx",
        "forged4_not_windows",
        "forged4_not_emscripten",
    ] {
        assert_refused(&record, name, "TypeMismatch");
    }
    assert_admitted(&replay("ReplayHonest4", ReplayMode::ImportsTrusted), 1);
}

#[test]
fn test_replay_module_unsafe_is_left_out_and_its_safe_user_refused() {
    let record = replay("ReplayForged5", ReplayMode::ImportsTrusted);
    assert_refused(&record, "forged5_unsafe", "UnsafeDeclaration");

    let honest = replay("ReplayHonestUnsafe", ReplayMode::ImportsTrusted);
    assert_admitted(&honest, 1);
    assert_eq!(honest.not_replayable, 1, "{honest:?}");
}

/// `leanchecker ReplayCrossB` accepts (its import is trusted);
/// `leanchecker --fresh ReplayCrossB` refuses (`unknown constant 'cross_forged'`).
#[test]
fn test_replay_module_imports_are_trusted_unless_fresh() {
    let record = replay("ReplayCrossA", ReplayMode::ImportsTrusted);
    assert_refused(&record, "cross_forged", "refers to itself");
    assert_eq!(record.admitted, 1, "{record:?}");

    assert_admitted(&replay("ReplayCrossB", ReplayMode::ImportsTrusted), 2);

    let fresh = replay("ReplayCrossB", ReplayMode::Fresh);
    assert_eq!(fresh.mode, ReplayMode::Fresh);
    assert_refused(&fresh, "cross_forged", "refers to itself");
    assert_refused(&fresh, "cross_uses_forged", "cross_forged");
    assert!(
        fresh.constants_checked > 100,
        "--fresh replays Init.Prelude too: {}",
        fresh.constants_checked
    );
}

/// `leanchecker --fresh ReplayHonest` (Init.Prelude and the module) exits 0:
/// the whole prelude replays in Lean's order from an empty environment.
#[test]
fn test_replay_module_honest_modules_are_admitted_fresh_or_not() {
    assert_admitted(&replay("ReplayHonest", ReplayMode::ImportsTrusted), 4);
    let fresh = replay("ReplayHonest", ReplayMode::Fresh);
    assert!(fresh.ok, "{:?}", fresh.first_refusal);
    assert_eq!(fresh.admitted, fresh.constants_checked, "{fresh:?}");
    assert_admitted(&replay("ReplayHonestUniv", ReplayMode::ImportsTrusted), 1);
}

/// Clean's prelude is not in the replay environment: `sorry`, `trustedArith`
/// and `trustedAy` are unknown constants, and a module-local name Clean's
/// prelude also holds is the module's own declaration.
#[test]
fn test_replay_module_prelude_only_constants_are_unknown() {
    let record = replay("ReplayPrelude", ReplayMode::ImportsTrusted);
    for forged in ["prelude_sorry", "prelude_arith", "prelude_ay"] {
        assert_refused(&record, forged, "UnknownConst");
    }
    assert_refused(&record, "Nat.not_succ_lt_zero", "TypeMismatch");
    assert_eq!(record.admitted, 1, "prelude_honest: {record:?}");

    let used = replay("ReplayPreludeUse", ReplayMode::ImportsTrusted);
    assert_refused(&used, "prelude_shadow_use", "TypeMismatch");
}

/// `leanchecker ReplayRedeclare`: `(kernel) constant has already been
/// declared 'Nat.pred'`, in the replay, so `redecl_pred` gets its own verdict
/// (against `Init.Prelude`'s `Nat.pred`); `leanchecker --fresh
/// ReplayRedeclare`: `import ReplayRedeclare failed, environment already
/// contains 'Nat.pred' from Init.Prelude`, at the import. Never an unnamed
/// load error, which the loader's own duplicate rule used to make it.
#[test]
fn test_replay_module_redeclaration_is_refused() {
    let record = replay("ReplayRedeclare", ReplayMode::ImportsTrusted);
    assert!(record.load_error.is_none(), "{record:?}");
    assert_refused(&record, "Nat.pred", "already declared");
    assert_refused(&record, "Nat.pred", "replay order:");
    assert!(
        record.refusals.iter().any(|r| r.constant == "redecl_pred"),
        "{:?}",
        record.refusals
    );
    let fresh = replay("ReplayRedeclare", ReplayMode::Fresh);
    assert!(fresh.load_error.is_none(), "{fresh:?}");
    assert_refused(
        &fresh,
        "Nat.pred",
        "import ReplayRedeclare failed, environment already contains 'Nat.pred'",
    );
}

/// Stored recursors, recursor rules and constructors are regenerated by the
/// kernel and compared (`checkPostponedRecursors`/`Constructors`); the
/// stored quotient is the kernel's canonical one.
///
/// A forged recursor record never becomes resident: the loader refuses it as
/// not the recursor the kernel generates from the stored family
/// (clean-kernel `env/imported_family.rs`), and the replay refuses it by name
/// with that reason. Its block is refused with it, as in every other lane
/// (`replay_forged_lanes.rs`): `leanchecker ReplayForgedRec` reports `Invalid
/// recursor FRT.rec` for the stored record, so no member of the block is
/// admitted as stored. Before the block check read the load-refused recursor,
/// `FRT`, `FRT.a` and `FRT.b` were admitted (3 of 5).
#[test]
fn test_replay_module_forged_inductive_blocks_and_quotient_are_refused() {
    for (module, user) in [
        ("ReplayForgedRec", "forged_rec_false"),
        ("ReplayForgedRule", "forged_rule_eq"),
        ("ReplayForgedCtor", "forged_ctor_false"),
        ("ReplayForgedQuot", "forged_quot_false"),
    ] {
        let record = replay(module, ReplayMode::ImportsTrusted);
        assert!(
            record.refusals.iter().any(|r| r.constant == user),
            "{module}: `{user}` must be refused: {:?}",
            record.refusals
        );
        assert_eq!(record.admitted, 0, "{module}: {record:?}");
    }
    let rec = replay("ReplayForgedRec", ReplayMode::ImportsTrusted);
    assert_refused(&rec, "FRT.rec", "imported family record FRT.rec refused");
    assert_refused(&rec, "FRT.rec", "kernel generates");
    for member in ["FRT", "FRT.a", "FRT.b"] {
        assert_refused(&rec, member, "Invalid recursor FRT.rec");
    }
    let rule = replay("ReplayForgedRule", ReplayMode::ImportsTrusted);
    for member in ["FRR", "FRR.a", "FRR.b"] {
        assert_refused(&rule, member, "Invalid recursor FRR.rec");
    }
}

/// Each block shape the kernel distinguishes, compiled by Lean with every
/// auxiliary definition its elaborator adds (`noConfusion` included, checked
/// as STORED — the loader's regeneration is not run by the replay).
#[test]
fn test_replay_module_honest_inductive_blocks_are_admitted() {
    let record = replay("ReplayHonestInd", ReplayMode::ImportsTrusted);
    assert!(record.ok, "{:?}", record.refusals);
    assert!(record.constants_checked > 100, "{record:?}");
    assert_eq!(record.admitted, record.constants_checked, "{record:?}");
}

/// What `--max-heartbeats N` bounds, as its help states it: each check of a
/// declaration runs under N, the inductive-block rebuild does not, and a
/// declaration whose checks ran out of budget is refused as BUDGET EXHAUSTED,
/// never admitted and never reported as a finding.
///
/// The module is admitted in full at `0` (the test above), so at `1` every
/// refusal is the budget's doing. None of them is a block refusal: the
/// rebuild, which no admission of a block could finish in one heartbeat, ran
/// under the kernel's default limit. And none may read as the kernel's verdict:
/// `whnf`/`is_def_eq` stop silently once the budget is spent, so a starved
/// check fails with whatever the under-reduction produced (it used to be
/// reported as a bare `TypeMismatch`); each refusal must name the budget.
#[test]
fn test_replay_module_max_heartbeats_bounds_declaration_checks_not_block_rebuilds() {
    let record = replay_module("ReplayHonestInd", ReplayMode::ImportsTrusted, &search(), 1);
    assert!(
        !record.ok,
        "one heartbeat per check must refuse: {record:?}"
    );
    assert_eq!(
        record.admitted + record.refusals.len(),
        record.constants_checked,
        "{record:?}"
    );
    assert_eq!(
        record.budget_exhausted,
        record.refusals.len(),
        "every refusal of an honest module at one heartbeat is the budget's: {:?}",
        record.refusals
    );
    for refusal in &record.refusals {
        assert_eq!(
            refusal.outcome,
            RefusalOutcome::BudgetExhausted,
            "{refusal:?}"
        );
        assert!(
            refusal.reason.starts_with("budget exhausted: `")
                || (refusal
                    .reason
                    .contains("which was not admitted (budget exhausted: `")),
            "a starved declaration, or a dependent of one, must name the budget: {refusal:?}"
        );
    }
    let first = record
        .first_refusal
        .as_ref()
        .expect("a refused module names one");
    assert_eq!(first.outcome, RefusalOutcome::BudgetExhausted, "{first:?}");
    // The starved check's own kernel error is still shown, behind the budget.
    // The kernel reports a def-eq cut short by a spent budget as
    // HeartbeatExceeded in every build profile; the debug certificate path used
    // to report it as TypeMismatch (the misreport this record works around),
    // and no refusal of this honest module may read as one.
    assert!(
        record
            .refusals
            .iter()
            .any(|r| r.reason.starts_with("budget exhausted: `")
                && r.reason.contains("HeartbeatExceeded")),
        "the starved check's own error (the kernel's HeartbeatExceeded) is still shown, \
         behind the budget: {:?}",
        record.refusals
    );
    assert!(
        record
            .refusals
            .iter()
            .all(|r| !r.reason.contains("TypeMismatch")),
        "a starved check of an honest module reported as a type mismatch: {:?}",
        record.refusals
    );
    let json = serde_json::to_string(&record).expect("the record serializes");
    assert!(json.contains("\"outcome\":\"budget-exhausted\""), "{json}");
    let block_refusals: Vec<&RefusalRecord> = record
        .refusals
        .iter()
        .filter(|r| {
            [
                "inductive block `",
                "Invalid constructor",
                "Invalid recursor",
                "No such ",
            ]
            .iter()
            .any(|needle| r.reason.contains(needle))
        })
        .collect();
    assert!(
        block_refusals.is_empty(),
        "the inductive-block rebuild is not under --max-heartbeats: {block_refusals:?}"
    );
}

/// A starved check never decides a later one (`local_roster::ReplayChecker`
/// replaces the kernel checker after it): at every small budget, each refusal
/// of the honest module is the budget's. Measured 2026-09-30 while one
/// checker kept a starved check's memoised `whnf`/`is_def_eq` answers: 60 of
/// 105 refusals at 2, 17 of 88 at 3, 11 of 78 at 5 and 8 of 65 at 8 read as
/// findings (outcome `refused`, no budget named), `HOd.succ` failing
/// `TypeMismatch` right after the starved `HEv.succ`. One heartbeat (above)
/// starves every check, so it cannot see this.
#[test]
fn test_replay_module_small_budgets_never_report_a_finding_on_an_honest_module() {
    let search = search();
    let mut starved_somewhere = false;
    for limit in [2, 3, 5, 8, 13, 21, 34, 55] {
        let record = replay_module(
            "ReplayHonestInd",
            ReplayMode::ImportsTrusted,
            &search,
            limit,
        );
        let findings: Vec<&RefusalRecord> = record
            .refusals
            .iter()
            .filter(|r| r.outcome == RefusalOutcome::Refused)
            .collect();
        assert!(
            findings.is_empty(),
            "--max-heartbeats {limit}: {} of {} refusal(s) of an honest module read as \
             findings: {findings:?}",
            findings.len(),
            record.refusals.len()
        );
        assert_eq!(record.budget_exhausted, record.refusals.len(), "{record:?}");
        assert_eq!(
            record.admitted + record.refusals.len(),
            record.constants_checked,
            "{record:?}"
        );
        starved_somewhere |= !record.refusals.is_empty();
    }
    assert!(
        starved_somewhere,
        "control: some budget must starve a check, or this pins nothing"
    );
}

/// The control of the test above: a normal finite budget (the kernel's
/// default, `DEFAULT_HEARTBEAT_LIMIT`) admits the honest module in full, so
/// the refusals at one heartbeat are the budget's and not the checks'.
#[test]
fn test_replay_module_default_finite_budget_admits_honest_module() {
    let record = replay_module(
        "ReplayHonestInd",
        ReplayMode::ImportsTrusted,
        &search(),
        clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT,
    );
    assert!(record.ok, "{:?}", record.refusals);
    assert_eq!(record.budget_exhausted, 0, "{record:?}");
    assert_eq!(record.admitted, record.constants_checked, "{record:?}");
}

/// Budget exhaustion never launders a finding: an ill-typed declaration checked
/// under a finite budget with room to spare is refused as the kernel's verdict
/// (`outcome: refused`), not as budget exhausted.
#[test]
fn test_replay_module_finding_under_finite_budget_is_not_budget_exhausted() {
    let record = replay_module(
        "ReplayForgedThmType",
        ReplayMode::ImportsTrusted,
        &search(),
        clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT,
    );
    assert_refused(&record, "forged_thm_nat", "not a proposition");
    assert_eq!(record.budget_exhausted, 0, "{record:?}");
    assert!(
        record
            .refusals
            .iter()
            .all(|r| r.outcome == RefusalOutcome::Refused && !r.reason.contains("budget")),
        "{:?}",
        record.refusals
    );
}

/// Lean's `add_theorem`: `(kernel) type of theorem 'forged_thm_nat' is not a
/// proposition`.
#[test]
fn test_replay_module_theorem_whose_type_is_not_a_proposition_is_refused() {
    let record = replay("ReplayForgedThmType", ReplayMode::ImportsTrusted);
    assert_refused(&record, "forged_thm_nat", "not a proposition");
}

/// `(kernel) invalid reference to undefined universe level parameter 'u'` and
/// `duplicate universe level parameter: 'u'`: the loader's structural tier
/// refuses to register either, and the replay refuses what was not registered.
#[test]
fn test_replay_module_universe_header_forgeries_are_refused() {
    let record = replay("ReplayForgedUniv", ReplayMode::ImportsTrusted);
    assert_refused(&record, "forged_univ", "could not register it as stored");
    assert_refused(
        &record,
        "forged_univ",
        "Undefined universe level parameter 'u'",
    );

    let record = replay("ReplayForgedDupUniv", ReplayMode::ImportsTrusted);
    assert_refused(
        &record,
        "forged_dup_univ",
        "Duplicate universe level parameter 'u'",
    );
}

/// `leanchecker ReplayForgedLamType`: `(kernel) type expected` — the "type"
/// of `forged_lam_ax` is a lambda. The replay refuses it by Lean's
/// `ensure_sort` in both modes, and the theorem stated by it with it.
#[test]
fn test_replay_module_lambda_typed_axiom_is_refused_type_expected() {
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let record = replay("ReplayForgedLamType", mode);
        assert_refused(&record, "forged_lam_ax", "type expected");
        assert!(
            record
                .refusals
                .iter()
                .any(|r| r.constant == "forged_lam_thm"),
            "{mode:?}: {:?}",
            record.refusals
        );
    }
}

/// A module that DEFINES an imported axiom: `leanchecker ReplayForgedBoolDef`
/// checks `forged_bool_false : False` against the imported axiom and refuses
/// it (`application type mismatch`); `--fresh` aborts at the import. The
/// kernel-only load no longer fills the import's `bool_ax_b` with the module's
/// value, so the proof of `False` that unfolds it is refused too, not only the
/// redefinition. The control is the import itself, admitted.
///
/// Each refusal is at Lean's layer, and never an unnamed load error (the
/// loader's own rule refuses the whole import for a name two artifacts
/// declare; the replay's load leaves it to the replay): pinned `leanchecker
/// ReplayForgedBoolDef` refuses in its replay, and `leanchecker --fresh
/// ReplayForgedBoolDef` with `import ReplayForgedBoolDef failed, environment
/// already contains 'bool_ax_b' from ReplayHonestBoolAx`.
#[test]
fn test_replay_module_definition_of_an_imported_axiom_is_refused_with_its_false_proof() {
    assert_admitted(&replay("ReplayHonestBoolAx", ReplayMode::ImportsTrusted), 2);
    let record = replay("ReplayForgedBoolDef", ReplayMode::ImportsTrusted);
    assert!(record.load_error.is_none(), "{record:?}");
    assert_refused(&record, "bool_ax_b", "already declared");
    assert_refused(&record, "bool_ax_b", "replay order:");
    assert!(
        record
            .refusals
            .iter()
            .any(|r| r.constant == "forged_bool_false"),
        "the proof of False must be refused: {:?}",
        record.refusals
    );
    assert_eq!(record.admitted, 0, "{record:?}");
    let fresh = replay("ReplayForgedBoolDef", ReplayMode::Fresh);
    assert!(fresh.load_error.is_none(), "{fresh:?}");
    assert_refused(&fresh, "bool_ax_b", "already declared");
    assert_refused(
        &fresh,
        "bool_ax_b",
        "import ReplayForgedBoolDef failed, environment already contains 'bool_ax_b'",
    );
    assert_eq!(
        fresh.first_refusal.as_ref().map(|r| r.constant.as_str()),
        Some("bool_ax_b"),
        "--fresh: the import's refusal comes first, as leanchecker's does: {fresh:?}"
    );
    assert!(
        fresh
            .refusals
            .iter()
            .any(|r| r.constant == "forged_bool_false"),
        "--fresh: the proof of False must be refused: {:?}",
        fresh.refusals
    );
}

/// The one cross-module pair Lean's import merges, a theorem over an imported
/// axiom of its statement (`subsumesInfo`): `leanchecker
/// ReplayForgedThmOverAx` refuses the theorem (`already declared`), and
/// `--fresh` accepts the module. The control for the repair above, which must
/// not refuse what the merge admits.
#[test]
fn test_replay_module_theorem_over_imported_axiom_follows_lean_import_merge() {
    assert_admitted(&replay("ReplayHonestPropAx", ReplayMode::ImportsTrusted), 1);
    let record = replay("ReplayForgedThmOverAx", ReplayMode::ImportsTrusted);
    assert!(
        record.refusals.iter().any(|r| r.constant == "prop_ax_p"),
        "{:?}",
        record.refusals
    );
    let fresh = replay("ReplayForgedThmOverAx", ReplayMode::Fresh);
    assert!(fresh.ok, "--fresh merges them: {:?}", fresh.refusals);
}

/// An INDUCTIVE over an imported axiom of its name, with a proof of `False`
/// that holds only if the module's inductive replaces the import's axiom
/// (`ind_ax_not ind_ax_t.mk`). Pinned `leanchecker ReplayForgedIndOverAx`:
/// `(kernel) constant has already been declared 'ind_ax_t'`; `leanchecker
/// --fresh`: `import ReplayForgedIndOverAx failed, environment already
/// contains 'ind_ax_t' from ReplayHonestIndAx`. Under the replay's load the
/// loader's rule 1 no longer refuses the import, and its carrier-stub
/// discharge then let the inductive displace the imported axiom unrecorded, so
/// every declaration was admitted, the proof of `False` included. The control
/// is the import itself, admitted.
#[test]
fn test_replay_module_inductive_over_an_imported_axiom_is_refused_with_its_false_proof() {
    assert_admitted(&replay("ReplayHonestIndAx", ReplayMode::ImportsTrusted), 2);
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let record = replay("ReplayForgedIndOverAx", mode);
        assert!(record.load_error.is_none(), "{mode:?}: {record:?}");
        assert_refused(&record, "ind_ax_t", "already");
        assert!(
            record
                .refusals
                .iter()
                .any(|r| r.constant == "forged_ind_false"),
            "{mode:?}: the proof of False must be refused: {:?}",
            record.refusals
        );
    }
    // The block's constructor and recursor are not registered over a resident
    // axiom (the loader's refusal comes first, load-time refusals lead), and
    // nothing of the module is admitted, as in Lean's replay, where
    // `forged_ind_false` meets `(kernel) unknown constant 'ind_ax_t.mk'`.
    let record = replay("ReplayForgedIndOverAx", ReplayMode::ImportsTrusted);
    assert_refused(&record, "ind_ax_t", "already declared");
    assert_refused(&record, "ind_ax_t.mk", "not resident");
    assert_refused(&record, "forged_ind_false", "ind_ax_t.mk");
    assert_eq!(record.admitted, 0, "{record:?}");
    let fresh = replay("ReplayForgedIndOverAx", ReplayMode::Fresh);
    assert_refused(
        &fresh,
        "ind_ax_t",
        "import ReplayForgedIndOverAx failed, environment already contains 'ind_ax_t'",
    );
    assert_eq!(
        fresh.first_refusal.as_ref().map(|r| r.constant.as_str()),
        Some("ind_ax_t"),
        "--fresh: the import's refusal comes first, as leanchecker's does: {fresh:?}"
    );
}

/// A duplicate is refused at Lean's import exactly when Lean imports its
/// module: with the imports trusted, the modules not replayed (the replayed
/// module's own duplicates are the replay's `already declared`, `declared`'s
/// to decide); under `--fresh`, every module, the replayed one included
/// (pinned `leanchecker --fresh ReplayForgedBoolDef`: `import
/// ReplayForgedBoolDef failed, environment already contains 'bool_ax_b' from
/// ReplayHonestBoolAx`). Built summaries, because no fixture can carry a
/// duplicate between two IMPORTS: Lean's own import refuses to build a module
/// over two imports that declare one name, so the generator cannot mint it.
#[test]
fn test_import_merge_refusals_name_the_duplicates_lean_imports() {
    let summary = |module: &str, duplicate: &str| {
        let mut summary = LoadSummary::empty();
        summary.module_name = Some(module.to_owned());
        summary.shadowed_declarations.push((
            Name::from_string(duplicate),
            "declared by module `A`".to_owned(),
        ));
        summary
    };
    let summaries = [
        summary("B", "from_an_import"),
        summary("M", "from_the_module"),
    ];
    let replayed = |label: &str| label == "M";
    let refused: Vec<String> =
        import_merge_refusals(ReplayMode::ImportsTrusted, &summaries, &replayed)
            .into_iter()
            .map(|r| r.constant)
            .collect();
    assert_eq!(refused, ["from_an_import"]);
    let fresh = import_merge_refusals(ReplayMode::Fresh, &summaries, &|_: &str| true);
    let refused: Vec<&str> = fresh.iter().map(|r| r.constant.as_str()).collect();
    assert_eq!(refused, ["from_an_import", "from_the_module"]);
    assert!(
        fresh[1]
            .reason
            .contains("import M failed, environment already contains 'from_the_module'"),
        "{}",
        fresh[1].reason
    );
}

/// The replay's load leaves to the replay what `leanchecker` refuses per
/// declaration, where the loader's own rules refuse the whole import
/// (`OleanImportPolicy::with_replay_refusals`): a self-referential
/// declaration, a module whose IMPORT holds one (`leanchecker ReplayCrossB`
/// exits 0), and a redefinition of an imported axiom are registered or
/// recorded, not an import error. The default policy still refuses each, so
/// `clean check` keeps its module-trust rules.
#[test]
fn test_replay_load_policy_records_what_the_default_load_refuses() {
    let search = search();
    let load = |module: &str, policy: OleanImportPolicy| {
        let mut env = Environment::for_lean_replay();
        env.set_kernel_theory(KernelTheory::Lean);
        let mut visited = hashbrown::HashSet::new();
        let loaded = load_module_with_deps_shared_with_policy(
            &mut env,
            module,
            &search,
            &mut visited,
            policy,
        );
        (env, loaded)
    };
    let default_policy = OleanImportPolicy::default().with_kernel_only();
    for (module, needle) in [
        ("ReplayForged", "depend on themselves"),
        ("ReplayForged3", "depend on themselves"),
        ("ReplayCrossA", "cross_forged"),
        ("ReplayCrossB", "cross_forged"),
        ("ReplayRedeclare", "Nat.pred"),
        ("ReplayForgedBoolDef", "bool_ax_b"),
        ("ReplayForgedIndOverAx", "ind_ax_t"),
    ] {
        let (_, refused) = load(module, default_policy);
        let error = refused.err().map(|e| e.to_string()).unwrap_or_default();
        assert!(
            error.contains(needle),
            "{module}: the default load: {error:?}"
        );
    }
    let (env, loaded) = load("ReplayCrossB", replay_load_policy());
    loaded.unwrap_or_else(|e| panic!("ReplayCrossB under the replay policy: {e}"));
    assert!(env.get_const(&Name::from_string("cross_forged")).is_some());
    let (_, loaded) = load("ReplayForgedBoolDef", replay_load_policy());
    let summaries = loaded.unwrap_or_else(|e| panic!("ReplayForgedBoolDef: {e}"));
    assert!(
        summaries.iter().any(|s| s
            .shadowed_declarations
            .iter()
            .any(|(name, _)| name.to_string() == "bool_ax_b")),
        "the redefinition is recorded for the replay to refuse"
    );
    // An inductive over an imported axiom is a duplicate like any other, not
    // a carrier stub for the loader to discharge (`is_axiom_carrier_stub`).
    let (env, loaded) = load("ReplayForgedIndOverAx", replay_load_policy());
    let summaries = loaded.unwrap_or_else(|e| panic!("ReplayForgedIndOverAx: {e}"));
    assert!(
        summaries.iter().any(|s| s
            .shadowed_declarations
            .iter()
            .any(|(name, _)| name.to_string() == "ind_ax_t")),
        "the inductive is recorded for the replay to refuse"
    );
    assert!(
        env.get_inductive(&Name::from_string("ind_ax_t")).is_none(),
        "the imported axiom stays resident"
    );
}

/// `load_module_with_deps_replaying_module` (the mathverse sharded worker's
/// load) leaves rules 1 and 3 to the replay for the named module ONLY: its
/// own self-dependent declarations register as stored and its redeclarations
/// are recorded, while an IMPORT holding a self-dependent declaration is still
/// refused, by name. It is not a kernel-only load, so it confines the
/// `.olean.private` stub upgrade by the replay policy alone: the imported
/// `axiom bool_ax_b` stays value-less rather than taking the module's `true`,
/// which would make `forged_bool_false : False` check. (Rule 2, which it keeps
/// for references INTO the module, is pinned in `artifact_ledger`'s tests: no
/// fixture carries an import that refers to a name only its importer declares.)
#[test]
fn test_load_replaying_module_relaxes_the_module_trust_rules_for_that_module_only() {
    let search = search();
    let load = |module: &str| {
        let mut env = Environment::for_lean_replay();
        env.set_kernel_theory(KernelTheory::Lean);
        let loaded = crate::load_module_with_deps_replaying_module(
            &mut env,
            module,
            &search,
            OleanImportPolicy::default(),
        );
        (env, loaded)
    };
    let (env, loaded) = load("ReplayForged3");
    loaded.unwrap_or_else(|e| panic!("ReplayForged3: {e}"));
    assert!(
        env.get_const(&Name::from_string("forged3_self")).is_some(),
        "the self-reference registers as stored, for the replay to refuse"
    );
    let (_, loaded) = load("ReplayRedeclare");
    let summaries = loaded.unwrap_or_else(|e| panic!("ReplayRedeclare: {e}"));
    assert!(
        summaries
            .iter()
            .any(|s| s.module_name.as_deref() == Some("ReplayRedeclare")
                && s.shadowed_declarations
                    .iter()
                    .any(|(name, _)| name.to_string() == "Nat.pred")),
        "the redeclaration is recorded against the module"
    );
    let (env, loaded) = load("ReplayForgedBoolDef");
    let summaries = loaded.unwrap_or_else(|e| panic!("ReplayForgedBoolDef: {e}"));
    assert!(
        summaries.iter().any(|s| s
            .shadowed_declarations
            .iter()
            .any(|(name, _)| name.to_string() == "bool_ax_b")),
        "the redefinition is recorded for the replay to refuse"
    );
    assert!(
        env.get_const(&Name::from_string("bool_ax_b"))
            .is_some_and(|c| c.value.is_none()),
        "the imported axiom stays value-less"
    );
    let (_, refused) = load("ReplayCrossB");
    let error = refused.err().map(|e| e.to_string()).unwrap_or_default();
    assert!(
        error.contains("depend on themselves") && error.contains("cross_forged"),
        "an import's self-dependent declaration refuses the import: {error:?}"
    );
}

/// A load that fails outright still names what it was about: here the module
/// itself, which no search path holds.
#[test]
fn test_load_error_refusals_name_the_declaration_or_the_module() {
    let cycle = ImportError::DefinitionalCycle {
        names: vec!["a".to_owned(), "b".to_owned()],
    };
    let named: Vec<String> = load_error_refusals("M", &cycle)
        .into_iter()
        .map(|r| r.constant)
        .collect();
    assert_eq!(named, ["a", "b"]);
    let missing = replay("ReplayNoSuchModule", ReplayMode::ImportsTrusted);
    assert_eq!(
        missing.first_refusal.as_ref().map(|r| r.constant.as_str()),
        Some("ReplayNoSuchModule"),
        "{missing:?}"
    );
}

/// Names the replay environment seeds (`Environment::for_lean_replay`)
/// redeclared by a module whose imports already hold them: `leanchecker`
/// refuses `axiom Quot.sound` over `Init.Core` (`already declared`) and
/// accepts it `--fresh` (the two axioms merge), and refuses `axiom Quot.ind`
/// over `Init.Prelude` in both modes.
#[test]
fn test_replay_module_seeded_quotient_names_redeclared_follow_lean() {
    let record = replay("ReplayForgedQuotRedecl", ReplayMode::ImportsTrusted);
    assert_refused(&record, "Quot.sound", "already declared");
    let fresh = replay("ReplayForgedQuotRedecl", ReplayMode::Fresh);
    assert!(
        fresh.ok,
        "--fresh merges the two axioms: {:?}",
        fresh.refusals
    );
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let record = replay("ReplayForgedQuotIndAxiom", mode);
        assert_refused(&record, "Quot.ind", "already declared");
    }
}

/// The toolchain's own `Init.Core` declares `Quot.sound`, which Clean's
/// replay environment seeds with its canonical quotient (Lean's `quotDecl`
/// does not): it is the module's declaration, replayed, never "already
/// declared". `leanchecker Init.Core` exits 0.
#[test]
fn test_replay_module_init_core_is_admitted_with_its_quot_sound() {
    let record = replay("Init.Core", ReplayMode::ImportsTrusted);
    assert!(record.ok, "{:?}", record.refusals);
    assert!(record.constants_checked > 1000, "{record:?}");
    assert_eq!(record.admitted, record.constants_checked, "{record:?}");
}

/// `Init.Data.String.Search` restates `Init.Data.String.Lemmas.Basic`'s
/// `String.pos.congr_simp`: an axiom in its exported part, the theorem in its
/// private part. Lean's replay reads the private part and skips a theorem
/// restating an identical resident theorem; `leanchecker` exits 0.
#[test]
fn test_replay_module_restated_theorem_follows_the_most_private_part() {
    let record = replay("Init.Data.String.Search", ReplayMode::ImportsTrusted);
    assert!(record.ok, "{:?}", record.refusals);
    assert!(record.restated >= 1, "{record:?}");
}

#[test]
fn test_replay_module_missing_module_is_a_load_error() {
    let record = replay("ReplayNoSuchModule", ReplayMode::ImportsTrusted);
    assert!(!record.ok && record.load_error.is_some(), "{record:?}");
}

fn touch(root: &std::path::Path, rel: &str) {
    let path = root.join(rel);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).unwrap_or_else(|e| panic!("{e}"));
    }
    std::fs::write(&path, b"").unwrap_or_else(|e| panic!("{e}"));
}

/// `leanchecker A` replays every module `A` is a component prefix of;
/// `--fresh A` exactly `A`; server/private parts and other extensions are not
/// modules, and `AB` is not under `A`.
#[test]
fn test_select_modules_prefix_is_component_wise_and_exact_under_fresh() {
    let dir = tempfile::tempdir().unwrap_or_else(|e| panic!("{e}"));
    let root = dir.path();
    for rel in [
        "A.olean",
        "A/B.olean",
        "A/B.olean.private",
        "A/B.olean.server",
        "A/B/C.olean",
        "A/B/C.ilean",
        "AB.olean",
    ] {
        touch(root, rel);
    }
    let search = vec![root.to_path_buf()];
    let set =
        |items: &[&str]| -> BTreeSet<String> { items.iter().map(|s| (*s).to_owned()).collect() };
    let select = |targets: &[&str], exact: bool, fresh: bool| {
        let targets: Vec<String> = targets.iter().map(|s| (*s).to_owned()).collect();
        select_modules(&targets, &search, exact, fresh)
    };
    assert_eq!(
        select(&["A"], false, false).unwrap_or_default(),
        set(&["A", "A.B", "A.B.C"])
    );
    assert_eq!(select(&["A"], true, false).unwrap_or_default(), set(&["A"]));
    assert_eq!(select(&["A"], false, true).unwrap_or_default(), set(&["A"]));
    assert_eq!(
        select(&["A.B"], false, false).unwrap_or_default(),
        set(&["A.B", "A.B.C"])
    );
    assert_eq!(
        select(&["A.B.C", "A.B"], false, false).unwrap_or_default(),
        set(&["A.B", "A.B.C"])
    );
    assert!(matches!(
        select(&["Nope"], false, false),
        Err(ReplayTargetError::NotFound { .. })
    ));
    assert!(matches!(
        select(&["A..B"], false, false),
        Err(ReplayTargetError::BadModuleName(_))
    ));
    assert!(matches!(
        select(&["A", "AB"], false, true),
        Err(ReplayTargetError::FreshNeedsOneModule(_))
    ));
}

#[test]
fn test_replay_search_path_orders_explicit_then_lean_path_then_toolchain() {
    let lean_path =
        std::env::join_paths(["/lp/one", "/lp/two", "/explicit"]).unwrap_or_else(|e| panic!("{e}"));
    let paths = replay_search_path(
        &[PathBuf::from("/explicit")],
        Some(lean_path.as_os_str()),
        Some(PathBuf::from("/toolchain/lib/lean")),
    )
    .unwrap_or_else(|e| panic!("{e}"));
    let expected: Vec<PathBuf> = ["/explicit", "/lp/one", "/lp/two", "/toolchain/lib/lean"]
        .iter()
        .map(PathBuf::from)
        .collect();
    assert_eq!(paths, expected);
    assert!(matches!(
        replay_search_path(&[], None, None),
        Err(ReplayTargetError::NoToolchain(_))
    ));
}

/// The name table the accounting reads is the module's own: with nothing
/// covered, every stored declaration comes back, so a declaration the loader
/// dropped silently would be refused by name; a missing module is an error.
#[test]
fn test_unaccounted_declarations_reads_the_stored_name_table() {
    let search = search();
    let mut names = accounting::unaccounted_declarations("ReplayHonest", &search, &|_| false)
        .unwrap_or_else(|e| panic!("{e}"));
    names.sort();
    assert_eq!(
        names,
        ["honest_chain", "honest_one", "honest_one_eq", "honest_t"]
    );
    let none = accounting::unaccounted_declarations("ReplayHonest", &search, &|_| true)
        .unwrap_or_else(|e| panic!("{e}"));
    assert!(none.is_empty(), "{none:?}");
    assert!(
        accounting::unaccounted_declarations("ReplayNoSuchModule", &search, &|_| true).is_err()
    );
}

/// The kernel-only load registers exactly the declarations a full load does,
/// with the same types, values and kinds; only the elaborator's tables stay
/// empty. The verdicts of every other test here are on this load. Its one
/// deliberate difference, never filling ANOTHER module's value-less constant
/// except by a theorem over an axiom (`OleanImportPolicy::with_kernel_only`),
/// does not arise in this closure, whose every value-less stub is filled by
/// its own module's private part.
#[test]
fn test_kernel_only_load_registers_the_same_declarations() {
    use clean_kernel::expr::Expr;
    let search = search();
    let load = |policy: OleanImportPolicy| {
        let mut env = Environment::for_lean_replay();
        let mut visited = hashbrown::HashSet::new();
        load_module_with_deps_shared_with_policy(
            &mut env,
            "ReplayHonestInd",
            &search,
            &mut visited,
            policy,
        )
        .unwrap_or_else(|e| panic!("{e}"));
        env
    };
    type Row = (Expr, Option<Expr>, String);
    let snapshot = |env: &Environment| -> (BTreeMap<String, Row>, BTreeSet<String>) {
        let constants = env
            .constants()
            .map(|c| {
                let row = (c.type_.clone(), c.value.clone(), format!("{:?}", c.kind));
                (c.name.to_string(), row)
            })
            .collect();
        let families = env
            .inductives()
            .map(|i| i.name.to_string())
            .chain(env.constructors().map(|c| c.name.to_string()))
            .chain(env.recursors().map(|r| r.name.to_string()))
            .collect();
        (constants, families)
    };
    let full = load(OleanImportPolicy::default());
    let kernel = load(OleanImportPolicy::default().with_kernel_only());
    let (full_constants, full_families) = snapshot(&full);
    let (kernel_constants, kernel_families) = snapshot(&kernel);
    assert!(full_constants.len() > 1000, "{}", full_constants.len());
    assert_eq!(full_families, kernel_families);
    assert!(
        full_constants == kernel_constants,
        "the kernel-only load changed a declaration"
    );
    assert!(full.get_simp_lemmas().next().is_some());
    assert!(kernel.get_simp_lemmas().next().is_none());
}

// The large-elimination gate's two level rules (result level up to whnf;
// only a provably nonzero level is exempt), in their own file so this one
// stays under the 1000-line paragon limit.
mod level_gate;
// Universe-level equalities in Lean's kernel theory (DECISIONS R150).
mod level_equiv;
// The `is_prop`-requires-a-sort rule; release-only (its fixture's closure).
#[cfg(not(debug_assertions))]
mod is_prop_sort;
// Hole R112: a block found through a forged `all`; a stored `isRec` the
// replay did not compare.
mod block_cover;
// Hole B1 (R113): a declaration placed where `lean` never reads it.
mod misplaced;
// R131: value-free stubs a later part completes.
mod stubs;
// Nested blocks through dependent containers, the `Nat.pow` exponent cap and
// Lean's level equivalence (kernel fidelity, 2026-10-23).
mod kernel_fidelity;
