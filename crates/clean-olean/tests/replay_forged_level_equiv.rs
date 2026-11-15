// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-level equality in Lean's kernel theory across the `.olean` lanes
//! (fixture family `replay_forged`: `ReplayForgedLevelSubsumption`,
//! `ReplayHonestLevelEquiv`, `ReplayLevelSharing`, the cross-module pair, and
//! `ReplayForgedLevelReach` / `ReplayHonestLevelReach` /
//! `ReplayHonestLevelProj`; pinned-Lean per-constant verdicts in its README;
//! DECISIONS R150).
//!
//! The loader decodes every stored `max`/`imax` node verbatim, and the
//! `verify_batch_full` lanes run `KernelTheory::Lean` (from
//! `Environment::for_lean_replay`), whose level comparison, substitution
//! (constant types, projections, δ, ι) and Π sort follow pinned Lean's
//! `level.cpp`, and whose inductive checks follow `inductive.cpp` (stored
//! blocks are re-admitted in Lean's theory). So the three lanes refuse the
//! nine equalities pinned Lean refuses (each true at every assignment:
//! Clean's own normaliser admitted t1-t3, its collapsing decoder t4/t9, its
//! collapsing substitution t5, the projection's and δ's, and its collapsing
//! `imax` t10) and the three inductive blocks it refuses (a mutual block's
//! universes, a field bound, a skipped bound), and admit the honest twins in
//! full. `recheck_closed` and `ImportedConeGate` replay into Clean's
//! own `Extended` environment and keep its level algebra, pinned below as a
//! known gap.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{Environment, KernelTheory, ProofValueElision};
use clean_kernel::name::Name;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::recheck_closed::{recheck_closed, ClosedRecheckOptions};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::verify_batch_full::{
    typecheck_constants_full, typecheck_constants_full_streaming,
};
use clean_olean::verify_parallel::typecheck_constants_full_parallel;
use clean_olean::{
    default_search_paths, load_module_with_deps_shared_with_policy, parse_module_file,
    ImportedConeGate, OleanImportPolicy,
};

const FAMILY: &str = "replay_forged";

type Outcome = (usize, usize, BTreeMap<String, String>);

/// The fixture modules a test loads, whose every constant must reach the
/// lanes (the loader may skip `Init`'s compiler artifacts, never these).
const FIXTURE_MODULES: [&str; 9] = [
    "ReplayForgedLevelSubsumption",
    "ReplayHonestLevelEquiv",
    "ReplayLevelSharing",
    "ReplayHonestLevelImport",
    "ReplayForgedLevelImport",
    "ReplayHonestLevelImportUse",
    "ReplayForgedLevelReach",
    "ReplayHonestLevelReach",
    "ReplayHonestLevelProj",
];

/// The seven equalities of `ReplayForgedLevelSubsumption`.
const FORGED: [&str; 7] = [
    "fls_join",
    "fls_join_wf",
    "fls_imax_reflatten",
    "fls_decode_max",
    "fls_decode_imax",
    "fls_subst",
    "fls_infer_pi",
];

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| (*s).to_owned()).collect()
}

/// Every name of `forged` the lane admitted, in order, so a failure names
/// exactly the forgeries that got through.
fn admitted_forged(outcome: &Outcome, forged: &BTreeSet<String>) -> Vec<String> {
    forged
        .iter()
        .filter(|name| !outcome.2.contains_key(*name))
        .cloned()
        .collect()
}

/// Every name of `module` the lane refused, in order.
fn refused_names(outcome: &Outcome) -> Vec<String> {
    outcome.2.keys().cloned().collect()
}

/// Fail when `lane` admitted any of `admitted`, naming each on its own line
/// first, so a demonstration arm can pin exactly which forgery got through.
fn assert_none_admitted(lane: &str, admitted: &[String]) {
    for name in admitted {
        eprintln!("{lane} admitted forged `{name}`");
    }
    assert!(admitted.is_empty(), "{lane} admitted forged {admitted:?}");
}

/// Fail when `lane` refused any of the honest `refused`, naming each on its
/// own line first.
fn assert_none_refused(lane: &str, refused: &[String], why: &BTreeMap<String, String>) {
    for name in refused {
        eprintln!("{lane} refused honest `{name}`");
    }
    assert!(
        refused.is_empty(),
        "{lane} refused honest {refused:?}: {why:?}"
    );
}

/// Lean's replay environment plus `module`'s closure through the trusted
/// `.olean` path; the loader must skip no fixture constant.
fn load(module: &str) -> Environment {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    let fixture: BTreeSet<String> = FIXTURE_MODULES
        .iter()
        .flat_map(|m| module_constants(m))
        .collect();
    let skipped: Vec<_> = load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .unwrap_or_else(|e| panic!("load {module}: {e}"))
    .into_iter()
    .flat_map(|summary| summary.skipped_constants)
    .filter(|s| fixture.contains(&s.name))
    .map(|s| (s.name, s.reason))
    .collect();
    assert!(
        skipped.is_empty(),
        "{module}: the loader skipped fixture constants {skipped:?}"
    );
    env.regenerate_missing_no_confusion();
    env
}

fn module_constants(module: &str) -> BTreeSet<String> {
    let path = compiled_fixture_dir(FAMILY).join(format!("{module}.olean"));
    parse_module_file(&path)
        .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
        .const_names
        .into_iter()
        .collect()
}

/// The eager, parallel and streaming lanes' verdicts over `targets`.
fn lanes(env: Environment, targets: &BTreeSet<String>) -> Vec<(&'static str, Outcome)> {
    let eager = typecheck_constants_full(&env, targets, DEFAULT_HEARTBEAT_LIMIT);
    let parallel = typecheck_constants_full_parallel(&env, targets, 4, DEFAULT_HEARTBEAT_LIMIT);
    let mut env = env;
    let (pass, fail, errors, _stats) = typecheck_constants_full_streaming(
        &mut env,
        targets,
        DEFAULT_HEARTBEAT_LIMIT,
        ProofValueElision::OpaqueAndTheorem,
        Some(1),
    );
    vec![
        ("eager", eager),
        ("parallel", parallel),
        ("streaming", (pass, fail, errors)),
    ]
}

#[test]
fn test_forged_level_equalities_are_refused_by_every_lane() {
    let forged = names(&FORGED);
    let all = module_constants("ReplayForgedLevelSubsumption");
    assert!(forged.is_subset(&all), "{all:?}");
    for (lane, outcome) in lanes(load("ReplayForgedLevelSubsumption"), &all) {
        assert_none_admitted(lane, &admitted_forged(&outcome, &forged));
        let refused: BTreeSet<String> = outcome.2.keys().cloned().collect();
        assert_eq!(refused, forged, "{lane}: {:?}", outcome.2);
        assert_eq!(
            (outcome.0, outcome.1),
            (all.len() - forged.len(), forged.len()),
            "{lane}: {:?}",
            outcome.2
        );
    }
}

#[test]
fn test_honest_level_equalities_are_admitted_by_every_lane() {
    let honest = module_constants("ReplayHonestLevelEquiv");
    assert_eq!(honest.len(), 9, "{honest:?}");
    for (lane, outcome) in lanes(load("ReplayHonestLevelEquiv"), &honest) {
        assert_eq!(
            (outcome.0, outcome.1),
            (honest.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
}

/// Pinned Lean admits `ls_same` and refuses `ls_sorted` through `.olean`
/// object sharing; every lane refuses both, naming the sharing dependence.
#[test]
fn test_sharing_dependent_instantiation_is_refused_by_name_in_every_lane() {
    let all = module_constants("ReplayLevelSharing");
    for (lane, outcome) in lanes(load("ReplayLevelSharing"), &all) {
        for name in ["ls_same", "ls_sorted"] {
            let why = outcome
                .2
                .get(name)
                .unwrap_or_else(|| panic!("{lane}: `{name}` must be refused: {:?}", outcome.2));
            assert!(
                why.contains("LevelSharingDependent") || why.contains("object sharing"),
                "{lane}: `{name}` refused for another reason: {why}"
            );
        }
        assert!(
            !outcome.2.contains_key("ls_cS"),
            "{lane}: the axiom is admitted: {:?}",
            outcome.2
        );
    }
}

/// t4 and t9 across a module boundary (`ReplayForgedLevelImport` over the
/// honest `ReplayHonestLevelImport`): the stored levels reach the lanes only
/// through the import's decode.
#[test]
fn test_cross_module_level_forgeries_are_refused_by_every_lane() {
    let forged = module_constants("ReplayForgedLevelImport");
    assert_eq!(forged.len(), 2, "{forged:?}");
    for (lane, outcome) in lanes(load("ReplayForgedLevelImport"), &forged) {
        assert_eq!((outcome.0, outcome.1), (0, 2), "{lane}: {:?}", outcome.2);
        for name in ["fli_t4", "fli_t9"] {
            assert!(
                outcome
                    .2
                    .get(name)
                    .is_some_and(|why| why.contains("TypeMismatch")),
                "{lane}: `{name}` must be refused as a type mismatch: {:?}",
                outcome.2
            );
        }
    }
    let honest = module_constants("ReplayHonestLevelImportUse");
    for (lane, outcome) in lanes(load("ReplayHonestLevelImportUse"), &honest) {
        assert_eq!((outcome.0, outcome.1), (2, 0), "{lane}: {:?}", outcome.2);
    }
}

/// The forged blocks of `ReplayForgedLevelReach`, each minted from a twin
/// pinned Lean admits with the inductive's stored sort overwritten:
/// `flr_MA`/`flr_MB` (one mutual block at levels Lean's `is_equivalent`
/// does not equate), `flr_Fb` (a field bound Lean's `is_geq` does not prove)
/// and `flr_Z` (`Sort (max 0 0)`, not structurally `0`, over a `Nat` field).
const REACH_FORGED_BLOCKS: [&str; 4] = ["flr_MA", "flr_MB", "flr_Fb", "flr_Z"];

/// Whether `name` is one of `ReplayForgedLevelReach`'s forgeries: `fls_proj`,
/// `fls_delta`, or a member of a forged block.
fn is_reach_forgery(name: &str) -> bool {
    name.starts_with("fls_")
        || REACH_FORGED_BLOCKS
            .iter()
            .any(|block| name == *block || name.starts_with(&format!("{block}.")))
}

/// Every lane refuses `forged` (with `needle` in the reason when given) and
/// no honest constant of `ReplayForgedLevelReach` (`flr_S`, `flr_D`,
/// `flr_Av`).
fn assert_forged_reach_refused(forged: &[&str], needle: Option<&str>) {
    let all = module_constants("ReplayForgedLevelReach");
    assert!(forged.iter().all(|f| all.contains(*f)), "{all:?}");
    for (lane, outcome) in lanes(load("ReplayForgedLevelReach"), &all) {
        assert_none_admitted(lane, &admitted_forged(&outcome, &names(forged)));
        if let Some(needle) = needle {
            for name in forged {
                let why = &outcome.2[*name];
                assert!(why.contains(needle), "{lane}: `{name}`: {why}");
            }
        }
        let honest_refused: Vec<String> = refused_names(&outcome)
            .into_iter()
            .filter(|n| !is_reach_forgery(n))
            .collect();
        assert_none_refused(lane, &honest_refused, &outcome.2);
    }
}

/// Every constant of `module` is admitted by every lane.
fn assert_honest_module_admitted(module: &str) {
    let honest = module_constants(module);
    for (lane, outcome) in lanes(load(module), &honest) {
        assert_none_refused(lane, &refused_names(&outcome), &outcome.2);
        assert_eq!(
            (outcome.0, outcome.1),
            (honest.len(), 0),
            "{lane}: {module}"
        );
    }
}

/// `type_checker.cpp:241`: `infer_proj` instantiates the constructor's type
/// with `instantiate_type_lparams`. Pinned Lean refuses `fls_proj` and admits
/// `hle_proj` (the same projection at `Sort (max (max u v) (imax u v))`) and
/// the elaborated `rhp_c5`, whose `delta` proof keeps a raw `s.1`.
#[test]
fn test_projection_levels_follow_pinned_lean_in_every_lane() {
    assert_forged_reach_refused(&["fls_proj"], Some("TypeMismatch"));
    assert_honest_module_admitted("ReplayHonestLevelProj");
    assert_honest_module_admitted("ReplayHonestLevelReach");
}

/// `unfold_definition_core` instantiates the value with
/// `instantiate_value_lparams`. Pinned Lean refuses `fls_delta` and admits
/// `hle_delta`.
#[test]
fn test_delta_levels_follow_pinned_lean_in_every_lane() {
    assert_forged_reach_refused(&["fls_delta"], Some("TypeMismatch"));
    assert_honest_module_admitted("ReplayHonestLevelReach");
}

/// `inductive_reduce_rec` instantiates the rule's right-hand side with
/// `instantiate_lparams`: `hle_iota`'s ι-reduct keeps the binder
/// `Sort (max (max u v) (imax u v))`, the only spelling that is well typed
/// there, so a collapsing instantiation refuses it.
#[test]
fn test_iota_levels_follow_pinned_lean_in_every_lane() {
    assert_honest_module_admitted("ReplayHonestLevelReach");
}

/// `inductive.cpp` @ v4.30.0-rc2 on three blocks pinned Lean refuses: a
/// mutual block whose levels are not `is_equivalent` (:250), a field whose
/// sort `is_geq` does not bound (:439), and a `Sort (max 0 0)` whose bound is
/// checked because the level is not STRUCTURALLY `0`. Each lane rebuilds a
/// stored block in a scratch copy (`lean_replay_inductive_block`), in Lean's
/// theory even when the environment is `Extended`. The honest twins, and the
/// two recursors pinned Lean builds from a structural `is_zero` (`hlr_P0.rec`
/// eliminates only into `Prop`, `hlr_Q0.rec` has `k = false`), are admitted.
#[test]
fn test_inductive_levels_follow_pinned_lean_in_every_lane() {
    assert_forged_reach_refused(&REACH_FORGED_BLOCKS, None);
    assert_honest_module_admitted("ReplayHonestLevelReach");
}

/// `recheck_closed` replays a cone into Clean's own `Environment::default()`,
/// and `ImportedConeGate` into the consumer's base (an `Extended` prelude in
/// every production caller): both run `KernelTheory::Extended`, which keeps
/// Clean's level algebra (DECISIONS R150 scopes the Lean profile to the lanes
/// that start from `Environment::for_lean_replay`). KNOWN GAP, pinned: both
/// admit the equalities pinned Lean refuses, each true at every assignment.
/// This fails the day either lane runs Lean's level algebra.
#[test]
fn test_closed_recheck_and_import_gate_keep_clean_level_algebra() {
    let env = load("ReplayForgedLevelSubsumption");
    let targets: BTreeSet<Name> = FORGED.iter().map(|s| Name::from_string(s)).collect();
    let run = recheck_closed(&env, &targets, &ClosedRecheckOptions::default());
    assert_eq!(run.replayed.kernel_theory(), KernelTheory::Extended);
    let admitted: BTreeSet<String> = FORGED
        .iter()
        .filter(|f| run.admitted.contains(&Name::from_string(f)))
        .map(|f| (*f).to_owned())
        .collect();
    assert_eq!(admitted, names(&FORGED), "{:?}", run.report.refusals);
    assert!(run.report.passed(), "{:?}", run.report.refusals);

    let mut gate = ImportedConeGate::new(&Environment::default());
    for forged in FORGED {
        let roots: BTreeSet<Name> = [Name::from_string(forged)].into_iter().collect();
        let verdict = gate.check(&env, &roots);
        assert!(
            verdict.refusals.is_empty(),
            "ImportedConeGate refused `{forged}`: {:?}",
            verdict.refusals
        );
        // `fls_subst`/`fls_infer_pi` rest on the module's own axioms, which the
        // gate reports (not a kernel refusal); the other five pass outright.
        let rests_on_axioms = matches!(forged, "fls_subst" | "fls_infer_pi");
        assert_eq!(
            verdict.passed(false),
            !rests_on_axioms,
            "`{forged}`: {verdict:?}"
        );
    }
}
