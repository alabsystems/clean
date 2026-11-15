// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `verify_batch_full` re-check lanes against `.olean`s Lean's kernel
//! never admitted (fixture family `replay_forged`, minted by the pinned Lean
//! with the kernel check skipped; see its README for `leanchecker`'s verdicts).
//!
//! Every lane — eager `typecheck_constants_full`, the chunked streaming form
//! with proof-value elision, and `typecheck_constants_full_parallel` — must
//! refuse each forgery with a named error and verify each honest declaration.
//! Before 2026-09-24 all three stamped `forged3_self : False := forged3_self`
//! (a target resident while its own value was checked), `isOSX = true :=
//! rfl` (a native reducer for Lean's `@[extern] opaque` platform query) and
//! `False := unsafeCast True.intro` (a safe declaration using an unsafe one);
//! and, in round 2, `False` through a recursor stored with no minor premises
//! or a constructor stored with type `False`, and five `String` equations Lean
//! refuses, through reducers whose result is not Lean's.
//!
//! The environment is built as the production callers build it: Lean's replay
//! environment (`Environment::for_lean_replay`) plus the module's `.olean`
//! closure. The lanes assume whatever the caller supplies outside the checked
//! set, so a Clean-prelude base would serve `sorry`; the callers no longer
//! supply one.
//!
//! TWO LAYERS, EACH ASSERTED BY NAME. Since module-trust round 29 the `.olean`
//! import itself refuses an artifact whose declarations depend on themselves
//! (`ImportError::DefinitionalCycle`) and a name two artifacts declare
//! differently (`ImportError::ConflictingDeclaration`), so those forgeries no
//! longer reach a lane through the import. The lanes' own refusals of them
//! (the replay admission gate, the in-run "already declared" refusal) are still
//! the lanes' contract — `verify_batch_full` checks whatever environment its
//! caller supplies — so each such test asserts the import's refusal AND then
//! hands the lanes the environment the forgery would have produced
//! ([`forged_resident`], [`InRun::seed`]) and asserts the lanes' refusal. A test
//! that returned early on the import's refusal would stay green with the lane
//! defence deleted (measured 2026-09-28: three of this battery's five mutation
//! arms went GREEN that way).

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{
    ConstantInfo, ConstantKind, Environment, ProofValueElision, Reducibility, TrustedEnvExt,
};
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::verify_batch::{
    collect_new_env_names, verify_one_module_with_mode_in_run, ModuleResult, ValidationMode,
};
use clean_olean::verify_batch_full::{
    typecheck_constants_full, typecheck_constants_full_streaming,
};
use clean_olean::verify_parallel::typecheck_constants_full_parallel;
use clean_olean::{
    convert_parsed_constant_to_const_info, default_search_paths,
    load_module_with_deps_shared_with_policy, parse_module_file, OleanImportPolicy,
};

const FAMILY: &str = "replay_forged";

/// The module's closure loaded the way the lanes load it: Lean's replay
/// environment, then the fixture module and its imports through the trusted
/// `.olean` path.
fn load(module: &str) -> Environment {
    try_load(module).unwrap_or_else(|e| panic!("load {module}: {e}"))
}

/// [`load`], returning the import's refusal instead of panicking. The lanes
/// load under a re-check lane's policy: a refused completion of an artifact's
/// own stub refuses the import (R131).
fn try_load(module: &str) -> Result<Environment, String> {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &search,
        &mut visited,
        OleanImportPolicy::default().refusing_refused_completions(),
    )
    .map_err(|e| e.to_string())?;
    env.regenerate_missing_no_confusion();
    Ok(env)
}

/// LAYER 1. The import refuses `module` as an inconsistent artifact whose
/// declarations depend on themselves (module-trust round 29,
/// `ImportError::DefinitionalCycle`), naming a member of the cycle.
fn expect_import_refuses_cycle(module: &str, cycle: &[&str]) {
    let error = match try_load(module) {
        Ok(_) => panic!("{module}: the import must refuse a self-dependent artifact"),
        Err(error) => error,
    };
    assert!(error.contains("depend on themselves"), "{module}: {error}");
    assert!(
        cycle.iter().any(|name| error.contains(name)),
        "{module}: the refusal must name the cycle {cycle:?}: {error}"
    );
}

/// LAYER 2's input for a module the import refuses: `module`'s imports through
/// the trusted `.olean` path, then `module`'s OWN declarations — decoded from
/// the same forged `.olean` by the production converter — made resident
/// structurally, exactly as the loader registers them had it not refused the
/// artifact. This is the environment the lanes' contract covers ("the
/// environment a caller supplies holds every target already",
/// `verify_batch_replay`), and the one they faced before the import refused
/// these forgeries.
fn forged_resident(module: &str) -> Environment {
    let path = compiled_fixture_dir(FAMILY).join(format!("{module}.olean"));
    let parsed =
        parse_module_file(&path).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    for import in &parsed.imports {
        load_module_with_deps_shared_with_policy(
            &mut env,
            &import.module_name,
            &search,
            &mut visited,
            OleanImportPolicy::default(),
        )
        .unwrap_or_else(|e| panic!("load {} (imported by {module}): {e}", import.module_name));
    }
    let own: Vec<ConstantInfo> = parsed
        .constants
        .iter()
        .map(|c| {
            convert_parsed_constant_to_const_info(c)
                .unwrap_or_else(|e| panic!("{module}: convert {}: {e}", c.name))
                .unwrap_or_else(|| panic!("{module}: {} is not a plain constant", c.name))
        })
        .collect();
    assert!(!own.is_empty(), "{module} declares nothing");
    // SOUNDNESS: adversarial lane-input fixture only. Structural insertion is
    // not admission: it makes the forged module's declarations resident so the
    // re-check lanes, whose refusals are under test, see them; the
    // environment never escapes this test.
    let rejected = env.extend_constants_structural(own.into_iter());
    assert!(rejected.is_empty(), "{module}: {rejected:?}");
    env.regenerate_missing_no_confusion();
    env
}

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| (*s).to_owned()).collect()
}

type Outcome = (usize, usize, BTreeMap<String, String>);

/// The three lanes' verdicts over `targets` of `module`.
fn lanes(module: &str, targets: &BTreeSet<String>) -> Vec<(&'static str, Outcome)> {
    lanes_over(load(module), targets)
}

/// The three lanes' verdicts over `targets` of the supplied environment.
fn lanes_over(env: Environment, targets: &BTreeSet<String>) -> Vec<(&'static str, Outcome)> {
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

fn expect_refused(lane: &str, outcome: &Outcome, name: &str, needle: &str) {
    let message = outcome
        .2
        .get(name)
        .unwrap_or_else(|| panic!("{lane}: `{name}` must be refused; errors {:?}", outcome.2));
    assert!(
        message.contains(needle),
        "{lane}: `{name}` refused, but without `{needle}`: {message}"
    );
}

/// Layer 1: the import refuses the self-dependent artifact. Layer 2: with its
/// declarations resident anyway, every lane refuses the self-reference and the
/// cycle — the replay admission gate (`Lean.Environment.replay`: a pending
/// constant is not in the environment).
#[test]
fn test_verify_batch_full_lanes_self_reference_and_cycle_are_refused() {
    let targets = names(&["forged3_self", "forged3_cycA", "forged3_cycB"]);
    expect_import_refuses_cycle(
        "ReplayForged3",
        &["forged3_self", "forged3_cycA", "forged3_cycB"],
    );
    for (lane, outcome) in lanes_over(forged_resident("ReplayForged3"), &targets) {
        assert_eq!((outcome.0, outcome.1), (0, 3), "{lane}: {:?}", outcome.2);
        expect_refused(lane, &outcome, "forged3_self", "refers to itself");
        expect_refused(lane, &outcome, "forged3_cycB", "dependency cycle");
        expect_refused(lane, &outcome, "forged3_cycA", "depends on `forged3_cycB`");
    }
}

#[test]
fn test_verify_batch_full_lanes_forged_module_is_refused_with_its_control() {
    let targets = names(&["forged_self", "forged_cycA", "forged_cycB", "forged_bad"]);
    expect_import_refuses_cycle(
        "ReplayForged",
        &["forged_self", "forged_cycA", "forged_cycB"],
    );
    for (lane, outcome) in lanes_over(forged_resident("ReplayForged"), &targets) {
        assert_eq!((outcome.0, outcome.1), (0, 4), "{lane}: {:?}", outcome.2);
        expect_refused(lane, &outcome, "forged_self", "refers to itself");
        expect_refused(lane, &outcome, "forged_cycB", "dependency cycle");
        expect_refused(lane, &outcome, "forged_bad", "TypeMismatch");
    }
}

/// Lean's kernel cannot reduce the `@[extern] opaque` platform queries, so none
/// of the four `rfl` statements is provable in Lean's theory — whichever of
/// them happens to be true on the build host.
#[test]
fn test_verify_batch_full_lanes_platform_booleans_are_stuck_as_in_lean() {
    let targets = names(&[
        "forged4_osx",
        "forged4_not_osx",
        "forged4_not_windows",
        "forged4_not_emscripten",
    ]);
    for (lane, outcome) in lanes("ReplayForged4", &targets) {
        assert_eq!((outcome.0, outcome.1), (0, 4), "{lane}: {:?}", outcome.2);
        for name in &targets {
            expect_refused(lane, &outcome, name, "check_type: TypeMismatch");
        }
    }
}

#[test]
fn test_verify_batch_full_lanes_safe_theorem_using_unsafe_is_refused() {
    let targets = names(&["forged5_unsafe"]);
    for (lane, outcome) in lanes("ReplayForged5", &targets) {
        assert_eq!((outcome.0, outcome.1), (0, 1), "{lane}: {:?}", outcome.2);
        expect_refused(lane, &outcome, "forged5_unsafe", "UnsafeDeclaration");
    }
}

/// The honest controls, including a module-mate chain and a definition the
/// next theorem must δ-unfold: replay order must still admit them.
#[test]
fn test_verify_batch_full_lanes_honest_modules_verify() {
    let honest = names(&["honest_t", "honest_chain", "honest_one", "honest_one_eq"]);
    for (lane, outcome) in lanes("ReplayHonest", &honest) {
        assert_eq!((outcome.0, outcome.1), (4, 0), "{lane}: {:?}", outcome.2);
    }
    let honest4 = names(&["honest4_osx_refl"]);
    for (lane, outcome) in lanes("ReplayHonest4", &honest4) {
        assert_eq!((outcome.0, outcome.1), (1, 0), "{lane}: {:?}", outcome.2);
    }
}

/// `verify_batch_full` has no "skipped" bucket, so a requested unsafe target is
/// a named refusal (Lean's replay never admits it) and its safe neighbour still
/// verifies.
#[test]
fn test_verify_batch_full_lanes_unsafe_target_is_refused_safe_neighbour_verifies() {
    let targets = names(&["honest_unsafe_val", "honest_safe"]);
    for (lane, outcome) in lanes("ReplayHonestUnsafe", &targets) {
        assert_eq!((outcome.0, outcome.1), (1, 1), "{lane}: {:?}", outcome.2);
        expect_refused(lane, &outcome, "honest_unsafe_val", "is unsafe");
    }
}

/// `clean olean verify-batch`'s in-run loop: module after module in ONE
/// cumulative environment, from the runner's own starting environment and
/// Init preload.
struct InRun {
    env: Environment,
    search: Vec<std::path::PathBuf>,
    known: std::collections::HashSet<String>,
    visited: hashbrown::HashSet<String>,
    not_admitted: BTreeSet<String>,
}

impl InRun {
    fn new() -> Self {
        let env = Environment::default();
        let mut search = vec![compiled_fixture_dir(FAMILY)];
        search.extend(default_search_paths());
        let mut known = std::collections::HashSet::new();
        collect_new_env_names(&env, &mut known);
        let mut run = Self {
            env,
            search,
            known,
            visited: hashbrown::HashSet::new(),
            not_admitted: BTreeSet::new(),
        };
        assert!(run.run("Init.Prelude", true).load_ok);
        run
    }

    fn run(&mut self, module: &str, load_only: bool) -> ModuleResult {
        verify_one_module_with_mode_in_run(
            &mut self.env,
            module,
            module,
            &self.search,
            &mut self.known,
            load_only,
            ValidationMode::Full,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::None,
            &mut self.visited,
            &mut self.not_admitted,
        )
    }

    /// Make `constant` resident before the next module loads, owned by no
    /// artifact: a kernel seed, or anything else resident that the artifact
    /// ledger does not own. The loader keeps it and records a module's own
    /// declaration of that name as shadowed (`import/load_shadowing.rs`),
    /// which is what the run's "already declared" refusal consumes.
    fn seed(&mut self, constant: ConstantInfo) {
        // SOUNDNESS: adversarial lane-input fixture only. Structural insertion
        // is not admission; the environment never escapes this test.
        let rejected = self
            .env
            .extend_constants_structural(std::iter::once(constant));
        assert!(rejected.is_empty(), "{rejected:?}");
        // The seed is the run's starting state, not a module's addition.
        collect_new_env_names(&self.env, &mut self.known);
    }
}

/// `clean olean verify-batch --full-validation` loads module after module into
/// ONE environment. Layer 1: the import refuses `ReplayCrossA` (`cross_forged`
/// depends on itself). Layer 2: the refused load leaves its declarations
/// resident, and Lean's replay of the whole run never added them, so
/// `ReplayCrossB` — which Lean's kernel checked with `ReplayCrossA` trusted —
/// loads, and the run refuses its use of `cross_forged` (the replay admission
/// gate over `not_admitted`). Measured 2026-09-24 before that gate:
/// `cross_uses_forged` passed on top of the refused `cross_forged`.
#[test]
fn test_verify_batch_in_run_refuses_use_of_an_earlier_modules_refusal() {
    let mut run = InRun::new();
    let a = run.run("ReplayCrossA", false);
    assert!(!a.load_ok, "the import must refuse ReplayCrossA: {a:?}");
    let error = a.load_error.as_deref().unwrap_or_default();
    assert!(
        error.contains("depend on themselves") && error.contains("cross_forged"),
        "{error}"
    );
    let b = run.run("ReplayCrossB", false);
    assert!(b.load_ok, "ReplayCrossB must load and be checked: {b:?}");
    let message = b
        .tc_errors
        .get("cross_uses_forged")
        .unwrap_or_else(|| panic!("a use of a refused declaration was admitted: {b:?}"));
    assert!(
        message.contains("which this replay did not admit"),
        "{message}"
    );
    // `cross_honest` came from the refused artifact too, so its user is not
    // admitted either: Lean's replay of the run never added `ReplayCrossA`.
    assert_eq!((b.tc_pass, b.tc_fail), (0, 2), "{:?}", b.tc_errors);
}

/// Every declaration `module` stores, by name (its `.olean` header).
fn declared(module: &str) -> BTreeSet<String> {
    let path = compiled_fixture_dir(FAMILY).join(format!("{module}.olean"));
    let parsed =
        parse_module_file(&path).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    parsed.const_names.into_iter().collect()
}

/// Hole A: a constant no `.olean` of the closure declares is unknown, as for
/// `leanchecker`; and a module-local name Clean's prelude also holds is the
/// module's own declaration. Measured before the fix: `per-constant-verify`
/// and every `stamp-verified` mode stamped the three `: False` forgeries.
#[test]
fn test_verify_batch_full_lanes_prelude_only_constants_are_unknown() {
    let targets = names(&[
        "prelude_sorry",
        "prelude_arith",
        "prelude_ay",
        "Nat.not_succ_lt_zero",
        "prelude_honest",
    ]);
    for (lane, outcome) in lanes("ReplayPrelude", &targets) {
        assert_eq!((outcome.0, outcome.1), (1, 4), "{lane}: {:?}", outcome.2);
        for forged in ["prelude_sorry", "prelude_arith", "prelude_ay"] {
            expect_refused(lane, &outcome, forged, "UnknownConst");
        }
        expect_refused(lane, &outcome, "Nat.not_succ_lt_zero", "TypeMismatch");
    }
    let targets = names(&["Nat.not_succ_lt_zero", "prelude_shadow_use"]);
    for (lane, outcome) in lanes("ReplayPreludeUse", &targets) {
        assert_eq!((outcome.0, outcome.1), (1, 1), "{lane}: {:?}", outcome.2);
        expect_refused(lane, &outcome, "prelude_shadow_use", "TypeMismatch");
    }
}

/// The `.olean` loader's recursor refusals for `module`: every stored recursor
/// record that is not the one the kernel generates from the stored family is
/// refused at import (clean-kernel `env/imported_family.rs`), named.
fn load_time_recursor_refusals(module: &str) -> BTreeMap<String, String> {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .unwrap_or_else(|e| panic!("load {module}: {e}"))
    .into_iter()
    .flat_map(|summary| summary.skipped_constants)
    .filter(|s| s.reason.contains("imported family record"))
    .map(|s| (s.name, s.reason))
    .collect()
}

/// Hole B: each stored block is rebuilt by the kernel from its stored types,
/// and every stored constructor and recursor must equal the regenerated one;
/// the block's members and every user are refused otherwise.
///
/// Two lines of defence now meet here. The loader refuses each forged
/// recursor record at import, so it never becomes resident (the lanes report
/// it missing, a refusal); the replay then refuses the block the record
/// belonged to, and every user, exactly as Lean's replay refuses a module for
/// one invalid stored member.
#[test]
fn test_verify_batch_full_lanes_forged_inductive_blocks_are_refused() {
    // (module, user, block members, the member the LOADER refuses). A forged
    // recursor is refused at import; a forged constructor TYPE is a fact about
    // the family declaration itself, which only the replay's re-admission
    // checks (`FRC.rec` is exactly what the kernel derives from the stored
    // shape, so it imports, and the replay refuses its block).
    for (module, user, members, refused_at_load) in [
        (
            "ReplayForgedRec",
            "forged_rec_false",
            ["FRT", "FRT.a", "FRT.b", "FRT.rec"].as_slice(),
            Some("FRT.rec"),
        ),
        (
            "ReplayForgedRule",
            "forged_rule_eq",
            ["FRR", "FRR.a", "FRR.b", "FRR.rec"].as_slice(),
            Some("FRR.rec"),
        ),
        (
            "ReplayForgedCtor",
            "forged_ctor_false",
            ["FRC", "FRC.a", "FRC.rec"].as_slice(),
            None,
        ),
    ] {
        let mut targets = names(members);
        targets.insert(user.to_owned());
        for (lane, outcome) in lanes(module, &targets) {
            assert_eq!(
                (outcome.0, outcome.1),
                (0, targets.len()),
                "{module} {lane}: {:?}",
                outcome.2
            );
            for member in members {
                if Some(*member) == refused_at_load {
                    expect_refused(lane, &outcome, member, "missing requested target");
                } else {
                    expect_refused(lane, &outcome, member, "replay order:");
                }
            }
        }
        let at_load = load_time_recursor_refusals(module);
        match refused_at_load {
            Some(rec) => assert!(
                at_load.get(rec).is_some_and(
                    |why| why.contains(&format!("imported family record {rec} refused"))
                ),
                "{module}: the loader must refuse the stored `{rec}` by name: {at_load:?}"
            ),
            None => assert!(at_load.is_empty(), "{module}: {at_load:?}"),
        }
    }
}

/// `kernel-result-sort-whnf-elim` (P0, 2026-10-16) at the structural import
/// tier and in every lane: `inductive FDP : fdp_prop` with `fdp_prop := Prop`
/// is a `Prop` family to Lean's kernel, which generates a `Prop`-only
/// `FDP.rec`. The forgery stores a LARGE `FDP.rec` (a motive universe), the one
/// Clean used to regenerate from the syntactic head, and proves `False`
/// through it. The loader must refuse that record (its regeneration now reads
/// the level up to whnf), and the honest twin must import with no refusal.
#[test]
fn test_delta_prop_family_imports_and_replays_at_leans_result_level() {
    let at_load = load_time_recursor_refusals("ReplayForgedDeltaPropLargeElim");
    assert!(
        at_load.get("FDP.rec").is_some_and(|why| {
            why.contains("imported family record FDP.rec refused")
                && why.contains("elimination universe differs")
        }),
        "the loader must refuse the stored large `FDP.rec` by name: {at_load:?}"
    );
    let honest_at_load = load_time_recursor_refusals("ReplayHonestDeltaProp");
    assert!(honest_at_load.is_empty(), "{honest_at_load:?}");

    let members = ["FDP", "FDP.t", "FDP.f", "FDP.rec"];
    let mut targets = names(&members);
    targets.insert("forged_dp_false".to_owned());
    for (lane, outcome) in lanes("ReplayForgedDeltaPropLargeElim", &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (0, targets.len()),
            "{lane}: {:?}",
            outcome.2
        );
        expect_refused(lane, &outcome, "FDP.rec", "missing requested target");
        for member in ["FDP", "FDP.t", "FDP.f"] {
            expect_refused(lane, &outcome, member, "replay order:");
        }
    }
    let honest = declared("ReplayHonestDeltaProp");
    for (lane, outcome) in lanes("ReplayHonestDeltaProp", &honest) {
        assert_eq!(
            (outcome.0, outcome.1),
            (honest.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
}

/// The honest control for Hole B: every block shape the kernel distinguishes,
/// compiled by Lean, with every auxiliary definition its elaborator adds —
/// each stored member must equal Clean's regeneration, or this module fails.
#[test]
fn test_verify_batch_full_lanes_honest_inductive_blocks_verify() {
    let targets = declared("ReplayHonestInd");
    assert!(targets.len() > 100, "the whole module: {}", targets.len());
    for (lane, outcome) in lanes("ReplayHonestInd", &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (targets.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
}

/// A stored `quotInfo` is replayed as the kernel's own quotient declaration:
/// the canonical `Quot.ind` stays resident, so `Quot.ind False` is ill-typed.
#[test]
fn test_verify_batch_full_lanes_stored_quotient_is_the_canonical_one() {
    let targets = names(&["forged_quot_false"]);
    for (lane, outcome) in lanes("ReplayForgedQuot", &targets) {
        assert_eq!((outcome.0, outcome.1), (0, 1), "{lane}: {:?}", outcome.2);
    }
}

/// Hole C: a native reducer fires in Lean's theory only when a differential
/// battery shows it computes what δι computes. `String.drop`/`take` return a
/// `String.Slice` in Lean 4.30 and trim/case-map are ASCII-only; Clean's
/// reducers are not, and every lane accepted the five equations before.
#[test]
fn test_verify_batch_full_lanes_string_reducers_that_disagree_with_lean_are_off() {
    let forged = names(&[
        "forged_str_drop",
        "forged_str_take",
        "forged_str_trim",
        "forged_str_lower",
        "forged_str_upper",
    ]);
    // One module: its `String` closure is the battery's slowest load (286
    // modules). The honest control `ReplayHonestStr` runs in the mathverse
    // battery and in `lean_profile_reducer_differential.rs`.
    for (lane, outcome) in lanes("ReplayForgedStr", &forged) {
        assert_eq!((outcome.0, outcome.1), (0, 5), "{lane}: {:?}", outcome.2);
        for name in &forged {
            expect_refused(lane, &outcome, name, "TypeMismatch");
        }
    }
}

/// Clean's prelude statement of `Nat.not_succ_lt_zero` — `∀ n, Nat.lt (n+1) 0
/// → False`, the one `ReplayPreludeUse`'s user needs — as a resident theorem.
/// The fixture spells that statement as `prelude_shadow_use`'s type, so it is
/// read from there rather than rebuilt by hand. Its value is `sorryAx` at that
/// statement: what the run must refuse is the MODULE's redeclaration, never the
/// seed's proof, and a value-carrying seed is the shape a kernel seed has (a
/// value-free one takes the loader's stub-completion path instead).
fn clean_prelude_not_succ_lt_zero() -> ConstantInfo {
    let path = compiled_fixture_dir(FAMILY).join("ReplayPreludeUse.olean");
    let parsed =
        parse_module_file(&path).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    let user = parsed
        .constants
        .iter()
        .find(|c| c.name == "prelude_shadow_use")
        .unwrap_or_else(|| panic!("ReplayPreludeUse declares no prelude_shadow_use"));
    let user = convert_parsed_constant_to_const_info(user)
        .unwrap_or_else(|e| panic!("convert prelude_shadow_use: {e}"))
        .unwrap_or_else(|| panic!("prelude_shadow_use is not a plain constant"));
    let placeholder = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("sorryAx"), vec![Level::zero()]),
            user.type_.clone(),
        ),
        Expr::const_(Name::from_string("Bool.false"), vec![]),
    );
    ConstantInfo::new_with_reducibility(
        Name::from_string("Nat.not_succ_lt_zero"),
        user.level_params,
        user.type_,
        Some(placeholder),
        Reducibility::Opaque,
        ConstantKind::Theorem,
    )
}

/// `clean olean verify-batch` loads module after module into one environment,
/// and the loader keeps the first declaration of a name: a later module's
/// declaration of a name the environment already holds is dropped, and its
/// users would be checked against the resident one.
///
/// Layer 1: when another ARTIFACT holds the name differently, the import
/// itself refuses the module (module-trust `ConflictingDeclaration`) —
/// `ReplayPreludeUse` after `ReplayPrelude` (both declare
/// `Nat.not_succ_lt_zero`), and `ReplayRedeclare` (`Nat.pred`, which
/// `Init.Prelude` declares).
///
/// Layer 2: a name resident with no artifact behind it — a kernel seed, or
/// Clean's prelude statement of `Nat.not_succ_lt_zero` that this fixture was
/// minted against — is no artifact's declaration, so the import keeps it and
/// drops the module's own as shadowed. The run refuses the module's
/// declaration as already declared (Lean's `addDecl`), and its user with it;
/// without that refusal both are checked against the resident statement and
/// pass.
#[test]
fn test_verify_batch_in_run_refuses_a_declaration_another_module_holds() {
    let mut run = InRun::new();
    let prelude = run.run("ReplayPrelude", false);
    assert!(prelude.load_ok, "{prelude:?}");
    let used = run.run("ReplayPreludeUse", false);
    assert!(
        !used.load_ok,
        "the import must refuse a second, different `Nat.not_succ_lt_zero`: {used:?}"
    );
    let error = used.load_error.as_deref().unwrap_or_default();
    assert!(
        error.contains("Nat.not_succ_lt_zero") && error.contains("ReplayPrelude"),
        "{error}"
    );
    let redeclared = run.run("ReplayRedeclare", false);
    assert!(
        !redeclared.load_ok,
        "the import must refuse a redeclared `Nat.pred`: {redeclared:?}"
    );
    let error = redeclared.load_error.as_deref().unwrap_or_default();
    assert!(
        error.contains("Nat.pred") && error.contains("Init.Prelude"),
        "{error}"
    );

    let mut run = InRun::new();
    run.seed(clean_prelude_not_succ_lt_zero());
    let used = run.run("ReplayPreludeUse", false);
    assert!(
        used.load_ok,
        "ReplayPreludeUse must load over the seed: {used:?}"
    );
    let message = used
        .tc_errors
        .get("Nat.not_succ_lt_zero")
        .unwrap_or_else(|| panic!("counted and refused: {:?}", used.tc_errors));
    assert!(message.contains("already declared"), "{message}");
    assert!(
        used.tc_errors.contains_key("prelude_shadow_use"),
        "{:?}",
        used.tc_errors
    );
    assert_eq!((used.tc_pass, used.tc_fail), (0, 2), "{:?}", used.tc_errors);
}

/// leanprover/lean4#14807, `is_prop` requires a sort (shipped in v4.33.1).
/// `ReplayIsPropStuck` projects a data field (`IPK.observe`) out of a value
/// whose type's type does not reduce to a sort. Before the fix these lanes
/// admitted the module (a live Clean hole for leanprover/lean4#14807, measured
/// 2026-10-18); after it, `is_prop` errors at the sort
/// requirement, so every lane refuses `IPK.observe` and the `False` that uses
/// it, while the forged family (admitted unchanged by this guard) and the
/// honest base verify.
///
/// Release-only (`cfg(not(debug_assertions))`, so a debug build does not
/// compile it rather than pass it): the fixture imports `Init.WF`, whose
/// closure a debug build did not finish loading in 17 min (release: ~24 s).
#[cfg(not(debug_assertions))]
#[test]
fn test_verify_batch_full_lanes_projection_needs_a_sort_typed_type() {
    let targets = declared("ReplayIsPropStuck");
    assert!(targets.contains("IPK.observe"), "{targets:?}");
    for (lane, outcome) in lanes("ReplayIsPropStuck", &targets) {
        expect_refused(lane, &outcome, "IPK.observe", "ExpectedSort");
        expect_refused(lane, &outcome, "isprop_stuck_false", "IPK.observe");
    }
    let honest = declared("ReplayIsPropStuckBase");
    for (lane, outcome) in lanes("ReplayIsPropStuckBase", &honest) {
        assert_eq!(
            (outcome.0, outcome.1),
            (honest.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
}

// Hole R112: blocks found through a forged `all`, and stored flags the replay
// did not compare.
#[path = "replay_forged_lanes/block_cover.rs"]
mod block_cover;
// Hole B1 (R113): a declaration in a part `lean` never reads is refused by name.
#[path = "replay_forged_lanes/misplaced.rs"]
mod misplaced;
// Hole B3 (R113) through the loader: a trailer on an imported Lean part.
#[path = "replay_forged_lanes/trailer.rs"]
mod trailer;

// R131: value-free stubs a later part completes.
#[path = "replay_forged_lanes/stubs.rs"]
mod stubs;
// R142: a value the authoritative part states must be resident with it.
#[path = "replay_forged_lanes/values.rs"]
mod values;
