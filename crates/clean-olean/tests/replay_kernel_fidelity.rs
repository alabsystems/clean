// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-wide places where Clean's kernel disagrees, or disagreed, with
//! pinned Lean v4.30.0-rc2, through the `.olean` loader and the three
//! `verify_batch_full` lanes (fixture family `replay_forged`; `leanchecker`
//! and per-constant verdicts in its README; `docs/DECISIONS.md` R139-R141).
//!
//! Closed (R139, R140; the level shapes by R150's Lean level algebra):
//! - `ReplayHonestDepNested` and `ReplayHonestDepNestedDeep`: blocks nested
//!   through a DEPENDENT container whose family argument is a lambda.
//!   `ReplayHonestDepNested` nests once, through `Sigma`, `PSigma` and a user
//!   `DBox` (its `SJ` is a single-level stand-in for the redex in `Lean.Json`'s
//!   map field); `ReplayHonestDepNestedDeep` has `Lean.Json`'s real shape, a
//!   structure over a RECURSIVE dependent container. Lean keeps the β-redex its
//!   elimination leaves, so it stores `isReflexive := false` and the redex in
//!   every recursor. Clean β-normalized the auxiliary types and refused every
//!   such block and its users: a false refusal of `.olean`s Lean wrote (the
//!   same refusal stopped `Lean.Data.Json.Basic` and `Lean.Data.PrefixTree`;
//!   `reports/kernel-fidelity-2026-10-24/`). `ReplayForgedDepNestedRefl` (`SGS`
//!   stored with `isReflexive := true`) is still refused.
//! - `ReplayForgedPowCap`: `Nat.pow 1 16777217 = 1 := rfl` and `Nat.pow 0
//!   16777217 = 0 := rfl`, which Lean refuses (`reduce_pow` declines an
//!   exponent above `2^24`, then deep recursion) and Clean folded.
//! - Levels (R141's review items K3-K5, closed by R150): every lane refuses
//!   what pinned Lean refuses in `ReplayForgedLevelJoin` (`LJB`, `LJD`, `LJE`),
//!   `ReplayForgedLevelAssoc` (`LJB2`, `LJS2`) and `ReplayForgedMutualLevel`,
//!   and admits all of `ReplayHonestLevelAssoc`, whose `B1` and `P1` a
//!   comparison by Lean's `is_equivalent` over Clean-built levels refused and
//!   whose `LB` Clean refused before R150.
//!
//! KNOWN GAPS, pinned so each fails loudly the day it closes (D2
//! over-acceptances: Clean admits what pinned Lean refuses, every admitted
//! statement true):
//! - `ReplayForgedPowCapOuter` (R140's open half): an outer `Nat.mul`/`add`/
//!   `sub`/`pow` over an over-cap `Nat.pow` δ-reduces past the stuck operand.
//! - `ReplayForgedShlCap`: `Nat.shiftLeft` by `2^32` or more, where Lean's
//!   kernel aborts the process and Clean closes the equation by congruence.
//!
//! It sits beside the `olean-replay-order` battery (`replay_forged_lanes.rs`),
//! not in it: that battery's mutation arms pin its file.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{Environment, ProofValueElision};
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::verify_batch_full::{
    typecheck_constants_full, typecheck_constants_full_streaming,
};
use clean_olean::verify_parallel::typecheck_constants_full_parallel;
use clean_olean::{
    default_search_paths, load_module_with_deps_shared_with_policy, parse_module_file,
    OleanImportPolicy,
};

const FAMILY: &str = "replay_forged";

type Outcome = (usize, usize, BTreeMap<String, String>);

/// Lean's replay environment plus `module`'s closure through the trusted
/// `.olean` path, and the loader's family-record refusals.
fn load(module: &str) -> (Environment, BTreeMap<String, String>) {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    let refusals = load_module_with_deps_shared_with_policy(
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
    .collect();
    env.regenerate_missing_no_confusion();
    (env, refusals)
}

/// Every declaration `module` stores, by name (its `.olean` header).
fn declared(module: &str) -> BTreeSet<String> {
    let path = compiled_fixture_dir(FAMILY).join(format!("{module}.olean"));
    let parsed =
        parse_module_file(&path).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    parsed.const_names.into_iter().collect()
}

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| (*s).to_owned()).collect()
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

/// `leanchecker ReplayHonestDepNested`: rc 0, every constant accepted. The
/// loader imports every recursor record (each equals the regenerated one)
/// and every lane verifies all 26 declarations.
#[test]
fn test_dependent_container_nested_blocks_import_and_verify_in_every_lane() {
    let (env, at_load) = load("ReplayHonestDepNested");
    assert!(
        at_load.is_empty(),
        "the loader refuses no recursor Lean generated: {at_load:?}"
    );
    let targets = declared("ReplayHonestDepNested");
    for expected in [
        "SGS",
        "SGS.rec_1",
        "SG.rec_1",
        "SGP.rec_1",
        "DB.rec_1",
        "SJ.rec_1",
        "honest_sgs_elim",
        "honest_sj_depth",
    ] {
        assert!(targets.contains(expected), "{expected}: {targets:?}");
    }
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (targets.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
}

/// `leanchecker ReplayForgedDepNestedRefl`: rc 0 — Lean's replay installs
/// the regenerated inductive value and never reads the stored flag. Clean's
/// replay checks later declarations against the STORED value (R112), so it
/// compares the flag: the honest `false` regenerates, the stored `true` is
/// refused, and the block's user with it.
#[test]
fn test_dependent_container_nested_forged_reflexive_flag_is_refused() {
    let (env, _) = load("ReplayForgedDepNestedRefl");
    let targets = declared("ReplayForgedDepNestedRefl");
    assert_eq!(
        targets,
        names(&["SGS", "SGS.mk", "SGS.rec", "SGS.rec_1", "forged_sgs_elim"])
    );
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (0, targets.len()),
            "{lane}: {:?}",
            outcome.2
        );
        for member in ["SGS", "SGS.mk", "SGS.rec", "SGS.rec_1"] {
            expect_refused(lane, &outcome, member, "reflexive flag (isReflexive)");
        }
        expect_refused(lane, &outcome, "forged_sgs_elim", "SGS");
    }
}

/// Per constant, pinned Lean refuses both forgeries (`deep recursion
/// detected`) and accepts both controls; so does every lane, the forgeries
/// as a mismatch of the stuck `Nat.pow` application.
#[test]
fn test_nat_pow_folds_only_up_to_leans_exponent_cap_in_every_lane() {
    let (env, _) = load("ReplayForgedPowCap");
    let targets = names(&[
        "pow_one_at_cap",
        "pow_small",
        "pow_one_over_cap",
        "pow_zero_over_cap",
    ]);
    assert_eq!(declared("ReplayForgedPowCap"), targets);
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!((outcome.0, outcome.1), (2, 2), "{lane}: {:?}", outcome.2);
        expect_refused(lane, &outcome, "pow_one_over_cap", "TypeMismatch");
        expect_refused(lane, &outcome, "pow_zero_over_cap", "TypeMismatch");
    }
}

/// Every lane verifies a module and its declarations admitted, by name.
fn expect_admitted_in_every_lane(module: &str, names_: &[&str]) {
    let (env, _) = load(module);
    let targets = names(names_);
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (targets.len(), 0),
            "{module} {lane}: {:?}",
            outcome.2
        );
    }
}

/// `leanchecker ReplayHonestDepNestedDeep`: rc 0. The base kernel refused the
/// `RJ` block and every user (`Invalid recursor RJ.rec_2`, 40 of the module's
/// 80 declarations); every lane now verifies all of it.
#[test]
fn test_recursive_dependent_container_nested_block_verifies_in_every_lane() {
    let targets = declared("ReplayHonestDepNestedDeep");
    for expected in [
        "RJ",
        "RJ.rec",
        "RJ.rec_1",
        "RJ.rec_2",
        "honest_rj_obj",
        "honest_rj_ne",
    ] {
        assert!(targets.contains(expected), "{expected}: {targets:?}");
    }
    let (env, at_load) = load("ReplayHonestDepNestedDeep");
    assert!(at_load.is_empty(), "{at_load:?}");
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (targets.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
}

/// `leanchecker ReplayHonestLevelAssoc`: rc 0, every constant accepted, and so
/// does every lane: `P1` and `B1`, which a Lean-theory comparison by Lean's
/// `is_equivalent` over the levels Clean built refused (R141, review K3), and
/// `LB : Sort (max (max u v) (imax u v)) := LA` with `LA : Sort (max u (max v
/// (imax u v)))`, which Clean refused before R150 decoded levels as stored.
#[test]
fn test_level_spellings_lean_equates_verify_in_every_lane() {
    expect_admitted_in_every_lane(
        "ReplayHonestLevelAssoc",
        &["X", "Y", "P1", "A1", "B1", "LA", "LB"],
    );
}

/// Per constant, pinned Lean refuses `LJB`, `LJD` and `LJE` (`declaration
/// type mismatch`) and accepts `LJA`, `LJC`, `LJK` and `LJF`; so does every
/// lane (R150; an admission before it, R141).
#[test]
fn test_level_join_equations_are_refused_as_lean_refuses_them() {
    let (env, _) = load("ReplayForgedLevelJoin");
    let targets = names(&["LJA", "LJC", "LJB", "LJD", "LJK", "LJF", "LJE"]);
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!((outcome.0, outcome.1), (4, 3), "{lane}: {:?}", outcome.2);
        for forged in ["LJB", "LJD", "LJE"] {
            expect_refused(lane, &outcome, forged, "TypeMismatch");
        }
    }
}

/// Review K4: `LJB2` (`LJB` re-associated) and `LJS2 : Sort (succ (max u
/// (v+1))) := LJS1` with `LJS1 : Sort (succ (imax u (v+1)))`; pinned Lean
/// refuses both (`declaration type mismatch`) and accepts the two axioms. Every
/// lane refuses both too: `LJB2` as a mismatch, `LJS2` by R150's fail-closed
/// rule for a stored level Lean's `mk_imax` would rebuild (`LJS1`'s `imax u
/// (v+1)`), where Lean's own verdict depends on the `.olean`'s object sharing.
#[test]
fn test_level_spellings_lean_refuses_are_refused_in_every_lane() {
    let (env, _) = load("ReplayForgedLevelAssoc");
    let targets = names(&["LJA2", "LJB2", "LJS1", "LJS2"]);
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!((outcome.0, outcome.1), (2, 2), "{lane}: {:?}", outcome.2);
        expect_refused(lane, &outcome, "LJB2", "TypeMismatch");
        expect_refused(lane, &outcome, "LJS2", "LevelSharingDependent");
    }
}

/// Review K5: `leanchecker ReplayForgedMutualLevel` rc 1, `mutually inductive
/// types must live in the same universe`; every lane refuses the block, each
/// member and recursor by the same mutual-universe check.
#[test]
fn test_mutual_universe_join_is_refused_in_every_lane() {
    let (env, _) = load("ReplayForgedMutualLevel");
    let block = ["MA", "MA.a", "MA.rec", "MB", "MB.b", "MB.rec"];
    let targets = names(&block);
    for (lane, outcome) in lanes(env, &targets) {
        assert_eq!((outcome.0, outcome.1), (0, 6), "{lane}: {:?}", outcome.2);
        for member in block {
            expect_refused(lane, &outcome, member, "lives in a different universe");
        }
    }
}

/// KNOWN GAP (R140's open half, review K1): pinned Lean refuses the five
/// forgeries (`deep recursion detected`) and accepts the two controls; every
/// lane admits all seven.
#[test]
fn test_outer_nat_op_over_an_over_cap_pow_is_admitted_known_gap() {
    expect_admitted_in_every_lane(
        "ReplayForgedPowCapOuter",
        &[
            "mul_at_zero",
            "add_at_zero",
            "mul_over_zero",
            "add_over_zero",
            "sub_over_zero",
            "pow_over_exp0",
            "mul_over2_zero",
        ],
    );
}

/// KNOWN GAP (review K2): `leanchecker ReplayForgedShlCap` panics (`Nat.shiftl
/// exponent is too big`, exit 1) on the shift-`2^32` congruence; every lane
/// admits both forgeries, with the controls.
#[test]
fn test_shift_left_past_leans_abort_is_admitted_known_gap() {
    expect_admitted_in_every_lane(
        "ReplayForgedShlCap",
        &["shl_zero_base", "shl_cong_small", "shl_cong", "shl_cong64"],
    );
}
