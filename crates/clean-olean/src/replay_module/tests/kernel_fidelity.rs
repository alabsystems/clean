// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay` (`leanchecker`'s semantics, unlimited heartbeats) on
//! places where Clean's kernel disagrees, or disagreed, with pinned Lean
//! v4.30.0-rc2 (fixture family `replay_forged`; verdicts in its README;
//! `docs/DECISIONS.md` R139-R141):
//!
//! - `ReplayHonestDepNested`, `ReplayHonestDepNestedDeep`: blocks nested
//!   through a dependent container with a lambda family argument, once and
//!   through a recursive container (`Lean.Json`'s shape). Lean keeps the
//!   β-redex its elimination leaves (`isReflexive := false`, the redex in
//!   every recursor); Clean regenerated them β-normalized and refused every
//!   block and user, as it refused `Lean.Data.Json.Basic` (`Invalid recursor
//!   Lean.Json.rec_1`, or `Lean.Json.rec` in a `--json` run: every recursor
//!   carries the redex; `reports/kernel-fidelity-2026-10-24/before/`).
//! - `ReplayForgedPowCap`: `Nat.pow 1 16777217 = 1 := rfl`, which Lean
//!   refuses (deep recursion past its `2^24` fold cap) and Clean folded.
//!   With no heartbeat budget, the declined fold must not turn into a 2^24
//!   step δ-walk that ends in an acceptance either: it stays stuck.
//! - Levels (R141's review items K3-K5, closed by R150): levels equal at
//!   every assignment but not Lean's `is_equivalent` (`ReplayForgedLevelJoin`,
//!   `ReplayForgedLevelAssoc`, `ReplayForgedMutualLevel`) are refused as Lean
//!   refuses them, and `ReplayHonestLevelAssoc` is admitted in full.
//! - KNOWN GAPS, pinned: the over-cap `Nat.pow` under an outer operation
//!   (`ReplayForgedPowCapOuter`) and the shift Lean aborts on
//!   (`ReplayForgedShlCap`) are admitted.

use super::*;

/// `leanchecker ReplayHonestDepNested`: rc 0.
#[test]
fn test_replay_module_dependent_container_nested_blocks_are_admitted() {
    let record = replay("ReplayHonestDepNested", ReplayMode::ImportsTrusted);
    assert_admitted(&record, record.constants_checked);
    assert!(record.constants_checked >= 26, "{record:?}");
}

/// `leanchecker ReplayForgedDepNestedRefl`: rc 0 (Lean installs the
/// regenerated value); Clean compares the stored flag (R112) and refuses
/// the block, and its user through it.
#[test]
fn test_replay_module_dependent_container_forged_reflexive_flag_is_refused() {
    let record = replay("ReplayForgedDepNestedRefl", ReplayMode::ImportsTrusted);
    assert_eq!(record.admitted, 0, "{record:?}");
    assert_refused(&record, "SGS", "reflexive flag (isReflexive)");
    assert_refused(&record, "forged_sgs_elim", "SGS");
}

/// `leanchecker ReplayForgedPowCap`: rc 1, `(kernel) deep recursion
/// detected` replaying `pow_one_over_cap`; per constant both forgeries are
/// refused and both controls accepted.
#[test]
fn test_replay_module_nat_pow_above_the_exponent_cap_is_refused() {
    let record = replay("ReplayForgedPowCap", ReplayMode::ImportsTrusted);
    assert_eq!(record.constants_checked, 4, "{record:?}");
    assert_eq!(record.admitted, 2, "the two controls: {record:?}");
    assert_eq!(record.budget_exhausted, 0, "unlimited budget: {record:?}");
    assert_refused(&record, "pow_one_over_cap", "TypeMismatch");
    assert_refused(&record, "pow_zero_over_cap", "TypeMismatch");
}

/// `leanchecker ReplayHonestDepNestedDeep`: rc 0, all 80 constants. The base
/// kernel refused 40 of them (`Invalid recursor RJ.rec_2`).
#[test]
fn test_replay_module_recursive_dependent_container_nested_block_is_admitted() {
    let record = replay("ReplayHonestDepNestedDeep", ReplayMode::ImportsTrusted);
    assert_admitted(&record, 80);
}

/// `leanchecker ReplayForgedLevelJoin`: rc 1, `declaration type mismatch`
/// replaying `LJB`; per constant `LJB`, `LJD` and `LJE` are refused, the four
/// controls accepted. So does the replay (R150; all seven admitted before it).
#[test]
fn test_replay_module_level_join_equations_are_refused_as_lean_refuses_them() {
    let record = replay("ReplayForgedLevelJoin", ReplayMode::ImportsTrusted);
    assert_eq!(record.constants_checked, 7, "{record:?}");
    assert_eq!(record.admitted, 4, "{record:?}");
    for forged in ["LJB", "LJD", "LJE"] {
        assert_refused(&record, forged, "TypeMismatch");
    }
}

/// `leanchecker ReplayHonestLevelAssoc`: rc 0, all seven accepted; so does the
/// replay (`LB` was refused before R150).
#[test]
fn test_replay_module_honest_level_spellings_are_admitted() {
    let record = replay("ReplayHonestLevelAssoc", ReplayMode::ImportsTrusted);
    assert_admitted(&record, 7);
}

/// Pinned Lean refuses `LJB2`/`LJS2` (`declaration type mismatch`) and the
/// `MA`/`MB` block (`mutually inductive types must live in the same
/// universe`); so does the replay (R150): `LJB2` as a mismatch, `LJS2` by the
/// fail-closed rule for a stored level Lean's `mk_imax` would rebuild, and
/// every constant of the block by its mutual-universe check.
#[test]
fn test_replay_module_level_forgeries_are_refused_as_lean_refuses_them() {
    let assoc = replay("ReplayForgedLevelAssoc", ReplayMode::ImportsTrusted);
    assert_eq!(
        (assoc.constants_checked, assoc.admitted),
        (4, 2),
        "{assoc:?}"
    );
    assert_refused(&assoc, "LJB2", "TypeMismatch");
    assert_refused(&assoc, "LJS2", "LevelSharingDependent");
    let mutual = replay("ReplayForgedMutualLevel", ReplayMode::ImportsTrusted);
    assert_eq!(
        (mutual.constants_checked, mutual.admitted),
        (6, 0),
        "{mutual:?}"
    );
    assert_refused(&mutual, "MA", "lives in a different universe");
}

/// KNOWN GAP (review K1): pinned Lean refuses the five over-cap forgeries
/// under an outer operation (`deep recursion detected`); the replay admits all
/// seven constants.
#[test]
fn test_replay_module_outer_pow_forgeries_are_admitted_known_gap() {
    let record = replay("ReplayForgedPowCapOuter", ReplayMode::ImportsTrusted);
    assert_admitted(&record, 7);
    assert_eq!(record.budget_exhausted, 0, "{record:?}");
}

/// KNOWN GAP: `leanchecker ReplayForgedShlCap` aborts (`INTERNAL PANIC:
/// Nat.shiftl exponent is too big`, exit 1); Clean admits all four.
#[test]
fn test_replay_module_shift_left_past_leans_abort_is_admitted_known_gap() {
    let record = replay("ReplayForgedShlCap", ReplayMode::ImportsTrusted);
    assert_admitted(&record, 4);
}
