// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hole R112 in the three `verify_batch_full` lanes: a stored inductive block
//! the replay never rebuilt, and a stored flag it never compared.
//!
//! - `ReplayForgedAllGhost` / `ReplayForgedAllOther`: `FAG`/`FAO : Prop` with
//!   the negative constructor `mk : (T → False) → T`, stored with an `all` that
//!   names no block containing it (`[FAG_ghost]`, or `[FAH, FAO]` with the
//!   honest `FAH` first) and no recursor. Before the fix every lane admitted
//!   `forged_all_* : False` (measured 2026-10-22, release `clean olean
//!   verify-batch --full-validation`: `tc_pass 3, tc_fail 0`), because the
//!   block was found through `all` and never sent to the kernel. Pinned
//!   `leanchecker` refuses both (README).
//! - `ReplayForgedIsRec`: `FIR | mk : FIR → FIR` stored with `isRec := false`.
//!   Every lane admitted `forged_isrec_eta : ∀ x, FIR.mk x.1 = x := rfl` by
//!   structure eta read off the stored flag.
//! - Controls: `ReplayHonestIndFlags` (Lean's block-level `isRec` on the
//!   non-recursive member of a mutual block, `isReflexive` from a nested
//!   block's auxiliary types) verifies in full, and `ReplayForgedMutualEta`
//!   (unit-like eta on that member, which Lean refuses) is refused by the
//!   kernel, not by the block replay.

use super::*;

#[test]
fn test_verify_batch_full_lanes_block_found_through_a_forged_all_is_refused() {
    for (module, members, user, honest) in [
        (
            "ReplayForgedAllGhost",
            ["FAG", "FAG.mk"],
            "forged_all_ghost_false",
            &[][..],
        ),
        (
            "ReplayForgedAllOther",
            ["FAO", "FAO.mk"],
            "forged_all_other_false",
            &["FAH", "FAH.a", "FAH.rec"][..],
        ),
    ] {
        let targets = declared(module);
        assert_eq!(
            targets.len(),
            members.len() + 1 + honest.len(),
            "{module}: {targets:?}"
        );
        for (lane, outcome) in lanes(module, &targets) {
            assert_eq!(
                (outcome.0, outcome.1),
                (honest.len(), members.len() + 1),
                "{module} {lane}: {:?}",
                outcome.2
            );
            expect_refused(lane, &outcome, members[0], "No such inductive");
            // The constructor is refused by name (`No such constructor`) or,
            // first, through its type: its stored block is not its type's, so
            // its type is an ordinary dependency, refused `No such inductive`.
            expect_refused(lane, &outcome, members[1], "No such");
            expect_refused(lane, &outcome, user, members[0]);
        }
    }
}

#[test]
fn test_verify_batch_full_lanes_forged_recursive_flag_is_refused() {
    let targets = declared("ReplayForgedIsRec");
    assert_eq!(
        targets,
        names(&["FIR", "FIR.mk", "FIR.rec", "forged_isrec_eta"])
    );
    for (lane, outcome) in lanes("ReplayForgedIsRec", &targets) {
        assert_eq!((outcome.0, outcome.1), (0, 4), "{lane}: {:?}", outcome.2);
        for member in ["FIR", "FIR.mk", "FIR.rec"] {
            expect_refused(lane, &outcome, member, "recursive flag (isRec)");
        }
        expect_refused(lane, &outcome, "forged_isrec_eta", "FIR");
    }
}

#[test]
fn test_verify_batch_full_lanes_block_level_flags_verify_and_bar_eta() {
    let targets = declared("ReplayHonestIndFlags");
    for (lane, outcome) in lanes("ReplayHonestIndFlags", &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (targets.len(), 0),
            "{lane}: {:?}",
            outcome.2
        );
    }
    let targets = declared("ReplayForgedMutualEta");
    for (lane, outcome) in lanes("ReplayForgedMutualEta", &targets) {
        assert_eq!(
            (outcome.0, outcome.1),
            (targets.len() - 1, 1),
            "{lane}: {:?}",
            outcome.2
        );
        expect_refused(lane, &outcome, "forged_hma_eta", "TypeMismatch");
    }
}
