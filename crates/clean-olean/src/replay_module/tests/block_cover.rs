// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay` on hole R112, against the `replay_forged` fixtures
//! pinned Lean minted with its kernel bypassed (`leanchecker` verdicts in the
//! family README): a stored type whose `all` names no block containing it is
//! never rebuilt, and a stored `isRec` the replay never compared decides eta.
//! Measured 2026-10-22 with a release `clean` before the fix: `clean olean
//! replay --exact` admitted every declaration of `ReplayForgedAllGhost` (3),
//! `ReplayForgedAllOther` (6) and `ReplayForgedIsRec` (4), two proofs of
//! `False` among them.

use super::*;

/// The constructor is refused by name or, first, through its type (its stored
/// block is not its type's, so its type is an ordinary dependency): either way
/// the message says `No such`.
///
/// `leanchecker ReplayForgedAllGhost`: rc 1 (its replay panics looking up
/// `FAG_ghost`, then `(kernel) unknown constant` while replaying `FAG`).
/// `leanchecker ReplayForgedAllOther`: rc 1, `(kernel) constant has already
/// been declared 'FAH'` while replaying `FAO`. Both are refused by name, and
/// the honest `FAH` block beside the forgery is admitted.
#[test]
fn test_replay_module_block_found_through_a_forged_all_is_refused() {
    let record = replay("ReplayForgedAllGhost", ReplayMode::ImportsTrusted);
    assert_eq!(record.constants_checked, 3, "{record:?}");
    assert_eq!(record.admitted, 0, "{record:?}");
    assert_refused(&record, "FAG", "No such inductive FAG");
    assert_refused(&record, "FAG.mk", "No such");
    assert_refused(&record, "forged_all_ghost_false", "FAG");

    let record = replay("ReplayForgedAllOther", ReplayMode::ImportsTrusted);
    assert_eq!(record.constants_checked, 6, "{record:?}");
    assert_eq!(record.admitted, 3, "the honest FAH block: {record:?}");
    assert_refused(&record, "FAO", "No such inductive FAO");
    assert_refused(&record, "FAO.mk", "No such");
    assert_refused(&record, "forged_all_other_false", "FAO");
}

/// `leanchecker ReplayForgedIsRec`: rc 1, `(kernel) declaration type
/// mismatch, 'forged_isrec_eta'` (the regenerated `isRec := true` bars eta).
/// The stored flag differs from the regenerated one, so the block is refused.
/// `leanchecker ReplayForgedMutualEta`: rc 1, the same mismatch for
/// `forged_hma_eta` (Lean's `isRec` is block-level), and `leanchecker
/// ReplayHonestIndFlags`: rc 0.
#[test]
fn test_replay_module_stored_flags_are_the_regenerated_ones() {
    let record = replay("ReplayForgedIsRec", ReplayMode::ImportsTrusted);
    assert_eq!(record.admitted, 0, "{record:?}");
    assert_refused(&record, "FIR", "recursive flag (isRec)");
    assert_refused(&record, "forged_isrec_eta", "FIR");

    let record = replay("ReplayForgedMutualEta", ReplayMode::ImportsTrusted);
    assert_eq!(record.admitted, record.constants_checked - 1, "{record:?}");
    assert_refused(&record, "forged_hma_eta", "TypeMismatch");

    let honest = replay("ReplayHonestIndFlags", ReplayMode::ImportsTrusted);
    assert_admitted(&honest, honest.constants_checked);
    assert!(honest.constants_checked >= 19, "{honest:?}");
}
