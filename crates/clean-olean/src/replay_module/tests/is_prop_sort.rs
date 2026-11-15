// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay` on the kernel's `is_prop`-requires-a-sort rule
//! (leanprover/lean4#14807, shipped in v4.33.1), against the `replay_forged`
//! fixture pinned Lean minted with `addDeclCore`.
//!
//! Release-only: the fixture imports `Init.WF`, whose closure a debug build did
//! not finish loading in 17 min (release: ~24 s), so a debug build compiles
//! nothing here rather than passing it.

use super::*;

/// `ReplayIsPropStuck` projects a data field (`IPK.observe`) out of a value
/// whose type's type does not reduce to a sort. Before the fix `clean olean
/// replay` admitted the module (a live Clean hole for leanprover/lean4#14807,
/// measured 2026-10-18); after it, `is_prop` errors at the sort requirement, so the
/// replay refuses `IPK.observe` and the `False` built on it, while the honest
/// base is admitted in full.
#[test]
fn test_replay_module_projection_needs_a_sort_typed_type() {
    let honest = replay("ReplayIsPropStuckBase", ReplayMode::ImportsTrusted);
    assert_admitted(&honest, honest.constants_checked);
    assert!(honest.constants_checked > 0, "{honest:?}");
    let forged = replay("ReplayIsPropStuck", ReplayMode::ImportsTrusted);
    assert_refused(&forged, "IPK.observe", "ExpectedSort");
    assert_refused(&forged, "isprop_stuck_false", "IPK.observe");
}
