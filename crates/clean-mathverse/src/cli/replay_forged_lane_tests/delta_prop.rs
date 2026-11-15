// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The δ-Prop family (`ReplayHonestDeltaProp`, `ReplayForgedDeltaPropLargeElim`)
//! through the mathverse re-check lanes; split from the parent module to keep
//! it under the size ratchet.

use super::*;

/// `kernel-result-sort-whnf-elim` (P0, 2026-10-16), per constant and through
/// every `stamp-verified` mode: `inductive FDP : fdp_prop` with
/// `fdp_prop := Prop` is a `Prop` family to Lean's kernel (whnf finds its
/// level), so `FDP.rec` eliminates only into `Prop`. The forgery stores a
/// LARGE `FDP.rec` and proves `False` through `FDP.rec.{1}` into `Bool`
/// (pinned `leanchecker`: rc 1, `incorrect number of universe levels
/// parameters for 'FDP.rec', #0 expected, #1 provided`). Every lane
/// regenerates the stored recursor and compares; while the kernel read the
/// syntactic head its regeneration was the forged one. The honest twin
/// (`leanchecker` rc 0) must verify in full.
#[test]
fn test_per_constant_verify_delta_prop_family_follows_leans_result_level() {
    let r = per_constant("ReplayForgedDeltaPropLargeElim", &[]);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert!(
        errs("forged_dp_false").is_some(),
        "`forged_dp_false : False` must be refused: targets {:?}, errors {:?}",
        r.targets,
        r.errors
    );
    assert_eq!((r.kernel_verified, r.failed), (1, 1), "{:?}", r.errors);
    let r = per_constant("ReplayHonestDeltaProp", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(
        r.kernel_verified,
        value_bearing("ReplayHonestDeltaProp").len()
    );
}

#[test]
fn test_stamp_verified_all_modes_delta_prop_family_follows_leans_result_level() {
    for mode in STAMP_MODES {
        let stamped = stamp(&["ReplayForgedDeltaPropLargeElim"], mode);
        for forged in ["forged_dp_false", "FDP", "FDP.t", "FDP.f", "FDP.rec"] {
            assert!(
                !stamped.contains(forged),
                "stamp-verified {mode:?} stamped `{forged}`: {stamped:?}"
            );
        }
        let wanted = value_bearing("ReplayHonestDeltaProp");
        let stamped = stamp(&["ReplayHonestDeltaProp"], mode);
        let missing: Vec<&String> = wanted.difference(&stamped).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?}: not stamped {missing:?}"
        );
    }
}
