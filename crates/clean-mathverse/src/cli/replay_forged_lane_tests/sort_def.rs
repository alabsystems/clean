// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An honest family whose sort is an IMPORTED definition
//! (`ReplayHonestSortDef`: `inductive HSD : HSDSort` with `HSDSort := Type`
//! in `ReplayHonestSortDefBase`), through the mathverse re-check lanes
//! (decision R147). Pinned `leanchecker` exits 0 on it, and Clean's `.olean`
//! replay admits every declaration.
//!
//! Measured 2026-10-19 before the fix: `per-constant-verify` refused all 14
//! value-bearing declarations, each as a dependent of `HSD`, whose stored
//! recursor was refused at import ("Invalid recursor HSD.rec"). Its demand
//! walk registered the family before `HSDSort` was resident, so the
//! recursor's regeneration could not reduce the type former to a sort. The
//! walk now loads what the family types name first
//! (`per_constant_family_deps.rs`).

use super::*;

/// `per-constant-verify` verifies the module in full; the honest base too.
#[test]
fn test_per_constant_verify_family_sorted_through_an_imported_definition() {
    let wanted = value_bearing("ReplayHonestSortDef");
    for name in ["hsd_use", "hsd_bit", "hsd_bit_mk"] {
        assert!(wanted.contains(name), "the fixture must declare `{name}`");
    }
    let r = per_constant("ReplayHonestSortDef", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(r.kernel_verified, wanted.len(), "{:?}", r.errors);
    let r = per_constant("ReplayHonestSortDefBase", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(
        r.kernel_verified,
        value_bearing("ReplayHonestSortDefBase").len()
    );
}

/// The lanes that load whole modules agree: every `stamp-verified` mode
/// stamps every value-bearing declaration of the module.
#[test]
fn test_stamp_verified_all_modes_family_sorted_through_an_imported_definition() {
    let wanted = value_bearing("ReplayHonestSortDef");
    for mode in STAMP_MODES {
        let stamped = stamp(&["ReplayHonestSortDef"], mode);
        let missing: Vec<&String> = wanted.difference(&stamped).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?}: not stamped {missing:?}"
        );
    }
}
