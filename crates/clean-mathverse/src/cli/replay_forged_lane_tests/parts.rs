// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The R113 review's findings P1, P2, P3 and P7 through the mathverse re-check
//! lanes: an artifact whose parts disagree, and a misplaced family in a
//! DEPENDENCY rather than in the module checked. Every lane must read a module
//! the way pinned `leanchecker` does and refuse an artifact whose parts tell a
//! different story (`clean_olean::read_artifact`, R113).
//!
//! Fixtures (`replay_forged` README, pinned `leanchecker` v4.30.0-rc2):
//!
//! - `ReplayMisplacedOlean` (P7): `SX`/`SX.mk`/`SX.rec` in `.olean` and
//!   `.olean.server` only; `sx_use` in every part. rc 1, `unknown constant 'SX'`.
//! - `ReplayPartsValDis` (P2): `pv_X := 1` in `.olean`/`.olean.server`, `pv_X := 0`
//!   in `.olean.private`; `pv_u : pv_X = 1`. rc 1, `declaration type mismatch, 'pv_u'`.
//! - `ReplayPartsValDepUser` (P2, dependency form) over `ReplayPartsValDep`. rc 1 on
//!   the user (`pd_t`); rc 0 on the dependency alone.
//! - `ReplayPartsImpT` (P3) over `ReplayPartsImpD`, whose `.olean` imports
//!   `ReplayPartsImpF` (`pi_Y := 1`) and whose `.olean.private` imports
//!   `ReplayPartsImpE` (`pi_Y := 0`). rc 1 on `pi_t : pi_Y = 1`; rc 0 on
//!   `ReplayPartsImpD` alone.
//! - `ReplayMisplacedDepUser` (P1, honest content) over `ReplayMisplacedDep`, whose
//!   honest `MD` is in `.olean`/`.olean.server` only. rc 1, `unknown constant 'MD'`;
//!   rc 0 on the dependency alone.
//! - Control: `ReplayHonestDepUser` over `ReplayHonestDep` (`MD` in every part), rc 0.
//!
//! Measured before the fix (R113's red-at-base run): `per-constant-verify`
//! verified every user above, and the sequential `stamp-verified` modes stamped
//! `sx_use` and `pv_u`, because they read a module through its `.olean` merged
//! with its private part, with the `.olean` winning on a value and naming the
//! imports. The three dependency modules pass `leanchecker` on their own; Clean
//! refuses them because their parts disagree, which is stricter than Lean
//! (the safe direction).

use super::*;

/// Each forged run: the module checked, its user declaration, and the text the
/// refusal must carry (naming the declaration, or the module, the rule refuses).
const PARTS: [(&str, &str, &str); 5] = [
    ("ReplayMisplacedOlean", "sx_use", "declares `SX`"),
    ("ReplayPartsValDis", "pv_u", "state `pv_X` differently"),
    ("ReplayPartsValDepUser", "pd_t", "state `pd_X` differently"),
    ("ReplayPartsImpT", "pi_t", "state its imports differently"),
    ("ReplayMisplacedDepUser", "md_use", "declares `MD`"),
];

#[test]
fn test_per_constant_verify_refuses_parts_that_disagree_and_misplaced_dependencies() {
    let problems: Vec<String> = PARTS
        .iter()
        .filter_map(|(module, _user, needle)| {
            refusal_problem(
                "per-constant-verify",
                module,
                try_per_constant(module, &[]),
                needle,
            )
        })
        .collect();
    assert_no_problems(&problems);
    let r = per_constant("ReplayHonestDepUser", &[]);
    assert_eq!(
        (r.kernel_verified, r.failed),
        (1, 0),
        "the honest control verifies `md_use`: {:?}",
        r.errors
    );
}

#[test]
fn test_stamp_verified_all_modes_refuse_parts_that_disagree_and_misplaced_dependencies() {
    let mut problems: Vec<String> = Vec::new();
    for mode in STAMP_MODES {
        let lane = format!("stamp-verified {}", mode.unwrap_or("(default)"));
        problems.extend(PARTS.iter().filter_map(|(module, _user, needle)| {
            refusal_problem(&lane, module, try_stamp(&[module], mode), needle)
        }));
    }
    assert_no_problems(&problems);
    for mode in STAMP_MODES {
        let lane = format!("stamp-verified {}", mode.unwrap_or("(default)"));
        let stamped = stamp(&["ReplayHonestDepUser"], mode);
        assert!(
            stamped.contains("md_use"),
            "{lane} must stamp the honest `md_use`: {stamped:?}"
        );
    }
}

#[test]
fn test_sharded_verify_module_refuses_parts_that_disagree_and_misplaced_dependencies() {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    let problems: Vec<String> = PARTS
        .iter()
        .filter_map(|(module, _user, needle)| {
            refusal_problem(
                "sharded",
                module,
                crate::verify::sharded::verify_module(module, &search, 64)
                    .map(|r| r.kernel_verified_names),
                needle,
            )
        })
        .collect();
    assert_no_problems(&problems);
    let r = sharded("ReplayHonestDepUser", 64);
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
    assert!(
        r.kernel_verified_names.iter().any(|n| n == "md_use"),
        "{:?}",
        r.kernel_verified_names
    );
}
