// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hole R112 through the mathverse re-check lanes: a stored inductive block
//! the replay never rebuilt (`ReplayForgedAllGhost`, `ReplayForgedAllOther`:
//! a negative `Prop` family whose stored `all` names no block containing it,
//! with a proof of `False`), and a stored or regenerated `isRec` that is not
//! Lean's (`ReplayForgedIsRec`, `ReplayForgedMutualEta`), with the honest
//! control `ReplayHonestIndFlags`. Pinned `leanchecker` refuses every
//! forgery and accepts the control (family README). Split from the parent
//! module to keep it under the size ratchet.
//!
//! Measured 2026-10-22 with a release `clean` before the fix:
//! `per-constant-verify` returned `kernel_verified 1` for
//! `forged_all_ghost_false : False`, `forged_all_other_false : False` and
//! `forged_isrec_eta`; `stamp-verified --parallel` stamped all three; the
//! sequential modes stamped the forged `FIR` block and `forged_hma_eta` (their
//! regenerated `HMA` was non-recursive per type).

use super::*;

/// Each forged module, its forged declarations (the value-bearing user
/// last), and the text its refusal must carry: for a block member, the block
/// replay's own reason; for the user, the same reason through its dependency
/// (`DependsOnRefused` carries it) or, for `forged_hma_eta`, the kernel's.
struct Forged {
    module: &'static str,
    members: &'static [&'static str],
    user: &'static str,
    member_needle: &'static str,
    user_needles: &'static [&'static str],
}

const FORGED: [Forged; 4] = [
    Forged {
        module: "ReplayForgedAllGhost",
        members: &["FAG", "FAG.mk"],
        user: "forged_all_ghost_false",
        member_needle: "No such",
        user_needles: &["No such", "FAG"],
    },
    Forged {
        module: "ReplayForgedAllOther",
        members: &["FAO", "FAO.mk"],
        user: "forged_all_other_false",
        member_needle: "No such",
        user_needles: &["No such", "FAO"],
    },
    Forged {
        module: "ReplayForgedIsRec",
        members: &["FIR", "FIR.mk", "FIR.rec"],
        user: "forged_isrec_eta",
        member_needle: "recursive flag (isRec)",
        user_needles: &["recursive flag (isRec)", "FIR"],
    },
    Forged {
        module: "ReplayForgedMutualEta",
        members: &[],
        user: "forged_hma_eta",
        member_needle: "",
        user_needles: &["TypeMismatch"],
    },
];

/// The honest block beside `ReplayForgedAllOther`'s forgery, which every lane
/// admits.
const ALL_OTHER_HONEST: [&str; 3] = ["FAH", "FAH.a", "FAH.rec"];

/// B7 (R113): each forged module has exactly one value-bearing target, its
/// user, refused for the block replay's reason, never for another one.
#[test]
fn test_per_constant_verify_block_coverage_and_flags_follow_lean() {
    for f in FORGED {
        let r = per_constant(f.module, &[]);
        assert_eq!(
            (r.kernel_verified, r.failed),
            (0, 1),
            "{}: targets {:?}, errors {:?}",
            f.module,
            r.targets,
            r.errors
        );
        let errs = |n: &str| r.errors.get(n).cloned();
        for needle in f.user_needles {
            assert_refused("pcv", &errs, f.user, needle);
        }
    }
    let r = per_constant("ReplayHonestIndFlags", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(
        r.kernel_verified,
        value_bearing("ReplayHonestIndFlags").len()
    );
}

#[test]
fn test_stamp_verified_all_modes_block_coverage_and_flags_follow_lean() {
    for mode in STAMP_MODES {
        for f in FORGED {
            let stamped = stamp(&[f.module], mode);
            for name in f.members.iter().chain([&f.user]) {
                assert!(
                    !stamped.contains(*name),
                    "stamp-verified {mode:?} on {} stamped `{name}`: {stamped:?}",
                    f.module
                );
            }
        }
        let wanted = value_bearing("ReplayHonestIndFlags");
        let stamped = stamp(&["ReplayHonestIndFlags"], mode);
        let missing: Vec<&String> = wanted.difference(&stamped).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?}: not stamped {missing:?}"
        );
    }
}

/// B7 (R113): every forged name is refused for the block replay's reason (or,
/// for `forged_hma_eta`, the kernel's), and the honest `FAH` block beside
/// `FAO` is not refused at all.
#[test]
fn test_sharded_verify_module_block_coverage_and_flags_follow_lean() {
    for f in FORGED {
        let r = sharded(f.module, 64);
        let reason = |name: &str| -> &str {
            r.failures
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, why)| why.as_str())
                .unwrap_or_else(|| {
                    panic!(
                        "{}: `{name}` not refused; failures {:?}",
                        f.module, r.failures
                    )
                })
        };
        for name in f.members.iter().chain([&f.user]) {
            assert!(
                !r.kernel_verified_names.iter().any(|n| n == name),
                "{}: `{name}` verified; failures {:?}",
                f.module,
                r.failures
            );
        }
        for member in f.members {
            let why = reason(member);
            assert!(
                why.contains(f.member_needle),
                "{}: `{member}` refused without `{}`: {why}",
                f.module,
                f.member_needle
            );
        }
        let why = reason(f.user);
        for needle in f.user_needles {
            assert!(
                why.contains(needle),
                "{}: `{}` refused without `{needle}`: {why}",
                f.module,
                f.user
            );
        }
        if f.module == "ReplayForgedAllOther" {
            for honest in ALL_OTHER_HONEST {
                assert!(
                    !r.failures.iter().any(|(n, _)| n == honest),
                    "the honest `{honest}` is refused; failures {:?}",
                    r.failures
                );
            }
        }
    }
    let r = sharded("ReplayHonestIndFlags", 64);
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
}
