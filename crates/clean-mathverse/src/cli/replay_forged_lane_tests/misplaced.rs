// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hole B1 (`docs/DECISIONS.md` R113) through the mathverse re-check lanes: a
//! declaration placed where `lean` never reads it. `ReplayMisplacedServer`
//! keeps the honest family `SO`/`SO.mk`/`SO.rec` in its `.olean.server` alone
//! and a theorem `so_use : SO.mk 0 = SO.mk 0` in the part `lean` reads;
//! `ReplayMisplacedServerPlain` is the same in a non-module artifact. Pinned
//! `leanchecker` refuses each (`unknown constant 'SO'` / `'SOP'`), and admits
//! the honest control `ReplayHonestServerParts` (every part holds `SH`).
//!
//! Measured 2026-10-22 with a release `clean` before the fix: `stamp-verified
//! --parallel` STAMPED `so_use` (its base loaded the `.olean.server`, so `SO`
//! was resident, while its shard rows came from the `.olean` plus the
//! `.olean.private` root, where `SO` is absent, so `SO` was never a replay row
//! and `so_use` was checked against a resident family `leanchecker` cannot
//! see). The `.olean` loader now refuses the artifact by the misplaced name.

use super::*;

const MISPLACED: [(&str, &str, &str); 2] = [
    ("ReplayMisplacedServer", "so_use", "SO"),
    ("ReplayMisplacedServerPlain", "sop_use", "SOP"),
];

#[test]
fn test_per_constant_verify_refuses_a_misplaced_declaration() {
    // The lane reads the target through the artifact reader, which refuses
    // the whole run by the misplaced name before any constant is checked.
    for (module, _user, needle) in MISPLACED {
        match try_per_constant(module, &[]) {
            Err(MathverseCliError::StampImportRefused {
                module: refused,
                names,
                reason,
            }) => {
                assert_eq!(refused, module, "{module}: {reason}");
                assert_eq!(names, vec![needle.to_owned()], "{module}: {reason}");
                assert!(
                    reason.contains(&format!("`.olean.server` declares `{needle}`")),
                    "{module}: refused without naming the misplaced `{needle}`: {reason}"
                );
            }
            other => panic!("per-constant-verify on {module} must refuse the run: {other:?}"),
        }
    }
    // Honest control: every part holds `SH`, so the lane verifies `sh_use`.
    let r = per_constant("ReplayHonestServerParts", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert!(
        r.kernel_verified >= 1,
        "the honest control must verify at least `sh_use`: {:?}",
        r.errors
    );
}

#[test]
fn test_stamp_verified_all_modes_refuse_a_misplaced_declaration() {
    for (module, user, needle) in MISPLACED {
        for mode in STAMP_MODES {
            let lane = mode.unwrap_or("(default)");
            match try_stamp(&[module], mode) {
                Ok(stamped) => assert!(
                    !stamped.contains(user),
                    "stamp-verified {lane} on {module} stamped `{user}`: {stamped:?}"
                ),
                // `--parallel` loads the target into its base, so the loader's
                // refusal surfaces as a whole-run refusal naming the misplaced
                // family.
                Err(MathverseCliError::StampImportRefused { names, .. }) => assert!(
                    names.iter().any(|n| n.contains(needle)),
                    "stamp-verified {lane} on {module}: refused at import without `{needle}`: {names:?}"
                ),
                Err(e) => panic!("stamp-verified {lane} on {module}: {e}"),
            }
        }
    }
    // Honest control stamps `sh_use` in every mode.
    for mode in STAMP_MODES {
        let stamped = stamp(&["ReplayHonestServerParts"], mode);
        assert!(
            stamped.contains("sh_use"),
            "stamp-verified {mode:?} must stamp the honest `sh_use`: {stamped:?}"
        );
    }
}

#[test]
fn test_sharded_verify_module_refuses_a_misplaced_declaration() {
    for (module, _user, needle) in MISPLACED {
        let mut search = vec![fixtures()];
        search.extend(clean_olean::default_search_paths());
        match crate::verify::sharded::verify_module(module, &search, 64) {
            Err(crate::verify::sharded::ShardedVerifyError::ImportRefused { names, .. }) => {
                assert!(
                    names.iter().any(|n| n.contains(needle)),
                    "{module}: refused at import without `{needle}`: {names:?}"
                );
            }
            Err(e) => panic!("sharded verify {module}: {e}"),
            Ok(r) => panic!(
                "sharded verify {module} was not refused: verified {:?}",
                r.kernel_verified_names
            ),
        }
    }
    let r = sharded("ReplayHonestServerParts", 64);
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
}
