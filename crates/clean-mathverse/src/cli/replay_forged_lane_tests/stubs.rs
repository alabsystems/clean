// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R131 (`docs/DECISIONS.md`) through the mathverse re-check lanes: value-free
//! stubs that a later part completes, and the two placement entries no other
//! fixture reaches alone (`replay_forged` README, pinned `leanchecker`
//! v4.30.0-rc2):
//!
//! - `ReplayStubRefused`: `writeModule`'s public-theorem layout (axiom stubs in
//!   `.olean`/`.olean.server`, the theorems in `.olean.private`) over
//!   `sr_t : 1 = 1 := Eq.refl 2`, a value the kernel refuses, and
//!   `sr_u : 1 = 1 := sr_t`. rc 1. Before R131 the loader kept `sr_t` resident
//!   as an axiom and recorded the refusal only as a reason string, so the
//!   sharded worker counted `sr_t` as an accepted axiom and verified `sr_u`
//!   (review finding S1).
//! - `ReplayStubRefusedDepUser`: the same refused value in a dependency
//!   (`srd_t`). The default mode trusts the import (rc 0) and `--fresh` refuses
//!   it (rc 1). `per-constant-verify` reads an import's types, as the default
//!   mode does; the lanes that load imports through the `.olean` loader refuse
//!   it, as `--fresh` does (stricter than the default mode, the safe direction).
//! - `ReplayStubPlainDepUser`, `ReplayStubPlainPrivDepUser`: a non-module
//!   dependency whose companion completes its `.olean`'s axiom stub (S2); rc 1.
//! - `ReplayStubPlainTgt`: that shape as the module checked (S3); default rc 1.
//! - `ReplayMisplacedOleanOnlyDepUser`, `ReplayMisplacedPrivPlainDepUser`: a
//!   family only the rule's `.olean` entry (a `module`) or `.olean.private`
//!   entry (not a `module`) refuses (S5); rc 1, `unknown constant`.
//! - Controls: `ReplayStubHonest`, `ReplayStubPlainHonestUser`, rc 0.

use super::*;

/// Each run every lane refuses, and the text the refusal carries.
const STUBS: [(&str, &str); 5] = [
    ("ReplayStubPlainDepUser", "state `spd_X` differently"),
    ("ReplayStubPlainPrivDepUser", "state `sppd_X` differently"),
    ("ReplayStubPlainTgt", "state `spt_f` differently"),
    (
        "ReplayMisplacedOleanOnlyDepUser",
        "`ReplayMisplacedOleanOnlyDep`'s `.olean` declares `MO`",
    ),
    (
        "ReplayMisplacedPrivPlainDepUser",
        "`ReplayMisplacedPrivPlainDep`'s `.olean.private` declares `MP`",
    ),
];

/// The dependency whose stub completion the kernel refuses, refused by every
/// lane that loads imports through the `.olean` loader.
const REFUSED_DEP: (&str, &str) = (
    "ReplayStubRefusedDepUser",
    "completes the value-free `srd_t` with a value the kernel refuses",
);

fn search() -> Vec<PathBuf> {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    search
}

#[test]
fn test_sharded_verify_module_refuses_a_refused_stub_completion_by_name() {
    let r = sharded("ReplayStubRefused", 64);
    assert_eq!(
        (
            r.counts.kernel_verified,
            r.counts.axiom_accepted,
            r.counts.failed
        ),
        (0, 0, 2),
        "`sr_t` is refused, never an accepted axiom, and `sr_u` with it: {:?}",
        r.failures
    );
    let reason = |name: &str| {
        r.failures
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, m)| m.clone())
            .unwrap_or_else(|| panic!("`{name}` must be a named failure: {:?}", r.failures))
    };
    let sr_t = reason("sr_t");
    assert!(
        sr_t.contains("Type check error in declaration sr_t"),
        "`sr_t` must carry the kernel's refusal: {sr_t}"
    );
    let sr_u = reason("sr_u");
    assert!(
        sr_u.contains("depends on `sr_t`"),
        "`sr_u` must be refused for its use of `sr_t`: {sr_u}"
    );
    let honest = sharded("ReplayStubHonest", 64);
    assert_eq!(
        (honest.counts.kernel_verified, honest.counts.failed),
        (2, 0),
        "{:?}",
        honest.failures
    );
}

#[test]
fn test_sharded_verify_module_refuses_stub_shapes_lean_does_not_read() {
    let problems: Vec<String> = STUBS
        .iter()
        .chain(std::iter::once(&REFUSED_DEP))
        .filter_map(|(module, needle)| {
            refusal_problem(
                "sharded",
                module,
                crate::verify::sharded::verify_module(module, &search(), 64)
                    .map(|r| r.kernel_verified_names),
                needle,
            )
        })
        .collect();
    assert_no_problems(&problems);
    let r = sharded("ReplayStubPlainHonestUser", 64);
    assert_eq!(
        (r.counts.kernel_verified, r.counts.failed),
        (1, 0),
        "{:?}",
        r.failures
    );
}

#[test]
fn test_per_constant_verify_refuses_stub_shapes_lean_does_not_read() {
    let problems: Vec<String> = STUBS
        .iter()
        .filter_map(|(module, needle)| {
            refusal_problem(
                "per-constant-verify",
                module,
                try_per_constant(module, &[]),
                needle,
            )
        })
        .collect();
    assert_no_problems(&problems);
    // The module's own refused value: checked from the private part, refused,
    // and its user never verified.
    let r = per_constant("ReplayStubRefused", &[]);
    assert_eq!(r.kernel_verified, 0, "{:?}", r.errors);
    assert!(
        r.errors.contains_key("sr_t"),
        "`sr_t` must be refused: {:?}",
        r.errors
    );
    // An import's refused value: its type is trusted, as `leanchecker`'s default
    // mode trusts it (rc 0).
    let dep = per_constant(REFUSED_DEP.0, &[]);
    assert_eq!(
        (dep.kernel_verified, dep.failed),
        (1, 0),
        "{:?}",
        dep.errors
    );
    for (module, verified) in [("ReplayStubHonest", 2), ("ReplayStubPlainHonestUser", 1)] {
        let r = per_constant(module, &[]);
        assert_eq!(
            (r.kernel_verified, r.failed),
            (verified, 0),
            "{module}: {:?}",
            r.errors
        );
    }
}

#[test]
fn test_stamp_verified_all_modes_refuse_stub_shapes_lean_does_not_read() {
    let mut problems: Vec<String> = Vec::new();
    for mode in STAMP_MODES {
        let lane = format!("stamp-verified {}", mode.unwrap_or("(default)"));
        problems.extend(
            STUBS
                .iter()
                .chain(std::iter::once(&REFUSED_DEP))
                .filter_map(|(module, needle)| {
                    refusal_problem(&lane, module, try_stamp(&[module], mode), needle)
                }),
        );
        // The module's own refused value: refused by name, or left unstamped.
        match try_stamp(&["ReplayStubRefused"], mode) {
            Ok(stamped) => {
                if stamped.contains("sr_t") || stamped.contains("sr_u") {
                    problems.push(format!("{lane} stamped `sr_t`/`sr_u`: {stamped:?}"));
                }
            }
            Err(e) => {
                let message = e.to_string();
                if !message.contains("`sr_t`") {
                    problems.push(format!("{lane} refused without `sr_t`: {message}"));
                }
            }
        }
        for (module, names) in [
            ("ReplayStubHonest", &["sh_t", "sh_u"][..]),
            ("ReplayStubPlainHonestUser", &["sph_t"][..]),
        ] {
            match try_stamp(&[module], mode) {
                Ok(stamped) if names.iter().all(|n| stamped.contains(*n)) => {}
                other => problems.push(format!(
                    "{lane} must stamp {names:?} of {module}: {other:?}"
                )),
            }
        }
    }
    assert_no_problems(&problems);
}
