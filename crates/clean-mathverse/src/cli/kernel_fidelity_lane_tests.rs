// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The mathverse `.olean` re-check lanes (`per-constant-verify`, the three
//! `stamp-verified` modes and the sharded worker) on places where Clean's
//! kernel disagrees, or disagreed, with pinned Lean v4.30.0-rc2 (fixture
//! family `replay_forged` in `crates/clean-olean`; verdicts in its README;
//! `docs/DECISIONS.md` R139-R141):
//!
//! - `ReplayHonestDepNested`, `ReplayHonestDepNestedDeep` (Lean: rc 0):
//!   blocks nested through a dependent container whose family argument is a
//!   lambda, once and through a recursive container (`Lean.Json`'s shape).
//!   Clean β-normalized the auxiliary types, regenerated `isReflexive := true`
//!   and redex-free recursors, and refused every block and user: a false
//!   refusal. Every lane must verify every value-bearing declaration.
//! - `ReplayForgedDepNestedRefl` (Lean: rc 0, it never reads the stored
//!   flag): `SGS` stored with `isReflexive := true`, refused by Clean's flag
//!   comparison (R112), and its user with it.
//! - `ReplayForgedPowCap` (Lean: the two forgeries `deep recursion`):
//!   `Nat.pow 1 16777217 = 1 := rfl` and `Nat.pow 0 16777217 = 0 := rfl`.
//! - Levels (R141's review items, closed by R150's Lean level algebra): the
//!   level forgeries Lean refuses (`ReplayForgedLevelJoin`'s `LJB`/`LJD`/`LJE`,
//!   `ReplayForgedLevelAssoc`'s `LJB2`/`LJS2`) are refused, and all of
//!   `ReplayHonestLevelAssoc` is verified. `ReplayForgedMutualLevel` stores no
//!   value-bearing declaration, so it is pinned in the `crates/clean-olean`
//!   lanes only.
//! - KNOWN GAPS, pinned so each fails loudly the day it closes: the over-cap
//!   `Nat.pow` under an outer operation (`ReplayForgedPowCapOuter`) and the
//!   shift Lean aborts on (`ReplayForgedShlCap`) are verified.
//!
//! It sits beside the `mathverse-replay-order` battery
//! (`replay_forged_lane_tests.rs`), not in it: that battery's mutation arms
//! pin its file. The harness below is the battery's, reduced to what these
//! tests call.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use clap::Parser;
use clean_kernel::env::ProofValueElision;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::test_support::compiled_fixture_dir;

use super::kv_cache::FingerprintMode;
use super::per_constant_load::{per_constant_verify, PerConstantResult};
use super::stamp_verified_dispatch::cmd_stamp_verified;
use super::{MathverseArgs, MathverseCommands};
use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

fn fixtures() -> PathBuf {
    compiled_fixture_dir("replay_forged")
}

fn per_constant(module: &str) -> PerConstantResult {
    let dir = fixtures();
    per_constant_verify(
        &dir.join(format!("{module}.olean")),
        &dir,
        &[],
        DEFAULT_HEARTBEAT_LIMIT,
        None,
        FingerprintMode::Metadata,
        false,
        false,
        true,
        ProofValueElision::None,
        64,
        None,
    )
    .unwrap_or_else(|e| panic!("per-constant-verify {module}: {e}"))
}

#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    Mathverse(MathverseArgs),
}

/// The three `stamp-verified` modes.
const STAMP_MODES: [Option<&str>; 3] = [None, Some("--single-pass"), Some("--parallel")];

fn path_str(p: &Path) -> &str {
    p.to_str().expect("utf-8 fixture path")
}

/// `clean mathverse stamp-verified <module>.olean [mode]`, as the CLI runs
/// it; the manifest's KernelVerified names.
fn stamp(module: &str, mode: Option<&str>) -> BTreeSet<String> {
    let dir = fixtures();
    let out = tempfile::tempdir().expect("tempdir");
    let manifest = out.path().join("kv-manifest.json");
    let mut argv: Vec<String> = vec!["clean".into(), "mathverse".into(), "stamp-verified".into()];
    argv.push(path_str(&dir.join(format!("{module}.olean"))).to_owned());
    for arg in [
        "--out-dir",
        path_str(out.path()),
        "--closure-root",
        path_str(&dir),
        "--manifest",
        path_str(&manifest),
        "--json",
    ] {
        argv.push(arg.to_owned());
    }
    if let Some(flag) = mode {
        argv.push(flag.to_owned());
    }
    let h = Harness::try_parse_from(&argv).expect("parse stamp-verified");
    let Top::Mathverse(args) = h.command;
    let MathverseCommands::StampVerified(s) = args.command else {
        panic!("expected stamp-verified");
    };
    cmd_stamp_verified(s).unwrap_or_else(|e| panic!("stamp-verified {module} {mode:?}: {e}"));
    let bytes = std::fs::read(&manifest).expect("manifest written");
    let m: KernelVerifiedManifest = serde_json::from_slice(&bytes).expect("manifest parses");
    m.accepted_names().iter().cloned().collect()
}

/// The sharded worker over one fixture module.
fn sharded(module: &str) -> crate::verify::sharded::ModuleVerifyResult {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    crate::verify::sharded::verify_module(module, &search, 64)
        .unwrap_or_else(|e| panic!("sharded verify {module}: {e}"))
}

/// Every value-bearing declaration a fixture module stores.
fn value_bearing(module: &str) -> BTreeSet<String> {
    let path = fixtures().join(format!("{module}.olean"));
    let parsed = clean_olean::parse_module_file(&path)
        .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    parsed
        .constants
        .iter()
        .filter(|c| {
            matches!(
                c.kind,
                clean_olean::ConstantKind::Definition
                    | clean_olean::ConstantKind::Theorem
                    | clean_olean::ConstantKind::Opaque
            )
        })
        .map(|c| c.name.clone())
        .collect()
}

fn set(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| (*s).to_owned()).collect()
}

/// Each module: the value-bearing declarations every lane must verify, and
/// those it must refuse with the reason's text.
struct Case {
    module: &'static str,
    verified: &'static [&'static str],
    refused: &'static [(&'static str, &'static str)],
}

/// The refusal R150 gives a stored level Lean's `mk_max`/`mk_imax` would
/// rebuild (`TypeError::LevelSharingDependent`).
const SHARING: &str = "LevelSharingDependent";

const CASES: [Case; 8] = [
    Case {
        module: "ReplayHonestDepNested",
        verified: &["honest_sgs_elim", "honest_sj_depth"],
        refused: &[],
    },
    Case {
        module: "ReplayForgedDepNestedRefl",
        verified: &[],
        refused: &[("forged_sgs_elim", "reflexive flag (isReflexive)")],
    },
    Case {
        module: "ReplayForgedPowCap",
        verified: &["pow_one_at_cap", "pow_small"],
        refused: &[
            ("pow_one_over_cap", "TypeMismatch"),
            ("pow_zero_over_cap", "TypeMismatch"),
        ],
    },
    Case {
        module: "ReplayHonestLevelAssoc",
        verified: &["P1", "B1", "LB"],
        refused: &[],
    },
    // Pinned Lean refuses `LJB`, `LJD`, `LJE`, `LJB2` and `LJS2`; so does
    // every lane since R150, `LJS2` by its fail-closed rule for a stored
    // level Lean's `mk_imax` would rebuild (`SHARING`).
    Case {
        module: "ReplayForgedLevelJoin",
        verified: &["LJC", "LJF"],
        refused: &[
            ("LJB", "TypeMismatch"),
            ("LJD", "TypeMismatch"),
            ("LJE", "TypeMismatch"),
        ],
    },
    Case {
        module: "ReplayForgedLevelAssoc",
        verified: &[],
        refused: &[("LJB2", "TypeMismatch"), ("LJS2", SHARING)],
    },
    // KNOWN GAPS: pinned Lean refuses every `*_over*` forgery and aborts on
    // `shl_cong`/`shl_cong64`.
    Case {
        module: "ReplayForgedPowCapOuter",
        verified: &[
            "mul_at_zero",
            "add_at_zero",
            "mul_over_zero",
            "add_over_zero",
            "sub_over_zero",
            "pow_over_exp0",
            "mul_over2_zero",
        ],
        refused: &[],
    },
    Case {
        module: "ReplayForgedShlCap",
        verified: &["shl_zero_base", "shl_cong_small", "shl_cong", "shl_cong64"],
        refused: &[],
    },
];

fn check_case_covers_module(case: &Case) {
    let mut all = set(case.verified);
    all.extend(case.refused.iter().map(|(n, _)| (*n).to_owned()));
    assert_eq!(all, value_bearing(case.module), "{}", case.module);
}

#[test]
fn test_per_constant_verify_kernel_fidelity_follows_lean() {
    for case in &CASES {
        check_case_covers_module(case);
        let r = per_constant(case.module);
        assert_eq!(
            (r.kernel_verified, r.failed),
            (case.verified.len(), case.refused.len()),
            "{}: {:?}",
            case.module,
            r.errors
        );
        for (name, needle) in case.refused {
            let why = r
                .errors
                .get(*name)
                .unwrap_or_else(|| panic!("{}: `{name}` not refused: {:?}", case.module, r.errors));
            assert!(why.contains(needle), "{}: `{name}`: {why}", case.module);
        }
    }
}

#[test]
fn test_stamp_verified_all_modes_kernel_fidelity_follows_lean() {
    for mode in STAMP_MODES {
        for case in &CASES {
            let stamped = stamp(case.module, mode);
            for name in case.verified {
                assert!(
                    stamped.contains(*name),
                    "stamp-verified {mode:?} on {}: `{name}` not stamped: {stamped:?}",
                    case.module
                );
            }
            for (name, _) in case.refused {
                assert!(
                    !stamped.contains(*name),
                    "stamp-verified {mode:?} on {}: `{name}` stamped",
                    case.module
                );
            }
        }
    }
}

#[test]
fn test_sharded_verify_module_kernel_fidelity_follows_lean() {
    for case in &CASES {
        let r = sharded(case.module);
        for name in case.verified {
            assert!(
                r.kernel_verified_names.iter().any(|n| n == name),
                "{}: `{name}` not verified; failures {:?}",
                case.module,
                r.failures
            );
        }
        for (name, needle) in case.refused {
            let why = r
                .failures
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, why)| why.as_str())
                .unwrap_or_else(|| {
                    panic!("{}: `{name}` not refused: {:?}", case.module, r.failures)
                });
            assert!(why.contains(needle), "{}: `{name}`: {why}", case.module);
        }
        if case.refused.is_empty() {
            assert_eq!(r.counts.failed, 0, "{}: {:?}", case.module, r.failures);
        }
    }
}

/// `ReplayHonestDepNestedDeep` (Lean: rc 0, all 80 constants): every lane
/// verifies every value-bearing declaration, `RJ`'s `below`/`brecOn`/
/// `sizeOf`/`noConfusion` machinery and both users among them.
#[test]
fn test_every_lane_verifies_the_recursive_dependent_container_block() {
    let module = "ReplayHonestDepNestedDeep";
    let all = value_bearing(module);
    for expected in [
        "honest_rj_obj",
        "honest_rj_ne",
        "RJ.brecOn",
        "RJ.noConfusion",
    ] {
        assert!(all.contains(expected), "{expected}: {all:?}");
    }
    let r = per_constant(module);
    assert_eq!(
        (r.kernel_verified, r.failed),
        (all.len(), 0),
        "{:?}",
        r.errors
    );
    for mode in STAMP_MODES {
        let stamped = stamp(module, mode);
        let missing: Vec<_> = all.difference(&stamped).collect();
        assert!(missing.is_empty(), "stamp-verified {mode:?}: {missing:?}");
    }
    let r = sharded(module);
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
    let missing: Vec<_> = all
        .iter()
        .filter(|n| !r.kernel_verified_names.iter().any(|v| v == *n))
        .collect();
    assert!(missing.is_empty(), "sharded: {missing:?}");
}
