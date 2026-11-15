// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe-level equality in Lean's kernel theory through the mathverse
//! re-check lanes (DECISIONS R150): `per-constant-verify`, every
//! `stamp-verified` mode and the sharded worker, each driven through the entry
//! point the CLI calls, as `replay_forged_lane_tests.rs` drives them. It is a
//! sibling of that battery, not a child, so the battery's pinned file is
//! untouched; the few helpers below are its own.
//!
//! `ReplayForgedLevelSubsumption` holds seven level equalities pinned Lean's
//! kernel refuses, each true at every assignment; `ReplayHonestLevelEquiv`
//! their twins, which it admits; `ReplayLevelSharing` an instantiation whose
//! Lean verdict depends on `.olean` object sharing (verdicts in the fixture
//! README). The `stamp-verified` lanes decode the closure through the mathverse
//! shard path (`shard_reconstruct`), which must keep each stored `max`/`imax`
//! node as Lean stored it. `ReplayForgedLevelReach` / `ReplayHonestLevelReach`
//! / `ReplayHonestLevelProj` carry the same instantiation through a
//! projection, a δ-unfolding, an ι-reduct and a recursor's structural `is_zero`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use clap::Parser;
use clean_kernel::env::ProofValueElision;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::test_support::compiled_fixture_dir;

use super::closure_load::build_closure_shards_for_target;
use super::kv_cache::FingerprintMode;
use super::per_constant_load::{per_constant_verify, PerConstantResult};
use super::stamp_verified_dispatch::cmd_stamp_verified;
use super::{MathverseArgs, MathverseCommands};
use crate::verify::kernel_verified_manifest::KernelVerifiedManifest;

const FORGED: [&str; 7] = [
    "fls_join",
    "fls_join_wf",
    "fls_imax_reflatten",
    "fls_decode_max",
    "fls_decode_imax",
    "fls_subst",
    "fls_infer_pi",
];

const SHARING: [&str; 2] = ["ls_same", "ls_sorted"];

/// The three `stamp-verified` modes: the merged sequential default, the
/// streaming `--single-pass`, and PARAGON's `--parallel`.
const STAMP_MODES: [Option<&str>; 3] = [None, Some("--single-pass"), Some("--parallel")];

fn fixtures() -> PathBuf {
    compiled_fixture_dir("replay_forged")
}

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| (*s).to_owned()).collect()
}

/// Fail when `lane` admitted any of `admitted`, naming each on its own line
/// first, so a demonstration arm can pin exactly which forgery got through.
fn assert_none_admitted<S: AsRef<str>>(lane: &str, admitted: &[S]) {
    for name in admitted {
        eprintln!("{lane} admitted forged `{}`", name.as_ref());
    }
    assert!(
        admitted.is_empty(),
        "{lane} admitted {} forgeries",
        admitted.len()
    );
}

fn is_sharing_refusal(why: &str) -> bool {
    why.contains("LevelSharingDependent") || why.contains("object sharing")
}

fn per_constant(module: &str) -> PerConstantResult {
    per_constant_with(module, None)
}

fn per_constant_with(module: &str, closure_shards: Option<&Path>) -> PerConstantResult {
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
        closure_shards,
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

fn path_str(p: &Path) -> &str {
    p.to_str().expect("utf-8 fixture path")
}

/// `clean mathverse stamp-verified <module>.olean [mode]`, as the CLI runs it;
/// the manifest's KernelVerified names.
fn stamp(module: &str, mode: Option<&str>) -> BTreeSet<String> {
    stamp_with(module, mode, None)
}

/// [`stamp`], serving the closure from `closure_shards` when given. The output
/// directory is nested in its own temporary directory, so the sibling default
/// cache (`<out>/../.clean-closure-shards`) is never a shared one.
fn stamp_with(module: &str, mode: Option<&str>, closure_shards: Option<&Path>) -> BTreeSet<String> {
    let dir = fixtures();
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("stamped");
    std::fs::create_dir_all(&out).expect("out dir");
    let manifest = out.join("kv-manifest.json");
    let olean = dir.join(format!("{module}.olean"));
    let mut argv: Vec<String> = vec!["clean".into(), "mathverse".into(), "stamp-verified".into()];
    for arg in [
        path_str(&olean),
        "--out-dir",
        path_str(&out),
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
    if let Some(shards) = closure_shards {
        argv.push("--closure-shards".to_owned());
        argv.push(path_str(shards).to_owned());
    } else {
        argv.push("--no-lazy-closure".to_owned());
    }
    let h = Harness::try_parse_from(&argv).expect("parse stamp-verified");
    let Top::Mathverse(args) = h.command;
    let MathverseCommands::StampVerified(s) = args.command else {
        panic!("expected stamp-verified");
    };
    cmd_stamp_verified(s).unwrap_or_else(|e| panic!("stamp-verified {module} {mode:?}: {e}"));
    let bytes = std::fs::read(&manifest).expect("manifest written");
    let m: KernelVerifiedManifest = serde_json::from_slice(&bytes).expect("manifest parses");
    m.kernel_verified_names.into_iter().collect()
}

fn sharded(module: &str) -> crate::verify::sharded::ModuleVerifyResult {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    crate::verify::sharded::verify_module(module, &search, 16)
        .unwrap_or_else(|e| panic!("sharded verify {module}: {e}"))
}

/// The module's definitions, theorems and opaques (what a lane verifies).
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

#[test]
fn test_per_constant_verify_level_equalities_follow_pinned_lean() {
    let r = per_constant("ReplayForgedLevelSubsumption");
    assert_eq!(
        value_bearing("ReplayForgedLevelSubsumption"),
        names(&FORGED)
    );
    let admitted: Vec<String> = names(&FORGED)
        .into_iter()
        .filter(|n| !r.errors.contains_key(n))
        .collect();
    assert_none_admitted("pcv", &admitted);
    let refused: BTreeSet<String> = r.errors.keys().cloned().collect();
    assert_eq!(refused, names(&FORGED), "{:?}", r.errors);
    assert_eq!(
        (r.kernel_verified, r.failed),
        (0, FORGED.len()),
        "{:?}",
        r.errors
    );

    let r = per_constant("ReplayHonestLevelEquiv");
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(
        r.kernel_verified,
        value_bearing("ReplayHonestLevelEquiv").len()
    );

    let r = per_constant("ReplayLevelSharing");
    for name in SHARING {
        let why = r
            .errors
            .get(name)
            .unwrap_or_else(|| panic!("pcv: `{name}` must be refused: {:?}", r.errors));
        assert!(is_sharing_refusal(why), "pcv: `{name}`: {why}");
    }
    assert_eq!(
        (r.kernel_verified, r.failed),
        (0, SHARING.len()),
        "{:?}",
        r.errors
    );
}

#[test]
fn test_stamp_verified_all_modes_level_equalities_follow_pinned_lean() {
    let honest = value_bearing("ReplayHonestLevelEquiv");
    for mode in STAMP_MODES {
        let stamped = stamp("ReplayForgedLevelSubsumption", mode);
        for name in FORGED {
            assert!(
                !stamped.contains(name),
                "stamp-verified {mode:?} stamped `{name}`: {stamped:?}"
            );
        }
        let stamped = stamp("ReplayLevelSharing", mode);
        for name in SHARING {
            assert!(
                !stamped.contains(name),
                "stamp-verified {mode:?} stamped `{name}`: {stamped:?}"
            );
        }
        let stamped = stamp("ReplayHonestLevelEquiv", mode);
        let missing: Vec<&String> = honest.difference(&stamped).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?}: not stamped {missing:?}"
        );
    }
}

#[test]
fn test_sharded_verify_module_level_equalities_follow_pinned_lean() {
    let r = sharded("ReplayForgedLevelSubsumption");
    let refused: BTreeSet<String> = r.failures.iter().map(|(n, _)| n.clone()).collect();
    assert_eq!(refused, names(&FORGED), "{:?}", r.failures);
    assert_eq!(r.counts.failed, FORGED.len(), "{:?}", r.failures);

    let r = sharded("ReplayHonestLevelEquiv");
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);

    let r = sharded("ReplayLevelSharing");
    for name in SHARING {
        let why = r
            .failures
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, why)| why.as_str())
            .unwrap_or_else(|| panic!("sharded: `{name}` must be refused: {:?}", r.failures));
        assert!(is_sharing_refusal(why), "sharded: `{name}`: {why}");
    }
}

/// The mathverse closure shards of `module`'s imports, built by the production
/// builder (`build-closure-shards`) into a fresh directory.
fn closure_shards(module: &str) -> tempfile::TempDir {
    let dir = fixtures();
    let shards = tempfile::tempdir().expect("tempdir");
    let (converted, skipped) =
        build_closure_shards_for_target(&dir.join(format!("{module}.olean")), &dir, shards.path())
            .unwrap_or_else(|e| panic!("build-closure-shards {module}: {e}"));
    assert!(
        converted > 0 && skipped == 0,
        "{module}: {converted} converted, {skipped} skipped"
    );
    shards
}

/// t4 and t9 across a module boundary, with the import served LAZILY from its
/// closure shard, so the imported levels come through `shard_reconstruct`:
/// pinned Lean refuses `fli_t4`/`fli_t9` (the stored levels of `hli_t4`/`hli_t9`
/// are not the declared ones) and admits `hliu_t4`/`hliu_t9`. A collapsing
/// reconstruction turns both verdicts around.
#[test]
fn test_per_constant_verify_lazy_closure_keeps_imported_levels() {
    let shards = closure_shards("ReplayForgedLevelImport");
    let r = per_constant_with("ReplayForgedLevelImport", Some(shards.path()));
    if r.lazy_shards_failed > 0 || r.lazy_served == 0 {
        // Named so a demonstration arm can pin this path as well as an
        // admitted forgery: both are the lazy lane mishandling the import.
        eprintln!(
            "lazy pcv: the import was not served from its shard ({} failed)",
            r.lazy_shards_failed
        );
    }
    assert!(
        r.lazy_served > 0 && r.lazy_shards_verified > 0 && r.lazy_shards_failed == 0,
        "the import must be served from its shard: served {}, verified {}, failed {}",
        r.lazy_served,
        r.lazy_shards_verified,
        r.lazy_shards_failed
    );
    let admitted: Vec<String> = names(&["fli_t4", "fli_t9"])
        .into_iter()
        .filter(|n| !r.errors.contains_key(n))
        .collect();
    assert_none_admitted("lazy pcv", &admitted);
    let refused: BTreeSet<String> = r.errors.keys().cloned().collect();
    assert_eq!(refused, names(&["fli_t4", "fli_t9"]), "{:?}", r.errors);
    assert_eq!(r.kernel_verified, 0, "{:?}", r.errors);

    let shards = closure_shards("ReplayHonestLevelImportUse");
    let r = per_constant_with("ReplayHonestLevelImportUse", Some(shards.path()));
    assert!(r.lazy_served > 0 && r.lazy_shards_failed == 0, "{r:?}");
    assert_eq!((r.kernel_verified, r.failed), (2, 0), "{:?}", r.errors);
}

/// The same pair through `stamp-verified --closure-shards`, sequential modes
/// (PARAGON's `--parallel` builds its own base from every target).
#[test]
fn test_stamp_verified_lazy_closure_keeps_imported_levels() {
    for mode in [None, Some("--single-pass")] {
        let shards = closure_shards("ReplayForgedLevelImport");
        let stamped = stamp_with("ReplayForgedLevelImport", mode, Some(shards.path()));
        for name in ["fli_t4", "fli_t9"] {
            assert!(
                !stamped.contains(name),
                "stamp-verified {mode:?} (lazy) stamped `{name}`: {stamped:?}"
            );
        }
        let shards = closure_shards("ReplayHonestLevelImportUse");
        let stamped = stamp_with("ReplayHonestLevelImportUse", mode, Some(shards.path()));
        let expected = value_bearing("ReplayHonestLevelImportUse");
        let missing: Vec<&String> = expected.iter().filter(|n| !stamped.contains(*n)).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?} (lazy): not stamped {missing:?}"
        );
    }
}

/// The cross-module pair on the eager lanes too.
#[test]
fn test_eager_lanes_refuse_cross_module_level_forgeries() {
    let r = per_constant("ReplayForgedLevelImport");
    let refused: BTreeSet<String> = r.errors.keys().cloned().collect();
    assert_eq!(refused, names(&["fli_t4", "fli_t9"]), "{:?}", r.errors);
    let r = per_constant("ReplayHonestLevelImportUse");
    assert_eq!((r.kernel_verified, r.failed), (2, 0), "{:?}", r.errors);
    let r = sharded("ReplayForgedLevelImport");
    let refused: BTreeSet<String> = r.failures.iter().map(|(n, _)| n.clone()).collect();
    assert_eq!(refused, names(&["fli_t4", "fli_t9"]), "{:?}", r.failures);
    for mode in STAMP_MODES {
        let stamped = stamp("ReplayForgedLevelImport", mode);
        assert!(
            !stamped.contains("fli_t4") && !stamped.contains("fli_t9"),
            "stamp-verified {mode:?}: {stamped:?}"
        );
    }
}

/// The two value forgeries of `ReplayForgedLevelReach`: a projection and a
/// δ-unfolding declared at the level a collapsing substitution builds.
const REACH_FORGED: [&str; 2] = ["fls_proj", "fls_delta"];

/// Whether `name` is one of `ReplayForgedLevelReach`'s forgeries: a value
/// forgery or a member of one of its three forged inductive blocks.
fn is_reach_forgery(name: &str) -> bool {
    name.starts_with("fls_")
        || ["flr_MA", "flr_MB", "flr_Fb", "flr_Z"]
            .iter()
            .any(|block| name == *block || name.starts_with(&format!("{block}.")))
}

/// The honest reach modules, each admitted in full by pinned Lean.
const REACH_HONEST: [&str; 2] = ["ReplayHonestLevelReach", "ReplayHonestLevelProj"];

#[test]
fn test_mathverse_lanes_follow_pinned_lean_on_projection_delta_iota_levels() {
    let r = per_constant("ReplayForgedLevelReach");
    let admitted: Vec<&str> = REACH_FORGED
        .into_iter()
        .filter(|n| !r.errors.contains_key(*n))
        .collect();
    assert_none_admitted("pcv", &admitted);
    let honest: Vec<&String> = r.errors.keys().filter(|n| !is_reach_forgery(n)).collect();
    assert!(
        honest.is_empty(),
        "pcv refused honest {honest:?}: {:?}",
        r.errors
    );
    let r = sharded("ReplayForgedLevelReach");
    let refused: BTreeSet<String> = r.failures.iter().map(|(n, _)| n.clone()).collect();
    let admitted: Vec<&str> = REACH_FORGED
        .into_iter()
        .filter(|n| !refused.contains(*n))
        .collect();
    assert_none_admitted("sharded", &admitted);
    let honest: Vec<&String> = refused.iter().filter(|n| !is_reach_forgery(n)).collect();
    assert!(
        honest.is_empty(),
        "sharded refused honest {honest:?}: {:?}",
        r.failures
    );
    for mode in STAMP_MODES {
        let stamped = stamp("ReplayForgedLevelReach", mode);
        let admitted: Vec<&str> = REACH_FORGED
            .into_iter()
            .filter(|n| stamped.contains(*n))
            .collect();
        assert_none_admitted(&format!("stamp-verified {mode:?}"), &admitted);
    }
    for module in REACH_HONEST {
        let r = per_constant(module);
        assert_eq!(
            (r.kernel_verified, r.failed),
            (value_bearing(module).len(), 0),
            "pcv refused honest {module}: {:?}",
            r.errors
        );
        let r = sharded(module);
        assert_eq!(
            r.counts.failed, 0,
            "sharded refused honest {module}: {:?}",
            r.failures
        );
        let expected = value_bearing(module);
        for mode in STAMP_MODES {
            let stamped = stamp(module, mode);
            let missing: Vec<&String> = expected.difference(&stamped).collect();
            assert!(
                missing.is_empty(),
                "stamp-verified {mode:?} did not stamp honest {missing:?} of {module}"
            );
        }
    }
}
