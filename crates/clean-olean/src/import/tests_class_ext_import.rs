// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-olean `Lean.classExtension` decode + restore
//! (#olean-env-ext-restore, lane-B increment 2).
//!
//! Before the typed decoder, every `classExtension` entry in a real Lean
//! `.olean` was parsed name-only: the generic `(Name × DataValue)` heuristic
//! recovered the class name but left `outParams`/`outLevelParams` as an opaque
//! payload, so imported classes materialized (if at all) only as the
//! conclusion head of some imported instance, always with EMPTY out-params. A
//! class with no imported instance (e.g. `Membership` after `Init.Prelude`)
//! did not exist at all — `is_class` returned `false`.
//!
//! These tests pin the restored behavior against the pinned v4.30.0-rc2
//! toolchain oleans and skip (with a message) when that toolchain is absent.
//! The decode is layout-validated, so a different toolchain would degrade to
//! counted `undecoded_entries`, never wrong data.
//!
//! Ground truth: `Lean/Class.lean:14-32` (`ClassEntry`, `classExtension`),
//! audited in `docs/plans/OLEAN_ENV_EXT_AUDIT_2026-07-09.md` §3 (row
//! `Lean.classExtension`) and pinned byte-for-byte with the raw-object probe.

use super::{load_module_with_deps, parse_module};
use crate::module::{ParsedClassEntry, ParsedExtensionEntry, LEAN_CLASS_EXTENSION};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

/// The pinned toolchain whose `ClassEntry` layout the decoder targets.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

/// Locate the pinned v4.30.0-rc2 stdlib, or `None` to skip.
fn v4_30_lib_path() -> Option<std::path::PathBuf> {
    crate::pinned_lean_lib_path()
}

/// Decode the `Lean.classExtension` entries of a single `.olean` (relative path
/// under `lib/lean`, e.g. `"Init/Prelude.olean"`), or `None` to skip.
fn decode_class_entries(rel: &str) -> Option<(Vec<ParsedClassEntry>, usize)> {
    let lib = v4_30_lib_path()?;
    let bytes = std::fs::read(lib.join(rel)).ok()?;
    let module = parse_module(&bytes).unwrap_or_else(|e| panic!("{rel} should parse: {e}"));
    let ext = module
        .entries
        .iter()
        .find(|ext| ext.extension_name == LEAN_CLASS_EXTENSION)
        .unwrap_or_else(|| panic!("{rel} should carry a Lean.classExtension entry array"));
    let decoded = ext
        .entries
        .iter()
        .map(|entry| match entry {
            ParsedExtensionEntry::Class(c) => c.clone(),
            other => panic!("classExtension should decode every entry as Class, got {other:?}"),
        })
        .collect();
    Some((decoded, ext.undecoded_entries))
}

fn find_class<'a>(decoded: &'a [ParsedClassEntry], name: &str) -> &'a ParsedClassEntry {
    decoded
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("{name} should be a persisted classExtension entry"))
}

#[test]
fn test_class_ext_decoder_prelude_entries_fully_decoded() {
    let Some((decoded, undecoded)) = decode_class_entries("Init/Prelude.olean") else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    // v4.30.0-rc2 Init.Prelude persists 75 class declarations; stay tolerant to
    // patch-level drift but insist on FULL decode (loud contract: an
    // undecodable entry must be counted, and for the pinned layout there is
    // none).
    assert!(
        decoded.len() >= 50,
        "expected >= 50 decoded class entries in Init.Prelude, got {}",
        decoded.len()
    );
    assert_eq!(
        undecoded, 0,
        "the pinned v4.30 ClassEntry layout should decode every entry"
    );

    // Out-param classes — the whole point of the increment. Verified against
    // the raw-object probe on the pinned olean.
    assert_eq!(
        find_class(&decoded, "Membership").out_params,
        vec![0],
        "Membership's first param is an outParam"
    );
    assert_eq!(find_class(&decoded, "HAdd").out_params, vec![2]);
    assert_eq!(find_class(&decoded, "HSMul").out_params, vec![2]);
    assert_eq!(find_class(&decoded, "Trans").out_params, vec![5]);

    // A non-out-param class must decode to the EMPTY vector (not merely be
    // absent) — the decoder distinguishes "class with no out-params" from
    // "class not persisted".
    assert!(
        find_class(&decoded, "Functor").out_params.is_empty(),
        "Functor has no outParams"
    );
    assert!(find_class(&decoded, "Inhabited").out_params.is_empty());

    // outLevelParams decoded for fidelity (parked, not yet consumed).
    assert_eq!(find_class(&decoded, "HAdd").out_level_params, vec![2]);
    assert_eq!(find_class(&decoded, "Membership").out_level_params, vec![0]);
}

#[test]
fn test_class_ext_decoder_getelem_out_params() {
    // `GetElem` is the canonical multi-out-param class (`Lean/Class.lean`
    // docstring pins `outParams := #[2, 3]`); it lives in `Init/GetElem.olean`.
    let Some((decoded, undecoded)) = decode_class_entries("Init/GetElem.olean") else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    assert_eq!(undecoded, 0);
    assert_eq!(
        find_class(&decoded, "GetElem").out_params,
        vec![2, 3],
        "GetElem's `elem` and `dom` params are outParams (Class.lean docstring)"
    );
    assert_eq!(find_class(&decoded, "GetElem?").out_params, vec![2, 3]);
    assert_eq!(
        find_class(&decoded, "LawfulGetElem").out_params,
        vec![2, 3, 4]
    );
}

#[test]
fn test_imported_class_registered_with_real_out_params() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let mut env = Environment::new();
    let summaries = load_module_with_deps(&mut env, "Init.Prelude", &[lib])
        .expect("Init.Prelude should import");

    // Loud contract holds end-to-end: nothing undecoded, and no hand-registered
    // twin drifted from the real Lean classExtension (empty mismatch list).
    for summary in &summaries {
        assert_eq!(summary.extension_undecoded_entries, 0);
        assert!(
            summary.class_out_param_mismatches.is_empty(),
            "class out-param fidelity drift in {:?}: {:?}",
            summary.module_name,
            summary.class_out_param_mismatches
        );
    }

    // `HAdd` was registered with EMPTY out-params before this increment (the
    // heuristic / instance bridge fabricate `[]`); the classExtension decode
    // supplies the real position of the `γ` outParam.
    let hadd = env
        .get_class_info(&Name::interned("HAdd"))
        .expect("HAdd must be a registered class after importing Init.Prelude");
    assert_eq!(
        hadd.out_params,
        vec![2],
        "HAdd's outParam position must come from the decoded classExtension entry"
    );
}

#[test]
fn test_imported_instance_less_class_now_exists() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // `Membership` has NO instance in Init.Prelude, so the instance-conclusion
    // heuristic never saw its head and it did not exist as a class at all
    // (audit §2: `is_class(Membership)` was false). The classExtension bridge
    // registers it directly from its `ClassEntry`.
    let membership = Name::interned("Membership");
    assert!(
        env.is_class(&membership),
        "Membership must be a registered class from its classExtension entry, \
         even with no imported instance"
    );
    assert_eq!(
        env.get_class_info(&membership)
            .expect("class info present")
            .out_params,
        vec![0],
        "Membership's outParam position [0] must be restored"
    );
}
