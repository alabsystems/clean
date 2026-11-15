// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R131 (`docs/DECISIONS.md`) through the `.olean` loader and verify-batch:
//! value-free stubs that a later part completes.
//!
//! Lean's `writeModule` writes every public theorem of a `module` to its
//! `.olean` (and `.olean.server`) as an axiom of its type, and the theorem in
//! its `.olean.private`, the part an importer that is not a `module` reads. The
//! loader completes the stub through the kernel's checked upgrade. Fixtures
//! (family README, pinned `leanchecker` v4.30.0-rc2):
//!
//! - `ReplayStubRefused`: that layout over `sr_t : 1 = 1 := Eq.refl 2`, a value
//!   the kernel refuses, and `sr_u : 1 = 1 := sr_t`. rc 1 (`sr_t`, declaration
//!   type mismatch). Before R131 the loader kept the stub resident as an axiom
//!   and recorded the refusal only as a skipped constant's reason (review
//!   finding S1), so verify-batch passed both declarations.
//! - `ReplayStubRefusedDepUser` over `ReplayStubRefusedDep` (the same refused
//!   value, `srd_t`, in a dependency): the default mode trusts the import
//!   (rc 0), `--fresh` refuses `srd_t` (rc 1). Clean's import refuses it, as
//!   `--fresh` does: stricter than the default mode, the safe direction.
//! - `ReplayStubPlainDepUser` / `ReplayStubPlainPrivDepUser`: NOT `module`s; the
//!   dependency's `.olean` holds `axiom spd_X : Nat` and its `.olean.server` (or
//!   a `.olean.private` with no server part) `def spd_X := 1`. Every importer
//!   reads a non-module artifact's `.olean`, so the user `spd_t : spd_X = 1` is
//!   rc 1. Before R131 the loader completed the stub from the companion (S2).
//! - `ReplayStubPlainTgt`: the same shape as the module checked (S3): the
//!   default mode replays the companion's ill-typed `spt_f` (rc 1), an importer
//!   reads the `.olean`'s axiom (`--fresh` rc 0).
//! - Controls: `ReplayStubHonest` (a `module` in the stub layout over values the
//!   kernel admits) and `ReplayStubPlainHonestUser` (a non-module companion that
//!   restates its `.olean`), rc 0.

use super::*;
use clean_olean::{read_artifact, ArtifactDepth, ImportError};

/// The loader's refusal of a stub completion the kernel refuses (R131).
const COMPLETION_REFUSED: &str = "with a value the kernel refuses";

#[test]
fn test_loader_refuses_an_artifact_whose_stub_completion_the_kernel_refuses() {
    for (module, name) in [
        ("ReplayStubRefused", "sr_t"),
        ("ReplayStubRefusedDepUser", "srd_t"),
    ] {
        let error = match try_load(module) {
            Ok(_) => panic!("{module}: a refused stub completion must refuse the import"),
            Err(error) => error,
        };
        assert!(
            error.contains(COMPLETION_REFUSED) && error.contains(&format!("`{name}`")),
            "{module}: the refusal must name `{name}`'s refused completion: {error}"
        );
    }
    // Control: the same layout over values the kernel admits.
    let targets = declared("ReplayStubHonest");
    assert_eq!(targets, names(&["sh_t", "sh_u"]));
    for (lane, outcome) in lanes("ReplayStubHonest", &targets) {
        assert_eq!((outcome.0, outcome.1), (2, 0), "{lane}: {:?}", outcome.2);
    }
}

/// `clean olean verify-batch --full-validation` (one environment, module after
/// module): the module whose stub completion the kernel refuses is refused at
/// its load, by name, and nothing of it is counted as verified. Before R131 its
/// load succeeded, `sr_t` was checked as the axiom it was left as, and both
/// declarations passed.
#[test]
fn test_verify_batch_in_run_refuses_a_refused_stub_completion() {
    let mut run = InRun::new();
    let refused = run.run("ReplayStubRefused", false);
    assert!(
        !refused.load_ok,
        "the load must be refused, not checked: {refused:?}"
    );
    let error = refused.load_error.as_deref().unwrap_or_default();
    assert!(
        error.contains(COMPLETION_REFUSED) && error.contains("`sr_t`"),
        "{error}"
    );
    assert_eq!((refused.tc_pass, refused.tc_fail), (0, 0), "{refused:?}");
    let honest = run.run("ReplayStubHonest", false);
    assert!(honest.load_ok, "{honest:?}");
    assert_eq!(
        (honest.tc_pass, honest.tc_fail),
        (2, 0),
        "{:?}",
        honest.tc_errors
    );
}

/// S2 and S3: a non-module artifact's companion may only restate its `.olean`.
/// The rule refuses each such artifact by the declaration, in the reader and in
/// the loader, so no loader lane gives `spd_X` the companion's definition.
#[test]
fn test_loader_refuses_a_non_module_companion_that_completes_a_stub() {
    for (module, artifact, name) in [
        ("ReplayStubPlainDepUser", "ReplayStubPlainDep", "spd_X"),
        (
            "ReplayStubPlainPrivDepUser",
            "ReplayStubPlainPrivDep",
            "sppd_X",
        ),
        ("ReplayStubPlainTgt", "ReplayStubPlainTgt", "spt_f"),
    ] {
        let needle = format!("the parts of `{artifact}` state `{name}` differently");
        let error = match try_load(module) {
            Ok(_) => panic!("{module}: the import must be refused"),
            Err(error) => error,
        };
        assert!(error.contains(&needle), "{module}: {error}");
        let path = compiled_fixture_dir(FAMILY).join(format!("{artifact}.olean"));
        match read_artifact(artifact, &path, ArtifactDepth::Records) {
            Err(ImportError::PartsDisagree {
                name: refused,
                module: label,
            }) => assert_eq!((refused.as_str(), label.as_str()), (name, artifact)),
            other => panic!("{artifact}: the reader must refuse `{name}`: {other:?}"),
        }
    }
    // Controls: a non-module companion that restates its `.olean`, and a
    // `module`'s stub layout, which the rule admits.
    let dir = compiled_fixture_dir(FAMILY);
    read_artifact(
        "ReplayStubPlainHonest",
        &dir.join("ReplayStubPlainHonest.olean"),
        ArtifactDepth::Records,
    )
    .expect("a non-module companion that restates its `.olean` is admitted");
    read_artifact(
        "ReplayStubHonest",
        &dir.join("ReplayStubHonest.olean"),
        ArtifactDepth::Records,
    )
    .expect("a `module`'s value-free stubs completed by its private part are admitted");
    let targets = declared("ReplayStubPlainHonestUser");
    for (lane, outcome) in lanes("ReplayStubPlainHonestUser", &targets) {
        assert_eq!((outcome.0, outcome.1), (1, 0), "{lane}: {:?}", outcome.2);
    }
}

/// The default load is an import trusted as Lean's importer trusts it — the
/// elaborator's, over whatever environment it supplies: it records a refused
/// completion of an artifact's own stub (`LoadSummary::refused_completions`)
/// and keeps the stub; only a re-check lane's policy refuses the import. Over
/// Clean's import-mode prelude the kernel's verdict on Lean's own values is not
/// Lean's: `Init.GetElem`'s `Array.instLawfulGetElemNatLtSize` is refused there
/// and admitted over Lean's replay environment (measured 2026-10-23, R131).
#[test]
fn test_a_trusted_import_records_a_refused_stub_completion() {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    let summaries = load_module_with_deps_shared_with_policy(
        &mut env,
        "ReplayStubRefused",
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .expect("a trusted import records the refusal");
    let refused: Vec<String> = summaries
        .iter()
        .flat_map(|s| s.refused_completions.iter().map(|(n, _)| n.to_string()))
        .collect();
    assert_eq!(refused, vec!["sr_t".to_string()], "{summaries:?}");
}
