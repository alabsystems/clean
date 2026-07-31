// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Network-backed integration test for `clean_mathverse::artifacts`.
//!
//! Exercises the real `gh release list` / `gh release view` shell-outs that
//! back `clean artifacts list` against the clean repo's release index.
//!
//! # Gating (offline-skip pattern)
//!
//! This legacy network test is opt-in via the `CLEAN_ARTIFACTS_NET_E2E` env
//! var, and additionally skips with an eprintln note when `gh` is absent or
//! unauthenticated. Normal CI never touches the network: it does not set the
//! env var, so the test returns early after one env lookup. Unlike explicit
//! qualification examples, an invocation that does not opt in is not evidence
//! that the network path passed.
//!
//! ```bash
//! CLEAN_ARTIFACTS_NET_E2E=1 cargo test --locked -p clean-mathverse \
//!     --test artifacts_network -- --nocapture
//! ```

use std::process::Command;

use clean_mathverse::artifacts::{list_release_assets, list_releases};
use clean_mathverse::release::DEFAULT_CLEAN_RELEASE_REPO;

/// Returns true when the `gh` CLI is installed and authenticated, i.e. the
/// network-backed assertions have a chance of being meaningful.
fn gh_is_usable() -> bool {
    Command::new("gh")
        .args(["auth", "status"])
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

#[test]
fn test_artifacts_list_releases_and_assets_against_real_repo() {
    // Gate 1: env opt-in — default test runs stay offline.
    if std::env::var("CLEAN_ARTIFACTS_NET_E2E").is_err() {
        eprintln!(
            "skip: CLEAN_ARTIFACTS_NET_E2E not set — artifacts network e2e is \
             opt-in (gh + network + auth). Set CLEAN_ARTIFACTS_NET_E2E=1 to run."
        );
        return;
    }
    // Gate 2: gh availability — opted in but offline/unauthenticated.
    if !gh_is_usable() {
        eprintln!(
            "skip: CLEAN_ARTIFACTS_NET_E2E set but `gh auth status` failed — \
             no usable gh CLI (offline or unauthenticated). Nothing to exercise."
        );
        return;
    }

    let releases = list_releases(DEFAULT_CLEAN_RELEASE_REPO, 30)
        .expect("gh release list must succeed against the clean repo");
    assert!(
        !releases.is_empty(),
        "expected at least one release on {DEFAULT_CLEAN_RELEASE_REPO}"
    );

    let mathverse_release = releases
        .iter()
        .find(|release| release.tag.starts_with("mathverse-v"))
        .expect("expected a mathverse-v* release in the index");
    eprintln!("e2e: inspecting assets of {}", mathverse_release.tag);

    let assets = list_release_assets(DEFAULT_CLEAN_RELEASE_REPO, &mathverse_release.tag)
        .expect("gh release view must succeed for the mathverse release");
    assert!(
        assets.iter().any(|asset| asset.name.ends_with(".tar.zst")),
        "expected a .tar.zst archive asset on {}; found: {:?}",
        mathverse_release.tag,
        assets.iter().map(|a| a.name.as_str()).collect::<Vec<_>>()
    );
}
