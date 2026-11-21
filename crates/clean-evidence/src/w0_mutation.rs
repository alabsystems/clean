// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Check the historical W0 comparator mutation receipt against its Git inputs.

mod git;
mod record;

use git::Snapshot;
use record::{sha256, Record};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::{fs, path::Path};

const RECEIPT: &str = "reports/evidence-ev2-w0-comparator-mutation-2026-11-18/receipt.json";
const BOARD: &str = "data/self_proof_scoreboard.json";
const COVERAGE: &str = "data/kcheck_coverage.json";
const COMPARATOR: &str = "crates/clean-cli/src/cmd_evidence/w0_scoreboard.rs";
const REPLAY: &str = "crates/clean/tests/w0_scoreboard_cli.rs";

// The selected build inputs v1 records in addition to the Git tree identity.
const SOURCE_FILES: &[&str] = &[
    ".cargo/config.toml",
    "Cargo.lock",
    "Cargo.toml",
    "crates/clean-cli/Cargo.toml",
    "crates/clean-cli/src/cli_args.rs",
    "crates/clean-cli/src/cmd_evidence.rs",
    "crates/clean-cli/src/cmd_evidence/clean_p3.rs",
    "crates/clean-cli/src/cmd_evidence/k3_receipt.rs",
    COMPARATOR,
    "crates/clean/Cargo.toml",
    "crates/clean/src/bin/clean.rs",
    REPLAY,
    "rust-toolchain.toml",
    "scripts/cargo_test_nonvacuous.sh",
    "scripts/rust_frontend.sh",
];

// The replay also copies the pinned K3 sources and the tracked C3 Lean files.
const FIXED_FIXTURES: &[&str] = &[
    BOARD,
    COVERAGE,
    "data/kcheck_coverage/prelude_roots.advice.bin",
    "data/kcheck_coverage/prelude_roots.transcript.txt",
    "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/prelude_roots.ndjson.gz",
    "reports/self-proof-p3-2026-11-12/patched_kernel_control.json",
    "reports/self-proof-p3-2026-11-12/patched_kernel_control_trust.json",
    "reports/self-proof-elab/baseline.json",
    "data/cic_l_rule_inventory.json",
    "data/kcheck_island_gaps.json",
];

#[derive(Debug, thiserror::Error)]
pub(super) enum CheckError {
    #[error("{0}")]
    Invalid(String),
    #[error("{0}")]
    Unavailable(String),
}

pub(super) struct Checked {
    pub(super) source: String,
    pub(super) fixtures: usize,
}

#[derive(Deserialize)]
struct CoverageSources {
    sources: BTreeMap<String, String>,
}

fn require_inventory(
    name: &str,
    pinned: &BTreeMap<String, String>,
    required: &BTreeSet<String>,
) -> Result<(), CheckError> {
    if let Some(path) = required.iter().find(|path| !pinned.contains_key(*path)) {
        return Err(CheckError::Invalid(format!("{name} is missing {path}")));
    }
    if let Some(path) = pinned.keys().find(|path| !required.contains(*path)) {
        return Err(CheckError::Invalid(format!("{name} has unexpected {path}")));
    }
    Ok(())
}

fn verify_pins(snapshot: &Snapshot, pins: &BTreeMap<String, String>) -> Result<(), CheckError> {
    for (path, expected) in pins {
        let seen = sha256(&snapshot.read(path)?);
        if seen != *expected {
            return Err(CheckError::Invalid(format!(
                "SHA-256 mismatch for {path} in the pinned Git tree. Expected {expected}, observed {seen}"
            )));
        }
    }
    Ok(())
}

pub(super) fn check(root: &Path, receipt: Option<&Path>) -> Result<Checked, CheckError> {
    let path = root.join(receipt.unwrap_or_else(|| Path::new(RECEIPT)));
    let bytes = fs::read(&path).map_err(|error| {
        CheckError::Unavailable(format!("cannot read receipt {}: {error}", path.display()))
    })?;
    let record = Record::parse(&bytes)?;
    require_inventory(
        "source inventory",
        &record.source_files_sha256,
        &SOURCE_FILES.iter().map(|name| (*name).to_owned()).collect(),
    )?;

    let snapshot = Snapshot::open(root, &record.source_commit, &record.source_tree)?;
    let coverage: CoverageSources = serde_json::from_slice(&snapshot.read(COVERAGE)?)
        .map_err(|error| CheckError::Invalid(format!("pinned {COVERAGE}: {error}")))?;
    let mut fixtures = snapshot.checker_sources()?;
    fixtures.extend(FIXED_FIXTURES.iter().map(|path| (*path).to_owned()));
    for relative in coverage.sources.keys() {
        if !relative.starts_with("theories/") {
            return Err(CheckError::Invalid(format!(
                "pinned {COVERAGE} names a source outside theories/ at {relative:?}"
            )));
        }
    }
    fixtures.extend(coverage.sources.keys().cloned());
    require_inventory("fixture inventory", &record.fixture_paths_sha256, &fixtures)?;
    for (relative, digest) in coverage.sources {
        if record.fixture_paths_sha256.get(&relative) != Some(&digest) {
            return Err(CheckError::Invalid(format!(
                "fixture digest for {relative} differs from the pinned K3 source digest"
            )));
        }
    }

    record.validate_inputs(
        &snapshot.read(COMPARATOR)?,
        &snapshot.read(REPLAY)?,
        &snapshot.read(BOARD)?,
        snapshot.epoch(),
    )?;
    verify_pins(&snapshot, &record.source_files_sha256)?;
    verify_pins(&snapshot, &record.fixture_paths_sha256)?;

    Ok(Checked {
        source: record.source_commit,
        fixtures: fixtures.len(),
    })
}
