// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The staleness verdict as a `clean.evidence/v1` record, with the inputs it
//! hashed and the repository state it was measured over.

use super::{
    check, StalenessCheck, StalenessFinding, TrustcoreError, ARTIFACTS, DIGEST_MODULE_SOURCE,
    DIGEST_SOURCE, MODULE_FILE, MODULE_TREE_KEY,
};
use crate::digest::sha256_file;
use crate::envelope::{
    utc_now, EnvelopeError, EvidenceEnvelope, Freshness, FreshnessPolicy, FreshnessState,
    InputIdentity, ProducerIdentity, Provenance, ProvenanceError, RepositoryState, SchemaVersion,
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::Path;

/// The figure this producer mints.
pub const FIGURE: &str = "trustcore.receipt_freshness";
/// The producer's identity in `provenance.producer.id`.
pub const PRODUCER_ID: &str = "clean-evidence/trustcore";
/// The command that re-checks the figure.
pub const GATE_COMMAND: &str = "clean-evidence check trustcore-staleness --repo-root .";
const INPUT_SCOPE: &str = "the TrustCore gate sources, both shared digest sources and the three \
                           launch receipts";
/// The producer's compiled source: the module that decides the verdict.
const PRODUCER_SOURCE: &[u8] = include_bytes!("../trustcore.rs");

/// The record's `value`: the verdict and every finding behind it.
#[derive(Serialize)]
struct FigureValue<'a> {
    state: FreshnessState,
    findings: &'a [StalenessFinding],
}

/// Why a record could not be produced.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum RecordError {
    #[error("cannot hash the trust-core gate sources: {0}")]
    Check(#[from] TrustcoreError),
    #[error("cannot observe the repository: {0}")]
    Provenance(#[from] ProvenanceError),
    #[error("cannot render the record: {0}")]
    Envelope(#[from] EnvelopeError),
    #[error("the system clock is before 1970")]
    Clock,
}

impl StalenessCheck {
    /// Run the check at `root` and wrap its verdict in an evidence record.
    /// `argv` is the producer command line as invoked. The inputs are hashed
    /// again after the check; a difference is recorded, never hidden.
    pub fn record(root: &Path, argv: &[String]) -> Result<(Self, EvidenceEnvelope), RecordError> {
        let started_at = utc_now().map_err(|_| RecordError::Clock)?;
        let repository = RepositoryState::capture(root)?;
        let checked = check(root)?;
        let files = input_files(root, &checked);
        let after = check(root)?;
        let moved = input_files(root, &after) != files;
        let state = if checked.findings.is_empty() {
            FreshnessState::Fresh
        } else {
            FreshnessState::Stale
        };
        let value = serde_json::to_value(FigureValue {
            state,
            findings: &checked.findings,
        })
        .map_err(EnvelopeError::from)?;
        let envelope = EvidenceEnvelope {
            schema: SchemaVersion::CURRENT,
            figure: FIGURE.to_owned(),
            value,
            denominator: None,
            rows_file: None,
            rows_sha256: None,
            labels: vec!["input-digest pins of the TrustCore launch receipts".to_owned()],
            non_claims: [
                "runs no TrustCore lane: a fresh pin says the receipts were minted over these \
                 sources, not that their lanes pass today",
                "the axiom-audit receipt is compared on its source-file pin and an optional \
                 module-tree pin only",
                "no binary identity: the standalone binary carries no build stamp",
            ]
            .into_iter()
            .map(str::to_owned)
            .collect(),
            gate_command: GATE_COMMAND.to_owned(),
            provenance: Provenance {
                clean_commit: repository.commit,
                tree_state: repository.tree_state,
                binary: None,
                toolchain: BTreeMap::new(),
                sibling_pins: BTreeMap::new(),
                producer: ProducerIdentity {
                    id: PRODUCER_ID.to_owned(),
                    argv: argv.to_vec(),
                    module_digest: hex(&Sha256::digest(PRODUCER_SOURCE)),
                },
                inputs: InputIdentity::from_files(INPUT_SCOPE, files),
                host: None,
                heavy_gate: None,
                started_at,
                finished_at: utc_now().map_err(|_| RecordError::Clock)?,
                inputs_moved_during_run: moved,
            },
            freshness: Freshness {
                policy: FreshnessPolicy::InputDigest,
                state,
            },
        };
        envelope.to_canonical_json()?;
        Ok((checked, envelope))
    }
}

/// Every input and its digest. A receipt that cannot be read is absent from
/// the map; the verdict already names it.
fn input_files(root: &Path, checked: &StalenessCheck) -> BTreeMap<String, String> {
    let sources = [
        (MODULE_FILE, &checked.file_sha256),
        (MODULE_TREE_KEY, &checked.tree_sha256),
        (DIGEST_SOURCE, &checked.digest_source_sha256),
        (DIGEST_MODULE_SOURCE, &checked.digest_module_sha256),
    ]
    .map(|(path, digest)| (path.to_owned(), digest.clone()));
    let receipts = ARTIFACTS.iter().filter_map(|(path, _)| {
        sha256_file(&root.join(path))
            .ok()
            .map(|digest| ((*path).to_owned(), digest))
    });
    sources.into_iter().chain(receipts).collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
