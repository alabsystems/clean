// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Record the standalone Python tooling inventory as canonical evidence.

use std::{collections::BTreeMap, fs, path::Path};

use crate::envelope::{
    utc_now, EvidenceEnvelope, Freshness, FreshnessPolicy, FreshnessState, InputIdentity,
    ProducerIdentity, Provenance, ProvenanceError, RepositoryState, SchemaVersion,
};
use sha2::{Digest, Sha256};

use super::{
    from_stable_inputs, git, hex, Counts, InventoryError, FIGURE, INPUT_SCOPE, PRODUCER_SOURCE,
    RECORD_PATH, REGISTRY, TRACKED_INPUT,
};

const PRODUCER_ID: &str = "clean-evidence/python-minters";
const PRODUCER_FILES: &[(&str, &[u8])] = &[
    (
        "crates/clean-evidence/src/envelope.rs",
        include_bytes!("../envelope.rs"),
    ),
    (
        "crates/clean-evidence/src/git.rs",
        include_bytes!("../git.rs"),
    ),
    (
        "crates/clean-evidence/src/main.rs",
        include_bytes!("../main.rs"),
    ),
    (
        "crates/clean-evidence/src/python_minters/mod.rs",
        include_bytes!("mod.rs"),
    ),
    (PRODUCER_SOURCE, include_bytes!("record.rs")),
];

fn repository(root: &Path) -> Result<RepositoryState, InventoryError> {
    RepositoryState::capture(root).map_err(|error| match error {
        ProvenanceError::HeadMoved => InventoryError::Invalid(error.to_string()),
        _ => InventoryError::Unavailable(error.to_string()),
    })
}

fn timestamp() -> Result<String, InventoryError> {
    utc_now()
        .map_err(|error| InventoryError::Unavailable(format!("cannot record UTC time: {error}")))
}

pub fn record(root: &Path, argv: Vec<String>) -> Result<Vec<u8>, InventoryError> {
    let started_at = timestamp()?;
    let repository_before = repository(root)?;
    let measured = from_stable_inputs(root, |inputs| {
        let measured = inputs.measure()?;
        let head = git::read(root, &["rev-parse", "--verify", "HEAD^{commit}"])
            .map_err(InventoryError::Unavailable)?;
        if head.strip_suffix(b"\n") != Some(repository_before.commit.as_bytes()) {
            return Err(InventoryError::Invalid(
                "HEAD moved during Python inventory recording".to_owned(),
            ));
        }
        Ok(measured)
    })?;
    let value = serde_json::to_value(&measured.counts)
        .map_err(|error| InventoryError::Invalid(error.to_string()))?;
    let producer_files = PRODUCER_FILES
        .iter()
        .map(|(name, bytes)| ((*name).to_owned(), hex(&Sha256::digest(bytes))))
        .collect();
    EvidenceEnvelope {
        schema: SchemaVersion::CURRENT,
        figure: FIGURE.to_owned(),
        value,
        denominator: None,
        rows_file: None,
        rows_sha256: None,
        labels: vec!["three Python membership counts with a registry row total".to_owned()],
        non_claims: vec![
            "Read-only observation scoped to path and registry counts.".to_owned(),
            "Build provenance and the publication verdict require separate qualification."
                .to_owned(),
        ],
        gate_command: "scripts/local_gate.sh --fast".to_owned(),
        provenance: Provenance {
            clean_commit: repository_before.commit,
            tree_state: repository_before.tree_state,
            binary: None,
            toolchain: BTreeMap::new(),
            sibling_pins: BTreeMap::new(),
            producer: ProducerIdentity {
                id: PRODUCER_ID.to_owned(),
                argv,
                module_digest: InputIdentity::files_digest(&producer_files),
            },
            inputs: measured.input_identity(),
            host: None,
            heavy_gate: None,
            started_at,
            finished_at: timestamp()?,
            inputs_moved_during_run: false,
        },
        freshness: Freshness {
            policy: FreshnessPolicy::InputDigest,
            state: FreshnessState::Fresh,
        },
    }
    .to_canonical_json()
    .map_err(|error| InventoryError::Invalid(error.to_string()))
}

/// A canonical Python tooling record and its comparison against the live scope.
pub struct RecordReading {
    pub envelope: EvidenceEnvelope,
    pub counts: Counts,
    pub fresh: bool,
}

/// Read the saved record and rederive its counts and freshness from stable
/// inputs. A stale record remains readable, but cannot qualify its counts
/// against the current checkout.
pub fn read_record(root: &Path) -> Result<RecordReading, InventoryError> {
    let path = root.join(RECORD_PATH);
    let read = || {
        fs::read(&path)
            .map_err(|error| InventoryError::Unavailable(format!("{}: {error}", path.display())))
    };
    let invalid = |reason| InventoryError::Invalid(format!("{RECORD_PATH}: {reason}"));
    let bytes = read()?;
    let envelope =
        EvidenceEnvelope::parse_canonical(&bytes).map_err(|error| invalid(error.to_string()))?;
    validate_metadata(&envelope).map_err(|reason| invalid(reason.to_owned()))?;
    if !envelope.value.is_object() {
        return Err(invalid("invalid counts: expected an object".to_owned()));
    }
    let counts: Counts = serde_json::from_value(envelope.value.clone())
        .map_err(|error| invalid(format!("invalid counts: {error}")))?;
    if counts.registry_path > counts.registry_rows
        || counts.registry_implemented_by > counts.registry_rows
    {
        return Err(invalid(
            "Python column count exceeds the registry row total".to_owned(),
        ));
    }
    let fresh = from_stable_inputs(root, |inputs| {
        let live = inputs.measure()?;
        if bytes != read()? {
            return Err(invalid("record changed during measurement".to_owned()));
        }
        let fresh = envelope.provenance.inputs == live.input_identity();
        if fresh && counts != live.counts {
            return Err(invalid(format!(
                "recorded counts {counts:?} differ from derived counts {:?}",
                live.counts
            )));
        }
        Ok(fresh)
    })?;
    Ok(RecordReading {
        envelope,
        counts,
        fresh,
    })
}

fn validate_metadata(envelope: &EvidenceEnvelope) -> Result<(), &'static str> {
    if envelope.figure != FIGURE {
        return Err("wrong figure, expected tooling.python_minters");
    }
    if envelope.denominator.is_some() || envelope.rows_file.is_some() {
        return Err("Python tooling records do not have a denominator or rows file");
    }
    let provenance = &envelope.provenance;
    if envelope.freshness.policy != FreshnessPolicy::InputDigest
        || provenance.inputs_moved_during_run
    {
        return Err("expected a stable input-digest measurement");
    }
    if provenance.producer.id != PRODUCER_ID || !is_sha256(&provenance.producer.module_digest) {
        return Err("invalid producer identity");
    }
    let inputs = &provenance.inputs;
    if inputs.scope != INPUT_SCOPE
        || inputs.files.len() != 2
        || ![TRACKED_INPUT, REGISTRY].iter().all(|name| {
            inputs
                .files
                .get(*name)
                .is_some_and(|digest| is_sha256(digest))
        })
    {
        return Err("invalid input scope or file digests");
    }
    if inputs.digest != InputIdentity::files_digest(&inputs.files) {
        return Err("input aggregate digest disagrees with the file digests");
    }
    Ok(())
}

fn is_sha256(digest: &str) -> bool {
    digest.len() == 64
        && digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
