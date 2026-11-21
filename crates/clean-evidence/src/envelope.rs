// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Versioned canonical evidence records and repository provenance.

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, SystemTimeError, UNIX_EPOCH};

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::Value;
use sha2::{Digest, Sha256};

#[path = "git.rs"]
mod git;
#[path = "python_minters/mod.rs"]
pub mod python_minters;

/// The format version of a `clean.evidence` record. Readers in this crate
/// understand major version 1 and preserve the minor version they read.
///
/// Minor-version rule (docs/DECISIONS.md, EV0 review): a minor version may
/// only add fields, each optional. Every reader refuses a field it does not
/// know, so a record that uses a newer minor's field is refused by an older
/// reader (fail closed), while a record from an older minor still reads in a
/// newer one. A new required field or a changed meaning is a new major.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SchemaVersion(u32);

impl SchemaVersion {
    pub const CURRENT: Self = Self(0);
}

impl Serialize for SchemaVersion {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&format!("clean.evidence/v1.{}", self.0))
    }
}

impl<'de> Deserialize<'de> for SchemaVersion {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let schema = String::deserialize(deserializer)?;
        let minor = schema
            .strip_prefix("clean.evidence/v1.")
            .and_then(|minor| minor.parse::<u32>().ok())
            .ok_or_else(|| {
                serde::de::Error::custom(format!("unsupported evidence schema {schema}"))
            })?;
        if schema != format!("clean.evidence/v1.{minor}") {
            return Err(serde::de::Error::custom(
                "noncanonical evidence schema version",
            ));
        }
        Ok(Self(minor))
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceEnvelope {
    pub schema: SchemaVersion,
    pub figure: String,
    pub value: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub denominator: Option<Denominator>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rows_file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rows_sha256: Option<String>,
    pub labels: Vec<String>,
    pub non_claims: Vec<String>,
    /// The command that re-checks this figure, carried over from
    /// `reports/rust-first-tooling.json`. That record's `generated_by` is
    /// `provenance.producer.argv` here, and its `non_claim` is `non_claims`.
    pub gate_command: String,
    pub provenance: Provenance,
    /// The state reported by the producer. An offline check must recompute it
    /// against current inputs.
    pub freshness: Freshness,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Denominator {
    pub count: u64,
    pub digest: String,
    pub scope: String,
}

/// Metadata observed by a producer. Optional fields are omitted when that
/// measurement does not apply; a missing heavy-gate observation is never
/// represented as a zero reservation.
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Provenance {
    pub clean_commit: String,
    pub tree_state: TreeState,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binary: Option<BinaryIdentity>,
    pub toolchain: BTreeMap<String, String>,
    pub sibling_pins: BTreeMap<String, String>,
    pub producer: ProducerIdentity,
    pub inputs: InputIdentity,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub host: Option<HostObservation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub heavy_gate: Option<HeavyGateObservation>,
    pub started_at: String,
    pub finished_at: String,
    pub inputs_moved_during_run: bool,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BinaryIdentity {
    pub version: String,
    pub git_sha: String,
    pub sha256: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProducerIdentity {
    pub id: String,
    pub argv: Vec<String>,
    pub module_digest: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct InputIdentity {
    pub scope: String,
    pub digest: String,
    pub files: BTreeMap<String, String>,
}

impl InputIdentity {
    /// Bind the ordered input names and their digests.
    pub fn from_files(scope: &str, files: BTreeMap<String, String>) -> Self {
        Self {
            scope: scope.to_owned(),
            digest: Self::files_digest(&files),
            files,
        }
    }

    /// SHA-256 over sorted `name NUL digest LF` frames.
    pub fn files_digest(files: &BTreeMap<String, String>) -> String {
        let mut hasher = Sha256::new();
        for (name, digest) in files {
            hasher.update(name.as_bytes());
            hasher.update([0]);
            hasher.update(digest.as_bytes());
            hasher.update(b"\n");
        }
        hasher
            .finalize()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct HostObservation {
    pub class: String,
    pub small_box: bool,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct HeavyGateObservation {
    pub label: String,
    pub reserved_gb: f64,
    pub peak_gb: f64,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum TreeState {
    Clean,
    Dirty,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Freshness {
    pub policy: FreshnessPolicy,
    pub state: FreshnessState,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum FreshnessPolicy {
    InputDigest,
    Commit,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
#[non_exhaustive]
pub enum FreshnessState {
    Fresh,
    Stale,
    Unknown,
}

/// Why a record could not be rendered or read as canonical evidence.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum EnvelopeError {
    #[error("{0}")]
    Json(#[from] serde_json::Error),
    #[error("rows_file and rows_sha256 must occur together")]
    IncompleteRowsBinding,
    #[error("heavy-gate measurements must be finite and nonnegative")]
    InvalidMemoryObservation,
    #[error("evidence JSON differs from canonical bytes")]
    Noncanonical,
}

impl EvidenceEnvelope {
    /// Render sorted object keys at every depth, two-space indentation and one
    /// final newline. Arrays keep their original order.
    pub fn to_canonical_json(&self) -> Result<Vec<u8>, EnvelopeError> {
        if self.rows_file.is_some() != self.rows_sha256.is_some() {
            return Err(EnvelopeError::IncompleteRowsBinding);
        }
        if self.provenance.heavy_gate.as_ref().is_some_and(|gate| {
            [gate.reserved_gb, gate.peak_gb]
                .into_iter()
                .any(|gb| !gb.is_finite() || gb < 0.0)
        }) {
            return Err(EnvelopeError::InvalidMemoryObservation);
        }
        let mut value = serde_json::to_value(self)?;
        value.sort_all_objects();
        let mut bytes = serde_json::to_vec_pretty(&value)?;
        bytes.push(b'\n');
        Ok(bytes)
    }

    /// Parse and require the exact canonical representation. A canonical
    /// envelope says nothing by itself about the truth or freshness of a figure.
    pub fn parse_canonical(bytes: &[u8]) -> Result<Self, EnvelopeError> {
        let record: Self = serde_json::from_slice(bytes)?;
        if record.to_canonical_json()? != bytes {
            return Err(EnvelopeError::Noncanonical);
        }
        Ok(record)
    }
}

/// Why the repository state could not be observed.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ProvenanceError {
    #[error("cannot run git at {root}: {source}")]
    Spawn {
        root: PathBuf,
        #[source]
        source: io::Error,
    },
    #[error("git {args} at {root}: {stderr}")]
    Git {
        args: String,
        root: PathBuf,
        stderr: String,
    },
    #[error("provenance requires the repository root, not {0}")]
    NotRepositoryRoot(PathBuf),
    #[error("HEAD moved during provenance capture")]
    HeadMoved,
    #[error("HEAD is not UTF-8")]
    NonUtf8Head,
}

/// The observed HEAD and worktree state of the explicitly supplied repository.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepositoryState {
    pub commit: String,
    pub tree_state: TreeState,
}

impl RepositoryState {
    /// Read HEAD before and after Git status. Refuse a moving HEAD; the caller
    /// separately checks the producer's declared inputs across the run.
    pub fn capture(root: &Path) -> Result<Self, ProvenanceError> {
        if git(root, &["rev-parse", "--show-prefix"])? != b"\n" {
            return Err(ProvenanceError::NotRepositoryRoot(root.to_path_buf()));
        }
        let head = ["rev-parse", "--verify", "HEAD^{commit}"];
        let commit = git(root, &head)?;
        let status = git(
            root,
            &[
                "status",
                "--porcelain=v1",
                "-z",
                "--untracked-files=normal",
                "--ignore-submodules=none",
            ],
        )?;
        if git(root, &head)? != commit {
            return Err(ProvenanceError::HeadMoved);
        }
        let commit = String::from_utf8(commit).map_err(|_| ProvenanceError::NonUtf8Head)?;
        Ok(Self {
            commit: commit.trim_end().to_owned(),
            tree_state: if status.is_empty() {
                TreeState::Clean
            } else {
                TreeState::Dirty
            },
        })
    }
}

fn git(root: &Path, args: &[&str]) -> Result<Vec<u8>, ProvenanceError> {
    let mut command = Command::new("git");
    command
        .current_dir(root)
        .arg("--no-replace-objects")
        .args(args);
    for (name, _) in std::env::vars_os() {
        if name
            .as_encoded_bytes()
            .get(..4)
            .is_some_and(|prefix| prefix.eq_ignore_ascii_case(b"GIT_"))
        {
            command.env_remove(name);
        }
    }
    command
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("GIT_NO_LAZY_FETCH", "1")
        .env("GIT_ALLOW_PROTOCOL", "")
        .env("GIT_TERMINAL_PROMPT", "0");
    let result = command.output().map_err(|source| ProvenanceError::Spawn {
        root: root.to_path_buf(),
        source,
    })?;
    if !result.status.success() {
        return Err(ProvenanceError::Git {
            args: args.join(" "),
            root: root.to_path_buf(),
            stderr: String::from_utf8_lossy(&result.stderr).trim().to_owned(),
        });
    }
    Ok(result.stdout)
}

/// The current time as `YYYY-MM-DDTHH:MM:SSZ`.
pub fn utc_now() -> Result<String, SystemTimeError> {
    let seconds = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();
    Ok(rfc3339_utc(seconds))
}

/// Seconds since the Unix epoch as an RFC 3339 UTC timestamp, by the
/// proleptic Gregorian civil-from-days conversion.
fn rfc3339_utc(seconds: u64) -> String {
    let days = seconds / 86_400;
    let second_of_day = seconds % 86_400;
    let shifted = days + 719_468;
    let era = shifted / 146_097;
    let day_of_era = shifted % 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_index + 2) / 5 + 1;
    let month = if month_index < 10 {
        month_index + 3
    } else {
        month_index - 9
    };
    let year = year_of_era + era * 400 + u64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        second_of_day / 3_600,
        second_of_day % 3_600 / 60,
        second_of_day % 60
    )
}

#[cfg(test)]
#[path = "envelope_tests.rs"]
mod tests;
