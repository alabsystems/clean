// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The PRIVILEGED publisher: the only process that holds a signing key and the
//! only place a queued submission is re-verified and minted.
//!
//! For each `Pending` submission staged by the public front-end, the publisher:
//!
//! 1. re-runs the ONE trust verdict
//!    (`graduate::recheck::recheck_and_classify`) in a FRESH kernel environment
//!    via the attestation bridge ([`super::attest`]) — never forked, never
//!    weakened;
//! 2. builds a [`SignedVerdict`] from that attestation
//!    ([`SignedVerdict::from_attestation`]): a foundational re-check yields a
//!    `KernelVerified` kind, anything else a `Rejected` kind — the signer cannot
//!    upgrade a non-foundational attestation;
//! 3. signs it with the configured [`SigningBackend`] (Ed25519 by default);
//! 4. on `KernelVerified`: writes the signed verdict to the verdicts directory
//!    (where `mathverse_serve`'s `/verdict` + `/audit` serve it) and stages the
//!    re-checked declaration for archive inclusion; marks the submission
//!    `KernelVerified`;
//! 5. otherwise: writes the signed `Rejected` verdict (when one was produced)
//!    and marks the submission `Rejected` with a reason.
//!
//! This reuses ALL of Phase-2's `trust_sign`: [`super::attest`],
//! [`SignedVerdict`], [`SigningBackend`], and the same structural invariants.
//! It does NOT re-implement `recheck_and_classify`, and a malformed /
//! unverifiable / non-foundational submission is `Rejected`, never silently
//! accepted as `KernelVerified`.

use std::path::{Path, PathBuf};

use clean_kernel::{Declaration, Environment};

use super::attestation::{attest, AttestError};
use super::backend::{SigningBackend, SigningError};
use super::signed_verdict::{SignedVerdict, SignedVerdictKind};
use super::submission::{SubmissionQueue, SubmissionRecord, SubmissionStatus};

/// Why the publisher could not process the queue (infrastructure-level). A
/// per-submission rejection is NOT an error — it is a `Rejected` decision
/// recorded on the record. Fail-closed: a signing key or I/O failure is a hard
/// error, never a silent unsigned/unverified pass.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PublishError {
    /// Enumerating or moving queue records failed.
    #[error("queue I/O error: {0}")]
    Io(String),

    /// Creating the verdicts / archive output directory failed.
    #[error("could not prepare output directory {path}: {source}")]
    OutputDir {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },

    /// Signing a verdict failed (key/primitive error). A produced verdict that
    /// cannot be signed is a hard error rather than an unsigned publish.
    #[error("signing error for `{name}`: {source}")]
    Signing {
        name: String,
        #[source]
        source: SigningError,
    },

    /// Writing a signed verdict or staged declaration to disk failed.
    #[error("write error for `{name}`: {reason}")]
    Write { name: String, reason: String },
}

/// Where the publisher writes its outputs. Held by the privileged process only.
#[derive(Clone, Debug)]
pub struct PublisherPaths {
    /// `<out>/verdicts/` — signed verdicts consumed by `mathverse_serve`.
    pub verdicts_dir: PathBuf,
    /// `<out>/archive/` — re-checked declarations staged for archive inclusion
    /// (one JSON per `KernelVerified` submission).
    pub archive_dir: PathBuf,
}

impl PublisherPaths {
    /// Derive the standard layout under a single output root.
    #[must_use]
    pub fn under(out_dir: impl Into<PathBuf>) -> Self {
        let out_dir = out_dir.into();
        Self {
            verdicts_dir: out_dir.join("verdicts"),
            archive_dir: out_dir.join("archive"),
        }
    }

    /// Create both output directories if they do not exist.
    fn ensure(&self) -> Result<(), PublishError> {
        for dir in [&self.verdicts_dir, &self.archive_dir] {
            std::fs::create_dir_all(dir).map_err(|source| PublishError::OutputDir {
                path: dir.clone(),
                source,
            })?;
        }
        Ok(())
    }
}

/// The per-submission outcome the publisher decided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PublishOutcome {
    /// The fresh-kernel re-check was foundational: a signed `KernelVerified`
    /// verdict was published and the declaration staged for archive inclusion.
    KernelVerified,
    /// The submission was rejected (kernel rejection, attestation failure, or a
    /// non-foundational closure). A signed `Rejected` verdict was published
    /// where one could be produced.
    Rejected,
}

/// One submission's publish result.
#[derive(Clone, Debug)]
pub struct PublishedSubmission {
    pub submission_id: String,
    pub name: String,
    pub outcome: PublishOutcome,
    /// The rejection reason (empty for `KernelVerified`).
    pub reason: String,
}

/// Aggregate result of one publisher pass over the queue.
#[derive(Clone, Debug, Default)]
pub struct PublishReport {
    pub results: Vec<PublishedSubmission>,
    /// Number that earned `KernelVerified`.
    pub kernel_verified: usize,
    /// Number rejected.
    pub rejected: usize,
}

/// Process every pending submission in `queue`, re-verifying + signing with
/// `backend`, writing outputs under `paths`, and resolving each queue record.
///
/// `clean_commit` is recorded in each attestation; `verified_at` is the
/// RFC-3339 UTC timestamp stamped into each signed verdict.
///
/// # Errors
/// Returns [`PublishError`] for infrastructure failures (queue I/O, output dir,
/// signing, or write). A per-submission rejection is recorded on the record, not
/// returned as an error.
pub fn process_queue(
    queue: &SubmissionQueue,
    backend: &dyn SigningBackend,
    paths: &PublisherPaths,
    clean_commit: &str,
    verified_at: &str,
) -> Result<PublishReport, PublishError> {
    paths.ensure()?;
    let pending = queue
        .list_pending()
        .map_err(|e| PublishError::Io(e.to_string()))?;

    let mut report = PublishReport::default();
    for record in pending {
        let published = publish_one(queue, &record, backend, paths, clean_commit, verified_at)?;
        match published.outcome {
            PublishOutcome::KernelVerified => report.kernel_verified += 1,
            PublishOutcome::Rejected => report.rejected += 1,
        }
        report.results.push(published);
    }
    Ok(report)
}

/// Re-verify, sign, publish, and resolve one pending submission.
fn publish_one(
    queue: &SubmissionQueue,
    record: &SubmissionRecord,
    backend: &dyn SigningBackend,
    paths: &PublisherPaths,
    clean_commit: &str,
    verified_at: &str,
) -> Result<PublishedSubmission, PublishError> {
    let name = record.submission.declaration_name();
    let decl = record.submission.declaration.clone();

    // 1. The ONE trust verdict in a FRESH kernel environment. Never forked,
    //    never weakened — the same bridge the re-auditor uses.
    let mut env = Environment::new();
    let attestation = attest(&mut env, decl.clone(), clean_commit);

    // 2. Classify into a signed verdict. A kernel rejection / attestation error
    //    is a `Rejected` decision with a reason — never a silent pass and never
    //    a `KernelVerified`.
    let (mut signed, outcome, reason) = match attestation {
        Ok(att) => {
            let signed = SignedVerdict::from_attestation(&att, verified_at.to_string());
            if signed.verdict == SignedVerdictKind::KernelVerified {
                (Some(signed), PublishOutcome::KernelVerified, String::new())
            } else {
                let reason = format!(
                    "fresh-kernel re-check is not foundational-only (closure: {})",
                    att.domain_axioms.join(", ")
                );
                (Some(signed), PublishOutcome::Rejected, reason)
            }
        }
        Err(err) => (None, PublishOutcome::Rejected, attest_reject_reason(&err)),
    };

    // 3. Sign + publish. A produced verdict that cannot be signed is a hard
    //    error (never an unsigned publish). `sign_with` re-checks the structural
    //    invariants, so a `KernelVerified` over a non-empty closure cannot sign.
    if let Some(verdict) = signed.as_mut() {
        verdict
            .sign_with(backend)
            .map_err(|source| PublishError::Signing {
                name: name.clone(),
                source,
            })?;
        write_verdict(&paths.verdicts_dir, &name, verdict)?;
        if outcome == PublishOutcome::KernelVerified {
            // Stage the re-checked declaration for archive inclusion. Only a
            // KernelVerified submission is archived (a rejected one is not added).
            stage_for_archive(&paths.archive_dir, &name, &decl)?;
        }
    }

    // 4. Resolve the queue record: move it to done/ with the decided status and
    //    the signed verdict, so the front-end's `GET /submit/{id}` reflects it.
    let status = match outcome {
        PublishOutcome::KernelVerified => SubmissionStatus::KernelVerified,
        PublishOutcome::Rejected => SubmissionStatus::Rejected,
    };
    let mut resolved = record.clone();
    resolved.status = status;
    resolved.verdict = signed;
    resolved.reason = reason.clone();
    queue
        .resolve(&resolved)
        .map_err(|e| PublishError::Io(e.to_string()))?;

    Ok(PublishedSubmission {
        submission_id: record.submission_id.clone(),
        name,
        outcome,
        reason,
    })
}

/// Map an attestation failure to a human-readable rejection reason.
fn attest_reject_reason(err: &AttestError) -> String {
    match err {
        AttestError::Recheck(e) => format!("kernel re-check rejected the declaration: {e}"),
        AttestError::Digest(e) => format!("could not compute the de Bruijn digest: {e}"),
        AttestError::NoValue(n) => format!("declaration `{n}` has no proof value to verify"),
    }
}

/// Write a signed verdict to `<verdicts_dir>/<safe-name>.json`.
fn write_verdict(
    verdicts_dir: &Path,
    name: &str,
    verdict: &SignedVerdict,
) -> Result<(), PublishError> {
    let path = verdicts_dir.join(format!("{}.json", safe_name(name)));
    let json = serde_json::to_vec_pretty(verdict).map_err(|e| PublishError::Write {
        name: name.to_string(),
        reason: format!("serialize verdict: {e}"),
    })?;
    std::fs::write(&path, json).map_err(|e| PublishError::Write {
        name: name.to_string(),
        reason: e.to_string(),
    })
}

/// Stage a re-checked declaration for archive inclusion at
/// `<archive_dir>/<safe-name>.json`.
fn stage_for_archive(
    archive_dir: &Path,
    name: &str,
    decl: &Declaration,
) -> Result<(), PublishError> {
    let path = archive_dir.join(format!("{}.json", safe_name(name)));
    let json = serde_json::to_vec_pretty(decl).map_err(|e| PublishError::Write {
        name: name.to_string(),
        reason: format!("serialize declaration: {e}"),
    })?;
    std::fs::write(&path, json).map_err(|e| PublishError::Write {
        name: name.to_string(),
        reason: e.to_string(),
    })
}

/// A filesystem-safe rendering of a declaration name.
fn safe_name(name: &str) -> String {
    name.replace(['/', ':', '.', ' ', '\\'], "_")
}

#[cfg(test)]
#[path = "publisher_tests.rs"]
mod tests;
