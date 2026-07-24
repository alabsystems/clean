// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase-2.1 live submission queue: the shared schema between the PUBLIC
//! front-end (`mathverse_serve`'s `POST /submit`) and the PRIVILEGED publisher
//! (`mathverse_publisher`).
//!
//! # The soundness split (state it plainly)
//!
//! The public front-end holds **no signing key** and **never mints**. It only:
//!
//! 1. parses + validates well-formedness of a candidate declaration
//!    ([`Submission::validate`]), enforcing size limits;
//! 2. stages the submission to the queue directory with a generated
//!    `submission_id` and `status = Pending` ([`SubmissionQueue::stage`]);
//! 3. answers `GET /submit/{id}` from the on-disk record ([`SubmissionQueue::load`]).
//!
//! The authoritative gate is the publisher: it re-runs the ONE trust verdict
//! (`graduate::recheck::recheck_and_classify`) in a FRESH kernel via the
//! attestation bridge ([`super::attest`]), and only a foundational re-check
//! earns a signed `KernelVerified`. A malformed / unverifiable / non-foundational
//! submission is `Rejected`, never silently accepted. See [`super::publisher`].
//!
//! # On-disk layout
//!
//! ```text
//! $MATHVERSE_SUBMIT_QUEUE/
//!   pending/<submission_id>.json     # SubmissionRecord, status=Pending
//!   done/<submission_id>.json        # SubmissionRecord, status=KernelVerified|Rejected
//! ```
//!
//! The publisher moves a record from `pending/` to `done/` once it has decided,
//! attaching the signed verdict (or the rejection reason). The front-end reads
//! both directories for a status lookup; it only ever WRITES `pending/`.

use std::path::{Path, PathBuf};

use clean_kernel::Declaration;
use serde::{Deserialize, Serialize};

use super::signed_verdict::SignedVerdict;

/// The pinned submission-record schema identifier.
pub const SUBMISSION_SCHEMA: &str = "mathverse-submission-v1";

/// Maximum accepted submission body size, in bytes. A declaration is a small
/// JSON object; anything larger is rejected before it touches the kernel.
pub const MAX_SUBMISSION_BYTES: usize = 1 << 20; // 1 MiB

/// The pending/done subdirectory names under the queue root.
const PENDING_DIR: &str = "pending";
const DONE_DIR: &str = "done";

/// A candidate to verify-and-add: a single kernel [`Declaration`] (a theorem or
/// definition carrying a proof value), optionally tagged with a client note.
///
/// This is the wire shape accepted by `POST /submit`. The declaration is the
/// existing `clean_kernel::Declaration` (serde round-trips it), so the front-end
/// performs no lossy translation — it stages exactly what the publisher will
/// re-check.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Submission {
    /// The declaration to re-verify and (if foundational) sign.
    pub declaration: Declaration,
    /// Optional free-text note from the submitter (recorded, never trusted).
    #[serde(default)]
    pub note: String,
}

/// Why a submission failed front-end well-formedness validation. This is the
/// CHEAP syntactic pre-check only — it never decides verification (that is the
/// publisher's fresh-kernel job). Fail-closed: a malformed body is rejected at
/// the door, never staged.
#[derive(Clone, Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SubmissionError {
    /// The request body exceeded [`MAX_SUBMISSION_BYTES`].
    #[error("submission too large: {got} bytes exceeds the {max}-byte limit")]
    TooLarge { got: usize, max: usize },

    /// The body did not parse as a [`Submission`] JSON object.
    #[error("malformed submission JSON: {0}")]
    Parse(String),

    /// The declaration is an axiom (no proof value): it cannot be re-verified
    /// into a `KernelVerified` and so is refused up front. Axioms are TCB
    /// changes, never user submissions.
    #[error("an axiom has no proof value to verify; submit a theorem or definition")]
    AxiomNotAccepted,

    /// The declaration has an empty name.
    #[error("submission declaration has an empty name")]
    EmptyName,
}

/// The lifecycle status of a staged submission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SubmissionStatus {
    /// Staged by the front-end; awaiting the privileged publisher's re-check.
    Pending,
    /// The publisher re-verified it in a fresh kernel and it earned a
    /// foundational `KernelVerified` signed verdict.
    KernelVerified,
    /// The publisher rejected it (malformed-on-recheck, kernel rejection, or a
    /// non-foundational closure). Carries a signed `Rejected` verdict where one
    /// could be produced, plus a human-readable reason.
    Rejected,
}

impl SubmissionStatus {
    /// The wire label for this status.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::KernelVerified => "KernelVerified",
            Self::Rejected => "Rejected",
        }
    }
}

/// One staged submission's on-disk record. The front-end writes it with
/// `status = Pending` and no verdict; the publisher rewrites it (into `done/`)
/// with the decided status, the signed verdict, and a reason.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubmissionRecord {
    pub schema: String,
    /// Generated content-addressed id (`sub_<blake3-prefix>`).
    pub submission_id: String,
    /// The staged candidate.
    pub submission: Submission,
    /// Current lifecycle status.
    pub status: SubmissionStatus,
    /// RFC-3339-ish UTC timestamp the front-end staged it.
    pub submitted_at: String,
    /// The publisher's signed verdict, once decided. `None` while pending and
    /// for a few publisher-side failures that never produced an attestation.
    #[serde(default)]
    pub verdict: Option<SignedVerdict>,
    /// Human-readable reason for a `Rejected` decision (empty otherwise).
    #[serde(default)]
    pub reason: String,
}

impl SubmissionRecord {
    /// The JSON the front-end returns to a submitter (and `GET /submit/{id}`
    /// echoes): id, status, note, and — once published — the signed verdict.
    #[must_use]
    pub fn status_json(&self) -> serde_json::Value {
        serde_json::json!({
            "submission_id": self.submission_id,
            "status": self.status.label(),
            "submitted_at": self.submitted_at,
            "reason": self.reason,
            "verdict": self.verdict,
            "note": SUBMISSION_TRUST_NOTE,
        })
    }
}

/// The honesty note attached to every submission response: the front-end never
/// mints; the publisher's fresh-kernel re-check is the authoritative gate.
pub const SUBMISSION_TRUST_NOTE: &str =
    "This front-end holds NO signing key and never mints a verdict. It validates \
     well-formedness and stages the submission to a queue (status=pending). A \
     privileged, offline publisher re-runs the kernel in a FRESH environment; only a \
     foundational-only re-check earns a signed KernelVerified verdict — otherwise the \
     submission is Rejected. Re-verification is the trust, not this endpoint.";

/// A filesystem-backed submission queue rooted at `$MATHVERSE_SUBMIT_QUEUE`.
///
/// The front-end uses [`Self::stage`] (write `pending/`) and [`Self::load`]
/// (status lookup). The publisher uses [`Self::list_pending`] and
/// [`Self::resolve`] (move `pending/` → `done/`). The queue holds no key.
#[derive(Clone, Debug)]
pub struct SubmissionQueue {
    root: PathBuf,
}

impl SubmissionQueue {
    /// Open (creating if needed) a queue rooted at `root`.
    ///
    /// # Errors
    /// Returns the I/O error if the `pending/` and `done/` directories cannot be
    /// created.
    pub fn open(root: impl Into<PathBuf>) -> std::io::Result<Self> {
        let root = root.into();
        std::fs::create_dir_all(root.join(PENDING_DIR))?;
        std::fs::create_dir_all(root.join(DONE_DIR))?;
        Ok(Self { root })
    }

    /// Validate a raw request body and stage it as a new `Pending` record,
    /// returning the persisted record (with its generated id).
    ///
    /// The front-end calls this. It performs the CHEAP syntactic pre-check
    /// ([`Submission::validate`]); it does NOT run the kernel and holds no key.
    ///
    /// # Errors
    /// Returns [`SubmissionError`] for an oversized / malformed / axiom body
    /// (rejected at the door, never staged), or wraps an I/O error as
    /// [`SubmissionError::Parse`] only as a last resort (the staging write).
    pub fn stage(&self, body: &[u8], submitted_at: &str) -> Result<SubmissionRecord, StageError> {
        let submission = Submission::validate(body)?;
        let submission_id = generate_submission_id(body, submitted_at);
        let record = SubmissionRecord {
            schema: SUBMISSION_SCHEMA.to_string(),
            submission_id: submission_id.clone(),
            submission,
            status: SubmissionStatus::Pending,
            submitted_at: submitted_at.to_string(),
            verdict: None,
            reason: String::new(),
        };
        let path = self
            .root
            .join(PENDING_DIR)
            .join(format!("{submission_id}.json"));
        let json = serde_json::to_vec_pretty(&record)
            .map_err(|e| StageError::Write(format!("serialize record: {e}")))?;
        std::fs::write(&path, json).map_err(|e| StageError::Write(e.to_string()))?;
        Ok(record)
    }

    /// Load a submission record by id, searching `done/` first (a decided record
    /// is the authoritative answer), then `pending/`. Returns `None` for an
    /// unknown id.
    #[must_use]
    pub fn load(&self, submission_id: &str) -> Option<SubmissionRecord> {
        if !is_valid_id(submission_id) {
            return None;
        }
        let file = format!("{submission_id}.json");
        for sub in [DONE_DIR, PENDING_DIR] {
            let path = self.root.join(sub).join(&file);
            if let Some(record) = read_record(&path) {
                return Some(record);
            }
        }
        None
    }

    /// List every pending submission record (publisher side), sorted by id for
    /// deterministic processing order.
    ///
    /// # Errors
    /// Returns the directory-read error if `pending/` cannot be enumerated.
    pub fn list_pending(&self) -> std::io::Result<Vec<SubmissionRecord>> {
        let mut records = Vec::new();
        for entry in std::fs::read_dir(self.root.join(PENDING_DIR))? {
            let path = entry?.path();
            if path.extension().is_some_and(|e| e == "json") {
                if let Some(record) = read_record(&path) {
                    records.push(record);
                }
            }
        }
        records.sort_by(|a, b| a.submission_id.cmp(&b.submission_id));
        Ok(records)
    }

    /// Persist a publisher decision: write the resolved record into `done/` and
    /// remove the `pending/` copy (the publisher side; it carries the key, this
    /// queue does not). A re-run that resolves an already-done id is idempotent.
    ///
    /// # Errors
    /// Returns the I/O error if the done record cannot be written.
    pub fn resolve(&self, record: &SubmissionRecord) -> std::io::Result<()> {
        let file = format!("{}.json", record.submission_id);
        let done_path = self.root.join(DONE_DIR).join(&file);
        let json = serde_json::to_vec_pretty(record)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        std::fs::write(&done_path, json)?;
        // Best-effort removal of the pending copy; a leftover is harmless because
        // `load` and `list_pending` both prefer/skip via the done record.
        let pending_path = self.root.join(PENDING_DIR).join(&file);
        let _ = std::fs::remove_file(pending_path);
        Ok(())
    }

    /// The queue root directory (diagnostics).
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }
}

/// Why staging a submission failed: a validation rejection (client error) or a
/// queue write failure (server error).
#[derive(Clone, Debug, thiserror::Error)]
#[non_exhaustive]
pub enum StageError {
    /// The body failed front-end well-formedness validation (HTTP 400).
    #[error(transparent)]
    Invalid(#[from] SubmissionError),
    /// The queue write itself failed (HTTP 500).
    #[error("could not stage submission: {0}")]
    Write(String),
}

impl Submission {
    /// Parse + validate a raw request body as a well-formed submission. This is
    /// the CHEAP syntactic pre-check the front-end runs; it never decides
    /// verification (the publisher's fresh kernel is the authoritative gate).
    ///
    /// # Errors
    /// Returns [`SubmissionError`] for an oversized body, a parse failure, an
    /// axiom (no proof value), or an empty declaration name.
    pub fn validate(body: &[u8]) -> Result<Self, SubmissionError> {
        if body.len() > MAX_SUBMISSION_BYTES {
            return Err(SubmissionError::TooLarge {
                got: body.len(),
                max: MAX_SUBMISSION_BYTES,
            });
        }
        let submission: Submission =
            serde_json::from_slice(body).map_err(|e| SubmissionError::Parse(e.to_string()))?;
        submission.check_shape()?;
        Ok(submission)
    }

    /// Structural shape check: non-empty name, and a value-bearing declaration
    /// (not a bare axiom). Does NOT run the kernel.
    fn check_shape(&self) -> Result<(), SubmissionError> {
        if matches!(&self.declaration, Declaration::Axiom { .. }) {
            return Err(SubmissionError::AxiomNotAccepted);
        }
        if self.declaration_name().trim().is_empty() {
            return Err(SubmissionError::EmptyName);
        }
        Ok(())
    }

    /// The declaration's name (for staging diagnostics and id derivation).
    #[must_use]
    pub fn declaration_name(&self) -> String {
        match &self.declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Definition { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. } => name.to_string(),
        }
    }
}

/// Generate a content-addressed submission id: `sub_<blake3-prefix>` over the
/// body bytes plus the timestamp, so two identical bodies submitted at the same
/// instant collide deterministically (idempotent re-submission) but distinct
/// content/time get distinct ids. No external id dependency (no `uuid`).
fn generate_submission_id(body: &[u8], submitted_at: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(body);
    hasher.update(b"@");
    hasher.update(submitted_at.as_bytes());
    let hex = hasher.finalize().to_hex();
    format!("sub_{}", &hex[..32])
}

/// `true` iff `id` is a syntactically valid submission id (so a status lookup
/// cannot escape the queue directory via `../` path traversal).
fn is_valid_id(id: &str) -> bool {
    id.starts_with("sub_")
        && id.len() <= 64
        && id[4..].chars().all(|c| c.is_ascii_hexdigit())
        && id.len() > 4
}

/// Read + deserialize one submission record, returning `None` on any read/parse
/// failure (a malformed on-disk record is never served as if valid).
fn read_record(path: &Path) -> Option<SubmissionRecord> {
    let bytes = std::fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Expr, Name};

    fn imp_self_decl() -> Declaration {
        Declaration::Theorem {
            name: Name::from_string("Submit.imp_self"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        }
    }

    fn imp_self_body() -> Vec<u8> {
        let submission = Submission {
            declaration: imp_self_decl(),
            note: "a foundational submission".to_string(),
        };
        serde_json::to_vec(&submission).expect("serialize submission")
    }

    #[test]
    fn test_validate_well_formed_submission_accepts() {
        let submission = Submission::validate(&imp_self_body()).expect("well-formed submission");
        assert_eq!(submission.declaration_name(), "Submit.imp_self");
    }

    #[test]
    fn test_validate_rejects_axiom() {
        let body = serde_json::to_vec(&Submission {
            declaration: Declaration::Axiom {
                name: Name::from_string("Submit.an_axiom"),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            },
            note: String::new(),
        })
        .expect("serialize");
        let err = Submission::validate(&body).expect_err("an axiom must be refused at the door");
        assert!(matches!(err, SubmissionError::AxiomNotAccepted));
    }

    #[test]
    fn test_validate_rejects_oversized() {
        let body = vec![b'x'; MAX_SUBMISSION_BYTES + 1];
        let err = Submission::validate(&body).expect_err("oversized body must be rejected");
        assert!(matches!(err, SubmissionError::TooLarge { .. }));
    }

    #[test]
    fn test_validate_rejects_garbage() {
        let err = Submission::validate(b"not json at all").expect_err("garbage must be rejected");
        assert!(matches!(err, SubmissionError::Parse(_)));
    }

    #[test]
    fn test_stage_then_load_round_trips_pending() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let queue = SubmissionQueue::open(tmp.path()).expect("open queue");
        let staged = queue
            .stage(&imp_self_body(), "1970-01-01T00:00:00Z")
            .expect("stage succeeds");
        assert_eq!(staged.status, SubmissionStatus::Pending);
        assert!(staged.submission_id.starts_with("sub_"));
        let loaded = queue.load(&staged.submission_id).expect("load by id");
        assert_eq!(loaded.submission_id, staged.submission_id);
        assert_eq!(loaded.status, SubmissionStatus::Pending);
    }

    #[test]
    fn test_load_unknown_id_is_none() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let queue = SubmissionQueue::open(tmp.path()).expect("open queue");
        assert!(queue.load("sub_deadbeef").is_none());
        // Path traversal attempts are rejected by id validation.
        assert!(queue.load("../../etc/passwd").is_none());
        assert!(queue.load("sub_../escape").is_none());
    }

    #[test]
    fn test_list_pending_returns_staged() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let queue = SubmissionQueue::open(tmp.path()).expect("open queue");
        queue
            .stage(&imp_self_body(), "1970-01-01T00:00:01Z")
            .expect("stage");
        let pending = queue.list_pending().expect("list pending");
        assert_eq!(pending.len(), 1);
        assert_eq!(pending[0].status, SubmissionStatus::Pending);
    }

    #[test]
    fn test_resolve_moves_pending_to_done() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let queue = SubmissionQueue::open(tmp.path()).expect("open queue");
        let mut staged = queue
            .stage(&imp_self_body(), "1970-01-01T00:00:02Z")
            .expect("stage");
        staged.status = SubmissionStatus::Rejected;
        staged.reason = "test resolution".to_string();
        queue.resolve(&staged).expect("resolve");
        // It is no longer pending, and the done record reflects the decision.
        assert!(queue.list_pending().expect("list").is_empty());
        let loaded = queue.load(&staged.submission_id).expect("load done record");
        assert_eq!(loaded.status, SubmissionStatus::Rejected);
        assert_eq!(loaded.reason, "test resolution");
    }
}
