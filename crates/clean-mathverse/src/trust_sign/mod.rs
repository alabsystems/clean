// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse Phase-2 trust layer — sign the kernel-re-verified verdict,
//! re-audit, and revoke.
//!
//! See `designs/2026-06-24-mathverse-phase2-trust-the-archive.md`.
//!
//! # Trust semantics (state it plainly)
//!
//! 1. **The signature = attestable PROVENANCE.** A [`SignedVerdict`] proves
//!    *which verifier, at which `clean_version`/`clean_commit` with
//!    `tcb_axioms = 3`, observed which kernel result over which de Bruijn
//!    digest*. It is non-repudiation for the host (with an asymmetric backend),
//!    **not** a truth oracle. The HMAC dev backend gives only key-holder
//!    provenance and declares `is_asymmetric() == false`.
//! 2. **The de Bruijn digest = independent RE-VERIFIABILITY.** Every claim is
//!    content-addressed by `expr_canonical_digest`; the verifier (the kernel)
//!    is tiny and open. The de Bruijn criterion applies: download the shard,
//!    run the open cake gate, re-earn the green yourself. You do not trust the
//!    host.
//! 3. **Consumers re-verify; they do not trust the host.** The signed verdict
//!    is a fast path and an accountability record, never the root of trust.
//!    The root is the kernel + the three-axiom TCB, re-run locally. A
//!    revoked-or-absent signature changes the *badge*; the consumer's own
//!    re-check changes the *truth*.
//!
//! # The soundness fence
//!
//! The signer's only legal `KernelVerified` input is a [`KernelAttestation`]
//! produced by [`attest`] — which calls the ONE trust verdict
//! (`graduate::recheck::recheck_and_classify`) and never relaxes it. A
//! non-foundational closure cannot be signed as `KernelVerified`
//! ([`SignedVerdict::check_invariants`] refuses it). Re-verification IS the
//! trust; this module only attests and revokes it.

mod attestation;
mod backend;
mod ed25519_ring;
mod gcp_kms;
mod gcp_kms_der;
mod hmac_dev;
mod publisher;
mod reauditor;
mod revocation;
mod signed_verdict;
mod submission;
mod verdict_store;

pub use attestation::{attest, AttestError, KernelAttestation};
pub use backend::{SigningBackend, SigningError, VerifyingBackend};
pub use ed25519_ring::{Ed25519LocalBackend, Ed25519Verifier, SIG_ALG_ED25519};
pub use gcp_kms::{
    CommandRunner, GcloudCommandRunner, GcpKmsBackend, GcpKmsConfig, GcpKmsKeyType, GcpKmsVerifier,
};
pub use hmac_dev::{HmacDevBackend, SIG_ALG_HMAC_SHA256};
pub use publisher::{
    process_queue, PublishError, PublishOutcome, PublishReport, PublishedSubmission, PublisherPaths,
};
pub use reauditor::{
    reaudit_core, reaudit_shard, record_path_for, ReauditError, ReauditOutcome, ReauditReport,
    ReauditVerdict,
};
pub use revocation::{RevocationEntry, RevocationList, RevocationReason, REVOCATION_LIST_SCHEMA};
pub use signed_verdict::{
    SignedVerdict, SignedVerdictKind, VerdictInvariantError, VerifierInfo, PINNED_TCB_AXIOMS,
    SIGNED_VERDICT_SCHEMA,
};
pub use submission::{
    StageError, Submission, SubmissionError, SubmissionQueue, SubmissionRecord, SubmissionStatus,
    MAX_SUBMISSION_BYTES, SUBMISSION_SCHEMA, SUBMISSION_TRUST_NOTE,
};
pub use verdict_store::{StoredVerdict, VerdictStore, VERDICT_TRUST_NOTE};
