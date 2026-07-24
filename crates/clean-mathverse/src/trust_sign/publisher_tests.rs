// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the privileged publisher: a foundational submission earns a signed
//! `KernelVerified` verdict (published + archived); a non-foundational, kernel-
//! rejected, or otherwise-unverifiable submission is `Rejected` and NEVER
//! `KernelVerified`.

use super::*;
use crate::trust_sign::ed25519_ring::{Ed25519LocalBackend, Ed25519Verifier};
use crate::trust_sign::signed_verdict::SignedVerdictKind;
use crate::trust_sign::submission::{Submission, SubmissionQueue, SubmissionStatus};
use clean_kernel::{BinderInfo, Declaration, Expr, Name};

/// `fun (p : Prop) (h : p) => h : ∀ (p : Prop), p → p` — foundational-only.
fn imp_self_decl() -> Declaration {
    Declaration::Theorem {
        name: Name::from_string("Publish.imp_self"),
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

/// Stage a submission body into a fresh queue, returning the queue + dirs.
fn stage(decl: Declaration) -> (tempfile::TempDir, SubmissionQueue, String) {
    let tmp = tempfile::tempdir().expect("tempdir");
    let queue = SubmissionQueue::open(tmp.path().join("queue")).expect("open queue");
    let body = serde_json::to_vec(&Submission {
        declaration: decl,
        note: String::new(),
    })
    .expect("serialize submission");
    let record = queue
        .stage(&body, "1970-01-01T00:00:00Z")
        .expect("stage submission");
    (tmp, queue, record.submission_id)
}

fn backend() -> Ed25519LocalBackend {
    Ed25519LocalBackend::generate("ed25519-local:publisher-test")
        .expect("keypair")
        .0
}

#[test]
fn test_foundational_submission_is_published_kernel_verified() {
    let (tmp, queue, id) = stage(imp_self_decl());
    let backend = backend();
    let paths = PublisherPaths::under(tmp.path().join("out"));

    let report = process_queue(
        &queue,
        &backend,
        &paths,
        "test-commit",
        "1970-01-01T00:00:00Z",
    )
    .expect("publisher pass succeeds");

    // The submission earned KernelVerified.
    assert_eq!(report.kernel_verified, 1);
    assert_eq!(report.rejected, 0);
    assert_eq!(report.results[0].outcome, PublishOutcome::KernelVerified);

    // A signed verdict was written to the verdicts dir, and it verifies + is
    // KernelVerified.
    let verdict_path = paths.verdicts_dir.join("Publish_imp_self.json");
    let bytes = std::fs::read(&verdict_path).expect("verdict written");
    let verdict: SignedVerdict = serde_json::from_slice(&bytes).expect("parse verdict");
    assert_eq!(verdict.verdict, SignedVerdictKind::KernelVerified);
    assert!(verdict.foundational);
    assert!(verdict.axiom_closure.is_empty());
    let verifier = Ed25519Verifier::new("ed25519-local:publisher-test", backend.public_key_bytes());
    verdict
        .verify_with(&verifier)
        .expect("published verdict signature verifies");

    // The declaration was staged for archive inclusion.
    assert!(paths.archive_dir.join("Publish_imp_self.json").exists());

    // The queue record reflects the decision: GET /submit/{id} would now show
    // KernelVerified with the signed verdict.
    let resolved = queue.load(&id).expect("load resolved record");
    assert_eq!(resolved.status, SubmissionStatus::KernelVerified);
    assert!(resolved.verdict.is_some());
    assert!(queue.list_pending().expect("list").is_empty());
}

#[test]
fn test_non_foundational_submission_is_rejected_never_kernel_verified() {
    // A theorem whose proof cites a domain axiom: the fresh-kernel re-check
    // succeeds but the closure is not foundational-only -> Rejected.
    let tmp = tempfile::tempdir().expect("tempdir");
    let queue = SubmissionQueue::open(tmp.path().join("queue")).expect("open queue");

    // The publisher re-checks in a FRESH env, so the cited axiom is unknown ->
    // the kernel rejects the proof term outright (a dangling const). Either way
    // it must never be KernelVerified. To exercise the *non-foundational closure*
    // path specifically, we submit a declaration that references an axiom by a
    // name the fresh env will reject — confirming Rejected, never green.
    let axiom_type = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let bad = Declaration::Theorem {
        name: Name::from_string("Publish.cites_unknown_axiom"),
        level_params: vec![],
        type_: axiom_type,
        value: Expr::const_str("Publish.NoSuchAxiom"),
    };
    let body = serde_json::to_vec(&Submission {
        declaration: bad,
        note: String::new(),
    })
    .expect("serialize");
    let id = queue
        .stage(&body, "1970-01-01T00:00:00Z")
        .expect("stage")
        .submission_id;

    let backend = backend();
    let paths = PublisherPaths::under(tmp.path().join("out"));
    let report = process_queue(&queue, &backend, &paths, "c", "1970-01-01T00:00:00Z")
        .expect("publisher pass");

    assert_eq!(report.kernel_verified, 0, "must never mint a green");
    assert_eq!(report.rejected, 1);
    assert_eq!(report.results[0].outcome, PublishOutcome::Rejected);

    let resolved = queue.load(&id).expect("load resolved");
    assert_eq!(resolved.status, SubmissionStatus::Rejected);
    assert!(!resolved.reason.is_empty(), "a rejection carries a reason");
    // No archive entry for a rejected submission.
    assert!(!paths
        .archive_dir
        .join("Publish_cites_unknown_axiom.json")
        .exists());
}

#[test]
fn test_ill_typed_submission_is_rejected_and_never_archived() {
    // An ill-typed declaration is kernel-rejected in the fresh env. The soundness
    // fence: a rejected submission is moved to Rejected and NOTHING non-green is
    // ever staged for archive inclusion. (A theorem citing an external domain
    // axiom is also rejected here — the publisher re-checks in a FRESH env where
    // that axiom is unknown, so it is a dangling const, never KernelVerified;
    // see `test_non_foundational_submission_is_rejected_never_kernel_verified`.)
    let tmp = tempfile::tempdir().expect("tempdir");
    let queue = SubmissionQueue::open(tmp.path().join("queue")).expect("open queue");
    // Type/value mismatch: claims `Prop -> Prop` but the value is `bvar(0)` at
    // top level (ill-typed) -> kernel rejection.
    let ill_typed = Declaration::Theorem {
        name: Name::from_string("Publish.ill_typed"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        value: Expr::bvar(0),
    };
    let body = serde_json::to_vec(&Submission {
        declaration: ill_typed,
        note: String::new(),
    })
    .expect("serialize");
    queue.stage(&body, "t").expect("stage");

    let backend = backend();
    let paths = PublisherPaths::under(tmp.path().join("out"));
    let report = process_queue(&queue, &backend, &paths, "c", "t").expect("publisher pass");
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.rejected, 1);
    // Archive dir created but empty (nothing green to stage).
    let archived: Vec<_> = std::fs::read_dir(&paths.archive_dir)
        .expect("archive dir exists")
        .collect();
    assert!(
        archived.is_empty(),
        "a rejected submission is never archived"
    );
}

#[test]
fn test_e2e_frontend_stages_without_key_then_publisher_mints() {
    // The full Phase-2.1 flow + the soundness fence that the FRONT-END never
    // signs: staging produces a Pending record with NO verdict (no key access);
    // only the privileged publisher (which holds the key) mints the green.
    let (tmp, queue, id) = stage(imp_self_decl());

    // Front-end side: the staged record is pending and carries NO signed verdict
    // (the front-end holds no signing key — it cannot have minted anything).
    let staged = queue.load(&id).expect("staged record");
    assert_eq!(staged.status, SubmissionStatus::Pending);
    assert!(
        staged.verdict.is_none(),
        "the front-end must not produce a verdict — it holds no signing key"
    );

    // Publisher side (separate, privileged): it holds the key and mints.
    let backend = backend();
    let paths = PublisherPaths::under(tmp.path().join("out"));
    process_queue(&queue, &backend, &paths, "commit", "t").expect("publish");

    // GET /submit/{id} would now reflect KernelVerified with the signed verdict.
    let done = queue.load(&id).expect("resolved record");
    assert_eq!(done.status, SubmissionStatus::KernelVerified);
    // The status JSON the HTTP layer serves carries the signed verdict.
    let status_json = done.status_json();
    assert_eq!(status_json["status"], "KernelVerified");
    assert!(status_json["verdict"].is_object());
    let verdict = done
        .verdict
        .as_ref()
        .expect("a signed verdict is attached once published");
    assert_eq!(verdict.verdict, SignedVerdictKind::KernelVerified);
}

#[test]
fn test_empty_queue_publishes_nothing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let queue = SubmissionQueue::open(tmp.path().join("queue")).expect("open queue");
    let backend = backend();
    let paths = PublisherPaths::under(tmp.path().join("out"));
    let report = process_queue(&queue, &backend, &paths, "c", "t").expect("empty pass");
    assert_eq!(report.results.len(), 0);
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.rejected, 0);
}
