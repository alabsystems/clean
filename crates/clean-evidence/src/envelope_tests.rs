// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serde_json::json;

#[test]
fn test_repository_state_replacement_tree_cannot_hide_staged_changes() {
    let repo = tempfile::tempdir().expect("fixture directory");
    let root = repo.path();
    git(root, &["init", "-q", "--object-format=sha1"]).expect("initialize fixture");
    git(root, &["config", "user.name", "Fixture"]).expect("fixture name");
    git(root, &["config", "user.email", "fixture@example.invalid"]).expect("fixture email");
    git(root, &["config", "commit.gpgsign", "false"]).expect("unsigned fixture commits");
    std::fs::write(root.join("input"), b"original").expect("original source");
    git(root, &["add", "input"]).expect("stage original");
    git(root, &["commit", "-qm", "original", "--no-verify"]).expect("original commit");
    let original = RepositoryState::capture(root).expect("original clean repository");
    assert_eq!(original.tree_state, TreeState::Clean);
    std::fs::write(root.join("input"), b"replacement").expect("replacement source");
    git(root, &["add", "input"]).expect("stage replacement");
    git(root, &["commit", "-qm", "replacement", "--no-verify"]).expect("replacement commit");
    let replacement = RepositoryState::capture(root).expect("replacement clean repository");
    git(root, &["reset", "--soft", &original.commit]).expect("retain replacement index");
    git(root, &["replace", &original.commit, &replacement.commit]).expect("replace original");

    // The ordinary Git view reports clean against the replacement tree while
    // HEAD still names the original commit. Provenance must observe the latter.
    let mut ordinary_git = Command::new("git");
    for (name, _) in std::env::vars_os() {
        if name
            .as_encoded_bytes()
            .get(..4)
            .is_some_and(|prefix| prefix.eq_ignore_ascii_case(b"GIT_"))
        {
            ordinary_git.env_remove(name);
        }
    }
    let replaced = ordinary_git
        .current_dir(root)
        .args(["status", "--porcelain=v1", "-z"])
        .output()
        .expect("ordinary replacement-aware status");
    assert!(replaced.status.success(), "{replaced:?}");
    assert!(replaced.stdout.is_empty(), "{replaced:?}");
    let observed = RepositoryState::capture(root).expect("immutable repository state");
    assert_eq!(observed.commit, original.commit);
    assert_eq!(observed.tree_state, TreeState::Dirty);
    git(root, &["replace", "-d", &original.commit]).expect("remove fixture replacement");
    assert_eq!(
        RepositoryState::capture(root).expect("restore view"),
        observed
    );
}

#[test]
fn test_repository_state_capture_root_and_nested_head_observed_nested_refused() {
    let repo = tempfile::tempdir().expect("fixture directory");
    let root = repo.path();
    git(root, &["init", "-q"]).expect("initialize fixture repository");
    git(
        root,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "fixture",
            "--allow-empty",
            "--no-verify",
        ],
    )
    .expect("create fixture commit");

    let clean = RepositoryState::capture(root).expect("capture clean repository");
    assert_eq!(clean.tree_state, TreeState::Clean);
    assert_eq!(
        clean.commit.as_bytes(),
        git(root, &["rev-parse", "HEAD"])
            .expect("read fixture HEAD")
            .trim_ascii()
    );

    let nested = root.join("nested");
    std::fs::create_dir(&nested).expect("create nested directory");
    std::fs::write(nested.join("new.txt"), b"fixture").expect("create untracked input");
    let dirty = RepositoryState::capture(root).expect("capture dirty repository");
    assert_eq!(dirty.tree_state, TreeState::Dirty);
    assert_eq!(dirty.commit, clean.commit);
    assert!(RepositoryState::capture(&nested).is_err());
}

fn fixture() -> EvidenceEnvelope {
    serde_json::from_value(json!({
        "schema": "clean.evidence/v1.0",
        "figure": "example",
        "value": { "z": 2, "a": { "y": 3, "b": 1 } },
        "labels": ["measurement"],
        "non_claims": ["scope outside the fixture"],
        "gate_command": "check example",
        "provenance": {
            "clean_commit": "0123456789012345678901234567890123456789",
            "tree_state": "clean",
            "toolchain": {},
            "sibling_pins": {},
            "producer": { "id": "example", "argv": ["check", "example"], "module_digest": "pin" },
            "inputs": { "scope": "file", "digest": "input-pin", "files": { "file": "file-pin" } },
            "started_at": "2026-11-17T00:00:00Z",
            "finished_at": "2026-11-17T00:00:01Z",
            "inputs_moved_during_run": false
        },
        "freshness": { "policy": "input-digest", "state": "unknown" }
    }))
    .expect("valid fixture")
}

#[test]
fn test_parse_canonical_noncanonical_or_unknown_major_refused_minor_preserved() {
    let fixture = fixture();
    let canonical = fixture.to_canonical_json().expect("render");
    let text = std::str::from_utf8(&canonical).expect("UTF-8");
    assert!(text.starts_with("{\n  \"figure\": \"example\",\n"));
    assert!(text.ends_with(
        "  \"value\": {\n    \"a\": {\n      \"b\": 1,\n      \"y\": 3\n    },\n    \"z\": 2\n  }\n}\n"
    ));
    assert!(!text.contains("heavy_gate"));
    assert_eq!(
        EvidenceEnvelope::parse_canonical(&canonical).expect("canonical fixture"),
        fixture
    );
    let unsupported = text.replace("clean.evidence/v1.0", "clean.evidence/v2.0");
    let error =
        EvidenceEnvelope::parse_canonical(unsupported.as_bytes()).expect_err("unknown major");
    assert!(error.to_string().contains("unsupported evidence schema"));

    let next_minor = text.replace("clean.evidence/v1.0", "clean.evidence/v1.1");
    let read =
        EvidenceEnvelope::parse_canonical(next_minor.as_bytes()).expect("known field layout");
    assert_eq!(
        read.to_canonical_json().expect("re-render"),
        next_minor.as_bytes()
    );
    // The minor-version rule: a field this reader does not know is refused,
    // whatever minor version the record names.
    let unknown_field = next_minor.replacen(
        "  \"figure\": \"example\",\n",
        "  \"figure\": \"example\",\n  \"future_field\": 1,\n",
        1,
    );
    assert_ne!(unknown_field, next_minor, "the planted field was inserted");
    assert!(matches!(
        EvidenceEnvelope::parse_canonical(unknown_field.as_bytes()),
        Err(EnvelopeError::Json(_))
    ));

    let compact = serde_json::to_vec(&fixture).expect("compact JSON");
    assert!(matches!(
        EvidenceEnvelope::parse_canonical(&compact),
        Err(EnvelopeError::Noncanonical)
    ));
}

#[test]
fn test_to_canonical_json_partial_rows_or_nonfinite_measurement_refused() {
    let mut fixture = fixture();
    fixture.rows_file = Some("rows.json".to_owned());
    assert!(matches!(
        fixture.to_canonical_json(),
        Err(EnvelopeError::IncompleteRowsBinding)
    ));
    fixture.rows_sha256 = Some("pin".to_owned());
    fixture.provenance.heavy_gate = Some(HeavyGateObservation {
        label: "example".to_owned(),
        reserved_gb: 4.0,
        peak_gb: f64::NAN,
    });
    assert!(matches!(
        fixture.to_canonical_json(),
        Err(EnvelopeError::InvalidMemoryObservation)
    ));
}

#[test]
fn test_rfc3339_utc_known_instants_rendered_exactly() {
    assert_eq!(rfc3339_utc(0), "1970-01-01T00:00:00Z");
    assert_eq!(rfc3339_utc(951_782_400), "2000-02-29T00:00:00Z");
    assert_eq!(rfc3339_utc(1_795_478_399), "2026-11-23T23:59:59Z");
    assert_eq!(rfc3339_utc(4_107_542_400), "2100-03-01T00:00:00Z");
}
