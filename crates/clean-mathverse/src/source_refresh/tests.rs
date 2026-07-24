// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use super::*;

/// Verify that the real mathverse_sources.toml in data/ parses correctly.
#[test]
fn test_parse_real_manifest() {
    let manifest_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../data/mathverse_sources.toml");
    if !manifest_path.exists() {
        eprintln!("SKIP: manifest not found at {}", manifest_path.display());
        return;
    }
    let manifest = load_manifest(&manifest_path).expect("should parse manifest");
    assert_eq!(
        manifest.sources.len(),
        16,
        "expected 16 sources (14 original + Lean 3 mathlib3 + Coq stdlib 8.20.0)"
    );

    for source in &manifest.sources {
        assert!(!source.name.is_empty());
        assert!(
            source.git_url.starts_with("https://"),
            "bad url: {}",
            source.git_url
        );
        assert!(
            source.file_type.starts_with('.'),
            "bad type: {}",
            source.file_type
        );
        assert!(
            (1..=5).contains(&source.import_tier),
            "bad tier: {}",
            source.import_tier
        );
        assert!(!source.clone_path.is_empty());
    }
}

/// Verify manifest round-trip: parse -> serialize -> parse.
#[test]
fn test_manifest_round_trip() {
    let toml_text = r#"
[[source]]
name = "Test Source"
git_url = "https://github.com/test/repo"
file_type = ".lean"
import_tier = 2
clone_path = "/tmp/test-repo"
last_fetched_sha = "abc123"
last_fetched_date = "2026-04-10"
"#;
    let manifest = parse_manifest(toml_text).expect("parse");
    assert_eq!(manifest.sources.len(), 1);
    assert_eq!(manifest.sources[0].last_fetched_sha, "abc123");

    let serialized = toml::to_string_pretty(&manifest).expect("serialize");
    let reparsed = parse_manifest(&serialized).expect("re-parse");
    assert_eq!(reparsed.sources[0].name, "Test Source");
    assert_eq!(reparsed.sources[0].last_fetched_sha, "abc123");
}

/// Test staleness detection with a mock git repo.
#[test]
fn test_staleness_detection_with_mock_repo() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (upstream, clone, working) = setup_mock_repo(&tmp);

    // Before any new commit: should be up-to-date.
    let manifest = mock_manifest(&upstream, &clone);
    let report = check_staleness(&manifest);
    assert_eq!(report.stale_count, 0, "should not be stale yet");
    assert_eq!(report.up_to_date_count, 1);

    // Push a new commit to upstream.
    push_new_commit(&working, "new.txt", "world", "second commit");

    // Now should be stale.
    let report2 = check_staleness(&manifest);
    assert_eq!(report2.stale_count, 1, "should be stale after new commit");
    let status = &report2.statuses[0];
    assert!(status.clone_exists);
    assert!(status.is_stale);
    assert_ne!(status.local_sha, status.remote_sha);
}

/// Test fetch_updates updates the manifest SHA.
#[test]
fn test_fetch_updates_with_mock_repo() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let (upstream, clone, working) = setup_mock_repo(&tmp);
    let original_sha = get_local_head(&clone).expect("local head");

    // Push a new commit.
    push_new_commit(&working, "new.txt", "world", "second commit");

    let mut manifest = mock_manifest(&upstream, &clone);
    manifest.sources[0].last_fetched_sha = original_sha.clone();

    let results = fetch_updates(&mut manifest);
    assert_eq!(results.len(), 1);
    assert!(results[0].success, "fetch should succeed");
    assert_ne!(results[0].new_sha, original_sha);
    assert!(!results[0].new_sha.is_empty());
    assert_eq!(manifest.sources[0].last_fetched_sha, results[0].new_sha);
    assert!(!manifest.sources[0].last_fetched_date.is_empty());

    let report = check_staleness(&manifest);
    assert_eq!(report.stale_count, 0, "should be up-to-date after fetch");
}

/// Test detection of missing clone (not yet downloaded).
#[test]
fn test_missing_clone_detected_as_stale() {
    let manifest = SourceManifest {
        sources: vec![SourceEntry {
            name: "NonExistent".to_string(),
            git_url: "https://github.com/nonexistent/nonexistent".to_string(),
            file_type: ".lean".to_string(),
            import_tier: 5,
            clone_path: "/tmp/definitely-does-not-exist-mathverse-test".to_string(),
            last_fetched_sha: String::new(),
            last_fetched_date: String::new(),
        }],
    };
    let status = &check_staleness(&manifest).statuses[0];
    assert!(!status.clone_exists);
    assert!(status.is_stale);
}

/// Test manifest save/load round-trip to disk.
#[test]
fn test_manifest_save_load_round_trip() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("test_sources.toml");
    let manifest = SourceManifest {
        sources: vec![
            make_entry(
                "Source A",
                "https://github.com/a/a",
                ".lean",
                2,
                "/tmp/a",
                "deadbeef",
                "2026-04-16",
            ),
            make_entry(
                "Source B",
                "https://github.com/b/b",
                ".v",
                3,
                "/tmp/b",
                "",
                "",
            ),
        ],
    };
    save_manifest(&manifest, &path).expect("save");
    let loaded = load_manifest(&path).expect("load");
    assert_eq!(loaded.sources.len(), 2);
    assert_eq!(loaded.sources[0].last_fetched_sha, "deadbeef");
    assert!(loaded.sources[1].last_fetched_sha.is_empty());
}

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn make_entry(
    name: &str,
    url: &str,
    ft: &str,
    tier: u8,
    cp: &str,
    sha: &str,
    date: &str,
) -> SourceEntry {
    SourceEntry {
        name: name.to_string(),
        git_url: url.to_string(),
        file_type: ft.to_string(),
        import_tier: tier,
        clone_path: cp.to_string(),
        last_fetched_sha: sha.to_string(),
        last_fetched_date: date.to_string(),
    }
}

/// Create a bare upstream, a working copy, and a shallow clone. Returns (upstream, clone, working).
fn setup_mock_repo(tmp: &tempfile::TempDir) -> (PathBuf, PathBuf, PathBuf) {
    let upstream = tmp.path().join("upstream.git");
    let clone = tmp.path().join("clone");
    let working = tmp.path().join("working");

    run_git(&upstream, &["init", "--bare"]);
    Command::new("git")
        .args([
            "clone",
            upstream.to_str().unwrap(),
            working.to_str().unwrap(),
        ])
        .output()
        .expect("clone working");
    run_git_in(&working, &["config", "user.email", "test@test.com"]);
    run_git_in(&working, &["config", "user.name", "Test"]);
    std::fs::write(working.join("init.txt"), "hello").expect("write");
    run_git_in(&working, &["add", "init.txt"]);
    run_git_in(&working, &["commit", "-m", "initial"]);
    run_git_in(&working, &["push", "origin", "HEAD"]);

    Command::new("git")
        .args([
            "clone",
            "--depth",
            "1",
            upstream.to_str().unwrap(),
            clone.to_str().unwrap(),
        ])
        .output()
        .expect("clone");
    (upstream, clone, working)
}

fn mock_manifest(upstream: &Path, clone: &Path) -> SourceManifest {
    SourceManifest {
        sources: vec![SourceEntry {
            name: "MockSource".to_string(),
            git_url: upstream.to_str().unwrap().to_string(),
            file_type: ".txt".to_string(),
            import_tier: 5,
            clone_path: clone.to_str().unwrap().to_string(),
            last_fetched_sha: String::new(),
            last_fetched_date: String::new(),
        }],
    }
}

fn push_new_commit(working: &Path, file: &str, content: &str, msg: &str) {
    std::fs::write(working.join(file), content).expect("write");
    run_git_in(working, &["add", file]);
    run_git_in(working, &["commit", "-m", msg]);
    run_git_in(working, &["push", "origin", "HEAD"]);
}

fn run_git(dir: &Path, args: &[&str]) {
    let _ = std::fs::create_dir_all(dir);
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .output()
        .expect("git");
    assert!(
        out.status.success(),
        "git {:?} in {}: {}",
        args,
        dir.display(),
        String::from_utf8_lossy(&out.stderr)
    );
}

fn run_git_in(dir: &Path, args: &[&str]) {
    let out = Command::new("git")
        .args(args)
        .current_dir(dir)
        .output()
        .expect("git");
    assert!(
        out.status.success(),
        "git {:?} in {}: {}",
        args,
        dir.display(),
        String::from_utf8_lossy(&out.stderr)
    );
}
