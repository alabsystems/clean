// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_evidence::envelope::{EvidenceEnvelope, FreshnessPolicy, FreshnessState, TreeState};
use clean_evidence::trustcore::{
    DENY_SORRY_SCHEMA, DIGEST_MODULE_SOURCE, DIGEST_SOURCE, FIGURE, GATE_COMMAND, KERNEL_SCHEMA,
    MODULE_FILE, MODULE_TREE_KEY, PRODUCER_ID,
};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{
    fs,
    path::Path,
    process::{Command, Output},
};

const FILE_PIN: &str = "73d21d9bb7794e9cf7f0d41ffb9ec12d1fc15bdab301168cb147330ab3c31596";
const TREE_PIN: &str = "ea99c055e30f9f568e10766a7ab452a6d7a9c87ed3a6a26613da56d2fa75c42d";
const DIGEST_PIN: &str = "979852919c35a4158d06ea4a66f529e1b5f51160313ebb36eaa4617f4aa56b87";
const DIGEST_MODULE_PIN: &str = "f981b2a8d82b4efa20998db3efba938a7d1f169b87a863d57a9f292b28bc1393";
const KERNEL_REPORT: &str = "reports/kernel-soundness-launch-evidence.json";
const DENY_REPORT: &str = "reports/deny-sorry-launch-evidence.json";
const AXIOM_REPORT: &str = "reports/axiom-audit-launch-evidence.json";
const MODULE_DIR: &str = "crates/clean-cli/src/cmd_replacement";

fn write(root: &Path, path: &str, bytes: impl AsRef<[u8]>) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
}

fn fixture(root: &Path) {
    write(root, MODULE_FILE, b"mod gate;\n");
    write(root, DIGEST_SOURCE, b"fn hash() {}\n");
    write(root, DIGEST_MODULE_SOURCE, b"pub mod digest;\n");
    write(root, &format!("{MODULE_DIR}/nested/zeta.rs"), b"abc\0xyz");
    write(root, &format!("{MODULE_DIR}/alpha.rs"), b"a\n");
    write(root, &format!("{MODULE_DIR}/tests/control.rs"), b"excluded");
    write(root, &format!("{MODULE_DIR}/.rs"), b"not a Rust extension");
    write(root, &format!("{MODULE_DIR}/note.txt"), b"excluded");
    #[cfg(unix)]
    std::os::unix::fs::symlink("alpha.rs", root.join(MODULE_DIR).join("alias.rs")).unwrap();

    for (report, schema) in [
        (KERNEL_REPORT, KERNEL_SCHEMA),
        (DENY_REPORT, DENY_SORRY_SCHEMA),
    ] {
        let artifact = json!({
            "schema_version": schema,
            "source_sha256": {
                MODULE_FILE: FILE_PIN,
                MODULE_TREE_KEY: TREE_PIN,
                DIGEST_SOURCE: DIGEST_PIN,
                DIGEST_MODULE_SOURCE: DIGEST_MODULE_PIN,
            }
        });
        write(root, report, artifact.to_string());
    }
    let optional = json!({ "source_sha256": { MODULE_FILE: FILE_PIN } });
    write(root, AXIOM_REPORT, optional.to_string());
}

fn run(root: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_clean-evidence"))
        .args(["check", "trustcore-staleness", "--repo-root"])
        .arg(root)
        .output()
        .unwrap()
}

fn assert_stale(root: &Path, reason: &str) {
    let out = run(root);
    assert_eq!(out.status.code(), Some(1));
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.ends_with("TRUSTCORE_STALENESS=stale\n"), "{stdout}");
    assert!(stdout.contains(reason), "{stdout}");
}

#[test]
fn test_trustcore_staleness_fresh_pins_then_source_mutations_reported_stale() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    fixture(root);
    let fresh = run(root);
    let stdout = String::from_utf8(fresh.stdout).unwrap();
    assert_eq!(fresh.status.code(), Some(0), "{stdout}");
    assert!(
        stdout.contains(FILE_PIN) && stdout.contains(TREE_PIN),
        "{stdout}"
    );
    assert!(stdout.ends_with("TRUSTCORE_STALENESS=fresh\n"), "{stdout}");

    write(root, &format!("{MODULE_DIR}/tests/control.rs"), b"changed");
    assert!(run(root).status.success());

    write(root, DIGEST_SOURCE, b"fn changed() {}\n");
    assert_stale(root, &format!("{KERNEL_REPORT}: pins {DIGEST_SOURCE}"));
    write(root, DIGEST_SOURCE, b"fn hash() {}\n");
    write(root, DIGEST_MODULE_SOURCE, b"mod replacement;\n");
    assert_stale(root, &format!("{DENY_REPORT}: pins {DIGEST_MODULE_SOURCE}"));
    write(root, DIGEST_MODULE_SOURCE, b"pub mod digest;\n");
    assert!(run(root).status.success());

    write(root, &format!("{MODULE_DIR}/nested/zeta.rs"), b"changed");
    assert_stale(root, &format!("{KERNEL_REPORT}: pins module-tree digest"));
    write(root, MODULE_FILE, b"mod other;\n");
    assert_stale(root, &format!("{AXIOM_REPORT}: pins {MODULE_FILE}"));
}

#[test]
fn test_trustcore_staleness_missing_malformed_or_optional_pins_fail_closed() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    fixture(root);
    let mut receipt: serde_json::Value =
        serde_json::from_slice(&fs::read(root.join(DENY_REPORT)).unwrap()).unwrap();
    receipt["schema_version"] = json!("clean-deny-sorry-launch-evidence-v1");
    receipt["source_sha256"]
        .as_object_mut()
        .unwrap()
        .remove(DIGEST_SOURCE);
    write(root, DENY_REPORT, receipt.to_string());
    assert_stale(
        root,
        &format!("{DENY_REPORT}: expected schema_version {DENY_SORRY_SCHEMA}"),
    );
    assert_stale(
        root,
        &format!("{DENY_REPORT}: source_sha256 is missing {DIGEST_SOURCE}"),
    );

    write(
        root,
        DENY_REPORT,
        json!({ "source_sha256": { MODULE_FILE: FILE_PIN } }).to_string(),
    );
    assert_stale(
        root,
        &format!("{DENY_REPORT}: source_sha256 is missing the module-tree pin"),
    );
    write(
        root,
        AXIOM_REPORT,
        json!({ "source_sha256": { MODULE_FILE: FILE_PIN, MODULE_TREE_KEY: "wrong" } }).to_string(),
    );
    assert_stale(
        root,
        &format!("{AXIOM_REPORT}: pins module-tree digest wrong"),
    );
    write(root, KERNEL_REPORT, b"{invalid");
    assert_stale(root, &format!("{KERNEL_REPORT}: unreadable"));
    fs::remove_file(root.join(AXIOM_REPORT)).unwrap();
    assert_stale(root, &format!("{AXIOM_REPORT}: unreadable"));
    fs::remove_dir_all(root.join(MODULE_DIR)).unwrap();
    assert_stale(root, "FAIL: cannot hash the trust-core gate sources:");
}

fn git(root: &Path, args: &[&str]) -> String {
    let mut command = Command::new("git");
    command.current_dir(root).args([
        "-c",
        "user.name=Fixture",
        "-c",
        "user.email=fixture@example.invalid",
        "-c",
        "commit.gpgsign=false",
    ]);
    for variable in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
    ] {
        command.env_remove(variable);
    }
    let out = command.args(args).output().unwrap();
    assert!(out.status.success(), "git {args:?}: {out:?}");
    String::from_utf8(out.stdout).unwrap().trim_end().to_owned()
}

fn run_json(root: &Path) -> (Output, Vec<String>) {
    let argv = ["check", "trustcore-staleness", "--json", "--repo-root"];
    let out = Command::new(env!("CARGO_BIN_EXE_clean-evidence"))
        .args(argv)
        .arg(root)
        .output()
        .unwrap();
    let recorded = std::iter::once("clean-evidence")
        .chain(argv)
        .map(str::to_owned)
        .chain([root.to_str().unwrap().to_owned()])
        .collect();
    (out, recorded)
}

/// The `--json` record is the production caller of the evidence envelope: it
/// must read back canonically and carry the verdict, every hashed input and
/// the repository state it was measured over.
#[test]
fn test_trustcore_staleness_json_record_canonical_inputs_and_provenance_recorded() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    fixture(root);
    git(root, &["init", "-q"]);
    git(root, &["add", "-A"]);
    git(root, &["commit", "-qm", "fixture", "--no-verify"]);
    let head = git(root, &["rev-parse", "HEAD"]);

    let (out, argv) = run_json(root);
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    let record = EvidenceEnvelope::parse_canonical(&out.stdout).expect("canonical record");
    assert_eq!(record.figure, FIGURE);
    assert_eq!(record.gate_command, GATE_COMMAND);
    assert_eq!(record.freshness.policy, FreshnessPolicy::InputDigest);
    assert_eq!(record.freshness.state, FreshnessState::Fresh);
    assert_eq!(record.value, json!({ "state": "fresh", "findings": [] }));
    let provenance = &record.provenance;
    assert_eq!(provenance.clean_commit, head);
    assert_eq!(provenance.tree_state, TreeState::Clean);
    assert!(!provenance.inputs_moved_during_run);
    assert_eq!(provenance.producer.id, PRODUCER_ID);
    assert_eq!(provenance.producer.argv, argv);
    let producer = Sha256::digest(include_bytes!("../src/trustcore.rs"));
    let producer: String = producer.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(provenance.producer.module_digest, producer);
    let files = &provenance.inputs.files;
    for (input, pin) in [
        (MODULE_FILE, FILE_PIN),
        (MODULE_TREE_KEY, TREE_PIN),
        (DIGEST_SOURCE, DIGEST_PIN),
        (DIGEST_MODULE_SOURCE, DIGEST_MODULE_PIN),
    ] {
        assert_eq!(files.get(input).map(String::as_str), Some(pin), "{input}");
    }
    for report in [KERNEL_REPORT, DENY_REPORT, AXIOM_REPORT] {
        assert!(files.contains_key(report), "{report} is an input");
    }

    write(root, &format!("{MODULE_DIR}/nested/zeta.rs"), b"changed");
    let (out, _) = run_json(root);
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    let stale = EvidenceEnvelope::parse_canonical(&out.stdout).expect("canonical record");
    assert_eq!(stale.freshness.state, FreshnessState::Stale);
    assert_eq!(stale.provenance.tree_state, TreeState::Dirty);
    assert_ne!(stale.provenance.inputs.digest, provenance.inputs.digest);
    assert_eq!(stale.value["findings"][0]["kind"], "tree-pin-mismatch");
    assert_eq!(stale.value["findings"][0]["artifact"], KERNEL_REPORT);

    let (out, _) = run_json(&root.join("crates"));
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    assert!(out.stdout.is_empty(), "no record without provenance");
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("cannot observe the repository"), "{stderr}");
}

#[test]
fn test_trustcore_staleness_unknown_or_repeated_flag_usage_refused() {
    for args in [
        &["check", "trustcore-staleness", "--jsonx"][..],
        &["check", "trustcore-staleness", "--json", "--json"],
        &["check", "trustcore-staleness", "--repo-root"],
        &["check", "other"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_clean-evidence"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2), "{args:?}");
    }
}
