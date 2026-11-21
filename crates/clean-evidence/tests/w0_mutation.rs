// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opt-in replay of the tracked W0 mutation receipt against its pinned Git tree.

use serde_json::{json, Value};
use std::fs;
use std::path::Path;
use std::process::{Command, Output};

const RECEIPT: &str = "reports/evidence-ev2-w0-comparator-mutation-2026-11-18/receipt.json";
const SUCCESS: &[u8] =
    b"W0_MUTATION_RECEIPT=ok source=71037af51ca3cce033a71f6adf9efe40a872a49b fixtures=142\n";
const COMPARE_SOURCE: &str = "crates/clean-cli/src/cmd_evidence/w0_scoreboard.rs";
const REPLAY_TEST: &str = "crates/clean/tests/w0_scoreboard_cli.rs";

fn command(repo: &Path, cwd: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean-evidence"));
    command
        .current_dir(cwd)
        .args(["check", "w0-mutation", "--repo-root"])
        .arg(repo);
    command
}

fn run(repo: &Path, cwd: &Path, receipt: Option<&Path>) -> Output {
    let mut command = command(repo, cwd);
    if let Some(path) = receipt {
        command.arg("--receipt").arg(path);
    }
    command.output().expect("run W0 mutation receipt check")
}

fn expect_exit(label: &str, output: Output, expected: i32) {
    let diagnostic = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(expected),
        "{label}: stdout={:?}, stderr={diagnostic}",
        String::from_utf8_lossy(&output.stdout),
    );
    if expected == 0 {
        assert_eq!(output.stdout.as_slice(), SUCCESS, "{label}");
        assert!(output.stderr.is_empty(), "{label}: {diagnostic}");
    } else {
        assert!(output.stdout.is_empty(), "{label} printed to stdout");
        assert!(!output.stderr.is_empty(), "{label} lacked a diagnostic");
    }
}

fn json_bytes(value: &Value) -> Vec<u8> {
    let mut bytes = serde_json::to_vec_pretty(value).expect("serialize receipt control");
    bytes.push(b'\n');
    bytes
}

#[test]
#[ignore = "requires the historical W0 mutation source revision"]
fn w0_mutation_receipt_replays_pinned_git_artifacts_and_refuses_mutations() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("Clean checkout with the historical source revision");
    let unrelated = tempfile::tempdir().expect("unrelated working directory");
    let controls = tempfile::tempdir().expect("receipt override directory");
    let tracked = repo.join(RECEIPT);
    let saved = fs::read(&tracked).expect("tracked W0 mutation receipt");
    let document: Value = serde_json::from_slice(&saved).expect("tracked receipt JSON");
    assert_eq!(json_bytes(&document), saved, "canonical tracked receipt");

    expect_exit("tracked receipt", run(&repo, unrelated.path(), None), 0);
    expect_exit(
        "relative receipt override",
        run(&repo, unrelated.path(), Some(Path::new(RECEIPT))),
        0,
    );
    let copied = controls.path().join("original.json");
    fs::write(&copied, &saved).expect("copy tracked receipt to an absolute override");
    expect_exit(
        "absolute receipt override",
        run(&repo, unrelated.path(), Some(&copied)),
        0,
    );
    assert_eq!(fs::read(&copied).expect("preserved copied receipt"), saved);

    let override_path = controls.path().join("mutated.json");
    let reject = |label: &str, changed: &[u8]| {
        assert_ne!(
            changed,
            saved.as_slice(),
            "{label} did not mutate the receipt"
        );
        fs::write(&override_path, changed).expect("write disposable receipt control");
        expect_exit(label, run(&repo, unrelated.path(), Some(&override_path)), 1);
        assert_eq!(
            fs::read(&override_path).expect("preserved mutation control"),
            changed,
            "{label}",
        );
    };

    reject("malformed JSON", b"{\n");
    reject(
        "positional receipt instead of an object",
        &json_bytes(&json!([document])),
    );
    let text = std::str::from_utf8(&saved).expect("canonical receipt UTF-8");
    let duplicate = text.replacen(
        "{\n",
        "{\n  \"schema\": \"clean.w0_comparator_mutation.v1\",\n",
        1,
    );
    assert_eq!(
        serde_json::from_str::<Value>(&duplicate).expect("JSON with repeated schema key"),
        document,
    );
    reject("duplicate schema key", duplicate.as_bytes());

    let mut wrong_exit = document.clone();
    wrong_exit["phases"]["mutant"]["replay_exit"] = json!(0);
    reject("mutant replay reported success", &json_bytes(&wrong_exit));
    let mut wrong_failure = document.clone();
    wrong_failure["phases"]["mutant"]["replay_failure"]["file"] = json!(COMPARE_SOURCE);
    reject(
        "mutant failure attached to a different source",
        &json_bytes(&wrong_failure),
    );

    let forged_pin = "0".repeat(64);
    for source in [COMPARE_SOURCE, REPLAY_TEST] {
        let mut wrong_pin = document.clone();
        assert!(
            wrong_pin["source_files_sha256"][source].is_string(),
            "{source}"
        );
        wrong_pin["source_files_sha256"][source] = json!(forged_pin);
        reject(source, &json_bytes(&wrong_pin));
    }

    for member in [
        "data/kcheck_island_gaps.json",
        "theories/cic_l/CICL/ConstructorUniverse.lean",
        "theories/kcheck_labelled/KCheck/AdmissionControls.lean",
    ] {
        let mut incomplete = document.clone();
        assert!(
            incomplete["fixture_paths_sha256"]
                .as_object_mut()
                .expect("fixture digest map")
                .remove(member)
                .is_some(),
            "{member}",
        );
        reject(member, &json_bytes(&incomplete));
    }

    let mut wrong_fixture = document.clone();
    wrong_fixture["fixture_paths_sha256"]["data/self_proof_scoreboard.json"] = json!(forged_pin);
    reject("changed saved board digest", &json_bytes(&wrong_fixture));
    let mut wrong_lowered = document.clone();
    wrong_lowered["lowered_board"]["sha256"] = json!(forged_pin);
    reject("changed lowered board digest", &json_bytes(&wrong_lowered));

    let missing = controls.path().join("missing.json");
    expect_exit(
        "missing receipt override",
        run(&repo, unrelated.path(), Some(&missing)),
        3,
    );
    assert!(!missing.exists(), "check created a missing receipt");
    expect_exit(
        "missing override argument",
        command(&repo, unrelated.path())
            .arg("--receipt")
            .output()
            .expect("run malformed command"),
        2,
    );
    assert_eq!(
        fs::read(&tracked).expect("preserved tracked receipt"),
        saved
    );
    assert_eq!(fs::read(&copied).expect("preserved copied receipt"), saved);
    assert_eq!(fs::read_dir(controls.path()).unwrap().count(), 2);
    assert_eq!(fs::read_dir(unrelated.path()).unwrap().count(), 0);
}
