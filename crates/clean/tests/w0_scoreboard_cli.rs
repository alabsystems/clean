// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replay a fixed W0 fixture and optionally the live checkout with the built CLI.

use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Output};

const BOARD: &str = "data/self_proof_scoreboard.json";
const RECEIPT: &str = "data/kcheck_coverage.json";
const ADVICE: &str = "data/kcheck_coverage/prelude_roots.advice.bin";
const TRANSCRIPT: &str = "data/kcheck_coverage/prelude_roots.transcript.txt";
const EXPORT: &str =
    "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/prelude_roots.ndjson.gz";
const CLEAN_P3: &str = "reports/self-proof-p3-2026-11-12/patched_kernel_control.json";
const C3: &str = "theories/kcheck_labelled";
const INPUTS: &[&str] = &[
    BOARD,
    RECEIPT,
    ADVICE,
    TRANSCRIPT,
    EXPORT,
    CLEAN_P3,
    "reports/self-proof-p3-2026-11-12/patched_kernel_control_trust.json",
    "reports/self-proof-elab/baseline.json",
    "data/cic_l_rule_inventory.json",
    "data/kcheck_island_gaps.json",
];
const FIXTURE: &[(&str, &[u8])] = &[
    (BOARD, include_bytes!("fixtures/w0_scoreboard/board.json")),
    (
        RECEIPT,
        include_bytes!("fixtures/w0_scoreboard/coverage.json"),
    ),
    (ADVICE, include_bytes!("fixtures/w0_scoreboard/advice.bin")),
    (
        TRANSCRIPT,
        include_bytes!("fixtures/w0_scoreboard/transcript.txt"),
    ),
    (
        EXPORT,
        include_bytes!("fixtures/w0_scoreboard/prelude_roots.ndjson.gz"),
    ),
    (
        CLEAN_P3,
        include_bytes!("fixtures/w0_scoreboard/clean-p3.json"),
    ),
    (
        "theories/kcheck_run/KCheckRun.lean",
        include_bytes!("fixtures/w0_scoreboard/KCheckRun.lean"),
    ),
    (
        "theories/kcheck_run/KCheckRunMain.lean",
        include_bytes!("fixtures/w0_scoreboard/KCheckRunMain.lean"),
    ),
    (
        "theories/kcheck_run/lean-toolchain",
        include_bytes!("fixtures/w0_scoreboard/lean-toolchain"),
    ),
];
const CHECK: &[&str] = &["status", "--scoreboard", "--check"];
const RENDER: &[&str] = &["status", "--scoreboard", "--json"];
const TEXT: &[&str] = &["status", "--scoreboard"];
const SUCCESS: &[u8] = b"SELF_PROOF_SCOREBOARD=ok the record matches its sources\n";
const BOARD_MISMATCH: &str = "data/self_proof_scoreboard.json differs from a re-derivation";
const STALE: &str = "stale or absent: the Lean sources of the recorded run have moved; re-mint with scripts/kcheck_coverage.py --write";
const MISSING_K3: &str = "stale or absent: data/kcheck_coverage.json does not exist";

fn invoke(root: &Path, cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_clean"))
        .current_dir(cwd)
        .arg("evidence")
        .args(args)
        .arg("--repo-root")
        .arg(root)
        .output()
        .expect("run the checkout-built Clean CLI")
}

fn succeeded(output: Output) -> Vec<u8> {
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "expected success, got {}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
    );
    output.stdout
}

fn refused(output: Output, needle: &str) {
    let diagnostic = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{diagnostic}");
    assert!(output.stdout.is_empty(), "refusal printed to stdout");
    assert!(
        diagnostic.contains(needle),
        "expected refusal mentioning {needle:?}, got {diagnostic}"
    );
}

fn collect_lean(root: &Path, relative: &Path, paths: &mut BTreeSet<PathBuf>) {
    for entry in fs::read_dir(root.join(relative)).expect("read checker source directory") {
        let entry = entry.expect("read checker source entry");
        let name = entry.file_name();
        if name == ".lake" {
            continue;
        }
        let path = relative.join(name);
        let kind = entry.file_type().expect("inspect checker source entry");
        if kind.is_dir() {
            collect_lean(root, &path, paths);
        } else if kind.is_file() && path.extension().is_some_and(|ext| ext == "lean") {
            paths.insert(path);
        }
    }
}

struct Snapshot<'a> {
    root: tempfile::TempDir,
    cwd: &'a Path,
    files: BTreeMap<PathBuf, Vec<u8>>,
}

impl<'a> Snapshot<'a> {
    fn copy(repo: &Path, cwd: &'a Path, receipt: &Value) -> Self {
        let mut paths: BTreeSet<_> = INPUTS.iter().copied().map(PathBuf::from).collect();
        for relative in receipt["sources"]
            .as_object()
            .expect("K3 source pins")
            .keys()
        {
            let path = PathBuf::from(relative);
            assert!(path.starts_with("theories"));
            assert!(path
                .components()
                .all(|part| matches!(part, Component::Normal(_))));
            paths.insert(path);
        }
        collect_lean(repo, Path::new(C3), &mut paths);
        let files = paths
            .into_iter()
            .map(|relative| {
                let original = repo.join(&relative);
                let bytes = fs::read(&original)
                    .unwrap_or_else(|error| panic!("read {}: {error}", original.display()));
                (relative, bytes)
            })
            .collect();
        Self::materialize(cwd, files)
    }

    fn materialize(cwd: &'a Path, files: BTreeMap<PathBuf, Vec<u8>>) -> Self {
        let root = tempfile::tempdir().expect("disposable W0 source snapshot");
        for (relative, bytes) in &files {
            let target = root.path().join(relative);
            fs::create_dir_all(target.parent().expect("fixture input parent"))
                .expect("create snapshot directory");
            fs::write(&target, bytes)
                .unwrap_or_else(|error| panic!("copy {}: {error}", target.display()));
        }
        Self { root, cwd, files }
    }

    fn replace(&mut self, relative: &str, bytes: Vec<u8>) {
        let expected = self
            .files
            .get_mut(Path::new(relative))
            .expect("edit a copied fixture input");
        let path = self.root.path().join(relative);
        fs::write(&path, &bytes).unwrap_or_else(|error| panic!("edit {}: {error}", path.display()));
        *expected = bytes;
    }

    fn run(&self, args: &[&str]) -> Output {
        let output = invoke(self.root.path(), self.cwd, args);
        for (relative, expected) in &self.files {
            let path = self.root.path().join(relative);
            let actual = fs::read(&path)
                .unwrap_or_else(|error| panic!("re-read {}: {error}", path.display()));
            assert!(
                &actual == expected,
                "evidence {args:?} changed fixture input {}",
                relative.display(),
            );
        }
        output
    }
}

fn json_bytes(value: &Value) -> Vec<u8> {
    let mut data = serde_json::to_vec_pretty(value).expect("serialize test mutation");
    data.push(b'\n');
    data
}

fn assert_k3_text(snapshot: &Snapshot<'_>, decided: &str, accepted: &str) {
    let text = String::from_utf8(succeeded(snapshot.run(TEXT))).expect("W0 text is UTF-8");
    let mut lines = text
        .strip_suffix('\n')
        .expect("W0 text final LF")
        .split('\n');
    assert_eq!(lines.nth(3), Some(decided));
    assert_eq!(lines.next(), Some(accepted));
}

fn assert_k3_absence(snapshot: &mut Snapshot<'_>, board: &Value, reason: &str) {
    refused(snapshot.run(CHECK), BOARD_MISMATCH);
    assert_k3_text(
        snapshot,
        &format!("  decided by compiled kcheck  : ABSENT ({reason})"),
        &format!("  accepted by kcheck, no site : ABSENT ({reason})"),
    );
    let mut expected = board.clone();
    expected["headline"]["decided_by_compiled_kcheck"] = json!({"absent": reason});
    expected["route"]["accepted_by_kcheck_no_site"] = json!({"absent": reason});
    let rendered = succeeded(snapshot.run(RENDER));
    let actual: Value = serde_json::from_slice(&rendered).expect("W0 absence JSON");
    assert_eq!(actual, expected, "only the two K3 rows may change");
    snapshot.replace(BOARD, rendered);
    assert_eq!(succeeded(snapshot.run(CHECK)), SUCCESS);
}

fn change_first_accepted_depth(advice: &mut [u8], syntax: &Value, receipt: &Value) {
    let lengths = syntax["frame_lengths"].as_array().expect("frame lengths");
    let rows = syntax["declarations"].as_array().expect("declaration rows");
    assert_eq!(lengths.len(), rows.len());
    let mut offset = 0;
    for (length, row) in lengths.iter().zip(rows) {
        let length = usize::try_from(length.as_u64().expect("byte length")).expect("frame size");
        let groups = (usize::BITS - length.leading_zeros()).div_ceil(7).max(1);
        offset += groups as usize;
        if row["class"] == "accepted" {
            let record_line = &receipt["figures"]["accepted_declarations"][0]["line"];
            assert_eq!(
                row["line"].as_str().expect("row line"),
                record_line.to_string(),
            );
            let frame = &mut advice[offset..offset + length];
            assert!(
                frame.len() >= 2 && frame[0] == 0x01,
                "expected a DEPTH token"
            );
            // Preserve the operand's continuation bit and all token boundaries.
            frame[1] ^= 1;
            return;
        }
        offset += length;
    }
    panic!("the replay requires a recorded accepted frame");
}

fn replay(snapshot: &mut Snapshot<'_>) {
    let board = snapshot.files[Path::new(BOARD)].clone();
    let receipt_bytes = snapshot.files[Path::new(RECEIPT)].clone();
    let receipt: Value = serde_json::from_slice(&receipt_bytes).expect("K3 receipt JSON");
    assert_eq!(succeeded(snapshot.run(CHECK)), SUCCESS);
    let original_board: Value = serde_json::from_slice(&board).expect("W0 board JSON");

    let mut lowered = original_board.clone();
    let minted = &mut lowered["headline"]["planted_false_mints_clean"]["minted_under_mutant"];
    *minted = json!(minted
        .as_u64()
        .and_then(|count| count.checked_sub(1))
        .expect("positive recorded Clean P3 mint count"));
    snapshot.replace(BOARD, json_bytes(&lowered));
    refused(snapshot.run(CHECK), BOARD_MISMATCH);

    let mut unqualified = original_board.clone();
    assert!(unqualified["route"]["accepted_by_kcheck_no_site"]["labels"]
        .as_object_mut()
        .expect("K3 board labels")
        .remove("site")
        .is_some());
    snapshot.replace(BOARD, json_bytes(&unqualified));
    refused(snapshot.run(CHECK), BOARD_MISMATCH);

    let mut unqualified_receipt = receipt.clone();
    assert!(unqualified_receipt["labels"]
        .as_object_mut()
        .expect("K3 receipt labels")
        .remove("site")
        .is_some());
    snapshot.replace(BOARD, board.clone());
    snapshot.replace(RECEIPT, json_bytes(&unqualified_receipt));
    refused(snapshot.run(CHECK), "labels are not the ones");

    for (bytes, diagnostic) in [
        (
            br#"{"advice":"#.as_slice(),
            "data/kcheck_coverage.json: EOF while parsing a value",
        ),
        (b"{\xff}", "data/kcheck_coverage.json is not UTF-8"),
        (
            br#"{"advice":{"origin":"\ud800"}}"#,
            "data/kcheck_coverage.json: unexpected end of hex escape",
        ),
    ] {
        snapshot.replace(RECEIPT, bytes.to_vec());
        for args in [TEXT, RENDER, CHECK, &["status", "--scoreboard", "--write"]] {
            refused(snapshot.run(args), diagnostic);
        }
    }
    snapshot.replace(RECEIPT, receipt_bytes);

    let figures = &receipt["figures"];
    assert_k3_text(
        snapshot,
        "  decided by compiled kcheck  : 0 real declarations",
        &format!(
            concat!(
                "  accepted by kcheck, no site : {} of {} in the fragment, of {} real declarations ",
                "(the run claims no soundness; built by upstream Lean; interim loader)"
            ),
            figures["accepted"], figures["inside_fragment"], figures["ordinary_declarations"],
        ),
    );

    let no_lf = board.strip_suffix(b"\n").expect("canonical final LF");
    snapshot.replace(BOARD, no_lf.to_vec());
    refused(snapshot.run(CHECK), BOARD_MISMATCH);
    let crlf = String::from_utf8(board.clone())
        .expect("canonical UTF-8")
        .replace('\n', "\r\n");
    snapshot.replace(BOARD, crlf.into_bytes());
    refused(snapshot.run(CHECK), BOARD_MISMATCH);
    snapshot.replace(BOARD, board.clone());

    let syntax: Value = serde_json::from_slice(&succeeded(
        snapshot.run(&["check-k3-packet-syntax", "--json"]),
    ))
    .expect("K3 packet syntax");
    let advice = snapshot.files[Path::new(ADVICE)].clone();
    let mut modified_advice = advice.clone();
    change_first_accepted_depth(&mut modified_advice, &syntax, &receipt);
    snapshot.replace(ADVICE, modified_advice);
    let figures: Value = serde_json::from_slice(&succeeded(
        snapshot.run(&["check-k3-packet-syntax", "--coverage-figures"]),
    ))
    .expect("figures from a packet with the same flags");
    let mut expected_figures = receipt["figures"].clone();
    let changed = &figures["accepted_declarations"][0]["advice_frame_sha256"];
    let original = &mut expected_figures["accepted_declarations"][0]["advice_frame_sha256"];
    assert!(changed.as_str().is_some());
    assert_ne!(&*original, changed);
    *original = changed.clone();
    assert_eq!(figures, expected_figures);
    refused(
        snapshot.run(CHECK),
        "data/kcheck_coverage.json differs from a re-derivation",
    );
    snapshot.replace(ADVICE, advice);

    let moved = receipt["sources"]
        .as_object()
        .expect("K3 source pins")
        .keys()
        .find(|path| path.ends_with(".lean") && !Path::new(path).starts_with(C3))
        .expect("a pinned Lean source outside the C3 scan");
    let source = snapshot.files[Path::new(moved)].clone();
    let mut moved_source = source.clone();
    moved_source.extend_from_slice(b"\n-- moved by the native W0 replay\n");
    snapshot.replace(moved, moved_source);
    assert_k3_absence(snapshot, &original_board, STALE);

    snapshot.replace(moved, source);
    snapshot.replace(BOARD, board);
    assert_eq!(succeeded(snapshot.run(CHECK)), SUCCESS);
}

#[test]
fn w0_scoreboard_self_test() {
    let unrelated = tempfile::tempdir().expect("unrelated working directory");
    let files: BTreeMap<_, _> = FIXTURE
        .iter()
        .map(|(relative, bytes)| (PathBuf::from(*relative), bytes.to_vec()))
        .collect();
    let mut snapshot = Snapshot::materialize(unrelated.path(), files.clone());
    replay(&mut snapshot);

    let mut without_receipt = files;
    assert!(without_receipt.remove(Path::new(RECEIPT)).is_some());
    let board =
        serde_json::from_slice(&without_receipt[Path::new(BOARD)]).expect("W0 fixture board");
    let mut missing = Snapshot::materialize(unrelated.path(), without_receipt);
    assert_k3_absence(&mut missing, &board, MISSING_K3);
    assert!(!missing.root.path().join(RECEIPT).exists());
}

#[test]
#[ignore = "requires the current W0 source artifacts for the opt-in replay"]
fn w0_scoreboard_replays_checkout_artifacts_and_refuses_mutations() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("Clean checkout");
    let unrelated = tempfile::tempdir().expect("unrelated working directory");
    let board = fs::read(repo.join(BOARD)).expect("current W0 board");
    let receipt_bytes = fs::read(repo.join(RECEIPT)).expect("current K3 receipt");
    let receipt: Value = serde_json::from_slice(&receipt_bytes).expect("K3 receipt JSON");
    assert_eq!(succeeded(invoke(&repo, unrelated.path(), CHECK)), SUCCESS);
    assert_eq!(
        fs::read(repo.join(BOARD)).expect("preserved W0 board"),
        board
    );
    assert_eq!(
        fs::read(repo.join(RECEIPT)).expect("preserved K3 receipt"),
        receipt_bytes,
    );
    replay(&mut Snapshot::copy(&repo, unrelated.path(), &receipt));
}
