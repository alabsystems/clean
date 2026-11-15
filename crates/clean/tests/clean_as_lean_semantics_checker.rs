// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `trust-ir-self-declared/clean-as-lean-semantics-checker` — the proof-program
//! row behind finding F-110, ported in-repo as the WS6.12 ratchet.
//!
//! The row asked whether Clean can check trust-ir's own Lean semantics
//! (`lean/trust_ir-semantics`, Lean 4.8.0 + lake). Its recorded status was
//! `unknown`: a 2026-06-01 note said "kernel yes, elaborator not yet" from ONE
//! file and nothing re-measured it. WS6.12 re-measured it at package scale
//! (`scripts/trust_ir_semantics_probe.py`, artifacts under
//! `reports/trust-ir-semantics-probe/`): the answer is still NO — 6 of 49
//! files elaborate, and `authority_transfer_ready` is false. Lean 4.8.0 + lake
//! stays the authority; nothing here changes trust-ir.
//!
//! This file pins BOTH halves of that answer against the real `clean` binary,
//! so neither can drift silently:
//!
//! * **PASS half** — the row's own `test_idea` sample (`def f | .a => 1
//!   | .b => 2`, `theorem t : f .a = 1 := rfl`, `deriving Repr`) elaborates
//!   today. Per the ratchet convention a PASS row carries a right-reason
//!   negative twin (a FALSE theorem refused BY NAME, with everything else still
//!   counted) and a mutation control (an injected `sorry` is flagged in
//!   `trust_summary.sorry_axioms`, never counted as a success).
//! * **GAP half** — the elaborator gaps the probe filed
//!   (`reports/trust-ir-semantics-probe/repros/manifest.json`, G01..G24) must
//!   STILL fail, each with its filed signature. `closed` (a repro now passes)
//!   and `changed` (it fails for a different reason) both FAIL this test on
//!   purpose: the day a gap closes, the tracker entry
//!   (`docs/issues/2026-09-19-trust-ir-semantics-elaborator-gaps.md`) must be
//!   re-filed in the same change, not left stale. A gap that closed is
//!   re-filed with `closed_by` and becomes a PASS row: its repro must keep
//!   passing and its right-reason negative twin must keep being refused. This
//!   is not hypothetical — the first run of this test against the landing
//!   tree caught G03 (`List.isEmpty`), closed upstream by `ab611b242` between
//!   the measured commit and `origin/main`. G01 — the root cascade that
//!   blocked the whole `Semantics/` + `Proofs/` tree — closed on 2026-09-30
//!   and is additionally asserted natively here as a PASS row with its twin,
//!   beside the unescaped spelling Lean 4.8 itself refuses, so the cascade's
//!   root cannot move without a review-visible flip.
//!
//! Every assertion reads `clean check --json` output. There is no skip path:
//! a missing `python3` or a missing manifest is a FAILURE, not a green.

#![cfg(unix)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root should be two parents above CARGO_MANIFEST_DIR")
}

/// The row's `test_idea`, verbatim in shape: an equation-compiled `def` over
/// an inductive with `deriving Repr`, and an `rfl` theorem about it.
const ROW_SAMPLE: &str = "inductive Tag where\n\
  | a\n\
  | b\n\
  deriving Repr\n\
\n\
def f : Tag -> Nat\n\
  | .a => 1\n\
  | .b => 2\n\
\n\
theorem t : f .a = 1 := rfl\n";

const NEGATIVE_TWIN_DECL: &str = "clean_as_lean_semantics_checker_negative_twin";

/// G01, the root cascade: trust-ir's `Value` inductive has a constructor
/// spelled like the Lean 4.8 keyword `partial`, declared escaped (`«partial»`)
/// and matched as `.partial _`. This is the shape of
/// `TrustIr/State/ValueMap.lean` reduced to its trigger.
const G01_ROOT_CASCADE: &str = "inductive Value where\n\
  | int (v : Int)\n\
  | «partial» (bytes : List Nat)\n\
\n\
def Value.isPartial : Value -> Bool\n\
  | .partial _ => true\n\
  | _ => false\n\
\n\
theorem g01_partial : (Value.partial []).isPartial = true := rfl\n\
theorem g01_int : (Value.int 0).isPartial = false := rfl\n";

/// The same constructor declared UNESCAPED — refused by Lean 4.8 itself
/// ("expected token"), so a parse error here is parity, not the gap.
const G01_UNESCAPED: &str = "inductive Value where\n\
  | int (v : Int)\n\
  | partial (bytes : List Nat)\n";

fn check_json(dir: &Path, name: &str, source: &str) -> (Output, String) {
    let path = dir.join(name);
    fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    let output = Command::new(clean_path())
        .args(["check", "--json", name])
        .current_dir(dir)
        .output()
        .unwrap_or_else(|e| panic!("failed to run clean check on {name}: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        stdout.contains("\"schema_version\": \"Clean-check-report-v2\""),
        "clean check --json {name} did not emit a v2 report\nstdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    (output, stdout)
}

/// The value of a scalar `"key": value` field in the pretty-printed report.
/// The report is flat enough (one field per line) that a string scan is exact;
/// this crate deliberately carries no JSON dev-dependency for it.
fn field<'a>(report: &'a str, key: &str) -> &'a str {
    let needle = format!("\"{key}\": ");
    let start = report
        .find(&needle)
        .unwrap_or_else(|| panic!("report has no field {key:?}:\n{report}"))
        + needle.len();
    let rest = &report[start..];
    let end = rest.find(['\n', ',']).unwrap_or(rest.len());
    rest[..end].trim()
}

/// Every string element of the `"key": [ ... ]` array in the report.
fn list(report: &str, key: &str) -> Vec<String> {
    let needle = format!("\"{key}\": [");
    let start = report
        .find(&needle)
        .unwrap_or_else(|| panic!("report has no list {key:?}:\n{report}"))
        + needle.len();
    let rest = &report[start..];
    // The list closes on a line that is exactly `]` (or `],`): an element's
    // TEXT may itself contain `]` — `[TrustIr.Basic] …` inherited-module tags,
    // `Kernel check failed for [anonymous]` — so the first `]` byte is not it.
    // Cutting there would silently drop elements and turn "the refusal names
    // X" assertions vacuous.
    rest.lines()
        .map(str::trim)
        .take_while(|l| *l != "]" && *l != "],")
        .filter(|l| l.starts_with('"'))
        .map(|l| l.trim_end_matches(',').trim_matches('"').to_string())
        .collect()
}

#[test]
fn list_scan_keeps_an_element_whose_text_contains_a_closing_bracket() {
    let report = "{\n  \"errors\": [\n    \"[TrustIr.Basic] x: Kernel check failed for [anonymous]\",\n    \"t: Parse error\"\n  ],\n  \"trust_failures\": []\n}\n";
    assert_eq!(
        list(report, "errors"),
        vec![
            "[TrustIr.Basic] x: Kernel check failed for [anonymous]".to_string(),
            "t: Parse error".to_string()
        ]
    );
    assert!(list(report, "trust_failures").is_empty());
}

#[test]
fn clean_as_lean_semantics_checker_row_sample_elaborates() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (output, report) = check_json(dir.path(), "RowSample.lean", ROW_SAMPLE);
    assert!(output.status.success(), "row sample must check: {report}");
    assert_eq!(field(&report, "status"), "\"pass\"", "{report}");
    assert_eq!(field(&report, "decl_count"), "3", "{report}");
    assert_eq!(field(&report, "success_count"), "3", "{report}");
    assert_eq!(field(&report, "failed_count"), "0", "{report}");
    assert_eq!(field(&report, "sorry_axioms"), "0", "{report}");
    assert_eq!(field(&report, "kernel_check_failures"), "0", "{report}");
}

/// Right-reason negative twin: the same file plus a FALSE `rfl` theorem must
/// be refused, naming exactly that declaration with a type mismatch, while
/// the three declarations the baseline accepted are still counted.
#[test]
fn clean_as_lean_semantics_checker_negative_twin_is_refused_by_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let twin = format!("{ROW_SAMPLE}theorem {NEGATIVE_TWIN_DECL} : f .a = 2 := rfl\n");
    let (output, report) = check_json(dir.path(), "RowTwin.lean", &twin);
    assert!(
        !output.status.success(),
        "the twin must be refused: {report}"
    );
    assert_eq!(field(&report, "status"), "\"fail\"", "{report}");
    assert_eq!(field(&report, "decl_count"), "4", "{report}");
    assert_eq!(field(&report, "success_count"), "3", "{report}");
    assert_eq!(field(&report, "failed_count"), "1", "{report}");
    assert_eq!(field(&report, "sorry_axioms"), "0", "{report}");
    let errors = list(&report, "errors");
    assert_eq!(errors.len(), 1, "exactly the twin fails: {report}");
    assert!(
        errors[0].starts_with(&format!("{NEGATIVE_TWIN_DECL}: "))
            && errors[0].contains("Type mismatch"),
        "the refusal must name the twin and its reason: {}",
        errors[0]
    );
}

/// Mutation control: a `sorry` in place of the proof must be flagged by
/// Clean's own axiom census (`trust_summary.sorry_axioms`), named in
/// `trust_failures`, and never counted as a success.
#[test]
fn clean_as_lean_semantics_checker_mutation_control_flags_sorry() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mutated = ROW_SAMPLE.replace(
        "theorem t : f .a = 1 := rfl\n",
        "theorem t : f .a = 1 := by\n  sorry\n",
    );
    assert_ne!(mutated, ROW_SAMPLE, "the mutation must apply");
    let (output, report) = check_json(dir.path(), "RowSorry.lean", &mutated);
    assert!(!output.status.success(), "a sorry must not pass: {report}");
    assert_eq!(field(&report, "status"), "\"fail\"", "{report}");
    assert_eq!(field(&report, "sorry_axioms"), "1", "{report}");
    assert_eq!(field(&report, "success_count"), "2", "{report}");
    assert_eq!(field(&report, "failed_count"), "1", "{report}");
    let trust_failures = list(&report, "trust_failures");
    assert_eq!(
        trust_failures,
        vec!["t: declaration uses explicit sorry".to_string()],
        "{report}"
    );
}

/// PASS ratchet, native: the root cascade G01 closed on 2026-09-30 (a word
/// glued to a preceding `.` is never a keyword, as in Lean's `dotIdent`).
/// The escaped constructor and its `.partial _` arm elaborate, and the
/// right-reason twin — a FALSE theorem that a catch-all reading of
/// `.partial _` would accept — is refused BY NAME.
#[test]
fn test_semantics_checker_g01_escaped_constructor_and_dot_arm_elaborates() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (output, report) = check_json(dir.path(), "G01.lean", G01_ROOT_CASCADE);
    assert!(
        output.status.success(),
        "GAP G01 REGRESSED: the `«partial»` constructor / `.partial _` arm no longer \
         elaborates. Re-file docs/issues/2026-09-19-trust-ir-semantics-elaborator-gaps.md \
         and reports/trust-ir-semantics-probe/repros/manifest.json.\n{report}"
    );
    assert_eq!(field(&report, "status"), "\"pass\"", "{report}");
    assert_eq!(field(&report, "success_count"), "4", "{report}");
    assert_eq!(field(&report, "sorry_axioms"), "0", "{report}");

    let twin =
        format!("{G01_ROOT_CASCADE}theorem g01_twin : (Value.int 0).isPartial = true := rfl\n");
    let (output, report) = check_json(dir.path(), "G01Twin.lean", &twin);
    assert!(
        !output.status.success(),
        "the G01 twin must be refused: {report}"
    );
    let errors = list(&report, "errors");
    assert_eq!(errors.len(), 1, "exactly the twin fails: {report}");
    assert!(
        errors[0].starts_with("g01_twin: ") && errors[0].contains("Type mismatch"),
        "the refusal must name the twin and its reason: {}",
        errors[0]
    );
}

/// Parity, native: the UNESCAPED declaration is a parse error in Lean 4.8 and
/// stays one here — the G01 fix reads a keyword as a name only after a glued
/// `.`, never in declaration position.
#[test]
fn test_semantics_checker_g01_unescaped_keyword_constructor_is_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (output, report) = check_json(dir.path(), "G01Unescaped.lean", G01_UNESCAPED);
    assert!(!output.status.success(), "Lean 4.8 refuses this: {report}");
    let errors = list(&report, "errors");
    assert!(
        errors.iter().any(|e| e.contains("Parse error")),
        "the refusal must be the parse error Lean gives: {report}"
    );
}

/// GAP ratchet, the whole filed corpus: every minimized repro under
/// `reports/trust-ir-semantics-probe/repros/` must still fail with its filed
/// signature. The probe's `repros` subcommand exits 1 on `closed` or `changed`
/// and 2 on an environment error, so anything but 0 fails here.
#[test]
fn clean_as_lean_semantics_checker_filed_gaps_still_fail_as_filed() {
    let root = workspace_root();
    let probe = root.join("scripts/trust_ir_semantics_probe.py");
    let manifest = root.join("reports/trust-ir-semantics-probe/repros/manifest.json");
    assert!(probe.is_file(), "missing {}", probe.display());
    assert!(manifest.is_file(), "missing {}", manifest.display());
    let output = run_repro_probe(&root, &manifest, None, &clean_path());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_repro_probe_succeeded(&output);
    assert!(stdout.contains("\"pass\": true"), "{stdout}");
    let manifest_text = fs::read_to_string(&manifest).expect("manifest is readable");
    let filed = manifest_text.matches("\"id\": \"G").count();
    let closed = manifest_text.matches("\"closed_by\": ").count();
    assert!(filed >= 14, "the manifest lost filed gaps: {filed}");
    let still_fails = stdout.matches("\"outcome\": \"still-fails\"").count();
    let still_passes = stdout.matches("\"outcome\": \"still-passes\"").count();
    assert_eq!(
        (still_fails, still_passes),
        (filed - closed, closed),
        "every OPEN row still fails and every closed-upstream row still passes \
         with its twin refused\n{stdout}"
    );
}

fn run_repro_probe(root: &Path, manifest: &Path, home: Option<&Path>, clean: &Path) -> Output {
    let mut command = Command::new("python3");
    command
        .arg("-B")
        .arg(root.join("scripts/trust_ir_semantics_probe.py"))
        .args(["repros", "--clean"])
        .arg(clean)
        .arg("--manifest")
        .arg(manifest)
        .current_dir(root);
    if let Some(home) = home {
        command
            .env("HOME", home)
            .env("ELAN_HOME", home.join("elan"));
    }
    command
        .output()
        .expect("python3 is required by this ratchet; it is not optional")
}

/// Only exit 1 with a judged negative report is corpus drift. Other failures
/// mean the probe could not judge the corpus. Every failure remains fatal.
fn assert_repro_probe_succeeded(output: &Output) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let judged_drift = serde_json::from_slice::<serde_json::Value>(&output.stdout)
        .ok()
        .is_some_and(|report| {
            report.get("pass").and_then(serde_json::Value::as_bool) == Some(false)
                && report
                    .get("repros")
                    .and_then(serde_json::Value::as_array)
                    .is_some_and(|rows| {
                        rows.iter().try_fold(false, |has_drift, row| {
                            match row.get("outcome").and_then(serde_json::Value::as_str) {
                                Some("still-fails" | "still-passes") => Some(has_drift),
                                Some(
                                    "closed" | "changed" | "regressed" | "twin-accepted"
                                    | "twin-changed",
                                ) => Some(true),
                                _ => None,
                            }
                        }) == Some(true)
                    })
        });
    match output.status.code() {
        Some(0) => {}
        Some(1) if judged_drift => panic!(
            "a filed elaborator gap no longer fails AS FILED (closed or changed). \
             Re-file the tracker entry and the manifest in this change.\n\
             exit=Some(1)\nstdout:\n{stdout}\nstderr:\n{stderr}"
        ),
        code => panic!(
            "the filed-gap probe could not evaluate the corpus (environment, invocation, \
             or process failure). Check the probe invocation and manifest access, and restore any missing \
             Python or reference Lean toolchain; keep the tracker unchanged until \
             a judged report is available.\n\
             exit={code:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        ),
    }
}

fn repro_failure_message(output: &Output) -> String {
    let failure = std::panic::catch_unwind(|| assert_repro_probe_succeeded(output))
        .expect_err("a failed or unavailable probe must still fail closed");
    failure
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| failure.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .expect("diagnostic panic message")
}

#[test]
fn filed_gap_missing_reference_world_is_an_environment_failure() {
    let root = workspace_root();
    let home = tempfile::tempdir().expect("isolated toolchain home");
    let output = run_repro_probe(
        &root,
        &root.join("reports/trust-ir-semantics-probe/repros/manifest.json"),
        Some(home.path()),
        &clean_path(),
    );
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("Lean toolchain leanprover/lean4:v4.8.0 is not installed"),
        "the real missing-world failure is required: {output:?}"
    );
    let message = repro_failure_message(&output);
    assert!(
        message.contains("could not evaluate the corpus"),
        "{message}"
    );
    assert!(!message.contains("Re-file the tracker"), "{message}");
}

#[test]
fn filed_gap_unreadable_manifest_is_not_semantic_drift() {
    let dir = tempfile::tempdir().expect("missing manifest control");
    let output = run_repro_probe(
        &workspace_root(),
        &dir.path().join("absent.json"),
        None,
        &clean_path(),
    );
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("FileNotFoundError"),
        "the real unreadable-manifest failure is required: {output:?}"
    );
    let message = repro_failure_message(&output);
    assert!(
        message.contains("could not evaluate the corpus"),
        "{message}"
    );
    assert!(!message.contains("Re-file the tracker"), "{message}");
}

fn diagnostic_control_manifest(dir: &Path) -> PathBuf {
    fs::write(
        dir.join("Probe.lean"),
        "def diagnostic_control : Nat := 0\n",
    )
    .expect("valid source control");
    let manifest = dir.join("manifest.json");
    fs::write(
        &manifest,
        serde_json::to_vec(&serde_json::json!({"gaps": [{
            "id": "diagnostic_control",
            "entry": "Probe.lean",
            "expect": "^intentionally-unmatched-control-signature$"
        }]}))
        .expect("control manifest JSON"),
    )
    .expect("control manifest");
    manifest
}

#[test]
fn filed_gap_judged_drift_still_requires_refiling() {
    let dir = tempfile::tempdir().expect("judged drift control");
    let manifest = diagnostic_control_manifest(dir.path());
    let output = run_repro_probe(&workspace_root(), &manifest, None, &clean_path());
    assert_eq!(output.status.code(), Some(1));
    let report: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("the real judged report");
    assert_eq!(report["pass"], false);
    assert_eq!(report["repros"][0]["outcome"], "closed");
    let message = repro_failure_message(&output);
    assert!(message.contains("Re-file the tracker"), "{message}");
    assert!(!message.contains("could not evaluate"), "{message}");
}

#[test]
fn filed_gap_checker_without_report_is_not_semantic_drift() {
    let dir = tempfile::tempdir().expect("no-report control");
    let manifest = diagnostic_control_manifest(dir.path());
    let output = run_repro_probe(
        &workspace_root(),
        &manifest,
        None,
        Path::new("/usr/bin/false"),
    );
    assert_eq!(output.status.code(), Some(1));
    let report: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("the real unjudged report");
    assert_eq!(report["pass"], false);
    assert_eq!(report["repros"][0]["outcome"], "no-report");
    let message = repro_failure_message(&output);
    assert!(
        message.contains("could not evaluate the corpus"),
        "{message}"
    );
    assert!(!message.contains("Re-file the tracker"), "{message}");
}
