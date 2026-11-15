// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check --json` on Lean 4.8.0's testing and audit commands: `#guard`,
//! `#print axioms` and `#guard_msgs` — the shape of trust-ir's
//! `TrustIr/Pred.lean` fixtures and `TrustIr/Proofs/AxiomAudit.lean` gate.
//!
//! Each command used to be skipped and replaced by `#check _`, so every one of
//! them failed `Kernel check failed for [anonymous]: Unknown free variable`,
//! and `#guard_msgs in #print axioms c` failed three times (the skip stopped
//! at `#print`, which read `axioms` as the constant and left `c` behind as an
//! unknown command). Expected messages are the pinned Lean 4.8.0 binary's
//! output for the same source; every negative control is a file Lean 4.8.0
//! rejects.

#![cfg(unix)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// `(exit success, report)` of `clean check --json` on `source`.
fn check_json(dir: &Path, source: &str) -> (bool, String) {
    let path = dir.join("Guard.lean");
    fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    let output = Command::new(clean_path())
        .args(["check", "--json", "Guard.lean"])
        .current_dir(dir)
        .output()
        .unwrap_or_else(|e| panic!("failed to run clean check: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        stdout.contains("\"schema_version\": \"Clean-check-report-v2\""),
        "no v2 report\nstdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), stdout)
}

/// The value of a scalar `"key": value` field in the pretty-printed report.
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

/// An audit gate in AxiomAudit's shape over theorems whose axiom lists Lean
/// 4.8.0 prints as written here.
const AUDIT: &str = "theorem t : True := True.intro\n\
theorem c2 (a b : Prop) (h : a ↔ b) : a = b := propext h\n\
namespace Audit\n\
/-- info: 't' does not depend on any axioms -/\n\
#guard_msgs in\n\
#print axioms t\n\
/-- info: 'c2' depends on axioms: [propext] -/\n\
#guard_msgs in\n\
#print axioms c2\n\
end Audit\n";

#[test]
fn test_clean_check_axiom_audit_gate_passes_and_counts_each_guard() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (ok, report) = check_json(dir.path(), AUDIT);
    assert!(ok, "Lean 4.8.0 builds this audit; so must Clean:\n{report}");
    assert_eq!(field(&report, "status"), "\"pass\"", "{report}");
    // Two theorems and two `#guard_msgs`: an audit file is not `nothing_checked`.
    assert_eq!(field(&report, "decl_count"), "4", "{report}");
    assert_eq!(field(&report, "success_count"), "4", "{report}");
}

#[test]
fn test_clean_check_axiom_audit_gate_with_wrong_expectation_fails() {
    // The gate's purpose: a proof that starts depending on a new axiom (here,
    // an expectation that omits `propext`) must fail the build.
    let dir = tempfile::tempdir().expect("tempdir");
    let mutated = AUDIT.replace(
        "'c2' depends on axioms: [propext]",
        "'c2' does not depend on any axioms",
    );
    assert_ne!(mutated, AUDIT, "the mutation must apply");
    let (ok, report) = check_json(dir.path(), &mutated);
    assert!(!ok, "a stale axiom audit must fail:\n{report}");
    assert_eq!(field(&report, "status"), "\"fail\"", "{report}");
    assert_eq!(field(&report, "failed_count"), "1", "{report}");
    assert!(
        report.contains(
            "❌ Docstring on `#guard_msgs` does not match generated message:\\n\\ninfo: 'c2' \
             depends on axioms: [propext]"
        ),
        "{report}"
    );
}

/// `Pred.implies`'s fixtures in miniature (non-overlapping arms: overlap is
/// the match compiler's business, not `#guard`'s). `success_count ==
/// decl_count` below also pins that `Shape.implies` itself elaborated.
const FIXTURES: &str = "inductive Shape where\n  | top\n  | interval (lo hi : Nat)\n\
def Shape.implies : Shape → Shape → Bool\n\
  | .top, .top => true\n\
  | .interval _ _, .top => true\n\
  | .top, .interval _ _ => false\n\
  | .interval a b, .interval c d => c ≤ a && b ≤ d\n\
#guard Shape.implies .top .top = true\n\
#guard Shape.implies (.interval 2 5) (.interval 0 7) = true\n\
#guard Shape.implies (.interval 0 7) (.interval 2 5) = false\n";

#[test]
fn test_clean_check_guard_fixtures_pass_without_kernel_failures() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (ok, report) = check_json(dir.path(), FIXTURES);
    assert!(ok, "{report}");
    assert_eq!(field(&report, "status"), "\"pass\"", "{report}");
    assert_eq!(field(&report, "failed_count"), "0", "{report}");
    assert_eq!(
        field(&report, "success_count"),
        field(&report, "decl_count"),
        "{report}"
    );
    assert_eq!(field(&report, "kernel_check_failures"), "0", "{report}");
}

#[test]
fn test_clean_check_false_guard_fails_by_evaluation() {
    // Lean 4.8.0: `did not evaluate to `true``.
    let dir = tempfile::tempdir().expect("tempdir");
    let (_, base) = check_json(dir.path(), FIXTURES);
    let source = format!("{FIXTURES}#guard Shape.implies .top (.interval 0 7) = true\n");
    let (ok, report) = check_json(dir.path(), &source);
    assert!(!ok, "a false #guard must fail:\n{report}");
    assert_eq!(field(&report, "failed_count"), "1", "{report}");
    // Exactly the false `#guard` is lost: everything the base run passed
    // still passes.
    assert_eq!(
        field(&report, "success_count"),
        field(&base, "success_count"),
        "{report}"
    );
    assert!(report.contains("did not evaluate to `true`"), "{report}");
    assert!(!report.contains("Unknown free variable"), "{report}");
}

#[test]
fn test_clean_check_unknown_hash_command_is_named_not_a_kernel_leak() {
    // Lean 4.8.0 refuses an unknown command when it parses it. Clean used to
    // substitute `#check _` for it, and the hole failed as `Kernel check
    // failed for [anonymous]: Unknown free variable`.
    let dir = tempfile::tempdir().expect("tempdir");
    let (ok, report) = check_json(
        dir.path(),
        "#frobnicate 1\ntheorem t : True := True.intro\n",
    );
    assert!(!ok, "an unknown command must fail the file:\n{report}");
    assert!(
        report.contains("unknown command `#frobnicate`"),
        "the refusal must name the command:\n{report}"
    );
    assert!(!report.contains("Unknown free variable"), "{report}");
    assert_eq!(field(&report, "success_count"), "1", "{report}");
}
