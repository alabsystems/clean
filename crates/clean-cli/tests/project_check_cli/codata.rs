// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `project check` over codata and codef declarations, and the lanes that
//! must refuse a file declaring nothing or passing on a user axiom.

use super::*;

// ─────────────────────────────────────────────────────────────────────────────
// `codata` / `codef` (2026-09-24). These commands register kernel-checked
// declarations but used to answer `ElabResult::Skipped`, so every
// per-declaration consumer saw NOTHING: `clean project check` reported a valid
// codata package as `0 checked` (and its vacuity gate then refused it), and a
// `sorry` in a codef clause reached no per-declaration gate — `clean check`
// exited 0 with `status: pass`, and `clean compile` compiled it. Battery: every
// generating lane, at top level and inside a namespace.
// ─────────────────────────────────────────────────────────────────────────────

const CODATA_STREAM: &str = "codata Strm (A : Type) where\n  head : A\n  tail : Strm A\n";
const CODATA_INDEXED: &str =
    "codata IS3 : (n : Nat) → Type where\n  val : Nat\n  next : IS3 (Nat.succ n)\n";
const CODATA_MUTUAL: &str =
    "mutual\n  codata TreeQ (A : Type) where\n    label : A\n    kids : ForestQ A\n  \
codata ForestQ (A : Type) where\n    first : TreeQ A\n    rest : ForestQ A\nend\n";

/// `(lane, source)` for a valid package in every generating lane.
fn valid_codata_sources() -> Vec<(&'static str, String)> {
    vec![
        ("plain codata", CODATA_STREAM.to_string()),
        ("indexed codata", CODATA_INDEXED.to_string()),
        (
            "variant codata",
            "codata VBox (A : Type) where\n  | wrap : A → VBox A → VBox A\n".to_string(),
        ),
        ("mutual codata", CODATA_MUTUAL.to_string()),
        (
            "plain codef",
            format!("{CODATA_STREAM}codef natsFrom (n : Nat) : Strm Nat where\n  head := n\n  tail := natsFrom (Nat.succ n)\n"),
        ),
        (
            "guarded codef",
            format!("{CODATA_STREAM}codef alternate (s : Nat) : Strm Nat where\n  head := s\n  tail := Strm.mk (Nat.add s 100) (alternate (Nat.succ s))\n"),
        ),
        (
            "indexed codef",
            format!("{CODATA_INDEXED}codef tracker (n : Nat) : IS3 n where\n  val := n\n  next := tracker (Nat.succ n)\n"),
        ),
        (
            "mutual codef",
            format!("{CODATA_MUTUAL}mutual\n  codef tq (s : Nat) : TreeQ Nat where\n    label := s\n    kids := fq (Nat.succ s)\n  codef fq (s : Nat) : ForestQ Nat where\n    first := tq s\n    rest := fq (Nat.succ s)\nend\n"),
        ),
    ]
}

/// `(lane, source, codef name)` with a `sorry` written in one codef clause.
fn sorry_codef_sources() -> Vec<(&'static str, String, &'static str)> {
    vec![
        (
            "plain codef",
            format!("{CODATA_STREAM}codef natsFrom (n : Nat) : Strm Nat where\n  head := sorry\n  tail := natsFrom (Nat.succ n)\n"),
            "natsFrom",
        ),
        (
            "guarded codef",
            format!("{CODATA_STREAM}codef alternate (s : Nat) : Strm Nat where\n  head := s\n  tail := Strm.mk sorry (alternate (Nat.succ s))\n"),
            "alternate",
        ),
        (
            "indexed codef",
            format!("{CODATA_INDEXED}codef tracker (n : Nat) : IS3 n where\n  val := sorry\n  next := tracker (Nat.succ n)\n"),
            "tracker",
        ),
        (
            "mutual codef",
            format!("{CODATA_MUTUAL}mutual\n  codef tq (s : Nat) : TreeQ Nat where\n    label := sorry\n    kids := fq (Nat.succ s)\n  codef fq (s : Nat) : ForestQ Nat where\n    first := tq s\n    rest := fq (Nat.succ s)\nend\n"),
            "tq",
        ),
    ]
}

fn in_namespace(source: &str) -> String {
    format!("namespace Wrap\n{source}end Wrap\n")
}

/// A valid codata/codef package is checked, counted, and passes — at top level
/// and inside a namespace. Pre-fix: `pass` with 0 declarations checked, and
/// then (with the vacuity gate) `fail: nothing_checked` on a valid package.
#[test]
fn codata_and_codef_declarations_are_checked_and_counted() {
    for (lane, source) in valid_codata_sources() {
        for (placement, text) in [
            ("top level", source.clone()),
            ("namespace", in_namespace(&source)),
        ] {
            let (output, report) = check_nested_project(&text, false);
            let summary = &report["summary"];
            assert!(
                output.status.success() && report["status"] == "pass",
                "{lane} ({placement}): a valid package must pass: {}",
                serde_json::to_string_pretty(&report["authority_blockers"]).unwrap_or_default()
            );
            let checked = usize_field(summary, "declarations_checked");
            assert!(checked > 0, "{lane} ({placement}): 0 declarations checked");
            assert_eq!(
                usize_field(summary, "declarations_passed"),
                checked,
                "{lane} ({placement})"
            );
            assert_eq!(
                usize_field(summary, "declarations_failed"),
                0,
                "{lane} ({placement})"
            );
        }
    }
}

/// A `sorry` in a codef clause is refused by all three commands, and each
/// refusal is on the codef's own trust warning. Pre-fix, `clean check` exited 0
/// with `status: pass` and `clean compile` emitted IR.
#[test]
fn a_sorry_in_a_codef_clause_is_refused_by_check_project_check_and_compile() {
    for (lane, source, name) in sorry_codef_sources() {
        for (placement, text, qualified) in [
            ("top level", source.clone(), name.to_string()),
            ("namespace", in_namespace(&source), format!("Wrap.{name}")),
        ] {
            let dir = tempfile::tempdir().expect("tempdir");
            let file = dir.path().join("Main.lean");
            fs::write(&file, &text).expect("write fixture");
            let file = file.to_str().expect("utf8 path");

            // clean project check
            let (output, report) = check_project(dir.path());
            assert!(
                !output.status.success(),
                "{lane} ({placement}): project check must fail"
            );
            assert!(
                report["authority_blockers"]
                    .as_array()
                    .expect("authority blockers")
                    .iter()
                    .any(|b| b["kind"] == "trust_failure"
                        && b["message"].as_str().is_some_and(|m| m.contains(name))),
                "{lane} ({placement}): the refusal must be a trust_failure naming `{name}`: {}",
                serde_json::to_string_pretty(&report["authority_blockers"]).unwrap_or_default()
            );

            // clean check
            let args = ["check", "--json", file];
            let output = run_clean(&args);
            let report = parse_json(&args, &output);
            assert!(
                !output.status.success() && report["status"] == "fail",
                "{lane} ({placement}): clean check must refuse a sorry-backed codef: {report}"
            );
            assert!(
                report["trust_failures"]
                    .as_array()
                    .is_some_and(|rows| !rows.is_empty()),
                "{lane} ({placement}): clean check must report the trust failure row: {report}"
            );

            // clean compile
            let output = run_clean(&["compile", file, "--decl", &qualified, "--emit", "l5ir"]);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                !output.status.success() && stderr.contains("trust warning"),
                "{lane} ({placement}): clean compile must refuse `{qualified}` on its trust warning\nstderr:\n{stderr}"
            );
        }
    }
}

/// Over-blocking control for the compile gate: a valid codef still compiles.
#[test]
fn a_valid_codef_still_compiles() {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("Main.lean");
    fs::write(
        &file,
        format!("{CODATA_STREAM}codef natsFrom (n : Nat) : Strm Nat where\n  head := n\n  tail := natsFrom (Nat.succ n)\n"),
    )
    .expect("write fixture");
    let output = run_clean(&[
        "compile",
        file.to_str().expect("utf8 path"),
        "--decl",
        "natsFrom",
        "--emit",
        "l5ir",
    ]);
    assert!(
        output.status.success(),
        "a valid codef must still compile\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Round-22 verification of `317f48b45`: a comment-only or administrative-only
/// file passed BOTH lanes after checking 0 declarations, exit 0. Checking
/// nothing is not a pass.
#[test]
fn a_file_that_declares_nothing_is_refused_by_both_lanes() {
    for (label, source) in [
        ("comment only", "-- a comment\n/- a block comment -/\n"),
        ("admin only", "open Nat\nset_option maxHeartbeats 400\n"),
        ("empty namespace", "namespace A\nend A\n"),
    ] {
        let (output, report) = check_nested_project(source, false);
        assert!(
            !output.status.success() && report["status"] == "fail",
            "{label}: project check must refuse a run that checked nothing: {report}"
        );
        assert!(
            report["authority_blockers"]
                .as_array()
                .expect("authority blockers")
                .iter()
                .any(|b| b["kind"] == "nothing_checked"),
            "{label}: the refusal must be nothing_checked: {report}"
        );

        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("Main.lean");
        fs::write(&file, source).expect("write fixture");
        let args = ["check", "--json", file.to_str().expect("utf8 path")];
        let output = run_clean(&args);
        let report = parse_json(&args, &output);
        assert!(
            !output.status.success() && report["status"] == "nothing_checked",
            "{label}: clean check must refuse a run that checked nothing: {report}"
        );
    }
}

/// Round-22 verification: `example : 1 = 2 := sorry` was counted as PASSED by
/// `clean project check` (`success_count 1, failed_count 0`) — its trust
/// warning was looked up by name, and an `example` has none.
#[test]
fn a_sorry_example_is_a_failed_row_not_a_pass() {
    for source in [
        "example : 1 = 2 := sorry\n",
        "namespace A\nexample : 1 = 2 := sorry\nend A\n",
        "section S\ntheorem good : 1 = 1 := rfl\nexample : 1 = 2 := sorry\nend S\n",
    ] {
        let (output, report) = check_nested_project(source, false);
        let summary = &report["summary"];
        assert!(!output.status.success(), "{source}: must fail: {report}");
        assert_eq!(
            usize_field(summary, "declarations_failed"),
            1,
            "{source}: the sorry example is one FAILED row: {report}"
        );
        assert_eq!(
            usize_field(summary, "declarations_passed") + 1,
            usize_field(summary, "declarations_checked"),
            "{source}: {report}"
        );
    }
}

/// Round-22 verification: `axiom bogus : 1 = 2` and a theorem proved from it
/// passed both lanes with nothing in either report saying so. The pass stands
/// (it is valid under the stated axiom) but must be disclosed per declaration.
#[test]
fn a_pass_that_rests_on_a_user_axiom_is_disclosed_by_both_lanes() {
    let source =
        "axiom bogus : 1 = 2\ntheorem bad : 1 = 2 := bogus\nnamespace A\nexample : 1 = 2 := bogus\n\
         theorem clean_one : 1 = 1 := rfl\nend A\n";
    let (output, report) = check_nested_project(source, false);
    assert!(output.status.success(), "{report}");
    assert_eq!(
        usize_field(&report["summary"], "declarations_passed_on_assumptions"),
        3,
        "bogus, bad and the example rest on `bogus`; A.clean_one does not: {report}"
    );
    let rows: Vec<&str> = report["modules"][0]["assumptions"]
        .as_array()
        .expect("assumptions")
        .iter()
        .filter_map(Value::as_str)
        .collect();
    for name in ["bogus:", "bad:", "example:"] {
        assert!(
            rows.iter()
                .any(|row| row.starts_with(name) && row.contains("bogus")),
            "missing assumption row for {name}: {rows:?}"
        );
    }
    assert!(
        !rows.iter().any(|row| row.contains("clean_one")),
        "an unconditional pass is not an assumption row: {rows:?}"
    );

    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("Main.lean");
    fs::write(&file, source).expect("write fixture");
    let args = ["check", "--json", file.to_str().expect("utf8 path")];
    let output = run_clean(&args);
    let report = parse_json(&args, &output);
    assert!(output.status.success(), "{report}");
    let rows = report["assumptions"].as_array().expect("assumptions");
    assert_eq!(rows.len(), 3, "{report}");
}
