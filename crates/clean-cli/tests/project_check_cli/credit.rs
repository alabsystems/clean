// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `project check` credits a theorem only through the closure-aware rule
//! `clean check` uses, and a module that checked nothing is not `pass`.

use super::*;

// ─────────────────────────────────────────────────────────────────────────────
// Round-24 verification of 29de4ae8b: `project check` credited a theorem whose
// proof reaches `sorryAx` through ANOTHER declaration, and marked modules
// `pass` that checked nothing or whose imports failed. `clean check` refused
// both. The credit rule is now the same closure-aware rule in both lanes.
// ─────────────────────────────────────────────────────────────────────────────

/// The refusal a citer of a sorry'd declaration gets, since 01189665c made a
/// declaration's trust verdict its constant CLOSURE's: a `trust_failure` for
/// the sorry, naming the declaration it came through (`through`), or naming
/// none when the citer's own terms carry it (`None`, the control whose sorry
/// is in its statement). It is decided before the cited-closure gate, which
/// therefore does not refuse the row as well.
fn assert_refused_as_a_sorry(label: &str, report: &Value, citer: &str, through: Option<&str>) {
    let refused = blocker_messages(report, "trust_failure");
    let own = format!("{citer}: declaration uses");
    assert!(
        refused.iter().any(|m| {
            m.starts_with(&own)
                && m.contains("sorry")
                && match through {
                    Some(via) => m.contains(&format!("(through {via}")),
                    None => !m.contains("(through "),
                }
        }),
        "{label}: {citer} must be refused as a sorry use (through {through:?}): {report}"
    );
    assert!(
        !blocker_messages(report, "cited_closure_not_credited")
            .iter()
            .any(|m| m.starts_with(&format!("{citer}:"))),
        "{label}: {citer} was refused twice: {report}"
    );
}

#[test]
fn a_theorem_citing_a_sorry_theorem_is_not_credited() {
    for (label, source, citer, through) in [
        (
            "namespace/section",
            "namespace A\ntheorem s : 1 = 2 := sorry\nend A\n\
             section S\ntheorem t : 1 = 2 := A.s\nend S\n",
            "t",
            Some("A.s"),
        ),
        (
            "top level",
            "theorem s : 1 = 2 := sorry\ntheorem t : 1 = 2 := s\n",
            "t",
            Some("s"),
        ),
        (
            "two citations away",
            "theorem s : 1 = 2 := sorry\ntheorem t : 1 = 2 := s\n\
             namespace B\ntheorem u : 1 = 2 := t\nend B\n",
            "B.u",
            Some("t"),
        ),
        (
            "a definition citing a sorry definition",
            // Refused on `t`'s own sorry warning (the sorry is in its
            // statement), not through a citation; kept as a control.
            "def d : Nat := sorry\ntheorem t : d = d := rfl\n",
            "t",
            None,
        ),
    ] {
        let (output, report) = check_nested_project(source, false);
        assert!(!output.status.success(), "{label}: {report}");
        let summary = &report["summary"];
        assert_eq!(
            usize_field(summary, "declarations_passed"),
            0,
            "{label}: nothing here may be credited: {report}"
        );
        assert_eq!(
            usize_field(summary, "declarations_failed"),
            usize_field(summary, "declarations_checked"),
            "{label}: {report}"
        );
        assert_refused_as_a_sorry(label, &report, citer, through);
        assert_eq!(module_report(&report, "Main")["status"], "fail");

        // The same verdict as `clean check` on the same file.
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("Main.lean");
        fs::write(&file, source).expect("write fixture");
        let (check_output, check_report) = clean_check_json(&file);
        assert!(!check_output.status.success(), "{label}: {check_report}");
        assert_eq!(
            check_report["success_count"].as_u64(),
            Some(0),
            "{label}: {check_report}"
        );
    }
}

#[test]
fn allow_sorry_waives_a_cited_sorry_in_both_lanes_and_nothing_else() {
    let source = "theorem s : 1 = 2 := sorry\ntheorem t : 1 = 2 := s\n";
    let (output, report) = check_nested_project(source, true);
    assert!(output.status.success(), "{report}");
    assert_eq!(usize_field(&report["summary"], "declarations_passed"), 2);
    assert!(blocker_messages(&report, "cited_closure_not_credited").is_empty());
}

#[test]
fn a_cross_module_citation_of_a_sorry_theorem_is_not_credited() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("Dep.lean", "theorem s : 1 = 2 := sorry\n"),
            ("Main.lean", "import Dep\ntheorem t : 1 = 2 := s\n"),
        ],
    );
    let (output, report) = check_project(dir.path());
    assert!(!output.status.success(), "{report}");
    let main = module_report(&report, "Main");
    assert_eq!(main["status"], "fail", "{report}");
    assert_eq!(usize_field(main, "success_count"), 0, "{report}");
    assert_eq!(usize_field(main, "failed_count"), 1, "{report}");
    assert_eq!(usize_field(&report["summary"], "declarations_passed"), 0);
    // Across the module boundary too: `t`'s closure reaches `Dep.lean`'s sorry.
    assert_refused_as_a_sorry("cross-module", &report, "t", Some("s"));

    let (check_output, check_report) = clean_check_json(&dir.path().join("Main.lean"));
    assert!(!check_output.status.success(), "{check_report}");
}

#[test]
fn a_good_citation_is_still_credited() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            (
                "Dep.lean",
                "namespace Dep\ntheorem s : 1 = 1 := rfl\ndef d : Nat := 2\nend Dep\n",
            ),
            (
                "Main.lean",
                "import Dep\nsection S\ntheorem t : 1 = 1 := Dep.s\n\
                 theorem u : Dep.d = 2 := rfl\nend S\n",
            ),
        ],
    );
    let (output, report) = check_project(dir.path());
    assert!(output.status.success(), "{report}");
    assert_eq!(usize_field(&report["summary"], "declarations_passed"), 4);
    assert_eq!(module_report(&report, "Main")["status"], "pass");
    assert_eq!(module_report(&report, "Dep")["status"], "pass");
    assert_eq!(usize_field(&report["summary"], "modules_passed"), 2);
}

#[test]
fn a_module_that_checked_nothing_is_not_pass() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("Good.lean", "theorem g : 1 = 1 := rfl\n"),
            ("Agg.lean", "import Good\n"),
            ("Notes.lean", "-- nothing but a comment\nopen Nat\n"),
        ],
    );
    let (output, report) = check_project(dir.path());
    // The RUN checked a declaration and nothing failed: it passes. The two
    // modules that checked nothing are not credited as passing modules.
    assert!(output.status.success(), "{report}");
    assert_eq!(module_report(&report, "Good")["status"], "pass");
    for module in ["Agg", "Notes"] {
        let entry = module_report(&report, module);
        assert_eq!(entry["status"], "nothing_checked", "{module}: {report}");
        assert_eq!(usize_field(entry, "checked_count"), 0);
    }
    let summary = &report["summary"];
    assert_eq!(usize_field(summary, "modules_passed"), 1);
    assert_eq!(usize_field(summary, "modules_nothing_checked"), 2);
}

#[test]
fn a_module_whose_import_failed_is_not_pass() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("Bad.lean", "theorem bad : 1 = 2 := rfl\n"),
            ("UsesBad.lean", "import Bad\ntheorem ok : 1 = 1 := rfl\n"),
            (
                "UsesUsesBad.lean",
                "import UsesBad\ntheorem ok2 : 2 = 2 := rfl\n",
            ),
            ("AggBad.lean", "import Bad\n"),
            ("Good.lean", "theorem g : 1 = 1 := rfl\n"),
        ],
    );
    let (output, report) = check_project(dir.path());
    assert!(!output.status.success(), "{report}");
    assert_eq!(module_report(&report, "Bad")["status"], "fail");
    for (module, failed) in [
        ("UsesBad", "Bad"),
        ("UsesUsesBad", "UsesBad"),
        ("AggBad", "Bad"),
    ] {
        let entry = module_report(&report, module);
        assert_eq!(entry["status"], "import_failed", "{module}: {report}");
        assert!(
            entry["failed_imports"]
                .as_array()
                .expect("failed_imports")
                .iter()
                .any(|m| m == failed),
            "{module} must name {failed}: {report}"
        );
        // `clean check` refuses the same file.
        let (check_output, check_report) =
            clean_check_json(&dir.path().join(format!("{module}.lean")));
        assert!(!check_output.status.success(), "{module}: {check_report}");
    }
    assert_eq!(module_report(&report, "Good")["status"], "pass");
    let summary = &report["summary"];
    assert_eq!(usize_field(summary, "modules_passed"), 1);
    assert_eq!(usize_field(summary, "modules_failed"), 1);
    assert_eq!(usize_field(summary, "modules_import_failed"), 3);
    // Only `g` is credited. `ok` and `ok2` checked, but against a failed
    // import, so they are `declarations_not_credited` (report v5); v4 counted
    // them in `declarations_passed`, which is how an `import_failed(1/1)`
    // module credited `theorem m : C.v = 3 := rfl` (round-24 verification of
    // ff6c33c2c, `b_attr_unknown`).
    assert_eq!(usize_field(summary, "declarations_passed"), 1);
    assert_eq!(usize_field(summary, "declarations_not_credited"), 2);
    assert_eq!(usize_field(summary, "declarations_checked"), 4);
}
