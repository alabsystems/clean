// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Process-boundary checks for `clean project check`.

use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;

use serde_json::Value;

const CLEAN_PROJECT_CHECK_BIN_ENV: &str = "CLEAN_PROJECT_CHECK_BIN";
const CARGO_CLEAN_BIN_ENV: &str = "CARGO_BIN_EXE_clean";

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root should be two parents above CARGO_MANIFEST_DIR")
}

fn clean_binary() -> PathBuf {
    static BINARY: OnceLock<PathBuf> = OnceLock::new();
    BINARY.get_or_init(resolve_clean_binary).clone()
}

fn resolve_clean_binary() -> PathBuf {
    if let Some(binary) = env::var_os(CLEAN_PROJECT_CHECK_BIN_ENV) {
        let binary = PathBuf::from(binary);
        assert!(
            binary.is_file(),
            "{CLEAN_PROJECT_CHECK_BIN_ENV} points to {}, but it is not a file",
            binary.display()
        );
        return binary;
    }

    if let Some(binary) = env::var_os(CARGO_CLEAN_BIN_ENV)
        .map(PathBuf::from)
        .filter(|binary| binary.is_file())
    {
        return binary;
    }

    build_clean_binary()
}

fn build_clean_binary() -> PathBuf {
    let root = workspace_root();
    // `$CARGO` is targo, which refuses a lane-less `build`: select the lane.
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("targo"));
    let status = Command::new(cargo)
        .args(["--unverified", "build", "--quiet"])
        .args(["-p", "clean", "--bin", "clean"])
        .current_dir(&root)
        .env("CARGO_TERM_COLOR", "never")
        .status()
        .expect("cargo build -p clean --bin clean should start");
    assert!(status.success(), "failed to build clean binary: {status}");

    // The nested build inherits CARGO_TARGET_DIR (a relative one is under `root`).
    let target_dir =
        env::var_os("CARGO_TARGET_DIR").map_or_else(|| root.join("target"), |dir| root.join(dir));
    let binary = target_dir
        .join("debug")
        .join(format!("clean{}", env::consts::EXE_SUFFIX));
    assert!(
        binary.is_file(),
        "cargo build succeeded, but {} does not exist",
        binary.display()
    );
    binary
}

fn run_clean(args: &[&str]) -> Output {
    Command::new(clean_binary())
        .args(args)
        .current_dir(workspace_root())
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .unwrap_or_else(|err| panic!("failed to run Clean {args:?}: {err}"))
}

fn parse_json(args: &[&str], output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "Clean {args:?} did not emit JSON on stdout: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[test]
fn project_check_json_aggregates_project_local_imports() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("Good.lean"),
        "def project_check_id (x : Nat) : Nat := x\n\
         theorem project_check_true : True := True.intro\n",
    )
    .expect("write good fixture");
    fs::write(
        dir.path().join("UsesGood.lean"),
        "import Good\n\
         theorem project_check_uses_good : True := True.intro\n",
    )
    .expect("write uses-good fixture");
    // Build artifacts under .lake/ must be skipped by the source scan.
    fs::create_dir_all(dir.path().join(".lake/build/lib/lean")).expect("build dir");
    fs::write(
        dir.path().join(".lake/build/lib/lean/Ignored.lean"),
        "theorem ignored : False := by\n  rfl\n",
    )
    .expect("write ignored build fixture");

    let project = dir.path().to_str().expect("utf8 tempdir");
    let args = ["project", "check", project, "--json"];
    let output = run_clean(&args);
    let report = parse_json(&args, &output);

    assert_eq!(report["schema_version"], "Clean-project-check-report-v5");
    assert_eq!(report["semantic_authority"]["engine"], "Clean");
    assert_eq!(report["semantic_authority"]["external_olean"], false);
    assert_eq!(report["summary"]["modules_found"], 2);

    let modules = report["modules"].as_array().expect("modules");
    let uses_good = modules
        .iter()
        .find(|module| module["module"] == "UsesGood")
        .expect("UsesGood module report");
    assert_eq!(uses_good["imports"][0]["module"], "Good");
    assert_eq!(uses_good["imports"][0]["project_local"], true);
}

#[test]
fn project_check_blocks_project_local_import_cycles() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("A.lean"),
        "import B\n\
         theorem cycle_a : True := True.intro\n",
    )
    .expect("write A fixture");
    fs::write(
        dir.path().join("B.lean"),
        "import A\n\
         theorem cycle_b : True := True.intro\n",
    )
    .expect("write B fixture");

    let project = dir.path().to_str().expect("utf8 tempdir");
    let args = ["project", "check", project, "--json"];
    let output = run_clean(&args);
    assert!(
        !output.status.success(),
        "import cycle should block project authority\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = parse_json(&args, &output);
    assert_eq!(report["status"], "fail");
    let cycle_blocker_count = report["authority_blockers"]
        .as_array()
        .expect("authority blockers")
        .iter()
        .filter(|blocker| blocker["kind"] == "project_import_cycle")
        .count();
    assert!(
        cycle_blocker_count >= 2,
        "expected both cycle members to be reported; got {cycle_blocker_count}"
    );
}

#[test]
fn project_check_blocks_external_imports_instead_of_using_lean_authority() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("UsesExternal.lean"),
        "import Mathlib\n\
         theorem project_external_import_ok : True := True.intro\n",
    )
    .expect("write fixture");

    let project = dir.path().to_str().expect("utf8 tempdir");
    let args = ["project", "check", project, "--json"];
    let output = run_clean(&args);
    assert!(
        !output.status.success(),
        "external import should block project authority\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = parse_json(&args, &output);

    assert_eq!(report["status"], "fail");
    assert_eq!(report["semantic_authority"]["lean4"], false);
    assert_eq!(report["semantic_authority"]["lake"], false);
    assert_eq!(report["semantic_authority"]["mathlib"], false);
    assert!(report["authority_blockers"]
        .as_array()
        .expect("authority blockers")
        .iter()
        .any(|blocker| blocker["kind"] == "external_import"
            && blocker["message"]
                .as_str()
                .expect("message")
                .contains("Mathlib")));
}

// ─────────────────────────────────────────────────────────────────────────────
// K5 VACUOUS-PASS BATTERY (2026-09-17)
//
// `clean project check` returned `status: pass` with `declarations_checked: 0,
// declarations_failed: 0` on the TSL package (1,580 declarations, of which
// `clean check` fails 1,133), and did NOT refuse a deliberate type error placed
// inside a `namespace TrustIr` block — while it did refuse the same error at top
// level. Root cause: a `namespace` / `section` / `mutual` block elaborates to one
// `ElabResult::Multiple`, which `typecheck_elab_result` answered `Ok("(skipped)")`
// for without looking inside, and `record_project_decl` then dropped.
//
// Every case below is a refusal that the pre-fix binary did not make, or a count
// it did not report. They are batteries, not one example: block SHAPE
// (namespace / section / mutual / nested / `open … in`), failure KIND (elaboration
// type error, `sorry`, a false theorem, an unparsable declaration), and POSITION
// (first, middle, last member; alongside passing siblings).
// ─────────────────────────────────────────────────────────────────────────────

fn write_project(dir: &Path, files: &[(&str, &str)]) {
    for (name, body) in files {
        let path = dir.join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture directory");
        }
        fs::write(&path, body).unwrap_or_else(|err| panic!("write {name}: {err}"));
    }
}

fn check_project(dir: &Path) -> (Output, Value) {
    let project = dir.to_str().expect("utf8 tempdir");
    let args = ["project", "check", project, "--json"];
    let output = run_clean(&args);
    let report = parse_json(&args, &output);
    (output, report)
}

fn check_nested_project(source: &str, allow_sorry: bool) -> (Output, Value) {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("Main.lean"), source).expect("write nested fixture");
    let project = dir.path().to_str().expect("utf8 tempdir");
    let mut args = vec!["project", "check", project, "--json"];
    if allow_sorry {
        args.push("--allow-sorry");
    }
    let output = run_clean(&args);
    let report = parse_json(&args, &output);
    (output, report)
}

fn module_report<'a>(report: &'a Value, module: &str) -> &'a Value {
    report["modules"]
        .as_array()
        .expect("modules")
        .iter()
        .find(|entry| entry["module"] == module)
        .unwrap_or_else(|| panic!("no module report for {module}"))
}

fn usize_field(value: &Value, key: &str) -> u64 {
    value[key]
        .as_u64()
        .unwrap_or_else(|| panic!("{key} should be a number, got {:?}", value[key]))
}

fn blocker_messages<'a>(report: &'a Value, kind: &str) -> Vec<&'a str> {
    report["authority_blockers"]
        .as_array()
        .expect("authority blockers")
        .iter()
        .filter(|b| b["kind"] == kind)
        .filter_map(|b| b["message"].as_str())
        .collect()
}

fn clean_check_json(file: &Path) -> (Output, Value) {
    let args = ["check", "--json", file.to_str().expect("utf8 path")];
    let output = run_clean(&args);
    let report = parse_json(&args, &output);
    (output, report)
}

/// The acceptance criterion, stated on its own: a package with ONE bad
/// declaration, inside a namespace, must exit non-zero.
#[test]
fn one_bad_declaration_inside_a_namespace_exits_non_zero() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[(
            "Solo.lean",
            "namespace SoloBattery\n\
             def soloBad : Bool := (0 : Nat)\n\
             end SoloBattery\n",
        )],
    );

    let (output, report) = check_project(dir.path());
    assert!(
        !output.status.success(),
        "a deliberate type error inside a namespace must be refused\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(report["status"], "fail");
    assert_eq!(usize_field(&report["summary"], "declarations_parsed"), 1);
    assert_eq!(usize_field(&report["summary"], "declarations_checked"), 1);
    assert_eq!(usize_field(&report["summary"], "declarations_passed"), 0);
    assert_eq!(usize_field(&report["summary"], "declarations_failed"), 1);
    assert!(
        report["authority_blockers"]
            .as_array()
            .expect("authority blockers")
            .iter()
            .any(|blocker| blocker["message"]
                .as_str()
                .is_some_and(|message| message.contains("soloBad"))),
        "the refusal must name the declaration: {}",
        serde_json::to_string_pretty(&report["authority_blockers"]).unwrap_or_default()
    );
}

/// Block shape battery: every block form that elaborates to `ElabResult::Multiple`
/// must have its members checked. Each module carries exactly one bad declaration.
#[test]
fn every_block_shape_has_its_members_checked() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            (
                "ShapeNamespace.lean",
                "namespace ShapeNs\n\
                 def nsBad : Bool := (0 : Nat)\n\
                 end ShapeNs\n",
            ),
            (
                "ShapeSection.lean",
                "section\n\
                 def sectionBad : Bool := (0 : Nat)\n\
                 end\n",
            ),
            (
                "ShapeNested.lean",
                "namespace ShapeOuter\n\
                 namespace ShapeInner\n\
                 def nestedBad : Bool := (0 : Nat)\n\
                 end ShapeInner\n\
                 end ShapeOuter\n",
            ),
            (
                "ShapeNamedSection.lean",
                "namespace ShapeNamed\n\
                 section NamedInner\n\
                 def namedSectionBad : Bool := (0 : Nat)\n\
                 end NamedInner\n\
                 end ShapeNamed\n",
            ),
        ],
    );

    let (output, report) = check_project(dir.path());
    assert!(
        !output.status.success(),
        "every block shape must refuse its bad member\nstdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
    for (module, decl) in [
        ("ShapeNamespace", "nsBad"),
        ("ShapeSection", "sectionBad"),
        ("ShapeNested", "nestedBad"),
        ("ShapeNamedSection", "namedSectionBad"),
    ] {
        let entry = module_report(&report, module);
        assert_eq!(entry["status"], "fail", "{module} must fail");
        assert_eq!(
            usize_field(entry, "checked_count"),
            1,
            "{module} must count its one declaration"
        );
        assert_eq!(usize_field(entry, "failed_count"), 1, "{module}");
        assert_eq!(usize_field(entry, "success_count"), 0, "{module}");
        assert!(
            entry["diagnostics"]
                .as_array()
                .expect("diagnostics")
                .iter()
                .any(|diag| diag["message"]
                    .as_str()
                    .is_some_and(|message| message.contains(decl))),
            "{module} must name {decl}: {}",
            serde_json::to_string_pretty(&entry["diagnostics"]).unwrap_or_default()
        );
    }
}

/// Failure-kind battery: an elaboration type error is not the only way a
/// declaration inside a block can be unsound. A `sorry` and a false theorem must
/// be refused too, and the module's own trust counters must be accounted for.
#[test]
fn every_failure_kind_inside_a_namespace_is_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            (
                "KindSorry.lean",
                "namespace KindSorry\n\
                 theorem sorryInBlock : True := sorry\n\
                 end KindSorry\n",
            ),
            (
                "KindFalse.lean",
                "namespace KindFalse\n\
                 theorem falseInBlock : (1 : Nat) = 2 := rfl\n\
                 end KindFalse\n",
            ),
            (
                "KindUnparsable.lean",
                "namespace KindUnparsable\n\
                 def ok : Nat := 1\n\
                 def := := :=\n\
                 end KindUnparsable\n",
            ),
        ],
    );

    let (output, report) = check_project(dir.path());
    assert!(
        !output.status.success(),
        "sorry, a false theorem and an unparsable declaration must all be refused\nstdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
    for module in ["KindSorry", "KindFalse", "KindUnparsable"] {
        let entry = module_report(&report, module);
        assert_eq!(entry["status"], "fail", "{module} must fail");
        assert!(
            usize_field(entry, "failed_count") >= 1,
            "{module} must report the failing declaration, not just a counter"
        );
    }
    // No module may claim a pass while its own trust counters recorded an event.
    for entry in report["modules"].as_array().expect("modules") {
        let minted = usize_field(&entry["trust_summary"], "sorry_axioms")
            + usize_field(&entry["trust_summary"], "kernel_check_failures");
        if minted > 0 {
            assert_eq!(
                entry["status"], "fail",
                "module {} minted {minted} trust event(s) and still passed",
                entry["module"]
            );
        }
    }
}

#[test]
fn project_check_counts_nested_namespace_and_section_leaves() {
    let (output, report) = check_nested_project(
        "namespace Outer\n\
         def before : Nat := 1\n\
         namespace Inner\n\
         theorem good : True := True.intro\n\
         section\n\
         def deep : Nat := 3\n\
         end\n\
         end Inner\n\
         def afterGood : Nat := 4\n\
         end Outer\n",
        false,
    );
    assert!(output.status.success(), "{report}");
    assert_eq!(report["status"], "pass");
    // Report v2: `declarations_checked` = passed + failed.
    assert_eq!(report["summary"]["declarations_checked"], 4);
    assert_eq!(report["summary"]["declarations_passed"], 4);
    assert_eq!(report["summary"]["declarations_failed"], 0);
    assert_eq!(report["summary"]["authority_blockers"], 0);
}

#[test]
fn project_check_reports_failed_nested_leaf_and_keeps_good_siblings() {
    for allow_sorry in [false, true] {
        let (output, report) = check_nested_project(
            "namespace Outer\n\
             namespace Inner\n\
             def before : Nat := 1\n\
             def bad : Bool := (0 : Nat)\n\
             def afterGood : Nat := 2\n\
             end Inner\n\
             end Outer\n",
            allow_sorry,
        );
        assert!(!output.status.success(), "{report}");
        assert_eq!(report["status"], "fail");
        // Report v2: the failing leaf is checked too (v1 counted passes only).
        assert_eq!(report["summary"]["declarations_checked"], 3);
        assert_eq!(report["summary"]["declarations_passed"], 2);
        assert_eq!(report["summary"]["declarations_failed"], 1);
        assert!(report["diagnostics"]
            .as_array()
            .expect("diagnostics")
            .iter()
            .any(|d| d["message"].as_str().expect("message").contains("bad")));
    }
}

#[test]
fn project_check_applies_sorry_policy_to_each_nested_leaf() {
    let source = "namespace Outer\n\
                  namespace Inner\n\
                  theorem good : True := True.intro\n\
                  theorem debt : False := by sorry\n\
                  end Inner\n\
                  end Outer\n";
    for allow_sorry in [false, true] {
        let (output, report) = check_nested_project(source, allow_sorry);
        assert_eq!(output.status.success(), allow_sorry, "{report}");
        assert_eq!(report["status"], if allow_sorry { "pass" } else { "fail" });
        // Report v2: both leaves are checked either way; the policy decides
        // how many of them pass.
        assert_eq!(report["summary"]["declarations_checked"], 2);
        assert_eq!(
            report["summary"]["declarations_passed"],
            if allow_sorry { 2 } else { 1 }
        );
        assert_eq!(
            report["summary"]["declarations_failed"],
            if allow_sorry { 0 } else { 1 }
        );
        assert!(
            report["modules"][0]["trust_summary"]["sorry_axioms"]
                .as_u64()
                .expect("counter")
                > 0
        );
        if !allow_sorry {
            assert!(report["authority_blockers"]
                .as_array()
                .expect("blockers")
                .iter()
                .any(|d| d["kind"] == "trust_failure"
                    && d["message"]
                        .as_str()
                        .expect("message")
                        .contains("Outer.Inner.debt")));
        }
    }
}

/// Position battery: a failing member must not hide its passing siblings, and a
/// passing sibling must not launder the failing member — in any position.
#[test]
fn passing_and_failing_siblings_are_reported_independently() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            (
                "PosFirst.lean",
                "namespace PosFirst\n\
                 def badFirst : Bool := (0 : Nat)\n\
                 def goodA : Nat := 1\n\
                 def goodB : Nat := 2\n\
                 end PosFirst\n",
            ),
            (
                "PosMiddle.lean",
                "namespace PosMiddle\n\
                 def goodC : Nat := 1\n\
                 def badMiddle : Bool := (0 : Nat)\n\
                 def goodD : Nat := 2\n\
                 end PosMiddle\n",
            ),
            (
                "PosLast.lean",
                "namespace PosLast\n\
                 def goodE : Nat := 1\n\
                 def goodF : Nat := 2\n\
                 def badLast : Bool := (0 : Nat)\n\
                 end PosLast\n",
            ),
        ],
    );

    let (output, report) = check_project(dir.path());
    assert!(!output.status.success(), "each module has one bad member");
    for (module, bad) in [
        ("PosFirst", "badFirst"),
        ("PosMiddle", "badMiddle"),
        ("PosLast", "badLast"),
    ] {
        let entry = module_report(&report, module);
        assert_eq!(
            usize_field(entry, "checked_count"),
            3,
            "{module}: 3 members"
        );
        assert_eq!(usize_field(entry, "success_count"), 2, "{module}: 2 pass");
        assert_eq!(usize_field(entry, "failed_count"), 1, "{module}: 1 fails");
        assert!(
            entry["diagnostics"]
                .as_array()
                .expect("diagnostics")
                .iter()
                .any(|diag| diag["message"]
                    .as_str()
                    .is_some_and(|message| message.contains(bad))),
            "{module} must name {bad}"
        );
    }
}

/// The counting half of the defect: a clean package must report the number of
/// declarations it checked, not zero.
#[test]
fn a_passing_package_reports_the_number_of_declarations_it_checked() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            (
                "CountBase.lean",
                "namespace CountBase\n\
                 def one : Nat := 1\n\
                 def two : Nat := 2\n\
                 theorem trivial : True := True.intro\n\
                 end CountBase\n",
            ),
            (
                "CountUser.lean",
                "import CountBase\n\
                 namespace CountUser\n\
                 def three : Nat := 3\n\
                 end CountUser\n",
            ),
        ],
    );

    let (output, report) = check_project(dir.path());
    assert!(
        output.status.success(),
        "a package with no bad declaration must pass\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(report["status"], "pass");
    assert_eq!(usize_field(&report["summary"], "declarations_parsed"), 4);
    assert_eq!(usize_field(&report["summary"], "declarations_checked"), 4);
    assert_eq!(usize_field(&report["summary"], "declarations_passed"), 4);
    assert_eq!(usize_field(&report["summary"], "declarations_failed"), 0);
    assert_eq!(
        usize_field(module_report(&report, "CountBase"), "checked_count"),
        3
    );
    assert_eq!(
        usize_field(module_report(&report, "CountUser"), "checked_count"),
        1
    );
}

/// A package that declares nothing has checked nothing, and a check that
/// checked nothing has no verdict: it is refused as `nothing_checked`, never
/// reported as a pass. This test used to assert the opposite (exit 0 with 0
/// declarations checked); the round-22 verification of `317f48b45` measured
/// that as a vacuous pass on comment-only and admin-only packages. What stays
/// true is the COUNT: nothing is parsed, nothing is checked, and nothing is
/// invented as a failed declaration row.
#[test]
fn a_package_that_declares_nothing_is_refused_as_nothing_checked() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("EmptyNs.lean", "namespace EmptyNs\nend EmptyNs\n"),
            ("OnlyImport.lean", "import EmptyNs\n"),
        ],
    );

    let (output, report) = check_project(dir.path());
    assert!(!output.status.success(), "{report}");
    assert_eq!(report["status"], "fail");
    assert_eq!(usize_field(&report["summary"], "declarations_parsed"), 0);
    assert_eq!(usize_field(&report["summary"], "declarations_checked"), 0);
    assert_eq!(usize_field(&report["summary"], "declarations_failed"), 0);
    let blockers = report["authority_blockers"].as_array().expect("blockers");
    assert_eq!(blockers.len(), 1, "{report}");
    assert_eq!(blockers[0]["kind"], "nothing_checked");
}

/// The control the K5 probe ran: the SAME error at top level was already
/// refused. It must stay refused, and now be named and counted the same way.
#[test]
fn the_same_error_at_top_level_is_still_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &["TopLevel.lean"]
            .iter()
            .map(|name| (*name, "def topLevelBad : Bool := (0 : Nat)\n"))
            .collect::<Vec<_>>(),
    );

    let (output, report) = check_project(dir.path());
    assert!(!output.status.success());
    assert_eq!(usize_field(&report["summary"], "declarations_checked"), 1);
    assert_eq!(usize_field(&report["summary"], "declarations_failed"), 1);
    assert!(
        report["authority_blockers"]
            .as_array()
            .expect("authority blockers")
            .iter()
            .any(|blocker| blocker["message"]
                .as_str()
                .is_some_and(|message| message.contains("topLevelBad"))),
        "a top-level failure must name its declaration too"
    );
}

#[test]
fn project_check_blocks_anonymous_sorry_without_a_registered_name() {
    for allow_sorry in [false, true] {
        let (output, report) = check_nested_project(
            "namespace Outer\nexample : True := by sorry\nend Outer\n",
            allow_sorry,
        );
        assert_eq!(output.status.success(), allow_sorry, "{report}");
        assert_eq!(report["status"], if allow_sorry { "pass" } else { "fail" });
        assert!(
            report["modules"][0]["trust_summary"]["sorry_axioms"]
                .as_u64()
                .expect("counter")
                > 0
        );
        if !allow_sorry {
            assert!(report["authority_blockers"]
                .as_array()
                .expect("blockers")
                .iter()
                .any(|d| d["kind"] == "sorry_axiom"));
        }
    }
}

#[test]
fn project_check_does_not_count_empty_namespace_as_a_declaration() {
    let (output, report) = check_nested_project("namespace Outer\nend Outer\n", false);
    // Not counted: 0 checked, 0 passed, 0 failed. And, having checked
    // nothing, the run is refused (`nothing_checked`), not passed.
    assert!(!output.status.success(), "{report}");
    assert_eq!(report["summary"]["declarations_checked"], 0);
    assert_eq!(report["summary"]["declarations_passed"], 0);
    assert_eq!(report["summary"]["declarations_failed"], 0);
    assert_eq!(report["summary"]["authority_blockers"], 1);
    assert_eq!(report["authority_blockers"][0]["kind"], "nothing_checked");
}

/// The descriptor's crediting sentence must state the sorry waiver the run
/// applies. `--allow-sorry` credits a declaration whose closure reaches a
/// `sorry` (the passing arm of
/// `project_check_blocks_anonymous_sorry_without_a_registered_name`, and
/// `ImportedConeVerdict::passed(allow_sorry)` for a cited closure), so a
/// sentence saying a credited declaration "reaches no `sorry`", with no
/// qualifier, is false for every `--allow-sorry` run.
#[test]
fn project_check_descriptor_states_the_sorry_waiver_its_crediting_rule_applies() {
    let descriptor = clean_cli::__test_support::all_features()
        .into_iter()
        .find(|d| d.path == ["project", "check"])
        .unwrap_or_else(|| panic!("no `project check` descriptor"));
    let description = descriptor.description.replace('\n', " ");
    let crediting = description
        .split(". ")
        .find(|sentence| sentence.contains("A declaration is credited only when"))
        .unwrap_or_else(|| panic!("no crediting sentence in: {description}"));
    assert!(
        crediting.contains("--allow-sorry"),
        "the crediting sentence names `sorry` without the `--allow-sorry` waiver: {crediting:?}"
    );
    assert!(
        !crediting.contains("no `sorry` or trust marker"),
        "the crediting sentence claims an unconditional sorry refusal: {crediting:?}"
    );
}

#[path = "project_check_cli/codata.rs"]
mod codata;
#[path = "project_check_cli/credit.rs"]
mod credit;
#[path = "project_check_cli/isolation.rs"]
mod isolation;
#[path = "project_check_cli/private_names.rs"]
mod private_names;
