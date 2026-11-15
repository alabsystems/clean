// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lean4export NDJSON front door (`clean_olean::ndjson`, the engine of
//! `clean olean replay --from-export`): plan item `checkers-ndjson-front-door`
//! of `docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`, its exit arms (a)-(e).
//!
//! - (a) From the sha256-pinned Round 2026-09 archive,
//!   `good/other/sparse-name-index` and `good/other/level-index-out-of-order`
//!   exit 0; `bad/other/orphan-ctor` (refused by the reader as no block) and
//!   `bad/other/extra-rec` exit 1.
//!   `good/init-prelude` is a pinned gap (Lean 4.29.1's `Nat` folds have no
//!   reviewed fold world), refused at `Char.ofNatAux` until that world lands.
//! - (b) One arm per lean4#15542/#15577 rule and per #15628/#15574 rule exits 1
//!   with its named `NdjsonError`; a format version other than 3 exits 2.
//! - (c) A non-quot record named `Quot.lift` exits 1.
//! - (d) OPEN: per-declaration equality with `clean olean replay --fresh` over a
//!   v4.30.0-rc2 lean4export export of `Init.Prelude`. The minting lane
//!   (`scripts/lean_export_mint.sh`) exists; the export is not minted yet.
//!   Pinned as a refusal that fails the day the export lands, or the lane goes.
//! - (e) A 25-million-digit `natVal` parses within a fixed bound, and budget
//!   exhaustion exits 2 (here for the NDJSON form; the `.olean` form's is in
//!   `src/cli/tests.rs`).
//!
//! Every arm runs the whole front door (reader, structural tier, replay) on an
//! in-memory export and asserts the exit code AND the rule or declaration that
//! decided it, so an arm cannot pass on a different refusal.

#[path = "support/kernel_arena.rs"]
mod kernel_arena;

#[path = "support/ndjson_exports.rs"]
mod exports;

use std::io::Read;
use std::time::{Duration, Instant};

use exports::{
    archived, arm_d_inputs, perturbed, replaced_once, verdict_of, within, HONEST, META, QUOT_ONLY,
};

use clean_olean::ndjson::{
    check_export_reader, DeclarationVerdict, ExitClass, ExportCheckOptions, ExportReport,
    MAX_LINE_BYTES, MAX_NAT_LITERAL_DIGITS,
};

fn check_bytes(bytes: &[u8], options: ExportCheckOptions) -> ExportReport {
    check_export_reader(bytes, options)
}

fn check_lines(meta: &str, lines: &[&str]) -> ExportReport {
    let mut text = String::from(meta);
    for line in lines {
        text.push('\n');
        text.push_str(line);
    }
    text.push('\n');
    check_bytes(text.as_bytes(), ExportCheckOptions::default())
}

fn rule(report: &ExportReport) -> &str {
    report.reader_error.as_ref().map_or("<none>", |e| e.rule)
}

#[test]
fn test_front_door_honest_control_is_accepted() {
    let report = check_lines(META, &HONEST);
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    assert_eq!((report.declarations, report.admitted), (1, 1), "{report:?}");
}

// -- (a) the archive ---------------------------------------------------------

#[test]
fn test_front_door_arm_a_archive_files_exit_as_the_round_expects() {
    let files = kernel_arena::archive();
    let table = kernel_arena::table();
    let mut failures = Vec::new();
    // `good/init-prelude` is a PINNED GAP, not exit 0: the export is Lean
    // 4.29.1's `Init.Prelude`, whose `Nat.add` (and every fold key over it)
    // has a δ-closure no reviewed native-fold world pins (v4.30.0-rc2 compiles
    // it through `Nat.add._f`), so `Nat.pow` does not fold and
    // `Char.ofNatAux`'s `2^32` bound is refused. Plan item
    // `kernel-extension-authority-worlds` owns the 4.29.1 world; the day it
    // lands this fails, and the file's expectation goes back to exit 0.
    let prelude = check_bytes(
        &files["good/init-prelude.ndjson"],
        ExportCheckOptions::default(),
    );
    let pinned = prelude
        .first_refusal
        .as_ref()
        .filter(|_| prelude.exit == ExitClass::Reject)
        .map(|first| (first.name.as_str(), first.reason.contains("TypeMismatch")));
    if pinned != Some(("Char.ofNatAux", true)) {
        failures.push(format!(
            "good/init-prelude.ndjson: the pinned fold-world gap changed shape (exit {}, first \
             refusal {:?}); if it is now accepted, restore its arm-(a) expectation",
            prelude.exit_code, prelude.first_refusal
        ));
    }
    // `orphan-ctor`'s constructor names a type its record does not declare:
    // the reader refuses the record as no block (R124) before any replay.
    for (path, expected, refused, reader) in [
        ("good/other/sparse-name-index.ndjson", 0u8, None, None),
        ("good/other/level-index-out-of-order.ndjson", 0, None, None),
        (
            "bad/other/orphan-ctor.ndjson",
            1,
            None,
            Some("inductive-block-shape"),
        ),
        (
            "bad/other/extra-rec.ndjson",
            1,
            Some(("rogue", "inconsistent")),
            None,
        ),
    ] {
        let row = table["tests"]
            .as_array()
            .and_then(|rows| rows.iter().find(|r| r["path"] == path))
            .unwrap_or_else(|| panic!("{path}: no row in the round table"));
        let outcome = if expected == 0 { "accept" } else { "reject" };
        assert_eq!(
            row["outcome"], outcome,
            "{path}: the round's expected outcome"
        );
        let report = check_bytes(&files[path], ExportCheckOptions::default());
        if report.exit_code != expected {
            failures.push(format!(
                "{path}: exit {} (expected {expected}); reader {:?}; first refusal {:?}",
                report.exit_code, report.reader_error, report.first_refusal
            ));
            continue;
        }
        if reader.is_some_and(|r| rule(&report) != r) {
            failures.push(format!(
                "{path}: refused by {} (expected the reader's {reader:?})",
                rule(&report)
            ));
        }
        // The target assertion: the forged member and its user are what was
        // refused, not something else.
        if let Some((forged, user)) = refused {
            for name in [forged, user] {
                let verdict = report
                    .records
                    .iter()
                    .find(|r| r.name == name)
                    .map(|r| r.verdict);
                if verdict != Some(DeclarationVerdict::Refused) {
                    failures.push(format!("{path}: `{name}` must be refused, got {verdict:?}"));
                }
            }
            let false_rec = report.records.iter().find(|r| r.name == "False.rec");
            if false_rec.is_none() {
                failures.push(format!("{path}: `False.rec` must be read"));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// -- (b) reader rules --------------------------------------------------------

fn check_owned(lines: &[String]) -> ExportReport {
    let refs: Vec<&str> = lines.iter().map(String::as_str).collect();
    check_lines(META, &refs)
}

#[test]
fn test_front_door_arm_b_each_lean4_15542_rule_rejects_by_name() {
    let mut extra_name = HONEST.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
    extra_name.insert(1, r#"{"in":1,"str":{"pre":0,"str":"b"}}"#.to_owned());
    let mut extra_level = HONEST.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
    extra_level.insert(2, r#"{"il":1,"succ":1}"#.to_owned());
    let mut extra_expr = HONEST.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
    extra_expr.insert(3, r#"{"ie":0,"bvar":0}"#.to_owned());
    let arms: Vec<(&str, Vec<String>, &str)> = vec![
        (
            "bytes after the object",
            perturbed(0, r#"{"in":1,"str":{"pre":0,"str":"a"}} x"#),
            "trailing-bytes",
        ),
        (
            "a second object on the line",
            perturbed(
                0,
                r#"{"in":1,"str":{"pre":0,"str":"a"}}{"in":2,"str":{"pre":0,"str":"b"}}"#,
            ),
            "trailing-bytes",
        ),
        (
            "a duplicate key",
            perturbed(0, r#"{"in":1,"in":2,"str":{"pre":0,"str":"a"}}"#),
            "duplicate-key",
        ),
        (
            "a duplicate nested key",
            perturbed(0, r#"{"in":1,"str":{"pre":0,"pre":1,"str":"a"}}"#),
            "duplicate-key",
        ),
        (
            "name index 0 rebound",
            perturbed(0, r#"{"in":0,"str":{"pre":0,"str":"a"}}"#),
            "name-index-rebound",
        ),
        ("name index 1 bound twice", extra_name, "name-index-rebound"),
        (
            "level index 0 rebound",
            perturbed(1, r#"{"il":0,"succ":0}"#),
            "level-index-rebound",
        ),
        (
            "level index 1 bound twice",
            extra_level,
            "level-index-rebound",
        ),
        ("expr index 0 bound twice", extra_expr, "expr-index-rebound"),
    ];
    let mut failures = Vec::new();
    for (what, lines, expected) in arms {
        let report = check_owned(&lines);
        if report.exit != ExitClass::Reject || rule(&report) != expected {
            failures.push(format!(
                "{what}: exit {:?} rule {} (expected reject by {expected})",
                report.exit,
                rule(&report)
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
fn test_front_door_arm_b_duplicate_keys_compare_after_unescaping_lean4_15628() {
    // `\u0070re` unescapes to `pre`: a duplicate only after unescaping.
    let report = check_owned(&perturbed(
        0,
        r#"{"in":1,"str":{"pre":0,"\u0070re":1,"str":"a"}}"#,
    ));
    assert_eq!(report.exit, ExitClass::Reject, "{report:?}");
    assert_eq!(rule(&report), "duplicate-key", "{report:?}");
    // Control: an escaped key that is NOT a duplicate is read.
    let report = check_owned(&perturbed(0, r#"{"in":1,"str":{"\u0070re":0,"str":"a"}}"#));
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
}

#[test]
fn test_front_door_arm_b_exponent_above_100000_rejects_lean4_15574() {
    // In an `mdata` payload, where an exporter may write any number.
    let mut lines: Vec<String> = HONEST.iter().map(|s| (*s).to_owned()).collect();
    lines.insert(
        3,
        r#"{"ie":1,"mdata":{"expr":0,"data":{"k":1e100001}}}"#.to_owned(),
    );
    let report = check_owned(&lines);
    assert_eq!(report.exit, ExitClass::Reject, "{report:?}");
    assert_eq!(rule(&report), "exponent-too-large", "{report:?}");
    // Control: at the cap the line is read (and the payload dropped, as Lean's
    // reader drops it).
    lines[3] = r#"{"ie":1,"mdata":{"expr":0,"data":{"k":1e100000}}}"#.to_owned();
    let report = check_owned(&lines);
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
}

#[test]
fn test_front_door_arm_b_format_and_lean_versions_outside_the_table_decline() {
    let format4 = META.replace(
        r#""format":{"version":"3.1.0"}"#,
        r#""format":{"version":"4.0.0"}"#,
    );
    let report = check_lines(&format4, &HONEST);
    assert_eq!(report.exit, ExitClass::Decline, "{report:?}");
    assert_eq!(report.exit_code, 2);
    assert_eq!(rule(&report), "format-version-unsupported", "{report:?}");
    let lean435 = META.replace(r#""version":"4.29.1""#, r#""version":"4.35.0""#);
    let report = check_lines(&lean435, &HONEST);
    assert_eq!(report.exit, ExitClass::Decline, "{report:?}");
    assert_eq!(rule(&report), "lean-version-unmapped", "{report:?}");
    // Format 3.0.0 is major version 3 but not the 3.1 this reader reads: it is
    // declined, not misread as malformed.
    let format30 = META.replace(
        r#""format":{"version":"3.1.0"}"#,
        r#""format":{"version":"3.0.0"}"#,
    );
    let report = check_lines(&format30, &HONEST);
    assert_eq!(report.exit, ExitClass::Decline, "{report:?}");
    assert_eq!(rule(&report), "format-version-unsupported", "{report:?}");
}

#[test]
fn test_front_door_arm_b_strict_record_shapes_reject() {
    let arms: Vec<(&str, Vec<String>, &str)> = vec![
        (
            "an unknown record",
            perturbed(1, r#"{"il":1,"zero":0}"#),
            "unknown-record",
        ),
        (
            "a reference to an unbound level",
            perturbed(2, r#"{"ie":0,"sort":7}"#),
            "unbound-level",
        ),
        (
            "an unknown field",
            perturbed(
                3,
                r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false,"x":0}}"#,
            ),
            "unknown-field",
        ),
        (
            "a non-canonical index",
            perturbed(0, r#"{"in":1e0,"str":{"pre":0,"str":"a"}}"#),
            "field",
        ),
        ("a blank line", perturbed(1, ""), "unexpected-end"),
        ("not an object", perturbed(1, "[1]"), "expected-object"),
        (
            "two declarations of one name",
            {
                let mut l: Vec<String> = HONEST.iter().map(|s| (*s).to_owned()).collect();
                l.push(HONEST[3].to_owned());
                l
            },
            "duplicate-declaration",
        ),
    ];
    let mut failures = Vec::new();
    for (what, lines, expected) in arms {
        let report = check_owned(&lines);
        if report.exit != ExitClass::Reject || rule(&report) != expected {
            failures.push(format!(
                "{what}: exit {:?} rule {}",
                report.exit,
                rule(&report)
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// -- (c) the quotient's names ------------------------------------------------

#[test]
fn test_front_door_arm_c_non_quot_record_named_quot_lift_rejects() {
    let lines = [
        r#"{"in":1,"str":{"pre":0,"str":"Quot"}}"#,
        r#"{"in":2,"str":{"pre":1,"str":"lift"}}"#,
        r#"{"il":1,"succ":0}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"axiom":{"name":2,"levelParams":[],"type":0,"isUnsafe":false}}"#,
    ];
    let report = check_lines(META, &lines);
    assert_eq!(report.exit, ExitClass::Reject, "{report:?}");
    assert_eq!(rule(&report), "reserved-quotient-name", "{report:?}");
    // Control: the same axiom under a free name is admitted.
    let free = lines.map(|l| l.replace(r#""str":"lift""#, r#""str":"lifted""#));
    let free: Vec<&str> = free.iter().map(String::as_str).collect();
    assert_eq!(check_lines(META, &free).exit, ExitClass::Accept);
}

/// A `quot` record whose stored type is not the kernel's (`Sort u` for `Quot`)
/// is refused for that type; the quotient-without-`Eq` refusal, with the
/// kernel's own type, is the next test.
#[test]
fn test_front_door_quot_record_with_a_wrong_type_is_refused() {
    let lines = [
        r#"{"in":1,"str":{"pre":0,"str":"Quot"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"u"}}"#,
        r#"{"il":1,"param":2}"#,
        r#"{"ie":0,"sort":1}"#,
        r#"{"quot":{"name":1,"levelParams":[2],"type":0,"kind":"type"}}"#,
    ];
    let report = check_lines(META, &lines);
    assert_eq!(report.exit, ExitClass::Reject, "{report:?}");
    let quot = report
        .records
        .iter()
        .find(|r| r.name == "Quot")
        .expect("Quot is declared");
    assert_eq!(quot.verdict, DeclarationVerdict::Refused, "{quot:?}");
    assert!(
        quot.reason
            .as_deref()
            .unwrap_or_default()
            .contains("quotDecl"),
        "refused for its type: {quot:?}"
    );
    // A `quot` record must carry the name its kind installs.
    let misnamed = lines.map(|l| l.replace(r#""kind":"type""#, r#""kind":"lift""#));
    let misnamed: Vec<&str> = misnamed.iter().map(String::as_str).collect();
    let report = check_lines(META, &misnamed);
    assert_eq!(rule(&report), "quotient-name-mismatch", "{report:?}");
}

/// The quotient enters only through `add_quot`, after an `Eq` of the shape its
/// kernel-built types name: a `quot` record whose stored type is the kernel's
/// own is still refused when the export has no `Eq` (Lean's `add_quot`:
/// `check_eq_type`).
#[test]
fn test_front_door_quotient_without_eq_is_refused_even_with_its_own_type() {
    let mut lines: Vec<&str> = QUOT_ONLY.to_vec();
    lines.push(r#"{"quot":{"name":1,"levelParams":[2],"type":7,"kind":"type"}}"#);
    let report = check_lines(META, &lines);
    assert_eq!(report.exit, ExitClass::Reject, "{report:?}");
    let quot = report
        .records
        .iter()
        .find(|r| r.name == "Quot")
        .expect("Quot is declared");
    assert_eq!(quot.verdict, DeclarationVerdict::Refused, "{quot:?}");
    let reason = quot.reason.as_deref().unwrap_or_default();
    assert!(
        reason.contains("add_quot"),
        "refused for its Eq, not its type: {reason}"
    );
}

/// A `quot` record whose stored type is not the kernel's is refused, even
/// over an honest `Eq` (Lean's replay ignores the stored type; this reader
/// does not let it disagree). `init-prelude`'s `Quot.lift` record is given
/// `Quot`'s type.
#[test]
fn test_front_door_quot_record_with_a_foreign_type_is_refused() {
    let files = kernel_arena::archive();
    let text = std::str::from_utf8(&files["good/init-prelude.ndjson"]).expect("UTF-8");
    let field = |line: &str, key: &str| -> String {
        let at = line.find(&format!("\"{key}\":")).expect("field") + key.len() + 3;
        line[at..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect()
    };
    let type_of_quot = text
        .lines()
        .find(|l| l.starts_with("{\"quot\"") && l.contains("\"kind\":\"type\""))
        .map(|l| field(l, "type"))
        .expect("init-prelude has the `type` quot record");
    let forged: String = text
        .lines()
        .map(|l| {
            if l.starts_with("{\"quot\"") && l.contains("\"kind\":\"lift\"") {
                let old = format!("\"type\":{}", field(l, "type"));
                l.replace(&old, &format!("\"type\":{type_of_quot}"))
            } else {
                l.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let report = check_bytes(forged.as_bytes(), ExportCheckOptions::default());
    assert_eq!(report.exit, ExitClass::Reject, "{:?}", report.first_refusal);
    let lift = report
        .records
        .iter()
        .find(|r| r.name == "Quot.lift")
        .expect("declared");
    assert_eq!(lift.verdict, DeclarationVerdict::Refused, "{lift:?}");
    assert!(
        lift.reason
            .as_deref()
            .unwrap_or_default()
            .contains("quotDecl"),
        "{lift:?}"
    );
}

// -- (d) OPEN: per-declaration equality with the .olean replay ---------------

/// Arm (d) is blocked on the export alone: the front door already judges a
/// v4.30.0-rc2 export under the R81 oracle world (the target precondition,
/// run through the reader here), and the minting lane exists (R120, since
/// 2026-10-28), but no export is minted. Fails the day the export lands, when
/// the equality arm must be written, or the day the lane is removed.
#[test]
fn test_front_door_arm_d_is_open_until_the_init_prelude_export_is_minted() {
    let rc2 = META.replace(r#""version":"4.29.1""#, r#""version":"4.30.0-rc2""#);
    let report = check_lines(&rc2, &HONEST);
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    assert_eq!(
        report.meta.as_ref().map(|m| m.lean_version.as_str()),
        Some("4.30.0-rc2"),
        "{report:?}"
    );
    let (export, lane) = arm_d_inputs();
    assert!(
        lane.is_file(),
        "the export-minting lane {} is gone, so arm (d)'s export cannot be minted",
        lane.display()
    );
    assert!(
        !export.exists(),
        "arm (d) is unblocked ({}): compare its per-declaration verdicts with \
         `clean olean replay --fresh Init.Prelude` and replace this pin with that arm",
        export.display()
    );
}

// -- (e) budgets -------------------------------------------------------------

#[test]
fn test_front_door_arm_e_a_25_million_digit_nat_literal_parses_within_a_bound() {
    const DIGITS: usize = 25_000_000;
    // Debug builds run num-bigint unoptimized; the bound is for that profile.
    const BOUND: Duration = Duration::from_secs(600);
    let mut text = String::with_capacity(META.len() + DIGITS + 64);
    text.push_str(META);
    text.push_str("\n{\"ie\":0,\"natVal\":\"9");
    text.extend(std::iter::repeat_n('7', DIGITS - 1));
    text.push_str("\"}\n");
    let start = Instant::now();
    let report = check_bytes(text.as_bytes(), ExportCheckOptions::default());
    let took = start.elapsed();
    assert_eq!(report.exit, ExitClass::Accept, "{:?}", report.reader_error);
    assert!(
        took < BOUND,
        "a {DIGITS}-digit natVal took {took:?} (bound {BOUND:?})"
    );
}

#[test]
fn test_front_door_arm_e_nat_literal_over_the_digit_budget_declines() {
    let mut text = String::from(META);
    text.push_str("\n{\"ie\":0,\"natVal\":\"");
    text.extend(std::iter::repeat_n('1', MAX_NAT_LITERAL_DIGITS + 1));
    text.push_str("\"}\n");
    let report = check_bytes(text.as_bytes(), ExportCheckOptions::default());
    assert_eq!(report.exit, ExitClass::Decline, "{report:?}");
    assert_eq!(rule(&report), "nat-literal-budget");
}

#[test]
fn test_front_door_arm_e_heartbeat_budget_exhaustion_declines_never_rejects() {
    let files = kernel_arena::archive();
    // An honest export whose checks reduce: `RTree.rec` on `RTree.mk`.
    let honest = &files["good/tutorial/122_rtreeRecReduction.ndjson"];
    let starved = check_bytes(
        honest,
        ExportCheckOptions {
            max_heartbeats: 1,
            axiom_closures: false,
        },
    );
    assert_eq!(
        starved.exit,
        ExitClass::Decline,
        "{:?}",
        starved.first_refusal
    );
    assert_eq!(
        starved.refused, 0,
        "a starved check is no finding: {starved:?}"
    );
    assert!(starved.budget_exhausted > 0, "{starved:?}");
    // Control: unlimited, the same export is accepted.
    let full = check_bytes(honest, ExportCheckOptions::default());
    assert_eq!(full.exit, ExitClass::Accept, "{:?}", full.first_refusal);
}

#[test]
fn test_front_door_json_report_carries_structural_axiom_closures() {
    let mut lines: Vec<&str> = HONEST.to_vec();
    lines.extend([
        r#"{"in":2,"str":{"pre":0,"str":"b"}}"#,
        r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
        r#"{"def":{"name":2,"levelParams":[],"type":0,"value":1,"hints":"abbrev","safety":"safe","all":[2]}}"#,
    ]);
    let mut text = String::from(META);
    for line in &lines {
        text.push('\n');
        text.push_str(line);
    }
    let report = check_bytes(
        text.as_bytes(),
        ExportCheckOptions {
            max_heartbeats: 0,
            axiom_closures: true,
        },
    );
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    let b = report.records.iter().find(|r| r.name == "b").expect("b");
    assert_eq!(b.axioms.as_deref(), Some(&["a".to_owned()][..]), "{b:?}");
}

// -- inductive blocks: structure and stored flags ----------------------------

/// A forged `all` must not let a family skip its block's replay: `bad : False`
/// never exits 0, whatever `all` names (finding C1 of the 2026-10-22 review).
#[test]
fn test_front_door_inductive_all_must_name_its_own_block() {
    let mut failures = Vec::new();
    for (what, all) in [
        ("`all` names an undeclared Z", "[8]"),
        ("`all` names another block's type first", "[1,6]"),
        ("`all` is empty", "[]"),
    ] {
        let report = check_bytes(
            exports::negative_block_export(all, true, true).as_bytes(),
            ExportCheckOptions::default(),
        );
        if report.exit != ExitClass::Reject || rule(&report) != "inductive-block-shape" {
            failures.push(format!(
                "{what}: exit {:?} rule {} first refusal {:?}",
                report.exit,
                rule(&report),
                report.first_refusal
            ));
        }
    }
    // Control: with `all` = [B] and Lean's flags the block reaches the kernel,
    // whose positivity check refuses `B`, and `bad` with it.
    let honest = check_bytes(
        exports::negative_block_export("[6]", true, true).as_bytes(),
        ExportCheckOptions::default(),
    );
    if honest.exit != ExitClass::Reject
        || verdict_of(&honest, "B") != Some(DeclarationVerdict::Refused)
        || verdict_of(&honest, "bad") != Some(DeclarationVerdict::Refused)
    {
        failures.push(format!(
            "`all` = [B]: exit {:?} reader {:?} first refusal {:?}",
            honest.exit, honest.reader_error, honest.first_refusal
        ));
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// An inductive record must be its block: every type's and recursor's `all`
/// is the record's `types`, every constructor's `induct` is one of them, and
/// the types' `ctors` lists, in order, are the record's `ctors`.
#[test]
fn test_front_door_inductive_record_must_be_one_block() {
    let honest = archived("good/tutorial/037_boolType.ndjson");
    let arms = [
        (
            "a recursor's `all` is not the block",
            replaced_once(
                &honest,
                r#"{"all":[1],"isUnsafe":false,"k":false"#,
                r#"{"all":[],"isUnsafe":false,"k":false"#,
            ),
        ),
        (
            "a constructor's `induct` is not a type of the block",
            replaced_once(
                &honest,
                r#"{"cidx":1,"induct":1,"#,
                r#"{"cidx":1,"induct":2,"#,
            ),
        ),
        (
            "a type lists fewer constructors than the record",
            replaced_once(&honest, r#""ctors":[2,3]"#, r#""ctors":[2]"#),
        ),
        (
            "a type lists its constructors in another order",
            replaced_once(&honest, r#""ctors":[2,3]"#, r#""ctors":[3,2]"#),
        ),
        (
            "a type's `all` is not the block",
            replaced_once(
                &honest,
                r#""types":[{"all":[1],"#,
                r#""types":[{"all":[1,1],"#,
            ),
        ),
    ];
    let mut failures = Vec::new();
    for (what, text) in arms {
        let report = check_bytes(text.as_bytes(), ExportCheckOptions::default());
        if report.exit != ExitClass::Reject || rule(&report) != "inductive-block-shape" {
            failures.push(format!(
                "{what}: exit {:?} rule {} first refusal {:?}",
                report.exit,
                rule(&report),
                report.first_refusal
            ));
        }
    }
    let control = check_bytes(honest.as_bytes(), ExportCheckOptions::default());
    if control.exit != ExitClass::Accept {
        failures.push(format!("the honest Bool export: {control:?}"));
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// A stored `isRec` that is not Lean's (block-level: some constructor binder
/// domain names a type of the block) is refused by the reader, so structure
/// eta can never run on a recursive structure (finding C2).
#[test]
fn test_front_door_inductive_flags_must_be_the_kernels() {
    let mut failures = Vec::new();
    let forged = check_bytes(
        exports::structure_eta_export(false).as_bytes(),
        ExportCheckOptions::default(),
    );
    if forged.exit != ExitClass::Reject || rule(&forged) != "inductive-flag-mismatch" {
        failures.push(format!(
            "isRec forged false: exit {:?} rule {} first refusal {:?}",
            forged.exit,
            rule(&forged),
            forged.first_refusal
        ));
    }
    // Control: with Lean's flag the family is admitted and the eta theorem is
    // refused, as Lean refuses it.
    let honest = check_bytes(
        exports::structure_eta_export(true).as_bytes(),
        ExportCheckOptions::default(),
    );
    let family_ok = ["S", "S.mk", "S.rec"]
        .iter()
        .all(|n| verdict_of(&honest, n) == Some(DeclarationVerdict::Admitted));
    if honest.exit != ExitClass::Reject
        || !family_ok
        || honest.first_refusal.as_ref().map(|f| f.name.as_str()) != Some("t")
    {
        failures.push(format!(
            "isRec true: exit {:?} reader {:?} first refusal {:?}",
            honest.exit, honest.reader_error, honest.first_refusal
        ));
    }
    // isReflexive: `RTree`'s constructor takes a function into `RTree`.
    let rtree = archived("good/tutorial/122_rtreeRecReduction.ndjson");
    let forged = check_bytes(
        replaced_once(&rtree, r#""isReflexive":true"#, r#""isReflexive":false"#).as_bytes(),
        ExportCheckOptions::default(),
    );
    if forged.exit != ExitClass::Reject || rule(&forged) != "inductive-flag-mismatch" {
        failures.push(format!(
            "isReflexive forged false: exit {:?} rule {}",
            forged.exit,
            rule(&forged)
        ));
    }
    // Lean's flag is per BLOCK: in `mutual A | a : A; B | b : A → B`, `A`
    // stores `isRec` true though no constructor of `A` names `A`.
    let mutual = |rec_a: bool, rec_b: bool| {
        check_bytes(
            exports::mutual_export(rec_a, rec_b).as_bytes(),
            ExportCheckOptions::default(),
        )
    };
    let both = mutual(true, true);
    if both.exit != ExitClass::Accept {
        failures.push(format!(
            "mutual, Lean's flags: exit {:?} reader {:?} first refusal {:?}",
            both.exit, both.reader_error, both.first_refusal
        ));
    }
    let per_type = mutual(false, true);
    if per_type.exit != ExitClass::Reject || rule(&per_type) != "inductive-flag-mismatch" {
        failures.push(format!(
            "mutual, a per-type flag: exit {:?} rule {}",
            per_type.exit,
            rule(&per_type)
        ));
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// -- reader cost bounds --------------------------------------------------------

/// A level DAG of a few KB must not make the reader walk its exponentially
/// large tree: over the budget it declines by name (finding C3).
#[test]
fn test_front_door_level_tree_budget_declines_a_level_dag() {
    let bomb = exports::level_ladder(64);
    assert!(bomb.len() < 8 << 10, "{} bytes", bomb.len());
    let report = within(Duration::from_secs(60), move || {
        check_bytes(bomb.as_bytes(), ExportCheckOptions::default())
    });
    assert_eq!(report.exit, ExitClass::Decline, "{report:?}");
    assert_eq!(rule(&report), "level-tree-budget", "{report:?}");
    // Control: a ladder whose tree is under the budget is read.
    let small = exports::level_ladder(6);
    let report = within(Duration::from_secs(60), move || {
        check_bytes(small.as_bytes(), ExportCheckOptions::default())
    });
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
}

/// Expressions whose kernel metadata words collide (lets that differ only in
/// their names, lambdas that differ only in binder information under long
/// application spines) must not make hash-consing quadratic (finding C4).
#[test]
fn test_front_door_expression_interning_stays_linear_on_metadata_collisions() {
    let text = exports::colliding_lets_export(200_000);
    let report = within(Duration::from_secs(120), move || {
        check_bytes(text.as_bytes(), ExportCheckOptions::default())
    });
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");

    let text = exports::binder_info_spines_export(80_000);
    let report = within(Duration::from_secs(60), move || {
        check_bytes(text.as_bytes(), ExportCheckOptions::default())
    });
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
}

// -- R117 and R118: every rule an arm ----------------------------------------

/// Decision R117: a `partial` definition left out declines (exit 2), never
/// accepts; an `unsafe` one is left out and declines nothing; a `safe` one is
/// admitted (finding C8).
#[test]
fn test_front_door_partial_definition_left_out_declines_r_n3() {
    let with_def = |safety: &str| {
        check_bytes(
            exports::partial_def_export(safety).as_bytes(),
            ExportCheckOptions::default(),
        )
    };
    let partial = with_def("partial");
    assert_eq!(partial.exit, ExitClass::Decline, "{partial:?}");
    assert_eq!(partial.exit_code, 2);
    assert_eq!(
        (partial.refused, partial.not_replayable),
        (0, 1),
        "{partial:?}"
    );
    assert!(
        partial
            .decline_reason
            .as_deref()
            .is_some_and(|r| r.contains("R117")),
        "{partial:?}"
    );
    let unsafe_def = with_def("unsafe");
    assert_eq!(unsafe_def.exit, ExitClass::Accept, "{unsafe_def:?}");
    assert_eq!(unsafe_def.not_replayable, 1);
    let safe = with_def("safe");
    assert_eq!(safe.exit, ExitClass::Accept, "{safe:?}");
    assert_eq!(safe.admitted, 2);
}

/// The export's own `axiom Quot.sound` must state the kernel's: `add_quot`
/// installs the kernel's statement under that name, so a forged record is
/// refused, never reported admitted (finding C9, rule 1).
#[test]
fn test_front_door_forged_quot_sound_is_refused() {
    let honest = archived("good/tutorial/129_quotSoundType.ndjson");
    let forged = exports::forged_quot_sound(&honest);
    let report = check_bytes(forged.as_bytes(), ExportCheckOptions::default());
    assert_eq!(report.exit, ExitClass::Reject, "{:?}", report.first_refusal);
    let record = report
        .records
        .iter()
        .find(|r| r.name == "Quot.sound")
        .expect("declared");
    assert_eq!(record.verdict, DeclarationVerdict::Refused, "{record:?}");
    assert!(
        record
            .reason
            .as_deref()
            .unwrap_or_default()
            .contains("the kernel's quotient states"),
        "{record:?}"
    );
    let control = check_bytes(honest.as_bytes(), ExportCheckOptions::default());
    assert_eq!(
        control.exit,
        ExitClass::Accept,
        "{:?}",
        control.first_refusal
    );
}

/// The rest of R118's rules, each by its own name (finding C9, rules 2-5).
#[test]
fn test_front_door_every_r_n4_rule_has_its_arm() {
    let long = std::io::BufReader::new(
        std::io::Cursor::new(format!("{META}\n"))
            .chain(std::io::repeat(b' ').take(MAX_LINE_BYTES as u64 + 1)),
    );
    let mut values: Vec<String> = HONEST.iter().map(|s| (*s).to_owned()).collect();
    let payload = format!("[{}0]", "0,".repeat(1 << 21));
    values.insert(
        3,
        exports::nested_mdata_lines(0)[3].replace("\"k\":", &format!("\"k\":{payload}")),
    );
    let format = |v: &str| {
        META.replace(
            r#""format":{"version":"3.1.0"}"#,
            &format!(r#""format":{{"version":"{v}"}}"#),
        )
    };
    let arms: Vec<(&str, ExportReport, ExitClass, &str)> = vec![
        (
            "a `.` inside a name component (stored escaped, R118)",
            check_owned(&perturbed(0, r#"{"in":1,"str":{"pre":0,"str":"a.b"}}"#)),
            ExitClass::Accept,
            "<none>",
        ),
        (
            "two names stored alike once escaped",
            check_lines(
                META,
                &[
                    r#"{"in":1,"str":{"pre":0,"str":"a.b"}}"#,
                    "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"\u{2024}a\u{2024}b\"}}",
                ],
            ),
            ExitClass::Decline,
            "name-collision",
        ),
        (
            "a line over MAX_LINE_BYTES",
            check_export_reader(long, ExportCheckOptions::default()),
            ExitClass::Decline,
            "line-too-long",
        ),
        (
            "values nested past MAX_DEPTH",
            check_owned(&exports::nested_mdata_lines(600)),
            ExitClass::Decline,
            "too-deep",
        ),
        (
            "a payload nested 500 deep",
            check_owned(&exports::nested_mdata_lines(500)),
            ExitClass::Accept,
            "<none>",
        ),
        (
            "a lone surrogate",
            check_owned(&perturbed(0, r#"{"in":1,"str":{"pre":0,"str":"\ud800"}}"#)),
            ExitClass::Reject,
            "invalid-escape",
        ),
        (
            "an escaped duplicate key (lean4#15628)",
            check_owned(&perturbed(
                0,
                r#"{"in":1,"str":{"pre":0,"\u0070re":1,"str":"a"}}"#,
            )),
            ExitClass::Reject,
            "duplicate-key",
        ),
        (
            "a de Bruijn index above u32",
            check_owned(&perturbed(2, r#"{"ie":0,"bvar":4294967296}"#)),
            ExitClass::Decline,
            "representation-limit",
        ),
        (
            "an index above u64",
            check_owned(&perturbed(
                0,
                r#"{"in":18446744073709551616,"str":{"pre":0,"str":"a"}}"#,
            )),
            ExitClass::Decline,
            "representation-limit",
        ),
        (
            "a line of 2^21 JSON values",
            check_owned(&values),
            ExitClass::Decline,
            "json-value-budget",
        ),
        (
            "format 3.0.0",
            check_lines(&format("3.0.0"), &HONEST),
            ExitClass::Decline,
            "format-version-unsupported",
        ),
        (
            "format 3.1.7",
            check_lines(&format("3.1.7"), &HONEST),
            ExitClass::Accept,
            "<none>",
        ),
    ];
    let failures: Vec<String> = arms
        .iter()
        .filter(|(_, report, exit, expected)| report.exit != *exit || rule(report) != *expected)
        .map(|(what, report, exit, expected)| {
            format!(
                "{what}: exit {:?} rule {} (expected {exit:?} by {expected})",
                report.exit,
                rule(report)
            )
        })
        .collect();
    assert!(failures.is_empty(), "{failures:#?}");
}
