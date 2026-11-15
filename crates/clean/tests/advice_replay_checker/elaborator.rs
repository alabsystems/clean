// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The elaborator's verdict, apart from any backend: `clean check`.
//!
//! Two things are held here, both against `data/kcheck_execution_gaps.json`:
//!
//! * every R4 item of `designs/2026-11-12-kcheck-model-first.md` (the ten
//!   items the plan's X1 row asks for, one probe each under `programs/`) is
//!   accepted or refused by `clean check` as its row's `elaborator` pin says;
//!   the backends are pinned by the lane tests in the parent file;
//! * every program under `rejected/` is one pinned Lean REJECTS (its recorded
//!   transcript says so), and `clean check` lands on its pinned outcome: a
//!   refusal by name, or an acceptance that a `false_acceptances` row of the
//!   gap list owns. These are the negative controls of the frontend fix of
//!   ledger class (197) and of R4 item (vi), and the false acceptance found
//!   beside class (197).

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use serde_json::Value;

use super::{
    check_pin, check_site, clean_cmd, fixture, gaps, pinned_row, program, report, rows, str_field,
    text, Outcome, Ran, GAPS, TIMEOUT,
};

/// The ten items of the design's risk R4, in order.
const R4_ITEMS: [&str; 10] = ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x"];

/// `clean check <source>` in a fresh scratch directory.
fn clean_check(source: &Path) -> Ran {
    clean_cmd(&[
        OsStr::new("check"),
        OsStr::new("--json"),
        source.as_os_str(),
    ])
}

/// The elaborator's outcome: `ACCEPTED` when every declaration passed without
/// parser recovery, else
/// `REFUSED` with the first failed declaration's line (`✗ name: …`) or the
/// CLI's own `Error:` line when none was reached.
fn classify_check(name: &str, ran: &Ran) -> Outcome {
    let status = ran
        .status
        .unwrap_or_else(|| panic!("{name}: `clean check` did not finish in {TIMEOUT:?}"));
    let out = text(&ran.stdout);
    let err = text(&ran.stderr);
    if let Ok(report) = serde_json::from_slice::<Value>(&ran.stdout) {
        let recovery = report["parser_recovery"]
            .as_array()
            .expect("parser recovery array");
        if let Some(note) = recovery.first() {
            return Outcome {
                class: "REFUSED",
                refusal: note.as_str().expect("parser recovery string").to_string(),
            };
        }
        if status.code() == Some(0) && report["status"] == "pass" {
            return Outcome {
                class: "ACCEPTED",
                refusal: String::new(),
            };
        }
        if let Some(error) = report["errors"]
            .as_array()
            .and_then(|errors| errors.first())
        {
            return Outcome {
                class: "REFUSED",
                refusal: format!("✗ {}", error.as_str().expect("error string")),
            };
        }
    }
    let failed = out
        .lines()
        .chain(err.lines())
        .map(str::trim_start)
        .find(|l| l.starts_with("✗ "));
    let line = failed.or_else(|| err.lines().find(|l| l.starts_with("Error: ")));
    match line {
        Some(line) => Outcome {
            class: "REFUSED",
            refusal: line.trim().to_string(),
        },
        None => panic!(
            "{name}: `clean check` failed (status {status:?}) without naming a declaration or an \
             error.\n--- stdout\n{out}\n--- stderr\n{err}"
        ),
    }
}

fn rejected_dir() -> PathBuf {
    fixture().join("rejected")
}

fn rejected_names() -> Vec<String> {
    let dir = rejected_dir();
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            (path.extension()? == "lean").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    names
}

/// The R4 table names each item once, in order, and each item's probe is a
/// program with an `elaborator` pin; every `_r4_` program is some item's.
#[test]
fn the_r4_table_names_every_item_once() {
    let pins = gaps();
    let table = rows(&pins, "r4_items");
    let items: Vec<&str> = table
        .iter()
        .map(|row| str_field(row, "item", "an r4_items row"))
        .collect();
    assert_eq!(
        items, R4_ITEMS,
        "{GAPS}: `r4_items` is the design's ten items, in order"
    );
    let mut probes = BTreeSet::new();
    for row in table {
        let item = str_field(row, "item", "an r4_items row");
        assert!(
            !str_field(row, "what", item).is_empty(),
            "R4 item {item}: empty `what`"
        );
        let name = str_field(row, "program", item);
        assert!(program(name).is_file(), "R4 item {item}: no program {name}");
        let pin = &pinned_row(&pins, name)["elaborator"];
        str_field(pin, "outcome", name);
        probes.insert(name.to_string());
    }
    for name in rows(&pins, "acyclic_controls") {
        let name = name.as_str().expect("acyclic control name");
        assert!(program(name).is_file(), "missing historical control {name}");
        str_field(&pinned_row(&pins, name)["elaborator"], "outcome", name);
        assert!(
            probes.insert(name.to_string()),
            "control duplicates a primary probe"
        );
    }
    let r4_rows: BTreeSet<String> = rows(&pins, "programs")
        .iter()
        .map(|row| str_field(row, "name", "a program row").to_string())
        .filter(|name| name.contains("_r4_"))
        .collect();
    assert_eq!(
        probes, r4_rows,
        "every `_r4_` program is the probe of one R4 item"
    );
}

/// Each R4 probe through `clean check`, against its `elaborator` pin. The
/// lane tests in the parent file pin the same programs on the backends.
#[test]
fn every_r4_item_lands_on_its_pinned_elaborator_outcome() {
    let pins = gaps();
    let mut failures = Vec::new();
    for row in rows(&pins, "r4_items") {
        let name = str_field(row, "program", "an r4_items row");
        let live = classify_check(name, &clean_check(&program(name)));
        eprintln!("x1: {name:<44} check={} {}", live.class, live.refusal);
        check_pin(
            name,
            "clean check",
            &live,
            &pinned_row(&pins, name)["elaborator"],
            &mut failures,
        );
    }
    for name in rows(&pins, "acyclic_controls") {
        let name = name.as_str().expect("acyclic control name");
        let live = classify_check(name, &clean_check(&program(name)));
        check_pin(
            name,
            "clean check",
            &live,
            &pinned_row(&pins, name)["elaborator"],
            &mut failures,
        );
    }
    report("Clean's elaborator on the R4 items", &failures);
}

/// NEGATIVE CONTROLS: programs pinned Lean rejects. Each row says what Lean
/// said (held against the committed transcript) and what `clean check` does.
/// A refusal is pinned by name; an acceptance is a false acceptance and must
/// be owned by a `false_acceptances` row, so it fails here the day it closes.
#[test]
fn every_program_lean_rejects_lands_on_its_pinned_check_outcome() {
    let pins = gaps();
    let table = rows(&pins, "rejected_by_lean");
    let on_disk: BTreeSet<String> = rejected_names().into_iter().collect();
    let pinned: BTreeSet<String> = table
        .iter()
        .map(|row| str_field(row, "name", "a rejected_by_lean row").to_string())
        .collect();
    assert_eq!(pinned, on_disk, "{GAPS} `rejected_by_lean` vs rejected/");
    let owners: BTreeSet<&str> = rows(&pins, "false_acceptances")
        .iter()
        .map(|row| str_field(row, "id", "a false_acceptances row"))
        .collect();
    let mut owned = BTreeSet::new();
    let mut failures = Vec::new();
    for row in table {
        let name = str_field(row, "name", "a rejected_by_lean row");
        let transcript = rejected_dir().join("expected");
        let rc = std::fs::read_to_string(transcript.join(format!("{name}.rc")))
            .unwrap_or_else(|e| panic!("rejected/expected/{name}.rc: {e}"));
        assert_ne!(rc.trim(), "0", "{name}: pinned Lean must reject it");
        let said = std::fs::read_to_string(transcript.join(format!("{name}.stdout")))
            .unwrap_or_else(|e| panic!("rejected/expected/{name}.stdout: {e}"));
        let lean_error = str_field(row, "lean_error", name);
        assert!(
            !lean_error.is_empty() && said.contains(lean_error),
            "{name}: Lean's transcript does not say `{lean_error}`:\n{said}"
        );
        let pin = &row["clean_check"];
        let owner = pin["false_acceptance"].as_str().unwrap_or_default();
        assert_eq!(
            str_field(pin, "outcome", name) == "ACCEPTED",
            !owner.is_empty(),
            "{name}: exactly an acceptance of a program Lean rejects names its false_acceptances row"
        );
        if !owner.is_empty() {
            assert!(
                owners.contains(owner),
                "{name}: unknown false acceptance `{owner}`"
            );
            owned.insert(owner);
        }
        let live = classify_check(
            name,
            &clean_check(&rejected_dir().join(format!("{name}.lean"))),
        );
        eprintln!("x1: {name:<44} check={} {}", live.class, live.refusal);
        check_pin(name, "clean check", &live, pin, &mut failures);
    }
    for row in rows(&pins, "false_acceptances") {
        let id = str_field(row, "id", "a false_acceptances row");
        assert!(
            owned.contains(id),
            "false acceptance `{id}` is shown by no rejected program"
        );
        assert!(
            !str_field(row, "construct", id).is_empty(),
            "`{id}`: empty construct"
        );
        check_site(id, &row["site"]);
    }
    report("`clean check` on what pinned Lean rejects", &failures);
}

/// The `elaborator` pins are explained like the lane pins: exactly a refused
/// row cites a gap, and every cited gap exists.
#[test]
fn every_elaborator_refusal_cites_a_gap() {
    let pins = gaps();
    let ids: BTreeSet<&str> = rows(&pins, "gaps")
        .iter()
        .map(|gap| str_field(gap, "id", "a gap"))
        .collect();
    for row in rows(&pins, "programs") {
        let name = str_field(row, "name", "a program row");
        let pin: &Value = &row["elaborator"];
        if pin.is_null() {
            continue;
        }
        let named: Vec<&str> = pin["gaps"]
            .as_array()
            .map(|g| g.iter().filter_map(Value::as_str).collect())
            .unwrap_or_default();
        assert_eq!(
            str_field(pin, "outcome", name) == "ACCEPTED",
            named.is_empty(),
            "{name} [elaborator]: exactly a refused row cites the gap that refuses it"
        );
        for id in named {
            assert!(ids.contains(id), "{name} [elaborator]: unknown gap `{id}`");
        }
    }
}

/// A successful exit with declarations checked must still fail classification
/// when the parser recovered and dropped part of the source.
#[test]
fn parser_recovery_is_never_an_acceptance() {
    let dir = tempfile::tempdir().expect("recovery fixture");
    let source = dir.path().join("Recovery.lean");
    std::fs::write(
        &source,
        "def good : Nat := 1\ntermination_by structural n unexpected\ndef sentinel : Nat := 2\n",
    )
    .expect("plant malformed termination clause");
    let ran = clean_check(&source);
    let report: Value = serde_json::from_slice(&ran.stdout).expect("check JSON");
    assert!(!report["parser_recovery"]
        .as_array()
        .expect("recovery")
        .is_empty());
    let outcome = classify_check("planted recovery", &ran);
    assert_eq!(outcome.class, "REFUSED");
    assert!(outcome.refusal.contains("parser recovery"));
}

/// The clause names rebind arguments after the colon, rather than naming
/// pattern variables. Header binders stay in scope. Lean accepts these rows.
#[test]
fn structural_clause_parity_rows_elaborate_without_recovery() {
    let path = super::repo_root().join("tests/fixtures/parser_parity/termination_structural.tsv");
    let rows = std::fs::read_to_string(path).expect("parity rows");
    let dir = tempfile::tempdir().expect("parity scratch");
    let mut count = 0;
    for row in rows
        .lines()
        .filter(|row| !row.starts_with('#') && !row.is_empty())
    {
        let source = dir.path().join("Structural.lean");
        std::fs::write(
            &source,
            row.split('\t').next().expect("input").replace("\\n", "\n"),
        )
        .expect("parity source");
        let outcome = classify_check("structural parity", &clean_check(&source));
        assert_eq!(outcome.class, "ACCEPTED", "{}", outcome.refusal);
        count += 1;
    }
    assert_eq!(count, 5);
}
