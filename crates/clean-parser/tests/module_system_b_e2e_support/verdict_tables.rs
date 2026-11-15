// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Replays pinned Lean's file-level verdicts on the module-system spellings
//! (plan item `formats-module-spelling-refusals`) through `parse_file`.
//!
//! `tests/fixtures/module_spellings/verdicts.tsv` and `modifier_matrix.tsv`
//! were printed by `lean <file>` on v4.30.0-rc2 and v4.33.1 alike, which
//! each row's `lean_toolchains` column names (`probe.py` beside them
//! regenerates both, and refuses a row the toolchains disagree on). For each row, a file Lean
//! accepts must parse with no recovery placeholder, and a file Lean refuses
//! must be refused with Lean's FIRST message, position included, byte for
//! byte. The one class Clean does not yet meet is pinned below by its own
//! shape, so it fails the day it closes.

use clean_parser::{parse_file, SurfaceDecl};

const VERDICTS: &str = include_str!("../../../../tests/fixtures/module_spellings/verdicts.tsv");
const MATRIX: &str =
    include_str!("../../../../tests/fixtures/module_spellings/modifier_matrix.tsv");
const LEAN_TOOLCHAIN: &str = include_str!("../../../../lean-toolchain");

/// The toolchains every row must have been printed by: the `lean-toolchain`
/// pin, and v4.33.1, the release the plan item measured beside it.
fn required_toolchains() -> Vec<&'static str> {
    let pin = LEAN_TOOLCHAIN
        .trim()
        .strip_prefix("leanprover/lean4:")
        .expect("lean-toolchain names a leanprover/lean4 release");
    vec![pin, "v4.33.1"]
}

/// One table row: its id, the columns between id and source, the source, and
/// Lean's verdict with every message it printed.
struct Row {
    id: String,
    fields: Vec<String>,
    source: String,
    lean_accepts: bool,
    lean_messages: Vec<String>,
}

fn rows(table: &str, header: &str) -> Vec<Row> {
    let mut lines = table.lines().filter(|line| !line.starts_with('#'));
    assert_eq!(lines.next(), Some(header), "the table's header moved");
    let required = required_toolchains();
    lines
        .map(|line| {
            let cols: Vec<&str> = line.split('\t').collect();
            assert_eq!(cols.len(), 7, "malformed row {line:?}");
            let printed_by: Vec<&str> = cols[6].split(',').collect();
            for toolchain in &required {
                assert!(
                    printed_by.contains(toolchain),
                    "row {:?} was not printed by Lean {toolchain}: {line:?}",
                    cols[0]
                );
            }
            let lean_accepts = match cols[4] {
                "accept" => true,
                "refuse" => false,
                other => panic!("unknown verdict {other:?} in {line:?}"),
            };
            let lean_messages: Vec<String> = if cols[5].is_empty() {
                Vec::new()
            } else {
                cols[5].split(" | ").map(str::to_owned).collect()
            };
            assert_eq!(
                lean_accepts,
                lean_messages.is_empty(),
                "a verdict disagrees with its messages: {line:?}"
            );
            Row {
                id: cols[0].to_owned(),
                fields: cols[1..3].iter().map(|c| (*c).to_owned()).collect(),
                source: cols[3].replace("\\n", "\n"),
                lean_accepts,
                lean_messages,
            }
        })
        .collect()
}

/// What Clean made of a file: refused with a message, a parse with a
/// recovery placeholder somewhere (also a refusal, by another route), or a
/// clean parse.
#[derive(Debug, PartialEq, Eq)]
enum CleanVerdict {
    Refused(String),
    Recovered,
    Accepted,
}

fn has_raw(decls: &[SurfaceDecl]) -> bool {
    decls.iter().any(|decl| match decl {
        SurfaceDecl::RawDecl { .. } => true,
        SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => has_raw(decls),
        _ => false,
    })
}

fn clean_verdict(source: &str) -> CleanVerdict {
    match parse_file(source) {
        Err(err) => CleanVerdict::Refused(err.to_string()),
        Ok(decls) if has_raw(&decls) => CleanVerdict::Recovered,
        Ok(_) => CleanVerdict::Accepted,
    }
}

/// Lean's verdict on `row`, in the shape Clean must produce.
fn lean_verdict(row: &Row) -> CleanVerdict {
    if row.lean_accepts {
        CleanVerdict::Accepted
    } else {
        CleanVerdict::Refused(row.lean_messages[0].clone())
    }
}

#[test]
fn test_every_verdicts_row_matches_pinned_lean() {
    let rows = rows(
        VERDICTS,
        "id\tmodule\tspelling\tsource\tlean_verdict\tlean_messages\tlean_toolchains",
    );
    assert_eq!(rows.len(), 31, "verdicts.tsv lost or gained a row");
    let mismatches: Vec<String> = rows
        .iter()
        .filter_map(|row| {
            let clean = clean_verdict(&row.source);
            let lean = lean_verdict(row);
            (clean != lean).then(|| {
                format!(
                    "{} ({:?}): Lean {lean:?}, Clean {clean:?}",
                    row.id, row.fields
                )
            })
        })
        .collect();
    assert!(
        mismatches.is_empty(),
        "{} of {} rows differ from pinned Lean:\n{}",
        mismatches.len(),
        rows.len(),
        mismatches.join("\n")
    );
}

/// Clean's `meta` arm takes `meta` only in front of `import` and the
/// declaration keywords, so in front of `section` or `variable` the word is an
/// unknown command (a `RawDecl`), whatever Lean says. Lean accepts three of
/// these eight rows (`meta section`, `public meta section`, `@[expose] public
/// noncomputable meta section`): an over-refusal, left as it stands because
/// widening it moves the source-elab corpus (350 such placeholders in the
/// pinned Mathlib, measured 2026-10-25) and is measured there first.
fn meta_before_section_or_variable(row: &Row) -> bool {
    let (prefix, command) = (&row.fields[0], &row.fields[1]);
    (prefix == "meta" || prefix.ends_with(" meta"))
        && (command == "section" || command == "variable")
}

#[test]
fn test_every_modifier_matrix_row_matches_pinned_lean() {
    let rows = rows(
        MATRIX,
        "id\tprefix\tcommand\tsource\tlean_verdict\tlean_messages\tlean_toolchains",
    );
    assert_eq!(rows.len(), 168, "modifier_matrix.tsv lost or gained a row");
    let mut pinned = Vec::new();
    let mut mismatches = Vec::new();
    for row in &rows {
        let clean = clean_verdict(&row.source);
        if meta_before_section_or_variable(row) {
            pinned.push((row.id.as_str(), row.lean_accepts, clean));
            continue;
        }
        let lean = lean_verdict(row);
        if clean != lean {
            mismatches.push(format!(
                "{} (`{} {}`): Lean {lean:?}, Clean {clean:?}",
                row.id, row.fields[0], row.fields[1]
            ));
        }
    }
    // Each pinned row: (id, whether Lean accepts it, what Clean makes of it).
    let expected_pins: Vec<(&str, bool, CleanVerdict)> = [
        ("m011", true),
        ("m012", false),
        ("m044", true),
        ("m045", false),
        ("m068", true),
        ("m069", false),
        ("m119", false),
        ("m120", false),
    ]
    .into_iter()
    .map(|(id, accepts)| (id, accepts, CleanVerdict::Recovered))
    .collect();
    // One report for both, so a red run names every row that moved.
    assert!(
        mismatches.is_empty() && pinned == expected_pins,
        "{} of {} rows differ from pinned Lean:\n{}\n\
         the pinned `meta` rows (each must stay Recovered until the gap closes):\n{pinned:?}",
        mismatches.len(),
        rows.len(),
        mismatches.join("\n")
    );
}
