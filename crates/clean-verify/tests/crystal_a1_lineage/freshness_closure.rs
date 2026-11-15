// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Two closures around `freshness.rs`, both of the same shape: a check that
//! cannot go stale by OMISSION.**
//!
//! `freshness.rs` pins the CHAINED set and the two revalidation records that
//! existed when it was written. Both are lists, and a list is exactly what a
//! new fixture or a new record slips past. This file replaces each list with
//! the property it was standing in for:
//!
//! 1. **Every committed `*.trust-ir.txt` is compared against a live dump.**
//!    `the_freshness_script_covers_exactly_the_chained_bodies` pins the chained
//!    set, which is all the rest of that gate reasons about — so it could not
//!    see a fixture that is committed, asserted against, and simply not chained.
//!    There was one: `level_is_zero_deref_callee.trust-ir.txt`, read verbatim by
//!    `crystal_a1_lineage/level_is_zero.rs`, is the recorded reason `is_zero`
//!    cannot be transcribed, and until 2026-08-19 no dump was ever compared to
//!    it. It is now in the script's `EXTRA_BODIES` table, and the assertion here
//!    is the CLOSURE — every fixture in the directory appears in one table or
//!    the other — so a thirteenth cannot arrive uncompared.
//!
//!    The same test carries a SECOND closure of the same shape over the
//!    MODULE-TABLE fixtures, `*.trust-ir-rows.txt` (2026-09-09): a verbatim
//!    copy of module rows that are not a function body — a `type ty.N` alias
//!    and the `global … @<name> …` row it types — compared by the script's
//!    `EXTRA_ROWS` loop. The suffix is different ON PURPOSE: it keeps those
//!    rows out of `check_crystal_fixture_pins.py`'s `*.trust-ir.txt` glob and
//!    out of the 21-row rebaseline record that gate reads, which means this
//!    closure is the ONLY thing that notices a rows fixture nothing compares.
//!
//! 2. **Every revalidation record is held to the same standard, including ones
//!    added after this file.** `RECORDS` is append-only and each entry keeps its
//!    own account of its own build; nothing here rewrites an earlier one.
//!
//! Neither of these SCHEDULES the comparison — that needs the Trust compiler,
//! which this suite does not run, and it remains a re-measurement duty with a
//! command. What `verify_runner.py::TARGET_EXTRA_PATHS` now adds is the other
//! half of the gap `freshness.rs` names: editing a record or the script demotes
//! this target's recorded green to UNKNOWN instead of leaving it reading fresh.

use std::collections::BTreeSet;
use std::path::PathBuf;

use super::freshness::{read_json, repo_root, EVIDENCE, HEAD_MEASURED, RECORD, RECORD_2, SCRIPT};

/// The THIRD revalidation: trust `28fb5dd812` (origin/main, 2026-08-19), 68
/// commits past `RECORD_2`'s producer, spanning wave-GS, wave-CP, wave-AF and
/// vtable slices 16/17 — every one of which touches the lowering that emits the
/// bodies these fixtures pin.
pub(crate) const RECORD_3: &str = "data/crystal_chain_revalidation_2026-08-19_28fb5dd812.json";

/// Every revalidation, oldest first. **Append-only.** A record is a dated
/// measurement against ONE producer, and a later one confirms rather than
/// replaces it: overwriting a correct record to make it look freshly minted
/// destroys the evidence that a per-build identity SURVIVED a producer change,
/// which is the only thing separating a stable digest from an unchecked one.
pub(crate) const RECORDS: &[&str] = &[RECORD, RECORD_2, RECORD_3];

fn script_table_keys(src: &str, marker: &str) -> BTreeSet<String> {
    let table = src
        .split_once(marker)
        .map(|(_, rest)| rest.split_once("\n}").map_or(rest, |(t, _)| t))
        .unwrap_or_else(|| panic!("{SCRIPT} has no `{marker}` table"));
    table
        .lines()
        .filter_map(|l| l.trim().strip_prefix('"'))
        .filter_map(|l| l.split_once('"'))
        .map(|(k, _)| k.to_string())
        .collect()
}

/// **A committed fixture that appears in NEITHER of the script's tables is a
/// fixture nothing compares to a dump.** That is the whole failure class, stated
/// as a closure instead of as a list.
#[test]
fn every_committed_trust_ir_fixture_is_compared_against_a_live_dump() {
    let p = repo_root().join(SCRIPT);
    let src = std::fs::read_to_string(&p).unwrap_or_else(|e| {
        panic!(
            "{} is missing or unreadable ({e}). It is the ONLY thing in this repo that \
             compares a chain fixture against a live trustc dump.",
            p.display()
        )
    });
    let mut covered = script_table_keys(&src, "BODIES: dict[str, str] = {");
    covered.extend(script_table_keys(&src, "EXTRA_BODIES: dict[str, str] = {"));

    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut committed: BTreeSet<String> = BTreeSet::new();
    let mut rows_committed: BTreeSet<String> = BTreeSet::new();
    for entry in std::fs::read_dir(&dir).expect("the fixtures directory must exist") {
        let name = entry.expect("readable dir entry").file_name();
        let name = name.to_string_lossy();
        if let Some(stem) = name.strip_suffix(".trust-ir.txt") {
            committed.insert(stem.to_string());
        } else if let Some(stem) = name.strip_suffix(".trust-ir-rows.txt") {
            rows_committed.insert(stem.to_string());
        }
    }
    assert!(
        !committed.is_empty(),
        "no *.trust-ir.txt fixtures under {}",
        dir.display()
    );

    // `tests/fixtures/synth/` holds the W2a SYNTHETIC modules — authored for
    // the semdiff battery, emitted by no producer, so no live dump can
    // re-derive them and this closure deliberately does not cover them. That
    // is a checked invariant, not an escape hatch: every file there must
    // SELF-DECLARE as synthetic and carry the `synth_` prefix, so an emitted
    // fixture can never hide from this closure by moving directories.
    let synth_dir = dir.join("synth");
    if synth_dir.is_dir() {
        for entry in std::fs::read_dir(&synth_dir).expect("readable synth fixtures dir") {
            let entry = entry.expect("readable dir entry");
            let name = entry.file_name().to_string_lossy().into_owned();
            let Some(stem) = name.strip_suffix(".trust-ir.txt") else {
                continue;
            };
            assert!(
                stem.starts_with("synth_"),
                "tests/fixtures/synth/{name} lacks the synth_ prefix; the synth directory is \
                 only for authored synthetic modules, never emitted bodies"
            );
            let text = std::fs::read_to_string(entry.path()).expect("readable synth fixture");
            assert!(
                text.contains("SYNTHETIC MODULE"),
                "tests/fixtures/synth/{name} does not self-declare as a SYNTHETIC MODULE; an \
                 emitted body may not live outside this freshness closure"
            );
        }
    }

    let uncovered: Vec<&String> = committed.difference(&covered).collect();
    assert!(
        uncovered.is_empty(),
        "these committed trust-ir fixtures are compared against NO live dump: {uncovered:?}. \
         Add each to BODIES (a chain) or EXTRA_BODIES (asserted against but not chained) in \
         {SCRIPT}. A fixture nothing re-derives is a gate asserting against IR the producer may \
         no longer emit."
    );
    let phantom: Vec<&String> = covered.difference(&committed).collect();
    assert!(
        phantom.is_empty(),
        "{SCRIPT} names fixtures that do not exist: {phantom:?}"
    );

    // SECOND CLOSURE — the module-table fixtures. `*.trust-ir-rows.txt` is
    // outside every other gate's glob (see the module doc), so a rows fixture
    // that the script's `EXTRA_ROWS` table does not name is compared against
    // NO live dump by anything at all.
    let rows_covered = script_table_keys(&src, "EXTRA_ROWS: dict[str, str] = {");
    let rows_uncovered: Vec<&String> = rows_committed.difference(&rows_covered).collect();
    assert!(
        rows_uncovered.is_empty(),
        "these committed trust-ir-rows fixtures are compared against NO live dump: \
         {rows_uncovered:?}. Add each to EXTRA_ROWS (a module-table row, not a body) in \
         {SCRIPT}. A fixture nothing re-derives is a gate asserting against IR the producer \
         may no longer emit."
    );
    let rows_phantom: Vec<&String> = rows_covered.difference(&rows_committed).collect();
    assert!(
        rows_phantom.is_empty(),
        "{SCRIPT} EXTRA_ROWS names rows fixtures that do not exist: {rows_phantom:?}"
    );
}

/// **Every record in [`RECORDS`], not just the two that existed when
/// `freshness.rs` was written.**
///
/// Same standard for each: it covers exactly the chained bodies, no body drifted
/// STRUCTURALLY, no body's instructions moved, and every drift class it admits is
/// one the script actually classifies. A record committed with a `STRUCTURAL`
/// verdict fails here — that is a re-DERIVATION of the spec module and its
/// refinement theorem, never a fixture refresh.
#[test]
fn every_revalidation_record_records_no_structural_drift() {
    for path in RECORDS {
        let record = read_json(path);
        let chains = record["chains"]
            .as_object()
            .unwrap_or_else(|| panic!("{path} must carry a `chains` object"));
        assert_eq!(
            chains.len(),
            EVIDENCE.len() - HEAD_MEASURED.len(),
            "{path} must cover every chained body THAT EXISTED WHEN IT WAS TAKEN, and nothing \
             else. A record is a dated measurement and cannot cover a later chain; \
             `freshness::HEAD_MEASURED` names those, each gated on its own live-dump record."
        );
        for (stem, _) in EVIDENCE {
            if HEAD_MEASURED.contains(stem) {
                continue;
            }
            let body = &chains[*stem]["emitted_body_vs_committed_fixture"];
            let verdict = body["verdict"].as_str().unwrap_or("<missing>");
            assert!(
                verdict == "IDENTICAL" || verdict == "NUMBERING-ONLY",
                "{path} / {stem}: recorded `{verdict}`. Only IDENTICAL and NUMBERING-ONLY are \
                 survivable: a STRUCTURAL verdict means the producer no longer emits the body \
                 this chain's spec module transcribes."
            );
            assert_eq!(
                body["instructions_moved"].as_u64(),
                Some(0),
                "{path} / {stem}: instructions moved — not a fixture refresh."
            );
            for class in body["drift_classes"].as_array().unwrap_or(&Vec::new()) {
                let c = class.as_str().unwrap_or("");
                assert!(
                    matches!(
                        c,
                        "functy-index"
                            | "type-table-index"
                            | "callee-index"
                            | "global-index"
                            | "loc-file-index"
                    ),
                    "{path} / {stem}: unknown drift class `{c}` — not one {SCRIPT} classifies"
                );
            }
        }
    }
}

/// The records form a CHAIN, and no link may be dropped.
///
/// Each record after the first names its predecessor, and that predecessor must
/// still be in the tree: a superseding record does not license deleting the one
/// it extends, because each is the only account of its own build.
#[test]
fn the_revalidation_records_form_an_unbroken_chain() {
    for pair in RECORDS.windows(2) {
        let (prev, next) = (pair[0], pair[1]);
        let record = read_json(next);
        assert_eq!(
            record["supersedes"]["record"].as_str(),
            Some(prev),
            "{next} must name {prev} as the record it extends, or the two are unrelated files \
             that happen to share a shape"
        );
        assert!(
            repo_root().join(prev).is_file(),
            "{next} names {prev} as the record it extends, but that file is gone"
        );
    }
}
