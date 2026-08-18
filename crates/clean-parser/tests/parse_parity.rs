// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser parse-parity harness — the permanent guard specified in
//! `docs/plans/PARSER_ELAB_DROPIN_AUDIT_2026-07-08.md` §6 ("`parse_parity`").
//!
//! Model: `crates/clean-kernel/src/env/carrier_differential_tests.rs` (a
//! checked-in Lean-v4.30 ground-truth table replayed row-by-row, exact-match,
//! with a pinned regeneration script). This is the parser analogue: it replays
//! `tests/fixtures/parser_parity/ground_truth.tsv` — 228 probes captured live
//! from the pinned `leanprover/lean4 v4.30.0-rc2` oracle — and, for each probe,
//! classifies clean-parser's outcome as one of:
//!
//! - **MATCH** — clean parses and the tree structurally corresponds to Lean's
//!   (renderer output == the fixture's `lean_tree` skeleton).
//! - **LOUD** — clean returns a `ParseError` where Lean produces a tree. A loud
//!   gap is strictly better than a silent misparse (task-C guidance); it is the
//!   *acceptable* failure mode for not-yet-implemented syntax.
//! - **SILENT-DIVERGENT** — clean parses but the tree disagrees with Lean
//!   (wrong tree), OR clean accepts input Lean rejects at parse time
//!   (over-acceptance). **This is the failure class the phase-1 gates cannot
//!   express** and the whole reason this harness exists.
//!
//! The test PASSES iff every SILENT-DIVERGENT probe is pinned in [`ALLOWLIST`]
//! and every ALLOWLIST entry is still divergent — a two-way **ratchet**. As each
//! Brick-3 item lands and flips a probe to MATCH/LOUD, its allowlist entry goes
//! stale and this test fails until the entry is removed. New silent misparses
//! fail immediately. The scoreboard (per family: match/loud/divergent) prints on
//! every run so coverage progress is measurable.
//!
//! Two further ratchets make the whole board load-bearing, not just the
//! divergent column:
//!
//! - **MATCH floors** — every family's MATCH count must equal its pinned
//!   [`MATCH_FLOORS`] entry, two-way: below the floor is a MATCH→LOUD
//!   regression (LOUD alone is always "acceptable", so without floors such a
//!   regression passed silently); above the floor is progress that must bump
//!   the floor. The failure message prints the measured table to paste.
//! - **README pinning** — the scoreboard block in
//!   `tests/fixtures/parser_parity/README.md` (`## Scoreboard at HEAD`) must
//!   byte-match the board generated on the run, so the published numbers can
//!   never go stale.
//!
//! The comparison skeleton and its normalizations are documented in
//! `parse_parity_support/render.rs`; the fixture format and the ratchet rule are
//! documented in `tests/fixtures/parser_parity/README.md`.
//!
//! Run: `cargo test -p clean-parser --test parse_parity -- --nocapture`

use clean_parser::{
    parse_expr, LevelExpr, Projection, QAntiquotContent, SurfaceArg, SurfaceExpr, SurfaceLit,
    UniverseExpr,
};

include!("parse_parity_support/render.rs");

// Currently-divergent probes, each pinned with a Brick-3 tag.
//
// `ALLOWLIST` — key `(family, input)`, the two columns the fixture row carries.
// The test ratchets on this list in BOTH directions:
//   * a divergent probe NOT listed here fails the test (a new silent misparse);
//   * a listed probe that is no longer divergent fails the test (stale entry —
//     its brick landed; delete the line).
//
// Brick 3 ("core operator + notation coverage", audit §5) landed: `$`/`<|`/`|>`/
// `|>.`, `>>`/`*>`/`<*`/`<*>`/`<|>`, `<$>`-precedence/`<&>`/`=<<`/`>=>`/`<=<`,
// GetElem `xs[i]`/`!`/`?`/`'h`, subtype `{x // p}`, collection `{a, b, c}`,
// field abbreviations, `⦃x⦄`/`fun [inst]` binders, `Σ'`/`(x : T) × b`
// Sigma/PSigma, the `∃`-desugar fix, `▸`/`∣`/`•`, and the ˢ isIdRest fix. The
// residual tags are the deliberate divergences documented in
// `parse_parity_support/allowlist.rs`:
//   * `B3-bigop-gate`     — `∑ ∏ ∑' ∏' ⋃ ⋂` are Mathlib-only; clean accepts
//                           them as a documented superset.
//   * `B3-setbuilder-gate`— `{x | p}` is Mathlib-only; clean accepts `setOf`.
//   * `B3-setprod-gate`   — `×ˢ` is Mathlib-only; clean accepts
//                           `SProd.sprod` for the Mathlib compatibility lane.
//   * `B3-existsunique-gate` — `∃!` is Mathlib-only; clean accepts it.
//   * `B3-patternfun-globalname` — `fun (some x) =>` needs global-name
//                           resolution to become a pattern (elaborator-side).
//   * `B3-getelem-postfix-ws` — `xs[1] !` / `xs[1] ?` consumed by clean's
//                           general postfix leniency; Lean rejects.
include!("parse_parity_support/allowlist.rs");

/// The eight probe families, in scoreboard order.
const FAMILIES: [&str; 8] = [
    "bigop",
    "getelem",
    "monadic",
    "brace",
    "binder",
    "lowprec",
    "rewrite",
    "freqsweep",
];

// Per-family MATCH floors — the scoreboard ratchet's second axis. The
// [`ALLOWLIST`] pins the DIVERGENT set exactly, but on its own a probe
// regressing MATCH→LOUD passes silently (LOUD is always an acceptable class).
// These floors pin each family's MATCH count, two-way, mirroring the
// `data/*ratchet*` discipline (regressions fail; improvements fail until the
// pin is advanced, so the pinned number always states the measured truth):
//
//   * MATCH below the floor fails — probe(s) regressed MATCH→LOUD/DIVERGENT;
//   * MATCH above the floor fails — progress landed; bump the floor (the
//     failure message prints the measured table to paste over this one).
//
// Seeded 2026-08-10 from the verified scoreboard (the README block, asserted
// against the measured board by this test on every run).
const MATCH_FLOORS: &[(&str, usize)] = &[
    ("bigop", 5),
    ("getelem", 25),
    ("monadic", 31),
    ("brace", 25),
    ("binder", 38),
    ("lowprec", 24),
    ("rewrite", 13),
    ("freqsweep", 24),
];

/// Expected outcome kind, from the fixture's `expected_kind` column.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ExpectedKind {
    /// Lean parses the input; `lean_tree` holds the skeleton to match.
    Tree,
    /// Lean rejects the input at PARSE time; `lean_tree` holds the error note.
    Error,
}

/// One classification bucket for the scoreboard.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Class {
    /// Clean parses and the tree corresponds to Lean's.
    Match,
    /// Clean rejects (loud gap) — acceptable for unimplemented syntax.
    Loud,
    /// Clean parses a tree that disagrees with Lean (or accepts what Lean
    /// rejects). The failure class.
    Divergent,
}

/// One fixture row.
struct Row {
    family: String,
    input: String,
    kind: ExpectedKind,
    lean_tree: String,
}

fn parse_kind(s: &str, lineno: usize) -> ExpectedKind {
    match s {
        "TREE" => ExpectedKind::Tree,
        "ERROR" => ExpectedKind::Error,
        other => panic!("line {lineno}: bad expected_kind {other:?} (want TREE|ERROR)"),
    }
}

fn fixture_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/parser_parity/ground_truth.tsv")
}

fn readme_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/parser_parity/README.md")
}

/// Look up a family's pinned MATCH floor.
fn match_floor(family: &str) -> usize {
    match MATCH_FLOORS.iter().find(|(f, _)| *f == family) {
        Some((_, floor)) => *floor,
        None => panic!("family {family:?} has no MATCH_FLOORS entry"),
    }
}

/// Render the per-family scoreboard table — the exact text pinned in the
/// fixture README's `## Scoreboard at HEAD` fenced block.
fn scoreboard_block(board: &std::collections::BTreeMap<&str, [usize; 3]>) -> String {
    let mut out = format!(
        "{:10} {:>6} {:>6} {:>10} {:>6}\n",
        "family", "match", "loud", "divergent", "total"
    );
    let mut tot = [0usize; 3];
    for f in FAMILIES {
        let s = board[f];
        for k in 0..3 {
            tot[k] += s[k];
        }
        out.push_str(&format!(
            "{:10} {:>6} {:>6} {:>10} {:>6}\n",
            f,
            s[0],
            s[1],
            s[2],
            s[0] + s[1] + s[2]
        ));
    }
    out.push_str(&format!(
        "{:10} {:>6} {:>6} {:>10} {:>6}\n",
        "TOTAL",
        tot[0],
        tot[1],
        tot[2],
        tot[0] + tot[1] + tot[2]
    ));
    out
}

/// Extract the fenced scoreboard block that follows the `## Scoreboard at
/// HEAD` heading in the fixture README.
fn readme_scoreboard_block(readme: &str) -> String {
    let mut lines = readme.lines();
    lines
        .by_ref()
        .find(|l| l.starts_with("## Scoreboard at HEAD"))
        .expect("README lost its `## Scoreboard at HEAD` heading");
    lines
        .by_ref()
        .find(|l| l.trim() == "```")
        .expect("README scoreboard heading has no fenced block after it");
    let mut block = String::new();
    for line in lines {
        if line.trim() == "```" {
            return block;
        }
        block.push_str(line);
        block.push('\n');
    }
    panic!("README scoreboard fenced block never closes");
}

fn load_rows() -> Vec<Row> {
    let table = std::fs::read_to_string(fixture_path())
        .expect("read tests/fixtures/parser_parity/ground_truth.tsv");
    let mut rows = Vec::new();
    for (idx, line) in table.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        assert!(
            cols.len() == 5,
            "line {}: expected 5 tab-separated columns, got {}: {line:?}",
            idx + 1,
            cols.len()
        );
        rows.push(Row {
            family: cols[0].to_string(),
            input: cols[1].to_string(),
            kind: parse_kind(cols[2], idx + 1),
            lean_tree: cols[3].to_string(),
        });
    }
    rows
}

/// Classify one row against clean-parser's live behavior.
fn classify(row: &Row) -> Class {
    match parse_expr(&row.input) {
        // Loud gap: clean rejects. Always acceptable, whatever Lean does.
        Err(_) => Class::Loud,
        Ok(tree) => match row.kind {
            // Lean rejects at parse time but clean accepted → over-acceptance.
            ExpectedKind::Error => Class::Divergent,
            // Both parse: compare the rendered skeleton to Lean's.
            ExpectedKind::Tree => {
                if render_skeleton(&tree) == row.lean_tree {
                    Class::Match
                } else {
                    Class::Divergent
                }
            }
        },
    }
}

#[test]
fn parse_parity_no_unpinned_silent_divergence() {
    let rows = load_rows();
    assert_eq!(
        rows.len(),
        228,
        "expected 228 probe rows, got {}",
        rows.len()
    );

    // Per-family tallies for the scoreboard.
    let mut board: std::collections::BTreeMap<&str, [usize; 3]> =
        FAMILIES.iter().map(|f| (*f, [0usize; 3])).collect();

    let mut unpinned: Vec<String> = Vec::new();
    // Track which allowlist rows actually fired, to catch stale entries.
    let mut hit: Vec<bool> = vec![false; ALLOWLIST.len()];

    for row in &rows {
        let class = classify(row);
        let slot = board
            .get_mut(row.family.as_str())
            .unwrap_or_else(|| panic!("unknown family {:?}", row.family));
        match class {
            Class::Match => slot[0] += 1,
            Class::Loud => slot[1] += 1,
            Class::Divergent => {
                slot[2] += 1;
                match ALLOWLIST
                    .iter()
                    .position(|(f, i, _)| *f == row.family && *i == row.input)
                {
                    Some(pos) => hit[pos] = true,
                    None => unpinned.push(format!(
                        "{}: `{}` — parsed to `{}` but Lean {}",
                        row.family,
                        row.input,
                        parse_expr(&row.input)
                            .map(|t| render_skeleton(&t))
                            .unwrap_or_default(),
                        match row.kind {
                            ExpectedKind::Tree => format!("expects `{}`", row.lean_tree),
                            ExpectedKind::Error => "rejects it at parse time".to_string(),
                        }
                    )),
                }
            }
        }
    }

    // Scoreboard (prints with --nocapture). The same block is pinned in the
    // fixture README and asserted against below.
    let board_block = scoreboard_block(&board);
    println!("\nparse-parity scoreboard (clean-parser @ HEAD vs Lean v4.30.0-rc2)");
    print!("{board_block}");
    println!(
        "allowlist: {} pinned divergences (each cites its Brick-3 fix)\n",
        ALLOWLIST.len()
    );

    // Stale allowlist entries: pinned as divergent but no longer divergent.
    let stale: Vec<String> = ALLOWLIST
        .iter()
        .zip(&hit)
        .filter(|(_, fired)| !**fired)
        .map(|((f, i, brick), _)| format!("{f}: `{i}` (brick {brick})"))
        .collect();

    assert!(
        unpinned.is_empty(),
        "{} UN-PINNED silent divergence(s) — a new silent misparse or over-acceptance \
         regressed. Fix the parser, or (if intentional) add an allowlist entry citing \
         its brick:\n{}",
        unpinned.len(),
        unpinned.join("\n")
    );
    assert!(
        stale.is_empty(),
        "{} STALE allowlist entry(ies) — these probes are no longer divergent (their \
         brick landed). Remove them from ALLOWLIST to advance the ratchet:\n{}",
        stale.len(),
        stale.join("\n")
    );

    // MATCH-floor ratchet (two-way). The ALLOWLIST pins the divergent set, but
    // without floors a probe regressing MATCH→LOUD passes silently. Every
    // family's MATCH count must equal its pinned floor.
    assert_eq!(
        MATCH_FLOORS.len(),
        FAMILIES.len(),
        "MATCH_FLOORS must pin every family exactly once"
    );
    let mut floor_breaks: Vec<String> = Vec::new();
    let mut measured = String::new();
    for f in FAMILIES {
        let floor = match_floor(f);
        let actual = board[f][0];
        measured.push_str(&format!("    (\"{f}\", {actual}),\n"));
        if actual < floor {
            floor_breaks.push(format!(
                "{f}: MATCH {actual} fell below floor {floor} — probe(s) regressed \
                 MATCH→LOUD/DIVERGENT"
            ));
        } else if actual > floor {
            floor_breaks.push(format!(
                "{f}: MATCH {actual} rose above floor {floor} — progress landed; bump the \
                 floor to advance the ratchet"
            ));
        }
    }
    assert!(
        floor_breaks.is_empty(),
        "{} MATCH-floor break(s):\n{}\nMeasured per-family MATCH counts — MATCH_FLOORS \
         must read exactly (fix regressions in the parser; paste only genuine rises):\n{}",
        floor_breaks.len(),
        floor_breaks.join("\n"),
        measured
    );

    // Scoreboard pinning: the README's `## Scoreboard at HEAD` fenced block
    // must equal the board measured on this run — the published numbers can
    // never go stale. On a legitimate change, paste the block printed above.
    let readme = std::fs::read_to_string(readme_path())
        .expect("read tests/fixtures/parser_parity/README.md");
    let pinned_block = readme_scoreboard_block(&readme);
    assert!(
        pinned_block == board_block,
        "STALE README scoreboard — the `## Scoreboard at HEAD` fenced block in \
         tests/fixtures/parser_parity/README.md does not match the board measured on \
         this run. Replace the fenced block's contents with:\n{board_block}"
    );
}
