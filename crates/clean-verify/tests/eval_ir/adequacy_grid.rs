// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Gate clause 5 — the adequacy grid covers the full `IRInst` field
//! surface (plan W5, §4(c)).**
//!
//! `data/evalir_adequacy_grid.json` is the per-constructor, per-field account
//! that replaces the trust-ir constructor-NAME parity check's role clean-side:
//! for every field of every constructor, whether the semantics READS it
//! (`relevant-by-design`), provably DROPS it (`irrelevance-proved-await-mint`,
//! naming its `Eq.refl` theorem), or never receives it at all (`audit-pin`,
//! the erased `align` slots) — plus the measured executor divergences
//! (`declared-delta`: six from W1-W4, five from the 2026-08-25 float-residue
//! wave, four from Phase B), whose permanent home the grid is. A delta row
//! states which WAY it runs: `accept-more` (the model continues where the
//! reference faults) is the only direction that could turn a false theorem
//! into a proof, so it is never left implicit, and the fail-closed
//! `reject-more` residues are named in their rows rather than glossed.
//!
//! There is no constructor count typed in this gate's producer any more: the
//! denominator is derived by `evalir_coverage.derive_denominator` from
//! `EMITTED_INSTS` and the `IRInst` inductive, and the grid's own telescope
//! parse is a third source held to it. The two counts this file DOES assert
//! (33 constructors, 33 dispatch arms) are the independent re-derivation the
//! module doc above describes — they are meant to be edited in the same commit
//! as the syntax, and to fail loudly if they are not.
//!
//! The grid is GENERATED, fail-closed, by `scripts/evalir_adequacy_grid.py`.
//! This gate re-derives the field surface INDEPENDENTLY — its own parse of
//! the `IRInst` telescopes and the `ir_exec` dispatch, not the script's — and
//! holds the committed artifact to it, so a new field, a new constructor, or
//! a dispatch arm that starts (or stops) reading a slot fails here even if
//! nobody re-ran the script. Spec-free: every check is over source text and
//! the committed JSON, so this clause runs on the authoring box while the
//! kernel-side registration of the theorems it names stays the big-box
//! obligation (`data/evalir_w5.PENDING.md`).

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

const GRID: &str = include_str!("../../../../data/evalir_adequacy_grid.json");

const STATE_PROVED: &str = "irrelevance-proved-await-mint";
const STATE_RELEVANT: &str = "relevant-by-design";
const STATE_AUDIT: &str = "audit-pin";
const STATE_DELTA: &str = "declared-delta";

fn crate_file(rel: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{} must be readable ({e})", p.display()))
}

fn grid() -> serde_json::Value {
    serde_json::from_str(GRID).expect("data/evalir_adequacy_grid.json must be valid JSON")
}

/// The `IRInst` constructor telescopes, parsed from the registered syntax.
fn irinst_fields() -> Vec<(String, Vec<String>)> {
    let src = crate_file("src/spec/core_spec/eval_ir_syntax.rs");
    let lines: Vec<&str> = src.lines().collect();
    let at = lines
        .iter()
        .position(|l| l.contains("inductive IRInst : Type"))
        .expect("eval_ir_syntax.rs must declare `inductive IRInst : Type`");
    let mut out = Vec::new();
    for line in &lines[at + 1..] {
        let t = line.trim();
        let Some(rest) = t.strip_prefix("| ") else {
            break;
        };
        let (name, tele) = rest
            .split_once(" : ")
            .expect("every IRInst constructor line is `| name : telescope`");
        let mut parts: Vec<String> = tele
            .split('\u{2192}')
            .map(|p| p.trim().to_string())
            .collect();
        let last = parts.pop().expect("a telescope has a result type");
        assert_eq!(
            last.trim_end_matches("\","),
            "IRInst",
            "{name}: telescope must end in IRInst"
        );
        out.push((name.to_string(), parts));
    }
    assert_eq!(
        out.len(),
        33,
        "IRInst includes the appended Release syntax without ARC execution"
    );
    out
}

/// The `ir_exec` dispatch arms: `(ctor, pattern vars, rhs)`.
fn dispatch_arms() -> BTreeMap<String, (Vec<String>, String)> {
    let src = crate_file("src/spec/core_spec/eval_ir_machine.rs");
    let lines: Vec<&str> = src.lines().collect();
    let at = lines
        .iter()
        .position(|l| l.contains("def ir_exec (m : IRModule) (i : IRInst)"))
        .expect("eval_ir_machine.rs must define the ir_exec dispatch");
    let mut out = BTreeMap::new();
    for line in &lines[at + 1..] {
        let t = line.trim();
        let Some(rest) = t.strip_prefix("| IRInst.") else {
            break;
        };
        let rest = rest.strip_suffix("\",").unwrap_or(rest);
        let (lhs, rhs) = rest
            .split_once(" => ")
            .expect("every dispatch arm is `| IRInst.<ctor> <vars> => <rhs>`");
        let mut toks = lhs.split_whitespace().map(str::to_string);
        let ctor = toks.next().expect("an arm names its constructor");
        out.insert(ctor, (toks.collect(), rhs.to_string()));
    }
    assert_eq!(
        out.len(),
        33,
        "the ir_exec dispatch includes both explicit byte-only atomic refusals"
    );
    out
}

fn word_used(rhs: &str, var: &str) -> bool {
    rhs.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .any(|t| t == var)
}

/// The load-bearing check: every field of every constructor has exactly one
/// grid row, in the state the SOURCES dictate — read fields `relevant`,
/// dropped fields `proved` with a theorem whose definition exists.
#[test]
fn eval_ir_adequacy_grid_covers_the_full_irinst_field_surface() {
    let g = grid();
    assert_eq!(
        g["schema"], "evalir-adequacy-grid/v1",
        "grid schema moved; update this gate and the script together"
    );
    let fields = irinst_fields();
    let arms = dispatch_arms();
    let field_index: BTreeMap<&str, &Vec<String>> =
        fields.iter().map(|(n, f)| (n.as_str(), f)).collect();
    assert_eq!(
        field_index.keys().copied().collect::<BTreeSet<_>>(),
        arms.keys().map(String::as_str).collect::<BTreeSet<_>>(),
        "syntax and dispatch disagree on the constructor set"
    );

    let machine = crate_file("src/spec/core_spec/eval_ir_machine.rs");
    let adequacy = crate_file("src/spec/core_spec/eval_ir_adequacy.rs");

    let rows = g["rows"].as_array().expect("grid rows must be an array");
    let mut seen: BTreeSet<(String, usize)> = BTreeSet::new();
    for row in rows.iter().filter(|r| r["kind"] == "field") {
        let ctor = row["constructor"].as_str().expect("field row constructor");
        let index = usize::try_from(row["index"].as_u64().expect("field row index"))
            .expect("index fits usize");
        let var = row["var"].as_str().expect("field row var");
        let ty = row["ty"].as_str().expect("field row ty");
        let state = row["state"].as_str().expect("field row state");
        assert!(
            seen.insert((ctor.to_string(), index)),
            "{ctor}.{index}: duplicate grid row"
        );
        let tys = field_index
            .get(ctor)
            .unwrap_or_else(|| panic!("{ctor}: grid names a constructor IRInst does not declare"));
        assert_eq!(
            tys.get(index).map(String::as_str),
            Some(ty),
            "{ctor}.{index}: grid type disagrees with the declared telescope"
        );
        let (vars, rhs) = &arms[ctor];
        assert_eq!(
            vars.get(index).map(String::as_str),
            Some(var),
            "{ctor}.{index}: grid var disagrees with the dispatch pattern"
        );
        if word_used(rhs, var) {
            assert_eq!(
                state, STATE_RELEVANT,
                "{ctor}.{var}: the dispatch arm READS this field; the only honest state is \
                 relevant-by-design. Regenerate the grid."
            );
        } else {
            assert_eq!(
                state, STATE_PROVED,
                "{ctor}.{var}: the dispatch arm DROPS this field; it needs an irrelevance \
                 theorem row. Regenerate the grid."
            );
            let theorem = row["theorem"]
                .as_str()
                .unwrap_or_else(|| panic!("{ctor}.{var}: a proved row must name its theorem"));
            let src = row["theorem_source"].as_str().expect("theorem_source");
            let text = if src.ends_with("eval_ir_adequacy.rs") {
                &adequacy
            } else if src.ends_with("eval_ir_machine.rs") {
                &machine
            } else {
                panic!("{ctor}.{var}: unexpected theorem source {src}")
            };
            assert!(
                text.contains(&format!("def {theorem} ")),
                "{ctor}.{var}: theorem `{theorem}` is not defined in {src} — a deleted \
                 theorem cannot keep its grid row"
            );
        }
    }
    // Completeness: no field of any constructor is unclassified.
    for (ctor, tys) in &fields {
        for i in 0..tys.len() {
            assert!(
                seen.contains(&(ctor.clone(), i)),
                "{ctor} field {i} has NO grid row — a new field cannot be silently \
                 unclassified; regenerate data/evalir_adequacy_grid.json"
            );
        }
    }
    assert_eq!(
        seen.len(),
        fields.iter().map(|(_, f)| f.len()).sum::<usize>(),
        "grid field-row count must equal the telescope field count"
    );
}

/// The erased-slot and measured-divergence rows are exactly the named ones,
/// and the audit-pin's own lineage test still exists.
#[test]
fn eval_ir_adequacy_grid_erasure_and_delta_rows_are_exactly_the_named_ones() {
    let g = grid();
    let rows = g["rows"].as_array().expect("grid rows must be an array");

    let erased: BTreeSet<(String, String)> = rows
        .iter()
        .filter(|r| r["kind"] == "erased")
        .map(|r| {
            assert_eq!(r["state"], STATE_AUDIT, "erased rows are audit-pin rows");
            (
                r["constructor"].as_str().expect("erased ctor").to_string(),
                r["name"].as_str().expect("erased name").to_string(),
            )
        })
        .collect();
    let want_erased: BTreeSet<(String, String)> = ["load", "store", "alloca"]
        .iter()
        .map(|c| ((*c).to_string(), "align".to_string()))
        .collect();
    assert_eq!(
        erased, want_erased,
        "the erased-slot rows must be exactly the three align slots"
    );

    let audit = crate_file("tests/crystal_a1_lineage/operand_audit.rs");
    assert!(
        audit.contains("fn the_alignment_operand_reaches_the_mint_and_its_exec_erasure_is_pinned"),
        "the audit-pin rows cite a lineage test that no longer exists"
    );

    let deltas: BTreeSet<String> = rows
        .iter()
        .filter(|r| r["kind"] == "delta")
        .map(|r| {
            assert_eq!(
                r["state"], STATE_DELTA,
                "delta rows are declared-delta rows"
            );
            r["id"].as_str().expect("delta id").to_string()
        })
        .collect();
    let want_deltas: BTreeSet<String> = [
        "undef-execution",
        "extractelement-oob-class",
        "null-callee-code",
        "uninit-fault-site",
        "f32-compares",
        "junk-bit-nan",
        // The float-residue wave's five (2026-08-25,
        // data/evalir_float_residue.PENDING.md): the dated whole-operator
        // refusals E2 answers (frem, fsqrt, the eight fp casts) and the two
        // cell-shaped boundaries (rounding-on-NaN, minmax's ambiguous cells).
        "frem-answers-in-e2",
        "fsqrt-answers-in-e2",
        "round-nan-payload",
        "minmax-ambiguous-cells",
        "fp-casts-answer-in-e2",
        // Phase B's four (2026-09-10), and NOT all in one direction — the
        // rows say which way each one runs, because "the model continues where
        // the reference faults" is the only direction that can turn a false
        // theorem into a proof and so is the one that must be declared rather
        // than discovered. ACCEPT-MORE: `copy-type-check-coarse` within a
        // shape class (a width, signedness or aggregate-id disagreement passes
        // the shape check and would fail expect_ty), and
        // `zero-address-is-not-null` (address 0 is an ordinary address here,
        // NullPtr there). NEITHER SIDE FAULTS: `enum-load-shape-directed` is a
        // VALUE divergence — the shape-directed view against the reference's
        // always-decode-the-byte-image. REJECT-MORE, fail-closed:
        // `borrow-one-past-the-end` (the reference's second
        // try_pointer_from_address loop admits base+size; the model has no
        // cell there), and the reject-more half of `copy-type-check-coarse`
        // (the reference's Copy arm never calls reject_partial and transports
        // poison verbatim), each named inside its own row.
        "copy-type-check-coarse",
        "enum-load-shape-directed",
        "zero-address-is-not-null",
        "borrow-one-past-the-end",
        // Crystal E5's three (2026-09-27, decision memo §23). REJECT-MORE, fail-closed:
        // `fat-null-lanes` (a wide value has no null lane). ACCEPT-MORE on ill-typed input only:
        // `ptrmeta-kind-pair` (the metadata type is not checked against the pointer's kind).
        // ACCEPT-MORE and PRE-EXISTING: `icmp-pointer-answers` (the model answers a thin-pointer
        // `icmp` the reference refuses; the wide half agrees).
        "fat-null-lanes",
        "ptrmeta-kind-pair",
        "icmp-pointer-answers",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect();
    assert_eq!(
        deltas, want_deltas,
        "the declared-delta rows must be exactly the eighteen measured findings (six from \
         W1-W4, five from the float-residue wave, four from Phase B, three from crystal E5) — a \
         new measured divergence gets a new row, and none is retired without a dated \
         re-measurement"
    );
}

/// The totals block and the dispatch echo cannot drift from the rows and the
/// registered source they summarize.
#[test]
fn eval_ir_adequacy_grid_totals_and_dispatch_echo_match_the_sources() {
    let g = grid();
    let rows = g["rows"].as_array().expect("grid rows must be an array");
    let count = |pred: &dyn Fn(&serde_json::Value) -> bool| -> u64 {
        u64::try_from(rows.iter().filter(|r| pred(r)).count()).expect("count fits u64")
    };
    let totals = &g["totals"];
    assert_eq!(
        totals["rows"].as_u64(),
        Some(count(&|_| true)),
        "totals.rows"
    );
    assert_eq!(
        totals["field_rows"].as_u64(),
        Some(count(&|r| r["kind"] == "field")),
        "totals.field_rows"
    );
    for (key, state) in [
        (STATE_RELEVANT, STATE_RELEVANT),
        (STATE_PROVED, STATE_PROVED),
        (STATE_AUDIT, STATE_AUDIT),
        (STATE_DELTA, STATE_DELTA),
    ] {
        assert_eq!(
            totals[key].as_u64(),
            Some(count(&|r| r["state"] == state)),
            "totals[{key}]"
        );
    }

    let arms = dispatch_arms();
    let echo = g["dispatch"].as_object().expect("grid dispatch echo");
    assert_eq!(echo.len(), arms.len(), "dispatch echo constructor count");
    for (ctor, (vars, rhs)) in &arms {
        let e = &echo[ctor];
        let evars: Vec<String> = e["vars"]
            .as_array()
            .expect("echo vars")
            .iter()
            .map(|v| v.as_str().expect("echo var").to_string())
            .collect();
        assert_eq!(&evars, vars, "{ctor}: dispatch echo vars drifted");
        assert_eq!(
            e["rhs"].as_str(),
            Some(rhs.as_str()),
            "{ctor}: dispatch echo rhs drifted — regenerate the grid"
        );
    }
}
