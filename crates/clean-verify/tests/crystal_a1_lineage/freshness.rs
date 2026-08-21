// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The chains cannot drift silently any more.**
//!
//! Every other test in this directory compares the registered spec module
//! against a COMMITTED FIXTURE. Not one of them has ever compared the fixture
//! against what `trustc` emits today — and until 2026-08-19 nothing else in the
//! repo did either. The only trustc-invoking scripts are
//! `scripts/trust_ir_build.sh` (whole-crate axis ratchet, touches no fixture)
//! and `scripts/trust_verify_ratchet.sh` (a different mechanism); the
//! perturbation batteries and `crystal_lane_matrix_battery.sh` MUTATE the
//! fixtures to prove the lanes discriminate but never re-derive them;
//! `verify_runner` has no trustc row; no hook does it.
//!
//! So the failure mode was open by construction: if the producer stopped
//! emitting the pinned body, every link-2a gate would keep passing — comparing
//! the spec to a file, while the shipped kernel was built from something else.
//! `crystal_a1_lineage.rs`'s module doc already conceded this for the lineage
//! DIGEST ("RECORDED here, not recomputed"); the emitted IR TEXT had no such
//! statement anywhere.
//!
//! ## What closes it, and what this file's share of that is
//!
//! The comparison itself cannot live in a unit test: re-deriving a body needs
//! the Trust compiler, which this suite does not run. It lives in
//! `scripts/crystal_fixture_freshness.py`, which takes a dump directory,
//! re-extracts every chained body, classifies every differing line, and is RED
//! on a STRUCTURAL change. Its 2026-08-19 run is committed at
//! `data/crystal_chain_revalidation_2026-08-19.json`.
//!
//! This file makes that mechanism NON-OPTIONAL, which is the part a test can do:
//!
//! * every chain fixture must carry a `superseded_at_head` pointer, so a pinned
//!   per-build number can never again sit in the tree with nothing saying when
//!   it was last checked;
//! * the pointer and the record must AGREE on the head digest, so hand-editing
//!   either one is caught;
//! * the record must say no chained body's instructions moved — a `STRUCTURAL`
//!   verdict, or a non-zero `instructions_moved`, fails here;
//! * and **the freshness script must cover exactly the bodies this gate chains**,
//!   so adding an eleventh chain without adding it to the script is a RED rather
//!   than a silent hole. That is the check whose absence let the first ten
//!   accumulate unmeasured.
//!
//! ## The second revalidation, and why a record is not a standing claim
//!
//! A revalidation is a dated measurement against ONE producer. The first was
//! taken at trust `6819d58406`; three producer-adoption waves landed almost
//! immediately after it, so "does it still hold?" was an open question with no
//! answer in the tree. It has one now:
//! `data/crystal_chain_revalidation_2026-08-19_ccf52b40c3.json` re-runs the
//! comparison at trust `ccf52b40c3`, 33 commits later, on byte-identical
//! clean-kernel source — a clean producer-only A/B. **No body drifted**, and
//! every chained body's `lineage` and `def_index` are the values the first
//! record already pinned, so nothing needed superseding.
//!
//! That last part is the load-bearing one, and it is why the second pointer is
//! **additive**. `superseded_at_head` is not rewritten, because it did not go
//! stale — the digests it names are the digests the body still carries.
//! Overwriting a correct record to make it look freshly minted would destroy
//! the evidence that it survived a producer change, which is the only thing
//! that distinguishes a per-build identity that is *stable* from one that has
//! simply not been re-checked.
//!
//! ## One limitation, measured and stated rather than left to be discovered
//!
//! The two files this module reads — `data/…revalidation….json` and
//! `scripts/crystal_fixture_freshness.py` — are OUTSIDE the suite runner's input
//! digest. `verify_runner.py::input_digest` hashes the target's path-dependency
//! closure plus the root `Cargo.toml`/`Cargo.lock`, the toolchain and the argv
//! (`verify_runner.py:1169`); `data/` and `scripts/` are in none of those. So
//! editing either one does **not** mark this target stale, and a GREEN row can
//! outlive a change to the record it rests on. The tests here still catch the
//! edit the moment they are re-run — they compare both sides — but they are not
//! *scheduled* by it. That is the same class of gap as the one this module
//! closes, one level up, and it is named here so the next person reading a green
//! row knows exactly what it is a claim about.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use serde_json::Value;

/// The record the 2026-08-19 revalidation is committed in.
pub(crate) const RECORD: &str = "data/crystal_chain_revalidation_2026-08-19.json";
/// The SECOND revalidation, taken against a producer 33 trust commits newer
/// (`ccf52b40c3` vs `6819d58406`), on byte-identical clean-kernel source.
///
/// It is a separate file rather than an edit to [`RECORD`] because each record
/// is a correct, internally consistent account of ONE build. Merging them would
/// manufacture a record describing neither.
pub(crate) const RECORD_2: &str = "data/crystal_chain_revalidation_2026-08-19_ccf52b40c3.json";
/// The newest current-source revalidation. It is append-only: older records
/// remain the evidence for the exact builds they measured.
pub(crate) const CURRENT_RECORD: &str = "data/crystal_chain_revalidation_2026-08-21_b03937e74.json";
/// The append-only old->new ledger produced by the source-bound fixture
/// rebaseline that makes strict freshness derivably green.
pub(crate) const CURRENT_REBASELINE: &str =
    "data/crystal_fixture_rebaseline_2026-08-21_b03937e74.json";
/// The reviewed load-bearing proof/spec/tag bindings required before the
/// rebaseline tool will move any fixture.
pub(crate) const CURRENT_REBASELINE_BINDINGS: &str =
    "data/crystal_fixture_rebaseline_bindings_2026-08-21_b03937e74.json";
/// The mechanism that produces it.
pub(crate) const SCRIPT: &str = "scripts/crystal_fixture_freshness.py";

/// Fixture stem -> the lineage/evidence file that pins its per-build numbers.
/// `level_is_zero` is the designated target rather than a chain, and its
/// evidence file is named for the A0 probe it came from.
pub(crate) const EVIDENCE: &[(&str, &str)] = &[
    ("has_cubical_layer", "has_cubical_layer.lineage.json"),
    ("level_kind_ord", "level_kind_ord.lineage.json"),
    ("from_source_system", "from_source_system.lineage.json"),
    ("flat_flags_contains", "flat_flags_contains.lineage.json"),
    ("bvar_in_range", "bvar_in_range.lineage.json"),
    ("is_valid_char", "is_valid_char.lineage.json"),
    ("expr_path_step_clone", "expr_path_step_clone.lineage.json"),
    ("float_div", "float_div.lineage.json"),
    ("float_add", "float_add.lineage.json"),
    ("float_sub", "float_sub.lineage.json"),
    ("float_mul", "float_mul.lineage.json"),
    ("get_char_val_trunc", "get_char_val_trunc.lineage.json"),
    ("meta_tag_shl", "meta_tag_shl.lineage.json"),
    ("level_is_zero", "level_is_zero.a0.json"),
    ("simp_priority_value", "simp_priority_value.lineage.json"),
    ("strict_monads", "strict_monads.lineage.json"),
    ("flat_flags_with", "flat_flags_with.lineage.json"),
    ("node_id_index", "node_id_index.lineage.json"),
];

/// Chains whose fixture **IS** the live-dump comparison rather than a dated pin
/// a later lane re-checked.
///
/// The two tests below require every chain to carry `superseded_at_head` and
/// `reconfirmed_at_newer_producer`, each naming a committed revalidation record
/// measured LATER than the fixture's own build. A chain that lands AFTER the
/// most recent revalidation cannot satisfy that and must not be made to look as
/// if it did: there is no later build to point at yet.
///
/// So it points at the freshness report its own fixture was cut from, and
/// `every_head_measured_chain_names_its_own_live_dump_record` gates it on
/// that — an ADDITIONAL requirement, not an exemption. A fixture with neither
/// kind of block still fails, and a row here whose record does not cover it, or
/// disagrees with it, or whose build was not reproduced three times, fails too.
/// The next lane that runs the freshness script records the body in the usual
/// way and the row leaves this list.
pub(crate) const HEAD_MEASURED: &[&str] = &[
    "simp_priority_value",
    // Chains 12-14, the 2026-08-20 float tranche. Same situation, same gate:
    // each fixture names its own live-dump record
    // (data/crystal_fixture_freshness_2026-08-20_lane13.json), which covers
    // every fixture in the tree, and its coverage.json is byte-identical
    // across three clean non-incremental builds.
    "float_add",
    "float_sub",
    "float_mul",
    // Chains 15-17, the 2026-08-20 second tranche — same dump cohort as the
    // floats, same reproduction trio, same record (regenerated from the same
    // dump after its BODIES table grew; the float rows are unchanged by that,
    // which the float gates keep asserting).
    "strict_monads",
    "flat_flags_with",
    "node_id_index",
];

/// The chains the two committed revalidation records actually measured:
/// everything except the head-measured rows, each of which is gated instead by
/// its own live-dump record
/// (`head_measurement::every_head_measured_chain_names_its_own_live_dump_record`).
fn revalidated() -> impl Iterator<Item = &'static (&'static str, &'static str)> {
    EVIDENCE
        .iter()
        .filter(|(stem, _)| !HEAD_MEASURED.contains(stem))
}

pub(crate) fn repo_root() -> PathBuf {
    // crates/clean-verify -> crates -> repo root
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("invariant: CARGO_MANIFEST_DIR is crates/clean-verify inside the repo")
        .to_path_buf()
}

pub(crate) fn read_json(rel: &str) -> Value {
    let p = repo_root().join(rel);
    let text = std::fs::read_to_string(&p).unwrap_or_else(|e| {
        panic!(
            "{} is missing or unreadable ({e}). It is the committed result of the only check \
             that compares a chain fixture to a LIVE trustc dump; without it this gate would \
             pass vacuously, so it fails closed instead.",
            p.display()
        )
    });
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("{} is not valid JSON ({e})", p.display()))
}

fn evidence(name: &str) -> Value {
    serde_json::from_str(&super::fixture(name))
        .unwrap_or_else(|e| panic!("fixture {name} is not valid JSON ({e})"))
}

/// Every chained fixture points at a revalidation record, and the two agree.
///
/// A pointer that disagrees with the record is the shape a hand-edit takes:
/// somebody bumps a digest in one place and not the other. Both sides are read
/// here and compared, so neither can move alone.
#[test]
fn every_chain_fixture_points_at_a_revalidation_and_agrees_with_it() {
    let record = read_json(RECORD);
    let chains = record["chains"]
        .as_object()
        .expect("the revalidation record must carry a `chains` object");

    for (stem, file) in revalidated() {
        let ev = evidence(file);
        let ptr = &ev["superseded_at_head"];
        assert!(
            ptr.is_object(),
            "{file} has no `superseded_at_head` block. Every pinned per-build number in this \
             directory is a dated measurement, not a claim about HEAD; without a pointer saying \
             when it was last checked against a live dump it is indistinguishable from a \
             current one. Re-derive with {SCRIPT} and record the result."
        );
        assert_eq!(
            ptr["record"].as_str(),
            Some(RECORD),
            "{file}: the pointer must name the committed record"
        );

        let entry = chains.get(*stem).unwrap_or_else(|| {
            panic!("{RECORD} carries no entry for {stem}, but {file} points at it")
        });
        assert_eq!(
            ptr["head_lineage"].as_str(),
            entry["lineage"]["at_head"].as_str(),
            "{file}: the head lineage in the fixture pointer and in {RECORD} disagree. One of \
             them was hand-edited; a digest names WHICH artifact a theorem is about, so two \
             answers is worse than a stale one."
        );
        assert_eq!(
            ptr["head_def_index"].as_u64(),
            entry["lineage"]["def_index_at_head"].as_u64(),
            "{file}: def_index disagrees with {RECORD}"
        );
        assert!(
            ptr["head_lineage"]
                .as_str()
                .is_some_and(|s| s.starts_with("sha256:") && s.len() > "sha256:".len()),
            "{file}: the head lineage must be a non-empty sha256 identifier"
        );
        assert_eq!(
            ptr["how_to_re_derive"].as_str().map(|s| s.contains(SCRIPT)),
            Some(true),
            "{file}: the pointer must name the command that re-derives it, or the next reader \
             has a stale number and no way to refresh it"
        );
    }
}

/// The record says no chained body's instructions moved — and says it per body.
///
/// This is the claim the whole revalidation exists to make. If a future run
/// records a `STRUCTURAL` verdict and somebody commits it without acting, this
/// fails: a structural change means the spec module and its refinement theorem
/// may no longer describe the emitted program, which is a re-DERIVATION and not
/// a fixture refresh.
#[test]
fn the_revalidation_records_no_structural_drift() {
    let record = read_json(RECORD);
    let chains = record["chains"]
        .as_object()
        .expect("the revalidation record must carry a `chains` object");
    assert_eq!(
        chains.len(),
        revalidated().count(),
        "the record must cover every chained body that existed when it was taken, and nothing \
         else. A record is a DATED measurement: it cannot cover a chain that landed after it — \
         HEAD_MEASURED names exactly those, each covered by its own live-dump record."
    );

    for (stem, _) in revalidated() {
        let body = &chains[*stem]["emitted_body_vs_committed_fixture"];
        let verdict = body["verdict"].as_str().unwrap_or("<missing>");
        assert!(
            verdict == "IDENTICAL" || verdict == "NUMBERING-ONLY",
            "{stem}: the last revalidation recorded `{verdict}`. Only IDENTICAL and \
             NUMBERING-ONLY are survivable here. A STRUCTURAL verdict means the producer no \
             longer emits the body this chain's spec module transcribes — re-derive the module \
             and its refinement theorem; do NOT refresh the fixture and move on."
        );
        assert_eq!(
            body["instructions_moved"].as_u64(),
            Some(0),
            "{stem}: instructions moved. See above — this is not a fixture refresh."
        );
        // Every class the record admits must be one the script classifies, or
        // the two have drifted apart and the verdict means nothing.
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
                "{stem}: unknown drift class `{c}` — it is not one {SCRIPT} classifies"
            );
        }
    }
}

/// **The check whose absence let ten chains accumulate unmeasured.**
///
/// `scripts/crystal_fixture_freshness.py` carries the list of bodies it
/// compares. If that list and the set of bodies this gate chains ever diverge,
/// a chain exists that no live-dump comparison covers — exactly the hole the
/// script was written to close, reopened one body at a time. So the two are
/// compared, by reading the script's own source rather than by restating it.
#[test]
fn the_freshness_script_covers_exactly_the_chained_bodies() {
    let p = repo_root().join(SCRIPT);
    let src = std::fs::read_to_string(&p).unwrap_or_else(|e| {
        panic!(
            "{} is missing or unreadable ({e}). It is the ONLY thing in this repo that compares \
             a chain fixture against a live trustc dump.",
            p.display()
        )
    });
    let table = src
        .split_once("BODIES: dict[str, str] = {")
        .map(|(_, rest)| rest.split_once("\n}").map_or(rest, |(t, _)| t))
        .unwrap_or_else(|| panic!("{} has no BODIES table", p.display()));

    let covered: BTreeSet<&str> = table
        .lines()
        .filter_map(|l| l.trim().strip_prefix('"'))
        .filter_map(|l| l.split_once('"'))
        .map(|(k, _)| k)
        .collect();
    let chained: BTreeSet<&str> = EVIDENCE.iter().map(|(stem, _)| *stem).collect();

    assert_eq!(
        covered, chained,
        "{SCRIPT}'s BODIES table and the chained bodies disagree. A body this gate chains but \
         the script does not compare has NO live-dump check at all — which is the state all ten \
         chains were in until 2026-08-19."
    );
}

/// The live-dump driver must really evict the subject before it claims a fresh
/// measurement.  A Trust-pinned checkout passes a `-Z` option through Cargo's
/// target config, so even `cargo clean` has to query the measured Trust
/// compiler.  The old best-effort cleanup used the host stable compiler,
/// discarded its error with `|| true`, and could leave a reused clean-kernel
/// artifact untouched.  The later missing-coverage check failed closed, but
/// only after the driver had failed to uphold its advertised precondition.
#[test]
fn the_live_dump_driver_cleans_with_the_measured_compiler_and_fails_closed() {
    let rel = "scripts/trust_ir_build.sh";
    let path = repo_root().join(rel);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{} is missing or unreadable ({e})", path.display()));
    assert!(
        source.contains("if ! RUSTC=\"$TRUSTC_BIN\" CARGO_TARGET_DIR=\"$TDIR\""),
        "{rel} must make Cargo's cleanup query the same sealed compiler as the measured build"
    );
    assert!(
        source.contains("cargo clean --locked --release -p clean-kernel"),
        "{rel} must evict the measured clean-kernel package before rebuilding it"
    );
    assert!(
        source.contains(
            "fail \"could not remove the clean-kernel subject artifacts with the measured compiler\""
        ),
        "{rel} must fail closed when subject eviction fails"
    );
    assert!(
        !source.contains("cargo clean --locked --release -p clean-kernel >/dev/null 2>&1 || true"),
        "{rel} silently ignores a failed subject eviction"
    );
}

/// **A revalidation is a dated measurement, so "does it still hold?" needs an
/// answer in the tree — not a re-read of the same file.**
///
/// The first revalidation pinned each chained body's `lineage` and `def_index`
/// at trust `6819d58406`. Those are per-BUILD identities: nothing in that record
/// establishes they survive the next producer wave, and three landed almost
/// immediately (vtable slices 13/14/15, producer adoption). So every fixture
/// carries a second, ADDITIVE pointer, and this test holds the two together.
///
/// It is additive on purpose. `superseded_at_head` is not rewritten, because it
/// did not go stale: the digests it names are the digests the body still
/// carries. Overwriting a correct record to make it look freshly minted would
/// destroy the very evidence that it survived.
#[test]
fn every_chain_fixture_is_reconfirmed_against_the_newer_producer() {
    let record = read_json(RECORD_2);
    let chains = record["chains"]
        .as_object()
        .expect("the second revalidation record must carry a `chains` object");
    assert_eq!(
        record["supersedes"]["record"].as_str(),
        Some(RECORD),
        "{RECORD_2} must name the record it extends, or the two are unrelated files that \
         happen to share a shape"
    );
    assert!(
        repo_root().join(RECORD).is_file(),
        "{RECORD_2} names {RECORD} as the record it extends, but that file is gone. A \
         superseding record does not license deleting its predecessor: each one is the only \
         account of its own build."
    );

    for (stem, file) in revalidated() {
        let ev = evidence(file);
        let ptr = &ev["reconfirmed_at_newer_producer"];
        assert!(
            ptr.is_object(),
            "{file} has no `reconfirmed_at_newer_producer` block. Its `superseded_at_head` \
             numbers were measured against ONE producer; without a later check they are a \
             claim about that build alone. Re-derive with {SCRIPT} and record the result."
        );
        assert_eq!(
            ptr["record"].as_str(),
            Some(RECORD_2),
            "{file}: the reconfirmation must name the committed record"
        );

        let entry = chains
            .get(*stem)
            .unwrap_or_else(|| panic!("{RECORD_2} carries no entry for {stem}"));

        // The whole point of the block: the digest did not move, and both sides
        // must say so identically.
        assert_eq!(
            ptr["head_lineage_still"].as_str(),
            entry["lineage"]["at_head"].as_str(),
            "{file}: the reconfirmed lineage and {RECORD_2} disagree — one was hand-edited"
        );
        assert_eq!(
            ptr["head_lineage_still"].as_str(),
            ev["superseded_at_head"]["head_lineage"].as_str(),
            "{file}: the reconfirmation reports a DIFFERENT lineage than `superseded_at_head`, \
             but records `head_lineage_moved_since_prior_revalidation` as false. Either the \
             digest moved — in which case the pin needs superseding, with the old value kept as \
             a correct record of a different build — or one of the two was hand-edited."
        );
        assert_eq!(
            ptr["head_def_index_still"].as_u64(),
            entry["lineage"]["def_index_at_head"].as_u64(),
            "{file}: def_index disagrees with {RECORD_2}"
        );
        assert_eq!(
            ptr["head_lineage_moved_since_prior_revalidation"].as_bool(),
            Some(false),
            "{file}: this block asserts the lineage was RECONFIRMED. If it moved, it is a \
             supersession and not a reconfirmation — record it as one."
        );
        assert_eq!(
            entry["lineage"]["re_pin_required"].as_bool(),
            Some(false),
            "{stem}: {RECORD_2} says a re-pin IS required, but the fixture carries a plain \
             reconfirmation. Re-pin it, keeping the old value as a superseded record."
        );
    }
}

/// The second revalidation records no structural drift either — per body.
///
/// Kept separate from the first record's check so a future third record cannot
/// be added without someone deciding which one this gate reads.
#[test]
fn the_second_revalidation_records_no_structural_drift() {
    let record = read_json(RECORD_2);
    let chains = record["chains"]
        .as_object()
        .expect("the second revalidation record must carry a `chains` object");
    assert_eq!(
        chains.len(),
        revalidated().count(),
        "the second record must cover every chained body and nothing else"
    );

    for (stem, _) in revalidated() {
        let body = &chains[*stem]["emitted_body_vs_committed_fixture"];
        let verdict = body["verdict"].as_str().unwrap_or("<missing>");
        assert!(
            verdict == "IDENTICAL" || verdict == "NUMBERING-ONLY",
            "{stem}: the newer-producer revalidation recorded `{verdict}`. A STRUCTURAL verdict \
             means the producer no longer emits the body this chain's spec module transcribes — \
             re-derive the module and its refinement theorem; do NOT refresh the fixture."
        );
        assert_eq!(
            body["instructions_moved"].as_u64(),
            Some(0),
            "{stem}: instructions moved under the newer producer. Not a fixture refresh."
        );
        // `gep` is the shape wave-DZ introduced, and the reason this whole
        // re-measurement exists. A body that gains one has gained an
        // instruction the spec module does not transcribe.
        assert_eq!(
            body["gep_in_emitted_body"].as_u64(),
            body["gep_in_fixture"].as_u64(),
            "{stem}: the emitted body and its fixture disagree on how many `gep` sites they \
             carry. That is exactly the wave-DZ shape this revalidation was run to detect."
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
                "{stem}: unknown drift class `{c}` — it is not one {SCRIPT} classifies"
            );
        }
    }
}

#[path = "freshness_enum_tag_stage2.rs"]
mod enum_tag_stage2;
#[path = "freshness_head.rs"]
mod head_measurement;
