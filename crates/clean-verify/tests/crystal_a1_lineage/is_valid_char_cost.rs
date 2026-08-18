// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The SIXTH chain's COST and ATTRIBUTION measurements** — the residue cost
//! law as it was, the law that replaced it, the eleven-minute attribution the
//! measurement corrects, and what the comparison lemmas cost.
//!
//! Every assertion here reads `tests/fixtures/is_valid_char.lineage.json`. None
//! of them is part of the links-2a/2c gate in `is_valid_char.rs`; they are the
//! recorded cost model, pinned as data so it cannot be quoted after it stops
//! being true.
//!
//! Moved out of `is_valid_char.rs` VERBATIM on 2026-08-17 (not one assertion or
//! test name touched) because that file had reached 602 lines and
//! `data/paragon_ratchet.json`'s `files_over_500` is shrink-only. The
//! `meta_tag_shl_evidence.rs` / `get_char_val_trunc_evidence.rs` precedent.

use super::super::*;

/// **The residue cost law, re-measured — and the record it corrects.**
///
/// This is not decoration on the chain: the law on record (`2^W`) says a
/// width-64 body is unreachable, and this body is at width 64. The correction
/// is what makes the chain exist, so it is pinned as data rather than left in
/// prose that no gate reads.
#[test]
fn is_valid_char_residue_cost_is_linear_in_the_dividend_not_the_width() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("is_valid_char.lineage.json"))
        .expect("evidence must be valid JSON");
    let law = &evidence["residue_cost_law_remeasured"];
    let m = &law["measurements_seconds"];
    let get = |k: &str| {
        m[k].as_f64()
            .unwrap_or_else(|| panic!("measurement {k} must be recorded"))
    };

    // Doubling the DIVIDEND at a fixed width doubles the wall clock.
    let (a, b, c) = (get("w64_n7000"), get("w64_n14000"), get("w64_n28000"));
    assert!(
        (b / a - 2.0).abs() < 0.25 && (c / b - 2.0).abs() < 0.25,
        "linear in the dividend: {a} / {b} / {c} for n = 7000 / 14000 / 28000"
    );
    // Moving the WIDTH by a factor of eight at a fixed dividend does not.
    let (w8, w64) = (get("w8_n7000"), get("w64_n7000"));
    assert!(
        (w8 / w64 - 1.0).abs() < 0.25,
        "independent of the width: {w8} at w = 8 vs {w64} at w = 64, same dividend 7000"
    );
    let (w32, w64b) = (get("w32_n55296"), get("w64_n55296"));
    assert!(
        (w32 / w64b - 1.0).abs() < 0.25,
        "and again at a larger dividend: {w32} at w = 32 vs {w64b} at w = 64"
    );
    assert!(
        law["supersedes"]
            .as_str()
            .is_some_and(|s| s.contains("2^W law")),
        "the record this measurement corrects must be named, not quietly replaced"
    );

    // The witness costs are why exactly one concrete `ir_eval` was registered
    // when this chain landed.
    let w = &evidence["witness_costs_seconds"];
    assert!(
        w["decide_c3_at_0"].as_f64().is_some_and(|s| s > 400.0),
        "deciding the 0x110000 residue is the reason no registered witness reaches bb4"
    );
    assert!(
        w["ir_eval_at_65"].as_f64().is_some_and(|s| s < 60.0),
        "…and the reason one concrete run IS registered: its path never materializes it"
    );

    // A superseded law must SAY it is superseded, in the record itself. The
    // failure mode this closes is a stale measurement read as current — which
    // is exactly what the `2^W` row above did for a day.
    assert!(
        law["superseded_by"]
            .as_str()
            .is_some_and(|s| s.contains("residue_cost_law_after_the_folding_lemma")),
        "the law this measurement was superseded BY must be named in the same record"
    );
}

/// **The law that replaced it, and the one thing a theorem cannot state.**
///
/// `ir_nat_ltb_walk_eq` proves the guards equal; no proposition can say the
/// kernel FOLDS a literal instead of walking it, so that half is a clock. Both
/// halves are pinned here as data, against the fixture, for the same reason the
/// row above is: a cost model that lives only in prose gets quoted after it
/// stops being true.
#[test]
fn is_valid_char_residue_cost_is_now_linear_in_the_quotient() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("is_valid_char.lineage.json"))
        .expect("evidence must be valid JSON");
    let law = &evidence["residue_cost_law_after_the_folding_lemma"];
    let m = &law["measurements_seconds"];
    let get = |k: &str| {
        m[k].as_f64()
            .unwrap_or_else(|| panic!("measurement {k} must be recorded"))
    };

    // Doubling the QUOTIENT doubles the wall — that is the loop that remains.
    let (q216, q432, q864) = (
        get("after_w8_n55296_q216"),
        get("after_w8_n110592_q432"),
        get("after_w8_n221184_q864"),
    );
    assert!(
        (q432 / q216 - 2.0).abs() < 0.25 && (q864 / q432 - 2.0).abs() < 0.25,
        "linear in the quotient: {q216} / {q432} / {q864} at q = 216 / 432 / 864"
    );
    // …and the DIVIDEND, which the superseded law was linear in, no longer
    // costs anything: the same 55,296 at a width that makes the quotient zero.
    assert!(
        get("after_w16_n55296_q0") * 10.0 < q216,
        "the dividend is free when the quotient is zero: {} at w=16 vs {q216} at w=8, same n",
        get("after_w16_n55296_q0")
    );

    // The two residues that WERE the wall, before and after, at this chain's
    // own width and at the fifth chain's sentinel.
    assert!(
        get("before_w64_n57343_double") > 20.0 && get("after_w64_n57343_double") < 1.0,
        "this body's left-constant icmp residue: {} -> {}",
        get("before_w64_n57343_double"),
        get("after_w64_n57343_double")
    );
    assert!(
        get("after_w32_n4294967295_double") < 1.0,
        "the u32 sentinel residue was extrapolated at ~9.6 days and never measured; it is now {}",
        get("after_w32_n4294967295_double")
    );

    assert!(
        law["what_it_does_NOT_fix"]
            .as_str()
            .is_some_and(|s| s.contains("ir_nat_eqb")),
        "the walk this lemma does NOT remove must be named in the record, not left to be \
         discovered by the next lane that assumes it was"
    );
}

/// **What the lemma is worth on a whole spec build — and the attribution it
/// corrects.**
///
/// `docs/CRYSTAL_STATUS.md` brackets chains 6 and 7 at "about 11 minutes added
/// to every full `Specification::new()` … concentrated in one place: the
/// width-64 residue of 57,343". Removing that residue ENTIRELY was then
/// measured, before and after, on a pristine worktree and on the same tree plus
/// the lemma: it is worth tens of seconds, not eleven minutes. A bracket
/// between a failing run and a green one is honest as a bracket; what it does
/// not support is the attribution, and a number that large left in prose gets
/// quoted.
#[test]
fn is_valid_char_the_eleven_minute_attribution_is_corrected_by_measurement() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("is_valid_char.lineage.json"))
        .expect("evidence must be valid JSON");
    let s = &evidence["full_specification_new_seconds"];
    let get = |k: &str| {
        s[k].as_f64()
            .unwrap_or_else(|| panic!("measurement {k} must be recorded"))
    };

    let before: Vec<f64> = s["pristine_1ec739677_wall"]
        .as_array()
        .expect("the pristine replicates must be recorded")
        .iter()
        .map(|v| v.as_f64().expect("a wall clock"))
        .collect();
    let after: Vec<f64> = s["with_the_lemma_wall"]
        .as_array()
        .expect("the lemma replicates must be recorded")
        .iter()
        .map(|v| v.as_f64().expect("a wall clock"))
        .collect();
    assert!(
        before.len() >= 4 && after.len() >= 4,
        "a headline figure needs replicates: {} before, {} after",
        before.len(),
        after.len()
    );
    // Non-overlapping is the whole claim. A mean difference inside the spread
    // would be noise on a box that carries other lanes.
    let (worst_after, best_before) = (
        after.iter().cloned().fold(f64::MIN, f64::max),
        before.iter().cloned().fold(f64::MAX, f64::min),
    );
    assert!(
        worst_after < best_before,
        "the distributions must not overlap: slowest after {worst_after} vs fastest before \
         {best_before}"
    );
    // The correction itself: the whole saving is far below the 668 s the
    // bracket attributes to this one residue.
    let saving = get("saving_wall");
    assert!(
        saving > 0.0 && saving < 300.0,
        "if removing the residue really were worth ~11 minutes this would show it: {saving} s"
    );
    assert!(
        (get("pristine_mean_user_cpu") - get("with_the_lemma_mean_user_cpu") - saving).abs() < 20.0,
        "wall and CPU must tell the same story, or the box was doing something else"
    );
    assert!(
        s["corrects"]
            .as_str()
            .is_some_and(|t| t.contains("11 minutes")),
        "the claim this measurement corrects must be quoted in the record"
    );

    // The witnesses that RUN and were still declined are part of the record,
    // not an omission — with the residue free the cost moved to `ir_nat_ltb`'s
    // peel of the ARGUMENT, and this body's arguments are large by
    // construction. A decline with a number attached is a result; a decline
    // without one is a shrug.
    let w = &evidence["witness_costs_seconds_after_the_folding_lemma"];
    for (k, floor) in [
        ("ir_eval_at_55296", 5.0),
        ("ir_eval_at_70000", 5.0),
        ("ir_eval_at_1114112", 100.0),
    ] {
        assert!(
            w[k].as_f64().is_some_and(|v| v > floor),
            "{k} was written, checked and declined; it must carry its measured cost"
        );
    }
    assert!(
        w["declined"]
            .as_str()
            .is_some_and(|t| t.contains("1114112")),
        "…and the record must say which ones they were"
    );
    assert!(
        w["ir_eval_at_65"].as_f64().is_some_and(|v| v < 1.0),
        "the one that IS registered is three orders of magnitude cheaper than it was"
    );
    assert_eq!(
        w["registered"].as_array().map(Vec::len),
        Some(1),
        "this body still registers exactly one concrete ir_eval witness — the lemma changed \
         which cost decides that, not the decision"
    );
}

/// **The comparison lemmas, and the fact that they COST rather than save.**
///
/// The three declarations the row above records as declined are registered now:
/// `ir_nat_ltb_walk_eq` folds the `icmp ult` this body emits three times. The
/// record has to carry two things that are easy to lose. First, the walk
/// baseline re-measured in the SAME window as the folded run — the 19.106 /
/// 31.404 / 210.144 s on file came from a box carrying six concurrent spec
/// builds, and a ratio across two boxes is not a ratio. Second, the sign: a
/// full `Specification::new()` got **slower**, and a lane that reads "folding
/// lemma" and assumes "saving" would quote the wrong direction.
#[test]
fn is_valid_char_the_comparison_lemmas_cost_what_they_cost() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("is_valid_char.lineage.json"))
        .expect("evidence must be valid JSON");
    let w = &evidence["witness_costs_seconds_after_the_comparison_lemmas"];

    // Every one of the three declined declarations is registered, and with the
    // ASCII one that is all four emitted condbr edges executed concretely.
    assert_eq!(
        w["registered"].as_array().map(Vec::len),
        Some(4),
        "all four emitted condbr edges must have a concrete ir_eval witness"
    );
    assert!(
        w["declined"]
            .as_str()
            .is_some_and(|s| s.starts_with("none")),
        "nothing is declined on cost here any more; if that changes, say which and at what price"
    );

    // The ratio, both sides measured on one box in one window.
    for (k, floor) in [
        ("ir_eval_at_55296", 1.0),
        ("ir_eval_at_70000", 1.0),
        ("ir_eval_at_1114112", 10.0),
    ] {
        let walk = w["walk_baseline_same_box_same_window"][k]
            .as_f64()
            .unwrap_or_else(|| panic!("{k}: the walk baseline must be re-measured, not carried"));
        let folded = w["folded"][k]
            .as_f64()
            .unwrap_or_else(|| panic!("{k}: the folded cost must be recorded"));
        assert!(
            walk > floor && folded < 0.1,
            "{k}: {walk} s walking its argument, {folded} s folded"
        );
    }

    // The fifth chain's sentinel path is a KILL, not a ratio: no baseline
    // number exists because the baseline never produced one.
    assert!(
        w["fifth_chain_sentinel_path"]
            .as_str()
            .is_some_and(|s| s.contains("KILLED") && s.contains("2857")),
        "a declaration that did not finish must be recorded as not finishing, with how long it ran"
    );

    // And the sign of the whole-build effect, with its attribution.
    let s = &evidence["full_specification_new_seconds_after_the_comparison_lemmas"];
    let cost = s["cost_wall"]
        .as_f64()
        .expect("the wall cost must be recorded");
    let cpu = s["cost_user_cpu"]
        .as_f64()
        .expect("the CPU cost must be recorded");
    assert!(
        cost > 0.0 && cpu > 0.0,
        "this change made the spec build SLOWER; a positive number here is the point, not a bug"
    );
    assert!(
        (cost - cpu).abs() < 2.0,
        "wall and CPU must tell the same story: {cost} vs {cpu}"
    );

    // Paired replicates, and every pair must agree in sign — that is what makes
    // a 5 s claim survivable on a box whose sequential rounds drift by 20 s.
    let pr = &s["paired_rounds_wall"];
    for r in 1..=3 {
        let get = |side: &str| -> Vec<f64> {
            pr[format!("round{r}_{side}")]
                .as_array()
                .unwrap_or_else(|| panic!("round{r}_{side} must be recorded"))
                .iter()
                .map(|v| v.as_f64().expect("a wall clock"))
                .collect()
        };
        let (b, a) = (get("before"), get("after"));
        assert!(
            b.len() == 2 && a.len() == 2,
            "two replicates per side per round"
        );
        let mean = |v: &[f64]| v.iter().sum::<f64>() / v.len() as f64;
        assert!(
            mean(&a) > mean(&b),
            "round {r} must agree with the others in SIGN: before {:?} after {:?}",
            b,
            a
        );
    }

    // The attribution has to be measured, and the alternative has to be priced.
    assert!(
        s["where_it_goes"]
            .as_str()
            .is_some_and(|t| t.contains("add_eval_ir_contains") && t.contains("ir_nat_eqb")),
        "the one stage that moved, and the head responsible, must both be named"
    );
    assert!(
        s["priced_alternative"]
            .as_str()
            .is_some_and(|t| t.contains("ir_nat_ltb")),
        "the cheaper half of the change must be priced separately, so the trade is visible"
    );
}
