// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scratch elaboration for the blanket-`hiota` refutation, before it is
//! registered.
//!
//! The ladder's iteration recipe, applied outside the ladder: append the
//! candidates to an ALREADY-BUILT spec so a failure names the constant instead
//! of aborting a nineteen-minute spec build at its first bad line — and so that
//! one run reports EVERY failure rather than the first.

use super::*;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};

/// Microseconds: every candidate must at least parse.
#[test]
fn blanket_hiota_refutation_candidates_parse() {
    for (name, src) in blanket_hiota_refutation_candidates() {
        parse_check(src).unwrap_or_else(|e| panic!("candidate {name} does not parse: {e}"));
    }
    parse_check(WHB_REFUTATION).expect("the refutation must parse");
    parse_check(WHB_PAR_REFUTATION).expect("the par refutation must parse");
}

/// The par twin is an IMPLICATION, not a second construction — pinned, because
/// the difference is the whole finding.
///
/// If an edit ever rebuilt it from the `whb_*` ingredients directly, it would
/// stop recording that the blanket par premise is the STRONGER hypothesis and
/// that refuting the DefEq one already refuted it. It must go through
/// `wh_blanket_hiota_defeq_is_false` and through `cd_star_join_to_def_eq`, and
/// through nothing else.
#[test]
fn the_par_refutation_is_an_implication_not_a_second_construction() {
    assert!(
        WHB_PAR_REFUTATION.contains("wh_blanket_hiota_defeq_is_false"),
        "the par refutation no longer goes through the DefEq one"
    );
    assert!(
        WHB_PAR_REFUTATION.contains("cd_star_join_to_def_eq"),
        "the par refutation no longer goes through the unconditional par-to-DefEq embedding"
    );
    for absent in [
        "whb_g",
        "whb_x",
        "whb_wfalse",
        "whb_wtrue",
        "whb_fires",
        "sort_injectivity",
    ] {
        assert!(
            !WHB_PAR_REFUTATION.contains(absent),
            "the par refutation rebuilds {absent} directly — it is a second construction, not the \
             implication this module says it is"
        );
    }
}

/// THE ITERATION TOOL — and, once it is green, the measurement.
///
/// Two steps here are `Eq.refl` COMPUTATIONS over the reflected environment and
/// neither has been executed: `whb_fires_*` (the six `opt_bind` levels of
/// `iota_reduct_whc` at a concrete `Bool.rec` spine) and `whb_*_is_sort*` (three
/// β steps through `def_eq_fuel_sound` at a GUESSED fuel of 8). Everything else
/// is application of constants this crate already proves. A failure in the fuel
/// legs is a wrong literal, not a wrong argument — raise it; a failure in
/// `whb_fires_*` means the chain's guards do not read the way
/// `iota_reduct_whc_src` says, which would be the real finding.
///
/// `#[ignore]` is forbidden org-wide, so this is a live test. It is written to
/// report every failure at once precisely because it is expected to need
/// iteration.
#[test]
fn blanket_hiota_refutation_elaborates() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        // Registered as of 2026-09-17, so the spec already carries it; this
        // stays as the iteration tool for any future edit to the term, which
        // is why it re-registers into a FRESH spec rather than asserting
        // presence. Nothing to re-add once the stage is live.
        if spec
            .definitions()
            .contains_key("wh_blanket_hiota_defeq_is_false")
            || spec
                .env()
                .get_const(&clean_kernel::Name::from_string(
                    "wh_blanket_hiota_defeq_is_false",
                ))
                .is_some()
        {
            return;
        }
        let mut failures: Vec<String> = Vec::new();
        for (name, src) in blanket_hiota_refutation_candidates() {
            if let Err(e) = spec.add_recursive_def(src, "blanket-hiota refutation scratch") {
                failures.push(format!("{name}: {e}"));
            }
        }
        if let Err(e) = spec.add_recursive_def(WHB_REFUTATION, "blanket-hiota refutation scratch") {
            failures.push(format!("wh_blanket_hiota_defeq_is_false: {e}"));
        }
        assert!(
            failures.is_empty(),
            "blanket-hiota refutation does not elaborate ({} failures):\n{}",
            failures.len(),
            failures.join("\n")
        );
    });
}

/// The refutation must bind the BLANKET premise, not the repaired one.
///
/// The whole point is that `def_eq_fuel_wh_sound`'s hypothesis is false while
/// `def_eq_fuel_wh_sound_hw`'s is satisfied at the development's only instance.
/// If an edit ever slipped the pre-pass soundness hypothesis into this binder,
/// the object would stop refuting anything and would still read as a
/// refutation — so pin the difference: the binder is `w`, then `g x r`, with
/// nothing between `w` and `g`.
#[test]
fn the_refutation_binds_the_blanket_premise_not_the_repaired_one() {
    assert!(
        WHB_REFUTATION
            .contains("(w : KExpr -> OptionType KExpr) (g : KExpr) (x : KExpr) (r : KExpr)"),
        "the refutation's premise is no longer the blanket one"
    );
    assert!(
        !WHB_REFUTATION.contains("(forall (e : KExpr) (rr : KExpr)"),
        "the refutation now binds a CONSTRAINED pre-pass — it refutes the repaired premise, \
         which is satisfied, so it would be refuting nothing"
    );
    // The two lying pre-passes must really be different, or the two firings
    // cannot disagree and the whole construction collapses to one DefEq.
    let candidates = blanket_hiota_refutation_candidates();
    let wfalse = candidates
        .iter()
        .find(|(n, _)| *n == "whb_wfalse")
        .expect("the false pre-pass");
    let wtrue = candidates
        .iter()
        .find(|(n, _)| *n == "whb_wtrue")
        .expect("the true pre-pass");
    assert_ne!(
        wfalse.1.replace("whb_wfalse", "W"),
        wtrue.1.replace("whb_wtrue", "W"),
        "the two pre-passes are the same function — they fire the same rule and prove nothing"
    );
}

/// The prose this refutation converts into a term must still be the prose it
/// converts.
///
/// It is no longer ONLY prose — `wh_blanket_hiota_defeq_is_false` is registered
/// — but the sentence has to stay, because the refutation's whole claim to be
/// interesting is that this module had been asserting it for months beside a
/// proof and nothing checked it. If the sentence goes, the object loses its
/// subject.
#[test]
fn the_refuted_prose_claim_is_still_the_modules_own() {
    let src = include_str!("wh_hiota_repair.rs");
    let doc = crate::test_utils::flatten_module_doc(src);
    assert!(
        doc.contains("The premise is false, and everything carrying it is vacuous"),
        "this module no longer makes the claim the refutation converts into a term"
    );
    assert!(
        src.contains("def wh_blanket_hiota_defeq_is_false"),
        "the refutation left this module — the claim above is prose again"
    );
}

/// MEASURED, then PINNED: `def_eq_fuel_wh the_red_env n d d` at the divergence
/// witness is `false` for n = 0..5 and `true` for n = 6, 7, 8.
///
/// ## Why this exists
///
/// A scoping pass proposed refuting ALGORITHM-side fuel monotonicity at the
/// two-way faithful loop by the same witness the LOOP refutation uses
/// (`kcre_witness_nat_zero_redex`, where `whnf_fuel_red_wh` returns the term at
/// budget 1 and `none` at budget 2), predicting
/// `def_eq_fuel_wh 2 d d = true` and `… 3 d d = false`. It was explicitly
/// flagged as DESIGNED, not measured. Measured, it is wrong twice over: n = 2
/// is already `false`, and the `true` at n = 6 SURVIVES to 7 and 8.
///
/// ## The reason, which is structural rather than incidental
///
/// `def_eq_fuel_wh (succ k)` whnfs both legs at `k` and then runs
/// `def_eq_struct` with the comparator AT `k`. So:
///
/// * the loop's spurious `some` needs SMALL `k` — it happens at budget 1 and is
///   gone by 2 (`wh_redex_false_stuck`, `wh_redex_collapses`);
/// * the structural layer succeeding needs LARGE `k` — at n = 2 the
///   sub-comparisons run at fuel 1, whose own legs whnf at fuel 0 and yield
///   `none`.
///
/// Those pull in OPPOSITE directions: the fuel at which the loop lies is
/// exactly the fuel at which the structural layer cannot yet succeed. **So the
/// loop-level refutation does not lift to the algorithm level**, and
/// `whnf_fuel_red_wh_monotone_is_false` must not be cited as though it did.
///
/// ## What is therefore OPEN, stated precisely
///
/// Algorithm-side monotonicity at loop (ii) — `def_eq_fuel_wh_succ_mono` — is
/// **neither proved nor refuted**. This witness does not refute it. That is
/// weaker than "blocked by falsity" and stronger than "unproved", and it is the
/// honest middle. It does not affect the transfer route to completeness, which
/// never raises a fuel.
///
/// ## Why a pin and not a note
///
/// The row is the evidence. If the reduction environment or the fuel discipline
/// changes, this fails and whoever changed it learns that a documented
/// measurement moved — which is the only way a measurement stays true.
#[test]
fn def_eq_fuel_wh_at_the_divergence_witness_is_monotone_here() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let d = "kcre_witness_nat_zero_redex";
        let expected = [
            "false", "false", "false", "false", "false", "false", "true", "true", "true",
        ];
        let mut nat = "Nat.zero".to_string();
        for (n, want) in expected.iter().enumerate() {
            let mut accepted: Vec<&str> = Vec::new();
            for val in ["Bool.true", "Bool.false"] {
                let name = format!("wh_mono_pin_{n}_{}", val.replace("Bool.", ""));
                let src = format!(
                    "def {name} : Eq Bool (def_eq_fuel_wh the_red_env {nat} {d} {d}) {val} \
                     := Eq.refl Bool {val}"
                );
                if spec
                    .add_recursive_def(&src, "fuel-monotonicity pin")
                    .is_ok()
                {
                    accepted.push(val);
                }
            }
            assert_eq!(
                accepted.len(),
                1,
                "at n={n} the kernel accepted {accepted:?} — exactly one of Bool.true / \
                 Bool.false must hold, or it would be proving Bool.true = Bool.false"
            );
            assert_eq!(
                accepted[0],
                &format!("Bool.{want}"),
                "def_eq_fuel_wh at n={n} measured {accepted:?}, pinned Bool.{want}. The reduction \
                 environment or the fuel discipline moved; re-derive the row before editing this \
                 test, and re-read what it says about the loop-level refutation not lifting."
            );
            nat = format!("(Nat.succ {nat})");
        }
    });
}
