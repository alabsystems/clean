// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Premise-search step-budget regression + calibration anchors.**
//!
//! Guards the deterministic step budget that ends the v3.2-grand incident — a
//! single Extended_Real line (`anon.s7298174`) spun the `prove_from_premises`
//! premise-instantiation search (`prove_goal`/`drive_premise`/`beta_normal`) at
//! 98.6 % CPU for 5+ hours, killing a 39-hour run whose snapshots only saved at
//! END. The search's nominal `fuel` does not bound a pathological premise shape;
//! [`super::PREMISE_STEP_BUDGET_DEFAULT`] does, deterministically (never
//! wall-clock).
//!
//! Fixtures are VERBATIM corpus JSON lines extracted by serial via the
//! `main_v32.jsonl.idx` seek-read (read-only), driven with an EMPTY closure —
//! exactly the reject_decode_tests pattern (a handful of parsed decls, never a
//! verify group, never the machine-wide verify lock). An empty closure is a
//! faithful reproduction: the recorded proof fails on its first unresolved `PThm`
//! dependency, reaching the *same* statement-level `prove_from_premises` fallback
//! whose premise-application walk is what explodes (the walk is a pure function
//! of the statement's premises/conclusion, closure-independent). Confirmed: under
//! `ISA_PREMISE_STEP_BUDGET=0` (opt-out) s7298174 never completes; under the
//! default budget it rejects in seconds.
//!
//! The three `KernelVerified` **success anchors** are the quantifier trio the arm
//! was built for — `allE` (s73810), `exE` (s75126), `bspec` (s279070); see
//! `docs/analysis/zproof-quantifier-trio.md`. Their measured peak step counts are
//! single digits (9 / 7 / 6), so the default is > 2000× the max observed — far
//! beyond the ≥ 100× calibration floor — and never cuts a legitimate KV line.

use std::collections::BTreeMap;

use super::{
    bump_premise_steps, premise_budget_exhausted, premise_step_budget, premise_steps_peak,
    reset_premise_steps, PREMISE_STEP_BUDGET_DEFAULT,
};
use crate::hol::isabelle_pure::parse_proven_theorem;
use crate::hol::isabelle_pure_verify::import_proven_theorems;
use crate::hol::isabelle_verify_config::VerifyConfig;
use crate::shard::ShardWriter;

const ALL_E: &str =
    include_str!("../../../tests/fixtures/isabelle/premise_budget/exemplar_s73810_allE.jsonl");
const EX_E: &str =
    include_str!("../../../tests/fixtures/isabelle/premise_budget/exemplar_s75126_exE.jsonl");
const BSPEC: &str =
    include_str!("../../../tests/fixtures/isabelle/premise_budget/exemplar_s279070_bspec.jsonl");
const STUCK: &str =
    include_str!("../../../tests/fixtures/isabelle/premise_budget/stuck_s7298174.jsonl");

/// Verify a single verbatim corpus line through the batch importer with an EMPTY
/// closure, under the DEFAULT premise budget (env explicitly cleared so the test
/// is hermetic — clearing only ever restores the compiled default, so it never
/// perturbs a concurrent reader). Returns `(kernel_verified, rejected,
/// rejection_reasons, premise_steps_peak)`.
fn verify_line(line: &str) -> (usize, usize, BTreeMap<String, usize>, u64) {
    crate::process_env::with_serialized_env_vars_removed(&["ISA_PREMISE_STEP_BUDGET"], || {
        let thm = parse_proven_theorem(line.trim()).expect("fixture line parses");
        let mut w = ShardWriter::new();
        let r = import_proven_theorems(std::slice::from_ref(&thm), &mut w);
        (
            r.kernel_verified,
            r.rejected,
            r.rejection_reasons,
            premise_steps_peak(),
        )
    })
}

/// **The incident regression.** Under the default budget the stuck Extended_Real
/// line rejects fast under the distinct `premise-budget-cut` bucket instead of
/// spinning (it never `KernelVerifies` — the recorded proof genuinely failed).
/// The wall-clock bound is a coarse spin tripwire only: the deterministic budget
/// caps the search at ~20 k steps, so a real cut is seconds; the historical spin
/// was hours.
#[test]
fn stuck_line_rejects_via_premise_budget_cut_not_spin() {
    let start = std::time::Instant::now();
    let (kv, rejected, reasons, peak) = verify_line(STUCK);
    let elapsed = start.elapsed();

    assert_eq!(
        kv, 0,
        "the stuck line must NOT KernelVerify (its recorded proof failed)"
    );
    assert_eq!(rejected, 1, "the stuck line is exactly one reject");
    assert_eq!(
        reasons.get("premise-budget-cut").copied(),
        Some(1),
        "the reject must bucket under the distinct 'premise-budget-cut' reason, got {reasons:?}"
    );
    // The search hit its per-attempt budget (bounded overshoot from the unwinding
    // loop is a handful of steps).
    assert!(
        peak >= PREMISE_STEP_BUDGET_DEFAULT,
        "the premise search must have reached the budget ({peak} >= {PREMISE_STEP_BUDGET_DEFAULT})"
    );
    // Spin tripwire: a bounded cut is seconds; the incident was 5+ hours. Generous
    // so it never flakes under load, tight enough to catch a regression to the
    // unbounded search.
    assert!(
        elapsed < std::time::Duration::from_secs(180),
        "the bounded cut must complete quickly, took {elapsed:?} (regression to the spin?)"
    );
}

/// **Calibration anchors.** The quantifier trio (`allE`/`exE`/`bspec`) — the KV
/// successes this arm exists for — still `KernelVerify` under the default budget,
/// and their measured peak step counts stay far below it: the default is ≥ 100×
/// the max observed success (the calibration floor), so no legitimate KV line is
/// ever cut.
#[test]
fn quantifier_trio_kv_under_default_budget_with_calibration_margin() {
    let mut max_peak = 0u64;
    for (tag, src) in [("allE", ALL_E), ("exE", EX_E), ("bspec", BSPEC)] {
        let (kv, rejected, reasons, peak) = verify_line(src);
        assert_eq!(
            kv, 1,
            "{tag} must KernelVerify via the premise-instantiation arm under the default budget \
             (rejected={rejected} reasons={reasons:?})"
        );
        assert!(
            peak < PREMISE_STEP_BUDGET_DEFAULT,
            "{tag} success used {peak} steps — must stay under the budget \
             {PREMISE_STEP_BUDGET_DEFAULT}"
        );
        max_peak = max_peak.max(peak);
    }
    assert!(
        max_peak > 0,
        "the arm must actually run the premise search on the exemplars (peak > 0)"
    );
    // The ≥ 100× calibration floor: the default has ample headroom over the worst
    // observed success, so unseen but legitimate deeper chains are safe too.
    assert!(
        PREMISE_STEP_BUDGET_DEFAULT >= 100 * max_peak,
        "default budget {PREMISE_STEP_BUDGET_DEFAULT} must be >= 100x the max observed \
         success ({max_peak} steps)"
    );
}

/// The **mechanism** unit test (no env, no import — deterministic and race-free):
/// with a config installed, [`bump_premise_steps`] returns `true` up to the
/// budget, then latches poison and returns `false`; [`premise_budget_exhausted`]
/// then reports the budget; [`reset_premise_steps`] clears it; and an unbounded
/// (`None`) budget never cuts.
#[test]
fn premise_step_budget_mechanism_cuts_and_resets() {
    let cfg = VerifyConfig {
        premise_step_budget: Some(3),
        ..VerifyConfig::default()
    };
    let _g = cfg.install();
    reset_premise_steps();
    assert_eq!(premise_step_budget(), Some(3));
    assert!(premise_budget_exhausted().is_none(), "fresh: not exhausted");
    // Steps 1..=3 are within budget (n > budget only once the 4th passes it).
    assert!(bump_premise_steps(), "step 1 within budget");
    assert!(bump_premise_steps(), "step 2 within budget");
    assert!(bump_premise_steps(), "step 3 within budget");
    assert!(!bump_premise_steps(), "step 4 exceeds budget -> cut");
    assert_eq!(
        premise_budget_exhausted(),
        Some(3),
        "poison latched with the budget value"
    );
    // Reset clears poison + counter for the next attempt.
    reset_premise_steps();
    assert!(premise_budget_exhausted().is_none(), "reset clears poison");
    assert!(bump_premise_steps(), "reset restarts the counter");

    // Unbounded budget (the `ISA_PREMISE_STEP_BUDGET=0` opt-out) never cuts.
    let cfg0 = VerifyConfig {
        premise_step_budget: None,
        ..VerifyConfig::default()
    };
    let _g0 = cfg0.install();
    reset_premise_steps();
    for _ in 0..100_000 {
        assert!(bump_premise_steps(), "unbounded budget never cuts");
    }
    assert!(premise_budget_exhausted().is_none());
}
