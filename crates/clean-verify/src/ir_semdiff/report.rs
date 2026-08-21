// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rows, verdicts, and the per-chain measured summary.
//!
//! Three rules are enforced structurally here rather than by convention:
//!
//! * **A single executor is never an agreement.** A row that only one side
//!   could reach is [`Agreement::Insufficient`] and is counted separately; it
//!   is never folded into the agreed column.
//! * **Totality is never rounded up.** [`ChainReport::total_domain`] is set by
//!   the caller from an exhaustive enumeration or not at all, and the printed
//!   summary says which it was.
//! * **Cost is part of the verdict, not a footnote.** [`ChainReport::is_green`]
//!   consults [`ChainReport::cost_verdict`], which fails closed three separate
//!   ways: a row that produced no cost datum, a threshold that was accepted but
//!   never shown *necessary*, and offsets that differ across the domain. See
//!   the note below for what that does and does not catch.
//!
//! The cost verdict itself lives in [`super::cost`], which documents what
//! making cost a gate does and does not catch.
//!
use std::collections::BTreeMap;

use super::cost::CostVerdict;
use super::obligations::RunResult;
use super::EnumModel;

/// One row of the differential: one chain, one input, every executor that could
/// reach it.
#[derive(Debug, Clone)]
pub struct DiffRow {
    /// Chain name (the shipped function's short name).
    pub chain: String,
    /// The input variant tag.
    pub tag: u32,
    /// trust-ir reference interpreter — value, and the exact step count when the
    /// run returned. A FAULT is a first-class answer with no step count, not a
    /// missing leg: "trust-ir faulted where Clean returned" is a disagreement
    /// worth seeing, and dropping the leg would silently downgrade it to
    /// `Insufficient`.
    pub trust: Option<(RunResult, Option<u32>)>,
    /// Clean's `ir_eval` — value, and the LEAST fuel at which the kernel
    /// accepted it (`None` when no fuel in the probed range was accepted).
    pub clean: Option<(RunResult, Option<u32>)>,
    /// Was that least fuel shown to be NEEDED — `fuel_out` kernel-accepted one
    /// step below it?
    ///
    /// A threshold that was accepted but never shown necessary is an upper
    /// bound, and an upper bound compared against trust-ir's exact step count is
    /// not a cost correspondence. Recorded per row and gated in
    /// [`ChainReport::cost_verdict`] rather than printed as a note, which is
    /// what it used to be.
    pub threshold_tight: bool,
    /// The shipped compiled function, called directly.
    pub shipped: Option<RunResult>,
    /// Anything that made a leg refuse rather than answer.
    pub notes: Vec<String>,
}

impl DiffRow {
    /// Do all the executors that answered agree on the returned VALUE?
    #[must_use]
    pub fn value_agreement(&self) -> Agreement {
        let mut seen: Vec<(&str, &RunResult)> = Vec::new();
        if let Some((r, _)) = &self.trust {
            seen.push(("trust-ir", r));
        }
        if let Some((r, _)) = &self.clean {
            seen.push(("clean", r));
        }
        if let Some(r) = &self.shipped {
            seen.push(("shipped", r));
        }
        if seen.len() < 2 {
            return Agreement::Insufficient;
        }
        let first = seen[0].1;
        if seen.iter().all(|(_, r)| *r == first) {
            Agreement::Agree(seen.len())
        } else {
            Agreement::Disagree(
                seen.iter()
                    .map(|(who, r)| format!("{who}={r}"))
                    .collect::<Vec<_>>()
                    .join(" vs "),
            )
        }
    }

    /// Clean's measured fuel threshold minus trust-ir's reported step count.
    ///
    /// `None` when either side produced no number — which is itself a gated
    /// condition, counted as [`CostVerdict::Unpriced`] rather than skipped.
    #[must_use]
    pub(crate) fn cost_offset(&self) -> Option<i64> {
        let (_, steps) = self.trust.as_ref()?;
        let (_, threshold) = self.clean.as_ref()?;
        Some(i64::from((*threshold)?) - i64::from((*steps)?))
    }

    /// A one-line rendering used by the gate's output.
    #[must_use]
    pub fn render(&self) -> String {
        let trust = self.trust.as_ref().map_or_else(
            || "-".to_owned(),
            |(r, s)| match s {
                Some(s) => format!("{r} @{s} steps"),
                None => format!("{r} @no-step-count"),
            },
        );
        let clean = self.clean.as_ref().map_or_else(
            || "-".to_owned(),
            |(r, t)| match t {
                Some(t) if self.threshold_tight => format!("{r} @fuel={t} (tight)"),
                Some(t) => format!("{r} @fuel>={t} LOOSE"),
                None => format!("{r} @fuel=?"),
            },
        );
        let shipped = self
            .shipped
            .as_ref()
            .map_or_else(|| "-".to_owned(), ToString::to_string);
        format!(
            "  tag {:>2} | trust-ir {trust:<24} | clean {clean:<26} | shipped {shipped:<12} | {:?}",
            self.tag,
            self.value_agreement()
        )
    }
}

/// The verdict for one row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Agreement {
    /// All `n` executors that answered returned the same value.
    Agree(usize),
    /// They did not. The payload names who said what, verbatim.
    Disagree(String),
    /// Fewer than two executors answered — no comparison was made.
    Insufficient,
}

/// The measured summary for one chain.
#[derive(Debug, Clone)]
pub struct ChainReport {
    /// Chain name.
    pub chain: String,
    /// How faithfully the harness modelled the argument enum.
    pub enum_model: EnumModel,
    /// Inputs where every answering executor agreed on the value.
    pub agreed: usize,
    /// Inputs where they did not.
    pub disagreed: usize,
    /// Inputs where fewer than two executors answered.
    pub insufficient: usize,
    /// Is the input set the WHOLE domain of the function?
    ///
    /// `true` only when every inhabitant of the argument type was enumerated,
    /// which makes agreement extensional on that body rather than a sample.
    pub total_domain: bool,
    /// Distinct Clean-minus-trust cost offsets observed, with their counts.
    pub cost_offsets: BTreeMap<i64, usize>,
    /// Rows whose fuel threshold was accepted but not shown necessary.
    pub loose_thresholds: usize,
    /// The offset this chain is DECLARED to have.
    ///
    /// Compared against the measured one, because a uniform-but-wrong offset is
    /// exactly what a mis-derived harness overhead produces.
    pub expected_cost_offset: i64,
    /// The rows themselves.
    pub rows: Vec<DiffRow>,
}

impl ChainReport {
    /// A chain passes only if every row agreed on the VALUE, at least one row
    /// exists, **and** the cost correspondence is the pinned uniform offset.
    #[must_use]
    pub fn is_green(&self) -> bool {
        self.disagreed == 0
            && self.insufficient == 0
            && self.agreed > 0
            && self.cost_verdict() == CostVerdict::Uniform(self.expected_cost_offset)
    }

    /// The cost verdict, fail-closed in three directions. See [`CostVerdict`].
    #[must_use]
    pub fn cost_verdict(&self) -> CostVerdict {
        CostVerdict::of(self.rows.len(), self.loose_thresholds, &self.cost_offsets)
    }

    /// Is the cost correspondence a single consistent offset over a fully
    /// priced, tightly pinned domain?
    #[must_use]
    pub fn cost_is_uniform(&self) -> bool {
        matches!(self.cost_verdict(), CostVerdict::Uniform(_))
    }

    /// Does the measured cost meet the chain's declared expectation?
    #[must_use]
    pub fn cost_is_pinned(&self) -> bool {
        self.cost_verdict() == CostVerdict::Uniform(self.expected_cost_offset)
    }

    /// One-line human summary, stating exactly what was measured.
    #[must_use]
    pub fn summary(&self) -> String {
        let scope = if self.total_domain {
            "TOTAL domain"
        } else {
            "SAMPLE of domain"
        };
        let offsets = if self.cost_offsets.is_empty() {
            "no cost data".to_owned()
        } else {
            self.cost_offsets
                .iter()
                .map(|(off, n)| format!("{off:+} x{n}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        format!(
            "{}: {} agreed / {} disagreed / {} insufficient over a {scope}; \
             enum model {:?}; clean-minus-trust cost offset {{{offsets}}} \
             vs pinned {:+}; cost verdict {:?}",
            self.chain,
            self.agreed,
            self.disagreed,
            self.insufficient,
            self.enum_model,
            self.expected_cost_offset,
            self.cost_verdict(),
        )
    }
}

/// Fold rows into a chain report.
#[must_use]
pub fn summarize(
    chain: &str,
    enum_model: EnumModel,
    total_domain: bool,
    expected_cost_offset: i64,
    rows: Vec<DiffRow>,
) -> ChainReport {
    let mut agreed = 0;
    let mut disagreed = 0;
    let mut insufficient = 0;
    let mut loose_thresholds = 0;
    let mut cost_offsets: BTreeMap<i64, usize> = BTreeMap::new();
    for row in &rows {
        match row.value_agreement() {
            Agreement::Agree(_) => agreed += 1,
            Agreement::Disagree(_) => disagreed += 1,
            Agreement::Insufficient => insufficient += 1,
        }
        if let Some(off) = row.cost_offset() {
            *cost_offsets.entry(off).or_insert(0) += 1;
        }
        if !row.threshold_tight {
            loose_thresholds += 1;
        }
    }
    ChainReport {
        chain: chain.to_owned(),
        enum_model,
        agreed,
        disagreed,
        insufficient,
        total_domain,
        cost_offsets,
        loose_thresholds,
        expected_cost_offset,
        rows,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(
        trust: Option<(RunResult, Option<u32>)>,
        clean: Option<(RunResult, Option<u32>)>,
    ) -> DiffRow {
        DiffRow {
            chain: "x".to_owned(),
            tag: 0,
            trust,
            clean,
            threshold_tight: true,
            shipped: None,
            notes: Vec::new(),
        }
    }

    fn agreeing(clean_fuel: u32) -> DiffRow {
        row(
            Some((RunResult::Bool(true), Some(6))),
            Some((RunResult::Bool(true), Some(clean_fuel))),
        )
    }

    #[test]
    fn test_a_single_executor_is_never_an_agreement() {
        let r = row(Some((RunResult::Bool(true), Some(6))), None);
        assert_eq!(r.value_agreement(), Agreement::Insufficient);
    }

    #[test]
    fn test_two_agreeing_executors_agree() {
        let r = agreeing(6);
        assert_eq!(r.value_agreement(), Agreement::Agree(2));
    }

    #[test]
    fn test_disagreement_names_both_sides() {
        let r = row(
            Some((RunResult::Bool(true), Some(6))),
            Some((RunResult::Bool(false), Some(6))),
        );
        match r.value_agreement() {
            Agreement::Disagree(detail) => {
                assert!(detail.contains("trust-ir=bool true"), "{detail}");
                assert!(detail.contains("clean=bool false"), "{detail}");
            }
            other => panic!("expected a disagreement, got {other:?}"),
        }
    }

    #[test]
    fn test_cost_offset_is_clean_minus_trust() {
        assert_eq!(agreeing(7).cost_offset(), Some(1));
    }

    #[test]
    fn test_an_empty_chain_is_not_green() {
        let report = summarize("empty", EnumModel::Exact, false, 0, Vec::new());
        assert!(
            !report.is_green(),
            "a chain with no rows must never be green"
        );
    }

    #[test]
    fn test_an_insufficient_row_blocks_green() {
        let report = summarize(
            "half",
            EnumModel::Exact,
            true,
            0,
            vec![row(Some((RunResult::Bool(true), Some(6))), None)],
        );
        assert!(!report.is_green());
        assert_eq!(report.insufficient, 1);
    }

    #[test]
    fn test_summary_says_sample_when_the_domain_is_not_exhausted() {
        let report = summarize("s", EnumModel::TagSurrogate, false, 0, vec![agreeing(6)]);
        assert!(
            report.summary().contains("SAMPLE of domain"),
            "{}",
            report.summary()
        );
        assert!(report.summary().contains("TagSurrogate"));
    }

    // ── the cost half is a GATE, and these are its falsifications ──────────

    #[test]
    fn test_values_agreeing_is_not_enough_when_the_offsets_diverge() {
        let report = summarize(
            "divergent",
            EnumModel::Exact,
            true,
            0,
            vec![agreeing(6), agreeing(7)],
        );
        assert_eq!(report.agreed, 2, "both rows agree on the VALUE");
        assert_eq!(report.disagreed, 0);
        assert_eq!(report.cost_verdict(), CostVerdict::Divergent);
        assert!(
            !report.is_green(),
            "a chain whose step structures diverge must not be green on values alone"
        );
    }

    #[test]
    fn test_a_uniform_but_unpinned_offset_is_not_green() {
        // Exactly the shape a wrong harness overhead produces: every row shifts
        // by the same amount, so uniformity alone cannot see it.
        let report = summarize(
            "shifted",
            EnumModel::Exact,
            true,
            0,
            vec![agreeing(7), agreeing(7)],
        );
        assert_eq!(report.cost_verdict(), CostVerdict::Uniform(1));
        assert!(
            report.cost_is_uniform(),
            "it IS uniform — that is the point"
        );
        assert!(
            !report.is_green(),
            "uniform is not enough: a constant shift must fail against the pin"
        );
    }

    #[test]
    fn test_an_unpriced_row_is_not_a_uniform_cost() {
        let report = summarize(
            "unpriced",
            EnumModel::Exact,
            true,
            0,
            vec![
                agreeing(6),
                row(
                    Some((RunResult::Bool(true), None)),
                    Some((RunResult::Bool(true), Some(6))),
                ),
            ],
        );
        assert_eq!(
            report.cost_verdict(),
            CostVerdict::Unpriced { rows: 2, priced: 1 },
            "one row of two produced no offset; the old `len() == 1` test called that uniform"
        );
        assert!(!report.is_green());
    }

    #[test]
    fn test_a_loose_threshold_is_not_a_cost() {
        let mut loose = agreeing(6);
        loose.threshold_tight = false;
        let report = summarize("loose", EnumModel::Exact, true, 0, vec![agreeing(6), loose]);
        assert_eq!(report.cost_verdict(), CostVerdict::Loose { loose: 1 });
        assert!(
            !report.is_green(),
            "an upper bound compared against an exact step count is not a correspondence"
        );
    }

    #[test]
    fn test_the_pinned_uniform_case_is_the_only_green_one() {
        let report = summarize(
            "ok",
            EnumModel::Exact,
            true,
            0,
            vec![agreeing(6), agreeing(6)],
        );
        assert_eq!(report.cost_verdict(), CostVerdict::Uniform(0));
        assert!(report.is_green());
    }
}
