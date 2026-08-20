// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rows, verdicts, and the per-chain measured summary.
//!
//! Two rules are enforced structurally here rather than by convention:
//!
//! * **A single executor is never an agreement.** A row that only one side
//!   could reach is [`Agreement::Insufficient`] and is counted separately; it
//!   is never folded into the agreed column.
//! * **Totality is never rounded up.** [`ChainReport::total_domain`] is set by
//!   the caller from an exhaustive enumeration or not at all, and the printed
//!   summary says which it was.

use std::collections::BTreeMap;

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
    /// Reported rather than asserted: a constant nonzero offset is a real
    /// finding about the two cost models, not a failure to hide. Only an
    /// *inconsistent* offset within a chain indicates the step structures
    /// actually differ.
    #[must_use]
    pub fn cost_offset(&self) -> Option<i64> {
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
                Some(t) => format!("{r} @fuel>={t}"),
                None => format!("{r} @fuel=?"),
            },
        );
        let shipped = self
            .shipped
            .as_ref()
            .map_or_else(|| "-".to_owned(), ToString::to_string);
        format!(
            "  tag {:>2} | trust-ir {trust:<24} | clean {clean:<24} | shipped {shipped:<12} | {:?}",
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
    /// The rows themselves.
    pub rows: Vec<DiffRow>,
}

impl ChainReport {
    /// A chain passes only if every row agreed and at least one row exists.
    #[must_use]
    pub fn is_green(&self) -> bool {
        self.disagreed == 0 && self.insufficient == 0 && self.agreed > 0
    }

    /// Is the cost correspondence a single consistent offset?
    ///
    /// One offset repeated across the whole domain means the two machines take
    /// the same number of steps up to a fixed convention. Several different
    /// offsets mean the step structures genuinely diverge somewhere.
    #[must_use]
    pub fn cost_is_uniform(&self) -> bool {
        self.cost_offsets.len() == 1
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
             enum model {:?}; clean-minus-trust cost offset {{{offsets}}}",
            self.chain, self.agreed, self.disagreed, self.insufficient, self.enum_model
        )
    }
}

/// Fold rows into a chain report.
#[must_use]
pub fn summarize(
    chain: &str,
    enum_model: EnumModel,
    total_domain: bool,
    rows: Vec<DiffRow>,
) -> ChainReport {
    let mut agreed = 0;
    let mut disagreed = 0;
    let mut insufficient = 0;
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
    }
    ChainReport {
        chain: chain.to_owned(),
        enum_model,
        agreed,
        disagreed,
        insufficient,
        total_domain,
        cost_offsets,
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
            shipped: None,
            notes: Vec::new(),
        }
    }

    #[test]
    fn test_a_single_executor_is_never_an_agreement() {
        let r = row(Some((RunResult::Bool(true), Some(6))), None);
        assert_eq!(r.value_agreement(), Agreement::Insufficient);
    }

    #[test]
    fn test_two_agreeing_executors_agree() {
        let r = row(
            Some((RunResult::Bool(true), Some(6))),
            Some((RunResult::Bool(true), Some(6))),
        );
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
        let r = row(
            Some((RunResult::Bool(true), Some(6))),
            Some((RunResult::Bool(true), Some(7))),
        );
        assert_eq!(r.cost_offset(), Some(1));
    }

    #[test]
    fn test_an_empty_chain_is_not_green() {
        let report = summarize("empty", EnumModel::Exact, false, Vec::new());
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
            vec![row(Some((RunResult::Bool(true), Some(6))), None)],
        );
        assert!(!report.is_green());
        assert_eq!(report.insufficient, 1);
    }

    #[test]
    fn test_summary_says_sample_when_the_domain_is_not_exhausted() {
        let report = summarize(
            "s",
            EnumModel::TagSurrogate,
            false,
            vec![row(
                Some((RunResult::Bool(true), Some(6))),
                Some((RunResult::Bool(true), Some(6))),
            )],
        );
        assert!(
            report.summary().contains("SAMPLE of domain"),
            "{}",
            report.summary()
        );
        assert!(report.summary().contains("TagSurrogate"));
    }
}
