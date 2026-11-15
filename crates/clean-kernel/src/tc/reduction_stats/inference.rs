// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Aggregate work observations, not proof or performance admission.
//!
//! Enable `clean-kernel/inference-stats` alone for this diagnostic. The legacy
//! `reduction-stats` feature has separate term-formatting/per-name costs and is
//! not implied. Every inference/memo hook is cfg-gated: with this feature off
//! there are no hook calls, TLS state, expression-kind reads or counter work.
//!
//! `CLEAN_INFERENCE_STATS_EARLY=1` (exactly `1`, no other spelling) opts into at
//! most eight aggregate stderr records PER THREAD. It is read once when that
//! thread first uses the facility. Fixed checkpoints are 1,000 through
//! 10,000,000,000 fast-inner entries, spaced by factors of ten. Resetting the
//! report does not reset these lifetime checkpoints or replenish the quota.
//! No environment option changes thresholds, type-checker limits or policy.
//! These bounded writes can perturb timing; they are not nominal benchmarks.
//! A thread may spend checkpoints during prelude/earlier work before a target
//! audit starts. Neither a reset nor an external phase label implies that all
//! thread-wide samples came from that audit.
//!
//! Counts are attempted fast-inner dispatches (including eventual errors), not
//! unique nodes. Depth is the existing shared inference-frame depth, which can
//! include certificate frames, not expression depth. Binder counters count
//! the named fast-inference call sites, NOT nodes traversed by those operations.
//! Structural hashing/equality, allocation/retained bytes, WHNF, certificate
//! inference and binder-helper internals are unmeasured. Memo peaks observe the
//! shared fast/certificate memo's actual insertions, per checker, never a sum
//! across checkers. No expression, name, context or certificate is retained.

/// Positions of the fixed node-kind counters; no child traversal is involved.
pub const INFERENCE_NODE_KINDS: [&str; 25] = [
    "BVar",
    "FVar",
    "Sort",
    "Const",
    "App",
    "Lam",
    "Pi",
    "Let",
    "Lit",
    "Proj",
    "MData",
    "SProp",
    "Squash",
    "CubicalInterval",
    "CubicalI0",
    "CubicalI1",
    "CubicalPath",
    "CubicalPathLam",
    "CubicalPathApp",
    "CubicalHComp",
    "CubicalTransp",
    "CubicalCoe",
    "ZFCSet",
    "ZFCMem",
    "ZFCComprehension",
];

/// Fixed-size current-thread totals since the last explicit reset.
/// Counters saturate instead of wrapping; no count changes checking behavior.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct InferenceStats {
    pub fast_visits: u64,
    pub strict_visits: u64,
    pub infer_only_visits: u64,
    pub node_kinds: [u64; 25],
    pub max_frame_depth: u32,
    pub arc_hits: u64,
    /// Includes inference failures and in-flight work in an early snapshot;
    /// not necessarily equal to admissions plus capacity refusals.
    pub arc_misses: u64,
    /// Fast misses whose input has neither free nor loose bound variables.
    pub arc_closed_input_misses: u64,
    /// A miss whose recursive fast inference actually returned an error.
    pub arc_inference_errors: u64,
    pub arc_no_frame_bypasses: u64,
    pub arc_admissions: u64,
    /// Successful inference could not admit an absent key (zero memo capacity).
    pub arc_capacity_refusals: u64,
    /// Recursive work had already filled the requested key before admission.
    pub arc_recursive_fills: u64,
    /// Largest SINGLE checker's shared memo seen at an insertion or fast lookup.
    pub arc_peak_entries: usize,
    /// Admission-window rotations; hits/upgrades do not rotate. These observe
    /// the shared fast/certificate memo, not only fast inference.
    pub arc_rotations: u64,
    /// Entries dropped by those rotations, not scope retirement, policy reset
    /// or outer-frame cleanup. This is an entry count, not retained bytes.
    pub arc_evicted_entries: u64,
    pub open_lam_calls: u64,
    pub open_pi_calls: u64,
    pub open_let_calls: u64,
    pub abstract_lam_calls: u64,
    pub subst_let_calls: u64,
    pub instantiate_app_calls: u64,
}

/// None when the feature is absent, rather than a misleading zero observation.
#[must_use]
pub fn inference_stats_snapshot() -> Option<InferenceStats> {
    #[cfg(feature = "inference-stats")]
    {
        Some(enabled::STATE.with(|state| state.borrow().counts))
    }
    #[cfg(not(feature = "inference-stats"))]
    {
        None
    }
}

/// Reset totals on this thread only; never reset the early-output lifetime quota.
/// Safe during inference: no diagnostic guard or type-checker state is changed.
pub fn inference_stats_reset() {
    #[cfg(feature = "inference-stats")]
    enabled::STATE.with(|state| state.borrow_mut().counts = InferenceStats::default());
}

/// Aggregate-only report, empty when disabled. No formatting of kernel terms.
#[must_use]
pub fn inference_stats_report() -> String {
    match inference_stats_snapshot() {
        Some(stats) => render(&stats),
        None => String::new(),
    }
}

fn render(stats: &InferenceStats) -> String {
    use std::fmt::Write;
    let mut out = format!("inference-stats v1: {stats:?}; node-kind-order=");
    for (i, name) in INFERENCE_NODE_KINDS.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{name}");
    }
    out.push('\n');
    out
}

#[cfg(all(feature = "inference-stats", not(debug_assertions)))]
pub(crate) use enabled::{
    record_arc, record_closed_input_miss, record_operation, record_visit, ArcEvent, Operation,
};
#[cfg(feature = "inference-stats")]
pub(crate) use enabled::{record_memo_entries, record_memo_rotation};

#[cfg(feature = "inference-stats")]
mod enabled {
    use super::*;
    #[cfg(any(test, not(debug_assertions)))]
    use crate::expr::ExprKind;
    use std::cell::RefCell;

    #[cfg(any(test, not(debug_assertions)))]
    pub(super) const CHECKPOINTS: [u64; 8] = [
        1_000,
        10_000,
        100_000,
        1_000_000,
        10_000_000,
        100_000_000,
        1_000_000_000,
        10_000_000_000,
    ];

    pub(super) struct State {
        pub(super) counts: InferenceStats,
        #[cfg(any(test, not(debug_assertions)))]
        early: bool,
        #[cfg(any(test, not(debug_assertions)))]
        lifetime_visits: u64,
        #[cfg(any(test, not(debug_assertions)))]
        next_checkpoint: usize,
    }

    impl State {
        fn new(_early: bool) -> Self {
            Self {
                counts: InferenceStats::default(),
                #[cfg(any(test, not(debug_assertions)))]
                early: _early,
                #[cfg(any(test, not(debug_assertions)))]
                lifetime_visits: 0,
                #[cfg(any(test, not(debug_assertions)))]
                next_checkpoint: 0,
            }
        }

        #[cfg(any(test, not(debug_assertions)))]
        fn visit(
            &mut self,
            kind: &ExprKind,
            depth: u32,
            infer_only: bool,
        ) -> Option<(u64, InferenceStats)> {
            inc(&mut self.counts.fast_visits);
            inc(if infer_only {
                &mut self.counts.infer_only_visits
            } else {
                &mut self.counts.strict_visits
            });
            inc(&mut self.counts.node_kinds[kind_index(kind)]);
            self.counts.max_frame_depth = self.counts.max_frame_depth.max(depth);
            inc(&mut self.lifetime_visits);
            if self.early && CHECKPOINTS.get(self.next_checkpoint) == Some(&self.lifetime_visits) {
                self.next_checkpoint += 1;
                Some((self.lifetime_visits, self.counts))
            } else {
                None
            }
        }
    }

    pub(super) fn early_enabled(value: Option<&str>) -> bool {
        value == Some("1")
    }

    thread_local! {
        pub(super) static STATE: RefCell<State> = RefCell::new(State::new(
            early_enabled(std::env::var("CLEAN_INFERENCE_STATS_EARLY").ok().as_deref())
        ));
    }

    #[cfg(any(test, not(debug_assertions)))]
    fn inc(counter: &mut u64) {
        *counter = counter.saturating_add(1);
    }

    #[cfg(any(test, not(debug_assertions)))]
    fn kind_index(kind: &ExprKind) -> usize {
        match kind {
            ExprKind::BVar(_) => 0,
            ExprKind::FVar(_) => 1,
            ExprKind::Sort(_) => 2,
            ExprKind::Const(..) => 3,
            ExprKind::App(..) => 4,
            ExprKind::Lam(..) => 5,
            ExprKind::Pi(..) => 6,
            ExprKind::Let(..) => 7,
            ExprKind::Lit(_) => 8,
            ExprKind::Proj(..) => 9,
            ExprKind::MData(..) => 10,
            ExprKind::SProp => 11,
            ExprKind::Squash(_) => 12,
            ExprKind::CubicalInterval => 13,
            ExprKind::CubicalI0 => 14,
            ExprKind::CubicalI1 => 15,
            ExprKind::CubicalPath { .. } => 16,
            ExprKind::CubicalPathLam { .. } => 17,
            ExprKind::CubicalPathApp { .. } => 18,
            ExprKind::CubicalHComp { .. } => 19,
            ExprKind::CubicalTransp { .. } => 20,
            ExprKind::CubicalCoe { .. } => 21,
            ExprKind::ZFCSet(_) => 22,
            ExprKind::ZFCMem { .. } => 23,
            ExprKind::ZFCComprehension { .. } => 24,
        }
    }

    #[cfg(any(test, not(debug_assertions)))]
    pub(crate) fn record_visit(kind: &ExprKind, depth: u32, infer_only: bool) {
        let checkpoint = STATE.with(|state| state.borrow_mut().visit(kind, depth, infer_only));
        // Release the TLS borrow before formatting/writing; output errors must
        // not turn a valid inference into a panic or change its result.
        if let Some((lifetime_visits, counts)) = checkpoint {
            write_checkpoint(&mut std::io::stderr().lock(), lifetime_visits, &counts);
        }
    }

    #[cfg(any(test, not(debug_assertions)))]
    fn write_checkpoint(output: &mut impl std::io::Write, visits: u64, counts: &InferenceStats) {
        let _ = write!(
            output,
            "[inference-stats checkpoint={visits}] {}",
            render(counts)
        );
    }

    #[cfg(any(test, not(debug_assertions)))]
    pub(crate) fn record_closed_input_miss(closed: bool) {
        if closed {
            STATE.with(|state| inc(&mut state.borrow_mut().counts.arc_closed_input_misses));
        }
    }

    #[cfg(any(test, not(debug_assertions)))]
    pub(crate) enum ArcEvent {
        Hit,
        Miss,
        InferenceError,
        NoFrame,
        Admission,
        CapacityRefusal,
        RecursiveFill,
    }

    #[cfg(any(test, not(debug_assertions)))]
    pub(crate) fn record_arc(event: ArcEvent, entries: usize) {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            state.counts.arc_peak_entries = state.counts.arc_peak_entries.max(entries);
            inc(match event {
                ArcEvent::Hit => &mut state.counts.arc_hits,
                ArcEvent::Miss => &mut state.counts.arc_misses,
                ArcEvent::InferenceError => &mut state.counts.arc_inference_errors,
                ArcEvent::NoFrame => &mut state.counts.arc_no_frame_bypasses,
                ArcEvent::Admission => &mut state.counts.arc_admissions,
                ArcEvent::CapacityRefusal => &mut state.counts.arc_capacity_refusals,
                ArcEvent::RecursiveFill => &mut state.counts.arc_recursive_fills,
            });
        });
    }

    pub(crate) fn record_memo_entries(entries: usize) {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            state.counts.arc_peak_entries = state.counts.arc_peak_entries.max(entries);
        });
    }

    pub(crate) fn record_memo_rotation(evicted: usize) {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            state.counts.arc_rotations = state.counts.arc_rotations.saturating_add(1);
            state.counts.arc_evicted_entries = state
                .counts
                .arc_evicted_entries
                .saturating_add(u64::try_from(evicted).unwrap_or(u64::MAX));
        });
    }

    #[cfg(any(test, not(debug_assertions)))]
    pub(crate) enum Operation {
        OpenLam,
        OpenPi,
        OpenLet,
        AbstractLam,
        SubstLet,
        InstantiateApp,
    }

    #[cfg(any(test, not(debug_assertions)))]
    pub(crate) fn record_operation(operation: Operation) {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            inc(match operation {
                Operation::OpenLam => &mut state.counts.open_lam_calls,
                Operation::OpenPi => &mut state.counts.open_pi_calls,
                Operation::OpenLet => &mut state.counts.open_let_calls,
                Operation::AbstractLam => &mut state.counts.abstract_lam_calls,
                Operation::SubstLet => &mut state.counts.subst_let_calls,
                Operation::InstantiateApp => &mut state.counts.instantiate_app_calls,
            });
        });
    }

    #[cfg(test)]
    include!("inference_tests.rs");
}

#[cfg(all(test, not(feature = "inference-stats")))]
mod disabled_tests {
    #[test]
    fn disabled_statistics_are_unavailable() {
        super::inference_stats_reset();
        assert_eq!(super::inference_stats_snapshot(), None);
        assert!(super::inference_stats_report().is_empty());
    }
}
