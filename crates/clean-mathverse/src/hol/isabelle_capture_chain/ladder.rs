// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The response-ladder state machine: given a segment that ran out of store,
//! decide the next recovery rung, and (for the bisect rung) split a segment
//! into two downward-closed sub-segments.
//!
//! Rung ladder (in order, each taken at most once per segment):
//!   A. threads>1  → retry the SAME segment at threads=1;
//!   B. >1 theory  → bisect into two chained sub-sessions;
//!   C. 1 theory   → demote to record_proofs=2 (proofless heap-bake);
//!   else          → exhausted (a single proofless theory still OOMs: halt).

use std::path::{Path, PathBuf};

use super::state::SegmentState;

/// The recovery action chosen for an out-of-store segment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LadderAction {
    /// Retry the same segment serialized (threads=1).
    RetryThreads1,
    /// Split the segment's theory list in half into two chained sub-sessions.
    Bisect,
    /// Demote to a proofless (record_proofs=2) heap-bake and re-run.
    Proofless,
    /// No rung remains — the chain must halt for manual intervention.
    Exhausted,
}

/// Decide the next ladder rung for a segment that just ran out of store.
///
/// Consults the segment's already-taken rungs so a resume never repeats an
/// exhausted step, and picks the first still-available rung in ladder order.
#[must_use]
pub fn decide_ladder(seg: &SegmentState) -> LadderAction {
    if !seg.ladder.retry_threads1 && seg.threads > 1 {
        LadderAction::RetryThreads1
    } else if !seg.ladder.bisected && seg.segment.theories.len() > 1 {
        LadderAction::Bisect
    } else if !seg.ladder.made_proofless && seg.segment.record_proofs > 2 {
        LadderAction::Proofless
    } else {
        LadderAction::Exhausted
    }
}

/// Split `seg` into two downward-closed sub-segments, preserving theory order.
///
/// The prefix (`<session>-1`) takes the lower half of the theory list and
/// chains on `seg`'s parent; the suffix (`<session>-2`) takes the upper half and
/// chains on the prefix. Because the theory list is already in downward-closed
/// intra-chain build order, the prefix is itself downward-closed (its imports
/// resolve within it → a parent heap) and the suffix builds on the prefix's
/// heap. Both sub-segments start with fresh ladder state at threads=1.
#[must_use]
pub fn bisect_segment(seg: &SegmentState) -> (SegmentState, SegmentState) {
    let theories = &seg.segment.theories;
    // len >= 2 is a precondition of the Bisect rung; mid is in [1, len-1] so
    // both halves are non-empty.
    let mid = (theories.len() / 2).clamp(1, theories.len().saturating_sub(1));
    let (lower, upper) = theories.split_at(mid);

    let sub1_session = format!("{}-1", seg.segment.session);
    let sub2_session = format!("{}-2", seg.segment.session);
    let sub1_dir = suffix_dir(&seg.segment.dir, "-1");
    let sub2_dir = suffix_dir(&seg.segment.dir, "-2");

    let mut a = seg.segment.clone();
    a.session = sub1_session.clone();
    a.dir = sub1_dir;
    a.theories = lower.to_vec();
    // a.parent stays seg.parent

    let mut b = seg.segment.clone();
    b.session = sub2_session;
    b.dir = sub2_dir;
    b.theories = upper.to_vec();
    b.parent = sub1_session;

    // Bisect only fires at threads=1 (rung A is exhausted or global threads=1),
    // so the sub-segments inherit the serialized thread count.
    (
        SegmentState::fresh(a, seg.threads),
        SegmentState::fresh(b, seg.threads),
    )
}

/// Append `suffix` to the final path component (`~/w/zp_c2` + `-1` →
/// `~/w/zp_c2-1`).
fn suffix_dir(dir: &Path, suffix: &str) -> PathBuf {
    let base = dir
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    dir.with_file_name(format!("{base}{suffix}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::isabelle_capture_chain::spec::Segment;
    use crate::hol::isabelle_capture_chain::state::LadderTaken;

    fn seg(threads: usize, rp: u32, theories: &[&str], ladder: LadderTaken) -> SegmentState {
        let mut s = SegmentState::fresh(
            Segment {
                session: "ZP-C2".into(),
                dir: "zp_c2".into(),
                theories: theories.iter().map(|t| (*t).to_string()).collect(),
                parent: "ZP-C1".into(),
                record_proofs: rp,
                note: None,
            },
            threads,
        );
        s.ladder = ladder;
        s
    }

    #[test]
    fn test_ladder_rung_a_when_threads_gt_1() {
        let s = seg(6, 4, &["T.a", "T.b"], LadderTaken::default());
        assert_eq!(decide_ladder(&s), LadderAction::RetryThreads1);
    }

    #[test]
    fn test_ladder_rung_b_bisect_at_threads1_multitheory() {
        let s = seg(1, 4, &["T.a", "T.b"], LadderTaken::default());
        assert_eq!(decide_ladder(&s), LadderAction::Bisect);
        // Also fires when threads>1 but rung A already taken.
        let s2 = seg(
            6,
            4,
            &["T.a", "T.b"],
            LadderTaken {
                retry_threads1: true,
                ..LadderTaken::default()
            },
        );
        assert_eq!(decide_ladder(&s2), LadderAction::Bisect);
    }

    #[test]
    fn test_ladder_rung_c_proofless_single_theory() {
        let s = seg(1, 4, &["T.a"], LadderTaken::default());
        assert_eq!(decide_ladder(&s), LadderAction::Proofless);
    }

    #[test]
    fn test_ladder_exhausted_single_proofless_theory() {
        let s = seg(
            1,
            2,
            &["T.a"],
            LadderTaken {
                made_proofless: true,
                ..LadderTaken::default()
            },
        );
        assert_eq!(decide_ladder(&s), LadderAction::Exhausted);
    }

    #[test]
    fn test_bisect_preserves_order_and_downward_closure() {
        let s = seg(
            1,
            4,
            &["T.a", "T.b", "T.c", "T.d", "T.e"],
            LadderTaken::default(),
        );
        let (a, b) = bisect_segment(&s);
        // Both halves non-empty, order preserved, concatenation == original.
        assert!(!a.segment.theories.is_empty() && !b.segment.theories.is_empty());
        let mut recombined = a.segment.theories.clone();
        recombined.extend(b.segment.theories.clone());
        assert_eq!(recombined, s.segment.theories, "order + closure preserved");
        // The suffix chains on the prefix (downward-closed prefix is a parent heap).
        assert_eq!(
            a.segment.parent, "ZP-C1",
            "prefix keeps the original parent"
        );
        assert_eq!(b.segment.parent, "ZP-C2-1", "suffix chains on the prefix");
        assert_eq!(a.segment.session, "ZP-C2-1");
        assert_eq!(b.segment.session, "ZP-C2-2");
        assert_eq!(a.segment.dir, PathBuf::from("zp_c2-1"));
        assert_eq!(b.segment.dir, PathBuf::from("zp_c2-2"));
    }

    #[test]
    fn test_bisect_two_theories_splits_one_and_one() {
        let s = seg(1, 4, &["T.a", "T.b"], LadderTaken::default());
        let (a, b) = bisect_segment(&s);
        assert_eq!(a.segment.theories, vec!["T.a".to_string()]);
        assert_eq!(b.segment.theories, vec!["T.b".to_string()]);
    }
}
