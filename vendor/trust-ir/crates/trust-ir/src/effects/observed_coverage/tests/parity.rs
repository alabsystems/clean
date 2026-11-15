// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_set_spelling_matches_the_exact_ordinary_inclusion_matrix() {
    let rows = sets();
    for ours in &rows {
        for theirs in &rows {
            trace(Query::Set(ours, theirs));
        }
    }
    assert!(EffectSet::Nothing.covers(&EffectSet::Places(Vec::new())));
    assert!(EffectSet::Places(Vec::new()).covers(&EffectSet::Nothing));
    assert!(!EffectSet::Places(Vec::new()).covers(&EffectSet::Everything));
}
#[test]
fn fixed_place_identity_keeps_tags_and_all_u32_bits_distinct() {
    for a in [p(0), p(1), p(u32::MAX), g(0), g(1), g(u32::MAX)] {
        for b in [p(0), p(1), p(u32::MAX), g(0), g(1), g(u32::MAX)] {
            let ours = EffectSet::Places(vec![a]);
            let theirs = EffectSet::Places(vec![b]);
            let events = trace(Query::Set(&ours, &theirs));
            assert_eq!(ours.covers(&theirs), a == b);
            assert!(events.events.iter().any(|event| event.work == 3));
        }
    }
}
#[test]
fn noncanonical_duplicate_and_reordered_rows_remain_a_set_not_structural_equality() {
    let ours = EffectSet::Places(vec![g(8), p(3), g(8), p(2), p(3)]);
    let theirs = EffectSet::Places(vec![p(2), g(8), p(3), p(2)]);
    assert_ne!(ours, theirs);
    assert!(ours.covers(&theirs));
    assert!(theirs.covers(&ours));
    trace(Query::Set(&ours, &theirs));
    trace(Query::Set(&theirs, &ours));
    trace(Query::Set(
        &ours,
        &EffectSet::Places(vec![p(3), g(9), p(2)]),
    ));
}
#[test]
fn summary_all_flag_truth_tables_and_independent_memory_sides_match_ordinary() {
    for ours in 0..16 {
        for theirs in 0..16 {
            let a = summary(ours);
            let b = summary(theirs);
            trace(Query::Summary(&a, &b));
            assert_eq!(a.covers(&b), theirs & !ours == 0);
        }
    }
    let rows = sets();
    for a in &rows {
        for b in &rows {
            let ours = EffectSummary::top().reading(a.clone()).writing(b.clone());
            let theirs = EffectSummary::pure().reading(b.clone()).writing(a.clone());
            trace(Query::Summary(&ours, &theirs));
        }
    }
}
#[test]
fn explicit_global_names_scan_both_sides_and_everything_is_not_an_explicit_global() {
    let rows = sets();
    for a in &rows {
        for b in &rows {
            let summary = EffectSummary::pure().reading(a.clone()).writing(b.clone());
            trace(Query::Names(&summary));
        }
    }
    assert!(!EffectSummary::top().names_a_global());
    assert!(
        EffectSummary::pure()
            .writing(EffectSet::Places(vec![p(0), g(0)]))
            .names_a_global()
    );
}
#[test]
fn set_shortcuts_do_not_walk_irrelevant_or_already_satisfied_rows() {
    let empty = EffectSet::Places(Vec::new());
    let long = EffectSet::Places(vec![g(99); 10000]);
    assert_eq!(
        trace(Query::Set(&EffectSet::Everything, &empty)).events,
        trace(Query::Set(&EffectSet::Everything, &long)).events
    );
    assert_eq!(
        trace(Query::Set(&empty, &EffectSet::Nothing)).events,
        trace(Query::Set(&long, &EffectSet::Nothing)).events
    );
    let early = EffectSet::Places(vec![p(1)]);
    let mut tailed = vec![p(1)];
    tailed.extend(vec![g(99); 10000]);
    assert_eq!(
        trace(Query::Set(&early, &early)).events,
        trace(Query::Set(&EffectSet::Places(tailed), &early)).events
    );
}
#[test]
fn first_missing_membership_does_not_scan_later_required_rows() {
    let ours = EffectSet::Places(vec![p(1), p(2)]);
    let short = EffectSet::Places(vec![g(0)]);
    let mut rows = vec![g(0)];
    rows.extend(vec![p(1); 10000]);
    let long = EffectSet::Places(rows);
    assert_eq!(
        trace(Query::Set(&ours, &short)).events,
        trace(Query::Set(&ours, &long)).events
    );
}
#[test]
fn summary_read_then_write_failures_skip_every_later_set_and_flag() {
    let pure = EffectSummary::pure();
    let read_fail = EffectSummary::top();
    let mut changed = read_fail.clone();
    changed.writes = EffectSet::Places(vec![g(9); 10000]);
    changed.allocates = false;
    changed.frees = false;
    changed.may_unwind = false;
    changed.io = false;
    assert_eq!(
        trace(Query::Summary(&pure, &read_fail)).events,
        trace(Query::Summary(&pure, &changed)).events
    );
    let write_fail = EffectSummary::pure().writing(EffectSet::Everything);
    changed = write_fail.clone();
    changed.allocates = true;
    changed.frees = true;
    changed.may_unwind = true;
    changed.io = true;
    assert_eq!(
        trace(Query::Summary(&pure, &write_fail)).events,
        trace(Query::Summary(&pure, &changed)).events
    );
}
#[test]
fn each_true_left_flag_skips_its_right_read_and_each_first_failure_skips_later_flags() {
    // Nothing/Nothing on both sides: begin + two(field + tag) + four left
    // flag reads + final publication. True left flags skip all four right reads.
    let top_flags = summary(15);
    let left_true = trace(Query::Summary(&top_flags, &summary(0)));
    let right_true = trace(Query::Summary(&top_flags, &summary(15)));
    assert_eq!(left_true.events, right_true.events);
    assert_eq!(left_true.events.len(), 10);
    for bit in 0..4 {
        let ours = summary(0);
        let fail = summary(1 << bit);
        let fail_with_later = summary(15 & !((1 << bit) - 1));
        let a = trace(Query::Summary(&ours, &fail));
        let b = trace(Query::Summary(&ours, &fail_with_later));
        assert_eq!(a.events, b.events);
        assert_eq!(a.events.len(), 6 + 2 * (bit as usize + 1));
    }
}
#[test]
fn names_global_stops_in_reads_and_at_the_first_global_without_tail_work() {
    let short = EffectSummary::pure().reading(EffectSet::Places(vec![p(0), g(1)]));
    let mut rows = vec![p(0), g(1)];
    rows.extend(vec![p(2); 10000]);
    let long = EffectSummary::pure()
        .reading(EffectSet::Places(rows))
        .writing(EffectSet::Places(vec![g(9); 10000]));
    assert_eq!(
        trace(Query::Names(&short)).events,
        trace(Query::Names(&long)).events
    );
    let short = EffectSummary::pure().writing(EffectSet::Places(vec![p(0), g(1)]));
    let mut long = short.clone();
    if let EffectSet::Places(rows) = &mut long.writes {
        rows.extend(vec![g(9); 10000]);
    }
    assert_eq!(
        trace(Query::Names(&short)).events,
        trace(Query::Names(&long)).events
    );
}
