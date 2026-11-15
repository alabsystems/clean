// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use proptest::prelude::*;
use std::cmp::Ordering;

/// The index-loop `dedup_max_args` this crate shipped before the
/// iterator rewrite (2026-10-03), kept verbatim as the differential
/// oracle for it.
fn dedup_max_args_indexed(args: &[Level]) -> Vec<Level> {
    let mut rargs: Vec<Level> = Vec::new();
    let mut i = 0usize;
    if !args.is_empty() && args[i].is_explicit() {
        while i.saturating_add(1) < args.len() && args[i.saturating_add(1)].is_explicit() {
            i = i.saturating_add(1);
        }
        let k = args[i].get_offset().1;
        let mut j = i.saturating_add(1);
        while j < args.len() {
            if args[j].get_offset().1 >= k {
                break;
            }
            j = j.saturating_add(1);
        }
        if j < args.len() {
            i = i.saturating_add(1);
        }
    }
    if i < args.len() {
        rargs.push(args[i].clone());
        let mut prev = args[i].get_offset();
        i = i.saturating_add(1);
        while i < args.len() {
            let cur = args[i].get_offset();
            if prev.0 == cur.0 {
                if prev.1 < cur.1 {
                    prev = cur;
                    rargs.pop();
                    rargs.push(args[i].clone());
                }
            } else {
                prev = cur;
                rargs.push(args[i].clone());
            }
            i = i.saturating_add(1);
        }
    }
    rargs
}

/// The index-loop `mk_max_from_args` (non-empty input), the oracle for
/// the iterator rewrite.
fn mk_max_from_args_indexed(args: &[Level]) -> Level {
    if args.len() == 1 {
        return args[0].clone();
    }
    let last = args.len().saturating_sub(1);
    let prev = args.len().saturating_sub(2);
    let mut r = Level::mk(Repr::Max(
        Arc::new(args[prev].clone()),
        Arc::new(args[last].clone()),
    ));
    for i in (0..prev).rev() {
        r = Level::mk(Repr::Max(Arc::new(args[i].clone()), Arc::new(r)));
    }
    r
}

fn atom(base: Option<u32>, off: u32) -> Level {
    let mut l = match base {
        None => Level::mk(Repr::Zero),
        Some(p) => Level::mk(Repr::Param(p)),
    };
    for _ in 0..off {
        l = Level::mk(Repr::Succ(Arc::new(l)));
    }
    l
}

fn sorted(mut args: Vec<Level>) -> Vec<Level> {
    args.sort_by(|a, b| {
        if is_norm_lt(a, b) {
            Ordering::Less
        } else if is_norm_lt(b, a) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    });
    args
}

#[test]
fn dedup_explicit_run_edges() {
    // Every arg explicit: only the largest survives.
    let all = sorted(vec![atom(None, 2), atom(None, 0), atom(None, 1)]);
    assert_eq!(dedup_max_args(&all), vec![atom(None, 2)]);
    // An explicit level subsumed by a later offset is dropped.
    let sub = sorted(vec![atom(None, 1), atom(Some(0), 1)]);
    assert_eq!(dedup_max_args(&sub), vec![atom(Some(0), 1)]);
    // ... and kept when no later offset reaches it.
    let keep = sorted(vec![atom(None, 3), atom(Some(0), 1)]);
    assert_eq!(dedup_max_args(&keep), keep);
    // Same base merges to the largest offset.
    let merge = sorted(vec![atom(Some(0), 0), atom(Some(0), 2)]);
    assert_eq!(dedup_max_args(&merge), vec![atom(Some(0), 2)]);
    assert!(dedup_max_args(&[]).is_empty());
    assert_eq!(mk_max_from_args(&[]), Level::zero());
}

proptest! {
    #[test]
    fn dedup_and_rebuild_match_indexed_oracle(
        raw in prop::collection::vec((prop::option::of(0u32..3), 0u32..4), 0..8)
    ) {
        let args = sorted(raw.into_iter().map(|(b, o)| atom(b, o)).collect());
        let got = dedup_max_args(&args);
        prop_assert_eq!(&got, &dedup_max_args_indexed(&args));
        if !got.is_empty() {
            prop_assert_eq!(mk_max_from_args(&got), mk_max_from_args_indexed(&got));
        }
        if !args.is_empty() {
            prop_assert_eq!(mk_max_from_args(&args), mk_max_from_args_indexed(&args));
        }
    }
}
