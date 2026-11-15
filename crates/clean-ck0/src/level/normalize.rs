// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The canonicalising helpers behind [`Level`]'s smart constructors.

use std::cmp::Ordering;
use std::sync::Arc;

use super::limit::Limit;
#[cfg(test)]
use super::limit::{total, Unbounded};
use super::{Level, Repr};

/// `imax` reduction given already-normalized children.
pub(super) fn reduce_imax<L: Limit>(l1: Level, l2: Level) -> Result<Level, L::Error> {
    if l2.is_zero() {
        return Ok(Level::zero());
    }
    if l2.is_nonzero() {
        return Level::max_in::<L>(l1, l2);
    }
    if l1.is_zero() {
        return Ok(l2);
    }
    if l1 == Level::succ(Level::zero()) {
        return Ok(l2);
    }
    if l1 == l2 {
        return Ok(l1);
    }
    let r = Level::mk(Repr::IMax(Arc::new(l1), Arc::new(l2)));
    L::admit(&r)?;
    Ok(r)
}

/// Flatten a (possibly nested) `Max` tree into its leaf args.
pub(super) fn push_max_args(l: &Level, out: &mut Vec<Level>) {
    match &l.repr {
        Repr::Max(a, b) => {
            push_max_args(a, out);
            push_max_args(b, out);
        }
        _ => out.push(l.clone()),
    }
}

/// Canonicalize a `Max`-rooted level (flatten, normalize children, sort, dedup,
/// subsume, reapply offset). Mirrors Lean `level.cpp` normalize for Max.
pub(super) fn normalize_max<L: Limit>(base: &Level, outer_offset: u32) -> Result<Level, L::Error> {
    let mut todo = Vec::new();
    push_max_args(base, &mut todo);

    let mut args = Vec::new();
    for a in &todo {
        let normed = a.normalize_in::<L>()?;
        push_max_args(&normed, &mut args);
    }

    args.sort_by(|a, b| {
        if is_norm_lt(a, b) {
            Ordering::Less
        } else if is_norm_lt(b, a) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    });

    let mut rargs = dedup_max_args(&args);

    if outer_offset > 0 {
        for a in &mut rargs {
            *a = a.add_offset_in::<L>(outer_offset)?;
        }
    }

    if rargs.is_empty() {
        Ok(Level::zero())
    } else {
        mk_max_from_args_in::<L>(&rargs)
    }
}

/// Rebuild a right-associated `Max` from sorted args. An empty slice is the
/// empty max, `zero` (the caller never passes one).
#[cfg(test)]
pub(super) fn mk_max_from_args(args: &[Level]) -> Level {
    total(mk_max_from_args_in::<Unbounded>(args))
}

/// [`mk_max_from_args`], admitting each node as it builds it: the chain is as
/// long as its arguments, so it is refused after at most one node past the
/// bound rather than built whole (R166).
pub(super) fn mk_max_from_args_in<L: Limit>(args: &[Level]) -> Result<Level, L::Error> {
    let mut rev = args.iter().rev();
    let Some(last) = rev.next() else {
        return Ok(Level::zero());
    };
    let Some(penultimate) = rev.next() else {
        return Ok(last.clone());
    };
    let mut r = Level::mk(Repr::Max(
        Arc::new(penultimate.clone()),
        Arc::new(last.clone()),
    ));
    L::admit(&r)?;
    for a in rev {
        r = Level::mk(Repr::Max(Arc::new(a.clone()), Arc::new(r)));
        L::admit(&r)?;
    }
    Ok(r)
}

/// Dedup sorted `Max` args: drop explicit levels subsumed by a parametric one
/// with >= offset, and merge same-base args keeping the largest offset.
pub(super) fn dedup_max_args(args: &[Level]) -> Vec<Level> {
    // Sorted order puts the explicit levels (`zero` + k) first; only the last
    // (largest) of them can survive, and only when no later arg has an offset
    // at least as large.
    let explicit_run = args.iter().take_while(|l| l.is_explicit()).count();
    let mut iter = args.iter().skip(explicit_run.saturating_sub(1));
    if let Some(last_explicit) = explicit_run.checked_sub(1).and_then(|n| args.get(n)) {
        let k = last_explicit.get_offset().1;
        if args
            .iter()
            .skip(explicit_run)
            .any(|l| l.get_offset().1 >= k)
        {
            iter = args.iter().skip(explicit_run);
        }
    }

    let mut rargs: Vec<Level> = Vec::new();
    if let Some(first) = iter.next() {
        rargs.push(first.clone());
        let mut prev = first.get_offset();
        for arg in iter {
            let cur = arg.get_offset();
            if prev.0 == cur.0 {
                if prev.1 < cur.1 {
                    prev = cur;
                    if let Some(kept) = rargs.last_mut() {
                        *kept = arg.clone();
                    }
                }
            } else {
                prev = cur;
                rargs.push(arg.clone());
            }
        }
    }
    rargs
}

/// Total order used to sort `Max` args during normalization (Lean `is_norm_lt`):
/// order by base, then offset.
pub(super) fn is_norm_lt(a: &Level, b: &Level) -> bool {
    let (ba, oa) = a.get_offset();
    let (bb, ob) = b.get_offset();
    let bc = base_cmp(&ba, &bb);
    match bc {
        Ordering::Less => true,
        Ordering::Greater => false,
        Ordering::Equal => oa < ob,
    }
}

/// A deterministic total order over level *bases* (post-offset-strip): order by
/// kind tag, then by structural contents.
pub(super) fn base_cmp(a: &Level, b: &Level) -> Ordering {
    fn tag(l: &Level) -> u8 {
        match &l.repr {
            Repr::Zero => 0,
            Repr::Param(_) => 1,
            Repr::Max(_, _) => 2,
            Repr::IMax(_, _) => 3,
            Repr::Succ(_) => 4,
        }
    }
    let ta = tag(a);
    let tb = tag(b);
    if ta != tb {
        return ta.cmp(&tb);
    }
    match (&a.repr, &b.repr) {
        (Repr::Zero, Repr::Zero) => Ordering::Equal,
        (Repr::Param(x), Repr::Param(y)) => x.cmp(y),
        (Repr::Max(a1, a2), Repr::Max(b1, b2)) | (Repr::IMax(a1, a2), Repr::IMax(b1, b2)) => {
            base_cmp(a1, b1).then_with(|| base_cmp(a2, b2))
        }
        (Repr::Succ(x), Repr::Succ(y)) => base_cmp(x, y),
        _ => Ordering::Equal,
    }
}
