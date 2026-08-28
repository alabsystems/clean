// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the kernel's `LocalContext`: fvar allocation, the reserved
//! fvar floor, and lookup. Split out of `local_context.rs` for file size.

use super::*;

#[test]
fn test_checked_add_u32_normal() {
    assert_eq!(checked_add_u32(10, 20, "test"), 30);
    assert_eq!(checked_add_u32(0, 0, "test"), 0);
    assert_eq!(checked_add_u32(u32::MAX - 1, 1, "test"), u32::MAX);
}

#[test]
fn test_checked_add_u32_overflow_saturates() {
    assert_eq!(checked_add_u32(u32::MAX, 1, "test_overflow"), u32::MAX);
}

#[test]
fn test_checked_add_u32_large_overflow_saturates() {
    assert_eq!(
        checked_add_u32(u32::MAX / 2 + 1, u32::MAX / 2 + 1, "test_large"),
        u32::MAX
    );
}

/// Regression: `push_low_local` must advance `next_id` past the id it
/// hands out, otherwise a subsequent plain `push` while the low local is
/// still active mints the same id and panics ("active duplicate FVarId").
/// Observed via the elaborator unifier opening a Pi/Lam binder
/// (`push_binder_local`) and then recursing into kernel `is_def_eq` →
/// `infer_type_fast` → `push`.
#[test]
fn test_push_low_local_then_push_mints_distinct_id() {
    let mut ctx = LocalContext::new();
    let low = ctx.push_low_local(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert_eq!(low, FVarId(0), "fresh context should hand out the low id 0");
    // Must not panic and must not collide with the active low local.
    let fresh = ctx.push(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert_ne!(
        low, fresh,
        "plain push after push_low_local must mint a distinct FVarId"
    );
}

/// `reserve_fvar_floor` must put BOTH fresh-id paths above the caller's
/// high-water mark. A caller that hands over only PART of the free
/// variables it has minted (the elaborator's demand-driven context) has
/// no other way to say "these ids are taken": `push`'s `next_id` and
/// `push_low_local`'s low cursor both derive their candidate from what
/// the context holds, so without the floor either could alias a binding
/// the caller kept to itself.
#[test]
fn test_reserve_fvar_floor_lifts_both_fresh_id_paths() {
    let mut ctx = LocalContext::new();
    ctx.reserve_fvar_floor(64);
    let plain = ctx.push(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert!(
        plain.0 >= 64,
        "plain push must respect the floor, got {plain:?}"
    );
    let low = ctx.push_low_local(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert!(low.0 >= 64, "low push must respect the floor, got {low:?}");
    assert_ne!(plain, low);
}

/// The floor never decreases either counter, and a floor at or above the
/// metavariable tag leaves the LOW range alone (that is the whole point
/// of `push_low_local`).
#[test]
fn test_reserve_fvar_floor_never_decreases_and_respects_the_tag() {
    const META_TAG: u64 = 1u64 << 63;
    let mut ctx = LocalContext::new();
    ctx.reserve_fvar_floor(100);
    ctx.reserve_fvar_floor(10);
    let after_lower = ctx.push(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert!(
        after_lower.0 >= 100,
        "a lower floor must not walk the counter back, got {after_lower:?}"
    );

    let mut tagged = LocalContext::new();
    tagged.reserve_fvar_floor(META_TAG + 5);
    let low = tagged.push_low_local(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert!(
        low.0 < META_TAG,
        "a tagged-range floor must not push the low cursor into the tagged range, got {low:?}"
    );
    assert!(tagged.next_id() >= META_TAG + 5);
}

/// `push_low_local` must never *decrease* `next_id`: a counter already in
/// the meta-tagged range (>= 1<<63, from registered meta-FVars) stays put
/// while the returned id remains in the low range.
#[test]
fn test_push_low_local_does_not_decrease_next_id() {
    const META_TAG: u64 = 1u64 << 63;
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        FVarId(META_TAG),
        Name::anon(),
        Expr::type_(),
        BinderInfo::Default,
    );
    assert_eq!(ctx.next_id(), META_TAG + 1);
    let low = ctx.push_low_local(Name::anon(), Expr::type_(), BinderInfo::Default);
    assert!(low.0 < META_TAG, "returned id must stay in the low range");
    assert_eq!(
        ctx.next_id(),
        META_TAG + 1,
        "tagged-range next_id must not be decreased"
    );
}
