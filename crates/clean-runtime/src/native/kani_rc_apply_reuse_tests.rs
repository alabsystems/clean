// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kani harnesses: RC state machine, closure apply, and reset/reuse models.
//!
//! Verifies correctness of reference counting transitions, closure application
//! case handling and termination, and reset/reuse lifecycle invariants.
//!
//! Run with: `cargo kani -p clean-runtime` (`cargo kani` sets `cfg(kani)`;
//! the crate has no `kani` feature), or `--harness verify_rc_sticky` for the
//! sticky-count harnesses of section 3.
//! STOCK EXCEPTION (Trust lacks kani; measured `targo kani` -> `error: no such command`; kani drives its own pinned nightly).
//!
//! Part of #1144

use std::sync::atomic::{AtomicU32, Ordering};

use super::{closure_layout, ctor_layout};
use crate::rc_core::{
    check_drop_property, check_inc_property, drop_cell, inc_cell, is_exclusive_cell, DropOutcome,
    RC_INC_MAX, RC_STICKY, RC_STICKY_DROP,
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 3. Reference counting state machine model
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Verify the drop boundary on the real cell (`rc_core::drop_cell`).
///
/// Property: below the sticky band a drop reports `Last` (the caller frees)
/// iff the count was 0 (uniquely owned), and otherwise lowers it by exactly 1.
/// Getting this wrong causes use-after-free (a shared drop treated as last)
/// or a leak (the last drop not reported).
#[kani::proof]
#[kani::unwind(1)]
fn verify_rc_dec_dealloc_boundary() {
    let rc: u32 = kani::any();
    kani::assume(rc <= 1000); // bounded for tractability

    let cell = AtomicU32::new(rc);
    let outcome = drop_cell(&cell);
    if rc == 0 {
        assert_eq!(outcome, DropOutcome::Last, "the last reference frees");
        // The cell is freed, so the wrapped value is never read.
        assert_eq!(cell.load(Ordering::Relaxed), u32::MAX);
    } else {
        assert_eq!(outcome, DropOutcome::Live, "a shared drop does not free");
        assert_eq!(cell.load(Ordering::Relaxed), rc - 1);
    }
}

/// Verify inc_n followed by n drops returns to unique, on the real cells.
///
/// Property: `inc_cell(n)` followed by n `drop_cell` calls returns rc to 0,
/// and no intermediate drop reports `Last`.
#[kani::proof]
#[kani::unwind(18)]
fn verify_rc_inc_n_dec_n() {
    let n: u32 = kani::any();
    kani::assume(n > 0 && n <= 16);

    let cell = AtomicU32::new(0);
    inc_cell(&cell, n as usize);
    assert_eq!(cell.load(Ordering::Relaxed), n);
    for _ in 0..n {
        assert_eq!(
            drop_cell(&cell),
            DropOutcome::Live,
            "intermediate drops do not free"
        );
    }
    assert!(is_exclusive_cell(&cell), "after n drops, unique again");
}

/// Sticky counts (Lean v4.35.0 lean4#14838): an inline increment (n <=
/// RC_INC_MAX) never wraps. Below RC_STICKY it is exact; at or above it the
/// count is unchanged. Replaces the harness that documented the wrap from
/// u32::MAX to 0 ("exclusive") this contract removes.
#[kani::proof]
#[kani::unwind(2)]
fn verify_rc_sticky_inc_n_inline_never_wraps() {
    let rc: u32 = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= RC_INC_MAX);
    check_inc_property(rc, n);
}

/// The cold path (Lean `lean_inc_ref_huge_n`) on a slice near the band: at or
/// above RC_STICKY unchanged; otherwise exactly `rc + n`, or frozen in
/// `[RC_STICKY, RC_STICKY + RC_INC_MAX)`. Never wraps.
#[kani::proof]
#[kani::unwind(6)]
fn verify_rc_sticky_inc_huge_slice() {
    let rc: u32 = kani::any();
    let n: usize = kani::any();
    kani::assume(rc >= RC_STICKY - 3 * RC_INC_MAX as u32);
    kani::assume(n > RC_INC_MAX && n <= 4 * RC_INC_MAX);
    check_inc_property(rc, n);
}

/// A drop at or above RC_STICKY_DROP is absorbed: `Frozen`, count unchanged
/// (Lean `lean_is_never_freed`, lean4#15241). u32::MAX is excluded: there the
/// debug-build heuristic for a second drop of a freed cell asserts.
#[kani::proof]
#[kani::unwind(1)]
fn verify_rc_sticky_drop_band_absorbing() {
    let rc: u32 = kani::any();
    kani::assume(rc >= RC_STICKY_DROP && rc != u32::MAX);
    check_drop_property(rc);
}

/// Below the band a drop is exact: `Last` iff the count was 0, else `Live`
/// one lower.
#[kani::proof]
#[kani::unwind(1)]
fn verify_rc_sticky_drop_below_band() {
    let rc: u32 = kani::any();
    kani::assume(rc < RC_STICKY_DROP);
    check_drop_property(rc);
}

/// Exclusive iff the count is 0, so a frozen cell is never exclusive and
/// reset never reuses it.
#[kani::proof]
#[kani::unwind(1)]
fn verify_rc_sticky_exclusive_iff_zero() {
    let rc: u32 = kani::any();
    let cell = AtomicU32::new(rc);
    assert_eq!(is_exclusive_cell(&cell), rc == 0);
}

/// Lean `run_never_frees` (tests/elab/rc_model.lean), in Clean's encoding:
/// from a frozen count, any three increments, inline increments or drops
/// never free and leave the count frozen.
#[kani::proof]
#[kani::unwind(4)]
fn verify_rc_sticky_never_freed_sequence() {
    let rc: u32 = kani::any();
    kani::assume(rc >= RC_STICKY_DROP && rc != u32::MAX);
    let cell = AtomicU32::new(rc);
    for _ in 0..3 {
        let op: u8 = kani::any();
        match op % 3 {
            0 => inc_cell(&cell, 1),
            1 => {
                let n: usize = kani::any();
                kani::assume(n <= RC_INC_MAX);
                inc_cell(&cell, n);
            }
            _ => assert_ne!(
                drop_cell(&cell),
                DropOutcome::Last,
                "a frozen object is never freed"
            ),
        }
        let now = cell.load(Ordering::Relaxed);
        assert!(now >= RC_STICKY_DROP, "a frozen count stays frozen");
        assert_ne!(now, u32::MAX, "increments stop below u32::MAX");
    }
}

/// Verify that arbitrary inc/dec sequences maintain RC consistency.
///
/// Property: Starting from rc=0, a sequence of `n_inc` inc operations followed
/// by `n_dec` dec operations (where n_dec <= n_inc) leaves rc = n_inc - n_dec.
/// Dealloc never fires during the sequence because rc > 0 at each dec point.
#[kani::proof]
#[kani::unwind(12)]
fn verify_rc_arbitrary_inc_dec_sequence() {
    let n_inc: u32 = kani::any();
    let n_dec: u32 = kani::any();
    kani::assume(n_inc > 0 && n_inc <= 5);
    kani::assume(n_dec > 0 && n_dec <= n_inc);

    let mut rc: u32 = 0;

    // Increment phase
    for _ in 0..n_inc {
        rc = rc.wrapping_add(1);
    }
    assert_eq!(rc, n_inc, "after inc phase, rc equals n_inc");

    // Decrement phase — each dec sees old > 0 (no dealloc)
    for _ in 0..n_dec {
        let old = rc;
        assert!(old > 0, "dec during sequence must see non-zero rc");
        rc = rc.wrapping_sub(1);
    }

    assert_eq!(
        rc,
        n_inc - n_dec,
        "final rc must equal inc count minus dec count"
    );
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 4. Closure apply model
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Verify apply_n case classification is exhaustive and non-overlapping.
///
/// Property: For any arity, num_fixed, n_args, exactly one case applies.
#[kani::proof]
#[kani::unwind(1)]
fn verify_apply_case_classification() {
    let arity: u16 = kani::any();
    let num_fixed: u16 = kani::any();
    let n_args: usize = kani::any();

    kani::assume(arity > 0 && arity <= 16);
    kani::assume(num_fixed < arity);
    kani::assume(n_args > 0 && n_args <= 16);

    let remaining = (arity - num_fixed) as usize;
    assert!(remaining > 0, "remaining must be > 0 (INV-1 + INV-2)");

    let under = n_args < remaining;
    let exact = n_args == remaining;
    let over = n_args > remaining;

    assert!(
        (under as u8) + (exact as u8) + (over as u8) == 1,
        "exactly one apply case must hold"
    );
}

/// Verify apply_n loop termination model.
///
/// Property: Each iteration consumes at least 1 argument (remaining >= 1).
#[kani::proof]
#[kani::unwind(6)]
fn verify_apply_loop_termination() {
    let n_args: usize = kani::any();
    kani::assume(n_args > 0 && n_args <= 4);

    let arity1: u16 = kani::any();
    let num_fixed1: u16 = kani::any();
    kani::assume(arity1 > 0 && arity1 <= 16);
    kani::assume(num_fixed1 < arity1);

    let remaining1 = (arity1 - num_fixed1) as usize;
    let mut offset: usize = 0;
    let mut iterations: usize = 0;

    if n_args < remaining1 {
        // Under-saturation: extend and return
    } else {
        offset += remaining1;
        iterations += 1;

        if offset < n_args {
            let arity2: u16 = kani::any();
            let num_fixed2: u16 = kani::any();
            kani::assume(arity2 > 0 && arity2 <= 16);
            kani::assume(num_fixed2 < arity2);

            let remaining2 = (arity2 - num_fixed2) as usize;
            let n_left = n_args - offset;

            if n_left <= remaining2 {
                iterations += 1;
            } else {
                let _ = remaining2;
                iterations += 1;
            }
        }
    }

    assert!(iterations <= n_args, "iterations bounded by arg count");
}

/// Verify closure invariant: arity > num_fixed (remaining > 0).
///
/// Violated invariant causes infinite loop in apply_n.
#[kani::proof]
#[kani::unwind(1)]
fn verify_closure_remaining_positive() {
    let arity: u16 = kani::any();
    let num_fixed: u16 = kani::any();

    kani::assume(arity > 0);
    kani::assume(num_fixed < arity);

    let remaining = arity - num_fixed;
    assert!(remaining > 0, "remaining must always be positive");
    assert!(remaining <= arity, "remaining <= arity");
}

/// Verify extend_closure produces a valid closure (INV-1, INV-2 preserved).
#[kani::proof]
#[kani::unwind(1)]
fn verify_extend_preserves_invariants() {
    let arity: u16 = kani::any();
    let num_fixed: u16 = kani::any();
    let n_new: u16 = kani::any();

    kani::assume(arity > 0 && arity <= 16);
    kani::assume(num_fixed < arity);
    let remaining = arity - num_fixed;
    kani::assume(n_new > 0 && n_new < remaining);

    let new_fixed = num_fixed + n_new;

    assert!(arity > 0, "INV-1: arity > 0 preserved");
    assert!(new_fixed < arity, "INV-2: num_fixed < arity preserved");
    assert!(
        (arity - new_fixed) > 0,
        "remaining still positive after extend"
    );
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 5. Reset/reuse model
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Verify that size-equal ctor layouts can have different pointer field counts.
///
/// Property: When ctor_layout(n1,s1).size() == ctor_layout(n2,s2).size() but
/// n1 != n2, the layouts have different pointer field counts. A size-only
/// reuse check would allow reusing a slot where the pointer/scalar boundary
/// is at the wrong offset, causing the GC to interpret scalar bytes as
/// pointers (or vice versa).
///
/// The layout formula is: 8 + n*8 + s. Collision when n1*8 + s1 == n2*8 + s2.
/// Example: (n=1,s=0) and (n=0,s=8) both produce size 16, but the first has
/// 1 pointer field and the second has 0 — reuse would corrupt the heap.
#[kani::proof]
#[kani::unwind(1)]
fn verify_reuse_size_match_field_count_mismatch() {
    let n1: u8 = kani::any();
    let s1: u8 = kani::any();
    let n2: u8 = kani::any();
    let s2: u8 = kani::any();

    // Restrict to small values for tractability
    kani::assume(n1 <= 4 && n2 <= 4);
    kani::assume(s1 <= 32 && s2 <= 32);

    let l1 = ctor_layout(n1, s1);
    let l2 = ctor_layout(n2, s2);

    // When sizes match AND pointer field counts differ, reuse is unsafe.
    // This verifies the property that motivates checking BOTH num_objs AND
    // scalar_sz in reuse() — size equality alone is insufficient.
    if l1.size() == l2.size() && n1 != n2 {
        // Size-equal layouts with different pointer counts: unsafe to reuse.
        // The difference in scalar_sz compensates for the pointer count change.
        // Verify: the scalar sizes MUST differ to achieve size equality with
        // different pointer counts (since ptr_sz = 8 and scalar changes by 1).
        assert_ne!(
            s1, s2,
            "size-equal layouts with different num_objs must have different scalar_sz"
        );
    }
}

/// Verify reset on Closure returns null (layout incompatible with Ctor reuse).
///
/// Property: Closure layout always differs from Ctor layout by 16 bytes.
#[kani::proof]
#[kani::unwind(1)]
fn verify_closure_reset_always_null() {
    let num_fixed: u16 = kani::any();
    kani::assume(num_fixed <= 16);

    let cl = closure_layout(num_fixed);
    let ctor = ctor_layout(num_fixed as u8, 0);

    if num_fixed <= 255 {
        // Closure: 24 + num_fixed * 8, Ctor: 8 + num_fixed * 8
        // Difference is always 16 (sizeof(LeanClosure) - sizeof(ObjHeader))
        assert_eq!(
            cl.size() - ctor.size(),
            16,
            "closure layout always 16 bytes larger than ctor with same field count"
        );
    }
}
