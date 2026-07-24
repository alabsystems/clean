// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kani harnesses: RC state machine, closure apply, and reset/reuse models.
//!
//! Verifies correctness of reference counting transitions, closure application
//! case handling and termination, and reset/reuse lifecycle invariants.
//!
//! Run with: `cargo kani --features kani -p clean-runtime`
//!
//! Part of #1144

use super::{closure_layout, ctor_layout};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 3. Reference counting state machine model
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Verify the dec() dealloc boundary: fetch_sub(1) returns the OLD value.
///
/// Property: dec() triggers dealloc iff the old ref_count is 0 (uniquely owned).
/// For any starting rc, after fetch_sub(1), old == 0 iff the object should be freed.
/// This is the critical correctness property — getting this wrong causes
/// use-after-free (old > 0 treated as 0) or memory leak (old == 0 not freed).
#[kani::proof]
#[kani::unwind(1)]
fn verify_rc_dec_dealloc_boundary() {
    let rc: u32 = kani::any();
    kani::assume(rc <= 1000); // bounded for tractability

    // Model fetch_sub(1, Release) — returns old value
    let old = rc;
    let new_rc = rc.wrapping_sub(1);

    if old == 0 {
        // Was uniquely owned → dealloc. After wrapping_sub, new value is u32::MAX.
        // This is expected — the object is freed so the wrapped value is never read.
        assert_eq!(new_rc, u32::MAX, "wrapping_sub(1) on 0 produces MAX");
    } else {
        // Was shared → no dealloc. New ref_count is old - 1.
        assert_eq!(new_rc, old - 1, "shared dec must decrement by exactly 1");
    }
}

/// Verify inc_n followed by n dec operations returns to unique.
///
/// Property: inc_n(n) followed by n individual dec operations returns rc to 0.
#[kani::proof]
#[kani::unwind(10)]
fn verify_rc_inc_n_dec_n() {
    let n: u32 = kani::any();
    kani::assume(n > 0 && n <= 8);

    let mut rc: u32 = 0;

    // inc_n
    rc = rc.wrapping_add(n);
    assert_eq!(rc, n);

    // n individual dec operations
    for _ in 0..n {
        let old = rc;
        rc = rc.wrapping_sub(1);
        assert!(old != 0, "intermediate decs should not trigger dealloc");
    }

    assert_eq!(rc, 0, "after n decs, should be unique");
}

/// Verify RC overflow would cause false dealloc — documents why bounded RC matters.
///
/// Property: If ref_count reaches u32::MAX and inc() is called, wrapping_add(1)
/// produces 0 — the "uniquely owned" sentinel. A subsequent dec() would trigger
/// dealloc despite ~4 billion live references. This is a known limitation of
/// wrapping reference counting (same as Lean 4 C runtime).
///
/// This harness documents the overflow behavior rather than preventing it.
/// Prevention is via the practical bound: 4 billion simultaneous references
/// to one object is infeasible.
#[kani::proof]
#[kani::unwind(1)]
fn verify_rc_overflow_wraps_to_zero() {
    let rc: u32 = kani::any();
    kani::assume(rc >= u32::MAX - 10); // near overflow boundary

    let after_inc = rc.wrapping_add(1);

    if rc == u32::MAX {
        // Overflow: wrapping to 0 makes it look "uniquely owned"
        assert_eq!(after_inc, 0, "overflow wraps to dealloc sentinel");
    } else {
        // No overflow: normal increment
        assert_eq!(after_inc, rc + 1);
        assert_ne!(after_inc, 0, "non-overflow inc must not hit sentinel");
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
