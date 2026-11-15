// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sticky (frozen) reference counts in both Rust runtime copies (plan item
//! `runtime-rc-sticky`; Lean v4.35.0 `lean.h` 640-765, lean4#14838/#15241).
//!
//! The same rows run on `runtime::{lean_inc, lean_inc_n, lean_dec,
//! lean_is_unique, lean_reset}` (the `--emit rust` lane) and on
//! `native::{inc, inc_n, dec, is_unique, reset}`. The C copy has its own
//! harness (`tests/c_header_rc_sticky.rs`). Counts are refs-1; the band
//! thresholds are Lean's widths measured from the u32 wrap point.
//!
//! The extreme frozen row here is 0xFFFF_FFFE, not `u32::MAX`: a drop at
//! `u32::MAX` keeps its debug-build `debug_assert` (a heuristic for a second
//! drop of a freed cell), pinned by the two `should_panic` tests beside the
//! copies. An increment at `u32::MAX` is asserted.

use std::sync::atomic::Ordering;

use crate::object_model::{lean_box, CleanExternalClass, LeanObjPtr, TaskObj, ThunkObj};
use crate::rc_core::{
    check_drop_property, check_inc_property, RC_INC_MAX, RC_STICKY, RC_STICKY_DROP,
};
use crate::runtime::{
    alloc_array, alloc_ctor, alloc_external, alloc_task, alloc_thunk, array_push, closure_apply,
    lean_dec, lean_inc, lean_inc_n, lean_is_unique, lean_reset,
};

const DROP: u32 = 0xE000_0000;
const STICKY: u32 = 0xF000_0000;
const INC_MAX: u32 = 0x1_0000;

/// One Rust copy of the reference-count operations.
struct RcCopy {
    inc: fn(LeanObjPtr),
    inc_n: fn(LeanObjPtr, usize),
    dec: fn(LeanObjPtr),
    is_unique: fn(LeanObjPtr) -> bool,
    reset: fn(LeanObjPtr) -> LeanObjPtr,
}

const RUNTIME: RcCopy = RcCopy {
    inc: lean_inc,
    inc_n: lean_inc_n,
    dec: lean_dec,
    is_unique: lean_is_unique,
    reset: lean_reset,
};

// SAFETY (all five native wrappers): every object passed in these tests is a
// live runtime allocation or a tagged scalar, which is native's contract.
fn native_inc(o: LeanObjPtr) {
    // SAFETY: see the note above the native wrappers.
    unsafe { crate::native::inc(o) }
}
fn native_inc_n(o: LeanObjPtr, n: usize) {
    // SAFETY: see the note above the native wrappers.
    unsafe { crate::native::inc_n(o, n) }
}
fn native_dec(o: LeanObjPtr) {
    // SAFETY: see the note above the native wrappers.
    unsafe { crate::native::dec(o) }
}
fn native_is_unique(o: LeanObjPtr) -> bool {
    // SAFETY: see the note above the native wrappers.
    unsafe { crate::native::is_unique(o) }
}
fn native_reset(o: LeanObjPtr) -> LeanObjPtr {
    // SAFETY: see the note above the native wrappers.
    unsafe { crate::native::reset(o) }
}

const NATIVE: RcCopy = RcCopy {
    inc: native_inc,
    inc_n: native_inc_n,
    dec: native_dec,
    is_unique: native_is_unique,
    reset: native_reset,
};

fn rc(o: LeanObjPtr) -> u32 {
    // SAFETY: `o` is a live heap object of the calling test.
    unsafe { (*o).header.ref_count.load(Ordering::Relaxed) }
}

fn set_rc(o: LeanObjPtr, v: u32) {
    // SAFETY: `o` is a live heap object of the calling test.
    unsafe { (*o).header.ref_count.store(v, Ordering::Relaxed) }
}

fn tag(o: LeanObjPtr) -> u8 {
    // SAFETY: `o` is a live heap object of the calling test.
    unsafe { (*o).header.tag }
}

fn leaf(t: u8) -> LeanObjPtr {
    alloc_ctor(t, &[])
}

/// Free an object the test set a count on: make it exclusive and drop it.
fn release(c: &RcCopy, o: LeanObjPtr) {
    set_rc(o, 0);
    (c.dec)(o);
}

/// Generate the runtime and native `#[test]` for one per-copy check.
macro_rules! both_copies {
    ($check:ident, $runtime:ident, $native:ident) => {
        #[test]
        fn $runtime() {
            $check(&RUNTIME);
        }
        #[test]
        fn $native() {
            $check(&NATIVE);
        }
    };
}

// -- The exit criterion: (a), (b), (c), plus reset and inc_n past u32 --

fn check_inc_at_u32_max_stays_shared(c: &RcCopy) {
    let o = leaf(7);
    set_rc(o, u32::MAX);
    (c.inc)(o);
    assert_eq!(rc(o), u32::MAX, "an increment at u32::MAX must not wrap");
    assert!(!(c.is_unique)(o), "a frozen cell is never exclusive");
    release(c, o);
}
both_copies!(
    check_inc_at_u32_max_stays_shared,
    test_rc_sticky_runtime_inc_at_u32_max_stays_shared,
    test_rc_sticky_native_inc_at_u32_max_stays_shared
);

fn check_drops_in_band_leave_count(c: &RcCopy) {
    let o = leaf(7);
    set_rc(o, 0xF800_0000);
    for _ in 0..(1u32 << 20) {
        (c.dec)(o);
    }
    assert_eq!(rc(o), 0xF800_0000, "drops inside the band are no-ops");
    assert_eq!(tag(o), 7, "the frozen cell is still live");
    release(c, o);
}
both_copies!(
    check_drops_in_band_leave_count,
    test_rc_sticky_runtime_drops_in_band_leave_count,
    test_rc_sticky_native_drops_in_band_leave_count
);

fn check_cascade_skips_frozen_child(c: &RcCopy) {
    let child = leaf(3);
    set_rc(child, 0xF800_0000);
    (c.dec)(alloc_ctor(1, &[child]));
    assert_eq!(
        rc(child),
        0xF800_0000,
        "the cascade must not adjust a frozen child"
    );
    assert_eq!(tag(child), 3);
    release(c, child);
}
both_copies!(
    check_cascade_skips_frozen_child,
    test_rc_sticky_runtime_cascade_skips_frozen_child,
    test_rc_sticky_native_cascade_skips_frozen_child
);

fn check_reset_frozen_declines_reuse(c: &RcCopy) {
    // Two increments from 0xFFFF_FFFE wrapped to 0 before the band, so reset
    // dropped the child (5 -> 4) and handed back a shared cell.
    let child = leaf(2);
    set_rc(child, 5);
    let o = alloc_ctor(1, &[child]);
    set_rc(o, 0xFFFF_FFFE);
    (c.inc)(o);
    (c.inc)(o);
    let r = (c.reset)(o);
    assert!(r.is_null(), "reset of a frozen cell must decline reuse");
    assert_eq!(rc(o), 0xFFFF_FFFE);
    assert_eq!(
        rc(child),
        5,
        "reset of a frozen cell must not drop its children"
    );
    set_rc(child, 0);
    release(c, o);
}
both_copies!(
    check_reset_frozen_declines_reuse,
    test_rc_sticky_runtime_reset_frozen_declines_reuse,
    test_rc_sticky_native_reset_frozen_declines_reuse
);

fn check_inc_n_past_u32_freezes(c: &RcCopy) {
    let o = leaf(0);
    (c.inc_n)(o, (1usize << 32) + 1);
    let after = rc(o);
    assert!(
        (STICKY..STICKY + INC_MAX).contains(&after),
        "inc_n(2^32 + 1) from 0 must freeze in [STICKY, STICKY + INC_MAX), got {after:#x}"
    );
    assert!(!(c.is_unique)(o));
    release(c, o);
}
both_copies!(
    check_inc_n_past_u32_freezes,
    test_rc_sticky_runtime_inc_n_past_u32_freezes,
    test_rc_sticky_native_inc_n_past_u32_freezes
);

// -- Lean's tables (rc_sticky.c g_never_freed / g_never_incremented), mapped --

const NEVER_FREED: [u32; 7] = [
    DROP,
    DROP + 1,
    STICKY - 1,
    STICKY,
    STICKY + 1,
    0xF800_0000,
    0xFFFF_FFFE,
];

fn check_never_freed_table(c: &RcCopy) {
    for v in NEVER_FREED {
        let o = leaf(1);
        set_rc(o, v);
        (c.dec)(o);
        assert_eq!(rc(o), v, "a drop at {v:#x} must leave the count");
        release(c, o);
        let child = leaf(2);
        set_rc(child, v);
        (c.dec)(alloc_ctor(0, &[child]));
        assert_eq!(
            rc(child),
            v,
            "a cascade over a child at {v:#x} must leave it"
        );
        release(c, child);
    }
}
both_copies!(
    check_never_freed_table,
    test_rc_sticky_runtime_never_freed_table,
    test_rc_sticky_native_never_freed_table
);

fn check_never_incremented_table(c: &RcCopy) {
    let ns = [1, INC_MAX as usize, INC_MAX as usize + 1, 1usize << 40];
    for v in [STICKY, STICKY + 1, 0xF800_0000, 0xFFFF_FFFE, u32::MAX] {
        let o = leaf(1);
        set_rc(o, v);
        (c.inc)(o);
        assert_eq!(rc(o), v, "inc at {v:#x}");
        for n in ns {
            set_rc(o, v);
            (c.inc_n)(o, n);
            assert_eq!(rc(o), v, "inc_n({n:#x}) at {v:#x}");
        }
        release(c, o);
    }
}
both_copies!(
    check_never_incremented_table,
    test_rc_sticky_runtime_never_incremented_table,
    test_rc_sticky_native_never_incremented_table
);

fn check_band_entry(c: &RcCopy) {
    let o = leaf(1);
    set_rc(o, STICKY - 1);
    (c.inc)(o);
    assert_eq!(rc(o), STICKY, "an increment enters the band");
    (c.inc)(o);
    assert_eq!(rc(o), STICKY, "and stops there");
    set_rc(o, DROP);
    (c.inc)(o);
    assert_eq!(rc(o), DROP + 1, "a count at DROP still takes increments");
    (c.dec)(o);
    assert_eq!(rc(o), DROP + 1, "but no drop");
    release(c, o);
}
both_copies!(
    check_band_entry,
    test_rc_sticky_runtime_band_entry,
    test_rc_sticky_native_band_entry
);

/// Negative control, green before and after: below the band every count
/// moves by exactly the amount asked.
fn check_below_band_exact(c: &RcCopy) {
    let o = leaf(1);
    (c.inc)(o);
    assert_eq!(rc(o), 1);
    (c.dec)(o);
    assert_eq!(rc(o), 0);
    assert!((c.is_unique)(o));
    set_rc(o, 0x7FFF_FFFF);
    (c.inc)(o);
    assert_eq!(rc(o), 0x8000_0000);
    (c.dec)(o);
    assert_eq!(rc(o), 0x7FFF_FFFF);
    set_rc(o, 0);
    (c.inc_n)(o, 3);
    assert_eq!(rc(o), 3);
    set_rc(o, DROP - 1);
    (c.dec)(o);
    assert_eq!(rc(o), DROP - 2);
    set_rc(o, 0);
    (c.inc_n)(o, INC_MAX as usize + 1);
    assert_eq!(rc(o), INC_MAX + 1, "the cold path applies every increment");
    release(c, o);
}
both_copies!(
    check_below_band_exact,
    test_rc_sticky_runtime_below_band_exact_controls,
    test_rc_sticky_native_below_band_exact_controls
);

// -- The deletion worklist: every kind, shared children, the spill --

/// A witness the test holds; each holder adds one reference, so its count
/// says how many holders are still alive.
fn holder_of(c: &RcCopy, w: LeanObjPtr) -> LeanObjPtr {
    (c.inc)(w);
    alloc_ctor(1, &[w])
}

fn check_kinds_skip_frozen_children(c: &RcCopy) {
    let w = leaf(9);
    // Array elements.
    let frozen = leaf(5);
    set_rc(frozen, 0xF800_0000);
    // SAFETY: `alloc_array` returns a live array; `array_push` takes the
    // caller's reference to each element.
    let arr = unsafe {
        let a = array_push(alloc_array(3), frozen);
        let a = array_push(a, holder_of(c, w));
        array_push(a, lean_box(7))
    };
    (c.dec)(arr);
    assert_eq!(rc(frozen), 0xF800_0000, "array: frozen element untouched");
    assert_eq!(rc(w), 0, "array: exclusive element freed");
    // Thunk closure (frozen) and value (exclusive).
    // SAFETY: `alloc_thunk` returns a live thunk whose `value` field this
    // test owns until the drop.
    let thunk = unsafe {
        let t = alloc_thunk(frozen);
        (*(t as *mut ThunkObj)).value = holder_of(c, w);
        t
    };
    (c.dec)(thunk);
    assert_eq!(rc(frozen), 0xF800_0000, "thunk: frozen closure untouched");
    assert_eq!(rc(w), 0, "thunk: exclusive value freed");
    // Task values.
    for (value, frozen_value) in [(frozen, true), (holder_of(c, w), false)] {
        // SAFETY: `alloc_task` returns a live task whose `value` field this
        // test owns until the drop.
        let task = unsafe {
            let t = alloc_task(std::ptr::null_mut());
            (*(t as *mut TaskObj)).value = value;
            t
        };
        (c.dec)(task);
        if frozen_value {
            assert_eq!(rc(frozen), 0xF800_0000, "task: frozen value untouched");
        } else {
            assert_eq!(rc(w), 0, "task: exclusive value freed");
        }
    }
    // External foreach hands its child to the drop visitor.
    unsafe fn visit(data: *mut (), visitor: LeanObjPtr) {
        // `data` is the frozen child this test stored; the visitor is the
        // runtime's drop closure, borrowed.
        closure_apply(visitor, &[data as LeanObjPtr]);
    }
    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: None,
        foreach: Some(visit),
    };
    // SAFETY: CLASS outlives the object; `data` is a live object.
    let ext = unsafe { alloc_external(&CLASS, frozen as *mut ()) };
    (c.dec)(ext);
    assert_eq!(rc(frozen), 0xF800_0000, "external: frozen child untouched");
    release(c, frozen);
    (c.dec)(w);
}
both_copies!(
    check_kinds_skip_frozen_children,
    test_rc_sticky_runtime_kinds_skip_frozen_children,
    test_rc_sticky_native_kinds_skip_frozen_children
);

fn check_shared_children_free_once(c: &RcCopy) {
    let w = leaf(9);
    // One child in two fields of one dying parent.
    let c1 = holder_of(c, w);
    (c.inc)(c1);
    (c.dec)(alloc_ctor(0, &[c1, c1]));
    assert_eq!(rc(w), 0, "a child in two fields is freed once");
    // One child under two dying parents.
    let c2 = holder_of(c, w);
    (c.inc)(c2);
    let p1 = alloc_ctor(2, &[c2]);
    let p2 = alloc_ctor(2, &[c2]);
    (c.dec)(alloc_ctor(3, &[p1, p2]));
    assert_eq!(rc(w), 0, "a child under two parents is freed once");
    // Lean's shared-child control: a surviving reference keeps it live.
    let c3 = leaf(4);
    set_rc(c3, 1);
    (c.dec)(alloc_ctor(0, &[c3]));
    assert_eq!(
        (rc(c3), tag(c3)),
        (0, 4),
        "a shared child keeps its other reference"
    );
    (c.dec)(c3);
    (c.dec)(w);
}
both_copies!(
    check_shared_children_free_once,
    test_rc_sticky_runtime_shared_children_free_once,
    test_rc_sticky_native_shared_children_free_once
);

fn check_many_pending_children(c: &RcCopy) {
    // 200 pending non-leaf children in one ctor and 1000 in one array: both
    // overflow any fixed local buffer. Every holder is freed exactly once.
    let w = leaf(9);
    let kids: Vec<LeanObjPtr> = (0..200).map(|_| holder_of(c, w)).collect();
    assert_eq!(rc(w), 200);
    (c.dec)(alloc_ctor(0, &kids));
    assert_eq!(rc(w), 0, "ctor with 200 pending children");
    let mut arr = alloc_array(1000);
    for _ in 0..1000 {
        // SAFETY: `arr` is a live, exclusive array; push takes the reference.
        arr = unsafe { array_push(arr, holder_of(c, w)) };
    }
    assert_eq!(rc(w), 1000);
    (c.dec)(arr);
    assert_eq!(rc(w), 0, "array with 1000 pending elements");
    (c.dec)(w);
}
both_copies!(
    check_many_pending_children,
    test_rc_sticky_runtime_many_pending_children,
    test_rc_sticky_native_many_pending_children
);

// -- The shared core: Lean's widths and the cell properties --

#[test]
fn test_rc_sticky_band_constants_match_lean_widths() {
    assert_eq!(
        (RC_STICKY_DROP, RC_STICKY, RC_INC_MAX),
        (DROP, STICKY, INC_MAX as usize)
    );
    assert_eq!(RC_STICKY - RC_STICKY_DROP, 1 << 28, "band width (Lean's)");
    assert_eq!(
        0u32.wrapping_sub(RC_STICKY),
        1 << 28,
        "room past RC_STICKY (Lean's)"
    );
}

/// Counts at every boundary the contract names.
const SWEEP_COUNTS: [u32; 25] = [
    0,
    1,
    2,
    INC_MAX - 1,
    INC_MAX,
    INC_MAX + 1,
    0x7FFF_FFFF,
    0x8000_0000,
    DROP - 2,
    DROP - 1,
    DROP,
    DROP + 1,
    DROP + 2,
    STICKY - INC_MAX - 1,
    STICKY - INC_MAX,
    STICKY - 2,
    STICKY - 1,
    STICKY,
    STICKY + 1,
    STICKY + 2,
    STICKY + INC_MAX,
    0xF800_0000,
    0xFFFF_FFFD,
    0xFFFF_FFFE,
    u32::MAX,
];

#[test]
fn test_rc_core_inc_property_boundary_sweep() {
    let m = INC_MAX as usize;
    let ns = [
        0,
        1,
        2,
        m - 1,
        m,
        m + 1,
        4 * m,
        (1 << 32) - 1,
        1 << 32,
        (1 << 32) + 1,
        usize::MAX,
    ];
    for rc in SWEEP_COUNTS {
        for n in ns {
            check_inc_property(rc, n);
        }
    }
}

#[test]
fn test_rc_core_drop_property_boundary_sweep() {
    // Not at u32::MAX: there the debug-build heuristic asserts (pinned by
    // the `should_panic` tests of both copies).
    for rc in SWEEP_COUNTS.into_iter().filter(|&rc| rc != u32::MAX) {
        check_drop_property(rc);
    }
}
