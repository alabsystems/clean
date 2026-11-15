// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reference counting shared by both Rust runtime copies: `runtime::refcount`
//! (the `--emit rust` lane) and `native::rc` (the native facade) are thin
//! names over this module. The C copy is `clean_runtime.h` /
//! `clean_runtime.c`, with the same contract.
//!
//! Sticky counts (Lean v4.35.0 `lean.h` 640-700, lean4#14838/#15241) in
//! Clean's encoding: `ref_count` stores refs-1, 0 is exclusive.
//!
//! * At or above [`RC_STICKY_DROP`] a count is frozen: no drop adjusts or
//!   frees it, so the object leaks instead of being freed while live.
//! * At or above [`RC_STICKY`] no increment adjusts it either.
//! * An increment of more than [`RC_INC_MAX`] runs Lean's chunked
//!   `lean_inc_ref_huge_n`, so it applies whole or leaves the count frozen.
//!
//! The band widths are Lean's, measured from the u32 wrap point: 2^28 between
//! the thresholds and 2^28 above `RC_STICKY`. They bound the relaxed pre-load
//! race Lean documents: a thread whose load predates the count entering the
//! band still commits its adjustment, and lifting a frozen count back out (or
//! wrapping it) takes that many such stale adjustments in flight at once.
//!
//! A dying object is freed through an explicit worklist that never adjusts a
//! frozen child, so a graph of any depth frees in constant stack (lean4#15241).

use std::alloc;
use std::mem::size_of;
use std::sync::atomic::{fence, AtomicU32, Ordering};

use crate::object_model::{
    alloc_closure_obj, is_scalar, lean_box, lean_panic, obj_child_count, obj_child_ptrs,
    object_layout, ArrayObj, ExternalObj, LeanObjPtr, ObjKind, TaskObj, ThunkObj,
};

/// Drops stop at or above this count (Lean `LEAN_RC_STICKY_DROP`).
pub(crate) const RC_STICKY_DROP: u32 = 0xE000_0000;
/// Increments stop at or above this count too (Lean `LEAN_RC_STICKY`).
pub(crate) const RC_STICKY: u32 = 0xF000_0000;
/// The largest increment applied in one step (Lean `LEAN_RC_INC_MAX`).
pub(crate) const RC_INC_MAX: usize = 0x1_0000;

/// What one dropped reference did to a count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DropOutcome {
    /// Other references remain; the count went down by one.
    Live,
    /// The count is frozen and was left unchanged.
    Frozen,
    /// That was the last reference: the caller frees the object.
    Last,
}

/// Add `n` references to a count.
#[inline]
pub(crate) fn inc_cell(rc: &AtomicU32, n: usize) {
    if n > RC_INC_MAX {
        inc_huge_cell(rc, n);
    } else if rc.load(Ordering::Relaxed) < RC_STICKY {
        // `n <= RC_INC_MAX`, so the cast is exact, and from below RC_STICKY
        // the count reaches at most 0xF000_FFFF: it never wraps.
        rc.fetch_add(n as u32, Ordering::Relaxed);
    }
}

/// Lean's `lean_inc_ref_huge_n`: ordinary steps of at most [`RC_INC_MAX`],
/// re-reading the count so the loop stops once it is frozen.
#[cold]
#[inline(never)]
fn inc_huge_cell(rc: &AtomicU32, mut n: usize) {
    while n > 0 && rc.load(Ordering::Relaxed) < RC_STICKY {
        let step = n.min(RC_INC_MAX);
        rc.fetch_add(step as u32, Ordering::Relaxed);
        n -= step;
    }
}

/// Drop one reference from a count. Release on the decrement, and an acquire
/// fence before reporting [`DropOutcome::Last`], so every write of a former
/// holder is visible to the code that frees.
#[inline]
pub(crate) fn drop_cell(rc: &AtomicU32) -> DropOutcome {
    let current = rc.load(Ordering::Relaxed);
    // Sequentially a count stops at 0xF000_FFFF; u32::MAX is what the last
    // drop leaves on a cell it frees. A debug-build heuristic for a second
    // drop of a freed cell, ahead of the band check.
    debug_assert_ne!(
        current,
        u32::MAX,
        "dec: ref_count wrapped to u32::MAX before decrement — likely prior underflow"
    );
    if current >= RC_STICKY_DROP {
        return DropOutcome::Frozen;
    }
    if rc.fetch_sub(1, Ordering::Release) != 0 {
        return DropOutcome::Live;
    }
    fence(Ordering::Acquire);
    DropOutcome::Last
}

/// Whether a count says exclusive. A frozen count is never 0.
#[inline]
pub(crate) fn is_exclusive_cell(rc: &AtomicU32) -> bool {
    rc.load(Ordering::Relaxed) == 0
}

/// Add `n` references to an object. No-op for scalars.
#[inline]
pub(crate) fn inc_n(o: LeanObjPtr, n: usize) {
    if !is_scalar(o) {
        // SAFETY: a non-scalar object pointer is a live heap object (the
        // runtime's contract for every RC entry point).
        inc_cell(unsafe { &(*o).header.ref_count }, n);
    }
}

/// Whether the caller holds the only reference. Scalars count as exclusive.
/// Relaxed suffices: a false "shared" only costs an allocation, and a false
/// "exclusive" cannot happen while the caller holds a reference (Lean
/// `lean_is_exclusive`).
#[inline]
pub(crate) fn is_exclusive(o: LeanObjPtr) -> bool {
    // SAFETY: a non-scalar object pointer is a live heap object.
    is_scalar(o) || is_exclusive_cell(unsafe { &(*o).header.ref_count })
}

/// Drop one reference; on the last one free the object and everything that
/// reference kept alive. No-op for scalars and frozen counts.
#[inline]
pub(crate) fn dec(o: LeanObjPtr) {
    if is_scalar(o) {
        return;
    }
    // SAFETY: a non-scalar object pointer is a live heap object.
    if drop_cell(unsafe { &(*o).header.ref_count }) == DropOutcome::Last {
        // SAFETY: the caller's reference was the last, so this thread owns
        // `o` and nothing reads it again.
        unsafe { release(o) }
    }
}

/// Pending dying objects held on the stack; a `Vec` takes the rest, so
/// freeing allocates only when more than this many are pending at once.
const LOCAL_WORKLIST: usize = 32;

struct Worklist {
    local: [LeanObjPtr; LOCAL_WORKLIST],
    len: usize,
    spill: Vec<LeanObjPtr>,
}

impl Worklist {
    fn new() -> Self {
        Self {
            local: [std::ptr::null_mut(); LOCAL_WORKLIST],
            len: 0,
            spill: Vec::new(),
        }
    }

    fn push(&mut self, o: LeanObjPtr) {
        if self.len < LOCAL_WORKLIST {
            self.local[self.len] = o;
            self.len += 1;
        } else {
            self.spill.push(o);
        }
    }

    fn pop(&mut self) -> Option<LeanObjPtr> {
        if let Some(o) = self.spill.pop() {
            return Some(o);
        }
        self.len = self.len.checked_sub(1)?;
        Some(self.local[self.len])
    }
}

/// Free `first`, whose last reference was just dropped, and every child whose
/// last reference that frees, through an explicit worklist. No recursion over
/// data, so a chain of any shape and depth frees in constant stack. A frozen
/// child is never adjusted or freed; a dying child with no children is freed
/// at once. An External's `foreach` visitor re-enters [`dec`], so recursion
/// is bounded by External nesting, never by data depth.
///
/// # Safety
///
/// `first` is a live heap object whose last reference the caller dropped
/// ([`drop_cell`] returned [`DropOutcome::Last`]); nothing reads it again.
unsafe fn release(first: LeanObjPtr) {
    // SAFETY: `first` is live and owned (the caller's contract).
    if unsafe { is_leaf(first) } {
        // SAFETY: as above; a leaf owns nothing but its own memory.
        unsafe { alloc::dealloc(first as *mut u8, object_layout(first)) };
        return;
    }
    let mut todo = Worklist::new();
    let mut o = first;
    loop {
        // SAFETY: `o` is `first` or was pushed after its last reference was
        // dropped, so this loop owns it. Its children are read (and an
        // External finalized) before its own memory is freed, with the
        // layout `object_layout` reads from the same live header.
        unsafe {
            drop_children(o, &mut todo);
            alloc::dealloc(o as *mut u8, object_layout(o));
        }
        match todo.pop() {
            Some(next) => o = next,
            None => return,
        }
    }
}

/// Drop each child reference of the dying `o`, queueing the children whose
/// last reference that was.
///
/// # Safety
///
/// `o` is a live heap object this thread owns (its last reference dropped).
unsafe fn drop_children(o: LeanObjPtr, todo: &mut Worklist) {
    // SAFETY: `o` is live and owned, so its header and the child slots its
    // kind defines are readable. Extended kinds (Part of #2250, #2244,
    // #2241) store children in struct fields, not the header's pointer array.
    unsafe {
        let kind = ObjKind::from_u8((*o).header.kind);
        if !matches!(kind, ObjKind::Ctor | ObjKind::Closure | ObjKind::Str)
            && (*o).header.num_objs != 0
        {
            lean_panic("lean_dec: extended type with num_objs > 0");
        }
        match kind {
            ObjKind::Ctor | ObjKind::Closure | ObjKind::Str => {
                let children = obj_child_ptrs(o);
                for i in 0..obj_child_count(o) {
                    drop_child(*children.add(i), todo);
                }
            }
            ObjKind::Array => {
                let data = (o as *const u8).add(size_of::<ArrayObj>()) as *const LeanObjPtr;
                for i in 0..(*(o as *const ArrayObj)).size {
                    drop_child(*data.add(i), todo);
                }
            }
            ObjKind::Thunk => {
                let thunk = o as *const ThunkObj;
                // The closure if unforced, the value if forced (Lean's
                // lean_thunk_object dealloc).
                for child in [(*thunk).closure, (*thunk).value] {
                    if !child.is_null() {
                        drop_child(child, todo);
                    }
                }
            }
            ObjKind::Task => {
                let value = (*(o as *const TaskObj)).value;
                if !value.is_null() {
                    drop_child(value, todo);
                }
            }
            ObjKind::External => external_cleanup(o),
        }
    }
}

/// A Ctor, Closure or Str with no children: freeing it is freeing its memory.
///
/// # Safety
///
/// `o` is a live heap object.
unsafe fn is_leaf(o: LeanObjPtr) -> bool {
    // SAFETY: `o` is live, so its header (and a Closure's `num_fixed`) is
    // readable.
    unsafe {
        matches!(
            ObjKind::from_u8((*o).header.kind),
            ObjKind::Ctor | ObjKind::Closure | ObjKind::Str
        ) && obj_child_count(o) == 0
    }
}

/// Drop one reference of a dying parent's child.
///
/// # Safety
///
/// `c` is a tagged scalar or a live heap object the dying parent referenced.
unsafe fn drop_child(c: LeanObjPtr, todo: &mut Worklist) {
    if is_scalar(c) {
        return;
    }
    // SAFETY: `c` is live (the parent held a reference to it). On `Last`
    // this thread owns it; a leaf needs nothing but its own memory, freed
    // with the layout its live header gives.
    unsafe {
        if drop_cell(&(*c).header.ref_count) != DropOutcome::Last {
            return;
        }
        if is_leaf(c) {
            alloc::dealloc(c as *mut u8, object_layout(c));
        } else {
            todo.push(c);
        }
    }
}

/// Closure target for External foreach: drop a Lean child and return Unit.
/// Arity 1, invoked via closure_apply when foreach calls the visitor.
/// Matches Lean 4's mark_persistent_fn/mark_mt_fn pattern (object.cpp:542).
/// Part of #2244. `extern "C"`: `invoke_closure_func` calls every closure
/// target through an `extern "C"` function pointer.
extern "C" fn dec_child_fn(child: LeanObjPtr) -> LeanObjPtr {
    dec(child);
    lean_box(0) // Lean Unit = boxed 0
}

/// Clean up an External object's children and resources before dealloc:
/// `foreach` (drop internal Lean children via a visitor closure), then
/// `finalize` (release non-Lean FFI resources).
///
/// # Safety
///
/// `o` must be a valid External object pointer (kind == External).
unsafe fn external_cleanup(o: LeanObjPtr) {
    // SAFETY: caller guarantees `o` is a valid External object (kind ==
    // External), so the cast to ExternalObj is valid. The class pointer is
    // valid for the lifetime of the object. foreach and finalize (if Some)
    // are safe to call with the external data.
    unsafe {
        let ext = o as *const ExternalObj;
        if let Some(foreach) = (*(*ext).class).foreach {
            let dec_closure = alloc_closure_obj(dec_child_fn as *const (), 1, &[]);
            foreach((*ext).data, dec_closure);
            // Free the temporary closure directly — foreach borrows it
            // (b_lean_obj_arg convention) so its refcount is still 0.
            alloc::dealloc(dec_closure as *mut u8, object_layout(dec_closure));
        }
        if let Some(f) = (*(*ext).class).finalize {
            f((*ext).data);
        }
    }
}

// ---------------------------------------------------------------------------
// Properties shared by the unit sweep (`rc_sticky_tests`) and the Kani
// harnesses (`native/kani_rc_apply_reuse_tests.rs`, a STOCK EXCEPTION lane).
// ---------------------------------------------------------------------------

/// `inc_cell(rc, n)`: never lowers or wraps a count; at or above
/// [`RC_STICKY`] leaves it; otherwise applies `n` exactly, except that a
/// cold-path increment may stop frozen in `[RC_STICKY, RC_STICKY + RC_INC_MAX)`.
#[cfg(any(test, kani))]
pub(crate) fn check_inc_property(rc: u32, n: usize) {
    let cell = AtomicU32::new(rc);
    inc_cell(&cell, n);
    let after = cell.load(Ordering::Relaxed);
    assert!(
        after >= rc,
        "inc_cell({rc:#x}, {n:#x}) lowered or wrapped to {after:#x}"
    );
    if rc >= RC_STICKY {
        assert_eq!(
            after, rc,
            "a count at or above RC_STICKY takes no increment"
        );
        return;
    }
    let exact = u128::from(rc) + n as u128;
    if n <= RC_INC_MAX || exact < u128::from(RC_STICKY) {
        assert_eq!(
            u128::from(after),
            exact,
            "inc_cell({rc:#x}, {n:#x}) must be exact"
        );
    } else {
        let frozen = (RC_STICKY..RC_STICKY + RC_INC_MAX as u32).contains(&after);
        assert!(
            u128::from(after) == exact || frozen,
            "inc_cell({rc:#x}, {n:#x}) gave {after:#x}: neither exact nor frozen"
        );
    }
    assert!(after < RC_STICKY + RC_INC_MAX as u32 || after == rc);
    assert!(!is_exclusive_cell(&cell) || (rc == 0 && n == 0));
}

/// `drop_cell(rc)`: at or above [`RC_STICKY_DROP`] reports `Frozen` and
/// leaves the count; otherwise `Last` exactly at 0, else `Live` one lower.
/// Not defined at `u32::MAX` in a debug build, where the heuristic asserts.
#[cfg(any(test, kani))]
pub(crate) fn check_drop_property(rc: u32) {
    let cell = AtomicU32::new(rc);
    let outcome = drop_cell(&cell);
    let after = cell.load(Ordering::Relaxed);
    if rc >= RC_STICKY_DROP {
        assert_eq!(
            (outcome, after),
            (DropOutcome::Frozen, rc),
            "a frozen count is absorbing"
        );
    } else if rc == 0 {
        assert_eq!(outcome, DropOutcome::Last, "the last reference frees");
    } else {
        assert_eq!(
            (outcome, after),
            (DropOutcome::Live, rc - 1),
            "a shared drop is exact"
        );
    }
}
