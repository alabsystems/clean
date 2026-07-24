// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::alloc;
use std::mem::size_of;
use std::sync::atomic::Ordering;

// -- Tagged pointers --

#[test]
fn test_box_unbox_zero() {
    let p = lean_box(0);
    assert!(is_scalar(p));
    assert_eq!(lean_unbox(p), 0);
}

#[test]
fn test_box_unbox_max() {
    let p = lean_box(MAX_SMALL);
    assert!(is_scalar(p));
    assert_eq!(lean_unbox(p), MAX_SMALL);
}

#[test]
fn test_box_unbox_mid() {
    let p = lean_box(42);
    assert!(is_scalar(p));
    assert_eq!(lean_unbox(p), 42);
}

#[test]
fn test_scalar_tag() {
    let p = lean_box(7);
    assert_eq!(obj_tag(p), 7);
}

// -- Constructor allocation --

#[test]
fn test_alloc_ctor_no_fields() {
    let o = alloc_ctor(3, &[]);
    assert!(!is_scalar(o));
    assert_eq!(obj_tag(o), 3);
    assert!(lean_is_unique(o));
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!((*o).header.num_objs, 0);
    }
    lean_dec(o); // should free
}

#[test]
fn test_alloc_ctor_with_fields() {
    let a = lean_box(10);
    let b = lean_box(20);
    let o = alloc_ctor(1, &[a, b]);
    assert_eq!(obj_tag(o), 1);
    assert_eq!(ctor_get(o, 0), a);
    assert_eq!(ctor_get(o, 1), b);
    lean_dec(o);
}

#[test]
fn test_ctor_set_field() {
    let o = alloc_ctor(0, &[lean_box(0)]);
    let new_val = lean_box(99);
    ctor_set(o, 0, new_val);
    assert_eq!(ctor_get(o, 0), new_val);
    lean_dec(o);
}

// -- Reference counting --

#[test]
fn test_inc_dec_scalar_noop() {
    let p = lean_box(5);
    lean_inc(p);
    lean_dec(p); // should be no-op, no crash
}

#[test]
fn test_unique_after_alloc() {
    let o = alloc_ctor(0, &[]);
    assert!(lean_is_unique(o));
    lean_dec(o);
}

#[test]
fn test_not_unique_after_inc() {
    let o = alloc_ctor(0, &[]);
    lean_inc(o);
    assert!(!lean_is_unique(o));
    lean_dec(o); // dec to 0
    assert!(lean_is_unique(o));
    lean_dec(o); // free
}

#[test]
fn test_inc_n() {
    let o = alloc_ctor(0, &[]);
    lean_inc_n(o, 3);
    // ref_count is now 3, need 3 decs before unique
    lean_dec(o);
    lean_dec(o);
    lean_dec(o);
    assert!(lean_is_unique(o));
    lean_dec(o); // free
}

#[test]
fn test_runtime_dec_allows_high_bit_shared_refcount() {
    let o = alloc_ctor(0, &[]);
    // SAFETY: All objects were allocated by test helpers above and are valid
    // for the duration of this test. Header dereferences are within bounds.
    unsafe {
        (*o).header.ref_count.store(0x8000_0000, Ordering::Relaxed);
    }
    lean_dec(o);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!(
            (*o).header.ref_count.load(Ordering::Relaxed),
            0x7FFF_FFFF,
            "lean_dec must accept still-representable shared refcounts"
        );
        // Restore unique ownership so the test can free the object cleanly.
        (*o).header.ref_count.store(0, Ordering::Relaxed);
    }
    lean_dec(o);
}

#[test]
#[should_panic(expected = "ref_count wrapped to u32::MAX")]
fn test_runtime_dec_underflow_detected() {
    let o = alloc_ctor(0, &[]);
    // SAFETY: All objects were allocated by test helpers above and are valid
    // for the duration of this test. Header dereferences are within bounds.
    unsafe {
        (*o).header.ref_count.store(u32::MAX, Ordering::Relaxed);
    }
    lean_dec(o);
}

#[test]
fn test_recursive_dec_frees_children() {
    // Allocate child, give parent a reference to it.
    let child = alloc_ctor(0, &[]);
    lean_inc(child); // parent holds a ref
    let parent = alloc_ctor(0, &[child]);
    // Parent owns child (ref_count 1). Decrementing parent should dec child.
    lean_dec(parent);
    // After parent freed, child ref_count should have been decremented.
    // child was inc'd once (ref_count=1), parent dec'd it (ref_count=0),
    // which is unique — object still alive.
    assert!(lean_is_unique(child));
    lean_dec(child); // free child
}

#[test]
fn test_dec_deep_linked_list_no_stack_overflow() {
    // Regression (#1934): lean_dec was fully recursive, causing stack
    // overflow on deep object graphs. The tail-child optimization converts
    // the last-field recursion into a loop.
    //
    // Build a linked list: Cons(head=scalar, tail=next) with depth 20_000.
    // Cons is tag=1 with 2 fields: [head, tail].
    // Without the tail-child optimization, this would overflow the stack
    // (default 8MB / ~64 bytes per frame ≈ ~125K max depth, but in
    // practice stack overflow occurs much earlier due to lean_dec frame size).
    const DEPTH: usize = 20_000;
    let mut tail = lean_box(0); // Nil = scalar 0
    for _ in 0..DEPTH {
        let head = lean_box(42);
        tail = alloc_ctor(1, &[head, tail]); // Cons(head, tail)
    }
    // This should not stack overflow thanks to the tail-child loop.
    lean_dec(tail);
}

// -- Heap-allocated boxing --

#[test]
fn test_box_uint64_roundtrip() {
    let val: u64 = 0xDEAD_BEEF_CAFE_BABE;
    let o = box_uint64(val);
    assert!(!is_scalar(o));
    assert_eq!(unbox_uint64(o), val);
    lean_dec(o);
}

#[test]
fn test_box_uint32_small_uses_tag() {
    let o = box_uint32(100);
    assert!(is_scalar(o));
    assert_eq!(unbox_uint32(o), 100);
}

#[test]
fn test_box_uint32_large_uses_tag() {
    // 0x1_0000 is above the old 0xFFF cutoff but still fits within MAX_SMALL.
    let val: u32 = 0x1_0000;
    let o = box_uint32(val);
    assert!(is_scalar(o));
    assert_eq!(unbox_uint32(o), val);
}

#[test]
fn test_box_float_roundtrip() {
    let val: f64 = std::f64::consts::PI;
    let o = box_float(val);
    assert!(!is_scalar(o));
    assert_eq!(unbox_float(o), val);
    lean_dec(o);
}

// -- Closures --

fn dummy_fn() {}

#[test]
fn test_alloc_closure_no_args() {
    let func = dummy_fn as *const ();
    let o = alloc_closure(func, 2, &[]);
    assert!(!is_scalar(o));
    assert_eq!(closure_func(o), func);
    assert_eq!(closure_arity(o), 2);
    assert_eq!(closure_num_fixed(o), 0);
    lean_dec(o);
}

#[test]
fn test_alloc_closure_with_args() {
    let func = dummy_fn as *const ();
    let a = lean_box(1);
    let b = lean_box(2);
    let o = alloc_closure(func, 3, &[a, b]);
    assert_eq!(closure_func(o), func);
    assert_eq!(closure_arity(o), 3);
    assert_eq!(closure_num_fixed(o), 2);
    assert_eq!(closure_arg(o, 0), a);
    assert_eq!(closure_arg(o, 1), b);
    lean_dec(o);
}

#[test]
fn test_native_and_runtime_closures_share_child_count_contract() {
    let func = dummy_fn as *const ();
    let args = [lean_box(1), lean_box(2), lean_box(3)];

    let runtime_closure = alloc_closure(func, 5, &args);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let native_closure = unsafe { crate::native::alloc_closure(func as *mut (), 5, &args) };

    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!((*runtime_closure).header.num_objs, 0);
        assert_eq!((*native_closure).header.num_objs, 0);
        assert_eq!(
            crate::object_model::obj_child_count(runtime_closure),
            args.len()
        );
        assert_eq!(
            crate::object_model::obj_child_count(native_closure),
            args.len()
        );
    }

    lean_dec(runtime_closure);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        crate::native::dec(native_closure);
    }
}

// -- Strings --

#[test]
fn test_mk_string_empty() {
    let o = mk_string("");
    assert_eq!(string_len(o), 0);
    // SAFETY: o is alive until lean_dec below. Part of #1923.
    unsafe {
        assert_eq!(string_data(o), b"");
        assert_eq!(string_as_str(o), "");
    }
    lean_dec(o);
}

#[test]
fn test_mk_string_ascii() {
    let o = mk_string("hello");
    assert_eq!(string_len(o), 5);
    // SAFETY: o is alive until lean_dec below. Part of #1923.
    unsafe {
        assert_eq!(string_data(o), b"hello");
        assert_eq!(string_as_str(o), "hello");
    }
    lean_dec(o);
}

#[test]
fn test_mk_string_utf8() {
    let s = "こんにちは";
    let o = mk_string(s);
    assert_eq!(string_len(o), s.len()); // byte length
                                        // SAFETY: o is alive until lean_dec below. Part of #1923.
    assert_eq!(unsafe { string_as_str(o) }, s);
    lean_dec(o);
}

// -- Reset / Reuse --

#[test]
fn test_reset_unique_returns_ptr() {
    let child = lean_box(42);
    let o = alloc_ctor(0, &[child]);
    let slot = lean_reset(o);
    assert!(!slot.is_null());
    // Slot is the same pointer
    assert_eq!(slot, o);
    // We can reuse it
    let reused = lean_reuse(slot, 5, 0, &[lean_box(99)]);
    assert_eq!(obj_tag(reused), 5);
    assert_eq!(ctor_get(reused, 0), lean_box(99));
    lean_dec(reused);
}

#[test]
fn test_reset_shared_returns_null() {
    let o = alloc_ctor(0, &[]);
    lean_inc(o); // now ref_count = 1, shared
    let slot = lean_reset(o);
    assert!(slot.is_null());
    // o has been dec'd by lean_reset. It was shared (rc=1) so not freed yet.
    // Need one more dec.
    lean_dec(o);
}

#[test]
fn test_reset_scalar_returns_as_is() {
    // Regression: lean_is_unique returns true for scalars, so without
    // the is_scalar guard, lean_reset would dereference a tagged pointer
    // to read header.kind — UB. Must return scalar unchanged.
    let s = lean_box(42);
    let slot = lean_reset(s);
    assert_eq!(slot, s);
    assert!(is_scalar(slot));
    assert_eq!(lean_unbox(slot), 42);
}

#[test]
fn test_reset_closure_decs_captured_args() {
    // Regression: lean_reset must use ClosureObj::args_ptr for closures,
    // not CleanObj::fields_ptr. The old code would interpret func/arity as
    // Lean objects and call lean_dec on them — UB.
    let func = dummy_fn as *const ();
    let captured = alloc_ctor(0, &[]);
    lean_inc(captured); // ref_count = 1 (shared: closure + this ref)
    let closure = alloc_closure(func, 3, &[captured]);

    // Reset should dec the captured arg (captured goes from rc=1 to rc=0).
    let slot = lean_reset(closure);
    assert!(!slot.is_null());

    // captured should now be uniquely owned (rc=0) after reset dec'd it.
    assert!(lean_is_unique(captured));
    lean_dec(captured); // free captured
                        // slot (the closure allocation) is leaked intentionally — no lean_dec
                        // because reset already removed the children and the slot has func
                        // pointer fields that lean_dec would misinterpret.
                        // In real usage, lean_reuse would consume the slot.
                        // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        alloc::dealloc(slot as *mut u8, closure_layout(1));
    }
}

#[test]
fn test_reuse_null_allocates_fresh() {
    let o = lean_reuse(std::ptr::null_mut(), 7, 0, &[lean_box(1)]);
    assert_eq!(obj_tag(o), 7);
    assert_eq!(ctor_get(o, 0), lean_box(1));
    lean_dec(o);
}

#[test]
fn test_reuse_closure_slot_falls_back() {
    // Regression (#1920): lean_reuse must not reuse non-Ctor slots.
    // Closures have a different internal layout (func/arity/num_fixed
    // before captured args). Writing Ctor fields into a Closure slot
    // overwrites the func pointer — UB.
    let func = dummy_fn as *const ();
    let captured = lean_box(42);
    let closure = alloc_closure(func, 2, &[captured]);

    // Reset the uniquely-owned closure → returns the slot.
    let slot = lean_reset(closure);
    assert!(!slot.is_null());

    // Reuse should detect Closure kind, free the slot, and allocate fresh.
    let reused = lean_reuse(slot, 3, 0, &[lean_box(10)]);
    assert_eq!(obj_tag(reused), 3);
    assert_eq!(ctor_get(reused, 0), lean_box(10));
    // Verify it's a proper Ctor, not a reused Closure shell.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!((*reused).header.kind, ObjKind::Ctor as u8);
    }
    lean_dec(reused);
}

#[test]
fn test_reuse_string_slot_falls_back() {
    // Regression (#1920): String slots also have different layout.
    let s = mk_string("hello");

    // Reset the uniquely-owned string → returns the slot.
    let slot = lean_reset(s);
    assert!(!slot.is_null());

    // Reuse should detect String kind, free the slot, and allocate fresh.
    let reused = lean_reuse(slot, 0, 0, &[lean_box(99)]);
    assert_eq!(obj_tag(reused), 0);
    assert_eq!(ctor_get(reused, 0), lean_box(99));
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!((*reused).header.kind, ObjKind::Ctor as u8);
    }
    lean_dec(reused);
}

#[test]
fn test_reuse_null_with_scalar_sz_allocates_correct_size() {
    // Part of #1974: scalar_sz > 0 must allocate extra bytes for scalar data.
    let o = lean_reuse(std::ptr::null_mut(), 0, 8, &[lean_box(1)]);
    assert_eq!(obj_tag(o), 0);
    assert_eq!(ctor_get(o, 0), lean_box(1));
    // Verify scalar_sz was stored in header.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!((*o).header.scalar_sz, 8);
    }
    lean_dec(o);
}

// Part of #1991 — lean_reuse Ctor-slot path must preserve scalar_sz in header.
// The compiler invariant is that reuse only happens for same-layout constructors
// (same num_objs, same scalar_sz). This test verifies scalar_sz is written to
// the header on the reuse path (previously it was not, which was a latent bug).
#[test]
fn test_reuse_ctor_slot_updates_scalar_sz() {
    // Allocate a Ctor with scalar_sz=8 (8 bytes of scalar payload).
    let original = alloc_ctor_uninit(0, 1, 8);
    // SAFETY: All objects were allocated by test helpers above and are valid
    // for the duration of this test. Header dereferences are within bounds.
    unsafe {
        // Set one object field for lean_reset/lean_dec to iterate.
        ctor_set(original, 0, lean_box(1));
        assert_eq!((*original).header.scalar_sz, 8);
        assert_eq!((*original).header.num_objs, 1);
    }

    // Reset it (returns the slot since it's uniquely owned).
    let slot = lean_reset(original);
    assert!(!slot.is_null());

    // Reuse the slot for a constructor with same layout (1 obj, 8 scalar bytes).
    // The release-enforced reuse check verifies the invariant: scalar_sz must match.
    let reused = lean_reuse(slot, 1, 8, &[lean_box(2)]);

    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        // Part of #1991: lean_reuse now writes scalar_sz on the reuse path.
        assert_eq!(
            (*reused).header.scalar_sz,
            8,
            "lean_reuse must write scalar_sz to header on Ctor reuse path"
        );
        assert_eq!((*reused).header.tag, 1, "tag should be updated");
    }

    lean_dec(reused);
}

// -- External finalize (Part of #2241) --

#[test]
fn test_external_finalize_called_on_lean_dec() {
    use std::sync::atomic::AtomicBool;
    static FINALIZED: AtomicBool = AtomicBool::new(false);

    unsafe fn test_finalize(_data: *mut ()) {
        FINALIZED.store(true, Ordering::SeqCst);
    }

    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: Some(test_finalize),
        foreach: None,
    };

    FINALIZED.store(false, Ordering::SeqCst);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let ext = unsafe { alloc_external(&CLASS, std::ptr::null_mut()) };
    assert!(
        !FINALIZED.load(Ordering::SeqCst),
        "finalize should not be called yet"
    );
    lean_dec(ext);
    assert!(
        FINALIZED.load(Ordering::SeqCst),
        "finalize must be called when External refcount reaches zero"
    );
}

#[test]
fn test_external_finalize_not_called_if_none() {
    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: None,
        foreach: None,
    };

    // Should not panic when finalize is None.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let ext = unsafe { alloc_external(&CLASS, std::ptr::null_mut()) };
    lean_dec(ext);
}

#[test]
fn test_external_finalize_receives_data_pointer() {
    use std::sync::atomic::AtomicUsize;
    static RECEIVED_DATA: AtomicUsize = AtomicUsize::new(0);

    unsafe fn capture_data(data: *mut ()) {
        RECEIVED_DATA.store(data as usize, Ordering::SeqCst);
    }

    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: Some(capture_data),
        foreach: None,
    };

    let sentinel: usize = 0xDEAD_BEEF;
    RECEIVED_DATA.store(0, Ordering::SeqCst);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let ext = unsafe { alloc_external(&CLASS, sentinel as *mut ()) };
    lean_dec(ext);
    assert_eq!(
        RECEIVED_DATA.load(Ordering::SeqCst),
        sentinel,
        "finalize must receive the original data pointer"
    );
}

// -- External foreach (Part of #2244) --

#[test]
fn test_external_foreach_decs_children_on_drop() {
    // Allocate a Lean child object (a Ctor). rc=0 means one logical owner.
    // The External's foreach callback will dec the child on dealloc,
    // consuming the sole reference (rc=0 → dealloc).
    // No clean_inc: rc=0 already represents one owner (the External).
    let child = alloc_ctor_uninit(0, 0, 0);

    // The foreach implementation calls the visitor closure on each child.
    // The visitor (dec_child_fn wrapped in a closure) will lean_dec the child.
    // In the dealloc context, foreach transfers the External's owned reference
    // to the visitor — no inc needed. The visitor's dec consumes the reference.
    unsafe fn test_foreach(data: *mut (), visitor: *mut CleanObj) {
        let child = data as *mut CleanObj;
        closure_apply(visitor, &[child]);
    }

    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: None,
        foreach: Some(test_foreach),
    };

    // Store the child pointer as the External's data.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let ext = unsafe { alloc_external(&CLASS, child as *mut ()) };

    // Before drop: child refcount should be 0 (sole owner = External).
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!(
            (*child).header.ref_count.load(Ordering::SeqCst),
            0,
            "child refcount should be 0 (sole owner) before External drop"
        );
    }

    // Drop the External — foreach should dec the child.
    lean_dec(ext);

    // After foreach + dealloc: child was dec'd by the visitor closure.
    // refcount went 1 → 0, which triggers dealloc of the child itself.
    // We can't read the child's refcount after it's freed, so the test
    // succeeds if it doesn't crash (no use-after-free, no leak).
    // For a stronger check, we use a finalize callback on the child side
    // (but Ctor objects don't have finalize). The absence of ASAN/MSAN
    // errors is the primary signal.
}

#[test]
fn test_external_foreach_not_called_if_none() {
    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: None,
        foreach: None,
    };

    // Should not panic when foreach is None.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let ext = unsafe { alloc_external(&CLASS, std::ptr::null_mut()) };
    lean_dec(ext);
}

#[test]
fn test_external_foreach_called_before_finalize() {
    use std::sync::atomic::AtomicU32;
    // Track the order: foreach sets to 1, finalize sets to 2.
    static ORDER: AtomicU32 = AtomicU32::new(0);

    unsafe fn order_foreach(_data: *mut (), _visitor: *mut CleanObj) {
        ORDER.store(1, Ordering::SeqCst);
    }

    unsafe fn order_finalize(_data: *mut ()) {
        assert_eq!(
            ORDER.load(Ordering::SeqCst),
            1,
            "foreach must be called before finalize"
        );
        ORDER.store(2, Ordering::SeqCst);
    }

    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: Some(order_finalize),
        foreach: Some(order_foreach),
    };

    ORDER.store(0, Ordering::SeqCst);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let ext = unsafe { alloc_external(&CLASS, std::ptr::null_mut()) };
    lean_dec(ext);
    assert_eq!(
        ORDER.load(Ordering::SeqCst),
        2,
        "both foreach and finalize must have run"
    );
}

// -- Dealloc layout correctness for extended types (Part of #2250) --

#[test]
fn test_dealloc_thunk_correct_layout() {
    // Allocate a thunk with a scalar closure (no heap child to dec).
    // If lean_dec uses the wrong layout (8 bytes instead of 24), this
    // triggers UB in the allocator. Detectable by Miri/ASAN.
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    let thunk = unsafe { alloc_thunk(lean_box(42)) };
    lean_dec(thunk);
}

#[test]
fn test_dealloc_thunk_decs_closure() {
    // Thunk holds a heap-allocated closure child. lean_dec must dec it
    // before dealloc to avoid a memory leak.
    let child = alloc_ctor_uninit(0, 0, 0);
    // alloc_thunk takes ownership of the closure pointer (rc=0 means
    // one logical owner). No clean_inc needed — the thunk is the sole owner.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let thunk = unsafe { alloc_thunk(child) };
    lean_dec(thunk);
    // If child leaked, ASAN/Miri would detect it. Absence of crash
    // plus no allocator UB = correct.
}

#[test]
fn test_dealloc_thunk_decs_value_when_forced() {
    // Simulate a forced thunk: value is set, closure is null.
    let value_child = alloc_ctor_uninit(0, 0, 0);
    // No clean_inc: the thunk's value field becomes the sole owner (rc=0).
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    let thunk = unsafe { alloc_thunk(lean_box(0)) }; // dummy closure (scalar)
                                                     // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        // Simulate forcing: set value, null out closure.
        let t = thunk as *mut ThunkObj;
        (*t).value = value_child;
        (*t).closure = std::ptr::null_mut();
    }
    lean_dec(thunk);
    // value_child should have been dec'd. No leak, no UB.
}

#[test]
fn test_dealloc_task_correct_layout() {
    // Allocate a task and drop it. Tests correct layout (24 bytes, not 8).
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    let task = unsafe { alloc_task(std::ptr::null_mut()) };
    lean_dec(task);
}

#[test]
fn test_dealloc_task_decs_value() {
    // Task with a completed value (heap object).
    let value_child = alloc_ctor_uninit(0, 0, 0);
    // No clean_inc: the task's value field becomes the sole owner (rc=0).
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    let task = unsafe { alloc_task(std::ptr::null_mut()) };
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        let t = task as *mut TaskObj;
        (*t).value = value_child;
    }
    lean_dec(task);
    // value_child should have been dec'd.
}

#[test]
fn test_dealloc_array_correct_layout() {
    // Allocate an empty array with capacity 4. Layout should be
    // sizeof(ArrayObj) + 4 * sizeof(ptr) = 24 + 32 = 56 bytes.
    let arr = alloc_array(4);
    lean_dec(arr);
}

#[test]
fn test_dealloc_array_decs_elements() {
    // Array holding 2 heap-allocated children. lean_dec must dec
    // all live elements (0..size) before freeing the array.
    let arr = alloc_array(4);
    let c1 = alloc_ctor_uninit(0, 0, 0);
    let c2 = alloc_ctor_uninit(1, 0, 0);
    // No clean_inc: array_push takes ownership of the caller's reference
    // (rc=0 → array is sole owner). Same fix as native/rc.rs counterpart.
    // array_push now returns the (possibly new) array pointer.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        let arr = array_push(arr, c1);
        let arr = array_push(arr, c2);
        lean_dec(arr);
    }
    // Both children should have been dec'd and freed.
}

// -- Array COW tests (Part of #2020) --

#[test]
fn test_array_push_realloc_on_overflow() {
    // Push beyond initial capacity triggers reallocation.
    let mut arr = alloc_array(2);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        // Fill to capacity.
        arr = array_push(arr, lean_box(10));
        arr = array_push(arr, lean_box(20));
        assert_eq!(array_size(arr), 2);
        // Push beyond capacity — should reallocate, not panic.
        arr = array_push(arr, lean_box(30));
        assert_eq!(array_size(arr), 3);
        // Verify all elements.
        assert_eq!(lean_unbox(array_get(arr, 0)), 10);
        assert_eq!(lean_unbox(array_get(arr, 1)), 20);
        assert_eq!(lean_unbox(array_get(arr, 2)), 30);
        lean_dec(arr);
    }
}

#[test]
fn test_array_push_cow_shared() {
    // Pushing onto a shared array must copy — original unchanged.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(42));
        // Share it: inc ref count so it's no longer exclusive.
        lean_inc(arr);
        let pushed = array_push(arr, lean_box(99));
        // pushed is a new allocation (COW copy).
        assert_ne!(pushed, arr);
        assert_eq!(array_size(arr), 1);
        assert_eq!(array_size(pushed), 2);
        assert_eq!(lean_unbox(array_get(pushed, 0)), 42);
        assert_eq!(lean_unbox(array_get(pushed, 1)), 99);
        lean_dec(arr);
        lean_dec(pushed);
    }
}

#[test]
fn test_array_uset_cow() {
    // uset on a shared array produces a copy; original unchanged.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(1));
        let arr = array_push(arr, lean_box(2));
        lean_inc(arr);
        let modified = array_uset(arr, 0, lean_box(99));
        assert_ne!(modified, arr);
        assert_eq!(lean_unbox(array_get(arr, 0)), 1);
        assert_eq!(lean_unbox(array_get(modified, 0)), 99);
        lean_dec(arr);
        lean_dec(modified);
    }
}

#[test]
fn test_array_uset_exclusive() {
    // uset on exclusive array modifies in place.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(1));
        let modified = array_uset(arr, 0, lean_box(99));
        assert_eq!(modified, arr);
        assert_eq!(lean_unbox(array_get(modified, 0)), 99);
        lean_dec(modified);
    }
}

#[test]
fn test_array_uget_incs_refcount() {
    // uget returns an inc'd reference.
    let arr = alloc_array(4);
    let elem = alloc_ctor_uninit(0, 0, 0);
    lean_inc(elem); // extra ref so we can check after array_uget
                    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        let arr = array_push(arr, elem);
        let got = array_uget(arr, 0);
        assert_eq!(got, elem);
        // elem has: 1 (our inc) + 1 (array) + 1 (uget inc) = rc 2
        // cleanup: dec our ref, dec uget's ref, dec array (which decs elem)
        lean_dec(got);
        lean_dec(elem);
        lean_dec(arr);
    }
}

#[test]
fn test_array_pop() {
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(10));
        let arr = array_push(arr, lean_box(20));
        let arr = array_pop(arr);
        assert_eq!(array_size(arr), 1);
        assert_eq!(lean_unbox(array_get(arr, 0)), 10);
        lean_dec(arr);
    }
}

#[test]
fn test_array_pop_empty_returns_unchanged() {
    // Lean 4 returns empty array unchanged on pop(empty).
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let result = array_pop(arr);
        assert_eq!(array_size(result), 0);
        assert_eq!(result, arr);
        lean_dec(result);
    }
}

#[test]
fn test_array_swap() {
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(10));
        let arr = array_push(arr, lean_box(20));
        let arr = array_uswap(arr, 0, 1);
        assert_eq!(lean_unbox(array_get(arr, 0)), 20);
        assert_eq!(lean_unbox(array_get(arr, 1)), 10);
        lean_dec(arr);
    }
}

#[test]
fn test_mk_array() {
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = mk_array(3, lean_box(7));
        assert_eq!(array_size(arr), 3);
        assert_eq!(lean_unbox(array_get(arr, 0)), 7);
        assert_eq!(lean_unbox(array_get(arr, 1)), 7);
        assert_eq!(lean_unbox(array_get(arr, 2)), 7);
        lean_dec(arr);
    }
}

#[test]
fn test_mk_array_consumes_v() {
    // mk_array consumes v (Lean 4 convention). With non-scalar v,
    // refcount after mk_array(3, v) should be: 3 refs in array,
    // caller's ref consumed. Net: v.rc = initial + 2 (3 array - 1 consumed).
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let v = alloc_ctor_uninit(0, 0, 0);
        // v has rc=0 (unique). mk_array consumes it.
        let arr = mk_array(3, v);
        assert_eq!(array_size(arr), 3);
        assert_eq!(array_get(arr, 0), v);
        assert_eq!(array_get(arr, 1), v);
        assert_eq!(array_get(arr, 2), v);
        // v.rc should be 2 (3 array refs - 1 consumed = net +2 from initial 0).
        // Dropping arr should dec all 3 refs → v.rc goes to -1 → freed.
        lean_dec(arr);
    }
}

#[test]
fn test_mk_array_zero_consumes_v() {
    // mk_array(0, v) should consume v even when n=0.
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let v = alloc_ctor_uninit(0, 0, 0);
        lean_inc(v); // rc=1 so dec inside mk_array doesn't free
        let arr = mk_array(0, v);
        assert_eq!(array_size(arr), 0);
        // v was consumed by mk_array (dec'd once). rc went from 1 to 0.
        // We still have our extra ref from lean_inc.
        lean_dec(v); // now rc goes to -1, freed.
        lean_dec(arr);
    }
}

#[test]
fn test_mk_empty_array() {
    let arr = mk_empty_array();
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        assert_eq!(array_size(arr), 0);
    }
    lean_dec(arr);
}

#[test]
fn test_array_set_oob_returns_unchanged() {
    // Out-of-bounds set should return array unchanged and dec the value.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(1));
        // idx=5 is out of bounds (size=1)
        let result = array_set(arr, lean_box(5), lean_box(99));
        assert_eq!(result, arr);
        assert_eq!(array_size(result), 1);
        assert_eq!(lean_unbox(array_get(result, 0)), 1);
        lean_dec(result);
    }
}

#[test]
fn test_array_get_checked_oob_returns_default() {
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(42));
        let def = lean_box(999);
        let result = array_get_checked(def, arr, lean_box(5));
        assert_eq!(lean_unbox(result), 999);
        lean_dec(arr);
    }
}

#[test]
fn test_copy_array_expand_doubles_capacity() {
    // copy_array with expand=true should double capacity.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(1));
        let arr = array_push(arr, lean_box(2));
        // Copy with expand — new capacity should be 8.
        let copied = copy_array(arr, true);
        assert_eq!(array_size(copied), 2);
        assert_eq!(lean_unbox(array_get(copied, 0)), 1);
        assert_eq!(lean_unbox(array_get(copied, 1)), 2);
        // Original was consumed (dec'd) by copy_array.
        // Push 6 more to verify expanded capacity (should fit 8 total).
        let mut c = copied;
        for i in 3..=8 {
            c = array_push(c, lean_box(i));
        }
        assert_eq!(array_size(c), 8);
        lean_dec(c);
    }
}

#[test]
fn test_ensure_exclusive_shared_copies() {
    // ensure_exclusive on a shared array produces a copy.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(42));
        lean_inc(arr); // make shared
        let excl = ensure_exclusive_array(arr);
        assert_ne!(excl, arr);
        assert_eq!(array_size(excl), 1);
        assert_eq!(lean_unbox(array_get(excl, 0)), 42);
        lean_dec(arr);
        lean_dec(excl);
    }
}

#[test]
fn test_ensure_exclusive_unique_returns_same() {
    // ensure_exclusive on a unique array returns the same pointer.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(7));
        let excl = ensure_exclusive_array(arr);
        assert_eq!(excl, arr);
        lean_dec(excl);
    }
}

#[test]
fn test_array_fset_boxed_index() {
    // fset with boxed index should work like uset.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(10));
        let arr = array_push(arr, lean_box(20));
        let result = array_fset(arr, lean_box(1), lean_box(99));
        assert_eq!(lean_unbox(array_get(result, 0)), 10);
        assert_eq!(lean_unbox(array_get(result, 1)), 99);
        lean_dec(result);
    }
}

#[test]
fn test_array_fswap_boxed_indices() {
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(10));
        let arr = array_push(arr, lean_box(20));
        let arr = array_push(arr, lean_box(30));
        let result = array_fswap(arr, lean_box(0), lean_box(2));
        assert_eq!(lean_unbox(array_get(result, 0)), 30);
        assert_eq!(lean_unbox(array_get(result, 2)), 10);
        lean_dec(result);
    }
}

#[test]
fn test_array_get_size_returns_boxed() {
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(1));
        let arr = array_push(arr, lean_box(2));
        let arr = array_push(arr, lean_box(3));
        let boxed_size = array_get_size(arr);
        assert_eq!(lean_unbox(boxed_size), 3);
        lean_dec(arr);
    }
}

#[test]
fn test_array_get_size_above_historical_cutoff() {
    const LEN: usize = 5_000;

    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let mut arr = mk_empty_array_with_capacity(lean_box(LEN));
        for i in 0..LEN {
            arr = array_push(arr, lean_box(i));
        }

        let boxed_size = array_get_size(arr);
        assert!(
            is_scalar(boxed_size),
            "sizes above the old 0xFFF cutoff should still use tagged pointers"
        );
        assert_eq!(lean_unbox(boxed_size), LEN);
        lean_dec(arr);
    }
}

#[test]
fn test_mk_empty_array_with_capacity_reserves() {
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = mk_empty_array_with_capacity(lean_box(16));
        assert_eq!(array_size(arr), 0);
        // Push 16 elements without triggering reallocation.
        let mut a = arr;
        for i in 0..16 {
            a = array_push(a, lean_box(i));
        }
        assert_eq!(array_size(a), 16);
        lean_dec(a);
    }
}

#[test]
fn test_array_swap_oob_returns_unchanged() {
    // Out-of-bounds swap should return array unchanged.
    let arr = alloc_array(4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, lean_box(10));
        // idx=5 is out of bounds (size=1)
        let result = array_swap(arr, lean_box(0), lean_box(5));
        assert_eq!(result, arr);
        assert_eq!(lean_unbox(array_get(result, 0)), 10);
        lean_dec(result);
    }
}

#[test]
fn test_array_fget_boxed_index() {
    let arr = alloc_array(4);
    let elem = alloc_ctor_uninit(0, 0, 0);
    lean_inc(elem);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let arr = array_push(arr, elem);
        let got = array_fget(arr, lean_box(0));
        assert_eq!(got, elem);
        lean_dec(got);
        lean_dec(elem);
        lean_dec(arr);
    }
}

#[test]
fn test_dealloc_external_correct_layout() {
    // Verify External uses Layout::new::<ExternalObj>() (24 bytes),
    // not obj_layout(0,0) (8 bytes). Part of #2250.
    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: None,
        foreach: None,
    };
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let ext = unsafe { alloc_external(&CLASS, std::ptr::null_mut()) };
    lean_dec(ext);
}

#[test]
fn test_reuse_ctor_slot_larger_layout_falls_back() {
    // Allocate a small Ctor (0 obj fields, 0 scalar bytes).
    let small = alloc_ctor_uninit(0, 0, 0);
    // Reset to get the reuse slot.
    let slot = lean_reset(small);
    assert!(!slot.is_null());

    // Reuse with a larger layout (2 obj fields, 8 scalar bytes).
    // This should fall back to fresh allocation, not overflow.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let reused = unsafe { reuse_slot(slot, 1, 2, 8) };
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!((*reused).header.tag, 1);
        assert_eq!((*reused).header.num_objs, 2);
        assert_eq!((*reused).header.scalar_sz, 8);
    }
    // Set object fields to valid scalars so lean_dec doesn't chase garbage.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        let fields = CleanObj::fields_ptr(reused);
        *fields.add(0) = lean_box(0);
        *fields.add(1) = lean_box(0);
    }
    lean_dec(reused);
}

#[test]
fn test_reuse_slot_closure_slot_falls_back() {
    let closure = alloc_closure(dummy_fn as *const (), 2, &[lean_box(7)]);
    let slot = lean_reset(closure);
    assert!(!slot.is_null());

    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let reused = unsafe { reuse_slot(slot, 1, 1, 0) };
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        assert_eq!((*reused).header.kind, ObjKind::Ctor as u8);
        let fields = CleanObj::fields_ptr(reused);
        *fields.add(0) = lean_box(11);
    }

    assert_eq!(obj_tag(reused), 1);
    assert_eq!(ctor_get(reused, 0), lean_box(11));
    lean_dec(reused);
}

// -- Header layout --

#[test]
fn test_obj_header_size_is_8_bytes() {
    assert_eq!(size_of::<ObjHeader>(), 8);
}

#[test]
fn test_scalar_sz_stored_in_header() {
    let o = box_uint64(42);
    // SAFETY: All objects were allocated by test helpers above and are valid
    // for the duration of this test. Header dereferences are within bounds.
    unsafe {
        assert_eq!((*o).header.scalar_sz, size_of::<u64>() as u8);
        assert_eq!((*o).header.num_objs, 0);
    }
    lean_dec(o);
}

// -- Dealloc regression (Part of #1904) --

#[test]
fn test_dealloc_ctor_with_scalar_and_pointer_fields() {
    // Regression: mixed scalar+pointer constructor. alloc with scalar_size > 0
    // and num_objs > 0. Dealloc must use both values for correct layout.
    let child = lean_box(7);
    let o = alloc_ctor_uninit(0, 1, size_of::<u64>() as u8);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        // Write the pointer field.
        let fields = CleanObj::fields_ptr(o);
        std::ptr::write(fields, child);
        // Write scalar payload.
        let scalar = CleanObj::scalar_ptr(o) as *mut u64;
        std::ptr::write(scalar, 0xCAFE_BABE);
    }
    // Verify reads.
    assert_eq!(ctor_get(o, 0), child);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        let scalar = CleanObj::scalar_ptr(o) as *const u64;
        assert_eq!(std::ptr::read(scalar), 0xCAFE_BABE);
    }
    // This lean_dec previously used wrong layout (scalar_size=0) — UB.
    lean_dec(o);
}

// -- Deallocation coverage (Part of #1987) --

#[test]
fn test_dealloc_closure_zero_args() {
    let dummy_fn: *const () = 0x1000 as *const ();
    let c = alloc_closure(dummy_fn, 2, &[]);
    // Single owner — lean_dec should deallocate without UB.
    lean_dec(c);
}

#[test]
fn test_dealloc_closure_with_args() {
    let dummy_fn: *const () = 0x1000 as *const ();
    // Captured args are scalars so lean_dec on children is a no-op.
    let args = [lean_box(1), lean_box(2), lean_box(3)];
    let c = alloc_closure(dummy_fn, 5, &args);
    lean_dec(c);
}

#[test]
fn test_dealloc_string_empty() {
    let s = mk_string("");
    lean_dec(s);
}

#[test]
fn test_dealloc_string_short() {
    let s = mk_string("hello");
    lean_dec(s);
}

#[test]
fn test_dealloc_string_long() {
    let long = "a".repeat(1024);
    let s = mk_string(&long);
    lean_dec(s);
}

#[test]
fn test_dealloc_ctor_scalar_only() {
    // Ctor with 0 pointer fields but 8 bytes scalar payload.
    let o = alloc_ctor_uninit(0, 0, 8);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let p = CleanObj::scalar_ptr(o) as *mut u64;
        std::ptr::write(p, 42);
    }
    lean_dec(o);
}

#[test]
fn test_dealloc_ctor_many_fields() {
    // Ctor with multiple pointer fields (all scalars) and scalar payload.
    let fields = [lean_box(0), lean_box(1), lean_box(2), lean_box(3)];
    let o = alloc_ctor_uninit(0, 4, 4);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let dst = CleanObj::fields_ptr(o);
        for (i, &f) in fields.iter().enumerate() {
            std::ptr::write(dst.add(i), f);
        }
        let p = CleanObj::scalar_ptr(o) as *mut u32;
        std::ptr::write(p, 0xDEAD);
    }
    lean_dec(o);
}

// -- Deallocation coverage: varying sizes (Part of #1987) --

#[test]
fn test_dealloc_closure_one_arg() {
    let dummy_fn: *const () = 0x1000 as *const ();
    let c = alloc_closure(dummy_fn, 3, &[lean_box(42)]);
    lean_dec(c);
}

#[test]
fn test_dealloc_closure_many_args() {
    let dummy_fn: *const () = 0x1000 as *const ();
    let args: Vec<LeanObjPtr> = (0..8).map(lean_box).collect();
    let c = alloc_closure(dummy_fn, 10, &args);
    lean_dec(c);
}

#[test]
fn test_dealloc_ctor_max_scalar() {
    // Ctor with maximum scalar_sz (255 bytes) and no pointer fields.
    let o = alloc_ctor_uninit(0, 0, 255);
    lean_dec(o);
}

#[test]
fn test_dealloc_ctor_max_fields_no_scalar() {
    // Ctor with many pointer fields (all scalars) and no scalar payload.
    let fields: Vec<LeanObjPtr> = (0..16).map(lean_box).collect();
    let o = alloc_ctor_uninit(0, 16, 0);
    // SAFETY: All pointers are valid heap objects allocated in this test.
    // They are uniquely owned unless explicitly shared via inc().
    unsafe {
        let dst = CleanObj::fields_ptr(o);
        for (i, &f) in fields.iter().enumerate() {
            std::ptr::write(dst.add(i), f);
        }
    }
    lean_dec(o);
}

// -- Deallocation coverage: heap children (Part of #1987) --
// These tests exercise the child-iteration path in lean_dec with actual
// heap-allocated children, not lean_box scalars. Without these, the
// recursive lean_dec calls on children are untested.

#[test]
fn test_dealloc_closure_heap_children() {
    // Closure captures 3 heap-allocated Ctor objects.
    // lean_dec on the closure must recursively free all children.
    let func = dummy_fn as *const ();
    let c1 = alloc_ctor(0, &[]);
    let c2 = alloc_ctor(1, &[]);
    let c3 = alloc_ctor(2, &[]);
    let closure = alloc_closure(func, 5, &[c1, c2, c3]);
    // Each child has ref_count=0 (unique owner is the closure).
    // lean_dec(closure) should dec ref_count to -1 (wrapping), then free
    // the closure and each child.
    lean_dec(closure);
}

#[test]
fn test_dealloc_ctor_heap_children() {
    // Ctor with 2 heap-allocated Ctor children + scalar payload.
    // lean_dec should recursively free children.
    let child1 = alloc_ctor(0, &[]);
    let child2 = alloc_ctor(1, &[]);
    let o = alloc_ctor_uninit(0, 2, 4);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        let fields = CleanObj::fields_ptr(o);
        std::ptr::write(fields, child1);
        std::ptr::write(fields.add(1), child2);
        let scalar = CleanObj::scalar_ptr(o) as *mut u32;
        std::ptr::write(scalar, 0xCAFE);
    }
    lean_dec(o);
}

#[test]
fn test_dealloc_ctor_nested_heap_children() {
    // Ctor whose child is itself a Ctor with a heap child — tests
    // the tail-call optimization loop in lean_dec.
    let grandchild = alloc_ctor(0, &[]);
    let child = alloc_ctor(0, &[grandchild]);
    let parent = alloc_ctor(0, &[child]);
    // Chain: parent -> child -> grandchild. lean_dec should free all 3.
    lean_dec(parent);
}

#[test]
fn test_dealloc_closure_mixed_scalar_heap_children() {
    // Closure captures a mix of boxed scalars and heap Ctors.
    // lean_dec must handle both: skip scalars, free heap objects.
    let func = dummy_fn as *const ();
    let heap_child = alloc_ctor(0, &[]);
    let args = [lean_box(42), heap_child, lean_box(99)];
    let closure = alloc_closure(func, 5, &args);
    lean_dec(closure);
}

#[test]
fn test_reset_closure_many_args_decs_all() {
    // lean_reset on a closure with multiple captured heap objects must dec all.
    let func = dummy_fn as *const ();
    let c1 = alloc_ctor(0, &[]);
    let c2 = alloc_ctor(0, &[]);
    lean_inc(c1);
    lean_inc(c2);
    let closure = alloc_closure(func, 5, &[c1, c2]);
    let slot = lean_reset(closure);
    assert!(!slot.is_null());
    // Both captured args should be uniquely owned after reset.
    assert!(lean_is_unique(c1));
    assert!(lean_is_unique(c2));
    lean_dec(c1);
    lean_dec(c2);
    // Free the slot allocation directly.
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        alloc::dealloc(slot as *mut u8, closure_layout(2));
    }
}

#[test]
fn test_reset_ctor_with_scalar_and_children() {
    // lean_reset on a Ctor with both pointer children and scalar payload.
    let child = alloc_ctor(0, &[]);
    lean_inc(child);
    let o = alloc_ctor_uninit(0, 1, 8);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        let fields = CleanObj::fields_ptr(o);
        std::ptr::write(fields, child);
        let scalar = CleanObj::scalar_ptr(o) as *mut u64;
        std::ptr::write(scalar, 0xBEEF);
    }
    let slot = lean_reset(o);
    assert!(!slot.is_null());
    assert!(lean_is_unique(child));
    lean_dec(child);
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    unsafe {
        alloc::dealloc(slot as *mut u8, obj_layout(1, 8));
    }
}

// -- Runtime init/finalize --

#[test]
fn test_runtime_init_finalize_noop() {
    runtime_init();
    runtime_finalize();
}

// -- Typed scalar getters/setters (Part of #2005 Phase 2) --

#[test]
fn test_ctor_get_set_uint8() {
    // Allocate a ctor with 1 object field + 1 byte scalar payload.
    let ptr_sz = size_of::<LeanObjPtr>();
    let o = alloc_ctor_uninit(0, 1, 1);
    ctor_set(o, 0, lean_box(0));
    // The scalar region starts at byte offset = num_objs * ptr_size.
    ctor_set_uint8(o, ptr_sz, 0xAB);
    assert_eq!(ctor_get_uint8(o, ptr_sz), 0xAB);
    lean_dec(o);
}

#[test]
fn test_ctor_get_set_uint16() {
    let ptr_sz = size_of::<LeanObjPtr>();
    let o = alloc_ctor_uninit(0, 1, 2);
    ctor_set(o, 0, lean_box(0));
    ctor_set_uint16(o, ptr_sz, 0xBEEF);
    assert_eq!(ctor_get_uint16(o, ptr_sz), 0xBEEF);
    lean_dec(o);
}

#[test]
fn test_ctor_get_set_uint32() {
    let ptr_sz = size_of::<LeanObjPtr>();
    let o = alloc_ctor_uninit(0, 1, 4);
    ctor_set(o, 0, lean_box(0));
    ctor_set_uint32(o, ptr_sz, 0xDEAD_BEEF);
    assert_eq!(ctor_get_uint32(o, ptr_sz), 0xDEAD_BEEF);
    lean_dec(o);
}

#[test]
fn test_ctor_get_set_uint64() {
    let ptr_sz = size_of::<LeanObjPtr>();
    let o = alloc_ctor_uninit(0, 1, 8);
    ctor_set(o, 0, lean_box(0));
    ctor_set_uint64(o, ptr_sz, 0xCAFE_BABE_DEAD_BEEF);
    assert_eq!(ctor_get_uint64(o, ptr_sz), 0xCAFE_BABE_DEAD_BEEF);
    lean_dec(o);
}

#[test]
fn test_ctor_get_set_usize() {
    // usize uses slot index, not byte offset.
    // Allocate 2 object slots — slot 0 is a pointer, slot 1 is usize scalar.
    let o = alloc_ctor_uninit(0, 1, size_of::<usize>() as u8);
    ctor_set(o, 0, lean_box(0));
    ctor_set_usize(o, 1, 0x1234_5678);
    assert_eq!(ctor_get_usize(o, 1), 0x1234_5678);
    lean_dec(o);
}

#[test]
fn test_ctor_get_set_float() {
    let ptr_sz = size_of::<LeanObjPtr>();
    let o = alloc_ctor_uninit(0, 1, 8);
    ctor_set(o, 0, lean_box(0));
    ctor_set_float(o, ptr_sz, std::f64::consts::PI);
    assert_eq!(ctor_get_float(o, ptr_sz), std::f64::consts::PI);
    lean_dec(o);
}

#[test]
fn test_ctor_get_set_float32() {
    let ptr_sz = size_of::<LeanObjPtr>();
    let o = alloc_ctor_uninit(0, 1, 4);
    ctor_set(o, 0, lean_box(0));
    ctor_set_float32(o, ptr_sz, std::f32::consts::E);
    assert_eq!(ctor_get_float32(o, ptr_sz), std::f32::consts::E);
    lean_dec(o);
}

#[test]
fn test_ctor_set_tag() {
    let o = alloc_ctor(0, &[]);
    assert_eq!(obj_tag(o), 0);
    ctor_set_tag(o, 42);
    assert_eq!(obj_tag(o), 42);
    lean_dec(o);
}

#[test]
fn test_scalar_only_ctor_get_set() {
    // Allocate a ctor with 0 object fields + 8 bytes scalar payload.
    // This matches the pattern emitted for `clean_alloc_ctor(tag, 0, 8, &[])`.
    let o = alloc_ctor_uninit(0, 0, 8);
    // offset=0 because there are no pointer fields, so scalar region starts at 0.
    ctor_set_uint64(o, 0, 0xDEAD_BEEF_CAFE_BABE);
    assert_eq!(ctor_get_uint64(o, 0), 0xDEAD_BEEF_CAFE_BABE);
    lean_dec(o);
}

#[test]
fn test_multi_scalar_ctor() {
    // Ctor with 1 object field + 12 bytes scalar: u32 at offset 8, u64 at offset 12.
    let ptr_sz = size_of::<LeanObjPtr>();
    let o = alloc_ctor_uninit(0, 1, 12);
    ctor_set(o, 0, lean_box(0));
    ctor_set_uint32(o, ptr_sz, 0xAAAA_BBBB);
    ctor_set_uint64(o, ptr_sz + 4, 0x1111_2222_3333_4444);
    assert_eq!(ctor_get_uint32(o, ptr_sz), 0xAAAA_BBBB);
    assert_eq!(ctor_get_uint64(o, ptr_sz + 4), 0x1111_2222_3333_4444);
    lean_dec(o);
}

// -- Public API wrappers (Part of #2005 Phase 2) --

#[test]
fn test_clean_is_exclusive() {
    let o = alloc_ctor(0, &[]);
    assert!(clean_is_exclusive(o));
    lean_inc(o);
    assert!(!clean_is_exclusive(o));
    lean_dec(o);
    lean_dec(o);
}

#[test]
fn test_clean_alloc_ctor() {
    let a = lean_box(10);
    let b = lean_box(20);
    let o = clean_alloc_ctor(1, 2, 0, &[a, b]);
    assert_eq!(obj_tag(o), 1);
    assert_eq!(ctor_get(o, 0), a);
    assert_eq!(ctor_get(o, 1), b);
    lean_dec(o);
}

#[test]
fn test_clean_alloc_ctor_scalar_only() {
    let o = clean_alloc_ctor(0, 0, 8, &[]);
    // SAFETY: All objects were allocated by test helpers above and are valid
    // for the duration of this test. Header dereferences are within bounds.
    unsafe {
        assert_eq!((*o).header.scalar_sz, 8);
        assert_eq!((*o).header.num_objs, 0);
    }
    lean_dec(o);
}

#[test]
fn test_clean_public_api_box_unbox() {
    let p = clean_box(42);
    assert_eq!(clean_unbox(p), 42);
    assert!(clean_is_scalar(p));

    let big = clean_box_uint64(0xDEAD_BEEF);
    assert_eq!(clean_unbox_uint64(big), 0xDEAD_BEEF);
    clean_dec(big);

    let f = clean_box_float(std::f64::consts::PI);
    assert_eq!(clean_unbox_float(f), std::f64::consts::PI);
    clean_dec(f);
}

#[test]
fn test_clean_public_api_refcount() {
    let o = alloc_ctor(0, &[]);
    clean_inc(o);
    assert!(!clean_is_exclusive(o));
    clean_inc_n(o, 2);
    // ref_count is now 3. Dec 3 times.
    clean_dec(o);
    clean_dec(o);
    clean_dec(o);
    assert!(clean_is_exclusive(o));
    clean_dec(o);
}

#[test]
fn test_clean_public_api_string() {
    let s = clean_mk_string("hello");
    // SAFETY: s is alive until clean_dec below. Part of #1923.
    assert_eq!(unsafe { string_as_str(s) }, "hello");
    clean_dec(s);
}

// -- Closure apply dispatch for arity 9-16 (Part of #1959) --

unsafe extern "C" fn sum_9(
    a0: LeanObjPtr,
    a1: LeanObjPtr,
    a2: LeanObjPtr,
    a3: LeanObjPtr,
    a4: LeanObjPtr,
    a5: LeanObjPtr,
    a6: LeanObjPtr,
    a7: LeanObjPtr,
    a8: LeanObjPtr,
) -> LeanObjPtr {
    let s = lean_unbox(a0)
        + lean_unbox(a1)
        + lean_unbox(a2)
        + lean_unbox(a3)
        + lean_unbox(a4)
        + lean_unbox(a5)
        + lean_unbox(a6)
        + lean_unbox(a7)
        + lean_unbox(a8);
    lean_box(s)
}

#[test]
fn test_closure_apply_arity_9() {
    let c = alloc_closure(sum_9 as *const (), 9, &[]);
    let args: Vec<LeanObjPtr> = (1..=9).map(lean_box).collect();
    let result = closure_apply(c, &args);
    assert_eq!(lean_unbox(result), 45); // 1+2+...+9 = 45
}

unsafe extern "C" fn sum_10(
    a0: LeanObjPtr,
    a1: LeanObjPtr,
    a2: LeanObjPtr,
    a3: LeanObjPtr,
    a4: LeanObjPtr,
    a5: LeanObjPtr,
    a6: LeanObjPtr,
    a7: LeanObjPtr,
    a8: LeanObjPtr,
    a9: LeanObjPtr,
) -> LeanObjPtr {
    let s = lean_unbox(a0)
        + lean_unbox(a1)
        + lean_unbox(a2)
        + lean_unbox(a3)
        + lean_unbox(a4)
        + lean_unbox(a5)
        + lean_unbox(a6)
        + lean_unbox(a7)
        + lean_unbox(a8)
        + lean_unbox(a9);
    lean_box(s)
}

#[test]
fn test_closure_apply_arity_10() {
    let c = alloc_closure(sum_10 as *const (), 10, &[]);
    let args: Vec<LeanObjPtr> = (1..=10).map(lean_box).collect();
    let result = closure_apply(c, &args);
    assert_eq!(lean_unbox(result), 55); // 1+2+...+10 = 55
}

unsafe extern "C" fn sum_16(
    a0: LeanObjPtr,
    a1: LeanObjPtr,
    a2: LeanObjPtr,
    a3: LeanObjPtr,
    a4: LeanObjPtr,
    a5: LeanObjPtr,
    a6: LeanObjPtr,
    a7: LeanObjPtr,
    a8: LeanObjPtr,
    a9: LeanObjPtr,
    a10: LeanObjPtr,
    a11: LeanObjPtr,
    a12: LeanObjPtr,
    a13: LeanObjPtr,
    a14: LeanObjPtr,
    a15: LeanObjPtr,
) -> LeanObjPtr {
    let s = lean_unbox(a0)
        + lean_unbox(a1)
        + lean_unbox(a2)
        + lean_unbox(a3)
        + lean_unbox(a4)
        + lean_unbox(a5)
        + lean_unbox(a6)
        + lean_unbox(a7)
        + lean_unbox(a8)
        + lean_unbox(a9)
        + lean_unbox(a10)
        + lean_unbox(a11)
        + lean_unbox(a12)
        + lean_unbox(a13)
        + lean_unbox(a14)
        + lean_unbox(a15);
    lean_box(s)
}

#[test]
fn test_closure_apply_arity_16() {
    let c = alloc_closure(sum_16 as *const (), 16, &[]);
    let args: Vec<LeanObjPtr> = (1..=16).map(lean_box).collect();
    let result = closure_apply(c, &args);
    assert_eq!(lean_unbox(result), 136); // 1+2+...+16 = 136
}

#[test]
fn test_closure_apply_arity_9_with_captured() {
    // Arity 9, 3 captured + 6 new = exact application
    let c = alloc_closure(
        sum_9 as *const (),
        9,
        &[lean_box(1), lean_box(2), lean_box(3)],
    );
    let new_args: Vec<LeanObjPtr> = (4..=9).map(lean_box).collect();
    let result = closure_apply(c, &new_args);
    assert_eq!(lean_unbox(result), 45); // 1+2+...+9 = 45
}

unsafe extern "C" fn add_captured_sum(captured: LeanObjPtr, next: LeanObjPtr) -> LeanObjPtr {
    lean_box(lean_unbox(captured) + lean_unbox(next))
}

unsafe extern "C" fn make_adder(a: LeanObjPtr, b: LeanObjPtr) -> LeanObjPtr {
    let captured = lean_box(lean_unbox(a) + lean_unbox(b));
    alloc_closure(add_captured_sum as *const (), 2, &[captured])
}

#[test]
fn test_closure_apply_over_application_recurses_into_result_closure() {
    let c = alloc_closure(make_adder as *const (), 2, &[]);
    let result = closure_apply(c, &[lean_box(10), lean_box(20), lean_box(3)]);
    assert_eq!(lean_unbox(result), 33);
}

// -- lean_reset Thunk/Task/External guard (Part of #2033) --

#[test]
fn test_reset_thunk_returns_null() {
    // Thunk-kind objects are not reusable: lean_reset must dec and return null.
    // Must use alloc_thunk — alloc_obj only allocates header-sized memory,
    // but lean_dealloc_obj reads ThunkObj.closure/value beyond the header.
    // SAFETY: All pointers are valid heap objects allocated in this test
    // and remain live for the duration of the unsafe block.
    let o = unsafe { alloc_thunk(std::ptr::null_mut()) };
    assert!(lean_is_unique(o));
    let slot = lean_reset(o);
    assert!(
        slot.is_null(),
        "lean_reset on Thunk must return null, got non-null"
    );
}

#[test]
fn test_reset_task_returns_null() {
    // Must use alloc_task — alloc_obj only allocates header-sized memory,
    // but lean_dealloc_obj reads TaskObj.value beyond the header.
    // SAFETY: All pointers are valid heap objects allocated in this test
    // and remain live for the duration of the unsafe block.
    let o = unsafe { alloc_task(std::ptr::null_mut()) };
    assert!(lean_is_unique(o));
    let slot = lean_reset(o);
    assert!(
        slot.is_null(),
        "lean_reset on Task must return null, got non-null"
    );
}

#[test]
fn test_reset_external_returns_null() {
    // Must use alloc_external (not alloc_obj) because lean_dec reads
    // ExternalObj.class for the finalize callback. alloc_obj only
    // allocates ObjHeader-sized memory, leaving class/data as garbage
    // → SIGSEGV when lean_dec dereferences (*ext).class.
    static CLASS: CleanExternalClass = CleanExternalClass {
        finalize: None,
        foreach: None,
    };
    // SAFETY: Pointers are valid heap objects allocated by the runtime.
    let o = unsafe { alloc_external(&CLASS, std::ptr::null_mut()) };
    assert!(lean_is_unique(o));
    let slot = lean_reset(o);
    assert!(
        slot.is_null(),
        "lean_reset on External must return null, got non-null"
    );
}

#[test]
fn test_reset_array_returns_null() {
    // Must use alloc_array — alloc_obj only allocates the base header,
    // but lean_dealloc_obj reads ArrayObj.capacity beyond the header.
    // Using alloc_obj here is UB (reads uninitialized memory).
    let o = alloc_array(0);
    assert!(lean_is_unique(o));
    let slot = lean_reset(o);
    assert!(
        slot.is_null(),
        "lean_reset on Array must return null, got non-null"
    );
}

#[test]
fn test_reset_str_unique_returns_slot() {
    // Str objects are reusable (same match arm as Ctor in lean_reset).
    // A unique string should return the original pointer for reuse.
    let s = mk_string("hello");
    assert!(lean_is_unique(s));
    let slot = lean_reset(s);
    assert!(
        !slot.is_null(),
        "lean_reset on unique Str must return non-null (reusable slot)"
    );
    assert_eq!(slot, s, "lean_reset on unique Str must return same pointer");
    // clean up: slot is still allocated, use lean_reuse to consume it.
    let reused = lean_reuse(slot, 0, 0, &[lean_box(1)]);
    lean_dec(reused);
}

#[test]
fn test_reset_str_shared_returns_null() {
    // A shared string should be dec'd and return null (not reusable).
    let s = mk_string("world");
    lean_inc(s); // ref_count 0 -> 1, now shared
    let slot = lean_reset(s);
    assert!(
        slot.is_null(),
        "lean_reset on shared Str must return null, got non-null"
    );
    // lean_reset dec'd once (rc 1 -> 0 but shared path doesn't free).
    // Need one more dec to free.
    lean_dec(s);
}
