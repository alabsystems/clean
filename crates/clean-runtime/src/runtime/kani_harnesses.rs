// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// -----------------------------------------------------------------------
// Layout consistency: alloc and dealloc must agree on size+align
// -----------------------------------------------------------------------

/// Verify obj_layout computes correct size for any (num_objs, scalar_sz).
///
/// Property: size == sizeof(ObjHeader) + num_objs * sizeof(ptr) + scalar_sz.
/// This is the foundational invariant for ctor alloc/dealloc — if the layout
/// computation is wrong, alloc::dealloc gets a mismatched layout and corrupts
/// the heap.
#[kani::proof]
fn verify_obj_layout_size() {
    let num_objs: u8 = kani::any();
    let scalar_sz: u8 = kani::any();

    let layout = obj_layout(num_objs, scalar_sz);

    let expected_size = std::mem::size_of::<ObjHeader>()
        + (num_objs as usize) * std::mem::size_of::<LeanObjPtr>()
        + scalar_sz as usize;
    assert_eq!(layout.size(), expected_size);

    // Alignment must be at least pointer-aligned (8 on 64-bit).
    let expected_align = std::mem::align_of::<ObjHeader>().max(std::mem::align_of::<LeanObjPtr>());
    assert_eq!(layout.align(), expected_align);
}

/// Verify closure_layout computes correct size.
///
/// Property: size == sizeof(ClosureObj) + num_fixed * sizeof(ptr).
/// lean_dec reads ClosureObj.num_fixed to compute this layout — mismatch
/// means heap corruption on dealloc.
#[kani::proof]
fn verify_closure_layout_size() {
    let num_fixed: u16 = kani::any();
    // Bound to prevent Kani state explosion (256 * 8 = 2KB max, reasonable).
    kani::assume(num_fixed <= 256);

    let layout = closure_layout(num_fixed);

    let expected_size = std::mem::size_of::<ClosureObj>()
        + (num_fixed as usize) * std::mem::size_of::<LeanObjPtr>();
    assert_eq!(layout.size(), expected_size);
    assert_eq!(layout.align(), std::mem::align_of::<ClosureObj>());
}

/// Verify string_layout computes correct size.
///
/// Property: size == sizeof(StringObj) + len + 1 (NUL terminator).
/// lean_dec reads StringObj.len to compute this — wrong size = heap corruption.
#[kani::proof]
fn verify_string_layout_size() {
    let len: usize = kani::any();
    kani::assume(len <= 1024);

    let layout = string_layout(len);

    let expected_size = std::mem::size_of::<StringObj>() + len + 1;
    assert_eq!(layout.size(), expected_size);
    assert_eq!(layout.align(), std::mem::align_of::<StringObj>());
}

// -----------------------------------------------------------------------
// ObjKind roundtrip: from_u8(v) as u8 == v for valid discriminants
// -----------------------------------------------------------------------

/// Verify ObjKind::from_u8 is a faithful inverse of the repr(u8) discriminant.
///
/// If this fails, lean_dec would compute the wrong dealloc layout based on
/// a corrupted kind dispatch.
#[kani::proof]
fn verify_objkind_roundtrip() {
    let v: u8 = kani::any();
    kani::assume(v <= 6); // Valid ObjKind range: 0..=6

    let kind = ObjKind::from_u8(v);
    assert_eq!(kind as u8, v);
}

// -----------------------------------------------------------------------
// Tagged pointer roundtrip: lean_box → lean_unbox for all valid values
// -----------------------------------------------------------------------

/// Verify tagged pointer encoding/decoding is lossless for all valid values.
///
/// Property: lean_unbox(lean_box(n)) == n for all n in 0..=MAX_SMALL.
/// Also verifies is_scalar correctly identifies tagged pointers.
#[kani::proof]
fn verify_tagged_pointer_roundtrip() {
    let n: usize = kani::any();
    kani::assume(n <= MAX_SMALL);

    let p = lean_box(n);
    assert!(
        is_scalar(p),
        "lean_box must produce a scalar-tagged pointer"
    );
    assert_eq!(
        lean_unbox(p),
        n,
        "lean_unbox must recover the original value"
    );
}

/// Verify tagged pointer bit pattern doesn't alias valid heap pointers.
///
/// Property: any lean_box result has bit 0 set, which means it can never
/// be confused with a properly-aligned heap pointer (alignment >= 4).
#[kani::proof]
fn verify_tagged_pointer_bit_set() {
    let n: usize = kani::any();
    kani::assume(n <= MAX_SMALL);

    let p = lean_box(n);
    assert_ne!(p as usize & 1, 0, "tagged pointer must have bit 0 set");
}

// -----------------------------------------------------------------------
// Alloc/dealloc roundtrip: header is correctly initialized and readable
// -----------------------------------------------------------------------

/// Verify alloc_obj initializes header fields correctly and the dealloc
/// layout matches the alloc layout.
///
/// This is the critical alloc/dealloc consistency property: lean_dec reads
/// header.num_objs and header.scalar_sz to compute the dealloc layout.
/// If alloc_obj writes different values than what lean_dec reads, heap
/// corruption follows.
#[kani::proof]
fn verify_alloc_header_roundtrip() {
    let tag: u8 = kani::any();
    let num_objs: u8 = kani::any();
    let scalar_sz: u8 = kani::any();
    // Bound to keep allocation reasonable for Kani's memory model.
    kani::assume(num_objs <= 8);
    kani::assume(scalar_sz <= 32);

    let o = alloc_obj(tag, ObjKind::Ctor, num_objs, scalar_sz);
    assert!(!o.is_null());

    // SAFETY: The object was returned by an allocator above and is non-null (asserted).
    // Dereferencing the header to verify fields is valid for the lifetime of the object.
    unsafe {
        // Header fields must match what was passed to alloc_obj.
        assert_eq!((*o).header.tag, tag);
        assert_eq!((*o).header.kind, ObjKind::Ctor as u8);
        assert_eq!((*o).header.num_objs, num_objs);
        assert_eq!((*o).header.scalar_sz, scalar_sz);
        // ref_count starts at 0 (uniquely owned).
        assert_eq!((*o).header.ref_count.load(Ordering::Relaxed), 0);

        // The layout lean_dec would compute from these header fields must
        // match the layout used for allocation.
        let alloc_layout = obj_layout(num_objs, scalar_sz);
        let dealloc_layout = obj_layout((*o).header.num_objs, (*o).header.scalar_sz);
        assert_eq!(alloc_layout.size(), dealloc_layout.size());
        assert_eq!(alloc_layout.align(), dealloc_layout.align());

        alloc::dealloc(o as *mut u8, alloc_layout);
    }
}

// -----------------------------------------------------------------------
// Ctor field access: pointer arithmetic stays within bounds
// -----------------------------------------------------------------------

/// Verify ctor_get and ctor_set access the correct fields after allocation.
///
/// Property: alloc_ctor with fields → ctor_get reads back the same values.
/// This proves the pointer arithmetic in fields_ptr + add(idx) is correct.
#[kani::proof]
fn verify_ctor_field_roundtrip() {
    let tag: u8 = kani::any();
    let num_fields: usize = kani::any();
    kani::assume(num_fields >= 1 && num_fields <= 4);

    // Use tagged scalars as field values (no heap children).
    let mut fields: [LeanObjPtr; 4] = [std::ptr::null_mut(); 4];
    for i in 0..num_fields {
        fields[i] = lean_box(i);
    }

    let o = alloc_ctor(tag, &fields[..num_fields]);
    assert!(!o.is_null());

    // Read back each field and verify it matches.
    for i in 0..num_fields {
        let got = ctor_get(o, i);
        assert_eq!(
            got, fields[i],
            "ctor_get({i}) must return the value written by alloc_ctor"
        );
    }

    // Verify ctor_set updates correctly.
    let new_val = lean_box(42);
    let idx: usize = kani::any();
    kani::assume(idx < num_fields);
    ctor_set(o, idx, new_val);
    assert_eq!(ctor_get(o, idx), new_val);

    lean_dec(o);
}

// -----------------------------------------------------------------------
// Closure alloc/dealloc: layout consistency through ClosureObj fields
// -----------------------------------------------------------------------

/// Verify closure allocation initializes ClosureObj fields correctly and
/// the dealloc layout (computed from num_fixed) matches the alloc layout.
///
/// This catches the closure child-count split risk: header.num_objs is not
/// authoritative for closures and must stay zero, while ClosureObj.num_fixed
/// carries the captured-argument count used by deallocation. This harness
/// verifies the shared-core contract used by both runtime facades.
#[kani::proof]
fn verify_closure_alloc_fields() {
    let arity: u16 = kani::any();
    kani::assume(arity >= 1 && arity <= 8);

    let num_args: usize = kani::any();
    kani::assume(num_args <= 4);
    kani::assume(num_args < arity as usize); // under-application

    // Tagged scalars as captured args.
    let mut args: [LeanObjPtr; 4] = [std::ptr::null_mut(); 4];
    for i in 0..num_args {
        args[i] = lean_box(i);
    }

    let func_ptr = std::ptr::null::<()>(); // Won't be called
    let o = alloc_closure(func_ptr, arity, &args[..num_args]);
    assert!(!o.is_null());

    // SAFETY: The object was returned by an allocator above and is non-null (asserted).
    // Dereferencing the header to verify fields is valid for the lifetime of the object.
    unsafe {
        let c = o as *const ClosureObj;

        // Verify ClosureObj fields.
        assert_eq!((*c).func, func_ptr);
        assert_eq!((*c).arity, arity);
        assert_eq!((*c).num_fixed, num_args as u16);
        assert_eq!((*c).header.kind, ObjKind::Closure as u8);

        // Shared closure contract: header.num_objs stays zero and child count
        // comes from num_fixed.
        assert_eq!((*c).header.num_objs, 0);
        assert_eq!(obj_child_count(o), num_args);

        // Layout that lean_dec would compute (reads num_fixed, not num_objs).
        let alloc_layout = closure_layout(num_args as u16);
        let dealloc_layout = closure_layout((*c).num_fixed);
        assert_eq!(alloc_layout.size(), dealloc_layout.size());
        assert_eq!(alloc_layout.align(), dealloc_layout.align());

        // Captured args must be readable.
        let args_ptr = ClosureObj::args_ptr(o as *mut ClosureObj);
        for i in 0..num_args {
            let arg = *args_ptr.add(i);
            assert!(is_scalar(arg));
            assert_eq!(lean_unbox(arg), i);
        }

        alloc::dealloc(o as *mut u8, alloc_layout);
    }
}

// -----------------------------------------------------------------------
// Reference counting: inc/dec arithmetic correctness
// -----------------------------------------------------------------------

/// Verify that N increments followed by N decrements returns ref_count to 0.
///
/// Property: after alloc (rc=0), inc N times (rc=N), dec N times (rc=0),
/// the object is uniquely owned again. This verifies the atomic arithmetic
/// doesn't overflow or underflow for reasonable reference counts.
#[kani::proof]
fn verify_refcount_inc_dec_roundtrip() {
    let n: u32 = kani::any();
    kani::assume(n >= 1 && n <= 16);

    let o = alloc_ctor(0, &[]);
    assert!(lean_is_unique(o), "freshly allocated must be unique (rc=0)");

    // Increment N times: rc goes from 0 to N.
    for _ in 0..n {
        lean_inc(o);
    }
    assert!(
        !lean_is_unique(o),
        "after inc, object must not be unique (rc > 0)"
    );

    // Decrement N times: rc goes from N back to 0.
    // Each dec should NOT free because old > 0.
    for _ in 0..n {
        // SAFETY: `o` is a valid heap object allocated above. The ref_count was
        // incremented N times, so fetch_sub is valid and will not underflow.
        unsafe {
            let old = (*o).header.ref_count.fetch_sub(1, Ordering::Release);
            assert!(old > 0, "dec must not underflow to free prematurely");
        }
    }

    // Now rc is back to 0 (unique).
    assert!(
        lean_is_unique(o),
        "after N inc + N dec, must be unique again"
    );

    // clean up.
    lean_dec(o);
}

// -----------------------------------------------------------------------
// lean_reuse: same-arity reuse preserves layout consistency
// -----------------------------------------------------------------------

/// Verify lean_reuse with a null slot allocates a fresh ctor correctly.
///
/// Property: lean_reuse(null, tag, scalar_sz, fields) behaves identically
/// to alloc_ctor_uninit + field writes.
#[kani::proof]
fn verify_lean_reuse_null_slot() {
    let tag: u8 = kani::any();
    let scalar_sz: u8 = kani::any();
    kani::assume(scalar_sz <= 16);

    let num_fields: usize = kani::any();
    kani::assume(num_fields <= 3);

    let mut fields: [LeanObjPtr; 3] = [std::ptr::null_mut(); 3];
    for i in 0..num_fields {
        fields[i] = lean_box(i);
    }

    let o = lean_reuse(std::ptr::null_mut(), tag, scalar_sz, &fields[..num_fields]);
    assert!(!o.is_null());

    // SAFETY: The object was returned by an allocator above and is non-null (asserted).
    // Dereferencing the header to verify fields is valid for the lifetime of the object.
    unsafe {
        assert_eq!((*o).header.tag, tag);
        assert_eq!((*o).header.kind, ObjKind::Ctor as u8);
        assert_eq!((*o).header.num_objs, num_fields as u8);
        assert_eq!((*o).header.scalar_sz, scalar_sz);
    }

    for i in 0..num_fields {
        assert_eq!(ctor_get(o, i), fields[i]);
    }

    lean_dec(o);
}

/// Verify lean_reuse with a same-arity ctor slot produces a valid object
/// with correct header and accessible fields.
///
/// Property: after reset + reuse with same num_objs, the object's header
/// is consistent and lean_dec would compute the correct dealloc layout.
#[kani::proof]
fn verify_lean_reuse_same_arity() {
    let tag1: u8 = kani::any();
    let tag2: u8 = kani::any();
    let num_fields: usize = kani::any();
    kani::assume(num_fields >= 1 && num_fields <= 3);

    // Allocate original ctor with scalar children.
    let mut fields1: [LeanObjPtr; 3] = [std::ptr::null_mut(); 3];
    for i in 0..num_fields {
        fields1[i] = lean_box(i);
    }
    let o = alloc_ctor(tag1, &fields1[..num_fields]);

    // Reset (since unique, returns the slot for reuse).
    let slot = lean_reset(o);
    assert!(
        !slot.is_null(),
        "unique ctor reset must return non-null slot"
    );

    // Reuse with same arity but different tag and field values.
    let mut fields2: [LeanObjPtr; 3] = [std::ptr::null_mut(); 3];
    for i in 0..num_fields {
        fields2[i] = lean_box(100 + i);
    }
    let reused = lean_reuse(slot, tag2, 0, &fields2[..num_fields]);
    assert!(!reused.is_null());

    // Verify header.
    // SAFETY: The object was returned by an allocator above and is non-null (asserted).
    // Dereferencing the header to verify fields is valid for the lifetime of the object.
    unsafe {
        assert_eq!((*reused).header.tag, tag2);
        assert_eq!((*reused).header.kind, ObjKind::Ctor as u8);
        assert_eq!((*reused).header.num_objs, num_fields as u8);
    }

    // Verify fields.
    for i in 0..num_fields {
        assert_eq!(ctor_get(reused, i), fields2[i]);
    }

    lean_dec(reused);
}

// -----------------------------------------------------------------------
// lean_dec: dealloc dispatch correctness for different object kinds
// -----------------------------------------------------------------------

/// Verify lean_dec correctly frees a uniquely-owned ctor with scalar children.
///
/// Property: lean_dec on a unique ctor (rc=0) with only scalar children
/// does not panic or corrupt memory. This exercises the Ctor branch of
/// lean_dec's dealloc dispatch.
#[kani::proof]
fn verify_lean_dec_ctor_scalar_children() {
    let tag: u8 = kani::any();
    let num_fields: usize = kani::any();
    kani::assume(num_fields <= 4);

    let mut fields: [LeanObjPtr; 4] = [std::ptr::null_mut(); 4];
    for i in 0..num_fields {
        fields[i] = lean_box(i);
    }

    let o = alloc_ctor(tag, &fields[..num_fields]);
    assert!(lean_is_unique(o));

    // lean_dec should free without error (all children are scalars = no-op dec).
    lean_dec(o);
}

/// Verify lean_dec on a scalar is a no-op (doesn't dereference the pointer).
#[kani::proof]
fn verify_lean_dec_scalar_noop() {
    let n: usize = kani::any();
    kani::assume(n <= MAX_SMALL);

    let p = lean_box(n);
    // Must not dereference the tagged pointer — it's not a heap address.
    lean_dec(p);
}

/// Verify lean_dec on a shared object decrements but does not free.
#[kani::proof]
fn verify_lean_dec_shared_no_free() {
    let o = alloc_ctor(0, &[lean_box(0)]);
    lean_inc(o); // rc: 0 → 1

    // First dec: rc 1 → 0, should NOT free (old=1, old != 0).
    lean_dec(o);

    // Object should still be accessible (unique now).
    assert!(lean_is_unique(o));
    assert_eq!(ctor_get(o, 0), lean_box(0));

    // Second dec: rc 0, old=0, should free.
    lean_dec(o);
}

// -----------------------------------------------------------------------
// fields_ptr / scalar_ptr: pointer arithmetic within allocation bounds
// -----------------------------------------------------------------------

/// Verify fields_ptr returns a pointer within the allocated region.
///
/// Property: fields_ptr(o) == o + sizeof(ObjHeader), which is the start
/// of the flexible tail. The returned pointer must be within the allocated
/// size.
#[kani::proof]
fn verify_fields_ptr_offset() {
    let num_objs: u8 = kani::any();
    let scalar_sz: u8 = kani::any();
    kani::assume(num_objs <= 8);
    kani::assume(scalar_sz <= 32);

    let o = alloc_obj(0, ObjKind::Ctor, num_objs, scalar_sz);

    // SAFETY: `o` was allocated by alloc_obj with the given num_objs/scalar_sz.
    // Pointer arithmetic via fields_ptr and scalar_ptr stays within the allocation.
    unsafe {
        let fields = CleanObj::fields_ptr(o);
        let base = o as usize;
        let fields_addr = fields as usize;

        // fields_ptr must be exactly sizeof(ObjHeader) bytes after the object.
        assert_eq!(fields_addr - base, std::mem::size_of::<ObjHeader>());

        // scalar_ptr must be after all pointer fields.
        let scalars = CleanObj::scalar_ptr(o);
        let scalars_addr = scalars as usize;
        let expected_scalar_offset = std::mem::size_of::<ObjHeader>()
            + (num_objs as usize) * std::mem::size_of::<LeanObjPtr>();
        assert_eq!(scalars_addr - base, expected_scalar_offset);

        // Both pointers must be within the allocated region.
        let layout = obj_layout(num_objs, scalar_sz);
        let end = base + layout.size();
        assert!(fields_addr <= end);
        assert!(scalars_addr <= end);

        alloc::dealloc(o as *mut u8, layout);
    }
}

// -----------------------------------------------------------------------
// Box/unbox roundtrip: heap-allocated typed values
// -----------------------------------------------------------------------

/// Verify box_uint64 / unbox_uint64 roundtrip for all u64 values.
///
/// Property: unbox_uint64(box_uint64(n)) == n. Both paths go through
/// scalar_ptr, so this also verifies scalar_ptr correctness for zero-field
/// objects (num_objs=0, scalar_sz=8).
#[kani::proof]
fn verify_box_unbox_uint64_roundtrip() {
    let n: u64 = kani::any();

    let o = box_uint64(n);
    assert!(!is_scalar(o), "box_uint64 must heap-allocate");
    let result = unbox_uint64(o);
    assert_eq!(result, n, "unbox_uint64 must recover original value");

    lean_dec(o);
}

/// Verify box_uint32 / unbox_uint32 roundtrip.
///
/// Property: unbox_uint32(box_uint32(n)) == n for ALL u32 values.
/// box_uint32 uses tagged pointers when `n <= MAX_SMALL` and heap allocation
/// otherwise. On 64-bit targets that covers all `u32` values; on narrower
/// targets the heap path is still possible.
#[kani::proof]
fn verify_box_unbox_uint32_roundtrip() {
    let n: u32 = kani::any();

    let o = box_uint32(n);
    let result = unbox_uint32(o);
    assert_eq!(result, n, "unbox_uint32 must recover original value");

    // Only dec heap-allocated boxes.
    if !is_scalar(o) {
        lean_dec(o);
    }
}

/// Verify box_float / unbox_float roundtrip for ALL f64 values including NaN.
///
/// Property: unbox_float(box_float(f)).to_bits() == f.to_bits() for all f64.
/// Uses bit-level comparison so NaN values are correctly verified (NaN != NaN
/// under IEEE 754 but their bit patterns must roundtrip exactly).
#[kani::proof]
fn verify_box_unbox_float_roundtrip() {
    let f: f64 = kani::any();

    let o = box_float(f);
    assert!(!is_scalar(o), "box_float must heap-allocate");
    let result = unbox_float(o);
    assert_eq!(
        result.to_bits(),
        f.to_bits(),
        "unbox_float must recover exact bit pattern"
    );

    lean_dec(o);
}

// -----------------------------------------------------------------------
// String alloc/data/len roundtrip
// -----------------------------------------------------------------------

/// Verify mk_string / string_data / string_len roundtrip.
///
/// Property: string_data returns the exact bytes passed to mk_string,
/// and string_len returns the correct byte length. This exercises
/// StringObj::data_ptr pointer arithmetic, copy_nonoverlapping, and
/// from_raw_parts.
#[kani::proof]
fn verify_string_alloc_data_len_roundtrip() {
    // Use a bounded symbolic length for tractability.
    let len: usize = kani::any();
    kani::assume(len <= 8);

    // Build a symbolic byte array.
    let mut buf = [0u8; 8];
    for i in 0..len {
        buf[i] = kani::any();
    }

    let s = std::str::from_utf8(&buf[..len]);
    // Only test valid UTF-8 (mk_string takes &str).
    kani::assume(s.is_ok());
    let s = s.expect("invariant: kani::assume(s.is_ok()) above");

    let o = mk_string(s);
    assert!(!is_scalar(o));

    // Verify length.
    assert_eq!(string_len(o), len);

    // Verify data bytes match.
    // SAFETY: o is alive until lean_dec below. Part of #1923.
    let data = unsafe { string_data(o) };
    assert_eq!(data.len(), len);
    for i in 0..len {
        assert_eq!(data[i], buf[i]);
    }

    lean_dec(o);
}

// -----------------------------------------------------------------------
// Scalar field read/write roundtrip via ctor_set/get
// -----------------------------------------------------------------------

/// Verify ctor_set_uint8 / ctor_get_uint8 roundtrip.
///
/// Property: writing a u8 value at a given offset and reading it back
/// returns the same value. The offset calculation accounts for num_objs
/// pointer fields before the scalar region.
#[kani::proof]
fn verify_scalar_uint8_roundtrip() {
    let num_objs: u8 = kani::any();
    kani::assume(num_objs <= 4);
    let scalar_sz: u8 = 8; // Enough room for any single scalar type

    let o = alloc_ctor_uninit(0, num_objs, scalar_sz);
    // Initialize pointer fields to scalars to avoid UB on lean_dec.
    for i in 0..num_objs as usize {
        ctor_set(o, i, lean_box(0));
    }

    let val: u8 = kani::any();
    // Offset into scalar region: num_objs * sizeof(ptr) places us at scalar start.
    let offset = num_objs as usize * std::mem::size_of::<LeanObjPtr>();
    ctor_set_uint8(o, offset, val);
    assert_eq!(ctor_get_uint8(o, offset), val);

    lean_dec(o);
}

/// Verify ctor_set_uint32 / ctor_get_uint32 roundtrip via unaligned read/write.
///
/// Property: write_unaligned + read_unaligned roundtrips correctly for u32
/// values in the scalar region, even at non-aligned offsets.
#[kani::proof]
fn verify_scalar_uint32_roundtrip() {
    let num_objs: u8 = kani::any();
    kani::assume(num_objs <= 2);
    let scalar_sz: u8 = 8;

    let o = alloc_ctor_uninit(0, num_objs, scalar_sz);
    for i in 0..num_objs as usize {
        ctor_set(o, i, lean_box(0));
    }

    let val: u32 = kani::any();
    let offset = num_objs as usize * std::mem::size_of::<LeanObjPtr>();
    ctor_set_uint32(o, offset, val);
    assert_eq!(ctor_get_uint32(o, offset), val);

    lean_dec(o);
}

/// Verify ctor_set_uint64 / ctor_get_uint64 roundtrip via unaligned read/write.
#[kani::proof]
fn verify_scalar_uint64_roundtrip() {
    let num_objs: u8 = kani::any();
    kani::assume(num_objs <= 2);
    let scalar_sz: u8 = 8;

    let o = alloc_ctor_uninit(0, num_objs, scalar_sz);
    for i in 0..num_objs as usize {
        ctor_set(o, i, lean_box(0));
    }

    let val: u64 = kani::any();
    let offset = num_objs as usize * std::mem::size_of::<LeanObjPtr>();
    ctor_set_uint64(o, offset, val);
    assert_eq!(ctor_get_uint64(o, offset), val);

    lean_dec(o);
}

/// Verify ctor_set_float / ctor_get_float roundtrip via unaligned read/write.
///
/// Uses bit-level comparison to cover ALL f64 values including NaN.
#[kani::proof]
fn verify_scalar_float_roundtrip() {
    let val: f64 = kani::any();

    let o = alloc_ctor_uninit(0, 0, 8);
    ctor_set_float(o, 0, val);
    let result = ctor_get_float(o, 0);
    assert_eq!(
        result.to_bits(),
        val.to_bits(),
        "ctor_get_float must recover exact bit pattern"
    );

    lean_dec(o);
}

// -----------------------------------------------------------------------
// lean_dec: closure deallocation
// -----------------------------------------------------------------------

/// Verify lean_dec correctly frees a uniquely-owned closure with scalar args.
///
/// Property: lean_dec on a unique closure (rc=0) with only scalar captured
/// args does not panic or corrupt memory. Exercises the Closure branch of
/// lean_dec's dealloc dispatch, including num_fixed (u16) read path.
#[kani::proof]
fn verify_lean_dec_closure_scalar_args() {
    let arity: u16 = kani::any();
    kani::assume(arity >= 1 && arity <= 8);

    let num_args: usize = kani::any();
    kani::assume(num_args >= 1 && num_args <= 4);
    kani::assume(num_args < arity as usize);

    let mut args: [LeanObjPtr; 4] = [std::ptr::null_mut(); 4];
    for i in 0..num_args {
        args[i] = lean_box(i);
    }

    let func_ptr = std::ptr::null::<()>();
    let o = alloc_closure(func_ptr, arity, &args[..num_args]);
    assert!(lean_is_unique(o));

    // lean_dec should free without error: all captured args are scalars.
    lean_dec(o);
}

// -----------------------------------------------------------------------
// lean_dec: nested heap children (recursive deallocation)
// -----------------------------------------------------------------------

/// Verify lean_dec correctly frees a ctor whose children are heap-allocated
/// ctors (exercises the recursive / tail-child deallocation path).
///
/// Property: lean_dec on a ctor with 2 heap-allocated children frees the
/// entire tree without memory corruption. The first child is dec'd via
/// recursive call; the last child is dec'd via tail-loop optimization.
#[kani::proof]
fn verify_lean_dec_heap_children() {
    // Allocate two leaf ctors (scalar children only).
    let leaf1 = alloc_ctor(1, &[lean_box(10)]);
    let leaf2 = alloc_ctor(2, &[lean_box(20)]);

    // Allocate parent ctor with two heap children.
    let parent = alloc_ctor(0, &[leaf1, leaf2]);
    assert!(lean_is_unique(parent));
    assert!(lean_is_unique(leaf1));
    assert!(lean_is_unique(leaf2));

    // lean_dec should recursively free leaf1 (recursive call on child 0),
    // then tail-loop into leaf2 (last child optimization).
    lean_dec(parent);
}

// -----------------------------------------------------------------------
// lean_reuse: closure slot triggers dealloc + fresh alloc path
// -----------------------------------------------------------------------

/// Verify lean_reuse with a closure slot correctly deallocates the closure
/// and allocates a fresh ctor.
///
/// Property: when the reset_slot is a Closure (kind != Ctor), lean_reuse
/// deallocates it using closure_layout(num_fixed) and allocates a fresh
/// ctor. The resulting object has correct header and accessible fields.
#[kani::proof]
fn verify_lean_reuse_closure_slot_deallocs() {
    let arity: u16 = 3;
    let num_args: usize = 1;

    // Allocate a closure with one scalar captured arg.
    let c = alloc_closure(std::ptr::null::<()>(), arity, &[lean_box(0)]);
    assert!(lean_is_unique(c));

    // Reset the closure — since unique, returns it as a slot.
    let slot = lean_reset(c);
    // lean_reset on a non-Ctor kind (Array/Thunk/Task/External) returns null,
    // but Closure IS handled: children are dec'd and the slot is returned.
    assert!(
        !slot.is_null(),
        "unique closure reset must return non-null slot"
    );

    // Reuse with a ctor. Since slot.kind == Closure != Ctor, lean_reuse
    // deallocates the closure slot and allocates a fresh ctor.
    let tag: u8 = kani::any();
    let o = lean_reuse(slot, tag, 0, &[lean_box(42)]);
    assert!(!o.is_null());

    // SAFETY: The object was returned by an allocator above and is non-null (asserted).
    // Dereferencing the header to verify fields is valid for the lifetime of the object.
    unsafe {
        assert_eq!((*o).header.tag, tag);
        assert_eq!((*o).header.kind, ObjKind::Ctor as u8);
        assert_eq!((*o).header.num_objs, 1);
    }
    assert_eq!(ctor_get(o, 0), lean_box(42));

    lean_dec(o);
}

// -----------------------------------------------------------------------
// Scalar roundtrip: uint16 (gap from initial harness set)
// -----------------------------------------------------------------------

/// Verify ctor_set_uint16 / ctor_get_uint16 roundtrip via unaligned read/write.
///
/// Property: write_unaligned(v) followed by read_unaligned at the same offset
/// recovers the original value for all u16 values.
#[kani::proof]
fn verify_scalar_uint16_roundtrip() {
    let val: u16 = kani::any();

    // Allocate ctor with 0 pointer fields and 2 bytes of scalar space.
    let o = alloc_ctor_uninit(0, 0, 2);
    ctor_set_uint16(o, 0, val);
    let result = ctor_get_uint16(o, 0);
    assert_eq!(result, val, "ctor_get_uint16 must recover original value");

    lean_dec(o);
}

// -----------------------------------------------------------------------
// Scalar roundtrip: float32 (gap from initial harness set)
// -----------------------------------------------------------------------

/// Verify ctor_set_float32 / ctor_get_float32 roundtrip via unaligned read/write.
///
/// Uses bit-level comparison to cover ALL f32 values including NaN.
#[kani::proof]
fn verify_scalar_float32_roundtrip() {
    let val: f32 = kani::any();

    // Allocate ctor with 0 pointer fields and 4 bytes of scalar space.
    let o = alloc_ctor_uninit(0, 0, 4);
    ctor_set_float32(o, 0, val);
    let result = ctor_get_float32(o, 0);
    assert_eq!(
        result.to_bits(),
        val.to_bits(),
        "ctor_get_float32 must recover exact bit pattern"
    );

    lean_dec(o);
}

// -----------------------------------------------------------------------
// Scalar roundtrip: usize (gap from initial harness set)
// -----------------------------------------------------------------------

/// Verify ctor_set_usize / ctor_get_usize roundtrip.
///
/// Unlike other scalar accessors, usize uses slot-index addressing (not byte
/// offset) because usize fields are pointer-sized. The slot index must be
/// >= num_objs to address the scalar region. We allocate a ctor with 0
/// pointer fields so slot 0 is the first scalar slot.
#[kani::proof]
fn verify_scalar_usize_roundtrip() {
    let val: usize = kani::any();

    // Allocate ctor with 0 pointer fields but enough scalar space for 1 usize.
    // scalar_sz is in bytes; usize is 8 bytes on 64-bit.
    let o = alloc_ctor_uninit(0, 0, std::mem::size_of::<usize>() as u8);
    ctor_set_usize(o, 0, val);
    let result = ctor_get_usize(o, 0);
    assert_eq!(result, val, "ctor_get_usize must recover original value");

    lean_dec(o);
}

// -----------------------------------------------------------------------
// Tag mutation: ctor_set_tag (gap from initial harness set)
// -----------------------------------------------------------------------

/// Verify ctor_set_tag correctly updates the header tag field.
///
/// Property: after ctor_set_tag(o, new_tag), obj_tag(o) == new_tag.
/// This exercises the unsafe header.tag write. Incorrect mutation could
/// corrupt the ObjKind or other header fields.
#[kani::proof]
fn verify_ctor_set_tag() {
    let original_tag: u8 = kani::any();
    let new_tag: u8 = kani::any();

    let o = alloc_ctor_uninit(original_tag, 0, 0);
    assert_eq!(obj_tag(o), original_tag);

    ctor_set_tag(o, new_tag);
    assert_eq!(obj_tag(o), new_tag, "ctor_set_tag must update header tag");

    // Verify that set_tag didn't corrupt the kind field.
    // SAFETY: The object was returned by an allocator above and is non-null (asserted).
    // Dereferencing the header to verify fields is valid for the lifetime of the object.
    unsafe {
        assert_eq!(
            (*o).header.kind,
            ObjKind::Ctor as u8,
            "ctor_set_tag must not corrupt kind field"
        );
    }

    lean_dec(o);
}
