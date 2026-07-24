// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kani harnesses: tagged pointers and layout computation.
//!
//! Verifies correctness of tagged pointer encoding/decoding and
//! layout computation for Ctor, Closure, and String objects.
//!
//! Run with: `cargo kani --features kani -p clean-runtime`
//!
//! Part of #1144

use super::{
    box_val, closure_layout, ctor_layout, is_scalar, string_layout, unbox_val, LeanObj, MAX_SMALL,
    OBJ_ALIGN,
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 1. Tagged pointer verification
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Verify box_val/unbox_val roundtrip for all valid small values.
///
/// Property: forall n in [0, MAX_SMALL]: unbox_val(box_val(n)) == n
#[kani::proof]
#[kani::unwind(1)]
fn verify_tagged_pointer_roundtrip_native() {
    let n: usize = kani::any();
    kani::assume(n <= MAX_SMALL);

    let tagged = box_val(n);
    assert!(
        is_scalar(tagged),
        "box_val must produce a scalar-tagged pointer"
    );
    assert_eq!(
        unbox_val(tagged),
        n,
        "unbox_val must recover original value"
    );
}

/// Verify tagged pointers always have the low bit set.
///
/// Property: forall n in [0, MAX_SMALL]: (box_val(n) as usize) & 1 == 1
#[kani::proof]
#[kani::unwind(1)]
fn verify_tagged_pointer_low_bit() {
    let n: usize = kani::any();
    kani::assume(n <= MAX_SMALL);

    let tagged = box_val(n);
    assert!(
        (tagged as usize) & 1 == 1,
        "tagged pointer must have low bit set"
    );
}

/// Verify that is_scalar correctly distinguishes tagged from heap pointers.
///
/// Property: A well-aligned heap allocation never has low bit set.
#[kani::proof]
#[kani::unwind(1)]
fn verify_is_scalar_alignment_distinction() {
    let addr: usize = kani::any();
    kani::assume(addr % OBJ_ALIGN == 0);
    kani::assume(addr != 0);

    let fake_heap = addr as *const LeanObj;
    assert!(
        !is_scalar(fake_heap),
        "aligned pointer must not be classified as scalar"
    );
}

/// Verify distinct small values produce distinct tagged pointers.
///
/// Property: forall a, b in [0, MAX_SMALL]: a != b => box_val(a) != box_val(b)
#[kani::proof]
#[kani::unwind(1)]
fn verify_tagged_pointer_injectivity() {
    let a: usize = kani::any();
    let b: usize = kani::any();
    kani::assume(a <= MAX_SMALL);
    kani::assume(b <= MAX_SMALL);
    kani::assume(a != b);

    assert_ne!(
        box_val(a),
        box_val(b),
        "distinct values must produce distinct tagged pointers"
    );
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 2. Layout computation verification
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Verify ctor_layout produces correctly sized layouts.
///
/// Property: layout.size() == sizeof(ObjHeader) + num_objs * sizeof(ptr) + scalar_sz
#[kani::proof]
#[kani::unwind(1)]
fn verify_ctor_layout_size() {
    let num_objs: u8 = kani::any();
    let scalar_sz: u8 = kani::any();

    let layout = ctor_layout(num_objs, scalar_sz);
    let expected_size = std::mem::size_of::<super::ObjHeader>()
        + (num_objs as usize) * std::mem::size_of::<*mut LeanObj>()
        + scalar_sz as usize;

    assert_eq!(layout.size(), expected_size, "ctor_layout size mismatch");
    assert_eq!(layout.align(), OBJ_ALIGN, "ctor_layout alignment mismatch");
}

/// Verify ctor_layout always produces a layout large enough for the header.
///
/// Property: layout.size() >= sizeof(ObjHeader) for all inputs
#[kani::proof]
#[kani::unwind(1)]
fn verify_ctor_layout_minimum_size() {
    let num_objs: u8 = kani::any();
    let scalar_sz: u8 = kani::any();

    let layout = ctor_layout(num_objs, scalar_sz);
    assert!(
        layout.size() >= std::mem::size_of::<super::ObjHeader>(),
        "ctor_layout must be at least ObjHeader size"
    );
}

/// Verify closure_layout produces correctly sized layouts.
///
/// Property: layout.size() == sizeof(LeanClosure) + num_fixed * sizeof(ptr)
#[kani::proof]
#[kani::unwind(1)]
fn verify_closure_layout_size_native() {
    let num_fixed: u16 = kani::any();
    kani::assume(num_fixed <= 256);

    let layout = closure_layout(num_fixed);
    let expected_size = std::mem::size_of::<super::LeanClosure>()
        + (num_fixed as usize) * std::mem::size_of::<*mut LeanObj>();

    assert_eq!(layout.size(), expected_size, "closure_layout size mismatch");
    assert_eq!(
        layout.align(),
        OBJ_ALIGN,
        "closure_layout alignment mismatch"
    );
}

/// Verify string_layout produces correctly sized layouts.
///
/// Property: layout.size() == sizeof(LeanString) + len + 1 (null terminator)
#[kani::proof]
#[kani::unwind(1)]
fn verify_string_layout_size_native() {
    let len: usize = kani::any();
    kani::assume(len <= 1024);

    let layout = string_layout(len);
    let expected_size = std::mem::size_of::<super::LeanString>() + len + 1;

    assert_eq!(layout.size(), expected_size, "string_layout size mismatch");
    assert_eq!(
        layout.align(),
        OBJ_ALIGN,
        "string_layout alignment mismatch"
    );
}

/// Verify ctor_layout size computation doesn't overflow for any valid inputs.
///
/// Property: For all u8 num_objs and scalar_sz, the size computation
/// sizeof(ObjHeader) + num_objs * sizeof(ptr) + scalar_sz fits in usize
/// without overflow (which would cause UB in Layout::from_size_align).
///
/// Max: 8 + 255*8 + 255 = 2303 — well within usize, but this verifies
/// the arithmetic doesn't have an unexpected overflow path.
#[kani::proof]
#[kani::unwind(1)]
fn verify_ctor_layout_no_overflow() {
    let num_objs: u8 = kani::any();
    let scalar_sz: u8 = kani::any();

    let header_sz = std::mem::size_of::<super::ObjHeader>();
    let ptr_sz = std::mem::size_of::<*mut LeanObj>();

    // Verify each step of the computation doesn't overflow
    let field_bytes = (num_objs as usize).checked_mul(ptr_sz);
    assert!(field_bytes.is_some(), "field bytes must not overflow");

    let subtotal = header_sz.checked_add(field_bytes.unwrap());
    assert!(subtotal.is_some(), "header + fields must not overflow");

    let total = subtotal.unwrap().checked_add(scalar_sz as usize);
    assert!(total.is_some(), "total size must not overflow");

    // Verify it matches what ctor_layout actually computes
    let layout = ctor_layout(num_objs, scalar_sz);
    assert_eq!(layout.size(), total.unwrap());
}
