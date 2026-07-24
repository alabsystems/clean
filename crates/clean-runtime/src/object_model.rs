// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Canonical object-model helpers shared by `native` and `runtime`.
//! Part of #2827.

use std::alloc::{self, Layout};
use std::mem::{align_of, size_of};
use std::sync::atomic::AtomicU32;

pub(crate) const TAG_BIT: usize = 1;
pub const MAX_SMALL: usize = usize::MAX >> 1;
pub(crate) const OBJ_ALIGN: usize = align_of::<usize>();

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjKind {
    Ctor = 0,
    Closure = 1,
    Array = 2,
    Str = 3,
    Thunk = 4,
    Task = 5,
    External = 6,
}

impl ObjKind {
    pub(crate) fn from_u8(v: u8) -> Self {
        match v {
            0 => Self::Ctor,
            1 => Self::Closure,
            2 => Self::Array,
            3 => Self::Str,
            4 => Self::Thunk,
            5 => Self::Task,
            6 => Self::External,
            _ => lean_panic("invalid ObjKind"),
        }
    }
}

#[repr(C)]
pub struct ObjHeader {
    pub(crate) ref_count: AtomicU32,
    pub(crate) tag: u8,
    pub(crate) kind: u8,
    pub(crate) num_objs: u8,
    pub(crate) scalar_sz: u8,
}

#[repr(C)]
pub struct CleanObj {
    pub(crate) header: ObjHeader,
}

pub type LeanObjPtr = *mut CleanObj;

impl CleanObj {
    #[inline]
    pub(crate) unsafe fn fields_ptr(ptr: *mut Self) -> *mut LeanObjPtr {
        // SAFETY: Delegates to obj_fields_ptr. Caller guarantees `ptr` is a
        // valid heap-allocated CleanObj, so the header-sized offset lands
        // within the allocation at the start of the fields region.
        unsafe { obj_fields_ptr(ptr) }
    }

    #[inline]
    pub(crate) unsafe fn scalar_ptr(ptr: *mut Self) -> *mut u8 {
        // SAFETY: Delegates to ctor_scalar_ptr. Caller guarantees `ptr` is a
        // valid Ctor object with enough allocation for header + fields + scalar.
        unsafe { ctor_scalar_ptr(ptr) }
    }
}

#[inline]
#[must_use]
pub fn is_scalar(o: *const CleanObj) -> bool {
    (o as usize & TAG_BIT) != 0
}

#[inline]
pub(crate) fn expect(condition: bool, msg: &str) {
    if !condition {
        invariant_violation(msg);
    }
}

#[inline]
pub(crate) fn expect_heap_obj(o: *const CleanObj, msg: &str) {
    if is_scalar(o) {
        invariant_violation(msg);
    }
}

#[inline]
pub(crate) fn expect_scalar(o: *const CleanObj, msg: &str) {
    if !is_scalar(o) {
        invariant_violation(msg);
    }
}

#[inline]
pub(crate) unsafe fn expect_obj_kind(o: *const CleanObj, expected: ObjKind, msg: &str) {
    expect_heap_obj(o, msg);
    // SAFETY: `o` was just verified as a non-scalar heap pointer by
    // expect_heap_obj, so dereferencing the header is valid.
    if unsafe { (*o).header.kind } != expected as u8 {
        invariant_violation(msg);
    }
}

#[inline]
pub(crate) fn expect_index_lt(idx: usize, len: usize, msg: &str) {
    if idx >= len {
        invariant_violation(msg);
    }
}

#[inline]
#[must_use]
pub(crate) fn lean_box(n: usize) -> LeanObjPtr {
    expect(n <= MAX_SMALL, "lean_box: value exceeds MAX_SMALL");
    ((n << 1) | TAG_BIT) as LeanObjPtr
}

#[inline]
#[must_use]
pub(crate) fn lean_unbox(o: LeanObjPtr) -> usize {
    expect_scalar(o, "lean_unbox: pointer is not a scalar");
    (o as usize) >> 1
}

#[inline]
#[must_use]
pub fn box_val(n: usize) -> LeanObjPtr {
    expect(n <= MAX_SMALL, "box_val: value exceeds MAX_SMALL");
    lean_box(n)
}

#[inline]
#[must_use]
pub fn unbox_val(o: *const CleanObj) -> usize {
    expect_scalar(o, "unbox_val: pointer is not a scalar");
    (o as usize) >> 1
}

#[inline]
#[must_use]
pub(crate) unsafe fn obj_fields_ptr(o: *const CleanObj) -> *mut LeanObjPtr {
    // SAFETY: Caller guarantees `o` is a valid heap-allocated CleanObj.
    // The fields region starts immediately after the ObjHeader, so adding
    // size_of::<ObjHeader>() bytes to the object base yields a valid pointer
    // within the allocation.
    unsafe { (o as *const u8).add(size_of::<ObjHeader>()) as *mut LeanObjPtr }
}

#[inline]
#[must_use]
pub(crate) unsafe fn ctor_scalar_ptr(o: *mut CleanObj) -> *mut u8 {
    // SAFETY: Caller guarantees `o` is a valid Ctor object. The scalar region
    // starts after the header and `num_objs` pointer fields. Reading
    // `num_objs` from the header is valid because `o` is a live heap object,
    // and the computed offset stays within the allocation (sized by
    // `obj_layout(num_objs, scalar_sz)`).
    unsafe {
        let offset =
            size_of::<ObjHeader>() + ((*o).header.num_objs as usize) * size_of::<LeanObjPtr>();
        (o as *mut u8).add(offset)
    }
}

#[inline]
#[must_use]
/// # Safety
/// `o` must be a valid constructor object and `idx < num_objs`.
pub unsafe fn ctor_get(o: *const CleanObj, idx: usize) -> LeanObjPtr {
    // SAFETY: Caller guarantees `o` is a valid Ctor heap object.
    // expect_obj_kind dereferences the header to verify kind == Ctor.
    unsafe {
        expect_obj_kind(o, ObjKind::Ctor, "ctor_get: pointer is not a constructor");
    }
    // SAFETY: After the kind check above, `o` is a valid Ctor. Reading
    // `num_objs` and computing fields_ptr + idx is within the allocation
    // because expect_index_lt verifies idx < num_objs.
    unsafe {
        expect_index_lt(
            idx,
            (*o).header.num_objs as usize,
            "ctor_get: field index out of bounds",
        );
        *obj_fields_ptr(o).add(idx)
    }
}

#[inline]
/// # Safety
/// `o` must be a uniquely owned constructor object and `idx < num_objs`.
pub unsafe fn ctor_set(o: *mut CleanObj, idx: usize, v: LeanObjPtr) {
    // SAFETY: Caller guarantees `o` is a uniquely owned Ctor heap object.
    // expect_obj_kind dereferences the header to verify kind == Ctor.
    unsafe {
        expect_obj_kind(o, ObjKind::Ctor, "ctor_set: pointer is not a constructor");
    }
    // SAFETY: After the kind check, `o` is a valid Ctor with unique ownership.
    // expect_index_lt verifies idx < num_objs, so fields_ptr + idx is within
    // the allocation. Unique ownership ensures no aliasing writes.
    unsafe {
        expect_index_lt(
            idx,
            (*o).header.num_objs as usize,
            "ctor_set: field index out of bounds",
        );
        obj_fields_ptr(o).add(idx).write(v);
    }
}

#[inline]
#[must_use]
/// # Safety
/// `o` must be a valid heap object or tagged scalar.
pub unsafe fn obj_tag(o: *const CleanObj) -> u8 {
    if is_scalar(o) {
        unbox_val(o) as u8
    } else {
        // SAFETY: `o` is not a scalar (checked above), so it is a valid heap
        // pointer. Dereferencing the header to read the tag field is valid.
        unsafe { (*o).header.tag }
    }
}

pub(crate) fn ctor_layout(num_objs: u8, scalar_sz: u8) -> Layout {
    let size =
        size_of::<ObjHeader>() + (num_objs as usize) * size_of::<LeanObjPtr>() + scalar_sz as usize;
    Layout::from_size_align(size, OBJ_ALIGN).expect("invalid ctor layout")
}

pub(crate) fn obj_layout(num_objs: u8, scalar_size: u8) -> Layout {
    ctor_layout(num_objs, scalar_size)
}

pub(crate) fn closure_layout(num_fixed: u16) -> Layout {
    let size = size_of::<ClosureObj>() + (num_fixed as usize) * size_of::<LeanObjPtr>();
    Layout::from_size_align(size, align_of::<ClosureObj>()).expect("invalid closure layout")
}

pub(crate) fn string_layout(len: usize) -> Layout {
    let size = size_of::<StringObj>() + len + 1;
    Layout::from_size_align(size, align_of::<StringObj>()).expect("invalid string layout")
}

pub(crate) fn array_layout(capacity: usize) -> Layout {
    let size = size_of::<ArrayObj>() + capacity * size_of::<LeanObjPtr>();
    Layout::from_size_align(size, align_of::<ArrayObj>()).expect("invalid array layout")
}

#[repr(C)]
pub(crate) struct ClosureObj {
    pub(crate) header: ObjHeader,
    pub(crate) func: *const (),
    pub(crate) arity: u16,
    pub(crate) num_fixed: u16,
}

impl ClosureObj {
    #[inline]
    pub(crate) unsafe fn args_ptr(ptr: *const Self) -> *mut LeanObjPtr {
        // SAFETY: Delegates to closure_args_ptr. Caller guarantees `ptr` is a
        // valid heap-allocated ClosureObj with space for num_fixed args after
        // the fixed-size fields.
        unsafe { closure_args_ptr(ptr) }
    }
}

#[inline]
#[must_use]
pub(crate) unsafe fn closure_args_ptr(c: *const ClosureObj) -> *mut LeanObjPtr {
    // SAFETY: Caller guarantees `c` is a valid heap-allocated ClosureObj. The
    // captured-args region starts immediately after the ClosureObj struct, so
    // adding size_of::<ClosureObj>() bytes to the base yields a valid pointer
    // within the allocation (sized by closure_layout(num_fixed)).
    unsafe { (c as *const u8).add(size_of::<ClosureObj>()) as *mut LeanObjPtr }
}

#[repr(C)]
pub(crate) struct StringObj {
    pub(crate) header: ObjHeader,
    pub(crate) len: usize,
}

impl StringObj {
    #[inline]
    pub(crate) unsafe fn data_ptr(ptr: *mut Self) -> *mut u8 {
        // SAFETY: Caller guarantees `ptr` is a valid heap-allocated StringObj.
        // The string data region starts immediately after the StringObj struct,
        // so adding size_of::<StringObj>() bytes to the base yields a valid
        // pointer within the allocation (sized by string_layout(len)).
        unsafe { (ptr as *mut u8).add(size_of::<StringObj>()) }
    }
}

#[repr(C)]
pub(crate) struct ArrayObj {
    pub(crate) header: ObjHeader,
    pub(crate) size: usize,
    pub(crate) capacity: usize,
}

#[repr(C)]
pub(crate) struct ThunkObj {
    pub(crate) header: ObjHeader,
    pub(crate) value: *mut CleanObj,
    pub(crate) closure: *mut CleanObj,
}

#[repr(C)]
pub(crate) struct TaskObj {
    pub(crate) header: ObjHeader,
    pub(crate) value: *mut CleanObj,
    pub(crate) imp: *mut (),
}

#[repr(C)]
pub struct CleanExternalClass {
    pub finalize: Option<unsafe fn(*mut ())>,
    pub foreach: Option<unsafe fn(*mut (), *mut CleanObj)>,
}

#[repr(C)]
pub(crate) struct ExternalObj {
    pub(crate) header: ObjHeader,
    pub(crate) class: *const CleanExternalClass,
    pub(crate) data: *mut (),
}

pub(crate) fn alloc_obj(tag: u8, kind: ObjKind, num_objs: u8, scalar_size: u8) -> *mut CleanObj {
    let layout = obj_layout(num_objs, scalar_size);
    // SAFETY: `layout` was computed by obj_layout which produces a valid,
    // non-zero-sized layout. alloc::alloc returns a valid pointer or null.
    let ptr = unsafe { alloc::alloc(layout) } as *mut CleanObj;
    if ptr.is_null() {
        lean_panic("out of memory");
    }
    // SAFETY: `ptr` is non-null (checked above) and points to a freshly
    // allocated region of `layout.size()` bytes. Writing the header via
    // `&raw mut` initializes the ObjHeader in place without creating an
    // intermediate reference to uninitialized memory.
    unsafe {
        std::ptr::write(
            &raw mut (*ptr).header,
            ObjHeader {
                ref_count: AtomicU32::new(0),
                tag,
                kind: kind as u8,
                num_objs,
                scalar_sz: scalar_size,
            },
        );
    }
    ptr
}

pub(crate) fn alloc_closure_obj(func: *const (), arity: u16, args: &[LeanObjPtr]) -> LeanObjPtr {
    expect(
        args.len() <= u16::MAX as usize,
        "alloc_closure_obj: captured args exceed u16 capacity",
    );
    let num_fixed = args.len() as u16;
    expect(arity > 0, "alloc_closure_obj: closure arity must be > 0");
    expect(
        num_fixed < arity,
        "alloc_closure_obj: closure num_fixed must be < arity",
    );

    let layout = closure_layout(num_fixed);
    // SAFETY: `layout` was computed by closure_layout which produces a valid,
    // non-zero-sized layout. alloc::alloc returns a valid pointer or null.
    let ptr = unsafe { alloc::alloc(layout) } as *mut ClosureObj;
    if ptr.is_null() {
        lean_panic("out of memory");
    }

    // SAFETY: `ptr` is non-null (checked above) and points to a freshly
    // allocated region of closure_layout(num_fixed) bytes. Header is written
    // via `&raw mut` to avoid referencing uninitialized memory. Fixed fields
    // (func, arity, num_fixed) are within the ClosureObj struct. The args
    // region has space for `num_fixed` pointers (guaranteed by layout), and
    // the loop writes exactly `args.len() == num_fixed` entries.
    unsafe {
        std::ptr::write(
            &raw mut (*ptr).header,
            ObjHeader {
                ref_count: AtomicU32::new(0),
                tag: 0,
                kind: ObjKind::Closure as u8,
                num_objs: 0,
                scalar_sz: 0,
            },
        );
        (*ptr).func = func;
        (*ptr).arity = arity;
        (*ptr).num_fixed = num_fixed;
        let dst = closure_args_ptr(ptr);
        for (i, &arg) in args.iter().enumerate() {
            dst.add(i).write(arg);
        }
    }

    ptr as LeanObjPtr
}

pub(crate) fn alloc_string_bytes(bytes: &[u8]) -> LeanObjPtr {
    let len = bytes.len();
    let layout = string_layout(len);
    // SAFETY: `layout` was computed by string_layout which produces a valid,
    // non-zero-sized layout (includes NUL terminator). alloc::alloc returns
    // a valid pointer or null.
    let ptr = unsafe { alloc::alloc(layout) } as *mut StringObj;
    if ptr.is_null() {
        lean_panic("out of memory");
    }

    // SAFETY: `ptr` is non-null (checked above) and points to a freshly
    // allocated region of string_layout(len) bytes. Header is written via
    // `&raw mut`. The data region (after StringObj) has space for `len` bytes
    // plus a NUL terminator. copy_nonoverlapping is valid because `bytes`
    // is a separate stack/heap allocation that cannot overlap with `dst`.
    unsafe {
        std::ptr::write(
            &raw mut (*ptr).header,
            ObjHeader {
                ref_count: AtomicU32::new(0),
                tag: 0,
                kind: ObjKind::Str as u8,
                num_objs: 0,
                scalar_sz: 0,
            },
        );
        (*ptr).len = len;
        let dst = StringObj::data_ptr(ptr);
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, len);
        *dst.add(len) = 0;
    }

    ptr as LeanObjPtr
}

pub(crate) unsafe fn obj_child_count(o: *const CleanObj) -> usize {
    // SAFETY: Caller guarantees `o` is a valid non-scalar heap object.
    // Reading header.kind to dispatch and then reading num_fixed (for
    // Closure) or num_objs (for others) are both within the header/struct
    // of the live allocation. Closure cast is valid because kind == Closure
    // means the allocation is a ClosureObj.
    unsafe {
        if ObjKind::from_u8((*o).header.kind) == ObjKind::Closure {
            (*(o as *const ClosureObj)).num_fixed as usize
        } else {
            (*o).header.num_objs as usize
        }
    }
}

pub(crate) unsafe fn obj_child_ptrs(o: *const CleanObj) -> *mut LeanObjPtr {
    // SAFETY: Caller guarantees `o` is a valid non-scalar heap object.
    // The kind field determines the correct cast and child pointer location.
    // Closure args follow ClosureObj; Ctor/Str fields follow ObjHeader.
    // Extended types (Array, Thunk, Task, External) store children in typed
    // struct fields rather than a pointer array, so null is returned.
    unsafe {
        match ObjKind::from_u8((*o).header.kind) {
            ObjKind::Closure => closure_args_ptr(o as *const ClosureObj),
            ObjKind::Ctor | ObjKind::Str => obj_fields_ptr(o),
            ObjKind::Array | ObjKind::Thunk | ObjKind::Task | ObjKind::External => {
                std::ptr::null_mut()
            }
        }
    }
}

pub(crate) unsafe fn object_layout(o: *const CleanObj) -> Layout {
    // SAFETY: Caller guarantees `o` is a valid non-scalar heap object.
    // The kind field determines the correct struct cast and layout
    // computation. Each branch reads only the fields relevant to that
    // kind's layout (e.g., Closure reads num_fixed, Array reads capacity).
    // These fields were initialized at allocation time and are valid.
    unsafe {
        match ObjKind::from_u8((*o).header.kind) {
            ObjKind::Ctor => obj_layout((*o).header.num_objs, (*o).header.scalar_sz),
            ObjKind::Closure => closure_layout((*(o as *const ClosureObj)).num_fixed),
            ObjKind::Array => array_layout((*(o as *const ArrayObj)).capacity),
            ObjKind::Str => string_layout((*(o as *const StringObj)).len),
            ObjKind::Thunk => Layout::new::<ThunkObj>(),
            ObjKind::Task => Layout::new::<TaskObj>(),
            ObjKind::External => Layout::new::<ExternalObj>(),
        }
    }
}

#[cold]
#[inline(never)]
fn invariant_violation(msg: &str) -> ! {
    lean_panic(msg)
}

#[cold]
pub(crate) fn lean_panic(msg: &str) -> ! {
    use std::io::Write;
    let _ = writeln!(std::io::stderr(), "clean panic: {msg}");
    std::process::abort();
}

pub(crate) fn runtime_init() {}

pub(crate) fn runtime_finalize() {}
