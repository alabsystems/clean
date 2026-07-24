// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helper predicates for FFI boundary verification.

pub(crate) fn abi_can_unwind(abi: &str) -> bool {
    abi.to_ascii_lowercase().contains("unwind")
}

pub(crate) fn is_ffi_primitive_name(name: &str) -> bool {
    matches!(
        name,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
            | "bool"
            | "char"
            | "c_void"
            | "c_char"
            | "c_schar"
            | "c_uchar"
            | "c_short"
            | "c_ushort"
            | "c_int"
            | "c_uint"
            | "c_long"
            | "c_ulong"
            | "c_longlong"
            | "c_ulonglong"
            | "c_float"
            | "c_double"
    )
}

pub(crate) fn is_known_rust_owned_type(name: &str) -> bool {
    matches!(
        name.rsplit("::").next().unwrap_or(name),
        "String" | "CString" | "OsString" | "PathBuf" | "Box" | "Rc" | "Arc"
    )
}

pub(crate) fn is_thread_affine_rust_type(name: &str) -> bool {
    let leaf = name
        .rsplit("::")
        .next()
        .unwrap_or(name)
        .split('<')
        .next()
        .unwrap_or(name);
    matches!(leaf, "Rc" | "Cell" | "RefCell" | "UnsafeCell")
}
