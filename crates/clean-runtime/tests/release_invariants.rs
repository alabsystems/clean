// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Release-mode runtime invariant ratchets for #2825.
//!
//! The parent tests re-exec this same integration test binary and assert on the
//! child exit status so the stopping invariant checks can be verified directly.
//! A violated invariant ends the child with `clean panic: <msg>` on stderr and
//! exit status 1 (Lean's `lean_internal_panic`, docs/DECISIONS.md R86) -- never
//! a crash signal, which would make macOS write a crash report on every run.

use std::process::Command;

use clean_runtime::{
    clean_alloc_ctor, clean_box, clean_ctor_get, clean_dec, clean_mk_string, clean_obj_tag,
    clean_reset, clean_reuse, clean_unbox, native,
};

/// The status a violated runtime invariant ends the process with (`lean_panic`).
const PANIC_STATUS: i32 = 1;

fn spawn_child(child_mode: &str, child_test_name: &str) -> std::process::Output {
    let exe = std::env::current_exe().expect("cannot get current exe path");
    Command::new(&exe)
        .env("CLEAN_RUNTIME_CHILD", child_mode)
        .arg("--exact")
        .arg(child_test_name)
        .arg("--test-threads=1")
        .arg("--nocapture")
        .output()
        .expect("failed to exec child process")
}

#[test]
fn release_invariant_child_heap_unbox_aborts() {
    if std::env::var("CLEAN_RUNTIME_CHILD").as_deref() != Ok("heap_unbox_aborts") {
        return;
    }
    let heap_obj = clean_alloc_ctor(0, 0, 0, &[]);
    let _ = clean_unbox(heap_obj);
}

#[test]
fn release_invariant_child_scalar_unbox_succeeds() {
    if std::env::var("CLEAN_RUNTIME_CHILD").as_deref() != Ok("scalar_unbox_succeeds") {
        return;
    }
    let scalar = clean_box(7);
    assert_eq!(clean_unbox(scalar), 7);
}

#[test]
fn release_invariant_heap_unbox_aborts() {
    let output = spawn_child(
        "heap_unbox_aborts",
        "release_invariant_child_heap_unbox_aborts",
    );

    assert!(
        output.status.code() == Some(PANIC_STATUS),
        "heap unbox child should stop with exit status {PANIC_STATUS}, got {:?}.\n\
         stdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("lean_unbox: pointer is not a scalar"),
        "panic message should mention the scalar invariant, got stderr:\n{}",
        stderr,
    );
}

#[test]
fn release_invariant_scalar_unbox_still_roundtrips() {
    let output = spawn_child(
        "scalar_unbox_succeeds",
        "release_invariant_child_scalar_unbox_succeeds",
    );

    assert!(
        output.status.success(),
        "scalar unbox child should succeed.\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn release_invariant_parent_heap_ctor_still_dec_refs_cleanly() {
    let heap_obj = clean_alloc_ctor(0, 0, 0, &[]);
    clean_dec(heap_obj);
}

// -- Bug class: out-of-bounds field access -----------------------------------

#[test]
fn release_invariant_child_ctor_get_oob_aborts() {
    if std::env::var("CLEAN_RUNTIME_CHILD").as_deref() != Ok("ctor_get_oob_aborts") {
        return;
    }
    // Allocate a ctor with 1 field, then access index 1 (out of bounds).
    let field = clean_box(42);
    let o = clean_alloc_ctor(0, 1, 0, &[field]);
    let _ = clean_ctor_get(o, 1);
}

#[test]
fn release_invariant_ctor_get_oob_aborts() {
    let output = spawn_child(
        "ctor_get_oob_aborts",
        "release_invariant_child_ctor_get_oob_aborts",
    );

    assert!(
        output.status.code() == Some(PANIC_STATUS),
        "ctor_get OOB child should stop with exit status {PANIC_STATUS}, got {:?}.\n\
         stdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("field index out of bounds"),
        "panic message should mention index out of bounds, got stderr:\n{}",
        stderr,
    );
}

// -- Bug class: ctor operation on non-constructor ----------------------------

#[test]
fn release_invariant_child_ctor_get_on_string_aborts() {
    if std::env::var("CLEAN_RUNTIME_CHILD").as_deref() != Ok("ctor_get_on_string_aborts") {
        return;
    }
    // Create a string object and try to ctor_get on it.
    let s = clean_mk_string("hello");
    let _ = clean_ctor_get(s, 0);
}

#[test]
fn release_invariant_ctor_get_on_string_aborts() {
    let output = spawn_child(
        "ctor_get_on_string_aborts",
        "release_invariant_child_ctor_get_on_string_aborts",
    );

    assert!(
        output.status.code() == Some(PANIC_STATUS),
        "ctor_get on string child should stop with exit status {PANIC_STATUS}, got {:?}.\n\
         stdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("pointer is not a constructor"),
        "panic message should mention kind mismatch, got stderr:\n{}",
        stderr,
    );
}

// -- Bug class: reuse-layout mismatch ----------------------------------------

#[test]
fn release_invariant_child_reuse_field_count_mismatch_aborts() {
    if std::env::var("CLEAN_RUNTIME_CHILD").as_deref() != Ok("reuse_field_count_mismatch_aborts") {
        return;
    }
    // Allocate a ctor with 1 field, reset it, then reuse with 0 fields.
    let field = clean_box(99);
    let o = clean_alloc_ctor(0, 1, 0, &[field]);
    let slot = clean_reset(o);
    // slot has num_objs=1, but we pass 0 fields — layout mismatch.
    let _ = clean_reuse(slot, 1, 0, &[]);
}

#[test]
fn release_invariant_reuse_field_count_mismatch_aborts() {
    let output = spawn_child(
        "reuse_field_count_mismatch_aborts",
        "release_invariant_child_reuse_field_count_mismatch_aborts",
    );

    assert!(
        output.status.code() == Some(PANIC_STATUS),
        "reuse layout mismatch child should stop with exit status {PANIC_STATUS}, got {:?}.\n\
         stdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("field count must match slot capacity"),
        "panic message should mention field count mismatch, got stderr:\n{}",
        stderr,
    );
}

#[test]
fn release_invariant_child_reuse_fallback_field_count_oob_aborts() {
    if std::env::var("CLEAN_RUNTIME_CHILD").as_deref()
        != Ok("reuse_fallback_field_count_oob_aborts")
    {
        return;
    }
    let fields = vec![clean_box(0); usize::from(u8::MAX) + 1];
    let _ = clean_reuse(std::ptr::null_mut(), 1, 0, &fields);
}

#[test]
fn release_invariant_reuse_fallback_field_count_oob_aborts() {
    let output = spawn_child(
        "reuse_fallback_field_count_oob_aborts",
        "release_invariant_child_reuse_fallback_field_count_oob_aborts",
    );

    assert!(
        output.status.code() == Some(PANIC_STATUS),
        "reuse fallback oversized field-count child should stop with exit status \
         {PANIC_STATUS}, got {:?}.\nstdout: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("fields.len() exceeds u8::MAX on fallback allocation"),
        "panic message should mention fallback field-count bound, got stderr:\n{}",
        stderr,
    );
}

// -- Bug class: boxed constructor tag wider than the 8-bit tag read ---------

#[test]
fn release_invariant_child_obj_tag_reads_wide_boxed_tag_whole() {
    if std::env::var("CLEAN_RUNTIME_CHILD").as_deref() != Ok("obj_tag_reads_wide_boxed_tag_whole") {
        return;
    }
    // Nullary constructors 256 / 299 / 65535 of a wide enum (an 8-bit read gave
    // 0 / 43 / 255), then boxed values past the 32-bit tag, which saturate.
    let wide: [usize; 5] = [256, 299, 65535, 1 << 32, (1 << 32) + 5];
    let public: Vec<String> = wide
        .iter()
        .map(|&v| u64::from(clean_obj_tag(clean_box(v))).to_string())
        .collect();
    let native_tags: Vec<String> = wide
        .iter()
        .map(|&v| {
            // SAFETY: `box_val` returns a tagged scalar, which `obj_tag` reads
            // without dereferencing.
            let tag = unsafe { native::obj_tag(native::box_val(v)) };
            u64::from(tag).to_string()
        })
        .collect();
    println!("read tags {}", public.join(" "));
    println!("native tags {}", native_tags.join(" "));
}

#[test]
fn release_invariant_obj_tag_reads_wide_boxed_tag_whole() {
    let output = spawn_child(
        "obj_tag_reads_wide_boxed_tag_whole",
        "release_invariant_child_obj_tag_reads_wide_boxed_tag_whole",
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "both Rust tag reads must return a boxed tag above 255 whole, never abort or wrap.\n\
         stdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr),
    );
    let expected = "256 299 65535 4294967295 4294967295";
    assert!(
        stdout.contains(&format!("read tags {expected}\n"))
            && stdout.contains(&format!("native tags {expected}\n")),
        "clean_obj_tag and native::obj_tag must read the whole tag and saturate past u32::MAX \
         (want {expected:?}), got stdout:\n{stdout}",
    );
}

#[test]
fn release_invariant_obj_tag_reads_boxed_tag_255() {
    assert_eq!(clean_obj_tag(clean_box(255)), 255);
    assert_eq!(clean_obj_tag(clean_box(0)), 0);
}
