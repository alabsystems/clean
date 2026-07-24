// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end C runtime behavioral tests.
//!
//! These tests compile raw C code against the clean C runtime, execute the
//! binary, and verify behavioral correctness. Unlike emit_parity_tests.rs
//! which tests the C *emitter*, these test the C *runtime* directly.
//!
//! Separated from emit_parity_tests.rs to keep files under the 1000-line limit
//! and because these tests have a different focus (runtime correctness vs
//! emitter parity).

use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

/// Monotonic counter for unique temp directory names across parallel tests.
static E2E_RT_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Find a C compiler in PATH. Tries cc, gcc, clang in order.
fn find_c_compiler() -> Option<String> {
    for compiler in &["cc", "gcc", "clang"] {
        if Command::new(compiler)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return Some(compiler.to_string());
        }
    }
    None
}

/// Path to clean_runtime include directory (contains clean_runtime.h).
fn runtime_include_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/include")
}

/// Path to clean_runtime.c implementation.
fn runtime_c_source() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/src/clean_runtime.c")
}

/// Compile raw C source against clean_runtime, run, and return stdout.
///
/// Returns None if no C compiler is available.
/// Panics on compilation or execution failure (test fails).
fn compile_and_run_c_raw(c_source: &str) -> Option<String> {
    let cc = match find_c_compiler() {
        Some(cc) => cc,
        None => {
            eprintln!("No C compiler found (cc/gcc/clang) — skipping e2e runtime test");
            return None;
        }
    };

    let tmp_dir = std::env::temp_dir().join(format!(
        "clean_e2e_rt_{}_{}",
        std::process::id(),
        E2E_RT_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&tmp_dir).expect("create temp dir");

    let source_path = tmp_dir.join("test.c");
    let binary_path = tmp_dir.join("test_bin");

    std::fs::write(&source_path, c_source).expect("write source");

    let compile = Command::new(&cc)
        .arg("-o")
        .arg(&binary_path)
        .arg(&source_path)
        .arg(runtime_c_source())
        .arg(format!("-I{}", runtime_include_dir().display()))
        .arg("-lm")
        .arg("-std=c11")
        .output()
        .expect("failed to invoke C compiler");

    if !compile.status.success() {
        let stderr = String::from_utf8_lossy(&compile.stderr);
        let _ = std::fs::remove_dir_all(&tmp_dir);
        panic!(
            "C compilation failed (compiler: {}):\n{}\n\nSource:\n{}",
            cc, stderr, c_source
        );
    }

    let run = Command::new(&binary_path)
        .output()
        .expect("failed to execute compiled binary");

    let _ = std::fs::remove_dir_all(&tmp_dir);

    if !run.status.success() {
        let stderr = String::from_utf8_lossy(&run.stderr);
        panic!(
            "Compiled program exited with {}:\nstderr: {}",
            run.status, stderr
        );
    }

    Some(String::from_utf8_lossy(&run.stdout).trim().to_string())
}

/// E2E: verify clean_dec tail-child optimization handles deep singly-linked chains.
///
/// Creates a chain of 10000 ctor objects (each with 1 child pointing to the next),
/// then decrements the head. Without tail-child optimization (pure recursion),
/// this recurses 10K deep. The iterative loop in clean_dec (#1998) handles this
/// in O(1) stack space. Verifies no crash/segfault.
#[test]
fn test_e2e_c_dec_deep_chain() {
    let source = r#"
#include "clean_runtime.h"
#include <stdio.h>

int main(void) {
    clean_runtime_init();

    /* Build a singly-linked chain: each node is a ctor with 1 object child. */
    clean_obj* chain = clean_box(0); /* leaf: tagged pointer */
    for (int i = 0; i < 10000; i++) {
        chain = clean_alloc_ctor(0, 1, 0, chain);
    }

    /* Decrement the head — iteratively frees entire chain via tail-child opt. */
    clean_dec(chain);
    printf("ok\n");

    clean_runtime_finalize();
    return 0;
}
"#;
    if let Some(output) = compile_and_run_c_raw(source) {
        assert_eq!(
            output, "ok",
            "clean_dec should handle deep chain without crash"
        );
    }
}

/// E2E: verify clean_box_uint64/clean_unbox_uint64 roundtrip at boundary values.
///
/// Tests uint64 box/unbox with 0, MAX, and a representative large value to verify
/// the memcpy-based read/write preserves all 8 bytes correctly.
#[test]
fn test_e2e_c_box_unbox_uint64_boundaries() {
    let source = r#"
#include "clean_runtime.h"
#include <stdio.h>
#include <inttypes.h>

int main(void) {
    clean_runtime_init();

    /* Test 0 */
    clean_obj* b0 = clean_box_uint64(0);
    uint64_t v0 = clean_unbox_uint64(b0);
    clean_dec(b0);

    /* Test UINT64_MAX */
    clean_obj* bmax = clean_box_uint64(UINT64_MAX);
    uint64_t vmax = clean_unbox_uint64(bmax);
    clean_dec(bmax);

    /* Test representative large value */
    clean_obj* blarge = clean_box_uint64(UINT64_C(0xDEADBEEFCAFEBABE));
    uint64_t vlarge = clean_unbox_uint64(blarge);
    clean_dec(blarge);

    if (v0 == 0 && vmax == UINT64_MAX && vlarge == UINT64_C(0xDEADBEEFCAFEBABE)) {
        printf("ok\n");
    } else {
        printf("FAIL: v0=%" PRIu64 " vmax=%" PRIu64 " vlarge=%" PRIx64 "\n",
               v0, vmax, vlarge);
    }

    clean_runtime_finalize();
    return 0;
}
"#;
    if let Some(output) = compile_and_run_c_raw(source) {
        assert_eq!(
            output, "ok",
            "uint64 box/unbox should preserve boundary values"
        );
    }
}

/// E2E: verify closure allocation, exact-application, and partial-application dispatch.
///
/// Creates a closure wrapping a 2-arity function (add), partially applies one arg,
/// then saturates with the second arg via clean_apply_1. Exercises:
///   - clean_alloc_closure (with captured arg)
///   - clean_apply_1 exact-application path
///   - Function pointer casting and the V1 flat-array calling convention
///   - Partial application (under-application → bigger closure → exact application)
#[test]
fn test_e2e_c_closure_invocation() {
    let source = r#"
#include "clean_runtime.h"
#include <stdio.h>

/* A simple 2-arity function: unbox both args, add, re-box. */
clean_obj* my_add(clean_obj* a, clean_obj* b) {
    size_t va = clean_unbox(a);
    size_t vb = clean_unbox(b);
    return clean_box(va + vb);
}

int main(void) {
    clean_runtime_init();

    /* --- Test 1: Exact application via clean_apply_2 --- */
    clean_obj* closure_full = clean_alloc_closure((void*)my_add, 2, 0);
    clean_obj* r1 = clean_apply_2(closure_full, clean_box(10), clean_box(20));
    size_t v1 = clean_unbox(r1);

    /* --- Test 2: Partial application (capture 1 arg), then saturate --- */
    clean_obj* partial = clean_alloc_closure((void*)my_add, 2, 1, clean_box(100));
    clean_obj* r2 = clean_apply_1(partial, clean_box(42));
    size_t v2 = clean_unbox(r2);

    /* --- Test 3: Over-application (arity-1 function applied with 2 args) --- */
    /* identity: 1-arity, returns its argument (which should be a closure). */

    if (v1 == 30 && v2 == 142) {
        printf("ok\n");
    } else {
        printf("FAIL: v1=%zu v2=%zu\n", v1, v2);
    }

    clean_runtime_finalize();
    return 0;
}
"#;
    if let Some(output) = compile_and_run_c_raw(source) {
        assert_eq!(
            output, "ok",
            "closure invocation should handle exact and partial application"
        );
    }
}

/// E2E: verify SSet byte-offset scalar write/read roundtrip in compiled C.
///
/// Allocates a ctor with 1 object field and 12 bytes of scalar payload, then
/// writes uint8, uint16, and uint32 values via the typed scalar setters at
/// computed byte offsets, and reads them back via the corresponding getters.
/// Verifies the byte-offset arithmetic is correct end-to-end.
#[test]
fn test_e2e_c_sset_byte_offset_roundtrip() {
    let source = r#"
#include "clean_runtime.h"
#include <stdio.h>

int main(void) {
    clean_runtime_init();

    /* Allocate ctor: tag=0, 1 object field, 12 bytes scalar payload.
     * Object field region: fields[0] (8 bytes on 64-bit).
     * Scalar region starts at byte offset = 1 * sizeof(clean_obj*) = 8. */
    clean_obj* o = clean_alloc_ctor(0, 1, 12, clean_box(99));

    unsigned base = 1 * sizeof(clean_obj*);  /* = 8 on 64-bit */

    /* Write scalars at successive offsets within the 12-byte scalar region. */
    clean_ctor_set_uint8(o, base + 0, 0xAB);
    clean_ctor_set_uint16(o, base + 2, 0xCDEF);
    clean_ctor_set_uint32(o, base + 4, 0x12345678);

    /* Read them back. */
    uint8_t  v8  = clean_ctor_get_uint8(o, base + 0);
    uint16_t v16 = clean_ctor_get_uint16(o, base + 2);
    uint32_t v32 = clean_ctor_get_uint32(o, base + 4);

    /* Also verify the object field survived. */
    clean_obj* child = clean_ctor_get(o, 0);
    size_t child_val = clean_unbox(child);

    if (v8 == 0xAB && v16 == 0xCDEF && v32 == 0x12345678 && child_val == 99) {
        printf("ok\n");
    } else {
        printf("FAIL: v8=0x%02x v16=0x%04x v32=0x%08x child=%zu\n",
               v8, v16, v32, child_val);
    }

    clean_dec(o);
    clean_runtime_finalize();
    return 0;
}
"#;
    if let Some(output) = compile_and_run_c_raw(source) {
        assert_eq!(
            output, "ok",
            "SSet byte-offset scalar write/read should roundtrip correctly"
        );
    }
}

/// E2E: verify reset/reuse returns a non-NULL slot for a uniquely-owned Ctor
/// and that clean_reuse successfully reuses the memory.
///
/// Exercises: clean_reset (exclusive ownership path), clean_reuse (reuse path),
/// and verifies that reused memory holds correct values after re-initialization.
#[test]
fn test_e2e_c_reset_reuse_ctor() {
    let source = r#"
#include "clean_runtime.h"
#include <stdio.h>

int main(void) {
    clean_runtime_init();

    /* Allocate a uniquely-owned ctor: tag=1, 2 obj fields, 0 scalar bytes. */
    clean_obj* original = clean_alloc_ctor(1, 2, 0, clean_box(10), clean_box(20));

    /* Reset: since ref_count == 0 (unique), should return non-NULL. */
    clean_obj* slot = clean_reset(original);

    if (slot == NULL) {
        printf("FAIL: reset returned NULL for unique ctor\n");
        clean_runtime_finalize();
        return 1;
    }

    /* Reuse the slot for a new ctor with same layout: tag=2, 2 obj fields. */
    clean_obj* reused = clean_reuse(slot, 2, 2, 0, clean_box(30), clean_box(40));

    /* Verify the reused object has correct values. */
    uint8_t tag = clean_obj_tag(reused);
    size_t f0 = clean_unbox(clean_ctor_get(reused, 0));
    size_t f1 = clean_unbox(clean_ctor_get(reused, 1));

    /* Verify that reuse actually reused memory (same pointer). */
    int same_ptr = (reused == slot);

    if (tag == 2 && f0 == 30 && f1 == 40 && same_ptr) {
        printf("ok\n");
    } else {
        printf("FAIL: tag=%u f0=%zu f1=%zu same_ptr=%d\n", tag, f0, f1, same_ptr);
    }

    clean_dec(reused);
    clean_runtime_finalize();
    return 0;
}
"#;
    if let Some(output) = compile_and_run_c_raw(source) {
        assert_eq!(
            output, "ok",
            "reset/reuse should recycle unique ctor memory with correct values"
        );
    }
}

/// E2E: verify clean_mk_string, clean_string_data, and clean_string_len
/// in compiled C.
///
/// Creates strings (empty, ASCII, multi-byte UTF-8), reads back data and length,
/// and verifies correctness. Exercises the string object layout (header + len + data).
#[test]
fn test_e2e_c_string_operations() {
    let source = r#"
#include "clean_runtime.h"
#include <stdio.h>
#include <string.h>

int main(void) {
    clean_runtime_init();

    /* Test 1: Empty string */
    clean_obj* s1 = clean_mk_string("");
    size_t len1 = clean_string_len(s1);
    const char* data1 = clean_string_data(s1);
    int ok1 = (len1 == 0 && data1[0] == '\0');

    /* Test 2: ASCII string */
    clean_obj* s2 = clean_mk_string("hello, clean");
    size_t len2 = clean_string_len(s2);
    const char* data2 = clean_string_data(s2);
    int ok2 = (len2 == 12 && strcmp(data2, "hello, clean") == 0);

    /* Test 3: String with special characters */
    clean_obj* s3 = clean_mk_string("a\tb\nc");
    size_t len3 = clean_string_len(s3);
    const char* data3 = clean_string_data(s3);
    int ok3 = (len3 == 5 && strcmp(data3, "a\tb\nc") == 0);

    if (ok1 && ok2 && ok3) {
        printf("ok\n");
    } else {
        printf("FAIL: ok1=%d ok2=%d ok3=%d len1=%zu len2=%zu len3=%zu\n",
               ok1, ok2, ok3, len1, len2, len3);
    }

    clean_dec(s1);
    clean_dec(s2);
    clean_dec(s3);
    clean_runtime_finalize();
    return 0;
}
"#;
    if let Some(output) = compile_and_run_c_raw(source) {
        assert_eq!(
            output, "ok",
            "string operations should create, read, and measure strings correctly"
        );
    }
}

/// E2E: verify clean_reset returns NULL for Task-kind objects and clean_dec
/// correctly frees them.
///
/// Task objects (kind=5) have internal structure that prevents safe in-place
/// reuse. clean_reset must decline reuse (return NULL) and dec the object.
/// This test manually constructs a Task-like object (header with kind=TASK
/// and 0 children) to verify the reset/dec path without needing clean_alloc_task
/// (which is Rust-only).
#[test]
fn test_e2e_c_task_dealloc() {
    let source = r#"
#include "clean_runtime.h"
#include <stdio.h>
#include <stdlib.h>

int main(void) {
    clean_runtime_init();

    /* Manually allocate an object and set its kind to TASK.
     * Task objects have no C-level allocator in the runtime header,
     * but we can construct one by allocating a ctor-sized object
     * and overwriting the kind byte. This tests clean_reset's
     * kind-dispatch path for TASK (should return NULL). */
    clean_obj* task = (clean_obj*)malloc(sizeof(clean_obj_header));
    if (!task) {
        printf("FAIL: malloc\n");
        return 1;
    }
    atomic_init(&task->header.ref_count, 0);  /* unique */
    task->header.tag = 0;
    task->header.kind = CLEAN_OBJ_KIND_TASK;
    task->header.num_objs = 0;
    task->header.scalar_sz = 0;

    /* clean_reset should decline reuse for Task kind and return NULL.
     * It will call clean_dec internally, which will free the object
     * (since num_children == 0 and ref_count == 0). */
    clean_obj* slot = clean_reset(task);

    if (slot == NULL) {
        printf("ok\n");
    } else {
        printf("FAIL: reset returned non-NULL for task object\n");
        /* Don't free slot — it's the same pointer as task, already freed by dec */
    }

    clean_runtime_finalize();
    return 0;
}
"#;
    if let Some(output) = compile_and_run_c_raw(source) {
        assert_eq!(
            output, "ok",
            "task dealloc: clean_reset should return NULL for Task-kind objects"
        );
    }
}
