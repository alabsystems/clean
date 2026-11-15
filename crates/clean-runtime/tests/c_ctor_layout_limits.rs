// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C-harness tests for the constructor layout the 8-byte object header holds.
//!
//! `clean_obj_header` stores the tag, `num_objs` and `scalar_sz` in one byte
//! each. The IR checker refuses the shapes that overflow them (rule C1); these
//! tests pin the runtime's defence in depth, compiled from the shipped C
//! sources and run as a process:
//!
//! * `clean_alloc_ctor` and `clean_reuse` stop with `clean panic:` and exit
//!   status 1 (Lean's `lean_internal_panic`; never a crash signal, so no
//!   macOS crash report) on an argument above 255 instead of casting it to a
//!   byte (a 256-field constructor allocated 0 slots and then wrote 256
//!   pointers; 320 scalar bytes allocated 64);
//! * `clean_obj_tag` returns a boxed constructor's whole tag (299, not 43), so
//!   the C lane's `switch` dispatches an enum of 256 or more constructors
//!   correctly; a boxed value above `UINT32_MAX` reads as `UINT32_MAX`, which
//!   no constructor tag reaches (the IR checker bounds tags by 65535), so a
//!   `switch` takes the branch the whole value would and never the one its
//!   low 32 bits name;
//! * the trust-cg lane's `clean_obj_tag` import (`runtime_extern.c`) returns
//!   the same 32-bit tag (its runtime ABI declares `U32`).
//!
//! A C compiler is required: a harness that cannot build is a failure here,
//! never a skip.

use std::path::Path;
use std::process::{Command, Output};

fn c_compiler() -> &'static str {
    ["cc", "clang", "gcc"]
        .into_iter()
        .find(|compiler| {
            Command::new(compiler)
                .arg("--version")
                .output()
                .is_ok_and(|o| o.status.success())
        })
        .expect("a C compiler (cc/clang/gcc) is required to run the runtime's C harness")
}

/// Write a crate C source flattened so `#include "clean_runtime.h"` resolves
/// next to it.
fn materialize(dir: &Path, file: &str, src: &str) {
    let flat = src.replacen("../include/clean_runtime.h", "clean_runtime.h", 1);
    std::fs::write(dir.join(file), flat).expect("write C source");
}

/// Build `main_c` against the runtime (and, with `with_extern`, against the
/// trust-cg forwarders of `runtime_extern.c`), run it, and return its output.
fn build_and_run(main_c: &str, with_extern: bool) -> Output {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        dir.path().join("clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .expect("write header");
    materialize(
        dir.path(),
        "clean_runtime.c",
        clean_runtime::runtime_source(),
    );
    if with_extern {
        materialize(
            dir.path(),
            "runtime_extern.c",
            clean_runtime::runtime_extern_source(),
        );
    }
    std::fs::write(dir.path().join("main.c"), main_c).expect("write main.c");
    let bin = dir.path().join("prog");
    let mut cc = Command::new(c_compiler());
    cc.args(["-std=c11", "-O1"])
        .arg("-I")
        .arg(dir.path())
        .arg(dir.path().join("main.c"))
        .arg(dir.path().join("clean_runtime.c"));
    if with_extern {
        cc.arg(dir.path().join("runtime_extern.c"));
    }
    let built = cc
        .arg("-lm")
        .arg("-o")
        .arg(&bin)
        .output()
        .expect("spawn C compiler");
    assert!(
        built.status.success(),
        "C harness failed to compile:\n{}\n\nmain.c:\n{main_c}",
        String::from_utf8_lossy(&built.stderr)
    );
    Command::new(&bin).output().expect("run C harness")
}

/// `n` comma-separated boxed field arguments, for a variadic allocator call.
fn boxed_args(n: usize) -> String {
    vec!["clean_box(1)"; n].join(", ")
}

/// The status `clean_panic` ends the program with: Lean's `lean_internal_panic`
/// calls `exit(1)` (pinned v4.30.0-rc2), and so does Clean's runtime
/// (docs/DECISIONS.md R86). A crash signal (the `abort()` it replaced) has no
/// exit code, so it fails this check.
const PANIC_STATUS: i32 = 1;

/// A harness whose `body` (described by `label`) must stop with a named
/// `clean panic:` and exit status [`PANIC_STATUS`] before the `survived` line
/// prints.
fn assert_panics(label: &str, body: &str, expected_message: &str) {
    let main_c = format!(
        "#include \"clean_runtime.h\"\n#include <stdio.h>\n\
         int main(void) {{\n    {body}\n    printf(\"survived\\n\");\n    return 0;\n}}\n"
    );
    let out = build_and_run(&main_c, false);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success() && !stdout.contains("survived"),
        "{label} must stop the program, but it ran on (status {:?}, stdout {stdout:?}, \
         stderr {stderr:?})",
        out.status
    );
    assert_eq!(
        out.status.code(),
        Some(PANIC_STATUS),
        "{label} must stop with exit status {PANIC_STATUS} (Lean's internal-panic status), \
         never a signal: status {:?}, stderr {stderr:?}",
        out.status
    );
    assert!(
        stderr.contains("clean panic: ") && stderr.contains(expected_message),
        "{label} must stop with a named `clean panic:` mentioning {expected_message:?}, \
         got status {:?} and stderr {stderr:?}",
        out.status
    );
}

#[test]
fn test_c_alloc_ctor_scalar_size_320_panics() {
    // 40 x UInt64: the layout_wide_scalars battery probe's scalar area.
    assert_panics(
        "clean_alloc_ctor(0, 0, 320)",
        "clean_alloc_ctor(0, 0, 320);",
        "320 scalar bytes",
    );
}

#[test]
fn test_c_alloc_ctor_256_object_fields_panics() {
    assert_panics(
        "clean_alloc_ctor with 256 object fields",
        &format!("clean_alloc_ctor(0, 256, 0, {});", boxed_args(256)),
        "256 object fields",
    );
}

#[test]
fn test_c_alloc_ctor_tag_256_panics() {
    assert_panics(
        "clean_alloc_ctor(256, 1, 0, x)",
        "clean_alloc_ctor(256, 1, 0, clean_box(1));",
        "constructor tag 256",
    );
}

#[test]
fn test_c_reuse_256_object_fields_panics() {
    // Fresh-allocation path (no reset slot).
    assert_panics(
        "clean_reuse(NULL, ..) with 256 object fields",
        &format!("clean_reuse(NULL, 0, 256, 0, {});", boxed_args(256)),
        "clean_reuse: 256 object fields",
    );
    // In-place path: a 0-field cell whose byte equals (uint8_t)256 passed the
    // old same-layout assertion and then took 256 pointer writes.
    assert_panics(
        "clean_reuse(0-field slot, ..) with 256 object fields",
        &format!(
            "clean_obj* slot = clean_alloc_ctor(0, 0, 0);\n    \
             clean_reuse(slot, 0, 256, 0, {});",
            boxed_args(256)
        ),
        "clean_reuse: 256 object fields",
    );
    assert_panics(
        "clean_reuse(0-byte slot, ..) with 256 scalar bytes",
        "clean_obj* slot = clean_alloc_ctor(0, 0, 0);\n    clean_reuse(slot, 0, 0, 256);",
        "clean_reuse: 256 scalar bytes",
    );
}

/// `clean_reuse` writes the tag into the same header byte `clean_alloc_ctor`
/// does, on both paths: in place over a reset slot (where `(uint8_t)256` used
/// to be stored as tag 0) and on a fresh allocation.
#[test]
fn test_c_reuse_tag_256_panics() {
    assert_panics(
        "clean_reuse(1-field slot, 256, ..)",
        "clean_obj* slot = clean_alloc_ctor(0, 1, 0, clean_box(1));\n    \
         clean_reuse(slot, 256, 1, 0, clean_box(2));",
        "clean_reuse: constructor tag 256",
    );
    assert_panics(
        "clean_reuse(NULL, 256, ..)",
        "clean_reuse(NULL, 256, 1, 0, clean_box(2));",
        "clean_reuse: constructor tag 256",
    );
}

/// The largest shapes the header holds still allocate, at full width.
#[test]
fn test_c_alloc_ctor_and_reuse_at_255_succeed() {
    let main_c = format!(
        "#include \"clean_runtime.h\"\n#include <stdio.h>\n\
         int main(void) {{\n\
         clean_obj* o = clean_alloc_ctor(255, 255, 255, {args});\n\
         printf(\"%u %u %u\\n\", (unsigned)o->header.tag, (unsigned)o->header.num_objs,\n\
                (unsigned)o->header.scalar_sz);\n\
         clean_obj* r = clean_reuse(NULL, 7, 2, 8, clean_box(1), clean_box(2));\n\
         printf(\"%u %u %u %zu\\n\", clean_obj_tag(r), (unsigned)r->header.num_objs,\n\
                (unsigned)r->header.scalar_sz, clean_unbox(clean_ctor_get(r, 1)));\n\
         return 0;\n}}\n",
        args = boxed_args(255)
    );
    let out = build_and_run(&main_c, false);
    assert!(
        out.status.success(),
        "255-wide shapes must allocate: status {:?}, stderr {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "255 255 255\n7 2 8 2\n"
    );
}

#[test]
fn test_c_obj_tag_reads_boxed_tag_299_whole() {
    let main_c = "#include \"clean_runtime.h\"\n#include <stdio.h>\n\
                  int main(void) {\n\
                  printf(\"%u %u %u\\n\", (unsigned)clean_obj_tag(clean_box(299)),\n\
                         (unsigned)clean_obj_tag(clean_box(255)),\n\
                         (unsigned)clean_obj_tag(clean_alloc_ctor(5, 1, 0, clean_box(1))));\n\
                  switch (clean_obj_tag(clean_box(299))) {\n\
                  case 43: printf(\"dispatched 43\\n\"); break;\n\
                  case 299: printf(\"dispatched 299\\n\"); break;\n\
                  default: printf(\"dispatched default\\n\"); break;\n\
                  }\n\
                  return 0;\n}\n";
    let out = build_and_run(main_c, false);
    assert!(
        out.status.success(),
        "status {:?}, stderr {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "299 255 5\ndispatched 299\n",
        "clean_obj_tag must return a boxed tag whole (an 8-bit read gives 43 for 299)"
    );
}

/// A boxed value wider than the 32-bit tag reads as `UINT32_MAX`, never as its
/// low 32 bits: `clean_box(2^32)` truncated would read 0 and take `case 0`.
#[test]
fn test_c_obj_tag_saturates_a_boxed_value_above_u32() {
    let main_c = "#include \"clean_runtime.h\"\n#include <stdio.h>\n\
                  int main(void) {\n\
                  size_t wide = (size_t)1 << 32;\n\
                  printf(\"%u %u %u\\n\", (unsigned)clean_obj_tag(clean_box(wide)),\n\
                         (unsigned)clean_obj_tag(clean_box(wide + 5)),\n\
                         (unsigned)clean_obj_tag(clean_box(4294967294u)));\n\
                  switch (clean_obj_tag(clean_box(wide + 5))) {\n\
                  case 0: printf(\"dispatched 0\\n\"); break;\n\
                  case 5: printf(\"dispatched 5\\n\"); break;\n\
                  default: printf(\"dispatched default\\n\"); break;\n\
                  }\n\
                  return 0;\n}\n";
    let out = build_and_run(main_c, false);
    assert!(
        out.status.success(),
        "status {:?}, stderr {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "4294967295 4294967295 4294967294\ndispatched default\n",
        "a boxed value above UINT32_MAX must read as UINT32_MAX (truncated, 2^32 + 5 reads 5)"
    );
}

/// The trust-cg lane binds `clean_obj_tag` through `runtime_extern.c` at the
/// 32-bit width its runtime ABI declares (`emit_trust_ir_runtime.rs`), so a
/// boxed tag above 255 reads back whole there too, and a boxed value above
/// `UINT32_MAX` saturates as the header's read does.
#[test]
fn test_c_extern_obj_tag_reads_boxed_tag_whole() {
    let main_c = "#include <stdint.h>\n#include <stddef.h>\n#include <stdio.h>\n\
                  typedef struct clean_obj clean_obj;\n\
                  extern uint32_t clean_obj_tag(clean_obj*);\n\
                  extern clean_obj* clean_box(size_t);\n\
                  int main(void) {\n\
                  printf(\"%u %u %u %u %u\\n\", (unsigned)clean_obj_tag(clean_box(255)),\n\
                         (unsigned)clean_obj_tag(clean_box(256)),\n\
                         (unsigned)clean_obj_tag(clean_box(299)),\n\
                         (unsigned)clean_obj_tag(clean_box(65535)),\n\
                         (unsigned)clean_obj_tag(clean_box((size_t)1 << 32)));\n\
                  return 0;\n}\n";
    let out = build_and_run(main_c, true);
    assert!(
        out.status.success(),
        "the extern clean_obj_tag must read boxed tags above 255 (an 8-bit ABI panicked or \
         truncated 299 to 43): status {:?}, stdout {:?}, stderr {}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "255 256 299 65535 4294967295\n"
    );
}
