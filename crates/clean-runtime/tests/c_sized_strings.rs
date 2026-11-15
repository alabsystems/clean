// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execute the shipped C constructor, including its byte-copy and RC contract.

use std::process::{Command, Output};

fn run(body: &str) -> Output {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        dir.path().join("clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .expect("header");
    std::fs::write(
        dir.path().join("runtime.c"),
        clean_runtime::runtime_source().replacen(
            "../include/clean_runtime.h",
            "clean_runtime.h",
            1,
        ),
    )
    .expect("runtime");
    std::fs::write(
        dir.path().join("main.c"),
        format!("#include \"clean_runtime.h\"\n#include <stdio.h>\n#include <assert.h>\nint main(void) {{\n{body}\n}}"),
    )
    .expect("main");
    // Match native_build's runtime flags. Its existing uint32 boxing comparison
    // warns under -Wall on 64-bit Clang; keep -Werror on this caller separately.
    let runtime = dir.path().join("runtime.o");
    let compiled = Command::new("cc")
        .args(["-std=c11", "-O2", "-c"])
        .arg(dir.path().join("runtime.c"))
        .arg("-o")
        .arg(&runtime)
        .output()
        .expect("compile shipped runtime");
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let bin = dir.path().join("strings");
    let compiled = Command::new("cc")
        .args(["-std=c11", "-Wall", "-Werror", "-O2"])
        .arg("-I")
        .arg(dir.path())
        .arg(dir.path().join("main.c"))
        .arg(runtime)
        .arg("-lm")
        .arg("-o")
        .arg(&bin)
        .output()
        .expect("C compiler required");
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    Command::new(bin)
        .output()
        .expect("execute constructor harness")
}

#[test]
fn sized_constructor_copies_exact_bytes_and_preserves_rc() {
    let out = run(r#"
    char bytes[] = {'a', 0, '7', (char)0xc3, (char)0xa9};
    clean_obj* s = clean_mk_string_from_bytes(bytes, sizeof bytes);
    bytes[0] = 'z'; /* borrowed input is copied, without reading a terminator */
    assert(clean_string_len(s) == 5);
    assert(clean_string_data(s)[0] == 'a');
    assert(clean_string_data(s)[5] == 0);
    clean_inc(s);
    clean_dec(s);
    fwrite(clean_string_data(s), 1, clean_string_len(s), stdout);
    clean_dec(s);
    clean_obj* empty = clean_mk_string_from_bytes(NULL, 0);
    assert(clean_string_len(empty) == 0 && clean_string_data(empty)[0] == 0);
    clean_dec(empty);
    clean_obj* legacy = clean_mk_string("argv");
    assert(clean_string_len(legacy) == 4);
    fwrite(clean_string_data(legacy), 1, clean_string_len(legacy), stdout);
    clean_dec(legacy);
    return 0;
    "#);
    assert!(out.status.success(), "{:?}: {:?}", out.status, out.stderr);
    assert_eq!(out.stdout, b"a\x007\xc3\xa9argv");
    assert!(out.stderr.is_empty());
}

#[test]
fn sized_constructor_refuses_overflow_before_reading_source() {
    for len in ["SIZE_MAX", "SIZE_MAX - sizeof(clean_obj_header)"] {
        let out = run(&format!(
            "clean_mk_string_from_bytes(NULL, {len});\nputs(\"survived\");\nreturn 0;"
        ));
        assert_eq!(out.status.code(), Some(1));
        assert!(out.stdout.is_empty());
        assert!(String::from_utf8_lossy(&out.stderr)
            .contains("clean_mk_string_from_bytes: string size overflow"));
    }
}
