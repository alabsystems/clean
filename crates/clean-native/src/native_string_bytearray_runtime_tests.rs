// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execute the shipped carrier conversions, separately from source admission.
//! A dummy C proof slot here does not qualify a proofless source expression.

use super::*;

const DRIVER: &str = r#"
#include "clean_runtime.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>
int main(int argc, char** argv) {
    const char* input = argc > 1 ? argv[1] : "";
    if (strcmp(input, "bad-bytearray") == 0) {
        l_String_ofByteArray(clean_box(0), clean_box(0));
        return 1;
    }
    if (strcmp(input, "bad-string") == 0) {
        l_String_toByteArray(clean_box(0));
        return 1;
    }
    if (strcmp(input, "bad-scalar") == 0) {
        clean_obj* chars = clean_alloc_ctor(1, 2, 0, clean_box(0xd800), clean_box(0));
        l_String_ofList(chars);
        return 1;
    }
    size_t n = strlen(input);
    uint32_t cps[] = {97 + (uint32_t)n, 0, 55, 233, 8364, 128512 + (uint32_t)n};
    clean_obj* chars = clean_box(0);
    for (size_t i = sizeof(cps) / sizeof(cps[0]); i > 0; i--) {
        chars = clean_alloc_ctor(1, 2, 0, clean_box_uint32(cps[i - 1]), chars);
    }
    clean_inc(chars);
    clean_obj* original = l_String_ofList(chars);
    assert(atomic_load(&chars->header.ref_count) == 0);
    clean_dec(chars);
    clean_inc(original);
    clean_obj* bytes = l_String_toByteArray(original);
    assert(atomic_load(&original->header.ref_count) == 0);
    clean_inc(bytes);
    clean_obj* copy = l_String_ofByteArray(bytes, clean_box(0));
    assert(atomic_load(&bytes->header.ref_count) == 0);
    assert(clean_string_len(copy) == clean_string_len(original));
    assert(memcmp(clean_string_data(copy), clean_string_data(original), clean_string_len(copy)) == 0);
    l_IO_println(copy);
    clean_dec(copy);
    clean_obj* second = l_String_ofByteArray(bytes, clean_box(0));
    l_IO_println(second);
    clean_dec(second);
    l_IO_println(original);
    clean_dec(original);
    clean_obj* empty = l_String_ofList(clean_box(0));
    assert(clean_string_len(empty) == 0);
    clean_obj* empty_bytes = l_String_toByteArray(empty);
    clean_obj* empty_copy = l_String_ofByteArray(empty_bytes, clean_box(0));
    assert(clean_string_len(empty_copy) == 0);
    l_IO_println(empty_copy);
    clean_dec(empty_copy);
    return 0;
}
"#;

#[test]
fn shipped_byte_array_bridge_preserves_bytes_and_transferred_shared_references() {
    let shims = select_shims_for_c_text(DRIVER).expect("actual production shim selection");
    let shims = format!("#include <stdio.h>\n{shims}");
    let dir = tempfile::tempdir().expect("tempdir");
    let binary = build_extract_executable(dir.path(), &shims, "", DRIVER)
        .expect("compile shipped carrier conversions");
    for input in ["", "suffix7", "é🦀"] {
        let output = Command::new(&binary).arg(input).output().expect("execute");
        let n = input.len() as u32;
        let first = char::from_u32(97 + n).expect("small scalar");
        let emoji = char::from_u32(128512 + n).expect("small scalar");
        let value = format!("{first}\x007é€{emoji}");
        let expected = format!("{value}\n{value}\n{value}\n\n");
        assert_eq!(output.status.code(), Some(0), "{:?}", output.stderr);
        assert_eq!(output.stdout, expected.as_bytes());
        assert!(output.stderr.is_empty(), "{:?}", output.stderr);
    }
    for (input, refusal) in [
        ("bad-bytearray", "expected ByteArray constructor"),
        ("bad-string", "expected flat String"),
        ("bad-scalar", "invalid Unicode scalar"),
    ] {
        let output = Command::new(&binary)
            .arg(input)
            .output()
            .expect("execute negative");
        assert!(
            !output.status.success(),
            "{input}: malformed carrier accepted"
        );
        assert!(String::from_utf8_lossy(&output.stderr).contains(refusal));
        assert!(output.stdout.is_empty());
    }
}
