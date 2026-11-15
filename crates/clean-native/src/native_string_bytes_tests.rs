// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execute the shipped shims. This is distinct from source String.push closure:
//! the main prelude has no String.push declaration yet (retained source RED).

use super::*;

const DRIVER: &str = r#"
#include "clean_runtime.h"
#include <stdio.h>
#include <assert.h>
int main(int argc, char** argv) {
    clean_obj* s = clean_mk_string(argc > 1 ? argv[1] : "");
    uint32_t n = (uint32_t)clean_unbox(l_String_length(s));
    clean_obj* tail = clean_mk_string_from_bytes("\316\262\0007", 4);
    clean_obj* a = l_String_push(s, clean_box_uint32(0));
    clean_obj* t = l_String_append(a, tail);
    clean_inc(t); clean_dec(t);
    assert(clean_unbox(l_String_utf8ByteSize(t)) == clean_string_len(s) + 5);
    assert(clean_unbox(l_String_length(t)) == n + 4);
    assert(clean_unbox(l_String_isEmpty(a)) == 0);
    l_IO_println(t);
    uint32_t cps[] = {0, 233, 8364, 128512 + n};
    for (size_t i = 0; i < 4; i++) {
        clean_obj* pushed = l_String_push(t, clean_box_uint32(cps[i]));
        l_IO_println(pushed);
        clean_dec(pushed);
        clean_obj* rendered = clean_apply_1(l_instToStringChar(), clean_box_uint32(cps[i]));
        l_IO_println(rendered);
        clean_dec(rendered);
    }
    l_IO_println(t);
    clean_dec(t); clean_dec(a); clean_dec(tail); clean_dec(s);
    return 0;
}
"#;

#[test]
fn shipped_push_and_char_shims_preserve_bytes_and_borrowed_shared_prefixes() {
    let shims = select_shims_for_c_text(DRIVER).expect("select actual production shims");
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
    let (includes, main) = DRIVER.split_once("int main").expect("driver main");
    std::fs::write(
        dir.path().join("main.c"),
        format!("{includes}\n{shims}\nint main{main}"),
    )
    .expect("driver plus shipped shim definitions");
    let binary = dir.path().join("push");
    let cc = Command::new("cc")
        .args(["-std=c11", "-O2"])
        .arg("-I")
        .arg(dir.path())
        .arg(dir.path().join("main.c"))
        .arg(dir.path().join("runtime.c"))
        .arg("-lm")
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("C compiler required");
    assert!(
        cc.status.success(),
        "{}",
        String::from_utf8_lossy(&cc.stderr)
    );
    for prefix in ["", "suffix7", "é🦀"] {
        let out = Command::new(&binary)
            .arg(prefix)
            .output()
            .expect("execute shipped push");
        let t = format!("{prefix}\0β\x007");
        let mut expected = format!("{t}\n");
        for cp in [0, 233, 8364, 128512 + prefix.chars().count() as u32] {
            let c = char::from_u32(cp).expect("valid scalar");
            expected.push_str(&format!("{t}{c}\n{c}\n"));
        }
        expected.push_str(&format!("{t}\n"));
        assert_eq!(out.status.code(), Some(0), "{:?}", out.stderr);
        assert_eq!(out.stdout, expected.as_bytes(), "{prefix:?}");
        assert!(out.stderr.is_empty());
    }
}
