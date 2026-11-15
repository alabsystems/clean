// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for C string literal emission.
//!
//! Part of #2055.

use clean_compiler::emit_c::emit_c;
use clean_compiler::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
mod runtime_fixture;

fn var(n: u32) -> VarId {
    VarId(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn string_decl(name_str: &str, value: &str) -> IRDecl {
    IRDecl {
        name: name(name_str),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::String(value.to_string()),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    }
}

#[test]
fn test_emit_c_string_ascii_unchanged() {
    let code = emit_c(&[string_decl("ascii", "hello")]).unwrap();
    assert!(
        code.contains("clean_mk_string_from_bytes(\"hello\", 5)"),
        "ASCII strings should be emitted unchanged. Got:\n{}",
        code
    );
}

#[test]
fn test_emit_c_string_unicode_preserves_utf8_bytes() {
    let code = emit_c(&[string_decl("unicode", "α")]).unwrap();
    assert!(
        code.contains("clean_mk_string_from_bytes(\"\\316\\261\", 2)"),
        "Unicode strings should be emitted as UTF-8 byte escapes. Got:\n{}",
        code
    );
    assert!(
        !code.contains("\\u{03b1}"),
        "C emission must not use Rust debug-style Unicode escapes. Got:\n{}",
        code
    );
}

#[test]
fn emitted_literals_execute_with_exact_byte_lengths() {
    let literals = ["", "\0", "\0\0", "a\x007", "é\0🦀", "\"\\\n\t"];
    let decls: Vec<_> = literals
        .iter()
        .enumerate()
        .map(|(i, s)| string_decl(&format!("s{i}"), s))
        .collect();
    let code = emit_c(&decls).expect("emit literals");
    let calls: String = (0..literals.len()).map(|i| format!(
        "s = l_s{i}(); fwrite(clean_string_data(s), 1, clean_string_len(s), stdout); clean_dec(s); fputc('|', stdout);\n"
    )).collect();
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("strings.c");
    std::fs::write(
        &source,
        format!("{code}\n#include <stdio.h>\nint main(void) {{ clean_obj* s;\n{calls}return 0; }}"),
    )
    .expect("write emitted program");
    let runtime = runtime_fixture::MaterializedRuntime::materialize();
    let runtime_object = dir.path().join("runtime.o");
    let compiled = std::process::Command::new("cc")
        .args(["-std=c11", "-O2", "-c"])
        .arg("-I")
        .arg(runtime.include_dir())
        .arg(runtime.c_source())
        .arg("-o")
        .arg(&runtime_object)
        .output()
        .expect("compile shipped runtime with native flags");
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let bin = dir.path().join("strings");
    let compiled = std::process::Command::new("cc")
        .args(["-std=c11", "-Wall", "-Werror"])
        .arg("-I")
        .arg(runtime.include_dir())
        .arg(source)
        .arg(runtime_object)
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
    let out = std::process::Command::new(bin)
        .output()
        .expect("execute emitted literals");
    let expected: Vec<u8> = literals
        .iter()
        .flat_map(|s| s.bytes().chain(*b"|"))
        .collect();
    assert!(out.status.success(), "{:?}: {:?}", out.status, out.stderr);
    assert_eq!(out.stdout, expected);
    assert!(out.stderr.is_empty());
}
