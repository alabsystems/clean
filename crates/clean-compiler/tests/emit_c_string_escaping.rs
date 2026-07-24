// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for C string literal emission.
//!
//! Part of #2055.

use clean_compiler::emit_c::emit_c;
use clean_compiler::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

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
        code.contains("clean_mk_string(\"hello\")"),
        "ASCII strings should be emitted unchanged. Got:\n{}",
        code
    );
}

#[test]
fn test_emit_c_string_unicode_preserves_utf8_bytes() {
    let code = emit_c(&[string_decl("unicode", "α")]).unwrap();
    assert!(
        code.contains("clean_mk_string(\"\\316\\261\")"),
        "Unicode strings should be emitted as UTF-8 byte escapes. Got:\n{}",
        code
    );
    assert!(
        !code.contains("\\u{03b1}"),
        "C emission must not use Rust debug-style Unicode escapes. Got:\n{}",
        code
    );
}
