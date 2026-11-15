// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `String` carrier audit: the scan itself, and — end to end through the
//! production emit path `clean run` uses — the measured programs that printed
//! a wrong answer at exit 0 before it.

use std::path::PathBuf;

use clean_kernel::{BinderInfo, Expr, Name};

use super::*;
use crate::native_build::emit_entry_c_with_type;

fn emit(source: &str) -> anyhow::Result<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let file: PathBuf = dir.path().join("string_carrier_fixture.lean");
    std::fs::write(&file, source).expect("write fixture");
    emit_entry_c_with_type(&file, "main", 0).map(|(c, _)| c)
}

fn refusal(source: &str) -> String {
    let err = emit(source).expect_err("the String carrier audit must refuse this program");
    format!("{err:#}")
}

fn string_ty() -> Expr {
    Expr::const_(Name::from_string("String"), vec![])
}

#[test]
fn test_check_string_carrier_constructor_projection_and_eliminator_are_refused() {
    let decl = Name::from_string("f");
    let ctor = Expr::app(
        Expr::const_(Name::from_string("String.mk"), vec![]),
        Expr::const_(Name::from_string("xs"), vec![]),
    );
    let err = check_string_carrier(&decl, &ctor).expect_err("String.mk builds a cell");
    assert!(err.to_string().contains("native-string-carrier"), "{err}");
    assert!(err.to_string().contains("`String.mk`"), "{err}");

    let proj = Expr::lam(
        BinderInfo::Default,
        string_ty(),
        Expr::proj(Name::from_string("String"), 0, Expr::bvar(0)),
    );
    let err = check_string_carrier(&decl, &proj).expect_err("s.1 reads a cell field");
    assert!(err.to_string().contains("projects a field"), "{err}");

    let cases = Expr::app(
        Expr::const_(Name::from_string("String.casesOn"), vec![]),
        Expr::const_(Name::from_string("s"), vec![]),
    );
    check_string_carrier(&decl, &cases).expect_err("String.casesOn reads a cell field");
}

#[test]
fn test_check_string_carrier_types_and_other_structures_pass() {
    let decl = Name::from_string("f");
    // A binder TYPE is erased: `fun (x : String.mk [] = s) => x` runs nothing
    // of `String.mk`.
    let in_type = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("String.mk"), vec![]),
        Expr::bvar(0),
    );
    check_string_carrier(&decl, &in_type).expect("a binder type is not computational");
    // Another structure's projection is not the String carrier.
    let other = Expr::proj(
        Name::from_string("Prod"),
        0,
        Expr::const_(Name::from_string("p"), vec![]),
    );
    check_string_carrier(&decl, &other).expect("Prod.1 is a real cell");
    // Ordinary string operations go through their shims.
    let append = Expr::app(
        Expr::const_(Name::from_string("String.append"), vec![]),
        Expr::str_lit("a"),
    );
    check_string_carrier(&decl, &append).expect("String.append is a shimmed operation");
}

/// Measured 2026-09-25 through `clean run`: printed an empty line at exit 0.
/// Pinned Lean v4.30.0-rc2 prints `42`. The prelude's `Nat.repr` reaches the
/// cell through `List.asString`, which is the declaration refused.
#[test]
fn test_native_emit_nat_repr_is_refused_not_miscompiled() {
    let msg = refusal("def main : IO Unit := IO.println (toString (Nat.repr 42))\n");
    assert!(msg.contains("native-string-carrier"), "{msg}");
    assert!(msg.contains("`List.asString`"), "{msg}");
}

/// Measured 2026-09-25 through `clean run`: printed an empty line at exit 0.
/// Pinned Lean v4.30.0-rc2 prints `ab`.
#[test]
fn test_native_emit_list_as_string_is_refused_not_miscompiled() {
    let msg = refusal("def main : IO Unit := IO.println ['a', 'b'].asString\n");
    assert!(msg.contains("native-string-carrier"), "{msg}");
}

/// Measured 2026-09-25 through `clean run`: `"abc" == String.mk ['a','b','c']`
/// printed `false` at exit 0 (Lean: `true`), and `"ab".data` died with SIGSEGV.
#[test]
fn test_native_emit_user_string_cell_use_is_refused() {
    let msg = refusal(
        "def main : IO Unit := IO.println (toString (\"abc\" == String.mk ['a', 'b', 'c']))\n",
    );
    assert!(msg.contains("native-string-carrier"), "{msg}");
    assert!(msg.contains("`main`"), "{msg}");
    let msg = refusal("def main : IO Unit := IO.println (toString \"ab\".data)\n");
    assert!(msg.contains("native-string-carrier"), "{msg}");
}

/// The control: string code that goes through the runtime's own string
/// operations still compiles (pinned Lean prints `cd25`).
#[test]
fn test_native_emit_shimmed_string_code_still_compiles() {
    emit(
        "def main : IO Unit := IO.println (\"c\" ++ \"d\" ++ toString \"ab\".length ++ \
         toString (2 + 3))\n",
    )
    .expect("shimmed string operations never build the prelude's cell");
}
