// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A structure or inductive with a TYPE-valued field (`α : Type`) compiles and
//! prints what Lean prints.
//!
//! Before 2026-10-07 `clean-compiler`'s constructor table refused the whole
//! environment at the first constructor field whose declared type is a
//! universe (`unsupported IR type expression: Sort(..)`), so any program that
//! declared such a structure -- and every program elaborated over
//! `import Lean`, whose library has them -- was refused at lowering, whatever
//! it used. The field is a type, erased at runtime
//! (`clean_compiler::to_ir::types::ctor_field_ir_type`).
//!
//! The expected bytes are REAL Lean's: `lean --run` of this exact program on
//! the pinned toolchain (v4.30.0-rc2, 2026-10-07) printed
//! `111\n8\n7\n9:false:ok\n`, and `clean run` of it prints the same bytes.
//! Lean gives the type field no slot (`lean -c`: `Box.mk` is
//! `lean_alloc_ctor(0, 2, 1)`, `m` is `lean_ctor_get(x, 1)`); Clean keeps an
//! object slot holding the boxed unit, as it does for a proof field. The
//! layouts differ; every value the program computes may not, which is what
//! this asserts -- a reader that counted the slot differently from the
//! producer would read `m` as `n`, or the `Bool` from the wrong byte.
//!
//! Three spellings are chosen to stay inside what Clean's FRONTEND accepts
//! today, each a separate open gap measured the same day (Lean accepts all
//! three original spellings): a field `α : Type` at the end of a line swallows
//! the next line's field name as a universe argument (Lean's `Type` level
//! argument is `checkColGt`), so the program writes `Type 0` / `(ty : Type)`;
//! `inductive T where | node : (β : Type) → …` needs its `Type 1` written
//! (Lean infers it); and a `Bool` LITERAL stored straight into a constructor's
//! scalar field is refused at lowering ("scalar field … receives an
//! object-typed value"), so the `Bool`s arrive as parameters.

#![cfg(unix)]

use std::path::PathBuf;
use std::process::Command;

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// Require a C compiler, FAIL-CLOSED with no skip path: a byte-exact suite
/// that skips silently asserts nothing (`tostring_instances_cli.rs`).
fn require_cc() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let found = Command::new(&cc)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    assert!(
        found,
        "a C compiler is required by this byte-exact suite (tried `{cc}`); none was found"
    );
}

const PROGRAM: &str = "\
structure Box where
  α : Type 0
  n : Nat
  b : Bool
  m : Nat

def mkBox (k : Nat) (b : Bool) : Box := { α := Nat, n := k, b := b, m := k + 1 }

def useBox (x : Box) : Nat := x.n + x.m + (if x.b then 100 else 0)

inductive T : Type 1 where
  | leaf : T
  | node : (β : Type) → Nat → T → T

def depth : T → Nat
  | .leaf => 0
  | .node _ k t => k + depth t

structure Pkt where
  tag : Nat
  (ty : Type)
  flag : Bool
  payload : String

def mkPkt (t : Nat) (f : Bool) (s : String) : Pkt := { tag := t, ty := String, flag := f, payload := s }

def describe (p : Pkt) : String := toString p.tag ++ \":\" ++ toString p.flag ++ \":\" ++ p.payload

def main : IO Unit := do
  IO.println (toString (useBox (mkBox 5 true)))
  IO.println (toString (mkBox 7 false).m)
  IO.println (toString (depth (.node Nat 3 (.node Bool 4 .leaf))))
  IO.println (describe (mkPkt 9 false \"ok\"))
";

/// Lean v4.30.0-rc2's `lean --run` output for `PROGRAM`, byte for byte.
const LEAN_PRINTS: &str = "111\n8\n7\n9:false:ok\n";

#[test]
fn type_valued_constructor_fields_print_what_lean_prints() {
    require_cc();
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("sort_field.lean");
    std::fs::write(&file, PROGRAM).expect("write the program");
    let output = Command::new(clean_path())
        .arg("run")
        .arg(&file)
        .args(["--decl", "main"])
        .output()
        .expect("spawn `clean run`");
    assert!(
        output.status.success(),
        "`clean run` failed: status={:?}\nstdout={}\nstderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        LEAN_PRINTS,
        "stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}
