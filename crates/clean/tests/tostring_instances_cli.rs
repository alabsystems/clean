// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's core `ToString` family renders the RIGHT TEXT through `clean run`.
//!
//! Measured 2026-08-27 before the instances were registered: `toString` on an
//! `Int`, a `Char`, a `UInt32`, a `UInt64` or a `List` did not fail at
//! runtime — it failed at elaboration, with
//! `failed to synthesize instance `ToString Int`` and friends. So the whole
//! family was outside the compiler pillar, and `List.foldl (·+·) 0 [1,2,3,4]`
//! could not be printed at all (its result defaults to `UInt64`).
//!
//! Every assertion here is on the EXACT printed bytes, never on "it built and
//! exited 0". That is deliberate and bought with a bug: the sibling defect
//! fixed in `cdd16e470` was `toString` rendering every non-`Nat` value as a
//! decimal number — `toString "world"` printed `5` — with exit status 0 and no
//! diagnostic. A test that only checked the build would have passed on all of
//! it. Two of the lines below are specifically shaped to catch a renderer that
//! reverted to that behaviour:
//!
//!  * `toString 'a'` must print `a`, not `97` (the code point) and not the
//!    empty string (a `String.mk [c]` ctor cell read as a byte string).
//!  * `toString ["a", "b"]` must print `[a, b]`, which is only possible if the
//!    list instance renders each ELEMENT through the element's own instance.
//!    A list renderer wired to `Nat` would print numbers here.
//!
//! The driver is the real `clean` binary, not the in-crate build helper: the
//! repo's landing rule is that a capability does not count without the
//! production caller that invokes it.

#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn cc_available() -> bool {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    Command::new(cc)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn write_lean(dir: &Path, name: &str, source: &str) -> PathBuf {
    let file = dir.join(name);
    std::fs::write(&file, source).expect("write lean fixture");
    file
}

fn run_decl(file: &Path, decl: &str) -> Output {
    Command::new(clean_path())
        .arg("run")
        .arg(file)
        .args(["--decl", decl])
        .output()
        .unwrap_or_else(|err| panic!("failed to spawn clean run --decl {decl}: {err}"))
}

fn assert_prints(file: &Path, decl: &str, expected: &str) {
    let output = run_decl(file, decl);
    assert!(
        output.status.success(),
        "`clean run --decl {decl}` failed: status={:?}\nstdout={}\nstderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        expected,
        "`clean run --decl {decl}` printed the wrong text; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// `ToString Int`: both constructors and zero.
///
/// `Int.negSucc n` denotes `-(n+1)`, so the negative arm has to render
/// `n + 1`, not `n` — `-5` vs `-4` is exactly the off-by-one a hand-written
/// recursor split gets wrong, and `0` pins that the `ofNat` arm is not
/// sign-prefixed.
#[test]
fn clean_run_renders_int_with_sign() {
    if !cc_available() {
        eprintln!("skipping clean_run_renders_int_with_sign: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_int.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString (5 : Int))\n  \
         IO.println (toString (-5 : Int))\n  \
         IO.println (toString (0 : Int))\n",
    );
    assert_prints(&file, "main", "5\n-5\n0\n");
}

/// `ToString Char` must print the CHARACTER.
///
/// `97` would mean the code point leaked through a `Nat` renderer; an empty
/// line would mean the `String.mk [c]` body was lowered from source into a
/// constructor cell and then read as the byte-string carrier. `é` is the
/// multi-byte leg: a shim that wrote `(char)cp` unconditionally would emit one
/// truncated byte.
#[test]
fn clean_run_renders_char_as_its_character() {
    if !cc_available() {
        eprintln!("skipping clean_run_renders_char_as_its_character: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_char.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString 'a')\n  \
         IO.println (toString 'Z')\n  \
         IO.println (toString 'é')\n",
    );
    assert_prints(&file, "main", "a\nZ\né\n");
}

/// `ToString UInt32` / `ToString UInt64` render the numeric value.
///
/// The large `UInt64` value is the one that matters: it is above `2^32`, so a
/// `toNat` that truncated to the `UInt32` window would print a different
/// number, and it is above `2^31` so a signed read would print a negative one.
#[test]
fn clean_run_renders_unsigned_widths() {
    if !cc_available() {
        eprintln!("skipping clean_run_renders_unsigned_widths: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_uint.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString (7 : UInt32))\n  \
         IO.println (toString (4294967295 : UInt32))\n  \
         IO.println (toString (9 : UInt64))\n  \
         IO.println (toString (4294967296 : UInt64))\n",
    );
    assert_prints(&file, "main", "7\n4294967295\n9\n4294967296\n");
}

/// `ToString (List α)` renders Lean's own bracketed, comma-separated form —
/// and renders each element through the ELEMENT's instance.
///
/// The `List String` line is the discriminating one: `[a, b]` is only
/// reachable if `instToStringString` (the identity) rendered the elements. A
/// list renderer that assumed `Nat` would print numbers, and the pre-`cdd16e470`
/// projection would have printed the strings' `len` fields.
#[test]
fn clean_run_renders_lists_through_the_element_instance() {
    if !cc_available() {
        eprintln!("skipping clean_run_renders_lists_through_the_element_instance: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_list.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString ([1, 2, 3] : List Nat))\n  \
         IO.println (toString ([7] : List Nat))\n  \
         IO.println (toString (([] : List Nat)))\n  \
         IO.println (toString ([\"a\", \"b\"] : List String))\n  \
         IO.println (toString ([true, false] : List Bool))\n",
    );
    assert_prints(&file, "main", "[1, 2, 3]\n[7]\n[]\n[a, b]\n[true, false]\n");
}

/// The instances compose: a list of ints, and a nested list.
///
/// Nesting is what proves the `List` instance is a genuine parametric instance
/// rather than a family of monomorphic ones — the inner `ToString (List Nat)`
/// is resolved as the element instance of the outer `ToString (List (List Nat))`.
#[test]
fn clean_run_renders_nested_and_mixed_containers() {
    if !cc_available() {
        eprintln!("skipping clean_run_renders_nested_and_mixed_containers: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_nested.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString ([1, -2, 3] : List Int))\n  \
         IO.println (toString ([[1, 2], [3]] : List (List Nat)))\n",
    );
    assert_prints(&file, "main", "[1, -2, 3]\n[[1, 2], [3]]\n");
}

/// REGRESSION for the three instances that already worked, run through the
/// same rebuilt binary.
///
/// Registering five new instances changes what instance synthesis sees for
/// `ToString`; this is the leg that would go red if a new instance started
/// winning a goal that `Nat`/`String`/`Bool` used to win.
#[test]
fn clean_run_keeps_rendering_the_three_original_instances() {
    if !cc_available() {
        eprintln!("skipping clean_run_keeps_rendering_the_three_original_instances: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_control.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString \"world\")\n  \
         IO.println (toString true)\n  \
         IO.println (toString false)\n  \
         IO.println (toString (40 + 2))\n",
    );
    assert_prints(&file, "main", "world\ntrue\nfalse\n42\n");
}
