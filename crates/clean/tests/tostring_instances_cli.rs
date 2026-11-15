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

/// The opt-out an environment genuinely without a C compiler must set by hand.
pub const CC_REQUIRED: &str = "a C compiler is required by this byte-exact suite";

fn cc_available() -> bool {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    Command::new(cc)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Require a C compiler. FAIL-CLOSED, with no skip path at all.
///
/// Every test in this file used to open with
/// `if !cc_available() { eprintln!("skipping …: no cc"); return; }`, so on any
/// box without `cc` all nine passed having asserted NOTHING — the same thing
/// `#[ignore]` does, wearing a disguise, and this repo's rule is that a test
/// PASSES, FAILS, or is DELETED.
///
/// That matters more here than it usually would. This suite exists because a
/// projection shim once decimal-rendered every non-`Nat` value at exit status 0
/// with no diagnostic, so its whole job is to assert the exact BYTES a program
/// prints. A silent skip turns the one instrument that watches for silently
/// wrong output into a green light.
///
/// There is deliberately NO opt-out, and the first draft of this fix had one.
/// An env-gated skip still leaves a bare `return` in every test, which
/// `scripts/check_self_skipping_tests.py` flags as `EARLY_RETURN` for exactly
/// the right reason: the assertions remain conditional on something other than
/// the thing they measure. The precedent is
/// `clean_olean::test_support::PINNED_LEAN_REQUIRED`, which panics when its
/// toolchain is absent and offers no escape either.
///
/// So: no C compiler, no verdict, and the run says so.
fn require_cc(test: &str) {
    if cc_available() {
        return;
    }
    panic!(
        "{test}: {CC_REQUIRED}, and none was found (tried $CC, else `cc`). \
         This suite asserts the exact bytes a compiled program prints, so \
         skipping it silently would retire the only check that catches \
         silently-wrong output. Install a C compiler to run this suite."
    );
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
    require_cc("clean_run_renders_int_with_sign");
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

/// Both Int notation and explicit E-rounding heads must lower and execute.
/// The noinline, parameterized helpers exercise the checked recursor bodies;
/// a successful tactic reduction alone cannot satisfy these stdout checks.
#[test]
fn clean_run_executes_euclidean_int_division_and_remainder() {
    require_cc("clean_run_executes_euclidean_int_division_and_remainder");
    let mut source = String::from(
        "@[noinline] def notationQuotient (a b : Int) : Int := a / b\n\
         @[noinline] def explicitQuotient (a b : Int) : Int := Int.ediv a b\n\
         @[noinline] def notationRemainder (a b : Int) : Int := a % b\n\
         @[noinline] def explicitRemainder (a b : Int) : Int := Int.emod a b\n\
         def main : IO Unit := do\n",
    );
    let mut expected = String::new();
    for (a, b, quotient, remainder) in [
        (7_i64, 2_i64, 3_i64, 1_i64),
        (-7, 2, -4, 1),
        (7, -2, -3, 1),
        (-7, -2, 4, 1),
        (6, 3, 2, 0),
        (-6, 3, -2, 0),
        (6, -3, -2, 0),
        (-6, -3, 2, 0),
        (-1, 256, -1, 255),
        (0, 2, 0, 0),
        (0, -2, 0, 0),
        (7, 0, 0, 7),
        (-7, 0, 0, -7),
        (0, 0, 0, 0),
    ] {
        for (function, answer) in [
            ("notationQuotient", quotient),
            ("explicitQuotient", quotient),
            ("notationRemainder", remainder),
            ("explicitRemainder", remainder),
        ] {
            source.push_str(&format!(
                "  IO.println (toString ({function} ({a}) ({b})))\n"
            ));
            expected.push_str(&answer.to_string());
            expected.push('\n');
        }
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(dir.path(), "int_euclidean.lean", &source);
    assert_prints(&file, "main", &expected);
}

/// Lean's F-rounding `Int.fdiv`/`Int.fmod` must lower and execute with Lean's
/// values (R168), a zero dividend over a negative divisor among them. Its own
/// `main`: one `do` block holding these rows and the E-rounding test's
/// overflows a debug `clean run`'s stack.
#[test]
fn clean_run_executes_floor_int_division_and_remainder() {
    require_cc("clean_run_executes_floor_int_division_and_remainder");
    let mut source = String::from(
        "@[noinline] def floorQuotient (a b : Int) : Int := Int.fdiv a b\n\
         @[noinline] def floorRemainder (a b : Int) : Int := Int.fmod a b\n\
         def main : IO Unit := do\n",
    );
    let mut expected = String::new();
    // `(a, b, Int.fdiv a b, Int.fmod a b)`, Lean 4.8.0's values.
    for (a, b, quotient, remainder) in [
        (7_i64, 2_i64, 3_i64, 1_i64),
        (-7, 2, -4, 1),
        (7, -2, -4, -1),
        (-7, -2, 3, -1),
        (6, -3, -2, 0),
        (-6, 3, -2, 0),
        (-1, 256, -1, 255),
        (1, -256, -1, -255),
        (0, 2, 0, 0),
        (0, -2, 0, 0),
        (7, 0, 0, 7),
        (-7, 0, 0, -7),
        (0, 0, 0, 0),
    ] {
        for (function, answer) in [("floorQuotient", quotient), ("floorRemainder", remainder)] {
            source.push_str(&format!(
                "  IO.println (toString ({function} ({a}) ({b})))\n"
            ));
            expected.push_str(&answer.to_string());
            expected.push('\n');
        }
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(dir.path(), "int_floor.lean", &source);
    assert_prints(&file, "main", &expected);
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
    require_cc("clean_run_renders_char_as_its_character");
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
    require_cc("clean_run_renders_unsigned_widths");
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
    require_cc("clean_run_renders_lists_through_the_element_instance");
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
    require_cc("clean_run_renders_nested_and_mixed_containers");
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
/// Registering eight new instances (five on 2026-08-27, `UInt8`/`UInt16`/
/// `USize` on 2026-09-16) changes what instance synthesis sees for `ToString`;
/// this is the leg that would go red if a new instance started winning a goal
/// that `Nat`/`String`/`Bool` used to win.
#[test]
fn clean_run_keeps_rendering_the_three_original_instances() {
    require_cc("clean_run_keeps_rendering_the_three_original_instances");
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

/// `ToString UInt8` / `ToString UInt16` / `ToString USize` render the numeric
/// value, at 0 and at the top of each width.
///
/// Measured 2026-09-16 BEFORE these three were registered: each of the three
/// `toString` calls below failed ELABORATION with "failed to synthesize
/// instance `ToString UInt8`" (and the `UInt16` / `USize` spellings), while
/// `IO.println (toString (UInt8.toNat (7 : UInt8)))` in the same file already
/// compiled, linked, ran and printed `7`. So the gap was the registration, and
/// this test is what says the registration renders the RIGHT TEXT.
///
/// Every expected byte is the pinned Lean v4.30.0-rc2's own output for the
/// identical program, captured with
/// `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean --run`.
/// Two legs discriminate: `65535` would print `255` if a `UInt16` were rendered
/// through the `UInt8` carrier, and `4294967296` is above `2^32`, so a
/// `USize.toNat` truncated to the `UInt32` window would print `0`.
/// `9223372036854775807` is `2^63 - 1`, the largest value the runtime's tagged
/// scalar box holds (`CLEAN_MAX_SMALL`);
/// `clean_run_usize_above_the_tagged_box_ceiling_prints_leans_value` covers
/// what happens above it.
#[test]
fn clean_run_renders_uint8_uint16_usize_at_their_boundaries() {
    require_cc("clean_run_renders_uint8_uint16_usize_at_their_boundaries");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_small_uint.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString (0 : UInt8))\n  \
         IO.println (toString (255 : UInt8))\n  \
         IO.println (toString (7 : UInt8))\n  \
         IO.println (toString (0 : UInt16))\n  \
         IO.println (toString (65535 : UInt16))\n  \
         IO.println (toString (300 : UInt16))\n  \
         IO.println (toString (0 : USize))\n  \
         IO.println (toString (4294967296 : USize))\n  \
         IO.println (toString (9223372036854775807 : USize))\n",
    );
    assert_prints(
        &file,
        "main",
        "0\n255\n7\n0\n65535\n300\n0\n4294967296\n9223372036854775807\n",
    );
}

/// NEGATIVE CONTROL: the rendering is of the WRAPPED carrier value, through the
/// carrier's OWN instance.
///
/// `UInt8.ofNat` wraps mod `2^8`, so `(256 : UInt8)` IS `0` — pinned Lean
/// v4.30.0-rc2 prints `0`, `0`, `0`, `[1, 2, 3]`, `[300]` for this program.
/// A renderer that printed the pre-truncation `Nat` the literal was built from
/// would print `256` / `65536` here with exit status 0 and no diagnostic, which
/// is the silently-wrong-output shape this whole file exists to catch. The
/// `(300 : UInt16)` line is the instance-SELECTION leg: routed through
/// `instToStringUInt8` it would print `44` (300 mod 256). The two list lines
/// are the composition leg — `[1, 2, 3]` is only reachable if
/// `instToStringList` rendered each element through the `UInt8` instance.
#[test]
fn clean_run_renders_the_wrapped_uint_value_not_the_literal() {
    require_cc("clean_run_renders_the_wrapped_uint_value_not_the_literal");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_uint_wrap.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString (256 : UInt8))\n  \
         IO.println (toString (65536 : UInt16))\n  \
         IO.println (toString ((255 : UInt8) + 1))\n  \
         IO.println (toString ([1, 2, 3] : List UInt8))\n  \
         IO.println (toString ([300] : List UInt16))\n",
    );
    assert_prints(&file, "main", "0\n0\n0\n[1, 2, 3]\n[300]\n");
}

/// A `USize` at or above `2^63` renders Lean's value, not the tagged box's
/// ceiling. Pinned Lean v4.30.0-rc2 prints `18446744073709551615`.
///
/// This test used to PIN THE DEFECT: it asserted `9223372036854775807`
/// (`2^63 - 1`), because `emit_c`'s `IRExpr::Box` arm boxed a `USize` with the
/// tagged `clean_box((size_t)x)`, whose `CLEAN_MAX_SMALL` is `2^63 - 1`
/// (`crates/clean-runtime/include/clean_runtime.h`), so bit 63 was dropped
/// wherever a `USize` crossed a boxed boundary. Its own doc said that the day
/// the box carried a full `USize` it would go red and be changed to Lean's
/// bytes. That day was 2026-09-18: WS6.1's review commit made the C backend box
/// a `USize` with the runtime's one Nat spelling, `clean_nat_of_u64` (tagged
/// below `2^63`, a heap Nat above), and nothing re-read this test, so it sat
/// red. Re-measured 2026-09-25 on the P0_EXEC branch: `clean compile --emit c`
/// boxes this program's `USize.ofNat` result with `clean_nat_of_u64`, and
/// `clean run` prints `18446744073709551615` at exit 0, byte-identical to
/// pinned Lean.
#[test]
fn clean_run_usize_above_the_tagged_box_ceiling_prints_leans_value() {
    require_cc("clean_run_usize_above_the_tagged_box_ceiling_prints_leans_value");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_usize_ceiling.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString (18446744073709551615 : USize))\n",
    );
    assert_prints(&file, "main", "18446744073709551615\n");
}

/// `ToString (Option α)` renders Lean's `(some x)` / `none`, through the
/// ELEMENT's instance, and composes with itself and with `List`.
///
/// Every expected byte here was produced by the pinned `lean 4.30.0-rc2`
/// (`#eval toString …`, quotes stripped), not by reading Lean's source:
///
/// ```text
/// toString (some 3 : Option Nat)          "(some 3)"
/// toString (none : Option Nat)            "none"
/// toString (some (some 3))                "(some (some 3))"
/// toString (some (none : Option Nat))     "(some none)"
/// toString ([some 1, none] : List _)      "[(some 1), none]"
/// toString (some [1, 2])                  "(some [1, 2])"
/// ```
///
/// The `none` leg is the one that catches a minor-order slip: `Option.rec`
/// takes its minors in constructor order (`none` then `some`), and a swapped
/// pair type-checks in neither direction only because the `some` minor is a
/// function — get it wrong and this prints `(some …)` for `none`.
/// `List (Option Nat)` is the composition leg: the outer `List` instance's
/// element instance IS this one, so `[(some 1), none]` is only reachable if
/// both are genuine parametric instances.
#[test]
fn clean_run_renders_options_like_lean() {
    require_cc("clean_run_renders_options_like_lean");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_option.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString (some 3 : Option Nat))\n  \
         IO.println (toString (none : Option Nat))\n  \
         IO.println (toString (some (some 3) : Option (Option Nat)))\n  \
         IO.println (toString (some (none : Option Nat)))\n  \
         IO.println (toString ([some 1, none] : List (Option Nat)))\n  \
         IO.println (toString (some ([1, 2] : List Nat)))\n",
    );
    assert_prints(
        &file,
        "main",
        "(some 3)\nnone\n(some (some 3))\n(some none)\n[(some 1), none]\n(some [1, 2])\n",
    );
}

/// `ToString (α × β)` renders Lean's `(a, b)`, each component through its OWN
/// instance, at two independent universes.
///
/// Expected bytes from the pinned `lean 4.30.0-rc2`:
///
/// ```text
/// toString ((1, 2) : Nat × Nat)             "(1, 2)"
/// toString ((1, 2, 3) : Nat × Nat × Nat)    "(1, (2, 3))"
/// toString ((true, 'x'))                    "(true, x)"
/// toString ((some 1, "a"))                  "((some 1), a)"
/// toString ([(1,2),(3,4)] : List (Nat × Nat))  "[(1, 2), (3, 4)]"
/// toString (([1,2], [3]))                   "([1, 2], [3])"
/// ```
///
/// `(1, (2, 3))` is the leg worth stating out loud: Lean does NOT flatten a
/// right-nested pair, because this instance appends the two renderings raw with
/// no `addParenHeuristic`, and the right component brings its own parentheses.
/// A "tidier" `(1, 2, 3)` would be a divergence, not an improvement.
/// `(true, 'x')` mixes two DIFFERENT element instances in one pair, which is
/// what rules out a body that reuses the left instance for both components —
/// that bug prints `(true, ...)` on the left and then renders `'x'` as a
/// `Bool`.
#[test]
fn clean_run_renders_pairs_like_lean() {
    require_cc("clean_run_renders_pairs_like_lean");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_prod.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString ((1, 2) : Nat × Nat))\n  \
         IO.println (toString ((1, 2, 3) : Nat × Nat × Nat))\n  \
         IO.println (toString ((true, 'x')))\n  \
         IO.println (toString ((some 1, \"a\") : Option Nat × String))\n  \
         IO.println (toString ([(1, 2), (3, 4)] : List (Nat × Nat)))\n  \
         IO.println (toString ((([1, 2] : List Nat), ([3] : List Nat))))\n",
    );
    assert_prints(
        &file,
        "main",
        "(1, 2)\n(1, (2, 3))\n(true, x)\n((some 1), a)\n[(1, 2), (3, 4)]\n([1, 2], [3])\n",
    );
}

/// PINNED DIVERGENCE, not a passing claim: Lean's `Option` instance wraps the
/// element rendering in `addParenHeuristic` and Clean's does not.
///
/// `addParenHeuristic` (`Init/Data/ToString/Basic.lean:90`) parenthesizes a
/// rendering that contains whitespace unless it already starts with `(`, `[`,
/// `{` or `#[`. Measured on the pinned `lean 4.30.0-rc2` versus this binary:
///
/// ```text
///                          lean 4.30.0-rc2     clean
/// toString (some "a b")    "(some (a b))"      (some a b)
/// toString (some ' ')      "(some ( ))"        (some  )
/// toString (some "ab")     "(some ab)"         (some ab)     <- agrees
/// ```
///
/// Only a `String` or `Char` element can reach the divergent branch in this
/// prelude; every other registered instance renders without whitespace or
/// behind an opener, so `clean_run_renders_options_like_lean` above is exact.
/// Closing it needs a declared `addParenHeuristic` plus its own C shim —
/// `String.isPrefixOf` / `Char.isWhitespace` exist here only as native whnf
/// reducers, and a body that reaches them through `String.data` is refused by
/// the native build ("the runtime `String` carrier is a flat byte string",
/// `select_shims_from_tables`). This test asserts the bytes Clean prints TODAY
/// so that the day the helper lands it goes red and is read, rather than the
/// divergence surviving as a comment nobody re-measures.
#[test]
fn clean_run_option_element_paren_heuristic_is_not_applied() {
    require_cc("clean_run_option_element_paren_heuristic_is_not_applied");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_option_paren.lean",
        "def main : IO Unit := do\n  \
         IO.println (toString (some \"a b\"))\n  \
         IO.println (toString (some \"ab\"))\n  \
         IO.println (toString (some ' '))\n",
    );
    assert_prints(&file, "main", "(some a b)\n(some ab)\n(some  )\n");
}

/// NEGATIVE CONTROL: the two new parametric instances must not answer a goal
/// they do not inhabit.
///
/// `Sum α β` is the sharp case — it has the same `{α} {β}` shape as
/// `instToStringProd`, and Lean does register `ToString (Sum α β)` while this
/// prelude does not. So the goal is one a candidate could plausibly be
/// mis-unified onto, and the required outcome is still a refusal naming the
/// carrier. If this ever starts passing, an instance is inhabiting `Sum`
/// through `Prod`'s or `Option`'s body and the rendering is garbage.
#[test]
fn clean_check_still_refuses_a_carrier_with_no_tostring_instance() {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_negative.lean",
        "def bad : String := toString (Sum.inl 1 : Sum Nat Nat)\n",
    );
    let output = Command::new(clean_path())
        .arg("check")
        .arg(&file)
        .output()
        .unwrap_or_else(|err| panic!("failed to spawn clean check: {err}"));
    assert!(
        !output.status.success(),
        "`clean check` must fail on a carrier with no ToString instance; stdout={}",
        String::from_utf8_lossy(&output.stdout)
    );
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        combined.contains("failed to synthesize instance `ToString (Sum Nat Nat)`"),
        "the refusal must name the Sum carrier, got: {combined}"
    );
}

/// `private` definitions compile and run under their module-local kernel
/// names (`_private.priv_run.0.double`, G21 brick B4: `clean run` names the
/// file's module as `clean check` does). The bytes are pinned Lean 4.8.0's
/// `lean --run` output for the same file, and the release build before B4
/// (plain names) printed the same.
#[test]
fn clean_run_private_definitions_print_the_same_bytes() {
    require_cc("clean_run_private_definitions_print_the_same_bytes");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "priv_run.lean",
        "private def double (n : Nat) : Nat := n * 2\n\
         private def greet (s : String) : String := \"hi \" ++ s\n\
         namespace Foo\n\
         private def tripled (n : Nat) : Nat := n * 3\n\
         end Foo\n\
         def main : IO Unit := do\n  \
         IO.println (toString (double 21))\n  \
         IO.println (greet \"there\")\n  \
         IO.println (toString (Foo.tripled 3))\n",
    );
    assert_prints(&file, "main", "42\nhi there\n9\n");
}

/// `ToString Float` (G27, 2026-10-08): the builtin prelude gained
/// `instToStringFloat := ⟨Float.toString⟩` so `s!"float:{x}"` ELABORATES, as
/// in Lean 4.8.0. `Float.toString` is an extern opaque whose prelude value is
/// the stand-in `fun _ => ""`, classified `Placeholder` by the native opaque
/// audit, so `clean run` must REFUSE a program that reaches it — pinned Lean
/// prints `2.500000`, and printing an empty line at exit 0 would be silently
/// wrong output. `clean check` of the same file passes.
#[test]
fn clean_run_refuses_float_tostring_rather_than_printing_the_stand_in() {
    require_cc("clean_run_refuses_float_tostring_rather_than_printing_the_stand_in");
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_lean(
        dir.path(),
        "ts_float.lean",
        "def atom (x : Float) : String := s!\"float:{x}\"\n\
         def main : IO Unit := IO.println (atom 2.5)\n",
    );
    let check = Command::new(clean_path())
        .arg("check")
        .arg(&file)
        .output()
        .unwrap_or_else(|err| panic!("failed to spawn clean check: {err}"));
    assert!(
        check.status.success(),
        "`clean check` must accept `ToString Float`: stdout={} stderr={}",
        String::from_utf8_lossy(&check.stdout),
        String::from_utf8_lossy(&check.stderr)
    );
    let output = run_decl(&file, "main");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !output.status.success(),
        "`clean run` must refuse the placeholder `Float.toString`, not print {stdout:?}"
    );
    assert!(
        !stdout.contains("float:"),
        "nothing may be printed from the stand-in body: {stdout:?}"
    );

    // The program above refuses on the literal's `Float.ofScientific` before
    // it reaches `Float.toString`, so it cannot fail for this subject alone.
    // This one reaches `Float.toString` (through `instToStringFloat`) with no
    // other Float placeholder on the path, so the refusal must NAME it: delete
    // the `Float.toString` audit row and this assertion fails.
    let only = write_lean(
        dir.path(),
        "ts_float_only.lean",
        "def atom (x : Float) : String := s!\"float:{x}\"\n\
         def main : IO Unit :=\n  IO.println (toString ([atom] : List (Float → String)).length)\n",
    );
    let output = run_decl(&only, "main");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "`clean run` must refuse the placeholder `Float.toString`: stdout={stdout:?}"
    );
    assert!(
        stderr.contains("`Float.toString`"),
        "the refusal must name `Float.toString`: stderr={stderr}"
    );
}
