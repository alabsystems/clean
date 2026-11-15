// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression pin — `^^^`, `<<<`, `>>>` and `toUInt{M}` at the machine carriers.
//!
//! ## The gap (measured 2026-09-16, Trust probes 07d / 07e / 07j / 06c / 06d)
//!
//! ```text
//! def bxor (a b : UInt64) : UInt64 := a ^^^ b          -- failed to synthesize HXor UInt64 UInt64 UInt64
//! def shl  (a b : UInt64) : UInt64 := a <<< b          -- failed to synthesize HShiftLeft UInt64 UInt64 UInt64
//! def bxor (a b : UInt64) : UInt64 := UInt64.xor a b   -- Unknown identifier: xor
//! def widen (a : UInt8) (b : UInt64) : UInt64 := a.toUInt64 + b   -- Unknown projection field toUInt64
//! def low8 (a : UInt64) : UInt8 := a.toUInt8           -- Unknown projection field toUInt8
//! ```
//!
//! So a hash, a checksum, a bit-pack or a mixed-width helper could not be
//! STATED — not in a definition, not in a theorem. Same shape as the gap
//! `uint_div_mod_bitwise.rs` pins: the `H*` classes and the name-keyed native
//! reducers were in place; the backing constants and the instances were not.
//!
//! ## The shift amount is the whole risk
//!
//! Lean 4 reduces a machine shift amount MODULO THE WIDTH
//! (`UInt64.shiftLeft a b = ⟨a.toBitVec <<< (UInt64.mod b 64).toBitVec⟩`,
//! `src/Init/Data/UInt/Basic.lean` at v4.30.0-rc2), so `(1 : UInt64) <<< 65 = 2`.
//! Rust's `1u64 << 65` panics in debug and masks in release; `checked_shl`
//! answers `None`. A body that said `0` — the natural guess — would be a false
//! computation in exactly the code this exists for. The values are therefore
//! checked by the KERNEL (`TypeChecker::is_def_eq`), each with a near-miss twin
//! the kernel must refuse, and the false equations are additionally offered as
//! `rfl` THEOREMS, which must not be admitted.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, TypeChecker};
use clean_parser::parse_file;

const WIDTHS: [(&str, u32); 4] = [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)];

/// `(surface operator, the `H*` class it desugars to, the backing operation)`.
const OPS: [(&str, &str, &str); 3] = [
    ("^^^", "HXor", "xor"),
    ("<<<", "HShiftLeft", "shiftLeft"),
    (">>>", "HShiftRight", "shiftRight"),
];

/// Drive the real file pipeline, and KERNEL-CHECK every definition it produces
/// (`TypeChecker::check_type` against the declared type) before registering it.
/// A pass here is therefore not an elaborator self-report.
fn elaborate_file(source: &str) -> Result<(Environment, Vec<(String, Expr)>), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut values = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| e.to_string())?;
        if let ElabResult::Definition { name, ty, val, .. } = &result {
            let tc = TypeChecker::new(&env);
            tc.check_type(val, ty)
                .map_err(|e| format!("kernel rejected {name}: {e}"))?;
            values.push((name.to_string(), val.clone()));
        }
    }
    Ok((env, values))
}

fn expect_value(source: &str) -> Expr {
    let (_, values) = elaborate_file(source)
        .unwrap_or_else(|e| panic!("must elaborate and kernel-check, got: {e}\n{source}"));
    values
        .last()
        .unwrap_or_else(|| panic!("no definition produced\n{source}"))
        .1
        .clone()
}

fn expect_accepted(source: &str) {
    if let Err(e) = elaborate_file(source) {
        panic!("must be ACCEPTED, got: {e}\n{source}");
    }
}

fn expect_refusal(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("must be REFUSED, but was accepted:\n{source}"),
        Err(e) => e,
    }
}

/// Elaborate `lhs`/`rhs` and ask the KERNEL whether the two values are
/// definitionally equal. The elaborator does not get a vote on the answer.
fn kernel_def_eq(carrier: &str, expr: &str, expected: &str) -> bool {
    let source = format!("def lhs : {carrier} := {expr}\n\ndef rhs : {carrier} := {expected}\n");
    let (env, values) = elaborate_file(&source)
        .unwrap_or_else(|e| panic!("must elaborate and kernel-check, got: {e}\n{source}"));
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.is_def_eq(&values[0].1, &values[1].1)
}

fn assert_reduces_to(carrier: &str, expr: &str, expected: &str) {
    assert!(
        kernel_def_eq(carrier, expr, expected),
        "{carrier}: `{expr}` must reduce to `{expected}`"
    );
}

fn assert_does_not_reduce_to(carrier: &str, expr: &str, wrong: &str) {
    assert!(
        !kernel_def_eq(carrier, expr, wrong),
        "{carrier}: `{expr}` = `{wrong}` is FALSE in Lean 4 and must be refused"
    );
}

// ── The gap: the five measured probe sources, verbatim ─────────────────────

#[test]
fn the_measured_probe_sources_elaborate() {
    for source in [
        "def bxor (a : UInt64) (b : UInt64) : UInt64 := a ^^^ b", // 07d
        "def shl (a : UInt64) (b : UInt64) : UInt64 := a <<< b",  // 07e
        "def bxor (a : UInt64) (b : UInt64) : UInt64 := UInt64.xor a b", // 07j
        "def shl (a : UInt64) (b : UInt64) : UInt64 := UInt64.shiftLeft a b", // 07j
        "def widen_add (a : UInt8) (b : UInt64) : UInt64 := a.toUInt64 + b", // 06c
        "def low8 (a : UInt64) : UInt8 := a.toUInt8",             // 06d
    ] {
        let _ = expect_value(source);
    }
}

#[test]
fn xor_and_shifts_elaborate_between_two_variables_at_every_uint_width() {
    for (carrier, _) in WIDTHS {
        for (op, _, _) in OPS {
            let _ = expect_value(&format!(
                "def probe (a b : {carrier}) : {carrier} := a {op} b"
            ));
        }
    }
}

/// Lean reaches `HShiftLeft α α α` through a `@[default_instance]`, so in
/// `a <<< 3` the numeral is typed at the CARRIER. `<<<`/`>>>` are not `binop%`
/// in Lean and are `homogeneous: false` in Clean's desugaring, so this is the
/// case the old "different elaboration problem" note was worried about.
#[test]
fn a_numeral_shift_amount_is_typed_at_the_carrier() {
    for (carrier, _) in WIDTHS {
        for (op, class, operation) in OPS {
            let source = format!(
                "def probe (a : {carrier}) : {carrier} := a {op} 3\n\
                 def explicit (a : {carrier}) : {carrier} := {carrier}.{operation} a (3 : {carrier})"
            );
            let (env, values) = elaborate_file(&source)
                .unwrap_or_else(|e| panic!("must elaborate and kernel-check: {e}\n{source}"));
            let val = &values[0].1;
            let printed = format!("{val:?}");
            let homogeneous_class = class.strip_prefix('H').unwrap_or(class);
            assert!(
                printed.contains(&format!("\"inst{class}{carrier}\""))
                    || (printed.contains(&format!("\"inst{class}\""))
                        && printed.contains(&format!("\"inst{homogeneous_class}{carrier}\""))),
                "`a {op} 3` at {carrier} must select its carrier dictionary, got:\n{printed}"
            );
            assert!(
                TypeChecker::with_mode(&env, env.mode()).is_def_eq(val, &values[1].1),
                "`a {op} 3` at {carrier} must equal the explicit carrier operation"
            );
        }
    }
}

/// The numeral rule is a rule about NUMERALS. A shift amount that carries a
/// type of its own keeps it, and `HShiftLeft UInt{N} Nat _` does not exist in
/// Lean 4 any more than it does here, so the mixed form stays REFUSED. Without
/// this pin the numeral fix could have been "shifts are homogeneous", which
/// would have been a different — and wrong — claim.
#[test]
fn a_typed_nat_shift_amount_is_still_refused() {
    for (carrier, _) in WIDTHS {
        for (op, class, _) in [OPS[1], OPS[2]] {
            let err = expect_refusal(&format!(
                "def probe (a : {carrier}) (n : Nat) : {carrier} := a {op} n"
            ));
            assert!(
                err.contains(&format!(
                    "failed to synthesize instance `{class} {carrier} Nat"
                )),
                "`{op}` at {carrier} with a Nat amount must be refused AS a missing \
                 `{class} {carrier} Nat _` instance, got:\n{err}"
            );
        }
    }
    // ... and the conversion is what makes it legal, at the carrier.
    let _ = expect_value("def probe (a : UInt8) (n : UInt8) : UInt8 := a <<< n");
}

/// The instance that resolves is the CARRIER's, never the `Nat` one: computing
/// a machine shift at `Nat` would drop both the amount-mod-width rule and the
/// wrap.
#[test]
fn the_carrier_instance_resolves_not_the_nat_one() {
    for (carrier, _) in WIDTHS {
        for (op, class, _) in OPS {
            let val = expect_value(&format!(
                "def probe (a b : {carrier}) : {carrier} := a {op} b"
            ));
            let printed = format!("{val:?}");
            assert!(
                printed.contains(&format!("\"inst{class}{carrier}\"")),
                "`{op}` at {carrier} must resolve inst{class}{carrier}, got:\n{printed}"
            );
            assert!(
                !printed.contains(&format!("\"inst{class}Nat\"")),
                "`{op}` at {carrier} must not fall back to the Nat instance:\n{printed}"
            );
        }
    }
}

/// No instance crosses carriers: Lean has no `HXor UInt8 UInt64 _`, and a
/// silently widened operand is the bug a width-typed spec exists to catch.
#[test]
fn mixed_width_operands_are_refused_without_an_explicit_conversion() {
    for (op, _, _) in OPS {
        let _ = expect_refusal(&format!(
            "def probe (a : UInt8) (b : UInt64) : UInt64 := a {op} b"
        ));
        // ... and the explicit conversion is what makes it legal.
        let _ = expect_value(&format!(
            "def probe (a : UInt8) (b : UInt64) : UInt64 := a.toUInt64 {op} b"
        ));
    }
}

/// THE BOUNDARY THAT STILL STANDS. `USize`'s width is
/// `System.Platform.numBits`, opaque in the kernel exactly as in Lean, so there
/// is no literal to reduce a shift amount by and no bound to truncate a
/// conversion to. Every `USize` form stays REFUSED until a platform-width-bound
/// `USize.ofNat` exists; claiming portable semantics without it would be
/// unsound. This replaces the pin `uint_div_mod_bitwise.rs` used to carry for
/// all five carriers.
#[test]
fn usize_is_still_refused_for_xor_shifts_and_conversions() {
    for (op, class, _) in OPS {
        let err = expect_refusal(&format!("def probe (a b : USize) : USize := a {op} b"));
        assert!(
            err.contains(&format!("failed to synthesize instance `{class} USize")),
            "`{op}` at USize must be refused AS a missing instance, got:\n{err}"
        );
    }
    let _ = expect_refusal("def probe (a : USize) : UInt64 := a.toUInt64");
    let _ = expect_refusal("def probe (a : UInt64) : USize := a.toUSize");
}

#[test]
fn the_backing_constants_are_registered_as_definitions() {
    let (env, _) = elaborate_file("def probe (a b : UInt64) : UInt64 := a ^^^ b")
        .expect("must elaborate and kernel-check");
    let mut names = Vec::new();
    for (carrier, _) in WIDTHS {
        for (_, _, backing) in OPS {
            names.push(format!("{carrier}.{backing}"));
        }
        for (to, _) in WIDTHS {
            if to != carrier {
                names.push(format!("{carrier}.to{to}"));
            }
        }
    }
    for cname in names {
        let info = env
            .get_const(&clean_kernel::Name::from_string(&cname))
            .unwrap_or_else(|| panic!("{cname} must be a constant in the prelude"));
        assert_eq!(
            info.kind,
            clean_kernel::ConstantKind::Definition,
            "{cname} must be a Definition, never an Axiom"
        );
    }
}

// ── The VALUES ─────────────────────────────────────────────────────────────

#[test]
fn xor_computes_at_every_uint_width() {
    for (carrier, _) in WIDTHS {
        assert_reduces_to(carrier, &format!("(12 : {carrier}) ^^^ 10"), "6");
        assert_reduces_to(carrier, &format!("(255 : {carrier}) ^^^ 255"), "0");
        assert_reduces_to(carrier, &format!("(170 : {carrier}) ^^^ 85"), "255");
        // near-miss twins: `|||` (14) and `&&&` (8) in place of `^^^`
        assert_does_not_reduce_to(carrier, &format!("(12 : {carrier}) ^^^ 10"), "14");
        assert_does_not_reduce_to(carrier, &format!("(12 : {carrier}) ^^^ 10"), "8");
    }
    // Probe 07d's own assertion.
    assert_reduces_to("UInt64", "(61680 : UInt64) ^^^ 65280", "4080");
}

/// THE LOAD-BEARING VALUE TEST: the shift amount is taken mod the width.
#[test]
fn the_shift_amount_is_reduced_modulo_the_width() {
    for (carrier, bits) in WIDTHS {
        // by exactly the width: the identity, NOT zero
        assert_reduces_to(carrier, &format!("(1 : {carrier}) <<< {bits}"), "1");
        assert_does_not_reduce_to(carrier, &format!("(1 : {carrier}) <<< {bits}"), "0");
        assert_reduces_to(carrier, &format!("(128 : {carrier}) >>> {bits}"), "128");
        assert_does_not_reduce_to(carrier, &format!("(128 : {carrier}) >>> {bits}"), "0");
        // by width + 1: a shift by ONE
        let past = bits + 1;
        assert_reduces_to(carrier, &format!("(1 : {carrier}) <<< {past}"), "2");
        assert_does_not_reduce_to(carrier, &format!("(1 : {carrier}) <<< {past}"), "0");
        assert_reduces_to(carrier, &format!("(128 : {carrier}) >>> {past}"), "64");
        assert_does_not_reduce_to(carrier, &format!("(128 : {carrier}) >>> {past}"), "0");
        // by zero, and an ordinary in-range amount
        assert_reduces_to(carrier, &format!("(37 : {carrier}) <<< 0"), "37");
        assert_reduces_to(carrier, &format!("(37 : {carrier}) >>> 0"), "37");
        assert_reduces_to(carrier, &format!("(1 : {carrier}) <<< 3"), "8");
        assert_reduces_to(carrier, &format!("(240 : {carrier}) >>> 4"), "15");
    }
    // Probe 07e's own assertion, and Lean's doc example for the narrow width.
    assert_reduces_to("UInt64", "(1 : UInt64) <<< 65", "2");
    assert_reduces_to("UInt8", "(1 : UInt8) <<< 254", "64");
}

/// A left shift WRAPS mod `2^w`; a right shift is LOGICAL (zero-filling).
#[test]
fn left_shift_wraps_and_right_shift_is_logical() {
    assert_reduces_to("UInt8", "(255 : UInt8) <<< 1", "254");
    assert_reduces_to("UInt8", "(129 : UInt8) <<< 1", "2");
    assert_reduces_to("UInt8", "(128 : UInt8) <<< 1", "0");
    assert_reduces_to("UInt8", "(128 : UInt8) >>> 7", "1");
    // an arithmetic (sign-propagating) shift would answer 255
    assert_does_not_reduce_to("UInt8", "(128 : UInt8) >>> 7", "255");
    assert_reduces_to(
        "UInt64",
        "(18446744073709551615 : UInt64) <<< 63",
        "9223372036854775808",
    );
    assert_reduces_to("UInt64", "(18446744073709551615 : UInt64) >>> 63", "1");
}

/// Widening is zero-extension, narrowing is truncation.
#[test]
fn conversions_zero_extend_and_truncate() {
    assert_reduces_to("UInt64", "(200 : UInt8).toUInt64", "200");
    assert_reduces_to("UInt64", "(200 : UInt8).toUInt64 + 100", "300"); // 06c
    assert_reduces_to("UInt8", "(4660 : UInt64).toUInt8", "52"); // 06d: 0x1234 -> 0x34
    assert_does_not_reduce_to("UInt8", "(4660 : UInt64).toUInt8", "18"); // the HIGH byte
    assert_does_not_reduce_to("UInt8", "(4660 : UInt64).toUInt8", "255"); // saturation
    assert_reduces_to("UInt16", "(4294967295 : UInt32).toUInt16", "65535");
    assert_reduces_to("UInt32", "(4294967296 : UInt64).toUInt32", "0");
    assert_reduces_to("UInt32", "(65535 : UInt16).toUInt32", "65535");
    // a sign-extending widen would answer 2^32 - 128
    assert_does_not_reduce_to("UInt32", "(128 : UInt8).toUInt32", "4294967168");
    // the everyday composite: pack two bytes into a word
    assert_reduces_to(
        "UInt16",
        "((171 : UInt8).toUInt16 <<< 8) ||| (205 : UInt8).toUInt16",
        "43981", // 0xABCD
    );
}

// ── Proof position: TRUE facts are admitted, their twins are not ────────────

#[test]
fn true_rfl_facts_are_admitted() {
    for source in [
        "theorem t : (1 : UInt64) <<< 65 = 2 := rfl",
        "theorem t : (1 : UInt8) <<< 8 = 1 := rfl",
        "theorem t : (128 : UInt8) >>> 9 = 64 := rfl",
        "theorem t : (12 : UInt32) ^^^ 10 = 6 := rfl",
        "theorem t : (4660 : UInt64).toUInt8 = 52 := rfl",
        "theorem t : (200 : UInt8).toUInt64 = 200 := rfl",
        // xor is an involution on a concrete pair
        "theorem t : ((90 : UInt8) ^^^ 60) ^^^ 60 = 90 := rfl",
    ] {
        expect_accepted(source);
    }
}

#[test]
fn false_rfl_twins_are_refused() {
    for source in [
        "theorem t : (1 : UInt64) <<< 65 = 0 := rfl", // shift-past-width-is-zero
        "theorem t : (1 : UInt8) <<< 8 = 0 := rfl",
        "theorem t : (128 : UInt8) >>> 9 = 0 := rfl",
        "theorem t : (128 : UInt8) >>> 7 = 255 := rfl", // arithmetic shift
        "theorem t : (12 : UInt32) ^^^ 10 = 14 := rfl", // or
        "theorem t : (4660 : UInt64).toUInt8 = 18 := rfl", // high byte
        "theorem t : (128 : UInt8).toUInt32 = 4294967168 := rfl", // sign extension
    ] {
        let _ = expect_refusal(source);
    }
}

/// `Nat`, which already worked, must keep working — and keep ITS answers, which
/// differ from the machine ones precisely where the amount exceeds a width.
#[test]
fn nat_keeps_working_and_keeps_its_own_semantics() {
    for (op, _, _) in OPS {
        let _ = expect_value(&format!("def probe (a b : Nat) : Nat := a {op} b"));
    }
    assert_reduces_to("Nat", "(12 : Nat) ^^^ 10", "6");
    assert_reduces_to("Nat", "(1 : Nat) <<< 65", "36893488147419103232"); // 2^65, no mod
    assert_reduces_to("Nat", "(128 : Nat) >>> 9", "0");
}

const HETEROGENEOUS_SHIFT_FIXTURE: &str = r#"
structure Tiny where
  val : Nat
instance tinyLiteral {n : Nat} : OfNat Tiny n where
  ofNat := Tiny.mk (n % 8)
instance tinyHomLeft : HShiftLeft Tiny Tiny Tiny where
  hShiftLeft _ amount := amount
instance tinyNatLeft : HShiftLeft Tiny Nat Tiny where
  hShiftLeft _ amount := Tiny.mk amount
instance tinyHomRight : HShiftRight Tiny Tiny Tiny where
  hShiftRight _ amount := amount
instance tinyNatRight : HShiftRight Tiny Nat Tiny where
  hShiftRight _ amount := Tiny.mk amount
"#;

const HOMOGENEOUS_SHIFT_PREMISES: &str = r#"
instance tinyShiftLeft : ShiftLeft Tiny where
  shiftLeft _ amount := amount
instance tinyShiftRight : ShiftRight Tiny where
  shiftRight _ amount := amount
"#;

fn shift_fixture_equation(fixture: &str, op: &str, expected: u32) -> String {
    format!(
        "{fixture}\ndef observed : Nat := Tiny.val ((Tiny.mk 1) {op} 8)\n\
             theorem expected : observed = {expected} := rfl\n"
    )
}

#[test]
fn heterogeneous_shift_amount_does_not_wrap_without_a_homogeneous_premise() {
    for op in ["<<<", ">>>"] {
        expect_accepted(&shift_fixture_equation(HETEROGENEOUS_SHIFT_FIXTURE, op, 8));
        expect_refusal(&shift_fixture_equation(HETEROGENEOUS_SHIFT_FIXTURE, op, 0));
    }
}

#[test]
fn a_real_homogeneous_shift_premise_selects_the_carrier_amount() {
    let fixture = format!("{HETEROGENEOUS_SHIFT_FIXTURE}\n{HOMOGENEOUS_SHIFT_PREMISES}");
    for op in ["<<<", ">>>"] {
        expect_accepted(&shift_fixture_equation(&fixture, op, 0));
        expect_refusal(&shift_fixture_equation(&fixture, op, 8));
    }
}

#[test]
fn shift_defaults_compare_user_priority_with_the_native_bridge() {
    for (priority, expected) in [(999, 0), (1000, 8), (1001, 8)] {
        let fixture = HETEROGENEOUS_SHIFT_FIXTURE
            .replace(
                "instance tinyNatLeft",
                &format!("@[default_instance {priority}] instance tinyNatLeft"),
            )
            .replace(
                "instance tinyNatRight",
                &format!("@[default_instance {priority}] instance tinyNatRight"),
            );
        let fixture = format!("{fixture}\n{HOMOGENEOUS_SHIFT_PREMISES}");
        for op in ["<<<", ">>>"] {
            expect_accepted(&shift_fixture_equation(&fixture, op, expected));
            expect_refusal(&shift_fixture_equation(&fixture, op, 8 - expected));
        }
    }
}

const POLYMORPHIC_SHIFT_FIXTURE: &str = r#"
universe u
structure Parcel (α : Type u) where
  payload : α
  val : Nat
instance parcelNatShift {α : Type u} : HShiftLeft (Parcel α) Nat (Parcel α) where
  hShiftLeft x amount := Parcel.mk x.payload amount
def preservingLevel.{v} {α : Type v} (x : Parcel α) : Parcel α := x <<< 8
"#;

#[test]
fn a_failed_shift_default_preserves_the_callers_universe_constraints() {
    expect_accepted(&format!(
        "{POLYMORPHIC_SHIFT_FIXTURE}\n\
        theorem expected.{{v}} {{α : Type v}} (x : Parcel α) :\n\
          Parcel.val (preservingLevel x) = 8 := rfl\n"
    ));
    expect_refusal(&format!(
        "{POLYMORPHIC_SHIFT_FIXTURE}\n\
        theorem wrong.{{v}} {{α : Type v}} (x : Parcel α) :\n\
          Parcel.val (preservingLevel x) = 0 := rfl\n"
    ));
}
