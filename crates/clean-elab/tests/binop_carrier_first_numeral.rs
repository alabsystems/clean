// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression pin — a bare NUMERAL takes its type from the sibling operand,
//! whichever side of the operator it sits on.
//!
//! ## The gap
//!
//! `def f (a b : UInt64) : UInt64 := if a < 10 then a else b` elaborated;
//! `def g (a b : UInt64) : UInt64 := if 10 < a then a else b` did not:
//!
//! ```text
//! Type mismatch: expected Const(Nat), got const mismatch: UInt64 vs Nat
//! ```
//!
//! The elaborator's argument loop is strictly left-to-right, so the numeral in
//! operand 0 was committed — by the `@[default_instance]` `Nat` pin at the
//! literal seam (`infer/coercion.rs`, step 0) — before the operand that names
//! the carrier had been looked at. `?α := Nat`, and `a : UInt64` then mismatched
//! rigidly. Real Lean has no such asymmetry: `binop%` (`Elab/Extra.lean`)
//! elaborates the operands that CARRY a type first and only then the
//! type-directed leaves, and a numeral at a metavariable type is postponed
//! rather than defaulted.
//!
//! The fix (`infer/elab_app.rs::pin_open_slots_from_carrier_operand`) is that
//! ordering in lookahead form, and it is head-agnostic: two argument positions
//! share a carrier when their binder domains are the same open metavariable
//! (`LT.lt`/`LE.le`/`Eq`/`BEq.beq : {α} → α → α → …`, and any user function of
//! that shape) or when the head is a homogeneous `binop%` desugaring, whose
//! `?α ?β ?γ` Lean's `@[default_instance] instHOp : HOp α α α` forces equal.
//!
//! ## What must stay refused
//!
//! The pass fires only when some argument is a bare numeral — an argument with
//! NO type of its own. A comparison of two typed operands at different types is
//! genuinely heterogeneous and still fails closed, and so does an ASCRIBED
//! literal, which is a carrier and not a leaf. Both are pinned below with their
//! messages.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, TypeChecker};
use clean_parser::parse_file;

/// Drive the real file pipeline, and KERNEL-CHECK every definition it produces
/// (`TypeChecker::check_type` against the declared type) before registering it.
/// A pass here is therefore not an elaborator self-report.
fn elaborate_file(source: &str) -> Result<Vec<(String, Expr)>, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut values = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result =
            elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
        if let ElabResult::Definition { name, ty, val, .. } = &result {
            let tc = TypeChecker::new(&env);
            tc.check_type(val, ty)
                .map_err(|e| format!("kernel rejected {name}: {e}"))?;
            values.push((name.to_string(), val.clone()));
        }
    }
    Ok(values)
}

/// Elaborate + kernel-check, returning the last definition's value.
fn expect_value(source: &str) -> Expr {
    let values = elaborate_file(source)
        .unwrap_or_else(|e| panic!("must elaborate and kernel-check, got: {e}\n{source}"));
    values
        .last()
        .unwrap_or_else(|| panic!("no definition produced\n{source}"))
        .1
        .clone()
}

fn expect_refusal(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("must be REFUSED, but elaborated:\n{source}"),
        Err(e) => e,
    }
}

/// `{width}` is a numeric carrier name; build the left- and right-numeral
/// comparison at it.
fn lt_pair(carrier: &str) -> (String, String) {
    (
        format!("def probe_left (a b : {carrier}) : {carrier} := if 10 < a then a else b"),
        format!("def probe_right (a b : {carrier}) : {carrier} := if a < 10 then a else b"),
    )
}

// ── The gap: a numeral on the LEFT, at every numeric carrier ────────────────

#[test]
fn left_numeral_lt_elaborates_at_every_numeric_carrier() {
    for carrier in ["UInt64", "UInt32", "UInt16", "UInt8", "Nat", "Int"] {
        let (left, _) = lt_pair(carrier);
        let _ = expect_value(&left);
    }
}

/// Controls: the direction that already worked must keep working, at the same
/// carriers. (`UInt64`/`Int` were the two measured passers.)
#[test]
fn right_numeral_lt_still_elaborates_at_every_numeric_carrier() {
    for carrier in ["UInt64", "UInt32", "UInt16", "UInt8", "Nat", "Int"] {
        let (_, right) = lt_pair(carrier);
        let _ = expect_value(&right);
    }
}

/// Not just `<`: the pass keys on the SHAPE (a carrier-free leaf sharing an
/// open type slot with a typed sibling), never on the operator.
#[test]
fn left_numeral_works_for_every_shared_carrier_operator() {
    for body in [
        "if 10 < a then a else b",
        "if 10 <= a then a else b",
        "if 10 > a then a else b",
        "if 10 >= a then a else b",
        "if 10 == a then a else b",
        "if 10 != a then a else b",
    ] {
        let _ = expect_value(&format!("def probe (a b : UInt64) : UInt64 := {body}"));
    }
}

/// The homogeneous `binop%` family, whose `?α ?β ?γ` are DISTINCT metavariables
/// linked by `@[default_instance] instHOp : HOp α α α`. `10 + a` previously
/// escaped elaboration with a leaked instance metavariable
/// ("unsolved metavariables ?[7]") rather than a type error.
///
/// `% / &&& |||` used to be absent from the `UInt64` row: the prelude
/// registered no `HMod`/`HDiv`/`HAnd`/`HOr` instance at ANY `UInt*` carrier, so
/// `a % b` between two VARIABLES already failed there — a prelude content gap,
/// unrelated to operand order. That gap is closed (`uint_div_mod_bitwise.rs`),
/// so the two rows are now the same set, and this test is the pin that the
/// carrier-first pass covers the new operators too.
#[test]
fn left_numeral_works_for_homogeneous_arithmetic() {
    for carrier in ["UInt64", "Nat"] {
        for body in ["10 + a", "10 - a", "10 * a", "10 % a", "10 / a", "10 &&& a"] {
            let _ = expect_value(&format!("def probe (a : {carrier}) : {carrier} := {body}"));
        }
    }
}

/// Controls for the same family in the direction that already worked.
#[test]
fn right_numeral_arithmetic_still_elaborates() {
    for body in ["a + 10", "a - 10", "a * 10"] {
        let _ = expect_value(&format!("def probe (a : UInt64) : UInt64 := {body}"));
    }
}

/// Both operands carrier-free: nothing names a carrier, so the
/// `@[default_instance]` `Nat` outcome stands — exactly Lean's behaviour for
/// `10 < 20`. The pass must not invent a carrier here.
#[test]
fn both_operands_numerals_default_to_nat() {
    let val = expect_value("def probe (a b : UInt64) : UInt64 := if 10 < 20 then a else b");
    let printed = format!("{val:?}");
    assert!(
        printed.contains("\"instLTNat\""),
        "a comparison of two numerals must stay at Nat, got:\n{printed}"
    );
}

/// A numeral in the outer operand of a NESTED shape: the carrier comes from an
/// application (`a + b`), not a bare variable.
#[test]
fn left_numeral_over_a_nested_operand() {
    let _ = expect_value("def probe (a b : UInt64) : UInt64 := if 10 < a + b then a else b");
}

/// Power and shift keep an INDEPENDENT exponent / shift-amount type
/// (`homogeneous == false`), and the pass must leave them alone: `2 ^ a` with
/// `a : Nat` is `HPow Nat Nat Nat`, not a shared carrier.
#[test]
fn power_keeps_its_independent_exponent_type() {
    let _ = expect_value("def probe (a : Nat) : Nat := 2 ^ a");
}

// ── The term the LEFT position mints ───────────────────────────────────────

/// The spelling downstream readers key on. For a numeral at a `UInt{N}` carrier
/// the elaborator mints the CARRIER form `{C}.ofNat v` — `UInt64.ofNat 10` —
/// and this must be true in the LEFT operand position exactly as it already was
/// on the right, so a consumer that pattern-matches the literal does not have
/// to learn a second shape.
#[test]
fn left_and_right_numerals_mint_the_same_carrier_form() {
    let left = expect_value("def probe (a b : UInt64) : UInt64 := if 10 < a then a else b");
    let right = expect_value("def probe (a b : UInt64) : UInt64 := if a < 10 then a else b");
    for (side, val) in [("left", &left), ("right", &right)] {
        let printed = format!("{val:?}");
        assert!(
            printed.contains("\"UInt64\", \"ofNat\""),
            "{side} numeral must mint `UInt64.ofNat 10`, got:\n{printed}"
        );
        assert!(
            printed.contains("\"instLTUInt64\""),
            "{side} comparison must resolve `LT UInt64`, got:\n{printed}"
        );
        assert!(
            !printed.contains("\"instLTNat\""),
            "{side} comparison must not fall back to a Nat comparison:\n{printed}"
        );
    }
}

/// The `Int` carrier keeps its own constructor spelling (`Int.ofNat`), reached
/// on the left through the new pass instead of through the `Int.ofNat` recovery
/// retry that used to repair it after the fact.
#[test]
fn left_numeral_at_int_mints_int_of_nat() {
    let val = expect_value("def probe (a b : Int) : Int := if 10 < a then a else b");
    let printed = format!("{val:?}");
    assert!(
        printed.contains("\"Int\", \"ofNat\""),
        "left numeral at Int must mint `Int.ofNat 10`, got:\n{printed}"
    );
}

// ── What must still be REFUSED ─────────────────────────────────────────────

/// A genuinely heterogeneous comparison: two operands that each carry a type,
/// and the types differ. No numeral is involved, so the pass never sees it and
/// the elaborator still fails closed. THIS IS THE LOAD-BEARING TEST — a "fix"
/// that inserts coercions until everything elaborates would turn this green.
#[test]
fn heterogeneous_comparison_of_typed_operands_is_refused() {
    let err = expect_refusal("def probe (a : Nat) (b : UInt64) : UInt64 := if a < b then b else b");
    assert!(
        err.contains("Type mismatch"),
        "expected a type mismatch, got: {err}"
    );
    assert!(
        err.contains("UInt64") && err.contains("Nat"),
        "the refusal must name both carriers, got: {err}"
    );
}

/// An ASCRIBED literal is a carrier, not a leaf: `(10 : Nat) < a` with
/// `a : UInt64` states two different types and must keep failing. This is the
/// precise boundary of the fix — the same digits, refused, because the program
/// named a type.
#[test]
fn ascribed_literal_at_the_wrong_carrier_is_refused() {
    let err =
        expect_refusal("def probe (a b : UInt64) : UInt64 := if (10 : Nat) < a then a else b");
    assert!(
        err.contains("Type mismatch"),
        "expected a type mismatch, got: {err}"
    );
}

/// The same boundary on the arithmetic side.
#[test]
fn ascribed_literal_in_arithmetic_at_the_wrong_carrier_is_refused() {
    let err = expect_refusal("def probe (a : UInt64) : UInt64 := (10 : Nat) + a");
    assert!(
        !err.is_empty(),
        "an ascribed Nat added to a UInt64 must be refused"
    );
}

/// A heterogeneous EQUALITY of typed operands, for the `Eq` head specifically —
/// `Eq {α} : α → α → Prop` is the shared-metavar shape the pass recognises, so
/// pin that recognising it did not make it permissive.
#[test]
fn heterogeneous_equality_of_typed_operands_is_refused() {
    let err = expect_refusal("theorem probe (a : Nat) (b : UInt64) : a = b := rfl");
    assert!(!err.is_empty(), "`a = b` across carriers must be refused");
}
