// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! B27 — arbitrary-precision (`>= 2^64`) numeric literals PARSE in every base.
//!
//! Before B27 the lexer accumulated numeric literals into a `u64`; any value at
//! or above `18446744073709551616` (`2^64`) overflowed and was rejected as a
//! `NumericOverflow` lex error in every base. Lean 4 `Nat` literals are
//! unbounded, so the accumulator is now the kernel's arbitrary-precision
//! `BigNat`. These tests pin the EXACT value of boundary and large literals in
//! decimal, hex, binary, and octal — a parse error or a truncated value fails.

use clean_kernel::BigNat;
use clean_parser::{parse_expr, SurfaceExpr, SurfaceLit};

/// Extract the `SurfaceLit` from a parsed leaf-literal expression.
fn parse_lit(src: &str) -> SurfaceLit {
    match parse_expr(src) {
        Ok(SurfaceExpr::Lit(_, lit)) => lit,
        Ok(other) => panic!("expected a literal for {src:?}, parsed {other:?}"),
        Err(e) => panic!("expected {src:?} to parse, got error: {e:?}"),
    }
}

/// The exact `BigNat` a literal must denote (folded independently of the lexer).
fn big(digits: &str, radix: u32) -> BigNat {
    BigNat::from_radix_str(digits, radix).expect("test literal folds to a BigNat")
}

/// `2^64` as a kernel `BigNat` — the exact boundary value, `[0, 1]`
/// little-endian (`0 + 1·2^64`).
fn two_pow_64() -> BigNat {
    BigNat::from_limbs(vec![0, 1])
}

#[test]
fn test_decimal_2_pow_64_parses_to_exact_value() {
    assert_eq!(
        parse_lit("18446744073709551616"),
        SurfaceLit::BigNat(two_pow_64())
    );
}

#[test]
fn test_decimal_2_pow_64_plus_one_parses_to_exact_value() {
    // 2^64 + 1 == [1, 1] little-endian.
    assert_eq!(
        parse_lit("18446744073709551617"),
        SurfaceLit::BigNat(BigNat::from_limbs(vec![1, 1]))
    );
}

#[test]
fn test_u64_max_stays_on_small_representation() {
    // The largest value below the boundary keeps the compact `Nat(u64)` arm.
    assert_eq!(parse_lit("18446744073709551615"), SurfaceLit::Nat(u64::MAX));
}

#[test]
fn test_hex_u64_max_plus_one_parses_to_exact_value() {
    // 0xFFFF_FFFF_FFFF_FFFF == u64::MAX (small); +1 crosses to 2^64.
    assert_eq!(parse_lit("0xFFFFFFFFFFFFFFFF"), SurfaceLit::Nat(u64::MAX));
    assert_eq!(
        parse_lit("0x10000000000000000"),
        SurfaceLit::BigNat(two_pow_64())
    );
    // Underscore digit-group separators inside a big hex literal are ignored.
    assert_eq!(
        parse_lit("0x1_0000_0000_0000_0000"),
        SurfaceLit::BigNat(two_pow_64())
    );
}

#[test]
fn test_binary_2_pow_64_parses_to_exact_value() {
    // `1` followed by 64 zero bits == 2^64.
    let src = format!("0b1{}", "0".repeat(64));
    assert_eq!(parse_lit(&src), SurfaceLit::BigNat(two_pow_64()));
}

#[test]
fn test_octal_2_pow_64_parses_to_exact_value() {
    // 2·8^21 == 2·2^63 == 2^64.
    assert_eq!(
        parse_lit("0o2000000000000000000000"),
        SurfaceLit::BigNat(two_pow_64())
    );
}

#[test]
fn test_hundred_digit_decimal_parses_to_exact_value() {
    // 10^99 — a 100-digit literal, far beyond u64 but well within the fold cap.
    let src = "1".to_string() + &"0".repeat(99);
    assert_eq!(parse_lit(&src), SurfaceLit::BigNat(big(&src, 10)));
}

#[test]
fn test_cross_base_boundary_values_agree() {
    // The same value (2^64) written in four bases yields one canonical BigNat.
    let expected = SurfaceLit::BigNat(two_pow_64());
    assert_eq!(parse_lit("18446744073709551616"), expected);
    assert_eq!(parse_lit("0x10000000000000000"), expected);
    assert_eq!(parse_lit("0o2000000000000000000000"), expected);
    assert_eq!(parse_lit(&format!("0b1{}", "0".repeat(64))), expected);
}

#[test]
fn test_big_literal_in_addition_expression_parses() {
    // `0xFFFFFFFFFFFFFFFF + 1` — the boundary literal as the LHS of `+`. Both
    // operands must survive: the literal-starter checks match a `NatLit`
    // regardless of its (now `BigNat`) payload, so nothing is silently dropped.
    let expr = parse_expr("0xFFFFFFFFFFFFFFFF + 1")
        .expect("boundary literal on the LHS of `+` must parse");
    let rendered = format!("{expr:?}");
    // 0xFFFF_FFFF_FFFF_FFFF == u64::MAX; it must appear intact in the tree.
    assert!(
        rendered.contains(&u64::MAX.to_string()),
        "big literal operand lost from the parse tree: {rendered}"
    );

    // The true crossing case `2^64 + 1` (a genuine `BigNat` operand) also parses.
    let big_sum = parse_expr("18446744073709551616 + 1").expect("`2^64 + 1` must parse");
    assert!(
        format!("{big_sum:?}").contains("BigNat"),
        "expected a BigNat operand in `2^64 + 1`"
    );
}
