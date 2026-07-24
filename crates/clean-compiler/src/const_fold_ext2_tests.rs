// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for ext2 constant folding pure helpers.

use crate::const_fold_ext2::*;
use crate::ir::*;
use clean_kernel::Name;

fn name(s: &str) -> Name {
    s.parse().unwrap()
}
fn fn_id(s: &str) -> FnId {
    FnId(name(s))
}
fn var(id: u32) -> VarId {
    VarId(id)
}
fn var_arg(id: u32) -> IRArg {
    IRArg::Var(var(id))
}
fn lit_u64(v: u64) -> IRExpr {
    IRExpr::Lit(IRLiteral::UInt64(v))
}
fn lit_bool(v: bool) -> IRExpr {
    IRExpr::Lit(IRLiteral::Bool(v))
}
fn str_expr(s: &str) -> IRExpr {
    IRExpr::String(s.to_owned())
}
fn apply(op: &str, args: Vec<IRArg>) -> IRExpr {
    IRExpr::Apply {
        fn_id: fn_id(op),
        args,
    }
}
fn simple_ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name("Test.ctor"),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}
fn ctor_with_fields(tag: u32, n: usize) -> CtorInfo {
    CtorInfo {
        name: name("Test.ctor"),
        tag,
        num_scalars: 0,
        num_objects: n as u32,
        field_types: vec![IRType::Object; n],
    }
}
fn chain_lets(bindings: Vec<(u32, IRExpr)>, ret_var: u32) -> IRBody {
    let mut body = IRBody::Ret(var_arg(ret_var));
    for (vid, expr) in bindings.into_iter().rev() {
        body = IRBody::VDecl {
            var: var(vid),
            ty: IRType::UInt64,
            value: expr,
            rest: Box::new(body),
        };
    }
    body
}
fn make_decl(body: IRBody) -> IRDecl {
    IRDecl {
        name: name("test_fn"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }
}

// -- Arithmetic folding (Nat/Int) --------------------------------------------

#[test]
fn test_fold_arith_nat_add() {
    assert!(matches!(fold_arith("Nat.add", 3, 4), Some(7)));
}

#[test]
fn test_fold_arith_nat_sub_saturates() {
    assert!(matches!(fold_arith("Nat.sub", 2, 5), Some(0)));
}

#[test]
fn test_fold_arith_nat_mul() {
    assert!(matches!(fold_arith("Nat.mul", 6, 7), Some(42)));
}

#[test]
fn test_fold_arith_nat_div() {
    assert!(matches!(fold_arith("Nat.div", 10, 3), Some(3)));
}

#[test]
fn test_fold_arith_nat_div_by_zero_yields_zero() {
    // Lean `Nat` division is total: `n / 0 = 0`. This matches the elaborator
    // simproc `Nat.reduceDiv` and the runtime `eval_int_binop`.
    assert_eq!(fold_arith("Nat.div", 10, 0), Some(0));
}

#[test]
fn test_fold_arith_nat_mod() {
    assert!(matches!(fold_arith("Nat.mod", 10, 3), Some(1)));
}

#[test]
fn test_fold_arith_nat_mod_by_zero_yields_dividend() {
    // Lean `Nat` modulus is total: `n % 0 = n`. Matches `Nat.reduceMod` and the
    // runtime `eval_int_binop`.
    assert_eq!(fold_arith("Nat.mod", 10, 0), Some(10));
}

#[test]
fn test_fold_arith_nat_pow() {
    assert_eq!(fold_arith("Nat.pow", 2, 10), Some(1024));
    // `0^0 = 1` per Lean / `u64::pow`.
    assert_eq!(fold_arith("Nat.pow", 0, 0), Some(1));
}

#[test]
fn test_fold_arith_nat_pow_overflow_not_folded() {
    // Result overflows u64 -> decline (matches `Nat.reducePow`).
    assert!(fold_arith("Nat.pow", 2, 64).is_none());
}

#[test]
fn test_fold_arith_nat_pow_huge_exponent_not_folded() {
    // Exponent does not fit in u32 -> decline rather than risk a huge result.
    assert!(fold_arith("Nat.pow", 2, u64::from(u32::MAX) + 1).is_none());
}

#[test]
fn test_fold_arith_nat_gcd() {
    assert_eq!(fold_arith("Nat.gcd", 12, 18), Some(6));
    assert_eq!(fold_arith("Nat.gcd", 17, 5), Some(1));
}

#[test]
fn test_fold_arith_nat_gcd_zero_edges() {
    // gcd(a, 0) = a, gcd(0, b) = b, gcd(0, 0) = 0 (Euclidean, total).
    assert_eq!(fold_arith("Nat.gcd", 9, 0), Some(9));
    assert_eq!(fold_arith("Nat.gcd", 0, 9), Some(9));
    assert_eq!(fold_arith("Nat.gcd", 0, 0), Some(0));
}

#[test]
fn test_fold_arith_nat_max_min() {
    assert_eq!(fold_arith("Nat.max", 3, 7), Some(7));
    assert_eq!(fold_arith("Nat.max", 7, 3), Some(7));
    assert_eq!(fold_arith("Nat.min", 3, 7), Some(3));
    assert_eq!(fold_arith("Nat.min", 7, 3), Some(3));
}

#[test]
fn test_fold_arith_nat_add_overflow() {
    assert!(fold_arith("Nat.add", u64::MAX, 1).is_none());
}

// -- Bitwise/logical folding (Nat) -------------------------------------------
//    Authoritative reference: `reduce_nat_land` / `reduce_nat_lor` /
//    `reduce_nat_lxor` in clean-kernel `native_reducers_arith.rs`, which compute
//    plain `a & b` / `a | b` / `a ^ b` on the non-negative bignum operands.

#[test]
fn test_fold_arith_nat_land_small_literals() {
    // 0b1100 & 0b1010 = 0b1000 = 8.
    assert_eq!(fold_arith("Nat.land", 0b1100, 0b1010), Some(0b1000));
    assert_eq!(fold_arith("Nat.land", 12, 10), Some(8));
    assert_eq!(fold_arith("Nat.land", 0xFF, 0x0F), Some(0x0F));
    // AND with 0 is 0; AND with all-ones leaves the operand unchanged.
    assert_eq!(fold_arith("Nat.land", 42, 0), Some(0));
    assert_eq!(fold_arith("Nat.land", 42, u64::MAX), Some(42));
}

#[test]
fn test_fold_arith_nat_lor_small_literals() {
    // 0b1100 | 0b1010 = 0b1110 = 14.
    assert_eq!(fold_arith("Nat.lor", 0b1100, 0b1010), Some(0b1110));
    assert_eq!(fold_arith("Nat.lor", 12, 10), Some(14));
    // OR with 0 leaves the operand unchanged.
    assert_eq!(fold_arith("Nat.lor", 42, 0), Some(42));
    assert_eq!(fold_arith("Nat.lor", 0xF0, 0x0F), Some(0xFF));
}

#[test]
fn test_fold_arith_nat_xor_small_literals() {
    // The kernel registers Nat XOR under the Lean name `Nat.xor`.
    // 0b1100 ^ 0b1010 = 0b0110 = 6.
    assert_eq!(fold_arith("Nat.xor", 0b1100, 0b1010), Some(0b0110));
    assert_eq!(fold_arith("Nat.xor", 12, 10), Some(6));
    // XOR with self is 0; XOR with 0 is identity.
    assert_eq!(fold_arith("Nat.xor", 42, 42), Some(0));
    assert_eq!(fold_arith("Nat.xor", 42, 0), Some(42));
}

#[test]
fn test_fold_arith_nat_bitwise_full_width_exact() {
    // Bitwise never grows past the wider operand, so a u64-wide computation is
    // exact even at the top of the range — no overflow, no decline.
    assert_eq!(fold_arith("Nat.land", u64::MAX, u64::MAX), Some(u64::MAX));
    assert_eq!(fold_arith("Nat.lor", u64::MAX, 0), Some(u64::MAX));
    assert_eq!(fold_arith("Nat.xor", u64::MAX, u64::MAX), Some(0));
}

// -- Int bitwise is DECLINED (decline-rather-than-guess) ---------------------
//    There is no kernel reducer for signed bitwise, and Int's infinite two's-
//    complement on negatives cannot be matched in a fixed 64-bit word, so we
//    must leave every `Int.land`/`Int.lor`/`Int.xor`/`Int.lnot` call untouched
//    rather than emit a width-truncated value the kernel never produces.

#[test]
fn test_fold_arith_int_bitwise_declines() {
    // Even for non-negative operands (where the answer would coincide with the
    // Nat fold), we DECLINE: there is no authoritative kernel result to match.
    assert_eq!(fold_arith("Int.land", 12, 10), None);
    assert_eq!(fold_arith("Int.lor", 12, 10), None);
    assert_eq!(fold_arith("Int.xor", 12, 10), None);
    // Negative operand: an all-ones infinite prefix cannot be represented.
    assert_eq!(fold_arith("Int.land", (-1i64) as u64, 0xFF), None);
    assert_eq!(fold_arith("Int.lor", (-1i64) as u64, 0), None);
    assert_eq!(fold_arith("Int.xor", (-1i64) as u64, 5), None);
    // `Int.lnot` (unary complement) likewise stays unfolded by `fold_arith`.
    assert_eq!(fold_arith("Int.lnot", 5, 0), None);
}

#[test]
fn test_fold_arith_int_add() {
    assert_eq!(fold_arith("Int.add", (-3i64) as u64, 5).unwrap(), 2);
}

#[test]
fn test_fold_arith_int_sub() {
    assert_eq!(fold_arith("Int.sub", 3, 5).unwrap(), (-2i64) as u64);
}

#[test]
fn test_fold_arith_int_mul() {
    assert_eq!(
        fold_arith("Int.mul", (-2i64) as u64, 3).unwrap(),
        (-6i64) as u64
    );
}

#[test]
fn test_fold_arith_int_div_by_zero() {
    assert!(fold_arith("Int.div", 10, 0).is_none());
}

#[test]
fn test_fold_arith_unknown_op() {
    assert!(fold_arith("Foo.bar", 1, 2).is_none());
}

// -- Overflow-consistency: const-fold must match the kernel's *unbounded*
//    Nat/Int semantics exactly, or DECLINE. A wrong fold is a miscompilation.
//    Authoritative reference: `TypeChecker::reduce_nat` in clean-kernel.

#[test]
fn test_fold_arith_nat_sub_truncates_at_zero() {
    // Nat is a non-negative bignum: 5 - 8 = 0 (truncated subtraction), NOT a
    // machine-saturating clamp and NOT a two's-complement wrap to a huge value.
    assert_eq!(fold_arith("Nat.sub", 5, 8), Some(0));
    assert_eq!(fold_arith("Nat.sub", 0, 1), Some(0));
    assert_eq!(fold_arith("Nat.sub", 8, 5), Some(3));
}

#[test]
fn test_fold_arith_nat_add_exact_in_range() {
    // In-range additions are exact (no wrap).
    assert_eq!(fold_arith("Nat.add", u64::MAX - 1, 1), Some(u64::MAX));
}

#[test]
fn test_fold_arith_nat_add_overflow_declines_not_wraps() {
    // u64::MAX + 1 is 2^64 — a BigNat the kernel produces but the IR cannot
    // carry. We must DECLINE, never wrap to 0.
    assert_eq!(fold_arith("Nat.add", u64::MAX, 1), None);
    assert_eq!(fold_arith("Nat.add", u64::MAX, u64::MAX), None);
}

#[test]
fn test_fold_arith_nat_mul_overflow_declines_not_wraps() {
    // 2^63 * 2 = 2^64 overflows u64; decline rather than wrap to 0.
    assert_eq!(fold_arith("Nat.mul", 1u64 << 63, 2), None);
    assert_eq!(fold_arith("Nat.mul", u64::MAX, 2), None);
    // In-range multiplication stays exact.
    assert_eq!(fold_arith("Nat.mul", 6, 7), Some(42));
}

#[test]
fn test_fold_arith_int_add_overflow_declines_not_wraps() {
    // Int is an unbounded signed bignum. i64::MAX + 1 = 2^63 is not
    // i64-representable; the old `wrapping_add` produced i64::MIN (a wrong,
    // negative value). We must DECLINE.
    assert_eq!(fold_arith("Int.add", i64::MAX as u64, 1), None);
    assert_eq!(fold_arith("Int.add", i64::MIN as u64, (-1i64) as u64), None);
    // In-range signed arithmetic remains exact (bit pattern == i64 two's comp).
    assert_eq!(fold_arith("Int.add", (-3i64) as u64, 5), Some(2));
}

#[test]
fn test_fold_arith_int_sub_overflow_declines_not_wraps() {
    // i64::MIN - 1 = -(2^63 + 1) is not representable; decline rather than wrap.
    assert_eq!(fold_arith("Int.sub", i64::MIN as u64, 1), None);
    assert_eq!(fold_arith("Int.sub", 3, 5), Some((-2i64) as u64));
}

#[test]
fn test_fold_arith_int_mul_overflow_declines_not_wraps() {
    // i64::MIN * -1 = 2^63 is not i64-representable; old `wrapping_mul` gave
    // i64::MIN. Decline. Also 2^62 * 4 = 2^64 overflows.
    assert_eq!(fold_arith("Int.mul", i64::MIN as u64, (-1i64) as u64), None);
    assert_eq!(fold_arith("Int.mul", 1u64 << 62, 4), None);
    assert_eq!(
        fold_arith("Int.mul", (-2i64) as u64, 3),
        Some((-6i64) as u64)
    );
}

#[test]
fn test_fold_arith_int_div_min_by_neg_one_declines() {
    // i64::MIN / -1 = 2^63, the single signed-division overflow. The old
    // `wrapping_div` wrapped to i64::MIN; we must DECLINE.
    assert_eq!(fold_arith("Int.div", i64::MIN as u64, (-1i64) as u64), None);
    // Ordinary signed division still folds exactly (truncated toward zero).
    assert_eq!(
        fold_arith("Int.div", (-7i64) as u64, 2),
        Some((-3i64) as u64)
    );
    assert_eq!(fold_arith("Int.div", 10, 0), None);
}

#[test]
fn test_fold_arith_int_mod_min_by_neg_one_declines() {
    // checked_rem(i64::MIN, -1) is None (overflow of the paired quotient); we
    // decline conservatively rather than risk divergence with `Int.div`.
    assert_eq!(fold_arith("Int.mod", i64::MIN as u64, (-1i64) as u64), None);
    assert_eq!(
        fold_arith("Int.mod", (-7i64) as u64, 2),
        Some((-1i64) as u64)
    );
    assert_eq!(fold_arith("Int.mod", 10, 0), None);
}

#[test]
fn test_fold_int_abs_min_declines_not_wraps() {
    // |i64::MIN| = 2^63 is not i64-representable; old `wrapping_abs` produced
    // i64::MIN (a *negative* "absolute value"). Decline.
    assert_eq!(fold_int_abs("Int.abs", i64::MIN as u64), None);
    assert_eq!(fold_int_abs("Int.natAbs", i64::MIN as u64), None);
    // Ordinary absolute values fold.
    assert_eq!(fold_int_abs("Int.abs", (-5i64) as u64), Some(5));
    assert_eq!(fold_int_abs("Int.natAbs", 7), Some(7));
}

#[test]
fn test_fold_arith_int_shift_left_overflow_declines_not_wraps() {
    // Left shift is multiplication by 2^n; if any significant bit is shifted
    // out the exact result overflows i64 and we must DECLINE, not wrap.
    assert_eq!(fold_arith("Int.shiftLeft", 1, 63), None); // 2^63 not in i64
    assert_eq!(fold_arith("Int.shiftLeft", 1u64 << 62, 2), None); // overflow
                                                                  // A shift >= 64 only leaves the value of `0` unchanged; everything else
                                                                  // would lose bits, so decline.
    assert_eq!(fold_arith("Int.shiftLeft", 0, 64), Some(0));
    assert_eq!(fold_arith("Int.shiftLeft", 1, 64), None);
    // Exact small shifts still fold.
    assert_eq!(fold_arith("Int.shiftLeft", 3, 4), Some(48));
}

// -- Boolean folding ---------------------------------------------------------

fn env_bools(vals: &[(u32, bool)]) -> PropagationEnv {
    let mut e = PropagationEnv::new();
    for &(id, b) in vals {
        e.insert(var(id), KnownVal2::Bool(b));
    }
    e
}

#[test]
fn test_fold_bool_and_tt() {
    assert!(matches!(
        fold_bool(
            "Bool.and",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, true), (1, true)])
        ),
        Some(true)
    ));
}

#[test]
fn test_fold_bool_and_tf() {
    assert!(matches!(
        fold_bool(
            "Bool.and",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, true), (1, false)])
        ),
        Some(false)
    ));
}

#[test]
fn test_fold_bool_or_ft() {
    assert!(matches!(
        fold_bool(
            "Bool.or",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, false), (1, true)])
        ),
        Some(true)
    ));
}

#[test]
fn test_fold_bool_or_ff() {
    assert!(matches!(
        fold_bool(
            "Bool.or",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, false), (1, false)])
        ),
        Some(false)
    ));
}

#[test]
fn test_fold_bool_not_true() {
    assert!(matches!(
        fold_bool("Bool.not", &[var_arg(0)], &env_bools(&[(0, true)])),
        Some(false)
    ));
}

#[test]
fn test_fold_bool_not_false() {
    assert!(matches!(
        fold_bool("Bool.not", &[var_arg(0)], &env_bools(&[(0, false)])),
        Some(true)
    ));
}

#[test]
fn test_fold_bool_unknown_op() {
    // `Foo.bar` is not a recognized boolean connective.
    assert!(fold_bool("Foo.bar", &[var_arg(0), var_arg(1)], &PropagationEnv::new()).is_none());
}

#[test]
fn test_fold_bool_xor_wrong_arity_not_folded() {
    // `Bool.xor` is binary; a single argument is left untouched (conservative).
    assert!(fold_bool("Bool.xor", &[var_arg(0)], &env_bools(&[(0, true)])).is_none());
}

#[test]
fn test_fold_bool_xor() {
    assert!(matches!(
        fold_bool(
            "Bool.xor",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, true), (1, false)])
        ),
        Some(true)
    ));
    assert!(matches!(
        fold_bool(
            "Bool.xor",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, true), (1, true)])
        ),
        Some(false)
    ));
}

#[test]
fn test_fold_bool_beq() {
    assert!(matches!(
        fold_bool(
            "Bool.beq",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, false), (1, false)])
        ),
        Some(true)
    ));
    assert!(matches!(
        fold_bool(
            "Bool.beq",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, true), (1, false)])
        ),
        Some(false)
    ));
}

#[test]
fn test_fold_bool_bne() {
    assert!(matches!(
        fold_bool(
            "Bool.bne",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, true), (1, false)])
        ),
        Some(true)
    ));
    assert!(matches!(
        fold_bool(
            "Bool.bne",
            &[var_arg(0), var_arg(1)],
            &env_bools(&[(0, true), (1, true)])
        ),
        Some(false)
    ));
}

#[test]
fn test_fold_bool_partial_args_not_folded() {
    // Only one operand is known -> cannot fold the connective.
    assert!(fold_bool(
        "Bool.xor",
        &[var_arg(0), var_arg(1)],
        &env_bools(&[(0, true)])
    )
    .is_none());
}

// -- String folding ----------------------------------------------------------

fn env_strs(vals: &[(u32, &str)]) -> PropagationEnv {
    let mut e = PropagationEnv::new();
    for &(id, s) in vals {
        e.insert(var(id), KnownVal2::Str(s.into()));
    }
    e
}

#[test]
fn test_fold_string_append() {
    let r = fold_string(
        "String.append",
        &[var_arg(0), var_arg(1)],
        &env_strs(&[(0, "hello"), (1, " world")]),
        4096,
    );
    assert!(matches!(r, Some(IRExpr::String(s)) if s == "hello world"));
}

#[test]
fn test_fold_string_length() {
    let r = fold_string(
        "String.length",
        &[var_arg(0)],
        &env_strs(&[(0, "hello")]),
        4096,
    );
    assert!(matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(5)))));
}

#[test]
fn test_fold_string_is_empty_false() {
    let r = fold_string(
        "String.isEmpty",
        &[var_arg(0)],
        &env_strs(&[(0, "abc")]),
        4096,
    );
    assert!(matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))));
}

#[test]
fn test_fold_string_is_empty_true() {
    let r = fold_string("String.isEmpty", &[var_arg(0)], &env_strs(&[(0, "")]), 4096);
    assert!(matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))));
}

#[test]
fn test_fold_string_append_max_length_guard() {
    let e = {
        let mut e = PropagationEnv::new();
        e.insert(var(0), KnownVal2::Str("a".repeat(600)));
        e.insert(var(1), KnownVal2::Str("b".repeat(600)));
        e
    };
    assert!(fold_string("String.append", &[var_arg(0), var_arg(1)], &e, 1024).is_none());
}

// -- Extended String folding: exactness-or-decline vs kernel reducers --------
//    Each arm below mirrors a native reducer in clean-kernel
//    `native_reducers_string.rs`; the expected values are cross-checked against
//    that file's reducers and `native_reducers_string_tests.rs`. The whole point
//    is byte/char-exact agreement (the B82 miscompilation lesson), so each op
//    gets a normal case plus an out-of-bounds / edge case, and a declined-case
//    test where the kernel value cannot be reproduced at fold time.

/// Build an env binding `(var, value)` pairs where strings become `Str` and
/// integers become `UInt64` literals (positions/counts resolve via `get_arg_u64`).
fn env_str_and_pos(strs: &[(u32, &str)], nums: &[(u32, u64)]) -> PropagationEnv {
    let mut e = PropagationEnv::new();
    for &(id, s) in strs {
        e.insert(var(id), KnownVal2::Str(s.into()));
    }
    for &(id, n) in nums {
        e.insert(var(id), KnownVal2::Lit(IRLiteral::UInt64(n)));
    }
    e
}

// --- String.take : first n CHARACTERS (mirrors reduce_string_take) ---

#[test]
fn test_fold_string_take_basic() {
    // reduce_string_take("hello", 3) == "hel" (native_reducers_string_tests.rs).
    let e = env_str_and_pos(&[(0, "hello")], &[(1, 3)]);
    let r = fold_string("String.take", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "hel"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_take_over_length_returns_whole_string() {
    // Edge: n exceeds char count -> the whole string (chars().take saturates).
    let e = env_str_and_pos(&[(0, "hi")], &[(1, 10)]);
    let r = fold_string("String.take", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "hi"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_take_counts_chars_not_bytes() {
    // "café" is 5 bytes / 4 chars; take 3 yields the first 3 CHARS "caf",
    // identical to the kernel's char-based reducer (NOT a 3-byte slice).
    let e = env_str_and_pos(&[(0, "caf\u{00e9}")], &[(1, 3)]);
    let r = fold_string("String.take", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "caf"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_take_max_len_guard_declines() {
    let e = {
        let mut e = PropagationEnv::new();
        e.insert(var(0), KnownVal2::Str("a".repeat(2000)));
        e.insert(var(1), KnownVal2::Lit(IRLiteral::UInt64(2000)));
        e
    };
    assert!(fold_string("String.take", &[var_arg(0), var_arg(1)], &e, 1024).is_none());
}

// --- String.drop : drop first n CHARACTERS (mirrors reduce_string_drop) ---

#[test]
fn test_fold_string_drop_basic() {
    // reduce_string_drop("hello", 3) == "lo".
    let e = env_str_and_pos(&[(0, "hello")], &[(1, 3)]);
    let r = fold_string("String.drop", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "lo"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_drop_over_length_returns_empty() {
    // Edge: dropping more chars than exist yields "" (chars().skip saturates).
    let e = env_str_and_pos(&[(0, "hi")], &[(1, 10)]);
    let r = fold_string("String.drop", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s.is_empty()),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_drop_counts_chars_not_bytes() {
    // "café": drop 3 chars -> "é" (the multi-byte char survives intact).
    let e = env_str_and_pos(&[(0, "caf\u{00e9}")], &[(1, 3)]);
    let r = fold_string("String.drop", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "\u{00e9}"),
        "got {r:?}"
    );
}

// --- String.toLower / String.toUpper (mirror reduce_string_to_lower/upper) ---

#[test]
fn test_fold_string_to_lower_basic() {
    let e = env_str_and_pos(&[(0, "Hello")], &[]);
    let r = fold_string("String.toLower", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "hello"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_to_upper_basic() {
    // native_reducers_string_tests.rs: toUpper("Hello") == "HELLO".
    let e = env_str_and_pos(&[(0, "abc")], &[]);
    let r = fold_string("String.toUpper", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "ABC"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_to_upper_empty_edge() {
    let e = env_str_and_pos(&[(0, "")], &[]);
    let r = fold_string("String.toUpper", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s.is_empty()),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_to_lower_max_len_guard_declines() {
    let e = {
        let mut e = PropagationEnv::new();
        e.insert(var(0), KnownVal2::Str("A".repeat(2000)));
        e
    };
    assert!(fold_string("String.toLower", &[var_arg(0)], &e, 1024).is_none());
}

// --- String.singleton : Char -> String (mirrors reduce_string_singleton) ---

#[test]
fn test_fold_string_singleton_ascii() {
    // Char 'A' is the UInt32 code point 65 in the IR (lower_char_literal).
    let mut e = PropagationEnv::new();
    e.insert(var(0), KnownVal2::Lit(IRLiteral::UInt32(b'A' as u32)));
    let r = fold_string("String.singleton", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "A"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_singleton_unicode() {
    // e-acute (0xE9) -> single multi-byte char string, exactly as the kernel.
    let mut e = PropagationEnv::new();
    e.insert(var(0), KnownVal2::Lit(IRLiteral::UInt32(0xE9)));
    let r = fold_string("String.singleton", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "\u{00e9}"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_singleton_invalid_codepoint_declines() {
    // 0xD800 is a UTF-16 surrogate: not a valid Unicode scalar. The kernel's
    // `char::from_u32` returns None, so const-fold must DECLINE (not panic).
    let mut e = PropagationEnv::new();
    e.insert(var(0), KnownVal2::Lit(IRLiteral::UInt32(0xD800)));
    let r = fold_string("String.singleton", &[var_arg(0)], &e, 4096);
    assert!(r.is_none(), "invalid code point must decline, got {r:?}");
}

// --- String.get : byte-position Char (mirrors reduce_string_get) ---

#[test]
fn test_fold_string_get_in_range_ascii() {
    // reduce_string_get("hello", 0) == 'h' == 104; index 1 == 'e' == 101.
    let e = env_str_and_pos(&[(0, "hello")], &[(1, 0), (2, 1)]);
    let r0 = fold_string("String.get", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r0, Some(IRExpr::Lit(IRLiteral::UInt32(104)))),
        "got {r0:?}"
    );
    let r1 = fold_string("String.get", &[var_arg(0), var_arg(2)], &e, 4096);
    assert!(
        matches!(r1, Some(IRExpr::Lit(IRLiteral::UInt32(101)))),
        "got {r1:?}"
    );
}

#[test]
fn test_fold_string_get_out_of_range_returns_null_char() {
    // Out-of-bounds byte pos: kernel returns the default Char '\0' (Char.mk 0).
    let e = env_str_and_pos(&[(0, "hi")], &[(1, 10)]);
    let r = fold_string("String.get", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(0)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_get_byte_position_unicode() {
    // "café": bytes [c,a,f, 0xC3,0xA9]. Byte pos 3 is the START of 'é' (0xE9),
    // matching reduce_string_get's byte-offset semantics exactly.
    let e = env_str_and_pos(&[(0, "caf\u{00e9}")], &[(1, 3)]);
    let r = fold_string("String.get", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(0xE9)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_get_non_boundary_byte_declines() {
    // Byte pos 4 lands in the MIDDLE of the 2-byte 'é'; the kernel would slice
    // at a non-boundary (UB-adjacent). Const-fold declines rather than guess.
    let e = env_str_and_pos(&[(0, "caf\u{00e9}")], &[(1, 4)]);
    let r = fold_string("String.get", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(r.is_none(), "non-boundary byte pos must decline, got {r:?}");
}

// --- String.front : first Char or '\0' (mirrors reduce_string_front) ---

#[test]
fn test_fold_string_front_basic() {
    let e = env_str_and_pos(&[(0, "hello")], &[]);
    let r = fold_string("String.front", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(104)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_front_empty_returns_null_char() {
    // Edge: front of "" is '\0' (kernel: chars().next().unwrap_or('\0')).
    let e = env_str_and_pos(&[(0, "")], &[]);
    let r = fold_string("String.front", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(0)))),
        "got {r:?}"
    );
}

// --- String.atEnd : byte pos >= len -> Bool (mirrors reduce_string_at_end) ---

#[test]
fn test_fold_string_at_end_false() {
    let e = env_str_and_pos(&[(0, "hello")], &[(1, 0)]);
    let r = fold_string("String.atEnd", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_at_end_true_at_byte_len() {
    // "hi" has byte length 2; pos 2 is at end -> true (byte semantics).
    let e = env_str_and_pos(&[(0, "hi")], &[(1, 2)]);
    let r = fold_string("String.atEnd", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_at_end_unicode_uses_byte_len() {
    // "café" is 5 BYTES (not 4 chars): pos 4 is NOT at end, pos 5 is.
    let e = env_str_and_pos(&[(0, "caf\u{00e9}")], &[(1, 4), (2, 5)]);
    let r4 = fold_string("String.atEnd", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r4, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r4:?}"
    );
    let r5 = fold_string("String.atEnd", &[var_arg(0), var_arg(2)], &e, 4096);
    assert!(
        matches!(r5, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r5:?}"
    );
}

// --- String.extract : byte-offset substring (mirrors reduce_string_extract) ---

#[test]
fn test_fold_string_extract_basic() {
    // reduce_string_extract("hello world", 0, 5) == "hello".
    let e = env_str_and_pos(&[(0, "hello world")], &[(1, 0), (2, 5)]);
    let r = fold_string(
        "String.extract",
        &[var_arg(0), var_arg(1), var_arg(2)],
        &e,
        4096,
    );
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "hello"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_extract_empty_when_start_ge_stop() {
    // start == stop -> "" (kernel returns empty string).
    let e = env_str_and_pos(&[(0, "hello")], &[(1, 3), (2, 3)]);
    let r = fold_string(
        "String.extract",
        &[var_arg(0), var_arg(1), var_arg(2)],
        &e,
        4096,
    );
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s.is_empty()),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_extract_clamps_bounds_to_byte_len() {
    // stop beyond byte length is clamped to len (kernel: min(stop, s.len())).
    let e = env_str_and_pos(&[(0, "abc")], &[(1, 1), (2, 99)]);
    let r = fold_string(
        "String.extract",
        &[var_arg(0), var_arg(1), var_arg(2)],
        &e,
        4096,
    );
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "bc"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_extract_non_boundary_declines() {
    // "café": stop byte 4 splits the 2-byte 'é'. Kernel returns None on a
    // non-boundary slice, so const-fold must DECLINE too.
    let e = env_str_and_pos(&[(0, "caf\u{00e9}")], &[(1, 0), (2, 4)]);
    let r = fold_string(
        "String.extract",
        &[var_arg(0), var_arg(1), var_arg(2)],
        &e,
        4096,
    );
    assert!(r.is_none(), "non-boundary extract must decline, got {r:?}");
}

// --- String.startsWith / endsWith / containsSubstr / isPrefixOf : Bool ------
//     (mirror reduce_string_starts_with / _ends_with / _contains /
//      _is_prefix_of). All total and exact.

#[test]
fn test_fold_string_starts_with_true() {
    // reduce_string_starts_with("hello", "he") == true.
    let e = env_strs(&[(0, "hello"), (1, "he")]);
    let r = fold_string("String.startsWith", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_starts_with_false() {
    let e = env_strs(&[(0, "hello"), (1, "lo")]);
    let r = fold_string("String.startsWith", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_starts_with_empty_prefix_is_true() {
    // Every string starts with the empty prefix (str::starts_with semantics).
    let e = env_strs(&[(0, "hello"), (1, "")]);
    let r = fold_string("String.startsWith", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_ends_with_true() {
    // reduce_string_ends_with("hello", "lo") == true.
    let e = env_strs(&[(0, "hello"), (1, "lo")]);
    let r = fold_string("String.endsWith", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_ends_with_false() {
    let e = env_strs(&[(0, "hello"), (1, "he")]);
    let r = fold_string("String.endsWith", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_contains_substr_true() {
    // reduce_string_contains("hello", "ell") == true.
    let e = env_strs(&[(0, "hello"), (1, "ell")]);
    let r = fold_string("String.containsSubstr", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_contains_substr_false() {
    let e = env_strs(&[(0, "hello"), (1, "xyz")]);
    let r = fold_string("String.containsSubstr", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_is_prefix_of_arg_order() {
    // reduce_string_is_prefix_of(prefix, s) == s.starts_with(prefix): args[0] is
    // the PREFIX, args[1] the haystack. ("he" is a prefix of "hello".)
    let e = env_strs(&[(0, "he"), (1, "hello")]);
    let r = fold_string("String.isPrefixOf", &[var_arg(0), var_arg(1)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r:?}"
    );
    // Reversed: "hello" is NOT a prefix of "he".
    let r2 = fold_string("String.isPrefixOf", &[var_arg(1), var_arg(0)], &e, 4096);
    assert!(
        matches!(r2, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r2:?}"
    );
}

// --- String.replace : String (mirrors reduce_string_replace) ----------------

#[test]
fn test_fold_string_replace_basic() {
    // reduce_string_replace("aXbXc", "X", "-") == "a-b-c".
    let e = env_strs(&[(0, "aXbXc"), (1, "X"), (2, "-")]);
    let r = fold_string(
        "String.replace",
        &[var_arg(0), var_arg(1), var_arg(2)],
        &e,
        4096,
    );
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "a-b-c"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_replace_no_match_unchanged() {
    let e = env_strs(&[(0, "hello"), (1, "z"), (2, "Q")]);
    let r = fold_string(
        "String.replace",
        &[var_arg(0), var_arg(1), var_arg(2)],
        &e,
        4096,
    );
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "hello"),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_replace_max_len_guard_declines() {
    // A replacement that blows past max_len declines rather than allocating.
    let mut e = PropagationEnv::new();
    e.insert(var(0), KnownVal2::Str("a".repeat(100)));
    e.insert(var(1), KnownVal2::Str("a".into()));
    e.insert(var(2), KnownVal2::Str("bb".into()));
    assert!(fold_string(
        "String.replace",
        &[var_arg(0), var_arg(1), var_arg(2)],
        &e,
        64
    )
    .is_none());
}

// --- String.trimLeft / trimRight : String (mirror reduce_string_trim_*) -----

#[test]
fn test_fold_string_trim_left() {
    // reduce_string_trim_left("  hi ") == "hi " (leading whitespace removed).
    let e = env_strs(&[(0, "  hi ")]);
    let r = fold_string("String.trimLeft", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == "hi "),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_trim_right() {
    // reduce_string_trim_right(" hi  ") == " hi" (trailing whitespace removed).
    let e = env_strs(&[(0, " hi  ")]);
    let r = fold_string("String.trimRight", &[var_arg(0)], &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::String(ref s)) if s == " hi"),
        "got {r:?}"
    );
}

// --- String.substrEq : byte-offset substring comparison ---------------------
//     (mirrors reduce_string_substr_eq exactly, including the OOB-false and
//      non-boundary-decline edge cases).

#[test]
fn test_fold_string_substr_eq_true() {
    // s1="hello", off1=1, s2="jello", off2=1, len=4 -> "ello"=="ello" -> true.
    let e = env_str_and_pos(&[(0, "hello"), (2, "jello")], &[(1, 1), (3, 1), (4, 4)]);
    let args = [var_arg(0), var_arg(1), var_arg(2), var_arg(3), var_arg(4)];
    let r = fold_string("String.substrEq", &args, &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_substr_eq_false() {
    // s1="hello"[0..3]="hel", s2="world"[0..3]="wor" -> false.
    let e = env_str_and_pos(&[(0, "hello"), (2, "world")], &[(1, 0), (3, 0), (4, 3)]);
    let args = [var_arg(0), var_arg(1), var_arg(2), var_arg(3), var_arg(4)];
    let r = fold_string("String.substrEq", &args, &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_substr_eq_out_of_bounds_is_false() {
    // off1+len exceeds s1.len() -> kernel returns false (not a decline).
    let e = env_str_and_pos(&[(0, "hi"), (2, "hi")], &[(1, 0), (3, 0), (4, 5)]);
    let args = [var_arg(0), var_arg(1), var_arg(2), var_arg(3), var_arg(4)];
    let r = fold_string("String.substrEq", &args, &e, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_string_substr_eq_non_boundary_declines() {
    // "café" is 5 bytes (é = 2 bytes at 3..5); slicing end at byte 4 lands inside
    // the é, so the kernel's is_char_boundary check fails -> DECLINE (None).
    let e = env_str_and_pos(
        &[(0, "caf\u{00e9}"), (2, "caf\u{00e9}")],
        &[(1, 0), (3, 0), (4, 4)],
    );
    let args = [var_arg(0), var_arg(1), var_arg(2), var_arg(3), var_arg(4)];
    assert!(fold_string("String.substrEq", &args, &e, 4096).is_none());
}

// --- Declined ops still return None (unchanged behavior) ---

#[test]
fn test_fold_string_declined_ops_return_none() {
    // Ops with no exact const-fold arm must still decline (left to the kernel).
    let e = env_str_and_pos(&[(0, "hello"), (1, "lo")], &[(2, 11)]);
    // String.hash, String.next, String.prev, String.intercalate, String.decLt
    // are deliberately NOT folded here: their kernel results are a Nat hash, a
    // byte position requiring full UTF-8 width logic, a List-shaped argument, or
    // a `Decidable` constructor (not a single scalar IRExpr).
    assert!(fold_string("String.hash", &[var_arg(0)], &e, 4096).is_none());
    assert!(fold_string("String.next", &[var_arg(0), var_arg(2)], &e, 4096).is_none());
    assert!(fold_string("String.prev", &[var_arg(0), var_arg(2)], &e, 4096).is_none());
    assert!(fold_string("String.intercalate", &[var_arg(0), var_arg(1)], &e, 4096).is_none());
    assert!(fold_string("String.decLt", &[var_arg(0), var_arg(1)], &e, 4096).is_none());
    // Unknown / unrelated op.
    assert!(fold_string("String.frobnicate", &[var_arg(0)], &e, 4096).is_none());
}

#[test]
fn test_fold_string_unknown_arg_declines() {
    // Args not bound to known literals must decline (no value to fold against).
    let e = PropagationEnv::new();
    assert!(fold_string("String.take", &[var_arg(0), var_arg(1)], &e, 4096).is_none());
    assert!(fold_string("String.get", &[var_arg(0), var_arg(1)], &e, 4096).is_none());
    assert!(fold_string("String.toUpper", &[var_arg(0)], &e, 4096).is_none());
}

// --- End-to-end: a folded String.take flows through the whole pass ---

#[test]
fn test_pass_folds_string_take_end_to_end() {
    let body = chain_lets_ty(
        vec![
            (0, str_expr("hello"), IRType::Object),
            (1, lit_u64(3), IRType::UInt64),
            (
                2,
                apply("String.take", vec![var_arg(0), var_arg(1)]),
                IRType::Object,
            ),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.string_folds >= 1,
        "expected a string fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::String(s)) if s == "hel"),
        "got {folded:?}"
    );
}

// -- Char folding ------------------------------------------------------------
//
// A `Char` in the IR is its Unicode scalar value as a `UInt32` code point (the
// `to_ir_ext::lower_char_literal` shape). Each arm below is value-equal to the
// kernel reducer in `clean-kernel/src/env/native_reducers_char.rs`.

/// Bind variable `id` to a `Char` carrying scalar value `c` (the `UInt32`
/// code-point shape the lowerer emits).
fn env_char(id: u32, c: char) -> PropagationEnv {
    let mut e = PropagationEnv::new();
    e.insert(var(id), KnownVal2::Lit(IRLiteral::UInt32(c as u32)));
    e
}

#[test]
fn test_fold_char_of_nat_valid_scalar() {
    // `Char.ofNat 65 = 'A'`, materialized as the UInt32 code point.
    let mut e = PropagationEnv::new();
    e.insert(var(0), KnownVal2::Lit(IRLiteral::UInt64(65)));
    let r = fold_char("Char.ofNat", &[var_arg(0)], &e);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(65)))),
        "{r:?}"
    );
}

#[test]
fn test_fold_char_of_nat_invalid_scalar_maps_to_nul() {
    // Surrogate / out-of-range code points are NOT valid scalar values; the
    // kernel's `char::from_u32(..).unwrap_or('\0')` maps them to NUL. A
    // high-surrogate `0xD800` and an above-max `0x110000` both fold to `'\0'`.
    let mut e = PropagationEnv::new();
    e.insert(var(0), KnownVal2::Lit(IRLiteral::UInt64(0xD800)));
    e.insert(var(1), KnownVal2::Lit(IRLiteral::UInt64(0x110000)));
    assert!(
        matches!(
            fold_char("Char.ofNat", &[var_arg(0)], &e),
            Some(IRExpr::Lit(IRLiteral::UInt32(0)))
        ),
        "surrogate ofNat should be '\\0'"
    );
    assert!(
        matches!(
            fold_char("Char.ofNat", &[var_arg(1)], &e),
            Some(IRExpr::Lit(IRLiteral::UInt32(0)))
        ),
        "above-max ofNat should be '\\0'"
    );
}

#[test]
fn test_fold_char_of_nat_truncates_to_u32_like_kernel() {
    // The kernel reads the Nat then does `n as u32`. A value with set bits above
    // bit 32 truncates: `0x1_0000_0041` -> low 32 bits `0x41` = 'A'.
    let mut e = PropagationEnv::new();
    e.insert(var(0), KnownVal2::Lit(IRLiteral::UInt64(0x1_0000_0041)));
    let r = fold_char("Char.ofNat", &[var_arg(0)], &e);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(0x41)))),
        "{r:?}"
    );
}

#[test]
fn test_fold_char_to_nat_and_val() {
    // `Char.toNat 'A' = 65 : Nat`, materialized UInt64; `Char.val` is the alias.
    let e = env_char(0, 'A');
    assert!(
        matches!(
            fold_char("Char.toNat", &[var_arg(0)], &e),
            Some(IRExpr::Lit(IRLiteral::UInt64(65)))
        ),
        "toNat"
    );
    assert!(
        matches!(
            fold_char("Char.val", &[var_arg(0)], &e),
            Some(IRExpr::Lit(IRLiteral::UInt64(65)))
        ),
        "val"
    );
}

#[test]
fn test_fold_char_to_nat_non_ascii() {
    // 'é' = U+00E9 = 233.
    let e = env_char(0, '\u{00e9}');
    assert!(matches!(
        fold_char("Char.toNat", &[var_arg(0)], &e),
        Some(IRExpr::Lit(IRLiteral::UInt64(233)))
    ));
}

#[test]
fn test_fold_char_is_alpha() {
    assert!(matches!(
        fold_char("Char.isAlpha", &[var_arg(0)], &env_char(0, 'x')),
        Some(IRExpr::Lit(IRLiteral::Bool(true)))
    ));
    assert!(matches!(
        fold_char("Char.isAlpha", &[var_arg(0)], &env_char(0, '7')),
        Some(IRExpr::Lit(IRLiteral::Bool(false)))
    ));
}

#[test]
fn test_fold_char_is_digit_ascii_only() {
    // Kernel `Char.isDigit` is ASCII `'0'..='9'` ONLY, not Unicode Nd.
    assert!(matches!(
        fold_char("Char.isDigit", &[var_arg(0)], &env_char(0, '5')),
        Some(IRExpr::Lit(IRLiteral::Bool(true)))
    ));
    // Arabic-Indic digit U+0660 is Unicode-numeric but NOT ASCII => false.
    assert!(matches!(
        fold_char("Char.isDigit", &[var_arg(0)], &env_char(0, '\u{0660}')),
        Some(IRExpr::Lit(IRLiteral::Bool(false)))
    ));
}

#[test]
fn test_fold_char_is_whitespace() {
    assert!(matches!(
        fold_char("Char.isWhitespace", &[var_arg(0)], &env_char(0, ' ')),
        Some(IRExpr::Lit(IRLiteral::Bool(true)))
    ));
    assert!(matches!(
        fold_char("Char.isWhitespace", &[var_arg(0)], &env_char(0, 'a')),
        Some(IRExpr::Lit(IRLiteral::Bool(false)))
    ));
}

#[test]
fn test_fold_char_is_lower_upper() {
    assert!(matches!(
        fold_char("Char.isLower", &[var_arg(0)], &env_char(0, 'a')),
        Some(IRExpr::Lit(IRLiteral::Bool(true)))
    ));
    assert!(matches!(
        fold_char("Char.isUpper", &[var_arg(0)], &env_char(0, 'A')),
        Some(IRExpr::Lit(IRLiteral::Bool(true)))
    ));
    assert!(matches!(
        fold_char("Char.isUpper", &[var_arg(0)], &env_char(0, 'a')),
        Some(IRExpr::Lit(IRLiteral::Bool(false)))
    ));
}

#[test]
fn test_fold_char_to_lower_ascii() {
    let r = fold_char("Char.toLower", &[var_arg(0)], &env_char(0, 'A'));
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(c))) if c == 'a' as u32),
        "{r:?}"
    );
}

#[test]
fn test_fold_char_to_upper_ascii() {
    let r = fold_char("Char.toUpper", &[var_arg(0)], &env_char(0, 'z'));
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(c))) if c == 'Z' as u32),
        "{r:?}"
    );
}

#[test]
fn test_fold_char_to_upper_non_ascii_first_char_mapping() {
    // Kernel non-ASCII branch is `c.to_uppercase().next().unwrap_or(c)`: 'é' ->
    // 'É' (single char). Match exactly.
    let r = fold_char("Char.toUpper", &[var_arg(0)], &env_char(0, '\u{00e9}'));
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt32(c))) if c == '\u{00c9}' as u32),
        "{r:?}"
    );
}

#[test]
fn test_fold_char_decidable_ops_decline() {
    // `Char.decEq`/`Char.decLe` build a `Decidable` constructor, not a scalar
    // literal — deliberately NOT folded.
    let mut e = env_char(0, 'a');
    e.insert(var(1), KnownVal2::Lit(IRLiteral::UInt32('b' as u32)));
    assert!(fold_char("Char.decEq", &[var_arg(0), var_arg(1)], &e).is_none());
    assert!(fold_char("Char.decLe", &[var_arg(0), var_arg(1)], &e).is_none());
}

#[test]
fn test_fold_char_unknown_arg_declines() {
    // No bound value => nothing to fold against.
    let e = PropagationEnv::new();
    assert!(fold_char("Char.toNat", &[var_arg(0)], &e).is_none());
    assert!(fold_char("Char.isAlpha", &[var_arg(0)], &e).is_none());
}

#[test]
fn test_fold_char_unknown_op_declines() {
    assert!(fold_char("Char.frobnicate", &[var_arg(0)], &env_char(0, 'a')).is_none());
    // A non-Char op on the same arg shape must not be mistaken for a Char fold.
    assert!(fold_char("Char.toNat", &[var_arg(0), var_arg(0)], &env_char(0, 'a')).is_none());
}

#[test]
fn test_pass_folds_char_to_nat_end_to_end() {
    // 'A' lowered as UInt32(65); Char.toNat folds to Nat (UInt64) 65.
    let body = chain_lets_ty(
        vec![
            (
                0,
                IRExpr::Lit(IRLiteral::UInt32('A' as u32)),
                IRType::UInt32,
            ),
            (1, apply("Char.toNat", vec![var_arg(0)]), IRType::UInt64),
        ],
        1,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.char_folds >= 1,
        "expected a char fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 1);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(65)))),
        "got {folded:?}"
    );
}

// -- Comparison folding ------------------------------------------------------

#[test]
fn test_fold_cmp_nat_beq_true() {
    assert!(matches!(fold_cmp("Nat.beq", 5, 5), Some(true)));
}

#[test]
fn test_fold_cmp_nat_beq_false() {
    assert!(matches!(fold_cmp("Nat.beq", 5, 6), Some(false)));
}

#[test]
fn test_fold_cmp_nat_ble() {
    assert!(matches!(fold_cmp("Nat.ble", 3, 5), Some(true)));
    assert!(matches!(fold_cmp("Nat.ble", 5, 5), Some(true)));
    assert!(matches!(fold_cmp("Nat.ble", 6, 5), Some(false)));
}

#[test]
fn test_fold_cmp_nat_blt() {
    assert!(matches!(fold_cmp("Nat.blt", 3, 5), Some(true)));
    assert!(matches!(fold_cmp("Nat.blt", 5, 5), Some(false)));
}

#[test]
fn test_fold_cmp_nat_bge() {
    assert!(matches!(fold_cmp("Nat.bge", 5, 3), Some(true)));
    assert!(matches!(fold_cmp("Nat.bge", 3, 5), Some(false)));
}

#[test]
fn test_fold_cmp_nat_bgt() {
    assert!(matches!(fold_cmp("Nat.bgt", 5, 3), Some(true)));
    assert!(matches!(fold_cmp("Nat.bgt", 5, 5), Some(false)));
}

#[test]
fn test_fold_cmp_int_signed() {
    let neg1 = (-1i64) as u64;
    assert!(matches!(fold_cmp("Int.blt", neg1, 0), Some(true)));
    assert!(matches!(fold_cmp("Int.bge", neg1, 0), Some(false)));
}

#[test]
fn test_fold_cmp_unknown_op() {
    assert!(fold_cmp("Foo.bar", 1, 2).is_none());
}

// -- Bitwise / shift folding (fixed-width unsigned) --------------------------

#[test]
fn test_fold_bitwise_uint8_land() {
    let r = fold_bitwise(
        "UInt8.land",
        &[IRLiteral::UInt8(0xF0), IRLiteral::UInt8(0x3C)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt8(0x30))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint16_lor() {
    let r = fold_bitwise(
        "UInt16.lor",
        &[IRLiteral::UInt16(0xF000), IRLiteral::UInt16(0x000F)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt16(0xF00F))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint32_xor() {
    let r = fold_bitwise(
        "UInt32.xor",
        &[
            IRLiteral::UInt32(0xFFFF_0000),
            IRLiteral::UInt32(0x00FF_00FF),
        ],
    );
    assert!(
        matches!(r, Some(IRLiteral::UInt32(0xFF00_00FF))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_bitwise_uint64_land() {
    let r = fold_bitwise(
        "UInt64.land",
        &[IRLiteral::UInt64(0xFF), IRLiteral::UInt64(0x0F)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt64(0x0F))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_usize_lor_preserves_type() {
    let r = fold_bitwise(
        "USize.lor",
        &[IRLiteral::USize(0b1010), IRLiteral::USize(0b0101)],
    );
    assert!(matches!(r, Some(IRLiteral::USize(0b1111))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint8_shift_left_wraps_to_width() {
    // 0x01 << 4 = 0x10 (within byte range).
    let r = fold_bitwise(
        "UInt8.shiftLeft",
        &[IRLiteral::UInt8(0x01), IRLiteral::UInt8(4)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt8(0x10))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint8_shift_left_drops_high_bits() {
    // 0xFF << 4 = 0xF0 after masking to 8 bits (high nibble shifted out).
    let r = fold_bitwise(
        "UInt8.shiftLeft",
        &[IRLiteral::UInt8(0xFF), IRLiteral::UInt8(4)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt8(0xF0))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint8_shift_left_past_width_is_zero() {
    // Shift amount >= bit width: runtime yields 0 (conservative, total).
    let r = fold_bitwise(
        "UInt8.shiftLeft",
        &[IRLiteral::UInt8(0xFF), IRLiteral::UInt8(8)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt8(0))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint64_shift_left_past_width_is_zero() {
    let r = fold_bitwise(
        "UInt64.shiftLeft",
        &[IRLiteral::UInt64(0x1), IRLiteral::UInt64(64)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt64(0))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint16_shift_right() {
    let r = fold_bitwise(
        "UInt16.shiftRight",
        &[IRLiteral::UInt16(0xF0), IRLiteral::UInt16(4)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt16(0x0F))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint32_shift_right_past_width_is_zero() {
    let r = fold_bitwise(
        "UInt32.shiftRight",
        &[IRLiteral::UInt32(0xFFFF_FFFF), IRLiteral::UInt32(32)],
    );
    assert!(matches!(r, Some(IRLiteral::UInt32(0))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint8_complement() {
    // ~0x00 masked to 8 bits = 0xFF.
    let r = fold_bitwise("UInt8.complement", &[IRLiteral::UInt8(0x00)]);
    assert!(matches!(r, Some(IRLiteral::UInt8(0xFF))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint16_complement() {
    let r = fold_bitwise("UInt16.complement", &[IRLiteral::UInt16(0x00FF)]);
    assert!(matches!(r, Some(IRLiteral::UInt16(0xFF00))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_uint64_complement() {
    let r = fold_bitwise("UInt64.complement", &[IRLiteral::UInt64(0)]);
    assert!(matches!(r, Some(IRLiteral::UInt64(u64::MAX))), "got {r:?}");
}

#[test]
fn test_fold_bitwise_mismatched_widths_not_folded() {
    // Cross-width operands are not a meaningful fixed-width op: refuse to fold.
    let r = fold_bitwise(
        "UInt8.land",
        &[IRLiteral::UInt8(0xFF), IRLiteral::UInt16(0x00FF)],
    );
    assert!(
        r.is_none(),
        "expected None for mismatched widths, got {r:?}"
    );
}

#[test]
fn test_fold_bitwise_unknown_op_not_folded() {
    let r = fold_bitwise(
        "UInt8.frobnicate",
        &[IRLiteral::UInt8(1), IRLiteral::UInt8(2)],
    );
    assert!(r.is_none());
}

#[test]
fn test_fold_bitwise_non_uint_prefix_not_folded() {
    // Nat is unbounded — not a fixed-width type, so this path declines.
    let r = fold_bitwise("Nat.land", &[IRLiteral::UInt8(1), IRLiteral::UInt8(2)]);
    assert!(r.is_none());
}

#[test]
fn test_fold_bitwise_complement_wrong_arity_not_folded() {
    let r = fold_bitwise(
        "UInt8.complement",
        &[IRLiteral::UInt8(1), IRLiteral::UInt8(2)],
    );
    assert!(r.is_none());
}

#[test]
fn test_fold_bitwise_float_operand_not_folded() {
    // Bitwise on a Float literal is meaningless: classify_uint declines.
    let r = fold_bitwise(
        "UInt64.land",
        &[IRLiteral::Float64(1.0), IRLiteral::UInt64(0xFF)],
    );
    assert!(r.is_none());
}

// -- Float arithmetic folding ------------------------------------------------

#[test]
fn test_fold_float64_add() {
    let r = fold_float(
        "Float.add",
        &[IRLiteral::Float64(1.5), IRLiteral::Float64(2.25)],
    );
    assert!(
        matches!(r, Some(IRLiteral::Float64(v)) if v == 3.75),
        "got {r:?}"
    );
}

#[test]
fn test_fold_float64_sub() {
    let r = fold_float(
        "Float.sub",
        &[IRLiteral::Float64(5.0), IRLiteral::Float64(1.5)],
    );
    assert!(
        matches!(r, Some(IRLiteral::Float64(v)) if v == 3.5),
        "got {r:?}"
    );
}

#[test]
fn test_fold_float64_mul() {
    let r = fold_float(
        "Float.mul",
        &[IRLiteral::Float64(3.0), IRLiteral::Float64(4.0)],
    );
    assert!(
        matches!(r, Some(IRLiteral::Float64(v)) if v == 12.0),
        "got {r:?}"
    );
}

#[test]
fn test_fold_float64_div() {
    let r = fold_float(
        "Float.div",
        &[IRLiteral::Float64(9.0), IRLiteral::Float64(2.0)],
    );
    assert!(
        matches!(r, Some(IRLiteral::Float64(v)) if v == 4.5),
        "got {r:?}"
    );
}

#[test]
fn test_fold_float64_div_by_zero_yields_infinity() {
    // IEEE 754: 1.0 / 0.0 = +Inf. This is total and matches the runtime, so we
    // DO fold it (the result is a well-defined constant, not undefined behavior).
    let r = fold_float(
        "Float.div",
        &[IRLiteral::Float64(1.0), IRLiteral::Float64(0.0)],
    );
    match r {
        Some(IRLiteral::Float64(v)) => {
            assert!(v.is_infinite() && v.is_sign_positive(), "got {v}");
        }
        o => panic!("expected +Inf Float64, got {o:?}"),
    }
}

#[test]
fn test_fold_float64_zero_div_zero_yields_nan() {
    // IEEE 754: 0.0 / 0.0 = NaN. Still total/deterministic, still folded.
    let r = fold_float(
        "Float.div",
        &[IRLiteral::Float64(0.0), IRLiteral::Float64(0.0)],
    );
    match r {
        Some(IRLiteral::Float64(v)) => assert!(v.is_nan(), "got {v}"),
        o => panic!("expected NaN Float64, got {o:?}"),
    }
}

#[test]
fn test_fold_float32_add_preserves_subtype() {
    let r = fold_float(
        "Float.add",
        &[IRLiteral::Float32(1.0), IRLiteral::Float32(2.0)],
    );
    assert!(
        matches!(r, Some(IRLiteral::Float32(v)) if v == 3.0),
        "got {r:?}"
    );
}

#[test]
fn test_fold_float_mixed_widths_not_folded() {
    // Float32 + Float64 is a type mismatch in the IR: do not fold.
    let r = fold_float(
        "Float.add",
        &[IRLiteral::Float32(1.0), IRLiteral::Float64(2.0)],
    );
    assert!(
        r.is_none(),
        "expected None for mixed float widths, got {r:?}"
    );
}

#[test]
fn test_fold_float_unknown_op_not_folded() {
    let r = fold_float(
        "Float.pow",
        &[IRLiteral::Float64(2.0), IRLiteral::Float64(3.0)],
    );
    assert!(r.is_none());
}

#[test]
fn test_fold_float_int_operand_not_folded() {
    let r = fold_float("Float.add", &[IRLiteral::UInt64(1), IRLiteral::UInt64(2)]);
    assert!(r.is_none());
}

#[test]
fn test_fold_float_wrong_arity_not_folded() {
    let r = fold_float("Float.add", &[IRLiteral::Float64(1.0)]);
    assert!(r.is_none());
}

// -- End-to-end pass: bitwise/float fold through fold_constants_ext2 ---------

/// Bind two fixed-width constants, apply a bitwise op, and confirm the whole
/// pass folds the call to the expected typed literal and counts a bitwise fold.
#[test]
fn test_pass_folds_uint8_land_end_to_end() {
    let body = chain_lets_ty(
        vec![
            (0, IRExpr::Lit(IRLiteral::UInt8(0xF0)), IRType::UInt8),
            (1, IRExpr::Lit(IRLiteral::UInt8(0x3C)), IRType::UInt8),
            (
                2,
                apply("UInt8.land", vec![var_arg(0), var_arg(1)]),
                IRType::UInt8,
            ),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.bitwise_folds >= 1,
        "expected a bitwise fold, stats={stats:?}"
    );
    assert_eq!(stats.total_folds(), stats.total_folds()); // sanity: includes bitwise
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt8(0x30)))),
        "got {folded:?}"
    );
}

#[test]
fn test_pass_folds_float64_mul_end_to_end() {
    let body = chain_lets_ty(
        vec![
            (0, IRExpr::Lit(IRLiteral::Float64(2.5)), IRType::Float64),
            (1, IRExpr::Lit(IRLiteral::Float64(4.0)), IRType::Float64),
            (
                2,
                apply("Float.mul", vec![var_arg(0), var_arg(1)]),
                IRType::Float64,
            ),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.float_folds >= 1,
        "expected a float fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::Float64(v))) if *v == 10.0),
        "got {folded:?}"
    );
}

/// `Nat.gcd` of two known constants folds end-to-end through the whole pass.
#[test]
fn test_pass_folds_nat_gcd_end_to_end() {
    let body = chain_lets(
        vec![
            (0, lit_u64(48)),
            (1, lit_u64(36)),
            (2, apply("Nat.gcd", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.arithmetic_folds >= 1,
        "expected an arithmetic fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(12)))),
        "got {folded:?}"
    );
}

/// `Nat.xor` of two known constants folds end-to-end through the pass.
#[test]
fn test_pass_folds_nat_xor_end_to_end() {
    let body = chain_lets(
        vec![
            (0, lit_u64(0b1100)),
            (1, lit_u64(0b1010)),
            (2, apply("Nat.xor", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.arithmetic_folds >= 1,
        "expected an arithmetic fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(0b0110)))),
        "got {folded:?}"
    );
}

/// `Int.land` of two known constants is left untouched by the pass: there is no
/// kernel reducer for signed bitwise, so the call must survive unfolded.
#[test]
fn test_pass_leaves_int_land_untouched() {
    let original = apply("Int.land", vec![var_arg(0), var_arg(1)]);
    let body = chain_lets(
        vec![(0, lit_u64(12)), (1, lit_u64(10)), (2, original.clone())],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let _ = fold_constants_ext2_default(&mut decls);
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert_eq!(
        folded,
        Some(&original),
        "Int.land must be left untouched (no kernel signed-bitwise reducer)"
    );
}

/// `Nat.pow` of two known constants folds end-to-end.
#[test]
fn test_pass_folds_nat_pow_end_to_end() {
    let body = chain_lets(
        vec![
            (0, lit_u64(3)),
            (1, lit_u64(4)),
            (2, apply("Nat.pow", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let _ = fold_constants_ext2_default(&mut decls);
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(81)))),
        "got {folded:?}"
    );
}

/// An overflowing `Nat.pow` is left untouched: the call site must remain an
/// `Apply` (no wrong constant substituted, no panic).
#[test]
fn test_pass_leaves_overflowing_nat_pow_untouched() {
    let body = chain_lets(
        vec![
            (0, lit_u64(2)),
            (1, lit_u64(64)),
            (2, apply("Nat.pow", vec![var_arg(0), var_arg(1)])),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let _ = fold_constants_ext2_default(&mut decls);
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Apply { .. })),
        "overflowing Nat.pow must not be folded, got {folded:?}"
    );
}

/// A `Nat.gcd` where one operand is an unknown (unbound) variable must NOT
/// fold — the call site stays an `Apply`.
#[test]
fn test_pass_leaves_partial_nat_gcd_untouched() {
    // Var 0 is a function parameter (no binding recorded), var 1 is a literal.
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: lit_u64(36),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: apply("Nat.gcd", vec![var_arg(0), var_arg(1)]),
            rest: Box::new(IRBody::Ret(var_arg(2))),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let _ = fold_constants_ext2_default(&mut decls);
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Apply { .. })),
        "partial Nat.gcd must not be folded, got {folded:?}"
    );
}

/// `Bool.xor` of two known booleans folds end-to-end via boolean folding.
#[test]
fn test_pass_folds_bool_xor_end_to_end() {
    let body = chain_lets_ty(
        vec![
            (0, lit_bool(true), IRType::Bool),
            (1, lit_bool(false), IRType::Bool),
            (
                2,
                apply("Bool.xor", vec![var_arg(0), var_arg(1)]),
                IRType::Bool,
            ),
        ],
        2,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.boolean_folds >= 1,
        "expected a boolean fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 2);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "got {folded:?}"
    );
}

/// Build a let-chain with per-binding types, returning `ret_var` at the tail.
fn chain_lets_ty(bindings: Vec<(u32, IRExpr, IRType)>, ret_var: u32) -> IRBody {
    let mut body = IRBody::Ret(var_arg(ret_var));
    for (vid, expr, ty) in bindings.into_iter().rev() {
        body = IRBody::VDecl {
            var: var(vid),
            ty,
            value: expr,
            rest: Box::new(body),
        };
    }
    body
}

/// Fetch the `value` of the VDecl binding variable `target`, walking the rest
/// chain. Returns `None` if no such binding exists.
fn nth_vdecl_value(body: &IRBody, target: u32) -> Option<&IRExpr> {
    let mut cur = body;
    loop {
        match cur {
            IRBody::VDecl {
                var, value, rest, ..
            } => {
                if var.0 == target {
                    return Some(value);
                }
                cur = rest;
            }
            _ => return None,
        }
    }
}

// -- Constructor tag folding -------------------------------------------------

#[test]
fn test_fold_ctor_tag_known() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: simple_ctor(3),
            args: vec![],
        },
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt64,
            value: IRExpr::Tag(var_arg(0)),
            rest: Box::new(IRBody::Ret(var_arg(1))),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.ctor_tag_folds >= 1);
    match &decls[0].body {
        IRBody::VDecl { rest, .. } => match rest.as_ref() {
            IRBody::VDecl { value, .. } => assert!(
                matches!(value, IRExpr::Lit(IRLiteral::UInt64(3))),
                "got {value:?}"
            ),
            o => panic!("expected VDecl, got {o:?}"),
        },
        o => panic!("expected VDecl, got {o:?}"),
    }
}

// -- Projection folding ------------------------------------------------------

#[test]
fn test_fold_projection_known_ctor() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::UInt64,
        value: lit_u64(42),
        rest: Box::new(IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor_with_fields(0, 1),
                args: vec![var_arg(0)],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::UInt64,
                value: IRExpr::Proj {
                    idx: 0,
                    ty: IRType::Object,
                    arg: var_arg(1),
                },
                rest: Box::new(IRBody::Ret(var_arg(2))),
            }),
        }),
    };
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.projection_folds >= 1);
}

// -- Int shift / abs folding -------------------------------------------------

#[test]
fn test_fold_arith_int_shift_left() {
    // Int.shiftLeft a n = a * 2^n (unbounded). 3 << 4 = 48, 1 << 10 = 1024 —
    // both exact and i64-representable, so they fold.
    assert_eq!(fold_arith("Int.shiftLeft", 3, 4), Some(48));
    assert_eq!(fold_arith("Int.shiftL", 1, 10), Some(1024));
}

#[test]
fn test_fold_arith_int_shift_left_past_width_declines() {
    // `Int` is unbounded: `(-1) << 64 = -(2^64)` and `0xDEAD << 200` are NOT 0 —
    // they overflow i64. The old fold wrongly returned 0 (a miscompilation); the
    // correct behaviour is to DECLINE (only the operand `0` survives, value 0).
    assert_eq!(fold_arith("Int.shiftLeft", (-1i64) as u64, 64), None);
    assert_eq!(fold_arith("Int.shiftL", 0xDEAD, 200), None);
    assert_eq!(fold_arith("Int.shiftLeft", 0, 64), Some(0));
}

#[test]
fn test_fold_arith_int_shift_right_arithmetic() {
    // Arithmetic right shift preserves sign: -8 >>> 1 = -4.
    assert_eq!(
        fold_arith("Int.shiftRight", (-8i64) as u64, 1),
        Some((-4i64) as u64)
    );
    assert_eq!(fold_arith("Int.shiftR", 32, 2), Some(8));
}

#[test]
fn test_fold_arith_int_shift_right_past_width_sign_fills() {
    // >= 64: non-negative -> 0, negative -> -1 (all sign bits).
    assert_eq!(fold_arith("Int.shiftRight", 12345, 64), Some(0));
    assert_eq!(
        fold_arith("Int.shiftR", (-1i64) as u64, 100),
        Some((-1i64) as u64)
    );
}

#[test]
fn test_fold_int_abs_positive_and_negative() {
    assert_eq!(fold_int_abs("Int.abs", 5), Some(5));
    assert_eq!(fold_int_abs("Int.abs", (-5i64) as u64), Some(5));
    assert_eq!(fold_int_abs("Int.natAbs", (-42i64) as u64), Some(42));
}

#[test]
fn test_fold_int_abs_of_min_declines() {
    // `Int` is unbounded: |i64::MIN| = 2^63, with no positive i64
    // representation. The old fold `wrapping_abs`'d back to the *negative*
    // i64::MIN (a miscompilation); the correct behaviour is to DECLINE.
    let min = i64::MIN as u64;
    assert_eq!(fold_int_abs("Int.abs", min), None);
    assert_eq!(fold_int_abs("Int.natAbs", min), None);
}

#[test]
fn test_fold_int_abs_unknown_op_not_folded() {
    assert!(fold_int_abs("Int.neg", 5).is_none());
}

#[test]
fn test_pass_folds_int_abs_end_to_end() {
    let neg = (-7i64) as u64;
    let body = chain_lets(
        vec![(0, lit_u64(neg)), (1, apply("Int.abs", vec![var_arg(0)]))],
        1,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(stats.arithmetic_folds >= 1, "stats={stats:?}");
    let folded = nth_vdecl_value(&decls[0].body, 1);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(7)))),
        "got {folded:?}"
    );
}

// -- Array folding -----------------------------------------------------------

fn array_ctor(n: usize) -> CtorInfo {
    CtorInfo {
        name: name("Array.mk"),
        tag: 0,
        num_scalars: 0,
        num_objects: n as u32,
        field_types: vec![IRType::Object; n],
    }
}

/// Build an env where `arr_var` is a known `Array.mk` of the literal elements at
/// `elem_vars[i]`, each bound to `UInt64(values[i])`.
fn env_array(arr_var: u32, elems: &[(u32, u64)]) -> PropagationEnv {
    let mut e = PropagationEnv::new();
    for &(id, v) in elems {
        e.insert(var(id), KnownVal2::Lit(IRLiteral::UInt64(v)));
    }
    e.insert(
        var(arr_var),
        KnownVal2::Array {
            info: array_ctor(elems.len()),
            elems: elems.iter().map(|&(id, _)| var_arg(id)).collect(),
        },
    );
    e
}

#[test]
fn test_fold_array_size() {
    let env = env_array(10, &[(0, 11), (1, 22), (2, 33)]);
    let r = fold_array("Array.size", &[var_arg(10)], &env);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(3)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_array_length_alias() {
    let env = env_array(10, &[(0, 1), (1, 2)]);
    let r = fold_array("Array.length", &[var_arg(10)], &env);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(2)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_array_get_in_range() {
    // Element index 1 holds the literal 22; folding `get` materializes it.
    let mut env = env_array(10, &[(0, 11), (1, 22), (2, 33)]);
    env.insert(var(20), KnownVal2::Lit(IRLiteral::UInt64(1)));
    let r = fold_array("Array.get", &[var_arg(10), var_arg(20)], &env);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(22)))),
        "got {r:?}"
    );
}

#[test]
fn test_fold_array_get_out_of_range_not_folded() {
    let mut env = env_array(10, &[(0, 11), (1, 22)]);
    env.insert(var(20), KnownVal2::Lit(IRLiteral::UInt64(5)));
    let r = fold_array("Array.get", &[var_arg(10), var_arg(20)], &env);
    assert!(r.is_none(), "out-of-range get must not fold, got {r:?}");
}

#[test]
fn test_fold_array_get_unknown_index_not_folded() {
    // Var 20 is not bound to a constant index.
    let env = env_array(10, &[(0, 11), (1, 22)]);
    let r = fold_array("Array.get", &[var_arg(10), var_arg(20)], &env);
    assert!(r.is_none(), "unknown index must not fold, got {r:?}");
}

#[test]
fn test_fold_array_set_in_range_rebuilds_ctor() {
    let mut env = env_array(10, &[(0, 11), (1, 22), (2, 33)]);
    env.insert(var(20), KnownVal2::Lit(IRLiteral::UInt64(1))); // index
                                                               // New value variable 30 (need not be a known constant for set).
    let r = fold_array("Array.set", &[var_arg(10), var_arg(20), var_arg(30)], &env);
    match r {
        Some(IRExpr::Ctor { info, args }) => {
            assert_eq!(info.name.to_string(), "Array.mk");
            assert_eq!(args, vec![var_arg(0), var_arg(30), var_arg(2)]);
        }
        o => panic!("expected rebuilt Array.mk ctor, got {o:?}"),
    }
}

#[test]
fn test_fold_array_set_out_of_range_not_folded() {
    let mut env = env_array(10, &[(0, 11)]);
    env.insert(var(20), KnownVal2::Lit(IRLiteral::UInt64(3)));
    let r = fold_array("Array.set", &[var_arg(10), var_arg(20), var_arg(30)], &env);
    assert!(r.is_none(), "out-of-range set must not fold, got {r:?}");
}

#[test]
fn test_fold_array_unknown_op_not_folded() {
    let env = env_array(10, &[(0, 11)]);
    assert!(fold_array("Array.foldl", &[var_arg(10)], &env).is_none());
}

#[test]
fn test_fold_array_on_non_array_not_folded() {
    // Var 0 is a plain literal, not a tracked Array.mk.
    let mut env = PropagationEnv::new();
    env.insert(var(0), KnownVal2::Lit(IRLiteral::UInt64(7)));
    assert!(fold_array("Array.size", &[var_arg(0)], &env).is_none());
}

/// End-to-end: build an `Array.mk` literal, take its size, and confirm the pass
/// folds the `Array.size` call to the element count and counts an array fold.
#[test]
fn test_pass_folds_array_size_end_to_end() {
    let body = chain_lets_ty(
        vec![
            (0, lit_u64(10), IRType::UInt64),
            (1, lit_u64(20), IRType::UInt64),
            (
                2,
                IRExpr::Ctor {
                    info: array_ctor(2),
                    args: vec![var_arg(0), var_arg(1)],
                },
                IRType::Object,
            ),
            (3, apply("Array.size", vec![var_arg(2)]), IRType::UInt64),
        ],
        3,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.array_folds >= 1,
        "expected an array fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 3);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(2)))),
        "got {folded:?}"
    );
}

// -- List folding ------------------------------------------------------------

fn list_nil_ctor() -> CtorInfo {
    CtorInfo {
        name: name("List.nil"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn list_cons_ctor() -> CtorInfo {
    CtorInfo {
        // Type-erased IR layout: `List.cons head tail` carries two object fields.
        name: name("List.cons"),
        tag: 1,
        num_scalars: 0,
        num_objects: 2,
        field_types: vec![IRType::Object; 2],
    }
}

/// Build an env holding a `List` cons-spine. `nil_var` is bound to `List.nil`;
/// each `(cons_var, head_var, head_val)` is bound to `List.cons head_var tail`
/// where the tail is the PREVIOUS spine var, and `head_var` to `UInt64(head_val)`.
/// The spine is built nil-first, so the LAST `cons_var` in `elems` is the head of
/// the list and the FIRST is the deepest (last) element.
fn env_list(nil_var: u32, elems: &[(u32, u32, u64)]) -> PropagationEnv {
    let mut e = PropagationEnv::new();
    e.insert(
        var(nil_var),
        KnownVal2::List {
            info: list_nil_ctor(),
            head: None,
            tail: None,
        },
    );
    let mut tail = nil_var;
    for &(cons_var, head_var, head_val) in elems {
        e.insert(var(head_var), KnownVal2::Lit(IRLiteral::UInt64(head_val)));
        e.insert(
            var(cons_var),
            KnownVal2::List {
                info: list_cons_ctor(),
                head: Some(var_arg(head_var)),
                tail: Some(var_arg(tail)),
            },
        );
        tail = cons_var;
    }
    e
}

#[test]
fn test_fold_list_length_three_element_spine() {
    // nil=0; cons 1 (head 10), cons 2 (head 11), cons 3 (head 12). Spine head=3.
    let env = env_list(0, &[(1, 10, 100), (2, 11, 200), (3, 12, 300)]);
    let r = fold_list("List.length", &[var_arg(3)], &env, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(3)))),
        "kernel reduce_list_length of a 3-cons spine is 3, got {r:?}"
    );
}

#[test]
fn test_fold_list_length_nil_is_zero() {
    let env = env_list(0, &[]);
    let r = fold_list("List.length", &[var_arg(0)], &env, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(0)))),
        "kernel reduce_list_length of List.nil is 0, got {r:?}"
    );
}

#[test]
fn test_fold_list_is_empty_nil_true() {
    let env = env_list(0, &[]);
    let r = fold_list("List.isEmpty", &[var_arg(0)], &env, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(true)))),
        "List.isEmpty [] = true, got {r:?}"
    );
}

#[test]
fn test_fold_list_is_empty_cons_false() {
    let env = env_list(0, &[(1, 10, 100)]);
    let r = fold_list("List.isEmpty", &[var_arg(1)], &env, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::Bool(false)))),
        "List.isEmpty (_ :: _) = false, got {r:?}"
    );
}

#[test]
fn test_fold_list_get_last_bang_returns_deepest_element() {
    // Spine order is [head(var3)=300, 200, 100]; the LAST element is the deepest
    // cons (var1, head value 100), matching the kernel's get_concrete_list_last.
    let env = env_list(0, &[(1, 10, 100), (2, 11, 200), (3, 12, 300)]);
    let r = fold_list("List.getLast!", &[var_arg(3)], &env, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(100)))),
        "kernel get_concrete_list_last yields the deepest element (100), got {r:?}"
    );
}

#[test]
fn test_fold_list_get_last_bang_single_element() {
    let env = env_list(0, &[(1, 10, 42)]);
    let r = fold_list("List.getLast!", &[var_arg(1)], &env, 4096);
    assert!(
        matches!(r, Some(IRExpr::Lit(IRLiteral::UInt64(42)))),
        "getLast! of a singleton is its only element, got {r:?}"
    );
}

#[test]
fn test_fold_list_get_last_bang_empty_declines() {
    // The kernel's reduce_list_get_last_bang returns None on the empty list
    // (leaving Lean's panic-backed default), which we cannot reproduce: DECLINE.
    let env = env_list(0, &[]);
    let r = fold_list("List.getLast!", &[var_arg(0)], &env, 4096);
    assert!(r.is_none(), "getLast! on [] must not fold, got {r:?}");
}

#[test]
fn test_fold_list_non_ground_tail_declines() {
    // Build a cons whose tail (var 99) is NOT a tracked List node: non-ground.
    let mut env = PropagationEnv::new();
    env.insert(var(10), KnownVal2::Lit(IRLiteral::UInt64(7)));
    env.insert(
        var(1),
        KnownVal2::List {
            info: list_cons_ctor(),
            head: Some(var_arg(10)),
            tail: Some(var_arg(99)), // unbound: symbolic tail
        },
    );
    let r = fold_list("List.length", &[var_arg(1)], &env, 4096);
    assert!(r.is_none(), "non-ground tail must decline, got {r:?}");
}

#[test]
fn test_fold_list_length_over_max_len_declines() {
    // A spine longer than max_len declines (mirrors the String.append guard).
    let env = env_list(0, &[(1, 10, 100), (2, 11, 200), (3, 12, 300)]);
    let r = fold_list("List.length", &[var_arg(3)], &env, 2);
    assert!(
        r.is_none(),
        "spine longer than max_len must decline, got {r:?}"
    );
}

#[test]
fn test_fold_list_on_non_list_declines() {
    // Var 0 is a plain literal, not a tracked List spine.
    let mut env = PropagationEnv::new();
    env.insert(var(0), KnownVal2::Lit(IRLiteral::UInt64(7)));
    assert!(fold_list("List.length", &[var_arg(0)], &env, 4096).is_none());
}

#[test]
fn test_fold_list_unknown_op_declines() {
    let env = env_list(0, &[(1, 10, 100)]);
    assert!(fold_list("List.map", &[var_arg(1)], &env, 4096).is_none());
    // A list-PRODUCING op (append) is intentionally not folded — the result is a
    // cons-spine that cannot be a single IRExpr.
    assert!(fold_list("List.append", &[var_arg(1), var_arg(0)], &env, 4096).is_none());
    assert!(fold_list("List.reverse", &[var_arg(1)], &env, 4096).is_none());
}

#[test]
fn test_fold_list_wrong_arity_declines() {
    let env = env_list(0, &[(1, 10, 100)]);
    // `List.length` takes a single (type-erased) list argument.
    assert!(fold_list("List.length", &[var_arg(1), var_arg(0)], &env, 4096).is_none());
}

/// End-to-end: build a 3-element `List.cons` spine, take its `List.length`, and
/// confirm the pass folds the call to the element count and counts a list fold.
#[test]
fn test_pass_folds_list_length_end_to_end() {
    let body = chain_lets_ty(
        vec![
            (
                0,
                IRExpr::Ctor {
                    info: list_nil_ctor(),
                    args: vec![],
                },
                IRType::Object,
            ),
            (10, lit_u64(100), IRType::UInt64),
            (
                1,
                IRExpr::Ctor {
                    info: list_cons_ctor(),
                    args: vec![var_arg(10), var_arg(0)],
                },
                IRType::Object,
            ),
            (11, lit_u64(200), IRType::UInt64),
            (
                2,
                IRExpr::Ctor {
                    info: list_cons_ctor(),
                    args: vec![var_arg(11), var_arg(1)],
                },
                IRType::Object,
            ),
            (12, lit_u64(300), IRType::UInt64),
            (
                3,
                IRExpr::Ctor {
                    info: list_cons_ctor(),
                    args: vec![var_arg(12), var_arg(2)],
                },
                IRType::Object,
            ),
            (4, apply("List.length", vec![var_arg(3)]), IRType::UInt64),
        ],
        4,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.list_folds >= 1,
        "expected a list fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 4);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(3)))),
        "got {folded:?}"
    );
}

/// End-to-end: `List.getLast!` over a built spine folds to the deepest element.
#[test]
fn test_pass_folds_list_get_last_bang_end_to_end() {
    let body = chain_lets_ty(
        vec![
            (
                0,
                IRExpr::Ctor {
                    info: list_nil_ctor(),
                    args: vec![],
                },
                IRType::Object,
            ),
            (10, lit_u64(42), IRType::UInt64),
            (
                1,
                IRExpr::Ctor {
                    info: list_cons_ctor(),
                    args: vec![var_arg(10), var_arg(0)],
                },
                IRType::Object,
            ),
            (11, lit_u64(99), IRType::UInt64),
            (
                2,
                IRExpr::Ctor {
                    info: list_cons_ctor(),
                    args: vec![var_arg(11), var_arg(1)],
                },
                IRType::Object,
            ),
            (3, apply("List.getLast!", vec![var_arg(2)]), IRType::UInt64),
        ],
        3,
    );
    let mut decls = vec![make_decl(body)];
    let stats = fold_constants_ext2_default(&mut decls);
    assert!(
        stats.list_folds >= 1 || stats.partial_eval_folds >= 1,
        "expected a list/partial fold, stats={stats:?}"
    );
    let folded = nth_vdecl_value(&decls[0].body, 3);
    assert!(
        matches!(folded, Some(IRExpr::Lit(IRLiteral::UInt64(42)))),
        "getLast! folds to the deepest element 42, got {folded:?}"
    );
}

// -- Statistics --------------------------------------------------------------

#[test]
fn test_stats_total_folds() {
    let stats = ConstFoldExt2Stats {
        arithmetic_folds: 1,
        boolean_folds: 2,
        string_folds: 3,
        array_folds: 11,
        list_folds: 12,
        char_folds: 13,
        comparison_folds: 4,
        bitwise_folds: 9,
        float_folds: 10,
        ctor_tag_folds: 5,
        projection_folds: 6,
        partial_eval_folds: 7,
        dead_branch_folds: 8,
        propagations: 100,
        iterations: 1,
    };
    assert_eq!(stats.total_folds(), 91);
}

#[test]
fn test_stats_merge() {
    let mut a = ConstFoldExt2Stats {
        arithmetic_folds: 1,
        boolean_folds: 1,
        string_folds: 1,
        array_folds: 1,
        list_folds: 1,
        char_folds: 1,
        comparison_folds: 1,
        bitwise_folds: 1,
        float_folds: 1,
        ctor_tag_folds: 1,
        projection_folds: 1,
        partial_eval_folds: 1,
        dead_branch_folds: 1,
        propagations: 1,
        iterations: 0,
    };
    let b = ConstFoldExt2Stats {
        arithmetic_folds: 10,
        boolean_folds: 10,
        string_folds: 10,
        array_folds: 10,
        list_folds: 10,
        char_folds: 10,
        comparison_folds: 10,
        bitwise_folds: 10,
        float_folds: 10,
        ctor_tag_folds: 10,
        projection_folds: 10,
        partial_eval_folds: 10,
        dead_branch_folds: 10,
        propagations: 10,
        iterations: 0,
    };
    a.merge(&b);
    assert_eq!(a.arithmetic_folds, 11);
    assert_eq!(a.array_folds, 11);
    assert_eq!(a.list_folds, 11);
    assert_eq!(a.char_folds, 11);
    assert_eq!(a.bitwise_folds, 11);
    assert_eq!(a.float_folds, 11);
    assert_eq!(a.total_folds(), 143);
}
