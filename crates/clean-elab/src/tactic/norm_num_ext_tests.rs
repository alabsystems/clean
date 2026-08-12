// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended norm_num tactic (rational, power, modular, bitwise).
//!
//! Part of #3082.

use super::norm_num_ext::*;
use super::tests::*;
use super::*;
use clean_kernel::level::Level;

// =========================================================================
// eval_extended unit tests
// =========================================================================

fn default_config() -> NormNumExtConfig {
    NormNumExtConfig::default()
}

#[test]
fn test_eval_extended_nat_literal() {
    let expr = Expr::nat_lit(42);
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(42));
}

#[test]
fn test_eval_extended_zero() {
    let expr = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(0));
}

#[test]
fn test_eval_extended_addition() {
    // Nat.add 10 20 = 30
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(20),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(30));
}

#[test]
fn test_eval_extended_power_nat() {
    // Nat.pow 2 10 = 1024
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(10),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(1024));
}

#[test]
fn test_eval_extended_power_zero_exponent() {
    // Nat.pow 7 0 = 1
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(7),
        ),
        Expr::nat_lit(0),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(1));
}

#[test]
fn test_eval_extended_power_one_exponent() {
    // Nat.pow 99 1 = 99
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(99),
        ),
        Expr::nat_lit(1),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(99));
}

#[test]
fn test_eval_extended_mod_nat() {
    // Nat.mod 17 5 = 2
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mod"), vec![]),
            Expr::nat_lit(17),
        ),
        Expr::nat_lit(5),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(2));
}

#[test]
fn test_eval_extended_mod_zero_divisor() {
    // Nat.mod 10 0 = 10 (Lean convention)
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mod"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(0),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(10));
}

#[test]
fn test_eval_extended_div_nat() {
    // Nat.div 20 4 = 5
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.div"), vec![]),
            Expr::nat_lit(20),
        ),
        Expr::nat_lit(4),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(5));
}

#[test]
fn test_eval_extended_div_truncation() {
    // Nat.div 7 2 = 3 (truncated)
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.div"), vec![]),
            Expr::nat_lit(7),
        ),
        Expr::nat_lit(2),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(3));
}

#[test]
fn test_eval_extended_div_by_zero() {
    // Nat.div 5 0 = 0 (Lean convention)
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.div"), vec![]),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(0),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(0));
}

#[test]
fn test_eval_extended_bitwise_and() {
    // Nat.land 0b1100 0b1010 = 0b1000 = 8
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.land"), vec![]),
            Expr::nat_lit(0b1100),
        ),
        Expr::nat_lit(0b1010),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(8));
}

#[test]
fn test_eval_extended_bitwise_or() {
    // Nat.lor 0b1100 0b1010 = 0b1110 = 14
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.lor"), vec![]),
            Expr::nat_lit(0b1100),
        ),
        Expr::nat_lit(0b1010),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(14));
}

#[test]
fn test_eval_extended_bitwise_xor() {
    // Nat.xor 0b1100 0b1010 = 0b0110 = 6
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.xor"), vec![]),
            Expr::nat_lit(0b1100),
        ),
        Expr::nat_lit(0b1010),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(6));
}

#[test]
fn test_eval_extended_shift_left() {
    // Nat.shiftLeft 1 3 = 8
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.shiftLeft"), vec![]),
            Expr::nat_lit(1),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(8));
}

#[test]
fn test_eval_extended_shift_right() {
    // Nat.shiftRight 16 2 = 4
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.shiftRight"), vec![]),
            Expr::nat_lit(16),
        ),
        Expr::nat_lit(2),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(4));
}

#[test]
fn test_eval_extended_int_neg() {
    // Int.neg (Int.ofNat 7) = -7
    let inner = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(7),
    );
    let expr = Expr::app(Expr::const_(Name::from_string("Int.neg"), vec![]), inner);
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(-7));
}

#[test]
fn test_eval_extended_neg_succ() {
    // Int.negSucc 2 = -3
    let expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(2),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(-3));
}

#[test]
fn test_eval_extended_nested_pow_mod() {
    // Nat.mod (Nat.pow 2 4) 5 = 16 % 5 = 1
    let pow_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(4),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mod"), vec![]), pow_expr),
        Expr::nat_lit(5),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(1));
}

// =========================================================================
// Signed Int mod/div: T-division (Int.mod/Int.div) vs Euclidean
// (Int.emod/Int.ediv). Matches Lean 4 core and clean-kernel's native
// `reduce_int_mod` (checked_rem) / `reduce_int_div` (checked_div).
// =========================================================================

/// Build `Int.<op> (-7) 3` where `-7 = Int.negSucc 6` and `3 = Int.ofNat 3`.
fn int_binop_neg7_3(op: &str) -> Expr {
    let neg7 = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(6),
    );
    let three = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(op), vec![]), neg7),
        three,
    )
}

#[test]
fn test_eval_extended_int_mod_negative_t_division() {
    // Int.mod uses T-remainder (sign follows dividend): (-7) % 3 = -1.
    // Lean 4 `Int.mod` and clean-kernel `reduce_int_mod` (checked_rem) agree.
    let expr = int_binop_neg7_3("Int.mod");
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(-1));
}

#[test]
fn test_eval_extended_int_div_negative_t_division() {
    // Int.div truncates toward zero: (-7) / 3 = -2.
    // Lean 4 `Int.div` and clean-kernel `reduce_int_div` (checked_div) agree.
    let expr = int_binop_neg7_3("Int.div");
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(-2));
}

#[test]
fn test_eval_extended_int_emod_negative_euclidean() {
    // Int.emod is Euclidean (remainder always non-negative): (-7) emod 3 = 2.
    let expr = int_binop_neg7_3("Int.emod");
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(2));
}

#[test]
fn test_eval_extended_int_ediv_negative_euclidean() {
    // Int.ediv rounds toward negative infinity (positive divisor):
    // (-7) ediv 3 = -3.
    let expr = int_binop_neg7_3("Int.ediv");
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(-3));
}

#[test]
fn test_eval_extended_int_mod_positive_unchanged() {
    // Positive operands: T-division and Euclidean agree, 7 % 3 = 1.
    let seven = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(7),
    );
    let three = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.mod"), vec![]), seven),
        three,
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(1));
}

#[test]
fn test_eval_extended_symbolic_returns_none() {
    let expr = Expr::const_(Name::from_string("x"), vec![]);
    assert_eq!(eval_extended(&expr, &default_config(), 0), None);
}

#[test]
fn test_eval_extended_max_depth_exceeded() {
    // Should return None when depth exceeds max_depth
    let expr = Expr::nat_lit(5);
    let mut config = default_config();
    config.max_depth = 0;
    assert_eq!(eval_extended(&expr, &config, 1), None);
}

#[test]
fn test_eval_extended_disabled_power() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );
    let mut config = default_config();
    config.enable_power = false;
    // With power disabled, Nat.pow should not be evaluated
    assert_eq!(eval_extended(&expr, &config, 0), None);
}

#[test]
fn test_eval_extended_disabled_bitwise() {
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.land"), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(1),
    );
    let mut config = default_config();
    config.enable_bitwise = false;
    assert_eq!(eval_extended(&expr, &config, 0), None);
}

// =========================================================================
// Extension registry tests
// =========================================================================

#[test]
fn test_custom_extension_registration() {
    clear_norm_num_extensions();
    // Register an extension that recognizes "MyConst" as 42
    fn my_ext(expr: &Expr) -> Option<i128> {
        if let ExprKind::Const(name, _) = expr.kind() {
            if name.to_string() == "MyConst" {
                return Some(42);
            }
        }
        None
    }
    register_norm_num_extension(my_ext);

    let expr = Expr::const_(Name::from_string("MyConst"), vec![]);
    let evaluated = eval_extended(&expr, &default_config(), 0);
    clear_norm_num_extensions();
    // Closed in Wave 90: the Const arm now falls through to
    // `try_custom_extensions` after exhausting the hard-coded
    // `Nat.zero` / `Int.one` / etc. table, so registered extensions are
    // actually reachable.
    assert_eq!(
        evaluated,
        Some(42),
        "registered custom extension must be consulted on nullary Const",
    );
}

#[test]
fn test_custom_extension_not_consulted_when_empty() {
    // Negative guard for Wave 90: without any registration, the
    // fallthrough must not invent a value for unknown constants — it
    // must return `None`.
    clear_norm_num_extensions();
    let expr = Expr::const_(Name::from_string("MyConst"), vec![]);
    let evaluated = eval_extended(&expr, &default_config(), 0);
    assert_eq!(
        evaluated, None,
        "no registered extensions => unknown Const must evaluate to None",
    );
}

#[test]
fn test_custom_extension_does_not_override_builtin() {
    // Negative guard for Wave 90: the built-in constant table
    // (`Nat.zero` / `Int.one` / ...) must take precedence over a
    // registered extension that would return a different value for the
    // same name. This prevents extensions from silently shadowing the
    // canonical interpretation of well-known constants.
    clear_norm_num_extensions();
    fn shadow_nat_zero(expr: &Expr) -> Option<i128> {
        if let ExprKind::Const(name, _) = expr.kind() {
            if name.to_string() == "Nat.zero" {
                return Some(999);
            }
        }
        None
    }
    register_norm_num_extension(shadow_nat_zero);

    let expr = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let evaluated = eval_extended(&expr, &default_config(), 0);
    clear_norm_num_extensions();
    assert_eq!(
        evaluated,
        Some(0),
        "built-in `Nat.zero = 0` must shadow a conflicting extension",
    );
}

// =========================================================================
// Tactic-level tests
// =========================================================================

/// Helper: build `@Eq.{1} Nat lhs rhs`
fn nat_eq_goal(lhs: Expr, rhs: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            lhs,
        ),
        rhs,
    )
}

#[test]
fn test_tactic_power_equality() {
    // Goal: 2 ^ 5 = 32
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let pow_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(5),
    );
    let goal = nat_eq_goal(pow_expr, Expr::nat_lit(32));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close 2^5 = 32");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_mod_equality() {
    // Goal: 10 % 3 = 1
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let mod_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mod"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    let goal = nat_eq_goal(mod_expr, Expr::nat_lit(1));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close 10 % 3 = 1");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_inequality_fails() {
    // Goal: 2 ^ 3 = 9 (should fail)
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let pow_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );
    let goal = nat_eq_goal(pow_expr, Expr::nat_lit(9));
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num_ext(&mut state);
    assert!(result.is_err(), "norm_num_ext should fail on 2^3 = 9");
}

#[test]
fn test_config_default_values() {
    let config = NormNumExtConfig::default();
    assert_eq!(config.max_depth, 64);
    assert!(config.enable_rational);
    assert!(config.enable_power);
    assert!(config.enable_modular);
    assert!(config.enable_bitwise);
    assert!(config.enable_comparison);
}

// =========================================================================
// Nat.gcd: number-theoretic normalization.
//
// Divergence: Lean 4 `norm_num` closes `Nat.gcd 12 18 = 6`, but Clean's
// extended evaluator returned `None` for `Nat.gcd`, so `eval_norm_num_ext`
// failed with `ArithmeticFailed { reason: "could not evaluate extended
// numeric goal" }` — even though the kernel CAN reduce `Nat.gcd` natively.
// The evaluator now recognises `Nat.gcd`, so both the equality close (via
// `rfl`, kernel-checkable since `Nat.gcd` is a native reducer) and the
// false-detection path work.
// =========================================================================

/// Build `<op> a b` as a binary application of a named constant.
fn binop_nat(op: &str, a: u64, b: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(op), vec![]),
            Expr::nat_lit(a),
        ),
        Expr::nat_lit(b),
    )
}

#[test]
fn test_eval_extended_gcd_basic() {
    // Nat.gcd 12 18 = 6
    assert_eq!(
        eval_extended(&binop_nat("Nat.gcd", 12, 18), &default_config(), 0),
        Some(6)
    );
}

#[test]
fn test_eval_extended_gcd_coprime() {
    // Nat.gcd 9 28 = 1
    assert_eq!(
        eval_extended(&binop_nat("Nat.gcd", 9, 28), &default_config(), 0),
        Some(1)
    );
}

#[test]
fn test_eval_extended_gcd_with_zero() {
    // Lean: Nat.gcd a 0 = a, Nat.gcd 0 b = b, Nat.gcd 0 0 = 0
    assert_eq!(
        eval_extended(&binop_nat("Nat.gcd", 7, 0), &default_config(), 0),
        Some(7)
    );
    assert_eq!(
        eval_extended(&binop_nat("Nat.gcd", 0, 5), &default_config(), 0),
        Some(5)
    );
    assert_eq!(
        eval_extended(&binop_nat("Nat.gcd", 0, 0), &default_config(), 0),
        Some(0)
    );
}

#[test]
fn test_eval_extended_nested_gcd_mod() {
    // Nat.mod (Nat.gcd 24 36) 7 = 12 % 7 = 5
    let gcd_expr = binop_nat("Nat.gcd", 24, 36);
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mod"), vec![]), gcd_expr),
        Expr::nat_lit(7),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(5));
}

#[test]
fn test_tactic_gcd_equality() {
    // Goal: Nat.gcd 12 18 = 6. Closes via rfl: Nat.gcd is a native kernel
    // reducer, so the produced Eq.refl proof type-checks.
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let goal = nat_eq_goal(binop_nat("Nat.gcd", 12, 18), Expr::nat_lit(6));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.gcd 12 18 = 6");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_gcd_coprime_equality() {
    // Goal: Nat.gcd 9 28 = 1 (coprime).
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let goal = nat_eq_goal(binop_nat("Nat.gcd", 9, 28), Expr::nat_lit(1));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.gcd 9 28 = 1");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_gcd_wrong_value_fails() {
    // Negative: Nat.gcd 12 18 = 7 is false (real value is 6).
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let goal = nat_eq_goal(binop_nat("Nat.gcd", 12, 18), Expr::nat_lit(7));
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num_ext(&mut state);
    assert!(
        result.is_err(),
        "norm_num_ext must reject Nat.gcd 12 18 = 7"
    );
}

// =========================================================================
// Int.natAbs / Int.toNat: Int -> Nat conversions.
//
// Divergence: Lean 4 `norm_num` closes goals such as `Int.natAbs (-5) = 5`
// and `Int.toNat (-3) = 0`, but Clean's extended evaluator did not recognise
// `Int.natAbs` / `Int.toNat`, so `eval_extended` returned `None` and
// `eval_norm_num_ext` fell back to a `reduce_eq` that produced no progress.
// The evaluator now handles both heads; the kernel has native reducers
// (`reduce_int_nat_abs`, `reduce_int_to_nat`) and `Int.toNat` is a prelude
// `def`, so the `rfl` close is kernel-checkable.
// =========================================================================

/// Build `Int.negSucc n` (= -(n+1)).
fn int_neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    )
}

/// Build `Int.ofNat n` (= n).
fn int_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

/// Build `<op> arg` as a unary application of a named constant.
fn unop(op: &str, arg: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string(op), vec![]), arg)
}

#[test]
fn test_eval_extended_int_nat_abs_negative() {
    // Int.natAbs (-5) = 5, where -5 = Int.negSucc 4.
    assert_eq!(
        eval_extended(&unop("Int.natAbs", int_neg_succ(4)), &default_config(), 0),
        Some(5)
    );
}

#[test]
fn test_eval_extended_int_nat_abs_positive() {
    // Int.natAbs 9 = 9, where 9 = Int.ofNat 9.
    assert_eq!(
        eval_extended(&unop("Int.natAbs", int_of_nat(9)), &default_config(), 0),
        Some(9)
    );
}

#[test]
fn test_eval_extended_int_nat_abs_zero() {
    // Int.natAbs 0 = 0.
    assert_eq!(
        eval_extended(&unop("Int.natAbs", int_of_nat(0)), &default_config(), 0),
        Some(0)
    );
}

#[test]
fn test_eval_extended_int_to_nat_negative_clamps_zero() {
    // Int.toNat (-3) = 0 (negatives clamp to zero), where -3 = Int.negSucc 2.
    assert_eq!(
        eval_extended(&unop("Int.toNat", int_neg_succ(2)), &default_config(), 0),
        Some(0)
    );
}

#[test]
fn test_eval_extended_int_to_nat_positive_unchanged() {
    // Int.toNat 7 = 7.
    assert_eq!(
        eval_extended(&unop("Int.toNat", int_of_nat(7)), &default_config(), 0),
        Some(7)
    );
}

#[test]
fn test_eval_extended_nested_nat_abs_neg() {
    // Int.natAbs (Int.neg (Int.ofNat 8)) = 8.
    let neg8 = unop("Int.neg", int_of_nat(8));
    assert_eq!(
        eval_extended(&unop("Int.natAbs", neg8), &default_config(), 0),
        Some(8)
    );
}

#[test]
fn test_tactic_int_to_nat_positive_equality() {
    // Goal: Int.toNat 7 = 7. Closes via rfl: Int.toNat is a prelude def and
    // a native kernel reducer, so the Eq.refl proof type-checks.
    let mut env = Environment::with_prelude();
    env.ensure_native_reducers();

    let goal = nat_eq_goal(unop("Int.toNat", int_of_nat(7)), Expr::nat_lit(7));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Int.toNat 7 = 7");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_int_to_nat_negative_clamps_to_zero() {
    // Goal: Int.toNat (-3) = 0, where -3 = Int.negSucc 2.
    let mut env = Environment::with_prelude();
    env.ensure_native_reducers();

    let goal = nat_eq_goal(unop("Int.toNat", int_neg_succ(2)), Expr::nat_lit(0));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Int.toNat (-3) = 0");
    assert!(state.is_complete());
}

#[test]
fn test_eval_ext_comparison_nat_abs_le() {
    // Comparison path: Int.natAbs (-5) <= 6 is true. Pre-fix, eval_extended
    // returned None for the Int.natAbs operand, so try_eval_ext_comparison
    // could not decide the comparison (and the norm_num_ext comparison gate
    // would not fire). This is the evaluator-level divergence exercised
    // through the comparison entry point rather than a kernel close.
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let le = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    nat,
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            unop("Int.natAbs", int_neg_succ(4)),
        ),
        Expr::nat_lit(6),
    );
    assert_eq!(
        try_eval_ext_comparison(&le, &default_config()),
        Some(true),
        "Int.natAbs (-5) <= 6 must evaluate to true",
    );
}

#[test]
fn test_eval_ext_comparison_nat_abs_lt_false() {
    // Negative comparison: Int.natAbs (-5) < 5 is false (|-5| = 5, not < 5).
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lt = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    nat,
                ),
                Expr::const_(Name::from_string("instLTNat"), vec![]),
            ),
            unop("Int.natAbs", int_neg_succ(4)),
        ),
        Expr::nat_lit(5),
    );
    assert_eq!(
        try_eval_ext_comparison(&lt, &default_config()),
        Some(false),
        "Int.natAbs (-5) < 5 must evaluate to false",
    );
}

#[test]
fn test_tactic_int_to_nat_wrong_value_fails() {
    // Negative: Int.toNat 7 = 8 is false (real value is 7).
    let mut env = Environment::with_prelude();
    env.ensure_native_reducers();

    let goal = nat_eq_goal(unop("Int.toNat", int_of_nat(7)), Expr::nat_lit(8));
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num_ext(&mut state);
    assert!(result.is_err(), "norm_num_ext must reject Int.toNat 7 = 8");
}

#[test]
fn test_eval_extended_nat_sub_saturating() {
    // Nat.sub 3 5 = 0 (saturating)
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.sub"), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(5),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(0));
}

// =========================================================================
// Int.subNatNat: signed natural difference.
//
// Divergence: Lean 4 `norm_num` closes goals such as `Int.subNatNat 5 2 = 3`
// and `Int.subNatNat 2 5 = -3`, but Clean's extended evaluator did not
// recognise the `Int.subNatNat` head, so `eval_extended` returned `None` and
// `eval_norm_num_ext` could not normalize either side (it fell through to a
// `reduce_eq` that, with the definition absent or unreduced, made no
// progress). The evaluator now treats `Int.subNatNat m n` as the signed
// difference `m - n`.
//
// SOUNDNESS: `Int.subNatNat` is a recursor-based `Declaration::Definition`
// in clean-kernel's prelude (`init_int_arith`), so the kernel reduces
// `Int.subNatNat m n` to its `Int.ofNat` / `Int.negSucc` normal form via
// delta + iota with NO `sorryAx`; the `rfl` close is kernel-checkable.
// =========================================================================

/// Build `@Eq.{1} Int lhs rhs`.
fn int_eq_goal(lhs: Expr, rhs: Expr) -> Expr {
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                int,
            ),
            lhs,
        ),
        rhs,
    )
}

#[test]
fn test_eval_extended_sub_nat_nat_positive() {
    // Int.subNatNat 5 2 = 3.
    assert_eq!(
        eval_extended(&binop_nat("Int.subNatNat", 5, 2), &default_config(), 0),
        Some(3)
    );
}

#[test]
fn test_eval_extended_sub_nat_nat_negative() {
    // Int.subNatNat 2 5 = -3 (the dividend is smaller, result is negative).
    assert_eq!(
        eval_extended(&binop_nat("Int.subNatNat", 2, 5), &default_config(), 0),
        Some(-3)
    );
}

#[test]
fn test_eval_extended_sub_nat_nat_equal_is_zero() {
    // Int.subNatNat 7 7 = 0.
    assert_eq!(
        eval_extended(&binop_nat("Int.subNatNat", 7, 7), &default_config(), 0),
        Some(0)
    );
}

#[test]
fn test_eval_extended_sub_nat_nat_with_zero() {
    // Int.subNatNat 4 0 = 4 and Int.subNatNat 0 4 = -4.
    assert_eq!(
        eval_extended(&binop_nat("Int.subNatNat", 4, 0), &default_config(), 0),
        Some(4)
    );
    assert_eq!(
        eval_extended(&binop_nat("Int.subNatNat", 0, 4), &default_config(), 0),
        Some(-4)
    );
}

#[test]
fn test_eval_extended_nested_sub_nat_nat() {
    // Int.natAbs (Int.subNatNat 2 5) = |-3| = 3.
    let snn = binop_nat("Int.subNatNat", 2, 5);
    assert_eq!(
        eval_extended(
            &Expr::app(Expr::const_(Name::from_string("Int.natAbs"), vec![]), snn),
            &default_config(),
            0
        ),
        Some(3)
    );
}

#[test]
fn test_tactic_sub_nat_nat_positive_equality() {
    // Goal: Int.subNatNat 5 2 = Int.ofNat 3. Closes via rfl: Int.subNatNat is
    // a recursor-based prelude def, so the kernel reduces it and the Eq.refl
    // proof type-checks. `init_int_ord_lemmas` transitively registers
    // `Int.subNatNat` via `init_int_arith`.
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize");
    env.ensure_native_reducers();

    let goal = int_eq_goal(binop_nat("Int.subNatNat", 5, 2), int_of_nat(3));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Int.subNatNat 5 2 = 3");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_sub_nat_nat_negative_equality() {
    // Goal: Int.subNatNat 2 5 = Int.negSucc 2 (i.e. = -3).
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize");
    env.ensure_native_reducers();

    let goal = int_eq_goal(binop_nat("Int.subNatNat", 2, 5), int_neg_succ(2));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Int.subNatNat 2 5 = -3");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_sub_nat_nat_wrong_value_fails() {
    // Negative: Int.subNatNat 5 2 = 4 is false (real value is 3).
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize");
    env.ensure_native_reducers();

    let goal = int_eq_goal(binop_nat("Int.subNatNat", 5, 2), int_of_nat(4));
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num_ext(&mut state);
    assert!(
        result.is_err(),
        "norm_num_ext must reject Int.subNatNat 5 2 = 4"
    );
}

#[test]
fn test_tactic_sub_nat_nat_proof_is_sorry_free_and_kernel_checks() {
    // SOUNDNESS guard: the proof closing `Int.subNatNat 5 2 = 3` must be
    // kernel-checkable AND axiom-free (no `sorryAx`). The close goes through
    // `rfl`/`Eq.refl`, which the kernel verifies by reducing `Int.subNatNat`
    // (recursor-based prelude def) to `Int.ofNat 3` — unlike the
    // `Nat.decLe`/`Int.decLt` reducers, this path emits no `sorryAx`.
    fn contains_const(expr: &Expr, name_str: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name == &Name::from_string(name_str),
            ExprKind::App(f, a) => contains_const(f, name_str) || contains_const(a, name_str),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_const(ty, name_str) || contains_const(body, name_str)
            }
            _ => false,
        }
    }

    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize");
    env.ensure_native_reducers();

    let goal_expr = int_eq_goal(binop_nat("Int.subNatNat", 5, 2), int_of_nat(3));
    let mut state = ProofState::new(env, goal_expr);
    let goal = state
        .current_goal()
        .cloned()
        .expect("state should have a goal");
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Int.subNatNat 5 2 = 3");
    assert!(state.is_complete());

    let proof = state
        .closed_proof()
        .expect("a completed proof state must yield a closed proof term");
    assert!(
        !contains_const(&proof, "sorryAx"),
        "Int.subNatNat close must not carry sorryAx"
    );
    assert!(
        !contains_const(&proof, "trustedAy"),
        "Int.subNatNat close must not carry a trusted-SMT axiom"
    );

    // The proof must type-check against the goal type under the kernel.
    let _cert = state
        .verify_proof(&goal, &proof)
        .expect("Int.subNatNat close proof must kernel-verify against the goal");
}

// =========================================================================
// Ground Int `<=` / `<` comparison close.
//
// Divergence: Lean 4 `norm_num` (and `decide`) close ground integer order
// goals such as `(2 : Int) ≤ 5` and `(2 : Int) < 5`. Clean evaluated the
// comparison to `true` but then delegated to `decide`, whose only Int
// comparison instances (`instDecidableIntLe` / `instDecidableIntLt`) are
// NON-COMPUTATIONAL AXIOMS — they never reduce to `isTrue`/`isFalse`, so the
// goal was left unproven (the tactic returned `Err`).
//
// Fix: build the constructive witness directly. `Int.le a b` unfolds to
// `Int.NonNeg (Int.sub b a)`; `Int.lt a b` to `Int.le (a+1) b`. The single
// constructor `Int.NonNeg.mk : (n : Nat) → Int.NonNeg (Int.ofNat n)` proves
// the goal once the difference reduces (via the native `Int.sub` reducer) to
// a non-negative `Int.ofNat`. No `sorryAx`, no decidability axiom.
// =========================================================================

/// Build `@LE.le.{0} Int instLEInt lhs rhs`.
fn int_le_goal(lhs: Expr, rhs: Expr) -> Expr {
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    int,
                ),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `@LT.lt.{0} Int instLTInt lhs rhs`.
fn int_lt_goal(lhs: Expr, rhs: Expr) -> Expr {
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    int,
                ),
                Expr::const_(Name::from_string("instLTInt"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

fn int_ord_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_int_ord_lemmas()
        .expect("Int ordering lemmas should initialize");
    env.ensure_native_reducers();
    env
}

#[test]
fn test_norm_num_ext_int_le_true_closes() {
    // Goal: (2 : Int) <= 5 — true.
    let mut state = ProofState::new(int_ord_env(), int_le_goal(int_of_nat(2), int_of_nat(5)));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (2 : Int) <= 5");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_int_lt_true_closes() {
    // Goal: (2 : Int) < 5 — true.
    let mut state = ProofState::new(int_ord_env(), int_lt_goal(int_of_nat(2), int_of_nat(5)));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (2 : Int) < 5");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_int_le_equal_endpoints_closes() {
    // Boundary: (4 : Int) <= 4 — true (difference is zero, witness Int.NonNeg.mk 0).
    let mut state = ProofState::new(int_ord_env(), int_le_goal(int_of_nat(4), int_of_nat(4)));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (4 : Int) <= 4");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_int_le_negative_endpoint_closes() {
    // Negative endpoint: (-3 : Int) <= 2 — true (difference is 5).
    let mut state = ProofState::new(int_ord_env(), int_le_goal(int_neg_succ(2), int_of_nat(2)));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (-3 : Int) <= 2");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_int_lt_negative_endpoints_closes() {
    // Both endpoints negative: (-5 : Int) < -3 — true (-5 < -3, difference is 1).
    let mut state = ProofState::new(int_ord_env(), int_lt_goal(int_neg_succ(4), int_neg_succ(2)));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (-5 : Int) < -3");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_int_le_false_rejected() {
    // Negative: (5 : Int) <= 2 — false.
    let mut state = ProofState::new(int_ord_env(), int_le_goal(int_of_nat(5), int_of_nat(2)));
    let result = eval_norm_num_ext(&mut state);
    assert!(result.is_err(), "norm_num_ext must reject (5 : Int) <= 2");
    assert!(!state.is_complete());
}

#[test]
fn test_norm_num_ext_int_lt_irreflexive_rejected() {
    // Negative: (4 : Int) < 4 — false (strict, equal endpoints).
    let mut state = ProofState::new(int_ord_env(), int_lt_goal(int_of_nat(4), int_of_nat(4)));
    let result = eval_norm_num_ext(&mut state);
    assert!(result.is_err(), "norm_num_ext must reject (4 : Int) < 4");
    assert!(!state.is_complete());
}

#[test]
fn test_decide_int_le_true_closes() {
    // The `decide` tactic must also close ground Int comparisons soundly.
    let mut state = ProofState::new(int_ord_env(), int_le_goal(int_of_nat(2), int_of_nat(5)));
    eval_decide(&mut state).expect("decide should close (2 : Int) <= 5");
    assert!(state.is_complete());
}

#[test]
fn test_decide_int_lt_false_rejected() {
    // `decide` must reject a false strict Int comparison.
    let mut state = ProofState::new(int_ord_env(), int_lt_goal(int_of_nat(5), int_of_nat(5)));
    let result = eval_decide(&mut state);
    assert!(result.is_err(), "decide must reject (5 : Int) < 5");
}

#[test]
fn test_int_ground_comparison_proof_is_sorry_free_and_kernel_checks() {
    // SOUNDNESS guard: the witness closing `(2 : Int) <= 5` must be
    // kernel-checkable AND axiom-free. The proof is `Int.NonNeg.mk 3`, an
    // inductive constructor — no `sorryAx`, and crucially no
    // `instDecidableIntLe` (the non-computational decidability axiom that the
    // `decide` reducer would otherwise have to consume).
    fn contains_const(expr: &Expr, name_str: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name == &Name::from_string(name_str),
            ExprKind::App(f, a) => contains_const(f, name_str) || contains_const(a, name_str),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_const(ty, name_str) || contains_const(body, name_str)
            }
            _ => false,
        }
    }

    let mut state = ProofState::new(int_ord_env(), int_le_goal(int_of_nat(2), int_of_nat(5)));
    let goal = state
        .current_goal()
        .cloned()
        .expect("state should have a goal");
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (2 : Int) <= 5");
    assert!(state.is_complete());

    let proof = state
        .closed_proof()
        .expect("a completed proof state must yield a closed proof term");

    // The witness head must be the Int.NonNeg.mk constructor.
    assert!(
        contains_const(&proof, "Int.NonNeg.mk"),
        "Int comparison close must use the Int.NonNeg.mk constructor"
    );
    assert!(
        !contains_const(&proof, "sorryAx"),
        "Int comparison close must not carry sorryAx"
    );
    assert!(
        !contains_const(&proof, "trustedAy"),
        "Int comparison close must not carry a trusted-SMT axiom"
    );
    assert!(
        !contains_const(&proof, "instDecidableIntLe"),
        "Int comparison close must not depend on the non-computational \
         instDecidableIntLe axiom"
    );

    // The proof must type-check against the goal type under the kernel.
    let _cert = state
        .verify_proof(&goal, &proof)
        .expect("Int comparison close proof must kernel-verify against the goal");
}

// =========================================================================
// Ground Nat `<=` / `<` / `>=` comparison close (constructive `Nat.le.step`
// chain witness).
//
// Divergence: Lean 4 `norm_num` / `decide` close ground Nat order goals. Clean
// already closed the `<=` / `<` (and typeclass `>=`) shapes via a sound
// `Nat.le.step` chain, but the BARE prelude `Nat.ge a b` head was not even
// recognized by the comparison evaluator (`try_eval_nat_comparison` only
// matched the `GE.ge` typeclass head), so a ground `Nat.ge 5 2` goal was
// dropped and the tactic returned `Err`.
//
// Fix: recognize the bare `Nat.ge` / `Nat.gt` heads, and close true ground Nat
// order goals with a constructive `Nat.le.refl` / `Nat.le.step` chain. The
// kernel's `Nat.decLe` / `Nat.decLt` reducers emit `Decidable.isTrue sorryAx`,
// so the constructive witness is required to stay sorry-free. `Nat.ge` is a
// reducible def unfolding to `Nat.le` with swapped arguments, so the kernel
// accepts the `Nat.le` witness; `close_goal` re-checks it.
// =========================================================================

/// Build `Nat.ge lhs rhs` (the bare prelude head; reduces to `Nat.le rhs lhs`).
fn nat_ge_bare(lhs: u64, rhs: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.ge"), vec![]),
            Expr::nat_lit(lhs),
        ),
        Expr::nat_lit(rhs),
    )
}

/// Build `@GE.ge.{0} Nat instLENat lhs rhs` (the typeclass head).
fn nat_ge_tc(lhs: u64, rhs: u64) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
                    nat,
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            Expr::nat_lit(lhs),
        ),
        Expr::nat_lit(rhs),
    )
}

fn nat_ord_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.ensure_native_reducers();
    env
}

#[test]
fn test_norm_num_ext_nat_ge_bare_true_closes() {
    // Goal: Nat.ge 5 2 — true. Previously dropped (bare head unrecognized).
    let mut state = ProofState::new(nat_ord_env(), nat_ge_bare(5, 2));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.ge 5 2");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_nat_ge_bare_equal_endpoints_closes() {
    // Boundary: Nat.ge 4 4 — true (reduces to Nat.le 4 4, witness Nat.le.refl 4).
    let mut state = ProofState::new(nat_ord_env(), nat_ge_bare(4, 4));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.ge 4 4");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_nat_ge_bare_false_rejected() {
    // Negative: Nat.ge 2 5 — false. Must not be mis-closed.
    let mut state = ProofState::new(nat_ord_env(), nat_ge_bare(2, 5));
    let result = eval_norm_num_ext(&mut state);
    assert!(result.is_err(), "norm_num_ext must reject Nat.ge 2 5");
    assert!(!state.is_complete());
}

#[test]
fn test_norm_num_ext_nat_ge_typeclass_true_closes() {
    // Goal: @GE.ge Nat instLENat 5 2 — true.
    let mut state = ProofState::new(nat_ord_env(), nat_ge_tc(5, 2));
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (5 : Nat) >= 2");
    assert!(state.is_complete());
}

#[test]
fn test_decide_nat_ge_bare_true_closes() {
    // `decide` must also close the bare ground Nat.ge goal soundly.
    let mut state = ProofState::new(nat_ord_env(), nat_ge_bare(5, 2));
    eval_decide(&mut state).expect("decide should close Nat.ge 5 2");
    assert!(state.is_complete());
}

#[test]
fn test_decide_nat_ge_bare_false_rejected() {
    // `decide` must reject a false bare Nat.ge goal.
    let mut state = ProofState::new(nat_ord_env(), nat_ge_bare(2, 5));
    let result = eval_decide(&mut state);
    assert!(result.is_err(), "decide must reject Nat.ge 2 5");
    assert!(!state.is_complete());
}

#[test]
fn test_nat_ge_ground_comparison_proof_is_sorry_free_and_kernel_checks() {
    // SOUNDNESS guard: the witness closing `Nat.ge 5 2` must be a
    // `Nat.le.refl` / `Nat.le.step` chain — kernel-checkable, AND free of both
    // `sorryAx` (which the native `Nat.decLe` reducer would otherwise inject
    // via `Decidable.isTrue sorryAx`) and the `trustedAy` SMT axiom.
    fn contains_const(expr: &Expr, name_str: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name == &Name::from_string(name_str),
            ExprKind::App(f, a) => contains_const(f, name_str) || contains_const(a, name_str),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_const(ty, name_str) || contains_const(body, name_str)
            }
            _ => false,
        }
    }

    let mut state = ProofState::new(nat_ord_env(), nat_ge_bare(5, 2));
    let goal = state
        .current_goal()
        .cloned()
        .expect("state should have a goal");
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.ge 5 2");
    assert!(state.is_complete());

    let proof = state
        .closed_proof()
        .expect("a completed proof state must yield a closed proof term");

    // The witness must be built from the Nat.le inductive constructors.
    assert!(
        contains_const(&proof, "Nat.le.refl") || contains_const(&proof, "Nat.le.step"),
        "Nat comparison close must use the Nat.le constructors, got {proof:?}"
    );
    assert!(
        !contains_const(&proof, "sorryAx"),
        "Nat comparison close must not carry sorryAx"
    );
    assert!(
        !contains_const(&proof, "trustedAy"),
        "Nat comparison close must not carry a trusted-SMT axiom"
    );

    // The proof must kernel-recheck against the goal type: infer its type and
    // confirm definitional equality with the goal target (the same check
    // `close_goal` performs, with full WHNF reduction so the `Nat.succ` chain
    // collapses to the goal's literal upper bound and the reducible `Nat.ge`
    // head unfolds to `Nat.le`).
    let inferred = state
        .infer_type(&goal, &proof)
        .expect("Nat comparison close proof must have an inferable type");
    assert!(
        state.is_def_eq(&goal, &inferred, &goal.target),
        "Nat comparison close proof type {inferred:?} must be def-eq to the goal {:?}",
        goal.target
    );
}

// =========================================================================
// Ground Nat comparison close where an OPERAND is `Nat.mod` / `Nat.div`.
//
// Divergence: Lean 4 `norm_num` / `decide` close ground Nat order goals whose
// operands contain `%` / `/`, e.g. `(17 : Nat) % 5 <= 4` and `(20 : Nat) / 4
// >= 4`. Clean recognized the comparison value through `eval_extended` (which
// handles `Nat.mod` / `Nat.div`), but the *sound* close path
// `try_close_nat_ground_comparison` reduced the operands with `eval_nat_expr`,
// which did NOT evaluate `Nat.mod` / `Nat.div`. So `nat_comparison_shape`
// returned `None`, the constructive `Nat.le.step` witness was skipped, and the
// goal fell through to `decide` — whose `Nat.decLe` reducer emits
// `Decidable.isTrue sorryAx`. The goal was either left open or closed with a
// `sorryAx`-tainted term.
//
// Fix: teach `eval_nat_expr` to evaluate `Nat.mod` / `Nat.div` (and the
// `HMod.hMod` / `Mod.mod` / `HDiv.hDiv` / `Div.div` heterogeneous heads) with
// Lean 4 semantics (`n % 0 = n`, `n / 0 = 0`). The kernel has native
// `Nat.mod` / `Nat.div` reducers, so the `Nat.le` witness still type-checks:
// `close_goal` reduces the operand to its literal before checking the chain.
// =========================================================================

/// Build `Nat.mod a b` (bare prelude head).
fn nat_mod(a: u64, b: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mod"), vec![]),
            Expr::nat_lit(a),
        ),
        Expr::nat_lit(b),
    )
}

/// Build `Nat.div a b` (bare prelude head).
fn nat_div(a: u64, b: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.div"), vec![]),
            Expr::nat_lit(a),
        ),
        Expr::nat_lit(b),
    )
}

/// Build `Nat.le lhs rhs` (bare prelude head) over arbitrary Nat operands.
fn nat_le_bare_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

#[test]
fn test_eval_nat_mod_basic() {
    // Direct evaluator: 17 % 5 = 2.
    assert_eq!(eval_nat_expr(&nat_mod(17, 5)), Some(2));
}

#[test]
fn test_eval_nat_div_basic() {
    // Direct evaluator: 20 / 4 = 5.
    assert_eq!(eval_nat_expr(&nat_div(20, 4)), Some(5));
}

#[test]
fn test_eval_nat_mod_by_zero_is_dividend() {
    // Lean 4 convention: n % 0 = n. Matches the kernel's native reducer.
    assert_eq!(eval_nat_expr(&nat_mod(10, 0)), Some(10));
}

#[test]
fn test_eval_nat_div_by_zero_is_zero() {
    // Lean 4 convention: n / 0 = 0. Matches the kernel's native reducer.
    assert_eq!(eval_nat_expr(&nat_div(10, 0)), Some(0));
}

#[test]
fn test_norm_num_ext_nat_mod_le_true_closes() {
    // Goal: Nat.le (17 % 5) 4  ==  2 <= 4 — true.
    let goal = nat_le_bare_expr(nat_mod(17, 5), Expr::nat_lit(4));
    let mut state = ProofState::new(nat_ord_env(), goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (17 % 5) <= 4");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_nat_div_ge_true_closes() {
    // Goal: Nat.ge (20 / 4) 4  ==  5 >= 4 — true (bare ge head).
    let goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.ge"), vec![]),
            nat_div(20, 4),
        ),
        Expr::nat_lit(4),
    );
    let mut state = ProofState::new(nat_ord_env(), goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (20 / 4) >= 4");
    assert!(state.is_complete());
}

#[test]
fn test_norm_num_ext_nat_mod_le_false_rejected() {
    // Negative: Nat.le (17 % 5) 1  ==  2 <= 1 — false. Must not be mis-closed.
    let goal = nat_le_bare_expr(nat_mod(17, 5), Expr::nat_lit(1));
    let mut state = ProofState::new(nat_ord_env(), goal);
    let result = eval_norm_num_ext(&mut state);
    assert!(result.is_err(), "norm_num_ext must reject (17 % 5) <= 1");
    assert!(!state.is_complete());
}

#[test]
fn test_norm_num_ext_nat_mod_eq_closes() {
    // Goal: Nat.mod 17 5 = 2 already worked through the kernel equality path;
    // pin that the operand evaluator change does not regress it.
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            nat_mod(17, 5),
        ),
        Expr::nat_lit(2),
    );
    let mut state = ProofState::new(nat_ord_env(), goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close 17 % 5 = 2");
    assert!(state.is_complete());
}

#[test]
fn test_nat_mod_comparison_proof_is_sorry_free_and_kernel_checks() {
    // SOUNDNESS guard: closing `Nat.le (17 % 5) 4` must use a constructive
    // `Nat.le.refl` / `Nat.le.step` chain — kernel-checkable, AND free of both
    // `sorryAx` (which the native `Nat.decLe` reducer injects via
    // `Decidable.isTrue sorryAx`) and the `trustedAy` SMT axiom. The kernel's
    // native `Nat.mod` reducer collapses the operand to `2` during the recheck.
    fn contains_const(expr: &Expr, name_str: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name == &Name::from_string(name_str),
            ExprKind::App(f, a) => contains_const(f, name_str) || contains_const(a, name_str),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_const(ty, name_str) || contains_const(body, name_str)
            }
            _ => false,
        }
    }

    let goal_expr = nat_le_bare_expr(nat_mod(17, 5), Expr::nat_lit(4));
    let mut state = ProofState::new(nat_ord_env(), goal_expr);
    let goal = state
        .current_goal()
        .cloned()
        .expect("state should have a goal");
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close (17 % 5) <= 4");
    assert!(state.is_complete());

    let proof = state
        .closed_proof()
        .expect("a completed proof state must yield a closed proof term");

    assert!(
        contains_const(&proof, "Nat.le.refl") || contains_const(&proof, "Nat.le.step"),
        "Nat comparison close must use the Nat.le constructors, got {proof:?}"
    );
    assert!(
        !contains_const(&proof, "sorryAx"),
        "Nat comparison close must not carry sorryAx"
    );
    assert!(
        !contains_const(&proof, "trustedAy"),
        "Nat comparison close must not carry a trusted-SMT axiom"
    );

    let inferred = state
        .infer_type(&goal, &proof)
        .expect("Nat comparison close proof must have an inferable type");
    assert!(
        state.is_def_eq(&goal, &inferred, &goal.target),
        "Nat comparison close proof type {inferred:?} must be def-eq to the goal {:?}",
        goal.target
    );
}

// =========================================================================
// Nat.factorial: ground factorial normalization.
//
// Divergence: Lean 4 `norm_num` closes `Nat.factorial 5 = 120`, but Clean's
// extended evaluator returned `None` for `Nat.factorial`, so `eval_norm_num_ext`
// failed with `ArithmeticFailed { reason: "could not evaluate extended numeric
// goal" }`.
//
// SOUNDNESS: clean-kernel has **no** native `Nat.factorial` reducer (unlike
// `Nat.gcd` / `Nat.pow`). `eval_extended` now computes `n!` purely to (a) decide
// whether an equality goal's two sides agree (rfl vs. `ArithmeticFailed`) and
// (b) feed the comparison / `decide` gate; it never produces a proof term. The
// proof is always built by `rfl` / `reduce_eq`, which the kernel re-checks. That
// close therefore succeeds ONLY when `Nat.factorial` is a recursor-based
// `Declaration::Definition` the kernel can unfold by delta + iota to the literal
// result. The tests below register exactly such a definition (mirroring Lean 4's
// `Nat.factorial 0 = 1`, `Nat.factorial (n+1) = (n+1) * Nat.factorial n`), so the
// `rfl` close is genuine and `sorryAx`-free; without it (see the no-definition
// test) the close fails rather than closing unsoundly.
// =========================================================================

/// Build `Nat.factorial arg` as a unary application of the constant.
fn nat_factorial(arg: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Nat.factorial"), vec![]),
        arg,
    )
}

/// Register a recursor-based `Nat.factorial` matching Lean 4 core:
/// `Nat.factorial := λ n => Nat.rec (motive := λ _ => Nat) 1 (λ m ih => (m+1) * ih) n`.
///
/// Built from the `Nat.rec` recursor and `Nat.succ` / `Nat.mul` only, so the
/// kernel reduces `Nat.factorial k` to its literal value by delta + iota with no
/// `sorryAx`. This is the genuine close path (the kernel has no native factorial
/// reducer).
fn factorial_env() -> Environment {
    use clean_kernel::env::Declaration;

    let mut env = Environment::with_prelude();
    env.ensure_native_reducers();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // Nat.factorial : Nat → Nat
    let fac_type = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());

    // motive: λ _ : Nat => Nat
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());

    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);

    // succ case: λ (m : Nat) => λ (ih : Nat) => Nat.mul (Nat.succ m) ih
    // Inside the inner body, de Bruijn: ih = bvar 0, m = bvar 1.
    let succ_case = {
        let m = Expr::bvar(1);
        let ih = Expr::bvar(0);
        let succ_m = Expr::app(nat_succ.clone(), m);
        let body = Expr::apps(nat_mul.clone(), [succ_m, ih]);
        let inner = Expr::lam(BinderInfo::Default, nat.clone(), body); // λ ih => ...
        Expr::lam(BinderInfo::Default, nat.clone(), inner) // λ m => λ ih => ...
    };

    // Nat.factorial := λ (n : Nat) => Nat.rec motive 1 succ_case n
    // Inside the body, n = bvar 0.
    let value = {
        let n = Expr::bvar(0);
        let body = Expr::apps(
            nat_rec.clone(),
            [motive.clone(), Expr::nat_lit(1), succ_case, n],
        );
        Expr::lam(BinderInfo::Default, nat.clone(), body)
    };

    env.add_decl(Declaration::Definition {
        name: Name::from_string("Nat.factorial"),
        level_params: vec![],
        type_: fac_type,
        value,
        is_reducible: true,
    })
    .expect("recursor-based Nat.factorial definition should type-check");
    env
}

#[test]
fn test_eval_extended_factorial_five() {
    // Nat.factorial 5 = 120.
    assert_eq!(
        eval_extended(&nat_factorial(Expr::nat_lit(5)), &default_config(), 0),
        Some(120)
    );
}

#[test]
fn test_eval_extended_factorial_zero_is_one() {
    // Nat.factorial 0 = 1 (empty product).
    assert_eq!(
        eval_extended(&nat_factorial(Expr::nat_lit(0)), &default_config(), 0),
        Some(1)
    );
}

#[test]
fn test_eval_extended_factorial_one_is_one() {
    // Nat.factorial 1 = 1.
    assert_eq!(
        eval_extended(&nat_factorial(Expr::nat_lit(1)), &default_config(), 0),
        Some(1)
    );
}

#[test]
fn test_eval_extended_factorial_unbound_arg_returns_none() {
    // Nat.factorial n for a free variable is symbolic — no value.
    let symbolic = nat_factorial(Expr::bvar(0));
    assert_eq!(eval_extended(&symbolic, &default_config(), 0), None);
}

#[test]
fn test_eval_extended_factorial_overflow_returns_none() {
    // 34! overflows i128 (33! < 2^118 < 34!); decline rather than wrap.
    assert_eq!(
        eval_extended(&nat_factorial(Expr::nat_lit(34)), &default_config(), 0),
        None
    );
}

#[test]
fn test_eval_extended_nested_factorial_mod() {
    // Nat.mod (Nat.factorial 5) 7 = 120 % 7 = 1.
    let fac = nat_factorial(Expr::nat_lit(5));
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mod"), vec![]), fac),
        Expr::nat_lit(7),
    );
    assert_eq!(eval_extended(&expr, &default_config(), 0), Some(1));
}

#[test]
fn test_tactic_factorial_equality() {
    // Goal: Nat.factorial 5 = 120. Closes via rfl: the recursor-based prelude
    // definition reduces under the kernel to the literal 120.
    let env = factorial_env();
    let goal = nat_eq_goal(nat_factorial(Expr::nat_lit(5)), Expr::nat_lit(120));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.factorial 5 = 120");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_factorial_zero_equality() {
    // Goal: Nat.factorial 0 = 1.
    let env = factorial_env();
    let goal = nat_eq_goal(nat_factorial(Expr::nat_lit(0)), Expr::nat_lit(1));
    let mut state = ProofState::new(env, goal);
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.factorial 0 = 1");
    assert!(state.is_complete());
}

#[test]
fn test_tactic_factorial_wrong_value_fails() {
    // Negative: Nat.factorial 5 = 100 is false (real value is 120).
    let env = factorial_env();
    let goal = nat_eq_goal(nat_factorial(Expr::nat_lit(5)), Expr::nat_lit(100));
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num_ext(&mut state);
    assert!(
        result.is_err(),
        "norm_num_ext must reject Nat.factorial 5 = 100"
    );
    assert!(!state.is_complete());
}

#[test]
fn test_tactic_factorial_proof_is_sorry_free_and_kernel_checks() {
    // SOUNDNESS guard: the proof closing `Nat.factorial 5 = 120` must be
    // kernel-checkable AND axiom-free (no `sorryAx`). The close goes through
    // `rfl`/`reduce_eq`, which the kernel verifies by unfolding the
    // recursor-based `Nat.factorial` definition to the literal `120`.
    fn contains_const(expr: &Expr, name_str: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name == &Name::from_string(name_str),
            ExprKind::App(f, a) => contains_const(f, name_str) || contains_const(a, name_str),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_const(ty, name_str) || contains_const(body, name_str)
            }
            _ => false,
        }
    }

    let env = factorial_env();
    let goal_expr = nat_eq_goal(nat_factorial(Expr::nat_lit(5)), Expr::nat_lit(120));
    let mut state = ProofState::new(env, goal_expr);
    let goal = state
        .current_goal()
        .cloned()
        .expect("state should have a goal");
    eval_norm_num_ext(&mut state).expect("norm_num_ext should close Nat.factorial 5 = 120");
    assert!(state.is_complete());

    let proof = state
        .closed_proof()
        .expect("a completed proof state must yield a closed proof term");
    assert!(
        !contains_const(&proof, "sorryAx"),
        "Nat.factorial close must not carry sorryAx"
    );
    assert!(
        !contains_const(&proof, "trustedAy"),
        "Nat.factorial close must not carry a trusted-SMT axiom"
    );

    // The proof must type-check against the goal type under the kernel.
    let _cert = state
        .verify_proof(&goal, &proof)
        .expect("Nat.factorial close proof must kernel-verify against the goal");
}

#[test]
fn test_tactic_factorial_no_definition_does_not_falsely_close() {
    // SOUNDNESS guard: with NO `Nat.factorial` definition and no native reducer,
    // the kernel cannot reduce `Nat.factorial 5`, so the `rfl`/`reduce_eq` close
    // must FAIL — the evaluator's computed value alone must never close the goal.
    let mut env = Environment::with_prelude();
    env.ensure_native_reducers();
    let goal = nat_eq_goal(nat_factorial(Expr::nat_lit(5)), Expr::nat_lit(120));
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num_ext(&mut state);
    assert!(
        result.is_err(),
        "without a Nat.factorial definition the kernel close must fail, not succeed unsoundly"
    );
    assert!(!state.is_complete());
}
