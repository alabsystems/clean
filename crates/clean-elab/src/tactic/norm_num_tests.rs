// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for enhanced norm_num tactic.
//!
//! Part of #3082.

use super::tests::*;
use super::*;
use clean_kernel::level::Level;

// =========================================================================
// eval_int_expr unit tests
// =========================================================================

#[test]
fn test_eval_int_expr_nat_literal() {
    // A Nat literal 42 should evaluate to Some(42) as Int
    let expr = Expr::nat_lit(42);
    assert_eq!(norm_num::eval_int_expr(&expr), Some(42));
}

#[test]
fn test_eval_int_expr_zero() {
    let expr = Expr::nat_lit(0);
    assert_eq!(norm_num::eval_int_expr(&expr), Some(0));
}

#[test]
fn test_eval_int_expr_of_nat() {
    // Int.ofNat 5
    let expr = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(5));
}

#[test]
fn test_eval_int_expr_neg_succ() {
    // Int.negSucc 0 = -1
    let expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(0),
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(-1));
}

#[test]
fn test_eval_int_expr_neg_succ_larger() {
    // Int.negSucc 4 = -5
    let expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(4),
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(-5));
}

#[test]
fn test_eval_int_expr_add() {
    // Int.add (Int.ofNat 3) (Int.ofNat 4) = 7
    let lhs = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(4),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), lhs),
        rhs,
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(7));
}

#[test]
fn test_eval_int_expr_mul() {
    // Int.mul (Int.ofNat 3) (Int.negSucc 1) = 3 * (-2) = -6
    let lhs = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(1),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.mul"), vec![]), lhs),
        rhs,
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(-6));
}

#[test]
fn test_eval_int_expr_sub() {
    // Int.sub (Int.ofNat 10) (Int.ofNat 3) = 7
    let lhs = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(10),
    );
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.sub"), vec![]), lhs),
        rhs,
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(7));
}

#[test]
fn test_eval_int_expr_neg() {
    // Int.neg (Int.ofNat 5) = -5
    let inner = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let expr = Expr::app(Expr::const_(Name::from_string("Int.neg"), vec![]), inner);
    assert_eq!(norm_num::eval_int_expr(&expr), Some(-5));
}

#[test]
fn test_eval_int_expr_symbolic_returns_none() {
    // A free variable should return None
    let expr = Expr::const_(Name::from_string("x"), vec![]);
    assert_eq!(norm_num::eval_int_expr(&expr), None);
}

// =========================================================================
// Int.div / Int.mod: T-division parity with Lean 4 core.
//
// Before this fix `eval_int_expr` only knew `Int.add` / `Int.sub` /
// `Int.mul` / `Int.neg`, so `decide` / `norm_num` left ground Int
// division/modulo equalities to the SMT fallback even though clean-kernel
// has native `reduce_int_div` / `reduce_int_mod` reducers (matching Lean's
// T-division: truncation toward zero, remainder sign follows the dividend).
// =========================================================================

/// Build `Int.<op> (Int.negSucc 6) (Int.ofNat 3)`, i.e. `<op> (-7) 3`.
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
fn test_eval_int_expr_div_negative_truncates_toward_zero() {
    // Int.div is T-division: (-7) / 3 = -2 (truncation toward zero), not -3.
    assert_eq!(
        norm_num::eval_int_expr(&int_binop_neg7_3("Int.div")),
        Some(-2)
    );
}

#[test]
fn test_eval_int_expr_mod_negative_remainder_follows_dividend() {
    // Int.mod is T-remainder: (-7) % 3 = -1 (sign follows the dividend), not 2.
    assert_eq!(
        norm_num::eval_int_expr(&int_binop_neg7_3("Int.mod")),
        Some(-1)
    );
}

#[test]
fn test_eval_int_expr_div_positive() {
    // Positive operands: 7 / 2 = 3.
    let seven = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(7),
    );
    let two = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(2),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.div"), vec![]), seven),
        two,
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(3));
}

#[test]
fn test_eval_int_expr_div_by_zero_is_zero() {
    // Lean totalizes `a / 0 = 0`, matching clean-kernel's `reduce_int_div`.
    let five = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let zero = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(0),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.div"), vec![]), five),
        zero,
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(0));
}

#[test]
fn test_eval_int_expr_mod_by_zero_is_dividend() {
    // Lean totalizes `a % 0 = a`, matching clean-kernel's `reduce_int_mod`.
    let five = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let zero = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(0),
    );
    let expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Int.mod"), vec![]), five),
        zero,
    );
    assert_eq!(norm_num::eval_int_expr(&expr), Some(5));
}

#[test]
fn test_eval_int_expr_emod_returns_none() {
    // SOUNDNESS: Euclidean `Int.emod` has NO native kernel reducer, so a `rfl`
    // close after evaluating it would fail to type-check. It must stay
    // unrecognized here (mirrors why `Nat.lcm` is excluded from the evaluator).
    assert_eq!(norm_num::eval_int_expr(&int_binop_neg7_3("Int.emod")), None);
}

#[test]
fn test_eval_int_expr_ediv_returns_none() {
    // SOUNDNESS: Euclidean `Int.ediv` has no native kernel reducer either.
    assert_eq!(norm_num::eval_int_expr(&int_binop_neg7_3("Int.ediv")), None);
}

// =========================================================================
// eval_norm_num tactic tests
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
fn test_eval_norm_num_nat_add() {
    // Goal: 2 + 3 = 5
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let two = Expr::nat_lit(2);
    let three = Expr::nat_lit(3);
    let five = Expr::nat_lit(5);
    let add_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), two),
        three,
    );
    let goal = nat_eq_goal(add_expr, five);

    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close 2 + 3 = 5");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_eval_norm_num_nat_mul() {
    // Goal: 4 * 7 = 28
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let four = Expr::nat_lit(4);
    let seven = Expr::nat_lit(7);
    let twentyeight = Expr::nat_lit(28);
    let mul_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mul"), vec![]), four),
        seven,
    );
    let goal = nat_eq_goal(mul_expr, twentyeight);

    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close 4 * 7 = 28");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_eval_norm_num_nat_succ() {
    // Goal: Nat.succ (Nat.succ 0) = 2
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let zero = Expr::nat_lit(0);
    let succ_zero = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), zero);
    let succ_succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        succ_zero,
    );
    let two = Expr::nat_lit(2);
    let goal = nat_eq_goal(succ_succ_zero, two);

    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close succ(succ(0)) = 2");
    assert!(state.is_complete(), "proof state should be complete");
}

#[test]
fn test_eval_norm_num_nat_inequality_fails() {
    // Goal: 2 + 3 = 6 (should fail)
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let two = Expr::nat_lit(2);
    let three = Expr::nat_lit(3);
    let six = Expr::nat_lit(6);
    let add_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), two),
        three,
    );
    let goal = nat_eq_goal(add_expr, six);

    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num(&mut state);
    assert!(result.is_err(), "norm_num should fail on 2 + 3 = 6");
}

#[test]
fn test_eval_norm_num_nested_nat() {
    // Goal: (2 + 3) * 4 = 20
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let two = Expr::nat_lit(2);
    let three = Expr::nat_lit(3);
    let four = Expr::nat_lit(4);
    let twenty = Expr::nat_lit(20);
    let add_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), two),
        three,
    );
    let mul_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mul"), vec![]), add_expr),
        four,
    );
    let goal = nat_eq_goal(mul_expr, twenty);

    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close (2+3)*4 = 20");
    assert!(state.is_complete(), "proof state should be complete");
}

// =========================================================================
// Ne (disequality) tactic tests — Lean parity.
//
// Lean 4's `norm_num` closes ground disequalities such as `(5 : Nat) ≠ 3`.
// Before this fix, `eval_norm_num` returned `ArithmeticFailed` for any `Ne`
// goal. The proof now goes through the noConfusion disequality builder, which
// produces a kernel-checkable, axiom-free term (`Ne a b` is the reducible
// definition `Eq a b → False`).
// =========================================================================

/// Helper: build `@Ne.{1} Nat lhs rhs`.
fn nat_ne_goal(lhs: Expr, rhs: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            lhs,
        ),
        rhs,
    )
}

#[test]
fn test_eval_norm_num_nat_disequality_closes() {
    // Goal: (5 : Nat) ≠ 3 — Lean's norm_num closes this; Clean used to reject it.
    let env = Environment::with_prelude();
    let goal = nat_ne_goal(Expr::nat_lit(5), Expr::nat_lit(3));
    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close 5 ≠ 3");
    assert!(state.is_complete(), "disequality goal should be closed");
}

#[test]
fn test_eval_norm_num_nat_disequality_zero_succ_closes() {
    // Goal: (0 : Nat) ≠ 4 — zero/succ constructor discrimination.
    let env = Environment::with_prelude();
    let goal = nat_ne_goal(Expr::nat_lit(0), Expr::nat_lit(4));
    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close 0 ≠ 4");
    assert!(state.is_complete(), "disequality goal should be closed");
}

#[test]
fn test_eval_norm_num_nat_disequality_no_trusted_axioms() {
    // The disequality proof must stay on the kernel noConfusion path with no
    // trusted/domain-specific axioms (mirrors decide_eq's soundness pin).
    let env = Environment::with_prelude();
    let goal = nat_ne_goal(Expr::nat_lit(7), Expr::nat_lit(2));
    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close 7 ≠ 2");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "disequality proof must not introduce trusted axioms",
    );
}

#[test]
fn test_eval_norm_num_nat_false_disequality_rejected() {
    // Goal: (3 : Nat) ≠ 3 is FALSE — norm_num must not close it.
    let env = Environment::with_prelude();
    let goal = nat_ne_goal(Expr::nat_lit(3), Expr::nat_lit(3));
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num(&mut state);
    assert!(result.is_err(), "norm_num must reject the false goal 3 ≠ 3");
    assert!(
        !state.is_complete(),
        "false disequality goal must remain open",
    );
}

#[test]
fn test_eval_decide_nat_disequality_closes() {
    // Lean's `decide` also closes ground disequalities; the kernel `decide`
    // path used to fall through to SMT and report a spurious counterexample.
    let env = Environment::with_prelude();
    let goal = nat_ne_goal(Expr::nat_lit(5), Expr::nat_lit(3));
    let mut state = ProofState::new(env, goal);
    super::decide::eval_decide(&mut state).expect("decide should close 5 ≠ 3");
    assert!(state.is_complete(), "disequality goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "decide disequality proof must not introduce trusted axioms",
    );
}

// =========================================================================
// Nat.gcd tactic-level parity with Lean 4 (tactic-divergence-12).
//
// Lean's `norm_num` / `decide` evaluate ground `Nat.gcd`; the kernel reduces
// it natively (`reduce_nat`'s `nat_gcd`). Before this fix, `eval_nat_expr`
// returned `None` for `Nat.gcd`, so the `norm_num` equality close fell through
// to the `reduce_eq` kernel path (which already worked) but every
// *comparison* over a `Nat.gcd` term went unrecognized: `try_eval_comparison`
// returned `None` and the constructive `Nat.le` witness builder had no operand
// values. The equality test is a soundness pin (the close is an `Eq.refl`
// whose def-eq check drives the native `reduce_nat` gcd reducer); the
// comparison tests are load-bearing on the new evaluator arm.
// =========================================================================

/// Build `@LE.le.{0} Nat instLENat lhs rhs`.
fn nat_le_goal(lhs: Expr, rhs: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    nat,
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `@LT.lt.{0} Nat instLTNat lhs rhs`.
fn nat_lt_goal(lhs: Expr, rhs: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    nat,
                ),
                Expr::const_(Name::from_string("instLTNat"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// Build `Nat.gcd a b`.
fn nat_gcd(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.gcd"), vec![]), a),
        b,
    )
}

#[test]
fn test_eval_norm_num_nat_gcd_equality_closes() {
    // Goal: Nat.gcd 12 18 = 6. Lean's norm_num closes it; the close reduces
    // through the kernel `reduce_eq` path, an `Eq.refl` whose def-eq check
    // drives the native gcd reducer. Kept as a soundness pin.
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let goal = nat_eq_goal(
        nat_gcd(Expr::nat_lit(12), Expr::nat_lit(18)),
        Expr::nat_lit(6),
    );
    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close gcd 12 18 = 6");
    assert!(state.is_complete(), "gcd equality goal should be closed");
}

#[test]
fn test_eval_norm_num_nat_gcd_wrong_value_rejected() {
    // Goal: Nat.gcd 12 18 = 5 is FALSE (the real gcd is 6).
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let goal = nat_eq_goal(
        nat_gcd(Expr::nat_lit(12), Expr::nat_lit(18)),
        Expr::nat_lit(5),
    );
    let mut state = ProofState::new(env, goal);
    let result = eval_norm_num(&mut state);
    assert!(result.is_err(), "norm_num must reject gcd 12 18 = 5");
    assert!(!state.is_complete(), "false gcd equality must remain open");
}

#[test]
fn test_eval_decide_nat_gcd_le_comparison_closes() {
    // Goal: Nat.gcd 12 18 <= 6 (true; gcd = 6). Lean's `decide` closes it.
    // Without the gcd arm in `eval_nat_expr`, `try_eval_comparison` returned
    // None and the constructive `Nat.le` witness builder had no value to work
    // with, so the goal fell through to SMT and stayed open.
    let env = Environment::with_prelude();
    let goal = nat_le_goal(
        nat_gcd(Expr::nat_lit(12), Expr::nat_lit(18)),
        Expr::nat_lit(6),
    );
    let mut state = ProofState::new(env, goal);
    super::decide::eval_decide(&mut state).expect("decide should close gcd 12 18 <= 6");
    assert!(state.is_complete(), "gcd comparison goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "gcd comparison proof must not introduce trusted axioms",
    );
}

#[test]
fn test_eval_decide_nat_gcd_lt_false_rejected() {
    // Goal: Nat.gcd 12 18 < 6 is FALSE (gcd = 6, not < 6). `decide` must reject.
    let env = Environment::with_prelude();
    let goal = nat_lt_goal(
        nat_gcd(Expr::nat_lit(12), Expr::nat_lit(18)),
        Expr::nat_lit(6),
    );
    let mut state = ProofState::new(env, goal);
    let result = super::decide::eval_decide(&mut state);
    assert!(
        result.is_err(),
        "decide must reject the false goal gcd 12 18 < 6"
    );
    assert!(
        !state.is_complete(),
        "false gcd comparison must remain open"
    );
}

// =========================================================================
// Int.div / Int.mod tactic-level parity with Lean 4.
//
// The fix lives in `eval_int_expr`. `eval_decide`'s Int-equality fast path
// has no kernel-proof fallback, so a missing `Int.div` evaluation forced
// the SMT fallback and left the goal open — the `decide` tests below are
// load-bearing on the new arms. The `norm_num` *equality* close already
// reduced through the kernel `reduce_eq` path; those tests are kept as a
// soundness pin (the close is an `Eq.refl` whose def-eq check drives the
// native `reduce_int_div` / `reduce_int_mod` reducer).
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
fn test_eval_decide_int_div_negative_closes() {
    // Goal: (-7 : Int) / 3 = -2 (T-division). Lean's `decide` closes it. Without
    // the `Int.div` arm in `eval_int_expr`, `eval_decide`'s Int-equality fast
    // path declined and the goal was left open (SMT fallback).
    let env = Environment::with_prelude();
    let lhs = int_binop_neg7_3("Int.div");
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(1),
    ); // Int.negSucc 1 = -2
    let goal = int_eq_goal(lhs, rhs);
    let mut state = ProofState::new(env, goal);
    super::decide::eval_decide(&mut state).expect("decide should close (-7)/3 = -2");
    assert!(
        state.is_complete(),
        "Int.div equality goal should be closed"
    );
}

#[test]
fn test_eval_decide_int_div_wrong_value_rejected() {
    // Goal: (-7 : Int) / 3 = -3 is FALSE (the real T-division value is -2).
    let env = Environment::with_prelude();
    let lhs = int_binop_neg7_3("Int.div");
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(2),
    ); // Int.negSucc 2 = -3
    let goal = int_eq_goal(lhs, rhs);
    let mut state = ProofState::new(env, goal);
    let result = super::decide::eval_decide(&mut state);
    assert!(
        result.is_err(),
        "decide must reject the false goal (-7)/3 = -3"
    );
    assert!(
        !state.is_complete(),
        "false Int.div equality goal must remain open"
    );
}

#[test]
fn test_eval_norm_num_int_div_negative_closes() {
    // Goal: (-7 : Int) / 3 = -2 (T-division). Lean's `norm_num` closes it. The
    // close reduces through the kernel `reduce_eq` path (an `Eq.refl` whose
    // def-eq check drives the native `reduce_int_div` reducer); kept here as a
    // tactic-level parity pin alongside the `decide` divergence above.
    let env = Environment::with_prelude();
    let lhs = int_binop_neg7_3("Int.div");
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(1),
    ); // Int.negSucc 1 = -2
    let goal = int_eq_goal(lhs, rhs);
    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close (-7)/3 = -2");
    assert!(
        state.is_complete(),
        "Int.div equality goal should be closed"
    );
}

#[test]
fn test_eval_norm_num_int_mod_negative_closes() {
    // Goal: (-7 : Int) % 3 = -1 (T-remainder, sign follows dividend).
    let env = Environment::with_prelude();
    let lhs = int_binop_neg7_3("Int.mod");
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(0),
    ); // Int.negSucc 0 = -1
    let goal = int_eq_goal(lhs, rhs);
    let mut state = ProofState::new(env, goal);
    eval_norm_num(&mut state).expect("norm_num should close (-7)%3 = -1");
    assert!(
        state.is_complete(),
        "Int.mod equality goal should be closed"
    );
}

#[test]
fn test_eval_norm_num_int_div_proof_is_sorry_free_and_kernel_checks() {
    // SOUNDNESS guard: closing `(-7 : Int) / 3 = -2` must produce a proof that
    // is `sorryAx`-free, carries no trusted/domain axioms, and kernel-rechecks
    // against the goal type (the def-eq check unfolds via the native
    // `reduce_int_div` reducer).
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

    let env = Environment::with_prelude();
    let lhs = int_binop_neg7_3("Int.div");
    let rhs = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(1),
    ); // -2
    let goal_expr = int_eq_goal(lhs, rhs);
    let mut state = ProofState::new(env, goal_expr);
    let goal = state
        .current_goal()
        .cloned()
        .expect("state should have a goal");
    eval_norm_num(&mut state).expect("norm_num should close (-7)/3 = -2");
    assert!(state.is_complete());
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "Int.div close must not introduce trusted axioms",
    );

    let proof = state
        .closed_proof()
        .expect("a completed proof state must yield a closed proof term");
    assert!(
        !contains_const(&proof, "sorryAx"),
        "Int.div close must not carry sorryAx"
    );

    let inferred = state
        .infer_type(&goal, &proof)
        .expect("Int.div close proof must have an inferable type");
    assert!(
        state.is_def_eq(&goal, &inferred, &goal.target),
        "Int.div close proof type {inferred:?} must be def-eq to the goal {:?}",
        goal.target
    );
}
