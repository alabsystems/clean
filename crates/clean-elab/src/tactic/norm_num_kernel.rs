// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verified norm_num theorem generation.
//!
//! Evaluates numeric expressions to normal form and constructs
//! `Declaration::Theorem` entries verified by the kernel type checker
//! via `add_decl()`. The proof strategy is:
//!
//! 1. Parse the goal as an equality `lhs = rhs` over Nat, Int, or Rat.
//! 2. Evaluate both sides to concrete values using the evaluators from
//!    `nat_expr_eval`, `norm_num`, and `norm_num_ext`.
//! 3. If both sides reduce to the same value `v`, construct a proof term
//!    `@Eq.refl α v`. The kernel verifies that `lhs` and `rhs` are both
//!    definitionally equal to `v` via its WHNF reduction engine.
//! 4. Wrap the proof in a `Declaration::Theorem` and register it via
//!    `env.add_decl()` for full kernel verification.
//!
//! This produces genuine kernel proof output — not axiom wrappers or
//! sorry-based stubs.
//!
//! Part of #3369.

use clean_kernel::env::Environment;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Declaration, EqProofBuilder, Expr};

use super::equality::match_equality;
use super::nat_expr_eval::eval_nat_expr;
use super::norm_num::eval_int_expr;
use super::norm_num_ext::{eval_extended, NormNumExtConfig};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from kernel-verified norm_num theorem generation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum NormNumKernelError {
    /// The goal is not an equality.
    #[error("goal is not an equality: {0}")]
    NotEquality(String),

    /// Could not evaluate one or both sides to a concrete value.
    #[error("could not evaluate expression to a concrete value: {0}")]
    EvalFailed(String),

    /// Both sides evaluate to different values.
    #[error("sides evaluate to different values: {lhs} != {rhs}")]
    Disequality { lhs: String, rhs: String },

    /// The kernel type checker rejected the generated proof.
    #[error("kernel rejected the proof: {0}")]
    KernelRejected(String),
}

// ---------------------------------------------------------------------------
// Numeric type classification
// ---------------------------------------------------------------------------

/// The numeric type of an expression, determined during evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NumericType {
    Nat,
    Int,
    Extended,
}

/// Result of evaluating both sides of a numeric equality.
#[derive(Debug)]
pub(crate) struct EvalResult {
    /// The numeric type used for evaluation.
    pub(crate) num_type: NumericType,
    /// The concrete value both sides reduce to (as i128 for uniformity).
    pub(crate) value: i128,
}

/// Try to evaluate both sides of an equality and return the common value.
///
/// Tries evaluators in order: Nat (u64), Int (i64), Extended (i128).
/// Returns the first evaluator where both sides produce the same value.
///
/// REQUIRES: `lhs` and `rhs` are well-formed kernel expressions
/// ENSURES: On Some, both sides evaluate to the same concrete value
/// ENSURES: On None, no evaluator could evaluate both sides to equal values
pub(crate) fn try_eval_equality(lhs: &Expr, rhs: &Expr) -> Option<EvalResult> {
    // Try Nat evaluation first (most common case, cheapest)
    if let (Some(l), Some(r)) = (eval_nat_expr(lhs), eval_nat_expr(rhs)) {
        if l == r {
            return Some(EvalResult {
                num_type: NumericType::Nat,
                value: i128::from(l),
            });
        }
        return None; // Both evaluated but to different values
    }

    // Try Int evaluation
    if let (Some(l), Some(r)) = (eval_int_expr(lhs), eval_int_expr(rhs)) {
        if l == r {
            return Some(EvalResult {
                num_type: NumericType::Int,
                value: i128::from(l),
            });
        }
        return None;
    }

    // Try extended evaluation (power, modular, bitwise, rational)
    let config = NormNumExtConfig::default();
    if let (Some(l), Some(r)) = (
        eval_extended(lhs, &config, 0),
        eval_extended(rhs, &config, 0),
    ) {
        if l == r {
            return Some(EvalResult {
                num_type: NumericType::Extended,
                value: l,
            });
        }
        return None;
    }

    None
}

// ---------------------------------------------------------------------------
// Proof term construction
// ---------------------------------------------------------------------------

/// Build a concrete Nat expression from a u64 value.
///
/// ENSURES: The returned expression is `Expr::nat_lit(n)`.
fn nat_value_expr(n: u64) -> Expr {
    Expr::nat_lit(n)
}

/// Build a concrete Int expression from an i64 value.
///
/// For non-negative values, produces `Int.ofNat n`.
/// For negative values, produces `Int.negSucc (|n| - 1)`.
///
/// ENSURES: The returned expression evaluates to `n` under `eval_int_expr`.
fn int_value_expr(n: i64) -> Expr {
    if n >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n as u64),
        )
    } else {
        // Int.negSucc k represents -(k+1)
        let k = ((-n) - 1) as u64;
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(k),
        )
    }
}

/// Build a concrete value expression for the given numeric type and value.
///
/// REQUIRES: `value` fits within the range of the target numeric type
/// ENSURES: The returned expression evaluates to `value` under the
///          corresponding evaluator
fn value_expr(num_type: NumericType, value: i128) -> Expr {
    match num_type {
        NumericType::Nat => nat_value_expr(value as u64),
        NumericType::Int => int_value_expr(value as i64),
        // For extended, we fall back to Nat representation if non-negative,
        // otherwise Int representation.
        NumericType::Extended => {
            if value >= 0 {
                nat_value_expr(value as u64)
            } else {
                int_value_expr(value as i64)
            }
        }
    }
}

/// Build a proof of `lhs = rhs` using Eq.refl on the evaluated value.
///
/// The proof term is `@Eq.refl.{u} α v` where `v` is the normal form
/// both sides reduce to. The kernel's definitional equality checker
/// verifies that `lhs ≡ v` and `rhs ≡ v`.
///
/// REQUIRES: `eval_result` was produced by `try_eval_equality` for this lhs/rhs
/// ENSURES: The returned expression is a valid proof of `@Eq α lhs rhs`
///          (assuming the kernel can verify the reductions)
fn build_eq_refl_proof(alpha: &Expr, eval_result: &EvalResult, u: Level) -> Expr {
    let v = value_expr(eval_result.num_type, eval_result.value);
    EqProofBuilder::mk_eq_refl(u, alpha.clone(), v)
}

// ---------------------------------------------------------------------------
// Kernel theorem generation
// ---------------------------------------------------------------------------

/// Generate a kernel-verified norm_num proof for an equality goal.
///
/// Given a goal expression of the form `lhs = rhs`, evaluates both sides
/// to normal form and constructs a proof term verified by the kernel.
///
/// Returns the proof term on success.
///
/// REQUIRES: `goal` is a well-formed equality expression `@Eq α lhs rhs`
/// ENSURES: On Ok, the returned expression is a valid proof of `goal`
/// ENSURES: On Err(NotEquality), `goal` is not an equality
/// ENSURES: On Err(EvalFailed), one or both sides cannot be evaluated
/// ENSURES: On Err(Disequality), both sides evaluate to different values
///
/// Part of #3369.
pub(crate) fn norm_num_kernel_proof(goal: &Expr) -> Result<Expr, NormNumKernelError> {
    // Step 1: Parse as equality
    let (alpha, lhs, rhs, levels) =
        match_equality(goal).map_err(|e| NormNumKernelError::NotEquality(format!("{e}")))?;

    let u = levels
        .first()
        .cloned()
        .unwrap_or_else(|| Level::succ(Level::zero()));

    // Step 2: Evaluate both sides
    let eval_result = try_eval_equality(&lhs, &rhs).ok_or_else(|| {
        // Determine which side failed or if they disagree
        let l_nat = eval_nat_expr(&lhs);
        let r_nat = eval_nat_expr(&rhs);
        let l_int = eval_int_expr(&lhs);
        let r_int = eval_int_expr(&rhs);
        let config = NormNumExtConfig::default();
        let l_ext = eval_extended(&lhs, &config, 0);
        let r_ext = eval_extended(&rhs, &config, 0);

        // Check if both sides evaluate but to different values
        if let (Some(l), Some(r)) = (l_nat, r_nat) {
            return NormNumKernelError::Disequality {
                lhs: l.to_string(),
                rhs: r.to_string(),
            };
        }
        if let (Some(l), Some(r)) = (l_int, r_int) {
            return NormNumKernelError::Disequality {
                lhs: l.to_string(),
                rhs: r.to_string(),
            };
        }
        if let (Some(l), Some(r)) = (l_ext, r_ext) {
            return NormNumKernelError::Disequality {
                lhs: l.to_string(),
                rhs: r.to_string(),
            };
        }

        NormNumKernelError::EvalFailed(
            "one or both sides are not ground numeric expressions".into(),
        )
    })?;

    // Step 3: Build proof term
    Ok(build_eq_refl_proof(&alpha, &eval_result, u))
}

/// Generate a kernel-verified norm_num theorem and register it.
///
/// Takes an environment, a theorem name, and a goal expression of the form
/// `lhs = rhs`. Evaluates both sides, constructs a proof, and registers
/// the result as a `Declaration::Theorem` verified by `add_decl()`.
///
/// REQUIRES: `env` contains all necessary declarations (Nat, Eq, etc.)
/// REQUIRES: `goal` is a well-formed equality expression
/// REQUIRES: `name` is not already declared in `env`
/// ENSURES: On Ok, a `Declaration::Theorem` with the given name is added
///          to `env` and verified by the kernel type checker
/// ENSURES: On Err, `env` is unchanged
///
/// Part of #3369.
pub fn norm_num_kernel_theorem(
    env: &mut Environment,
    name: &str,
    goal: &Expr,
) -> Result<Expr, NormNumKernelError> {
    // Generate the proof term
    let proof = norm_num_kernel_proof(goal)?;

    // Register as Declaration::Theorem
    let thm_name = Name::from_string(name);
    let decl = Declaration::Theorem {
        name: thm_name,
        level_params: vec![],
        type_: goal.clone(),
        value: proof.clone(),
    };

    env.add_decl(decl)
        .map_err(|e| NormNumKernelError::KernelRejected(format!("{e}")))?;

    Ok(proof)
}

/// Generate a kernel-verified norm_num proof without environment registration.
///
/// Like `norm_num_kernel_theorem` but returns the proof term and goal type
/// without registering in the environment. Useful for producing proof terms
/// for inline use (e.g., inside a tactic proof state).
///
/// Part of #3369.
pub fn norm_num_kernel_proof_only(goal: &Expr) -> Result<(Expr, Expr), NormNumKernelError> {
    let proof = norm_num_kernel_proof(goal)?;
    Ok((proof, goal.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::Environment;
    use clean_kernel::level::Level;
    use clean_kernel::ExprKind;

    // =========================================================================
    // Helpers
    // =========================================================================

    /// Build `@Eq.{1} Nat lhs rhs`.
    fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
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

    /// Build `@Eq.{1} Int lhs rhs`.
    fn int_eq(lhs: Expr, rhs: Expr) -> Expr {
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

    /// Build `Nat.add a b`.
    fn nat_add(a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), a),
            b,
        )
    }

    /// Build `Nat.mul a b`.
    fn nat_mul(a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Nat.mul"), vec![]), a),
            b,
        )
    }

    /// Build `Nat.pow a b`.
    fn nat_pow(a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Nat.pow"), vec![]), a),
            b,
        )
    }

    /// Build `Int.ofNat n`.
    fn int_ofnat(n: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    }

    /// Build `Int.add a b`.
    fn int_add(a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Int.add"), vec![]), a),
            b,
        )
    }

    /// Build `Int.negSucc n` (represents -(n+1)).
    fn int_neg_succ(n: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n),
        )
    }

    // =========================================================================
    // Test: try_eval_equality
    // =========================================================================

    #[test]
    fn test_eval_equality_nat_add() {
        // 2 + 3 and 5 should both evaluate to 5
        let lhs = nat_add(Expr::nat_lit(2), Expr::nat_lit(3));
        let rhs = Expr::nat_lit(5);
        let result = try_eval_equality(&lhs, &rhs);
        assert!(result.is_some(), "2+3 should evaluate equal to 5");
        let result = result.unwrap();
        assert_eq!(result.num_type, NumericType::Nat);
        assert_eq!(result.value, 5);
    }

    #[test]
    fn test_eval_equality_nat_mul() {
        // 4 * 7 and 28
        let lhs = nat_mul(Expr::nat_lit(4), Expr::nat_lit(7));
        let rhs = Expr::nat_lit(28);
        let result = try_eval_equality(&lhs, &rhs);
        assert!(result.is_some());
        assert_eq!(result.unwrap().value, 28);
    }

    #[test]
    fn test_eval_equality_nat_disequality() {
        // 2 + 3 and 6 should not be equal
        let lhs = nat_add(Expr::nat_lit(2), Expr::nat_lit(3));
        let rhs = Expr::nat_lit(6);
        assert!(try_eval_equality(&lhs, &rhs).is_none());
    }

    #[test]
    fn test_eval_equality_int_add() {
        // Int.ofNat(3) + Int.ofNat(4) and Int.ofNat(7)
        let lhs = int_add(int_ofnat(3), int_ofnat(4));
        let rhs = int_ofnat(7);
        let result = try_eval_equality(&lhs, &rhs);
        assert!(result.is_some());
        assert_eq!(result.unwrap().value, 7);
    }

    #[test]
    fn test_eval_equality_extended_pow() {
        // 2^10 and 1024
        let lhs = nat_pow(Expr::nat_lit(2), Expr::nat_lit(10));
        let rhs = Expr::nat_lit(1024);
        let result = try_eval_equality(&lhs, &rhs);
        assert!(result.is_some());
        assert_eq!(result.unwrap().value, 1024);
    }

    // =========================================================================
    // Test: norm_num_kernel_proof
    // =========================================================================

    #[test]
    fn test_kernel_proof_nat_add() {
        // Goal: 2 + 3 = 5
        let goal = nat_eq(
            nat_add(Expr::nat_lit(2), Expr::nat_lit(3)),
            Expr::nat_lit(5),
        );
        let result = norm_num_kernel_proof(&goal);
        assert!(
            result.is_ok(),
            "kernel proof should succeed for 2+3=5, got: {result:?}"
        );
        // The proof should be an Eq.refl application
        let proof = result.unwrap();
        // Eq.refl is a const applied to args — check it is an application
        assert!(
            matches!(proof.kind(), ExprKind::App(..)),
            "proof should be an application (Eq.refl)"
        );
    }

    #[test]
    fn test_kernel_proof_nat_mul() {
        // Goal: 6 * 7 = 42
        let goal = nat_eq(
            nat_mul(Expr::nat_lit(6), Expr::nat_lit(7)),
            Expr::nat_lit(42),
        );
        let result = norm_num_kernel_proof(&goal);
        assert!(result.is_ok(), "kernel proof should succeed for 6*7=42");
    }

    #[test]
    fn test_kernel_proof_nested_nat() {
        // Goal: (2 + 3) * 4 = 20
        let goal = nat_eq(
            nat_mul(
                nat_add(Expr::nat_lit(2), Expr::nat_lit(3)),
                Expr::nat_lit(4),
            ),
            Expr::nat_lit(20),
        );
        let result = norm_num_kernel_proof(&goal);
        assert!(result.is_ok(), "kernel proof should succeed for (2+3)*4=20");
    }

    #[test]
    fn test_kernel_proof_disequality_fails() {
        // Goal: 2 + 3 = 6 (should fail)
        let goal = nat_eq(
            nat_add(Expr::nat_lit(2), Expr::nat_lit(3)),
            Expr::nat_lit(6),
        );
        let result = norm_num_kernel_proof(&goal);
        assert!(result.is_err(), "kernel proof should fail for 2+3=6");
        assert!(
            matches!(result.unwrap_err(), NormNumKernelError::Disequality { .. }),
            "error should be Disequality"
        );
    }

    #[test]
    fn test_kernel_proof_int_equality() {
        // Goal: Int.ofNat(3) + Int.ofNat(4) = Int.ofNat(7)
        let goal = int_eq(int_add(int_ofnat(3), int_ofnat(4)), int_ofnat(7));
        let result = norm_num_kernel_proof(&goal);
        assert!(
            result.is_ok(),
            "kernel proof should succeed for Int(3)+Int(4)=Int(7), got: {result:?}"
        );
    }

    #[test]
    fn test_kernel_proof_non_equality_fails() {
        // A non-equality expression should fail
        let goal = Expr::const_(Name::from_string("True"), vec![]);
        let result = norm_num_kernel_proof(&goal);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            NormNumKernelError::NotEquality(_)
        ));
    }

    // =========================================================================
    // Test: norm_num_kernel_theorem (kernel verification)
    // =========================================================================

    #[test]
    fn test_kernel_theorem_nat_add_verified() {
        // Register 2 + 3 = 5 as a kernel theorem
        let mut env = Environment::with_prelude();
        let goal = nat_eq(
            nat_add(Expr::nat_lit(2), Expr::nat_lit(3)),
            Expr::nat_lit(5),
        );

        let result = norm_num_kernel_theorem(&mut env, "norm_num_2_plus_3", &goal);
        assert!(
            result.is_ok(),
            "norm_num_kernel_theorem should succeed for 2+3=5, got: {result:?}"
        );

        // Verify the theorem is registered in the environment
        let thm_name = Name::from_string("norm_num_2_plus_3");
        let const_info = env.get_const(&thm_name);
        assert!(
            const_info.is_some(),
            "theorem should be registered in the environment"
        );
        // It should have a proof value (Declaration::Theorem, not Axiom)
        let info = const_info.unwrap();
        assert!(
            info.value.is_some(),
            "Declaration::Theorem should have a proof value"
        );
    }

    #[test]
    fn test_kernel_theorem_nat_mul_verified() {
        // Register 7 * 8 = 56 as a kernel theorem
        let mut env = Environment::with_prelude();
        let goal = nat_eq(
            nat_mul(Expr::nat_lit(7), Expr::nat_lit(8)),
            Expr::nat_lit(56),
        );

        let result = norm_num_kernel_theorem(&mut env, "norm_num_7_times_8", &goal);
        assert!(
            result.is_ok(),
            "norm_num_kernel_theorem should succeed for 7*8=56, got: {result:?}"
        );
    }

    #[test]
    fn test_kernel_theorem_nested_expression() {
        // Register (3 + 4) * (2 + 5) = 49 as a kernel theorem
        let mut env = Environment::with_prelude();
        let goal = nat_eq(
            nat_mul(
                nat_add(Expr::nat_lit(3), Expr::nat_lit(4)),
                nat_add(Expr::nat_lit(2), Expr::nat_lit(5)),
            ),
            Expr::nat_lit(49),
        );

        let result = norm_num_kernel_theorem(&mut env, "norm_num_nested", &goal);
        assert!(
            result.is_ok(),
            "norm_num_kernel_theorem should succeed for (3+4)*(2+5)=49, got: {result:?}"
        );
    }

    #[test]
    fn test_kernel_theorem_disequality_rejected() {
        // 2 + 2 = 5 should be rejected
        let mut env = Environment::with_prelude();
        let goal = nat_eq(
            nat_add(Expr::nat_lit(2), Expr::nat_lit(2)),
            Expr::nat_lit(5),
        );

        let result = norm_num_kernel_theorem(&mut env, "should_fail", &goal);
        assert!(result.is_err(), "2+2=5 should be rejected");
    }

    #[test]
    fn test_kernel_theorem_duplicate_name_rejected() {
        let mut env = Environment::with_prelude();
        let goal = nat_eq(
            nat_add(Expr::nat_lit(1), Expr::nat_lit(1)),
            Expr::nat_lit(2),
        );

        // First should succeed
        let r1 = norm_num_kernel_theorem(&mut env, "dup_norm_num", &goal);
        assert!(r1.is_ok(), "first registration should succeed");

        // Duplicate name should fail
        let r2 = norm_num_kernel_theorem(&mut env, "dup_norm_num", &goal);
        assert!(r2.is_err(), "duplicate name should be rejected");
        assert!(
            matches!(r2.unwrap_err(), NormNumKernelError::KernelRejected(_)),
            "error should be KernelRejected"
        );
    }

    #[test]
    fn test_kernel_theorem_no_sorry() {
        // The generated proof must not contain sorry or trustedArith
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
        let goal = nat_eq(
            nat_add(Expr::nat_lit(10), Expr::nat_lit(20)),
            Expr::nat_lit(30),
        );

        let proof = norm_num_kernel_theorem(&mut env, "soundness_check", &goal)
            .expect("should produce a proof");

        assert!(
            !contains_const(&proof, "sorry"),
            "proof must not contain sorry"
        );
        assert!(
            !contains_const(&proof, "trustedArith"),
            "proof must not contain trustedArith"
        );
    }

    #[test]
    fn test_kernel_theorem_is_genuine_theorem() {
        // Verify that the registered declaration is a Theorem (not Axiom)
        let mut env = Environment::with_prelude();
        let goal = nat_eq(
            nat_mul(Expr::nat_lit(5), Expr::nat_lit(5)),
            Expr::nat_lit(25),
        );

        let _ = norm_num_kernel_theorem(&mut env, "genuine_thm_check", &goal)
            .expect("should produce a theorem");

        let info = env
            .get_const(&Name::from_string("genuine_thm_check"))
            .expect("theorem should be registered");
        assert!(
            info.value.is_some(),
            "must be a Theorem with proof value, not an Axiom"
        );
    }

    #[test]
    fn test_kernel_proof_only_returns_pair() {
        let goal = nat_eq(
            nat_add(Expr::nat_lit(100), Expr::nat_lit(200)),
            Expr::nat_lit(300),
        );

        let result = norm_num_kernel_proof_only(&goal);
        assert!(result.is_ok(), "proof_only should succeed");
        let (proof, ty) = result.unwrap();
        assert!(
            matches!(proof.kind(), ExprKind::App(..)),
            "proof should be an application"
        );
        assert!(
            matches!(ty.kind(), ExprKind::App(..)),
            "type should be an equality application"
        );
    }

    // =========================================================================
    // Test: Large numbers
    // =========================================================================

    #[test]
    fn test_kernel_theorem_large_nat() {
        let mut env = Environment::with_prelude();
        // 999 + 1 = 1000
        let goal = nat_eq(
            nat_add(Expr::nat_lit(999), Expr::nat_lit(1)),
            Expr::nat_lit(1000),
        );
        let result = norm_num_kernel_theorem(&mut env, "large_nat_thm", &goal);
        assert!(
            result.is_ok(),
            "kernel theorem should succeed for 999+1=1000, got: {result:?}"
        );
    }

    #[test]
    fn test_kernel_theorem_zero_identity() {
        let mut env = Environment::with_prelude();
        // 0 + 0 = 0
        let goal = nat_eq(
            nat_add(Expr::nat_lit(0), Expr::nat_lit(0)),
            Expr::nat_lit(0),
        );
        let result = norm_num_kernel_theorem(&mut env, "zero_identity", &goal);
        assert!(
            result.is_ok(),
            "kernel theorem should succeed for 0+0=0, got: {result:?}"
        );
    }

    // =========================================================================
    // Test: Int kernel theorems
    // =========================================================================

    #[test]
    fn test_kernel_theorem_int_add_verified() {
        let mut env = Environment::with_prelude();
        // init_int_ord_lemmas transitively registers Int.add via init_int_arith
        env.init_int_ord_lemmas()
            .expect("Int ordering lemmas should initialize");
        // Int.ofNat(5) + Int.ofNat(10) = Int.ofNat(15)
        let goal = int_eq(int_add(int_ofnat(5), int_ofnat(10)), int_ofnat(15));
        let result = norm_num_kernel_theorem(&mut env, "int_add_thm", &goal);
        assert!(
            result.is_ok(),
            "kernel theorem should succeed for Int(5)+Int(10)=Int(15), got: {result:?}"
        );
    }

    #[test]
    fn test_kernel_theorem_int_negative() {
        let mut env = Environment::with_prelude();
        env.init_int_ord_lemmas()
            .expect("Int ordering lemmas should initialize");
        // Int.negSucc(0) + Int.ofNat(2) = Int.ofNat(1)
        // i.e., (-1) + 2 = 1
        let goal = int_eq(int_add(int_neg_succ(0), int_ofnat(2)), int_ofnat(1));
        let result = norm_num_kernel_theorem(&mut env, "int_neg_thm", &goal);
        assert!(
            result.is_ok(),
            "kernel theorem should succeed for (-1)+2=1, got: {result:?}"
        );
    }

    // =========================================================================
    // Test: Power (extended)
    // =========================================================================

    #[test]
    fn test_kernel_theorem_nat_pow() {
        let mut env = Environment::with_prelude();
        // 2^8 = 256
        let goal = nat_eq(
            nat_pow(Expr::nat_lit(2), Expr::nat_lit(8)),
            Expr::nat_lit(256),
        );
        let result = norm_num_kernel_theorem(&mut env, "pow_thm", &goal);
        assert!(
            result.is_ok(),
            "kernel theorem should succeed for 2^8=256, got: {result:?}"
        );
    }

    // =========================================================================
    // Test: value_expr round-trip
    // =========================================================================

    #[test]
    fn test_value_expr_nat() {
        let expr = value_expr(NumericType::Nat, 42);
        assert_eq!(eval_nat_expr(&expr), Some(42));
    }

    #[test]
    fn test_value_expr_int_positive() {
        let expr = value_expr(NumericType::Int, 10);
        assert_eq!(eval_int_expr(&expr), Some(10));
    }

    #[test]
    fn test_value_expr_int_negative() {
        let expr = value_expr(NumericType::Int, -5);
        assert_eq!(eval_int_expr(&expr), Some(-5));
    }

    #[test]
    fn test_value_expr_extended_positive() {
        let expr = value_expr(NumericType::Extended, 100);
        assert_eq!(eval_nat_expr(&expr), Some(100));
    }

    #[test]
    fn test_value_expr_extended_negative() {
        let expr = value_expr(NumericType::Extended, -3);
        assert_eq!(eval_int_expr(&expr), Some(-3));
    }
}
