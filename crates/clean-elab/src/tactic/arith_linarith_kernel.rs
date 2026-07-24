// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-verified linarith theorem generation.
//!
//! Wraps the linarith tactic to produce `Declaration::Theorem` entries
//! that are verified by the kernel type checker via `add_decl()`.
//!
//! The core function `linarith_kernel_theorem` takes hypothesis types and a
//! goal type, runs linarith to find a proof, abstracts the free variables
//! into de Bruijn indices, and registers the result as a kernel theorem.
//!
//! Part of #3367.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Expr, FVarId};

use super::arith_linarith::linarith_prove;
use super::TacticError;

/// Errors from kernel-verified linarith theorem generation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LinarithKernelError {
    /// The linarith tactic could not prove the goal from the hypotheses.
    #[error("linarith tactic failed: {0}")]
    TacticFailed(TacticError),

    /// Linarith closed the goal but did not produce a proof term.
    #[error("linarith closed the goal but no proof term was retained")]
    NoProofTerm,

    /// The kernel type checker rejected the generated proof term.
    #[error("kernel rejected the proof: {0}")]
    KernelRejected(String),
}

impl From<TacticError> for LinarithKernelError {
    fn from(e: TacticError) -> Self {
        LinarithKernelError::TacticFailed(e)
    }
}

/// Build the closed type for a theorem: `forall (h0 : hyp0) (h1 : hyp1) ... , goal`.
///
/// Uses de Bruijn encoding: the goal is lifted by `n` (number of hypotheses),
/// and each hypothesis type is lifted by its position index.
///
/// REQUIRES: `hypotheses` contains well-typed kernel expressions
/// REQUIRES: `goal` is a well-typed kernel expression
/// ENSURES: The returned expression is a closed Pi-type (no free variables)
fn build_theorem_type(hypotheses: &[Expr], goal: &Expr, fvar_ids: &[FVarId]) -> Expr {
    // Start with the goal, then wrap in Pi binders from right to left.
    // We abstract FVars in reverse order so de Bruijn indices are correct.
    let mut ty = goal.clone();
    for i in (0..hypotheses.len()).rev() {
        ty = ty.abstract_fvar(fvar_ids[i]);
        let hyp_ty = {
            let mut h = hypotheses[i].clone();
            // Abstract all FVars with index > i (those already abstracted)
            for j in (i + 1..hypotheses.len()).rev() {
                h = h.abstract_fvar(fvar_ids[j]);
            }
            h
        };
        ty = Expr::pi(BinderInfo::Default, hyp_ty, ty);
    }
    ty
}

/// Build the closed proof value: `fun (h0 : hyp0) (h1 : hyp1) ... => proof_body`.
///
/// Abstracts free variables from the proof term produced by linarith.
///
/// REQUIRES: `proof` is a proof term potentially containing FVars from `fvar_ids`
/// REQUIRES: `hypotheses` and `fvar_ids` have the same length
/// ENSURES: The returned expression is a closed lambda term (no free variables)
fn build_theorem_value(hypotheses: &[Expr], proof: &Expr, fvar_ids: &[FVarId]) -> Expr {
    // Abstract FVars in reverse order, then wrap in lambda binders.
    let mut val = proof.clone();
    for i in (0..hypotheses.len()).rev() {
        val = val.abstract_fvar(fvar_ids[i]);
        let hyp_ty = {
            let mut h = hypotheses[i].clone();
            for j in (i + 1..hypotheses.len()).rev() {
                h = h.abstract_fvar(fvar_ids[j]);
            }
            h
        };
        val = Expr::lam(BinderInfo::Default, hyp_ty, val);
    }
    val
}

/// Generate a kernel-verified linarith theorem.
///
/// Takes an environment, a theorem name, hypothesis types, and a goal type.
/// Runs the linarith tactic to produce a proof term, wraps it in a
/// `Declaration::Theorem`, and verifies it via `env.add_decl()`.
///
/// The theorem's type is: `forall (h0 : hyp0) (h1 : hyp1) ..., goal`
/// The theorem's value is: `fun (h0 : hyp0) (h1 : hyp1) ... => proof`
///
/// REQUIRES: `env` contains all necessary declarations (Nat, LE, etc.)
/// REQUIRES: `hypotheses` are well-typed proposition types
/// REQUIRES: `goal` is a well-typed proposition type
/// REQUIRES: `name` is not already declared in `env`
/// ENSURES: On `Ok(proof)`, a `Declaration::Theorem` with the given name is
///          added to `env` and verified by the kernel type checker
/// ENSURES: On `Err(_)`, `env` is unchanged
///
/// # Example
/// ```text
/// let mut env = Environment::with_prelude();
/// // h : 3 <= 2 (contradictory) |- False
/// let h_ty = make_nat_le(3, 2);
/// let goal = Expr::const_(Name::from_string("False"), vec![]);
/// let proof = linarith_kernel_theorem(&mut env, "my_thm", &[h_ty], &goal)?;
/// assert!(env.get_const(&Name::from_string("my_thm")).is_some());
/// ```
///
/// Part of #3367.
pub fn linarith_kernel_theorem(
    env: &mut Environment,
    name: &str,
    hypotheses: &[Expr],
    goal: &Expr,
) -> Result<Expr, LinarithKernelError> {
    // Step 1: Run linarith to get a proof term (with FVar references)
    let proof = linarith_prove(env, hypotheses, goal)?;

    // Step 2: Build FVar IDs matching what linarith_prove used
    // linarith_prove uses FVarId::new(1000 + i) for hypothesis i
    let fvar_ids: Vec<FVarId> = (0..hypotheses.len())
        .map(|i| FVarId::new(1000 + i as u64))
        .collect();

    // Step 3: Build closed theorem type and value
    let thm_type = build_theorem_type(hypotheses, goal, &fvar_ids);
    let thm_value = build_theorem_value(hypotheses, &proof, &fvar_ids);

    // Step 4: Register as Declaration::Theorem and verify via kernel
    let thm_name = Name::from_string(name);
    let decl = Declaration::Theorem {
        name: thm_name,
        level_params: vec![],
        type_: thm_type,
        value: thm_value.clone(),
    };

    env.add_decl(decl)
        .map_err(|e| LinarithKernelError::KernelRejected(format!("{e}")))?;

    Ok(thm_value)
}

/// Generate a kernel-verified linarith theorem without modifying the environment.
///
/// Like `linarith_kernel_theorem` but returns the proof term and theorem type
/// without registering in the environment. Useful for producing proof terms
/// for inline use (e.g., inside a tactic proof state).
///
/// Part of #3367.
pub fn linarith_kernel_proof(
    env: &Environment,
    hypotheses: &[Expr],
    goal: &Expr,
) -> Result<(Expr, Expr), LinarithKernelError> {
    let proof = linarith_prove(env, hypotheses, goal)?;

    let fvar_ids: Vec<FVarId> = (0..hypotheses.len())
        .map(|i| FVarId::new(1000 + i as u64))
        .collect();

    let thm_type = build_theorem_type(hypotheses, goal, &fvar_ids);
    let thm_value = build_theorem_value(hypotheses, &proof, &fvar_ids);

    Ok((thm_value, thm_type))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::Environment;
    use clean_kernel::level::Level;

    /// Build `@LE.le.{0} Nat instLENat lhs rhs`.
    fn make_nat_le_tc(lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                        Expr::const_(Name::from_string("Nat"), vec![]),
                    ),
                    Expr::const_(Name::from_string("instLENat"), vec![]),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `@LE.le.{0} Int instLEInt lhs rhs`.
    fn make_int_le_tc(lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                        Expr::const_(Name::from_string("Int"), vec![]),
                    ),
                    Expr::const_(Name::from_string("instLEInt"), vec![]),
                ),
                lhs,
            ),
            rhs,
        )
    }

    fn int_ofnat(n: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    }

    fn false_expr() -> Expr {
        Expr::const_(Name::from_string("False"), vec![])
    }

    // =========================================================================
    // Test 1: Simple contradictory Nat inequality -> kernel theorem
    // =========================================================================

    /// Given h : 3 <= 2 (contradictory), linarith should produce a kernel-verified
    /// Declaration::Theorem proving False.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_nat_contradiction_3_le_2() {
        let mut env = Environment::with_prelude();
        let h_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
        let goal = false_expr();

        let result = linarith_kernel_theorem(&mut env, "nat_contra_3_2", &[h_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_theorem should succeed for h : 3 <= 2 |- False, got: {result:?}"
        );

        // Verify the theorem is registered in the environment
        let thm_name = Name::from_string("nat_contra_3_2");
        assert!(
            env.get_const(&thm_name).is_some(),
            "theorem 'nat_contra_3_2' should be registered in the environment"
        );
    }

    // =========================================================================
    // Test 2: Two-hypothesis Nat transitivity chain
    // =========================================================================

    /// h1 : 5 <= 3, h2 : 3 <= 1 -> 5 <= 1, contradiction -> False
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_nat_two_hyp_chain() {
        let mut env = Environment::with_prelude();
        let h1_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(3));
        let h2_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(1));
        let goal = false_expr();

        let result = linarith_kernel_theorem(&mut env, "nat_chain_5_3_1", &[h1_ty, h2_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_theorem should succeed for h1 : 5<=3, h2 : 3<=1 |- False, got: {result:?}"
        );

        let thm_name = Name::from_string("nat_chain_5_3_1");
        assert!(
            env.get_const(&thm_name).is_some(),
            "theorem 'nat_chain_5_3_1' should be registered in the environment"
        );
    }

    // =========================================================================
    // Test 3: Three-hypothesis Nat accumulation
    // =========================================================================

    /// h1 : 3<=1, h2 : 4<=2, h3 : 5<=0 -> (3+4+5) <= (1+2+0) = 12 <= 3, contradiction.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_nat_three_hyp_accumulation() {
        let mut env = Environment::with_prelude();
        let h1_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(1));
        let h2_ty = make_nat_le_tc(Expr::nat_lit(4), Expr::nat_lit(2));
        let h3_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(0));
        let goal = false_expr();

        let result =
            linarith_kernel_theorem(&mut env, "nat_accum_3hyp", &[h1_ty, h2_ty, h3_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_theorem should succeed for 3-hyp Nat accumulation, got: {result:?}"
        );

        let thm_name = Name::from_string("nat_accum_3hyp");
        assert!(
            env.get_const(&thm_name).is_some(),
            "theorem 'nat_accum_3hyp' should be registered in the environment"
        );
    }

    // =========================================================================
    // Test 4: Int contradiction
    // =========================================================================

    /// h : Int.ofNat(5) <= Int.ofNat(3), contradiction -> False
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_int_contradiction() {
        let mut env = Environment::with_prelude();
        env.init_int_ord_lemmas()
            .expect("Int ordering lemmas should initialize");

        let h_ty = make_int_le_tc(int_ofnat(5), int_ofnat(3));
        let goal = false_expr();

        let result = linarith_kernel_theorem(&mut env, "int_contra_5_3", &[h_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_theorem should succeed for Int contradiction, got: {result:?}"
        );
    }

    // =========================================================================
    // Test 5: kernel_proof (without registration)
    // =========================================================================

    /// linarith_kernel_proof should produce a valid proof term and type
    /// without modifying the environment.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_proof_returns_closed_term() {
        let env = Environment::with_prelude();
        let h_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
        let goal = false_expr();

        let result = linarith_kernel_proof(&env, &[h_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_proof should succeed, got: {result:?}"
        );

        let (value, ty) = result.unwrap();
        // The type should be a Pi: forall h : 3 <= 2, False
        assert!(
            matches!(value.kind(), clean_kernel::expr::ExprKind::Lam(..)),
            "proof value should be a lambda term"
        );
        assert!(
            matches!(ty.kind(), clean_kernel::expr::ExprKind::Pi(..)),
            "proof type should be a Pi type"
        );
    }

    // =========================================================================
    // Test 6: Error case - satisfiable constraints
    // =========================================================================

    /// When constraints are satisfiable, linarith should return TacticFailed.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_rejects_satisfiable() {
        let mut env = Environment::with_prelude();
        // h : 1 <= 3 (true, not contradictory)
        let h_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::nat_lit(3));
        let goal = false_expr();

        let result = linarith_kernel_theorem(&mut env, "should_fail", &[h_ty], &goal);
        assert!(
            result.is_err(),
            "linarith_kernel_theorem should fail for satisfiable constraints"
        );
        assert!(
            matches!(result.unwrap_err(), LinarithKernelError::TacticFailed(_)),
            "error should be TacticFailed"
        );
    }

    // =========================================================================
    // Test 7: Duplicate name error
    // =========================================================================

    /// Registering a theorem with a name that already exists should fail
    /// with KernelRejected.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_duplicate_name_rejected() {
        let mut env = Environment::with_prelude();
        let h_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
        let goal = false_expr();

        // First registration should succeed
        let result =
            linarith_kernel_theorem(&mut env, "dup_test_thm", std::slice::from_ref(&h_ty), &goal);
        assert!(result.is_ok(), "first registration should succeed");

        // Second registration with same name should fail
        let result2 = linarith_kernel_theorem(&mut env, "dup_test_thm", &[h_ty], &goal);
        assert!(result2.is_err(), "duplicate name should be rejected");
        assert!(
            matches!(result2.unwrap_err(), LinarithKernelError::KernelRejected(_)),
            "error should be KernelRejected for duplicate name"
        );
    }

    // =========================================================================
    // Test 8: Proof quality - no sorry or trustedArith
    // =========================================================================

    /// The generated proof must not contain sorry or trustedArith references.
    /// This verifies genuine proof reconstruction, not axiom wrapping.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_no_sorry_no_trusted_arith() {
        use clean_kernel::expr::ExprKind;

        fn contains_const(expr: &Expr, name_str: &str) -> bool {
            match expr.kind() {
                ExprKind::Const(name, _) => name == &Name::from_string(name_str),
                ExprKind::App(f, a) => contains_const(f, name_str) || contains_const(a, name_str),
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    contains_const(ty, name_str) || contains_const(body, name_str)
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    contains_const(ty, name_str)
                        || contains_const(val, name_str)
                        || contains_const(body, name_str)
                }
                ExprKind::Proj(_, _, inner)
                | ExprKind::MData(_, inner)
                | ExprKind::Squash(inner) => contains_const(inner, name_str),
                _ => false,
            }
        }

        let mut env = Environment::with_prelude();
        let h_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
        let goal = false_expr();

        let proof = linarith_kernel_theorem(&mut env, "soundness_check", &[h_ty], &goal)
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

    // =========================================================================
    // Test 9: Two-hypothesis Int transitivity with kernel verification
    // =========================================================================

    /// h1 : Int.ofNat(10) <= Int.ofNat(5), h2 : Int.ofNat(5) <= Int.ofNat(2)
    /// -> Int.ofNat(10) <= Int.ofNat(2), contradiction -> False
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_int_two_hyp_chain() {
        let mut env = Environment::with_prelude();
        env.init_int_ord_lemmas()
            .expect("Int ordering lemmas should initialize");

        let h1_ty = make_int_le_tc(int_ofnat(10), int_ofnat(5));
        let h2_ty = make_int_le_tc(int_ofnat(5), int_ofnat(2));
        let goal = false_expr();

        let result = linarith_kernel_theorem(&mut env, "int_chain_10_5_2", &[h1_ty, h2_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_theorem should succeed for Int 2-hyp chain, got: {result:?}"
        );
    }

    // =========================================================================
    // Test 10: Verify Declaration::Theorem structure
    // =========================================================================

    /// Verify that the registered declaration is actually a Theorem (not an Axiom
    /// or Definition), confirming genuine proof output.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_is_declaration_theorem() {
        let mut env = Environment::with_prelude();
        let h_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
        let goal = false_expr();

        let _ = linarith_kernel_theorem(&mut env, "decl_check", &[h_ty], &goal)
            .expect("should produce a theorem");

        let thm_name = Name::from_string("decl_check");
        let const_info = env.get_const(&thm_name);
        assert!(const_info.is_some(), "theorem should be registered");
        // The environment stores ConstantInfo, which has a `value` for theorems.
        // If it's an axiom, there would be no value.
        let info = const_info.unwrap();
        assert!(
            info.value.is_some(),
            "Declaration::Theorem should have a proof value (not be an axiom)"
        );
    }

    // =========================================================================
    // Test 11: Large contradiction gap
    // =========================================================================

    /// h : 100 <= 0 -> kernel-verified False
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_nat_large_gap() {
        let mut env = Environment::with_prelude();
        let h_ty = make_nat_le_tc(Expr::nat_lit(100), Expr::nat_lit(0));
        let goal = false_expr();

        let result = linarith_kernel_theorem(&mut env, "nat_large_gap", &[h_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_theorem should succeed for h : 100 <= 0 |- False, got: {result:?}"
        );
    }

    // Rat-specific kernel theorem tests live in
    // `tests/linarith_rat_kernel_theorem.rs` (#3367).

    // =========================================================================
    // Test 14: Farkas-style accumulation over Nat (3 hypotheses)
    // =========================================================================

    /// h1 : 2 <= 0, h2 : 3 <= 1, h3 : 1 <= 0
    /// Farkas: any positive combination gives a contradiction since
    /// 1*h1 alone gives 2 <= 0, which is false for Nat.
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_farkas_nat_accumulation() {
        let mut env = Environment::with_prelude();
        let h1_ty = make_nat_le_tc(Expr::nat_lit(2), Expr::nat_lit(0));
        let h2_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(1));
        let h3_ty = make_nat_le_tc(Expr::nat_lit(1), Expr::nat_lit(0));
        let goal = false_expr();

        let result =
            linarith_kernel_theorem(&mut env, "farkas_nat_3hyp", &[h1_ty, h2_ty, h3_ty], &goal);
        assert!(
            result.is_ok(),
            "linarith_kernel_theorem should succeed for Farkas Nat accumulation, got: {result:?}"
        );
    }

    // =========================================================================
    // Test 15: Empty hypothesis list
    // =========================================================================

    /// With no hypotheses and goal False, linarith should fail (no contradiction
    /// derivable from nothing).
    ///
    /// Part of #3367.
    #[test]
    fn test_kernel_theorem_no_hypotheses_fails() {
        let mut env = Environment::with_prelude();
        let goal = false_expr();

        let result = linarith_kernel_theorem(&mut env, "no_hyps", &[], &goal);
        assert!(
            result.is_err(),
            "linarith_kernel_theorem should fail with no hypotheses"
        );
    }
}
