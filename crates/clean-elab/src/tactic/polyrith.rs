// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial arithmetic tactics (polyrith)
//!
//! Provides tactics for proving polynomial equalities using algebraic certificates.
//! The `Polynomial` type and conversion helpers are in `polynomial.rs` (#307).

use clean_kernel::Expr;

use super::pattern::linear_combination_proof::build_linear_combination_eq_proof;
use super::pattern::LinearCoeff;
use super::polynomial::{expr_to_polynomial, VarMap};
use super::{match_equality, rfl, ProofState, TacticError, TacticResult};

// Re-export Polynomial type from polynomial module for backward compatibility
pub use super::polynomial::Polynomial;

/// A polynomial certificate for polyrith
#[derive(Debug, Clone)]
pub struct PolyrithCertificate {
    /// Coefficients for linear combination of hypotheses
    pub coefficients: Vec<(String, Polynomial)>,
    /// Whether the certificate was verified
    pub verified: bool,
    /// Human-readable explanation
    pub explanation: String,
}

/// Configuration for polyrith
#[derive(Debug, Clone)]
pub struct PolyrithConfig {
    /// Maximum polynomial degree to consider
    pub max_degree: u64,
    /// Whether to try simple integer coefficients first
    pub try_simple: bool,
    /// Maximum number of hypotheses to combine
    pub max_hyps: usize,
}

impl Default for PolyrithConfig {
    fn default() -> Self {
        PolyrithConfig {
            max_degree: 4,
            try_simple: true,
            max_hyps: 10,
        }
    }
}

/// The polyrith tactic: prove polynomial equalities using algebraic certificates
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: goal target is an equality between polynomial expressions
/// ENSURES: On Ok, the goal is closed with a proof term
/// ENSURES: On Err(GoalMismatch), target is not a polynomial equality
pub fn polyrith(state: &mut ProofState) -> TacticResult {
    polyrith_with_config(state, PolyrithConfig::default())
}

/// Polyrith with custom configuration
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the goal is closed with a proof term
pub fn polyrith_with_config(state: &mut ProofState, config: PolyrithConfig) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Parse goal as polynomial equality
    let (ty, lhs, rhs, _levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("polyrith: goal must be an equality".to_string()))?;

    // Check that it's a numeric type
    let ty_str = format!("{ty:?}");
    if !ty_str.contains("Nat")
        && !ty_str.contains("Int")
        && !ty_str.contains("Rat")
        && !ty_str.contains("Real")
    {
        // Allow anyway for now, may be polymorphic
    }

    let mut var_map = VarMap::new();

    let lhs_poly =
        expr_to_polynomial(&lhs, &mut var_map).ok_or_else(|| TacticError::ArithmeticFailed {
            tactic: "polyrith".into(),
            reason: "could not parse LHS as polynomial".into(),
        })?;
    let rhs_poly =
        expr_to_polynomial(&rhs, &mut var_map).ok_or_else(|| TacticError::ArithmeticFailed {
            tactic: "polyrith".into(),
            reason: "could not parse RHS as polynomial".into(),
        })?;

    let goal_poly = lhs_poly.sub(&rhs_poly);

    // If goal is trivially zero, done
    if goal_poly.is_zero() {
        // Close with reflexivity
        return rfl(state);
    }

    let hyp_polys = collect_hyp_polynomials(&goal.local_ctx, &mut var_map, config.max_hyps);

    // Try to find and use a verified certificate
    if let Some(cert) = find_polynomial_certificate(&goal_poly, &hyp_polys, &config) {
        if cert.verified {
            return close_with_verified_cert(state, &goal, &cert);
        }
    }

    // Try simple cases: goal reduces to lhs = lhs
    if config.try_simple && lhs == rhs {
        return rfl(state);
    }

    Err(TacticError::SearchExhausted {
        tactic: "polyrith".into(),
        detail: format!(
            "could not find polynomial certificate (goal degree: {}, {} hypotheses)",
            goal_poly.degree(),
            hyp_polys.len()
        ),
    })
}

/// Part of #2526: try proof reconstruction, then fail closed if it returns None.
fn close_with_verified_cert(
    state: &mut ProofState,
    goal: &super::Goal,
    cert: &PolyrithCertificate,
) -> TacticResult {
    if let Some(ref coeffs) = cert_to_linear_coeffs(cert) {
        if let Some(proof) = build_linear_combination_eq_proof(state, goal, coeffs) {
            return state
                .close_goal(goal, proof)
                .map_err(|_| TacticError::ArithmeticFailed {
                    tactic: "polyrith".into(),
                    reason: "proof reconstruction type check failed".into(),
                });
        }
    }
    Err(TacticError::ArithmeticFailed {
        tactic: "polyrith".into(),
        reason: "verified certificate, proof reconstruction returned None".into(),
    })
}

/// Collect polynomial representations of equality hypotheses from the local context.
///
/// REQUIRES: `ctx` entries have well-formed types; equality hypotheses use the same variable encoding as `goal`
/// ENSURES: Result length is at most `max_hyps`
/// ENSURES: Each returned polynomial is `lhs - rhs` for a parseable equality hypothesis from `ctx`
/// ENSURES: Non-equality or non-polynomial hypotheses are skipped
fn collect_hyp_polynomials(
    ctx: &[super::LocalDecl],
    var_map: &mut VarMap,
    max_hyps: usize,
) -> Vec<(String, Polynomial)> {
    let mut hyp_polys = Vec::new();
    for decl in ctx {
        if hyp_polys.len() >= max_hyps {
            break;
        }
        if let Ok((_, h_lhs, h_rhs, _)) = match_equality(&decl.ty) {
            if let (Some(hl), Some(hr)) = (
                expr_to_polynomial(&h_lhs, var_map),
                expr_to_polynomial(&h_rhs, var_map),
            ) {
                hyp_polys.push((decl.name.clone(), hl.sub(&hr)));
            }
        }
    }
    hyp_polys
}

/// REQUIRES: `hyps` contains polynomial representations of equality hypotheses
/// ENSURES: On Some, returned certificate is verified (cert.verified == true)
/// ENSURES: On None, no certificate was found within search bounds
fn find_polynomial_certificate(
    goal: &Polynomial,
    hyps: &[(String, Polynomial)],
    config: &PolyrithConfig,
) -> Option<PolyrithCertificate> {
    // Simple strategy: try small integer coefficients
    if hyps.is_empty() {
        if goal.is_zero() {
            return Some(PolyrithCertificate {
                coefficients: vec![],
                verified: true,
                explanation: "Goal is trivially zero".to_string(),
            });
        }
        return None;
    }

    // For single hypothesis case, check if goal is a multiple
    if hyps.len() == 1 {
        // Try coefficients -2, -1, 1, 2
        for c in [-2i64, -1, 1, 2] {
            let scaled = hyps[0].1.mul(&Polynomial::constant(c, 1));
            if scaled.sub(goal).is_zero() {
                return Some(PolyrithCertificate {
                    coefficients: vec![(hyps[0].0.clone(), Polynomial::constant(c, 1))],
                    verified: true,
                    explanation: format!("goal = {} * {}", c, hyps[0].0),
                });
            }
        }
    }

    // For two hypotheses, try simple linear combinations
    if hyps.len() >= 2 && goal.degree() <= config.max_degree {
        if let Some(cert) = try_two_hyp_combinations(goal, hyps) {
            return Some(cert);
        }
    }

    None
}

/// Try linear combinations of the first two hypotheses with small integer coefficients.
///
/// REQUIRES: `hyps.len() >= 2`
/// ENSURES: On Some, certificate uses only `hyps[0]` and `hyps[1]` with small integer or half-integer coefficients
/// ENSURES: On None, no tested two-hypothesis combination matched `goal`
fn try_two_hyp_combinations(
    goal: &Polynomial,
    hyps: &[(String, Polynomial)],
) -> Option<PolyrithCertificate> {
    for c1 in -3i64..=3 {
        for c2 in -3i64..=3 {
            if c1 == 0 && c2 == 0 {
                continue;
            }
            let combo = hyps[0]
                .1
                .mul(&Polynomial::constant(c1, 1))
                .add(&hyps[1].1.mul(&Polynomial::constant(c2, 1)));

            if combo.sub(goal).is_zero() {
                return Some(PolyrithCertificate {
                    coefficients: vec![
                        (hyps[0].0.clone(), Polynomial::constant(c1, 1)),
                        (hyps[1].0.clone(), Polynomial::constant(c2, 1)),
                    ],
                    verified: true,
                    explanation: format!("goal = {} * {} + {} * {}", c1, hyps[0].0, c2, hyps[1].0),
                });
            }
        }
    }

    // Try with division by 2
    for c1 in -2i64..=2 {
        for c2 in -2i64..=2 {
            let combo = hyps[0]
                .1
                .mul(&Polynomial::constant(c1, 2))
                .add(&hyps[1].1.mul(&Polynomial::constant(c2, 2)));

            if combo.sub(goal).is_zero() {
                return Some(PolyrithCertificate {
                    coefficients: vec![
                        (hyps[0].0.clone(), Polynomial::constant(c1, 2)),
                        (hyps[1].0.clone(), Polynomial::constant(c2, 2)),
                    ],
                    verified: true,
                    explanation: format!(
                        "goal = ({}/2) * {} + ({}/2) * {}",
                        c1, hyps[0].0, c2, hyps[1].0
                    ),
                });
            }
        }
    }

    None
}

/// Check if expression represents a polynomial
pub fn is_polynomial_expr(expr: &Expr) -> bool {
    let mut var_map = VarMap::new();
    expr_to_polynomial(expr, &mut var_map).is_some()
}

/// Convert verified certificate coefficients into `LinearCoeff`s.
///
/// Each `(hyp_name, Polynomial)` is passed through `Polynomial::as_constant_coeff()`.
/// Returns `None` if any coefficient is non-constant (fail-closed per design).
///
/// ENSURES: On Some, every coefficient was a constant rational
/// ENSURES: On None, at least one coefficient had variable terms
fn cert_to_linear_coeffs(cert: &PolyrithCertificate) -> Option<Vec<LinearCoeff>> {
    let mut coeffs = Vec::with_capacity(cert.coefficients.len());
    for (hyp_name, poly) in &cert.coefficients {
        let (num, den) = poly.as_constant_coeff()?;
        if num == 0 {
            continue; // skip zero-coefficient hypotheses
        }
        coeffs.push(LinearCoeff::new(hyp_name, num, den));
    }
    Some(coeffs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{env::Declaration, Environment, FVarId, Level, Name};

    use super::super::LocalDecl;

    fn setup_env_with_eq() -> Environment {
        let mut env = Environment::new();
        env.init_eq().expect("Eq should initialize");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("N"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("N should add");
        for name in ["x", "y"] {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::const_(Name::from_string("N"), vec![]),
            })
            .expect("constant should add");
        }
        env
    }

    fn make_eq_n(lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    Expr::const_(Name::from_string("N"), vec![]),
                ),
                lhs,
            ),
            rhs,
        )
    }

    #[test]
    fn test_verified_certificate_missing_proof_returns_arithmetic_failed() {
        let cert = PolyrithCertificate {
            coefficients: vec![("h".to_string(), Polynomial::constant(1, 2))],
            verified: true,
            explanation: "test missing proof".to_string(),
        };
        let env = setup_env_with_eq();
        let x = Expr::const_(Name::from_string("x"), vec![]);
        let y = Expr::const_(Name::from_string("y"), vec![]);
        let mut state = ProofState::with_context(
            env,
            make_eq_n(y.clone(), x.clone()),
            vec![LocalDecl {
                fvar: FVarId::new(0),
                name: "h".to_string(),
                ty: make_eq_n(x, y),
                value: None,
            }],
        );
        let goal = state.current_goal().expect("goal should exist").clone();

        let result = close_with_verified_cert(&mut state, &goal, &cert);
        assert!(
            matches!(
                result,
                Err(TacticError::ArithmeticFailed { ref tactic, ref reason })
                    if tactic == "polyrith"
                        && reason == "verified certificate, proof reconstruction returned None"
            ),
            "expected fail-closed ArithmeticFailed, got: {result:?}"
        );
        assert_eq!(
            state.trust_ledger().trusted_arith_count,
            0,
            "fail-closed polyrith must not record trustedArith"
        );
        assert!(
            !state.is_complete(),
            "fail-closed polyrith should leave the goal open"
        );
    }
}
