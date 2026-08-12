// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse tactic proof reconstruction
//!
//! Builds kernel-valid proof terms from mathverse certificates.
//! Handles arithmetic, parity, and divisibility contradictions.

use clean_kernel::{Environment, Expr, FVarId};

use super::arith_linarith::{build_linarith_proof, LinarithCertificate};
use super::arith_mathverse_proof_builders::{
    build_divisibility_contradiction_proof, build_parity_contradiction_proof,
};
use super::arithmetic::{LinearConstraint, LinearExpr};
use super::omega_tactic::{MathverseCertificate, MathverseContradictionType};
use super::{Goal, ProofState};

#[derive(Debug, Clone)]
pub(crate) enum MathverseProofOutcome {
    Proof(Expr),
    UnsupportedModularProof { reason: String },
}

/// Check for modular/parity contradictions
///
/// Detects when two constraints specify conflicting residue classes:
/// - expr ≡ r₁ (mod m) and expr ≡ r₂ (mod m) with r₁ ≠ r₂
/// - Special case: expr ≡ 0 (mod 2) and expr ≡ 1 (mod 2) is a parity contradiction
/// - expr ≡ 0 (mod m) and expr % m ≠ 0 is a contradiction
///
/// REQUIRES: `constraints` and `cert_map` have the same length
/// ENSURES: On Some, returned certificate has `contradiction_type` of `Parity` or `Divisibility`
/// ENSURES: On None, no modular contradiction was found
pub(crate) fn check_modular_contradictions(
    constraints: &[LinearConstraint],
    cert_map: &[MathverseCertificate],
) -> Option<MathverseCertificate> {
    // Collect modular constraints grouped by expression and modulus
    // For each Mod constraint, extract the base expression (without the remainder offset)
    // and track the remainder separately.
    //
    // LinearConstraint::Mod { expr, modulus } represents expr ≡ 0 (mod modulus)
    // where expr = original_expr - remainder
    // So: remainder = -expr.constant (when expr is var - remainder)
    //
    // We group by (coefficients_without_constant, modulus) to detect conflicts
    // where the same expression has different remainders.

    // Structure: Vec<(base_coeffs, modulus, remainder, constraint_index)>
    // where base_coeffs is the expression without the constant term
    let mut mod_constraints: Vec<(Vec<(usize, i64)>, i64, i64, usize)> = Vec::new();

    // NotMod constraints: (base_coeffs, modulus, remainder, constraint_index)
    // LinearConstraint::NotMod { expr, modulus } represents expr % modulus ≠ 0
    let mut not_mod_constraints: Vec<(Vec<(usize, i64)>, i64, i64, usize)> = Vec::new();

    for (idx, c) in constraints.iter().enumerate() {
        if let LinearConstraint::Mod { expr, modulus } = c {
            // expr ≡ 0 (mod modulus) where expr = base_expr - remainder
            // remainder = -expr.constant
            let remainder = -expr.constant;
            mod_constraints.push((expr.coeffs.clone(), *modulus, remainder, idx));
        } else if let LinearConstraint::NotMod { expr, modulus } = c {
            // expr % modulus ≠ 0 where expr = base_expr - remainder
            let remainder = -expr.constant;
            not_mod_constraints.push((expr.coeffs.clone(), *modulus, remainder, idx));
        }
    }

    // Check for Mod + NotMod contradictions
    // If base_expr ≡ r (mod m) and base_expr % m ≠ r, that's a contradiction
    for (base_coeffs, modulus, remainder, mod_idx) in &mod_constraints {
        // We have base_expr ≡ r (mod m), check for base_expr % m ≠ r with same r
        for (not_base_coeffs, not_modulus, not_remainder, not_mod_idx) in &not_mod_constraints {
            if not_modulus == modulus
                && *not_remainder == *remainder
                && base_coeffs == not_base_coeffs
            {
                // Found contradiction: expr ≡ r (mod m) and expr % m ≠ r

                // Combine certificates
                let mut combined = MathverseCertificate::new(cert_map[*mod_idx].coefficients.len());
                for (i, coeff) in cert_map[*mod_idx].coefficients.iter().enumerate() {
                    combined.coefficients[i] += coeff;
                }
                for (i, coeff) in cert_map[*not_mod_idx].coefficients.iter().enumerate() {
                    combined.coefficients[i] += coeff;
                }

                combined.contradiction_type = MathverseContradictionType::Divisibility;

                return Some(combined);
            }
        }
    }

    // Check for contradictions between Mod constraints with same expression but different remainders
    // Group by (base_coeffs, modulus)
    for (i, (base_coeffs_i, modulus_i, remainder_i, idx_i)) in mod_constraints.iter().enumerate() {
        for (base_coeffs_j, modulus_j, remainder_j, idx_j) in mod_constraints.iter().skip(i + 1) {
            // Check if same expression and modulus but different remainders
            if modulus_i == modulus_j
                && base_coeffs_i == base_coeffs_j
                && remainder_i != remainder_j
            {
                // Found a contradiction!

                // Combine certificates
                let mut combined = MathverseCertificate::new(cert_map[*idx_i].coefficients.len());
                for (k, coeff) in cert_map[*idx_i].coefficients.iter().enumerate() {
                    combined.coefficients[k] += coeff;
                }
                for (k, coeff) in cert_map[*idx_j].coefficients.iter().enumerate() {
                    combined.coefficients[k] += coeff;
                }

                // Determine contradiction type
                combined.contradiction_type = if *modulus_i == 2 {
                    MathverseContradictionType::Parity
                } else {
                    MathverseContradictionType::Divisibility
                };

                return Some(combined);
            }
        }
    }

    None
}

/// Check for equality/disequality contradictions (e = 0 and e ≠ 0)
///
/// REQUIRES: `constraints` and `cert_map` have the same length
/// ENSURES: On Some, returned certificate has `contradiction_type` of `Arithmetic`
/// ENSURES: On None, no equality/disequality contradiction was found
pub(crate) fn check_equality_contradictions(
    constraints: &[LinearConstraint],
    cert_map: &[MathverseCertificate],
) -> Option<MathverseCertificate> {
    // Collect Eq and Ne constraints
    let mut eq_constraints: Vec<(LinearExpr, usize)> = Vec::new();
    let mut ne_constraints: Vec<(LinearExpr, usize)> = Vec::new();

    for (idx, c) in constraints.iter().enumerate() {
        match c {
            LinearConstraint::Eq(e) => eq_constraints.push((e.clone(), idx)),
            LinearConstraint::Ne(e) => ne_constraints.push((e.clone(), idx)),
            _ => {}
        }
    }

    // Check for e = 0 paired with e ≠ 0
    for (eq_expr, eq_idx) in &eq_constraints {
        for (ne_expr, ne_idx) in &ne_constraints {
            if eq_expr == ne_expr {
                // Found a contradiction: e = 0 and e ≠ 0
                let mut combined = MathverseCertificate::new(cert_map[*eq_idx].coefficients.len());
                for (i, coeff) in cert_map[*eq_idx].coefficients.iter().enumerate() {
                    combined.coefficients[i] += coeff;
                }
                for (i, coeff) in cert_map[*ne_idx].coefficients.iter().enumerate() {
                    combined.coefficients[i] += coeff;
                }
                combined.contradiction_type = MathverseContradictionType::Arithmetic;

                return Some(combined);
            }
        }
    }

    None
}

/// Build mathverse proof from certificate
///
/// REQUIRES: `hypothesis_fvars` maps certificate indices to local context free variables
/// REQUIRES: `certificate.coefficients.len() <= hypothesis_fvars.len()`
/// ENSURES: On Some, returns a well-typed proof term of type `False`
/// ENSURES: On None, no proof could be constructed (caller should use sorry fallback)
pub(crate) fn build_mathverse_proof(
    state: &ProofState,
    goal: &Goal,
    certificate: &MathverseCertificate,
    hypothesis_fvars: &[FVarId],
    env: &Environment,
) -> Option<Expr> {
    // Handle different contradiction types
    match &certificate.contradiction_type {
        MathverseContradictionType::Arithmetic | MathverseContradictionType::LinearCombination => {
            // Direct goal-driven Nat inequality proof (ineq_gap fix): when the
            // contradiction comes from the negated goal (e.g. `n + 1 > n` with
            // no hypotheses), the refutation-of-hypotheses builder below has no
            // fvar to thread, so prove the goal directly first. The synthesized
            // term is still re-checked by the caller's `state.close_goal`.
            if certificate.uses_goal_negation {
                let direct_hyps: Vec<(Expr, Expr)> = goal
                    .local_ctx
                    .iter()
                    .map(|d| (Expr::fvar(d.fvar), d.ty.clone()))
                    .collect();
                if let Some(direct) =
                    super::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps(
                        &goal.target,
                        &direct_hyps,
                    )
                {
                    return Some(direct);
                }
            }
            // Use linarith infrastructure for linear combination proofs
            let linarith_cert = LinarithCertificate {
                coefficients: certificate.coefficients.clone(),
                result_constant: 1_i128,
            };
            build_linarith_proof(state, goal, &linarith_cert, hypothesis_fvars)
        }
        MathverseContradictionType::Parity => {
            match build_modular_mathverse_proof(state, goal, certificate, hypothesis_fvars, env) {
                MathverseProofOutcome::Proof(proof) => Some(proof),
                MathverseProofOutcome::UnsupportedModularProof { .. } => None,
            }
        }
        MathverseContradictionType::Divisibility => {
            match build_modular_mathverse_proof(state, goal, certificate, hypothesis_fvars, env) {
                MathverseProofOutcome::Proof(proof) => Some(proof),
                MathverseProofOutcome::UnsupportedModularProof { .. } => None,
            }
        }
    }
}

pub(crate) fn build_modular_mathverse_proof(
    state: &ProofState,
    goal: &Goal,
    certificate: &MathverseCertificate,
    hypothesis_fvars: &[FVarId],
    env: &Environment,
) -> MathverseProofOutcome {
    match &certificate.contradiction_type {
        MathverseContradictionType::Parity => {
            build_parity_contradiction_proof(state, goal, certificate, hypothesis_fvars, env)
                .map(MathverseProofOutcome::Proof)
                .unwrap_or_else(|| MathverseProofOutcome::UnsupportedModularProof {
                    reason: "parity contradiction has no theorem-backed proof bridge".into(),
                })
        }
        MathverseContradictionType::Divisibility => {
            build_divisibility_contradiction_proof(state, goal, certificate, hypothesis_fvars, env)
                .map(MathverseProofOutcome::Proof)
                .unwrap_or_else(|| MathverseProofOutcome::UnsupportedModularProof {
                    reason: "divisibility contradiction proof replay is unavailable".into(),
                })
        }
        MathverseContradictionType::Arithmetic | MathverseContradictionType::LinearCombination => {
            unreachable!("build_modular_mathverse_proof called for non-modular contradiction")
        }
    }
}
