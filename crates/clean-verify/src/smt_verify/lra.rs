// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRA (Linear Real Arithmetic) checker.
//!
//! Validates `la_generic` theory lemmas via Farkas lemma verification.
//!
//! ## Algorithm
//!
//! 1. Each clause literal is a blocking-clause literal (negation of conflict).
//! 2. Negate to get conflict literals.
//! 3. Each conflict literal is an arithmetic inequality.
//! 4. Multiply each inequality by its non-negative Farkas coefficient.
//! 5. Sum all weighted inequalities.
//! 6. The result must be a contradiction: `0 <= negative` or `0 < 0`.
//!
//! ## Strict inequality handling
//!
//! For real arithmetic, strict (`<`, `>`) and non-strict (`<=`, `>=`) inequalities
//! require different contradiction criteria:
//!
//! - **All non-strict**: The Farkas combination `c1*ineq1 + ... + cn*ineqn` must yield
//!   `K <= 0` where `K > 0` (i.e., a positive constant that violates `<= 0`).
//! - **At least one strict**: Strictness propagates through the combination. If any
//!   input inequality is strict (with positive coefficient), the result is `K < 0`,
//!   which contradicts at `K >= 0`. This means `K = 0` IS a contradiction when
//!   strictness is present (`0 < 0` is false).
//!
//! This distinction is critical for soundness: without it, a Farkas certificate
//! for `x >= 0 AND x <= 0` (which is satisfiable at `x = 0`) would incorrectly
//! be accepted if the sum constant is 0.
//!
//! Reference: ay's `~/ay/crates/ay-proof/src/checker/lra_farkas.rs`

use num_rational::Rational64;

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "lra";

/// An arithmetic relation extracted from an SMT term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ArithRelation {
    /// lhs <= rhs
    Le,
    /// lhs < rhs
    Lt,
    /// lhs >= rhs
    Ge,
    /// lhs > rhs
    Gt,
    /// lhs = rhs
    Eq,
    /// lhs != rhs
    Distinct,
}

/// A linear inequality: sum of (coefficient * variable) + constant REL 0.
///
/// Normalized form: `c1*x1 + c2*x2 + ... + constant REL 0`.
#[derive(Debug, Clone)]
pub(crate) struct LinearInequality {
    /// Variable coefficients: variable_name -> coefficient.
    pub(crate) coefficients: Vec<(String, Rational64)>,
    /// Constant term.
    pub(crate) constant: Rational64,
    /// Relation type.
    pub(crate) relation: ArithRelation,
}

/// Check an LRA `la_generic` theory lemma with Farkas coefficients.
///
/// The clause contains blocking literals (negation of the conflict).
/// The Farkas coefficients are provided as `(numerator, denominator)` pairs.
pub(crate) fn check_lra_farkas(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    farkas_coefficients: &[(i64, i64)],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "la_generic: empty clause");
    }

    if farkas_coefficients.len() != clause.len() {
        return fail(
            step_id,
            &format!(
                "la_generic: {} coefficients for {} literals",
                farkas_coefficients.len(),
                clause.len()
            ),
        );
    }

    // Validate all coefficients are non-negative.
    let coeffs: Vec<Rational64> = farkas_coefficients
        .iter()
        .map(|&(n, d)| {
            if d == 0 {
                Rational64::from_integer(0)
            } else {
                Rational64::new(n, d)
            }
        })
        .collect();

    for (i, c) in coeffs.iter().enumerate() {
        if *c < Rational64::from_integer(0) {
            return fail(
                step_id,
                &format!("la_generic: Farkas coefficient {i} is negative: {c}"),
            );
        }
    }

    // Extract linear inequalities from negated clause literals.
    let mut inequalities: Vec<LinearInequality> = Vec::new();
    for &lit in clause {
        match extract_conflict_inequality(dag, lit) {
            Some(ineq) => inequalities.push(ineq),
            None => {
                // Can't parse this literal as arithmetic; structurally accept.
                return StepVerdict {
                    step_id,
                    trust_level: StepTrustLevel::StructurallyAccepted,
                    checker: CHECKER_NAME,
                    detail: Some(
                        "la_generic: could not parse all literals as arithmetic".to_string(),
                    ),
                };
            }
        }
    }

    // Perform weighted sum: multiply each inequality by its coefficient and sum.
    let result = weighted_sum(&inequalities, &coeffs);

    // Check for contradiction.
    match result {
        Some(contradiction) => {
            if is_contradiction(&contradiction) {
                ok(step_id)
            } else {
                fail(
                    step_id,
                    &format!(
                        "la_generic: weighted sum does not yield contradiction (constant = {})",
                        contradiction.constant
                    ),
                )
            }
        }
        None => fail(step_id, "la_generic: could not compute weighted sum"),
    }
}

/// Check an LRA `la_generic` theory lemma without explicit coefficients.
///
/// Falls back to structural acceptance since we cannot verify without coefficients.
pub(crate) fn check_lra_structural(
    _dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "la_generic: empty clause");
    }
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::StructurallyAccepted,
        checker: CHECKER_NAME,
        detail: Some("la_generic: no Farkas coefficients, structurally accepted".to_string()),
    }
}

/// Extract a conflict inequality from a blocking-clause literal.
///
/// A blocking clause literal is the negation of a conflict literal.
/// So we negate it: `not(a <= b)` becomes `a > b`, etc.
pub(crate) fn extract_conflict_inequality(
    dag: &SmtProofDag,
    lit: SmtTermId,
) -> Option<LinearInequality> {
    let term = dag.term(lit)?;

    match term {
        // Positive literal in blocking clause means the conflict literal is negated.
        // E.g., `(>= x 0)` in the clause means conflict is `(< x 0)`, i.e., `x < 0`.
        SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
            let rel = match op.as_str() {
                "<=" => ArithRelation::Gt, // negation of <=
                ">=" => ArithRelation::Lt, // negation of >=
                "<" => ArithRelation::Ge,  // negation of <
                ">" => ArithRelation::Le,  // negation of >
                "=" => ArithRelation::Distinct,
                "distinct" => ArithRelation::Eq,
                _ => return None,
            };
            extract_linear_atom(dag, args[0], args[1], rel)
        }
        // Not(atom): the conflict literal is the atom itself.
        SmtTerm::Not(inner) => {
            let inner_term = dag.term(*inner)?;
            match inner_term {
                SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
                    let rel = match op.as_str() {
                        "<=" => ArithRelation::Le,
                        ">=" => ArithRelation::Ge,
                        "<" => ArithRelation::Lt,
                        ">" => ArithRelation::Gt,
                        "=" => ArithRelation::Eq,
                        "distinct" => ArithRelation::Distinct,
                        _ => return None,
                    };
                    extract_linear_atom(dag, args[0], args[1], rel)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract a linear inequality from `lhs REL rhs`, normalizing to `expr REL 0`.
pub(crate) fn extract_linear_atom(
    dag: &SmtProofDag,
    lhs: SmtTermId,
    rhs: SmtTermId,
    rel: ArithRelation,
) -> Option<LinearInequality> {
    let mut lhs_coeffs = extract_linear_expr(dag, lhs)?;
    let rhs_coeffs = extract_linear_expr(dag, rhs)?;

    // Normalize: lhs - rhs REL 0
    for (var, coeff) in &rhs_coeffs.0 {
        let entry = lhs_coeffs.0.iter_mut().find(|(v, _)| v == var);
        match entry {
            Some((_, c)) => *c -= coeff,
            None => lhs_coeffs.0.push((var.clone(), -coeff)),
        }
    }
    let constant = lhs_coeffs.1 - rhs_coeffs.1;

    Some(LinearInequality {
        coefficients: lhs_coeffs.0,
        constant,
        relation: rel,
    })
}

/// Extract linear expression coefficients from a term.
///
/// Returns (variable_coefficients, constant).
pub(crate) fn extract_linear_expr(
    dag: &SmtProofDag,
    term_id: SmtTermId,
) -> Option<(Vec<(String, Rational64)>, Rational64)> {
    let term = dag.term(term_id)?;
    match term {
        SmtTerm::Var(name, _) => Some((
            vec![(name.clone(), Rational64::from_integer(1))],
            Rational64::from_integer(0),
        )),
        SmtTerm::Int(n) => Some((vec![], Rational64::from_integer(*n))),
        SmtTerm::Rational(n, d) => {
            if *d == 0 {
                None
            } else {
                Some((vec![], Rational64::new(*n, *d)))
            }
        }
        SmtTerm::App(SmtSymbol::Named(op), args) => {
            match op.as_str() {
                "+" if args.len() == 2 => {
                    let mut left = extract_linear_expr(dag, args[0])?;
                    let right = extract_linear_expr(dag, args[1])?;
                    for (var, coeff) in right.0 {
                        let entry = left.0.iter_mut().find(|(v, _)| *v == var);
                        match entry {
                            Some((_, c)) => *c += coeff,
                            None => left.0.push((var, coeff)),
                        }
                    }
                    left.1 += right.1;
                    Some(left)
                }
                "-" if args.len() == 2 => {
                    let mut left = extract_linear_expr(dag, args[0])?;
                    let right = extract_linear_expr(dag, args[1])?;
                    for (var, coeff) in right.0 {
                        let entry = left.0.iter_mut().find(|(v, _)| *v == var);
                        match entry {
                            Some((_, c)) => *c -= coeff,
                            None => left.0.push((var, -coeff)),
                        }
                    }
                    left.1 -= right.1;
                    Some(left)
                }
                "-" if args.len() == 1 => {
                    // Unary minus.
                    let mut inner = extract_linear_expr(dag, args[0])?;
                    for (_, c) in inner.0.iter_mut() {
                        *c = -*c;
                    }
                    inner.1 = -inner.1;
                    Some(inner)
                }
                "*" if args.len() == 2 => {
                    // One side must be a constant for linearity.
                    let left = extract_linear_expr(dag, args[0]);
                    let right = extract_linear_expr(dag, args[1]);
                    match (left, right) {
                        (Some((ref lv, lc)), Some((ref rv, rc))) if lv.is_empty() => {
                            // Left is constant, multiply right.
                            let scaled: Vec<_> =
                                rv.iter().map(|(v, c)| (v.clone(), lc * c)).collect();
                            Some((scaled, lc * rc))
                        }
                        (Some((ref lv, lc)), Some((ref rv, rc))) if rv.is_empty() => {
                            // Right is constant, multiply left.
                            let scaled: Vec<_> =
                                lv.iter().map(|(v, c)| (v.clone(), rc * c)).collect();
                            Some((scaled, lc * rc))
                        }
                        _ => None, // Non-linear: cannot verify.
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Compute the weighted sum of linear inequalities.
///
/// Multiplies each inequality by its coefficient and sums them.
/// All inequalities are normalized to `<= 0` or `< 0` form.
pub(crate) fn weighted_sum(
    inequalities: &[LinearInequality],
    coefficients: &[Rational64],
) -> Option<LinearInequality> {
    let zero = Rational64::from_integer(0);
    let mut sum_coeffs: Vec<(String, Rational64)> = Vec::new();
    let mut sum_constant = zero;
    let mut has_strict = false;

    for (ineq, &coeff) in inequalities.iter().zip(coefficients.iter()) {
        if coeff == zero {
            continue;
        }

        // Normalize to <= 0 or < 0 form.
        let (flip, strict) = match ineq.relation {
            ArithRelation::Le => (false, false),    // a <= 0
            ArithRelation::Lt => (false, true),     // a < 0
            ArithRelation::Ge => (true, false),     // -a <= 0
            ArithRelation::Gt => (true, true),      // -a < 0
            ArithRelation::Eq => (false, false),    // a = 0 implies a <= 0
            ArithRelation::Distinct => return None, // Can't handle disequality
        };

        let sign = if flip {
            -Rational64::from_integer(1)
        } else {
            Rational64::from_integer(1)
        };

        if strict {
            has_strict = true;
        }

        // Add weighted coefficients.
        for (var, var_coeff) in &ineq.coefficients {
            let weighted = coeff * sign * var_coeff;
            let entry = sum_coeffs.iter_mut().find(|(v, _)| v == var);
            match entry {
                Some((_, c)) => *c += weighted,
                None => sum_coeffs.push((var.clone(), weighted)),
            }
        }
        sum_constant += coeff * sign * ineq.constant;
    }

    let result_rel = if has_strict {
        ArithRelation::Lt
    } else {
        ArithRelation::Le
    };

    Some(LinearInequality {
        coefficients: sum_coeffs,
        constant: sum_constant,
        relation: result_rel,
    })
}

/// Check if a linear inequality is a contradiction.
///
/// A contradiction occurs when:
/// - All variable coefficients are zero AND
/// - The constant term violates the relation:
///   - `0 <= negative` is false
///   - `0 < 0` is false
fn is_contradiction(ineq: &LinearInequality) -> bool {
    let zero = Rational64::from_integer(0);

    // All variable coefficients must be zero.
    let all_zero = ineq.coefficients.iter().all(|(_, c)| *c == zero);

    if !all_zero {
        return false;
    }

    // Check if constant violates the relation (already normalized to <= 0 or < 0).
    match ineq.relation {
        ArithRelation::Le => ineq.constant > zero, // 0 <= c with c > 0 is contradiction
        ArithRelation::Lt => ineq.constant >= zero, // 0 < c with c >= 0 is contradiction
        ArithRelation::Ge => ineq.constant < zero,
        ArithRelation::Gt => ineq.constant <= zero,
        ArithRelation::Eq => ineq.constant != zero,
        ArithRelation::Distinct => ineq.constant == zero,
    }
}

fn ok(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::KernelVerified,
        checker: CHECKER_NAME,
        detail: None,
    }
}

fn fail(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtTerm};

    /// Helper: build a term `(op lhs rhs)` in the DAG.
    fn add_binop(dag: &mut SmtProofDag, op: &str, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named(op.to_string()),
            vec![lhs, rhs],
        ))
    }

    #[test]
    fn test_lra_farkas_simple_contradiction() {
        // Conflict: x >= 1 AND x <= 0
        // Clause (blocking): (not (>= x 1)) (not (<= x 0))
        //   i.e., (<= x 0) and (>= x 1) are the conflict.
        //   The blocking clause contains: (< x 1) and (> x 0) -- the negations.
        //
        // Actually let's build a simpler example:
        // Clause: (<= x 0) and (>= x 1)
        // As blocking clause: (not (<= x 0)) (not (>= x 1))
        // Which means: (> x 0) (< x 1)
        // But that's not contradictory by itself.
        //
        // Better approach: build the clause and check directly.
        // Clause lits (blocking): (>= x 1), (<= x 0)
        // Negating for conflict: (< x 1), (> x 0) -- that's x < 1 AND x > 0, not contradictory.
        //
        // For a real Farkas proof we need:
        // Conflict: x <= -1 AND x >= 0
        // Blocking clause: not(x <= -1) OR not(x >= 0) => (x > -1) OR (x < 0)
        //
        // Let me just test the extract and weighted sum pieces directly.

        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
        let zero = dag.add_term(SmtTerm::Int(0));
        let one = dag.add_term(SmtTerm::Int(1));

        // Conflict: x <= -1 AND x >= 0
        // As blocking clause:
        //   lit0: not(x <= -1) expressed as (> x -1), but let's use a simpler form
        //   lit1: not(x >= 0) expressed as (< x 0)
        //
        // Even simpler: build the actual Farkas proof.
        // Clause: (>= x 0), (<= x -1)  -- blocking clause
        // Negate for conflict: (< x 0), (> x -1) -- not directly useful
        //
        // Let me instead test the core functions directly.

        // Test: x + 1 <= 0 with coefficient 1, and -x <= 0 with coefficient 1
        // Sum: (x + 1) + (-x) <= 0 => 1 <= 0 => contradiction!
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(1),
            relation: ArithRelation::Le,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };

        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert!(is_contradiction(&result));
    }

    #[test]
    fn test_lra_farkas_non_contradiction() {
        // x <= 1 and -x <= 0 => 0 + 1 <= 0 which is 1 <= 0 contradiction
        // But if we use wrong coefficients: x <= 1 and -x <= -2
        // Sum: 0 + (1 + -2) <= 0 => -1 <= 0 which is NOT a contradiction.
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(1),
            relation: ArithRelation::Le,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::new(-2, 1),
            relation: ArithRelation::Le,
        };

        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert!(!is_contradiction(&result));
    }

    #[test]
    fn test_lra_farkas_strict_contradiction() {
        // x < 0 and -x <= 0 => 0 < 0 which is contradiction.
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };

        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert!(is_contradiction(&result));
    }

    #[test]
    fn test_extract_linear_expr_variable() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
        let (coeffs, constant) = extract_linear_expr(&dag, x).expect("should extract");
        assert_eq!(coeffs.len(), 1);
        assert_eq!(coeffs[0].0, "x");
        assert_eq!(coeffs[0].1, Rational64::from_integer(1));
        assert_eq!(constant, Rational64::from_integer(0));
    }

    #[test]
    fn test_extract_linear_expr_constant() {
        let mut dag = SmtProofDag::new();
        let c = dag.add_term(SmtTerm::Int(42));
        let (coeffs, constant) = extract_linear_expr(&dag, c).expect("should extract");
        assert!(coeffs.is_empty());
        assert_eq!(constant, Rational64::from_integer(42));
    }

    #[test]
    fn test_extract_linear_expr_addition() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
        let three = dag.add_term(SmtTerm::Int(3));
        let sum = add_binop(&mut dag, "+", x, three);

        let (coeffs, constant) = extract_linear_expr(&dag, sum).expect("should extract");
        assert_eq!(coeffs.len(), 1);
        assert_eq!(coeffs[0].0, "x");
        assert_eq!(coeffs[0].1, Rational64::from_integer(1));
        assert_eq!(constant, Rational64::from_integer(3));
    }

    #[test]
    fn test_extract_linear_expr_multiplication_by_constant() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
        let two = dag.add_term(SmtTerm::Int(2));
        let prod = add_binop(&mut dag, "*", two, x);

        let (coeffs, constant) = extract_linear_expr(&dag, prod).expect("should extract");
        assert_eq!(coeffs.len(), 1);
        assert_eq!(coeffs[0].0, "x");
        assert_eq!(coeffs[0].1, Rational64::from_integer(2));
        assert_eq!(constant, Rational64::from_integer(0));
    }

    #[test]
    fn test_lra_check_farkas_with_dag() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Real));
        let zero = dag.add_term(SmtTerm::Int(0));
        let neg_one = dag.add_term(SmtTerm::Int(-1));

        // Blocking clause: (<= x -1), (>= x 0)
        // These are the positive literals in the clause.
        // Negation for conflict: (> x -1) => NO, that's wrong.
        //
        // Actually in Alethe, la_generic clause literals are:
        //   The clause itself is the disjunction of bounds that's a tautology
        //   when the conflict doesn't hold.
        //
        // For a real Farkas example: conflict is x >= 1 AND x <= -1.
        // Build: not(x >= 1) as literal => x < 1
        //        not(x <= -1) as literal => x > -1

        // Let's build: (not (<= x -1)) is lit0, (not (>= x 0)) is lit1
        let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
        let ge_x_0 = add_binop(&mut dag, ">=", x, zero);
        let not_le = dag.add_term(SmtTerm::Not(le_x_neg1));
        let not_ge = dag.add_term(SmtTerm::Not(ge_x_0));

        // Clause: [not(x <= -1), not(x >= 0)]
        // Conflict (negated): x <= -1 AND x >= 0
        // Farkas: 1*(x <= -1) + 1*(x >= 0) => 1*x + 1*(-x) <= -1 + 0 => 0 <= -1 contradiction!
        let clause = vec![not_le, not_ge];
        let farkas = vec![(1, 1), (1, 1)];

        let verdict = check_lra_farkas(&dag, SmtStepId(0), &clause, &farkas);
        assert_eq!(verdict.trust_level, StepTrustLevel::KernelVerified);
    }

    #[test]
    fn test_lra_empty_clause_fails() {
        let dag = SmtProofDag::new();
        let verdict = check_lra_farkas(&dag, SmtStepId(0), &[], &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_lra_structural_non_empty() {
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let verdict = check_lra_structural(&dag, SmtStepId(0), &[t]);
        assert_eq!(verdict.trust_level, StepTrustLevel::StructurallyAccepted);
    }

    #[test]
    fn test_lra_mismatched_coefficients() {
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let verdict = check_lra_farkas(&dag, SmtStepId(0), &[t], &[(1, 1), (2, 1)]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_is_contradiction_true() {
        let ineq = LinearInequality {
            coefficients: vec![],
            constant: Rational64::from_integer(1),
            relation: ArithRelation::Le,
        };
        assert!(is_contradiction(&ineq)); // 1 <= 0 is false
    }

    #[test]
    fn test_is_contradiction_false() {
        let ineq = LinearInequality {
            coefficients: vec![],
            constant: Rational64::from_integer(-1),
            relation: ArithRelation::Le,
        };
        assert!(!is_contradiction(&ineq)); // -1 <= 0 is true (not a contradiction)
    }

    // ─── Strict inequality tests (SMT-COMP correctness) ───

    #[test]
    fn test_strict_pure_conflict_x_gt_0_x_lt_0() {
        // Conflict: x > 0 AND x < 0.
        // Normalized: -x < 0 (from x > 0, flip) AND x < 0 (from x < 0).
        // Sum with coefficients (1, 1):
        //   (-x + x) + (0 + 0) < 0 => 0 < 0 => contradiction!
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Gt,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };

        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert!(
            is_contradiction(&result),
            "x > 0 AND x < 0 must be a contradiction"
        );
    }

    #[test]
    fn test_strict_mixed_x_ge_0_x_lt_0() {
        // Conflict: x >= 0 AND x < 0.
        // Normalized: -x <= 0 (from x >= 0, flip) AND x < 0 (from x < 0).
        // has_strict = true (from x < 0).
        // Sum: (-x + x) + (0 + 0) < 0 => 0 < 0 => contradiction!
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Ge,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };

        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert_eq!(
            result.relation,
            ArithRelation::Lt,
            "strictness must propagate"
        );
        assert!(
            is_contradiction(&result),
            "x >= 0 AND x < 0 must be a contradiction"
        );
    }

    #[test]
    fn test_strict_with_equality_x_eq_5_x_lt_5() {
        // Conflict: x = 5 AND x < 5.
        // Model as three inequalities (solver splits equality):
        //   (1) x - 5 <= 0   (from x = 5, le direction, coeff=0)
        //   (2) -x + 5 <= 0  (from x = 5, ge direction, coeff=1)
        //   (3) x - 5 < 0    (from x < 5, coeff=1)
        // Sum with (0, 1, 1): (-x + 5 + x - 5) < 0 => 0 < 0 => contradiction!
        let ineq_eq_le = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(-5),
            relation: ArithRelation::Le,
        };
        let ineq_eq_ge = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(5),
            relation: ArithRelation::Le,
        };
        let ineq_strict = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(-5),
            relation: ArithRelation::Lt,
        };

        let coeffs = vec![
            Rational64::from_integer(0),
            Rational64::from_integer(1),
            Rational64::from_integer(1),
        ];
        let result =
            weighted_sum(&[ineq_eq_le, ineq_eq_ge, ineq_strict], &coeffs).expect("should compute");
        assert_eq!(result.relation, ArithRelation::Lt);
        assert!(
            is_contradiction(&result),
            "x = 5 AND x < 5 must be a contradiction"
        );
    }

    #[test]
    fn test_strict_multiple_x_gt_0_y_gt_0_sum_lt_0() {
        // Conflict: x > 0 AND y > 0 AND x + y < 0.
        // Normalized:
        //   x > 0 => -x < 0 (flip, strict)
        //   y > 0 => -y < 0 (flip, strict)
        //   x + y < 0 => x + y < 0 (already < 0 form)
        // Sum with coefficients (1, 1, 1):
        //   (-x - y + x + y) + (0 + 0 + 0) < 0 => 0 < 0 => contradiction!
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Gt,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("y".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Gt,
        };
        let ineq3 = LinearInequality {
            coefficients: vec![
                ("x".to_string(), Rational64::from_integer(1)),
                ("y".to_string(), Rational64::from_integer(1)),
            ],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };

        let coeffs = vec![
            Rational64::from_integer(1),
            Rational64::from_integer(1),
            Rational64::from_integer(1),
        ];
        let result = weighted_sum(&[ineq1, ineq2, ineq3], &coeffs).expect("should compute");
        assert_eq!(result.relation, ArithRelation::Lt);
        assert!(
            is_contradiction(&result),
            "x > 0, y > 0, x + y < 0 must be a contradiction"
        );
    }

    #[test]
    fn test_all_nonstrict_sum_zero_not_contradiction() {
        // Edge case: x >= 0 AND x <= 0.
        // This is satisfiable (x = 0), so it must NOT be a contradiction.
        // Normalized: -x <= 0 (from x >= 0) AND x <= 0 (from x <= 0).
        // Sum: (-x + x) + (0 + 0) <= 0 => 0 <= 0 which is TRUE (not contradiction).
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Ge,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };

        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert_eq!(
            result.relation,
            ArithRelation::Le,
            "all non-strict must stay non-strict"
        );
        assert!(
            !is_contradiction(&result),
            "x >= 0 AND x <= 0 is satisfiable (x = 0), NOT a contradiction"
        );
    }

    #[test]
    fn test_strict_propagation_one_strict_makes_result_strict() {
        // x <= 0 (non-strict) AND -x < 0 (strict).
        // Sum: (x - x) + 0 = 0 with strictness from second inequality.
        // Result: 0 < 0 which IS a contradiction.
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };

        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert_eq!(
            result.relation,
            ArithRelation::Lt,
            "one strict makes all strict"
        );
        assert_eq!(result.constant, Rational64::from_integer(0));
        assert!(
            is_contradiction(&result),
            "sum = 0 with strict => 0 < 0 => contradiction"
        );
    }

    #[test]
    fn test_strict_zero_coefficient_does_not_propagate() {
        // A strict inequality multiplied by coefficient 0 should not contribute strictness.
        // x <= 1 (non-strict, coeff=1) AND y < 0 (strict, coeff=0) AND -x <= -2 (non-strict, coeff=1).
        // Since y < 0 has coefficient 0, strictness should NOT propagate.
        // Sum: (x - x) + (1 + (-2)) <= 0 => -1 <= 0 which is TRUE (not contradiction).
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(1),
            relation: ArithRelation::Le,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("y".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };
        let ineq3 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(-2),
            relation: ArithRelation::Le,
        };

        let coeffs = vec![
            Rational64::from_integer(1),
            Rational64::from_integer(0), // strict but zero coefficient
            Rational64::from_integer(1),
        ];
        let result = weighted_sum(&[ineq1, ineq2, ineq3], &coeffs).expect("should compute");
        assert_eq!(
            result.relation,
            ArithRelation::Le,
            "strict with zero coeff must not propagate strictness"
        );
        assert!(!is_contradiction(&result));
    }

    #[test]
    fn test_is_contradiction_strict_zero() {
        // 0 < 0 is false, hence a contradiction.
        let ineq = LinearInequality {
            coefficients: vec![],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };
        assert!(is_contradiction(&ineq));
    }

    #[test]
    fn test_is_contradiction_nonstrict_zero() {
        // 0 <= 0 is true, NOT a contradiction.
        let ineq = LinearInequality {
            coefficients: vec![],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };
        assert!(!is_contradiction(&ineq));
    }

    #[test]
    fn test_is_contradiction_strict_negative() {
        // -1 < 0 is true, NOT a contradiction.
        let ineq = LinearInequality {
            coefficients: vec![],
            constant: Rational64::from_integer(-1),
            relation: ArithRelation::Lt,
        };
        assert!(!is_contradiction(&ineq));
    }

    // ---- AI Model-flagged adversarial soundness tests ----

    #[test]
    fn test_farkas_strict_sum_exactly_zero_must_be_invalid_if_nonstrict() {
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };
        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert_eq!(result.relation, ArithRelation::Le);
        assert_eq!(result.constant, Rational64::from_integer(0));
        assert!(result
            .coefficients
            .iter()
            .all(|(_, c)| *c == Rational64::from_integer(0)));
        assert!(
            !is_contradiction(&result),
            "all-nonstrict zero sum must stay non-strict: 0 <= 0 is not a contradiction"
        );
    }

    #[test]
    fn test_farkas_strict_sum_exactly_zero_is_contradiction_with_one_strict() {
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Le,
        };
        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert_eq!(result.relation, ArithRelation::Lt);
        assert_eq!(result.constant, Rational64::from_integer(0));
        assert!(result
            .coefficients
            .iter()
            .all(|(_, c)| *c == Rational64::from_integer(0)));
        assert!(
            is_contradiction(&result),
            "one strict input must make the zero sum strict: 0 < 0 is a contradiction"
        );
    }

    #[test]
    fn test_farkas_all_strict_positive_sum_is_contradiction() {
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(1),
            relation: ArithRelation::Lt,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(0),
            relation: ArithRelation::Lt,
        };
        let coeffs = vec![Rational64::from_integer(1), Rational64::from_integer(1)];
        let result = weighted_sum(&[ineq1, ineq2], &coeffs).expect("should compute");
        assert_eq!(result.relation, ArithRelation::Lt);
        assert_eq!(result.constant, Rational64::from_integer(1));
        assert!(result
            .coefficients
            .iter()
            .all(|(_, c)| *c == Rational64::from_integer(0)));
        assert!(
            is_contradiction(&result),
            "strict sum with positive constant must yield a contradiction"
        );
    }

    #[test]
    fn test_farkas_rational_coefficients_half() {
        let ineq1 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(1))],
            constant: Rational64::from_integer(1),
            relation: ArithRelation::Le,
        };
        let ineq2 = LinearInequality {
            coefficients: vec![("x".to_string(), Rational64::from_integer(-1))],
            constant: Rational64::from_integer(-2),
            relation: ArithRelation::Le,
        };
        let half = Rational64::new(1, 2);
        let result = weighted_sum(&[ineq1, ineq2], &[half, half]).expect("should compute");
        assert_eq!(result.relation, ArithRelation::Le);
        assert_eq!(result.constant, Rational64::new(-1, 2));
        assert!(result
            .coefficients
            .iter()
            .all(|(_, c)| *c == Rational64::from_integer(0)));
        assert!(
            !is_contradiction(&result),
            "exact rational boundary -1/2 <= 0 is true, not a contradiction"
        );
    }
}
