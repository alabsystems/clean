// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete SAT/PB executable semantics for certificate-library seeding.
//!
//! This module is intentionally small: it gives ay and future `cert_simp`
//! library work stable Rust-side heads for literal, clause, CNF, and
//! pseudo-Boolean linear evaluation without pulling in VeriPB proof replay.

use super::types::{Assignment, Cnf, CnfError, Lit, SatClause};

/// Deterministic clause evaluation summary.
///
/// `value == None` means the clause is open under a partial assignment. The
/// counters are ordered-list facts, suitable for proof factory side conditions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClauseEval {
    /// Three-valued Boolean result for the clause.
    pub value: Option<bool>,
    /// Index of the first satisfied literal, if any.
    pub first_satisfied: Option<usize>,
    /// Number of falsified literals.
    pub false_count: usize,
    /// Number of unassigned literals.
    pub unassigned_count: usize,
}

/// Deterministic CNF evaluation summary.
///
/// `value == None` means no clause is false and at least one clause is open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CnfEval {
    /// Three-valued Boolean result for the CNF.
    pub value: Option<bool>,
    /// Index of the first falsified clause, if any.
    pub first_falsified: Option<usize>,
    /// Number of satisfied clauses.
    pub satisfied_count: usize,
    /// Number of open clauses.
    pub open_count: usize,
}

/// A pseudo-Boolean linear term `coeff * lit`.
///
/// Literals use the same DIMACS convention as SAT clauses: positive integers
/// are positive literals, negative integers are negated literals, and zero is
/// invalid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PbLinearTerm {
    /// Integer coefficient multiplying the 0/1 literal value.
    pub coeff: i64,
    /// Boolean literal evaluated as 0 or 1.
    pub lit: Lit,
}

impl PbLinearTerm {
    /// Build a PB term from a coefficient and DIMACS literal.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::ZeroLiteral`] when `lit == 0`.
    pub fn new(coeff: i64, lit: i32) -> Result<Self, CnfError> {
        Ok(Self {
            coeff,
            lit: Lit::new(lit)?,
        })
    }
}

/// Evaluation summary for a pseudo-Boolean linear expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinearEval {
    /// Full sum when every term is assigned; otherwise `None`.
    pub value: Option<i64>,
    /// Sum of the terms whose literals are assigned.
    pub assigned_sum: i64,
    /// Number of terms whose literals are unassigned.
    pub unassigned_count: usize,
}

/// Cardinality constraint kind over a literal list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CardinalityKind {
    /// At least `bound` literals are true.
    AtLeast,
    /// At most `bound` literals are true.
    AtMost,
    /// Exactly `bound` literals are true.
    Exactly,
}

/// A cardinality constraint over a validated literal list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CardinalityConstraint {
    /// Validated literal list, preserving caller order.
    pub lits: Vec<Lit>,
    /// Cardinality bound.
    pub bound: usize,
    /// Constraint kind.
    pub kind: CardinalityKind,
}

impl CardinalityConstraint {
    /// Build a cardinality constraint from DIMACS literals.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::ZeroLiteral`] when any literal is zero.
    pub fn new(lits: &[i32], bound: usize, kind: CardinalityKind) -> Result<Self, CnfError> {
        Ok(Self {
            lits: lits
                .iter()
                .copied()
                .map(Lit::new)
                .collect::<Result<Vec<_>, _>>()?,
            bound,
            kind,
        })
    }
}

/// Evaluation summary for a cardinality constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CardinalityEval {
    /// Three-valued Boolean result for the constraint.
    pub value: Option<bool>,
    /// Number of currently true literals.
    pub true_count: usize,
    /// Number of currently false literals.
    pub false_count: usize,
    /// Number of currently unassigned literals.
    pub unassigned_count: usize,
}

/// Pseudo-Boolean comparison kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PbComparison {
    /// Linear sum is at least the right-hand side.
    Ge,
    /// Linear sum is at most the right-hand side.
    Le,
    /// Linear sum is equal to the right-hand side.
    Eq,
}

/// A pseudo-Boolean linear constraint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbConstraint {
    /// Validated terms, preserving caller order.
    pub terms: Vec<PbLinearTerm>,
    /// Right-hand side.
    pub rhs: i64,
    /// Comparison kind.
    pub comparison: PbComparison,
}

impl PbConstraint {
    /// Build a PB constraint from coefficient/literal pairs.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::ZeroLiteral`] when any literal is zero.
    pub fn new(terms: &[(i64, i32)], rhs: i64, comparison: PbComparison) -> Result<Self, CnfError> {
        Ok(Self {
            terms: terms
                .iter()
                .copied()
                .map(|(coeff, lit)| PbLinearTerm::new(coeff, lit))
                .collect::<Result<Vec<_>, _>>()?,
            rhs,
            comparison,
        })
    }
}

/// Evaluation summary for a pseudo-Boolean constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PbEval {
    /// Three-valued Boolean result for the comparison.
    pub value: Option<bool>,
    /// Linear expression summary.
    pub linear: LinearEval,
    /// Right-hand side used by the comparison.
    pub rhs: i64,
    /// Comparison kind.
    pub comparison: PbComparison,
}

/// Build a validated SAT clause from DIMACS literals.
///
/// # Errors
///
/// Returns [`CnfError::ZeroLiteral`] when any literal is zero.
pub fn clause_from_dimacs(lits: &[i32]) -> Result<SatClause, CnfError> {
    Ok(SatClause(
        lits.iter()
            .copied()
            .map(Lit::new)
            .collect::<Result<Vec<_>, _>>()?,
    ))
}

/// Build a validated CNF from DIMACS clauses and a declared variable count.
///
/// # Errors
///
/// Returns [`CnfError::ZeroLiteral`] for literal zero and
/// [`CnfError::VariableOutOfRange`] when a variable exceeds `num_vars`.
pub fn cnf_from_dimacs_clauses(num_vars: u32, clauses: &[Vec<i32>]) -> Result<Cnf, CnfError> {
    let mut sat_clauses = Vec::with_capacity(clauses.len());
    for clause in clauses {
        let sat_clause = clause_from_dimacs(clause)?;
        for lit in &sat_clause.0 {
            let var = lit.var().index();
            if var > num_vars {
                return Err(CnfError::VariableOutOfRange { var, max: num_vars });
            }
        }
        sat_clauses.push(sat_clause);
    }
    Ok(Cnf {
        num_vars,
        clauses: sat_clauses,
    })
}

/// Evaluate a literal under a partial assignment.
///
/// Returns `None` exactly when the variable is unassigned.
#[must_use]
pub fn eval_lit(assignment: &Assignment, lit: Lit) -> Option<bool> {
    assignment.eval_lit(lit)
}

/// Evaluate a clause as disjunction under a partial assignment.
///
/// Empty clauses evaluate to `Some(false)`.
#[must_use]
pub fn eval_clause(assignment: &Assignment, clause: &SatClause) -> Option<bool> {
    assignment.eval_clause(clause)
}

/// Evaluate a clause and return deterministic proof-friendly counters.
#[must_use]
pub fn eval_clause_detail(assignment: &Assignment, clause: &SatClause) -> ClauseEval {
    let mut false_count = 0usize;
    let mut unassigned_count = 0usize;
    for (idx, lit) in clause.0.iter().copied().enumerate() {
        match eval_lit(assignment, lit) {
            Some(true) => {
                return ClauseEval {
                    value: Some(true),
                    first_satisfied: Some(idx),
                    false_count,
                    unassigned_count,
                };
            }
            Some(false) => false_count += 1,
            None => unassigned_count += 1,
        }
    }

    ClauseEval {
        value: if unassigned_count == 0 {
            Some(false)
        } else {
            None
        },
        first_satisfied: None,
        false_count,
        unassigned_count,
    }
}

/// Evaluate a CNF as conjunction under a partial assignment.
///
/// Empty CNFs evaluate to `Some(true)`.
#[must_use]
pub fn eval_cnf(assignment: &Assignment, cnf: &Cnf) -> Option<bool> {
    assignment.eval_cnf(cnf)
}

/// Evaluate a CNF and return deterministic proof-friendly counters.
#[must_use]
pub fn eval_cnf_detail(assignment: &Assignment, cnf: &Cnf) -> CnfEval {
    let mut satisfied_count = 0usize;
    let mut open_count = 0usize;
    for (idx, clause) in cnf.clauses.iter().enumerate() {
        match eval_clause_detail(assignment, clause).value {
            Some(true) => satisfied_count += 1,
            Some(false) => {
                return CnfEval {
                    value: Some(false),
                    first_falsified: Some(idx),
                    satisfied_count,
                    open_count,
                };
            }
            None => open_count += 1,
        }
    }

    CnfEval {
        value: if open_count == 0 { Some(true) } else { None },
        first_falsified: None,
        satisfied_count,
        open_count,
    }
}

/// Evaluate one literal as a PB indicator value.
///
/// Satisfied literals contribute `Some(1)`, falsified literals contribute
/// `Some(0)`, and unassigned literals produce `None`.
#[must_use]
pub fn eval_lit_indicator(assignment: &Assignment, lit: Lit) -> Option<i64> {
    eval_lit(assignment, lit).map(|value| if value { 1 } else { 0 })
}

/// Evaluate a pseudo-Boolean linear expression.
///
/// The result is `sum(coeff_i * evalLit(a, lit_i))`. The expression is partial:
/// if any referenced variable is unassigned, evaluation returns `None`.
#[must_use]
pub fn linear_eval(assignment: &Assignment, terms: &[PbLinearTerm]) -> Option<i64> {
    terms.iter().try_fold(0i64, |acc, term| {
        eval_lit_indicator(assignment, term.lit).map(|value| acc + term.coeff * value)
    })
}

/// Evaluate a PB linear expression and return deterministic counters.
#[must_use]
pub fn linear_eval_detail(assignment: &Assignment, terms: &[PbLinearTerm]) -> LinearEval {
    let mut assigned_sum = 0i64;
    let mut unassigned_count = 0usize;
    for term in terms {
        match eval_lit_indicator(assignment, term.lit) {
            Some(value) => assigned_sum += term.coeff * value,
            None => unassigned_count += 1,
        }
    }

    LinearEval {
        value: if unassigned_count == 0 {
            Some(assigned_sum)
        } else {
            None
        },
        assigned_sum,
        unassigned_count,
    }
}

/// Evaluate a cardinality constraint under a partial assignment.
#[must_use]
pub fn eval_cardinality(
    assignment: &Assignment,
    constraint: &CardinalityConstraint,
) -> CardinalityEval {
    let mut true_count = 0usize;
    let mut false_count = 0usize;
    let mut unassigned_count = 0usize;
    for lit in &constraint.lits {
        match eval_lit(assignment, *lit) {
            Some(true) => true_count += 1,
            Some(false) => false_count += 1,
            None => unassigned_count += 1,
        }
    }

    let possible_true_count = true_count + unassigned_count;
    let value = match constraint.kind {
        CardinalityKind::AtLeast if true_count >= constraint.bound => Some(true),
        CardinalityKind::AtLeast if possible_true_count < constraint.bound => Some(false),
        CardinalityKind::AtLeast => None,
        CardinalityKind::AtMost if true_count > constraint.bound => Some(false),
        CardinalityKind::AtMost if possible_true_count <= constraint.bound => Some(true),
        CardinalityKind::AtMost => None,
        CardinalityKind::Exactly if true_count > constraint.bound => Some(false),
        CardinalityKind::Exactly if possible_true_count < constraint.bound => Some(false),
        CardinalityKind::Exactly if unassigned_count == 0 => Some(true),
        CardinalityKind::Exactly => None,
    };

    CardinalityEval {
        value,
        true_count,
        false_count,
        unassigned_count,
    }
}

/// Evaluate a pseudo-Boolean constraint under a partial assignment.
///
/// Because coefficients may be negative, the comparison is decided only when
/// every term is assigned. This intentionally fail-closes for partial
/// assignments instead of deriving coefficient-bound implications here.
#[must_use]
pub fn eval_pb_constraint(assignment: &Assignment, constraint: &PbConstraint) -> PbEval {
    let linear = linear_eval_detail(assignment, &constraint.terms);
    let value = linear.value.map(|sum| match constraint.comparison {
        PbComparison::Ge => sum >= constraint.rhs,
        PbComparison::Le => sum <= constraint.rhs,
        PbComparison::Eq => sum == constraint.rhs,
    });

    PbEval {
        value,
        linear,
        rhs: constraint.rhs,
        comparison: constraint.comparison,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::types::Var;

    fn fixture_assignment() -> Assignment {
        let mut assignment = Assignment::new(4);
        assignment.set(Var(1), true);
        assignment.set(Var(2), false);
        assignment.set(Var(3), true);
        assignment
    }

    #[test]
    fn eval_lit_fixture_respects_polarity_and_unassigned_variables() {
        let assignment = fixture_assignment();

        assert_eq!(eval_lit(&assignment, Lit::from_dimacs(1)), Some(true));
        assert_eq!(eval_lit(&assignment, Lit::from_dimacs(-1)), Some(false));
        assert_eq!(eval_lit(&assignment, Lit::from_dimacs(2)), Some(false));
        assert_eq!(eval_lit(&assignment, Lit::from_dimacs(-2)), Some(true));
        assert_eq!(eval_lit(&assignment, Lit::from_dimacs(4)), None);
    }

    #[test]
    fn eval_clause_fixture_handles_satisfied_conflicting_and_open_clauses() {
        let assignment = fixture_assignment();

        let satisfied = SatClause::from_dimacs(&[-1, -2]);
        let falsified = SatClause::from_dimacs(&[-1, 2]);
        let open = SatClause::from_dimacs(&[-1, 4]);
        let empty = SatClause::from_dimacs(&[]);

        assert_eq!(eval_clause(&assignment, &satisfied), Some(true));
        assert_eq!(eval_clause(&assignment, &falsified), Some(false));
        assert_eq!(eval_clause(&assignment, &open), None);
        assert_eq!(eval_clause(&assignment, &empty), Some(false));
    }

    #[test]
    fn eval_clause_detail_reports_first_witness_and_counts() {
        let assignment = fixture_assignment();
        let satisfied = SatClause::from_dimacs(&[-1, 4, -2, 3]);
        let open = SatClause::from_dimacs(&[-1, 2, 4]);
        let empty = SatClause::from_dimacs(&[]);

        assert_eq!(
            eval_clause_detail(&assignment, &satisfied),
            ClauseEval {
                value: Some(true),
                first_satisfied: Some(2),
                false_count: 1,
                unassigned_count: 1,
            }
        );
        assert_eq!(
            eval_clause_detail(&assignment, &open),
            ClauseEval {
                value: None,
                first_satisfied: None,
                false_count: 2,
                unassigned_count: 1,
            }
        );
        assert_eq!(
            eval_clause_detail(&assignment, &empty),
            ClauseEval {
                value: Some(false),
                first_satisfied: None,
                false_count: 0,
                unassigned_count: 0,
            }
        );
    }

    #[test]
    fn eval_cnf_fixture_handles_true_false_open_and_empty_formulas() {
        let assignment = fixture_assignment();

        let true_cnf = Cnf {
            num_vars: 4,
            clauses: vec![
                SatClause::from_dimacs(&[1, 2]),
                SatClause::from_dimacs(&[-2, 3]),
            ],
        };
        let false_cnf = Cnf {
            num_vars: 4,
            clauses: vec![
                SatClause::from_dimacs(&[1]),
                SatClause::from_dimacs(&[-1, 2]),
            ],
        };
        let open_cnf = Cnf {
            num_vars: 4,
            clauses: vec![
                SatClause::from_dimacs(&[1]),
                SatClause::from_dimacs(&[4, 2]),
            ],
        };
        let empty_cnf = Cnf {
            num_vars: 0,
            clauses: vec![],
        };

        assert_eq!(eval_cnf(&assignment, &true_cnf), Some(true));
        assert_eq!(eval_cnf(&assignment, &false_cnf), Some(false));
        assert_eq!(eval_cnf(&assignment, &open_cnf), None);
        assert_eq!(eval_cnf(&assignment, &empty_cnf), Some(true));
    }

    #[test]
    fn eval_cnf_detail_reports_first_false_and_open_counts() {
        let assignment = fixture_assignment();
        let false_cnf = Cnf {
            num_vars: 4,
            clauses: vec![
                SatClause::from_dimacs(&[1]),
                SatClause::from_dimacs(&[4, 2]),
                SatClause::from_dimacs(&[-1, 2]),
            ],
        };
        let open_cnf = Cnf {
            num_vars: 4,
            clauses: vec![
                SatClause::from_dimacs(&[1]),
                SatClause::from_dimacs(&[4, 2]),
            ],
        };

        assert_eq!(
            eval_cnf_detail(&assignment, &false_cnf),
            CnfEval {
                value: Some(false),
                first_falsified: Some(2),
                satisfied_count: 1,
                open_count: 1,
            }
        );
        assert_eq!(
            eval_cnf_detail(&assignment, &open_cnf),
            CnfEval {
                value: None,
                first_falsified: None,
                satisfied_count: 1,
                open_count: 1,
            }
        );
    }

    #[test]
    fn linear_eval_fixture_sums_weighted_literal_indicators() {
        let assignment = fixture_assignment();
        let terms = [
            PbLinearTerm::new(5, 1).expect("valid literal"),
            PbLinearTerm::new(7, -2).expect("valid literal"),
            PbLinearTerm::new(-3, -3).expect("valid literal"),
            PbLinearTerm::new(11, 2).expect("valid literal"),
        ];

        assert_eq!(linear_eval(&assignment, &terms), Some(12));
    }

    #[test]
    fn linear_eval_fixture_is_partial_on_unassigned_literals() {
        let assignment = fixture_assignment();
        let terms = [
            PbLinearTerm::new(5, 1).expect("valid literal"),
            PbLinearTerm::new(13, -4).expect("valid literal"),
        ];

        assert_eq!(linear_eval(&assignment, &terms), None);
    }

    #[test]
    fn linear_eval_detail_reports_partial_assigned_sum() {
        let assignment = fixture_assignment();
        let terms = [
            PbLinearTerm::new(5, 1).expect("valid literal"),
            PbLinearTerm::new(7, -2).expect("valid literal"),
            PbLinearTerm::new(13, -4).expect("valid literal"),
            PbLinearTerm::new(-3, 2).expect("valid literal"),
        ];

        assert_eq!(
            linear_eval_detail(&assignment, &terms),
            LinearEval {
                value: None,
                assigned_sum: 12,
                unassigned_count: 1,
            }
        );
    }

    #[test]
    fn cardinality_eval_decides_when_partial_bounds_force_result() {
        let assignment = fixture_assignment();
        let at_least = CardinalityConstraint::new(&[1, 2, 4], 2, CardinalityKind::AtLeast).unwrap();
        let at_most = CardinalityConstraint::new(&[1, -2, 4], 1, CardinalityKind::AtMost).unwrap();
        let exactly_open =
            CardinalityConstraint::new(&[1, 2, 4], 2, CardinalityKind::Exactly).unwrap();
        let exactly_false =
            CardinalityConstraint::new(&[1, -2, 3], 2, CardinalityKind::Exactly).unwrap();
        let empty_true = CardinalityConstraint::new(&[], 0, CardinalityKind::Exactly).unwrap();

        assert_eq!(eval_cardinality(&assignment, &at_least).value, None);
        assert_eq!(eval_cardinality(&assignment, &at_most).value, Some(false));
        assert_eq!(eval_cardinality(&assignment, &exactly_open).value, None);
        assert_eq!(
            eval_cardinality(&assignment, &exactly_false).value,
            Some(false)
        );
        assert_eq!(
            eval_cardinality(&assignment, &empty_true),
            CardinalityEval {
                value: Some(true),
                true_count: 0,
                false_count: 0,
                unassigned_count: 0,
            }
        );
    }

    #[test]
    fn pb_constraint_eval_is_total_only_when_all_terms_are_assigned() {
        let assignment = fixture_assignment();
        let ge = PbConstraint::new(&[(2, 1), (3, -2), (5, 2)], 5, PbComparison::Ge).unwrap();
        let le = PbConstraint::new(&[(2, 1), (3, -2), (5, 2)], 4, PbComparison::Le).unwrap();
        let eq = PbConstraint::new(&[(2, 1), (3, -2), (5, 2)], 5, PbComparison::Eq).unwrap();
        let open = PbConstraint::new(&[(2, 1), (3, 4)], 2, PbComparison::Eq).unwrap();

        assert_eq!(eval_pb_constraint(&assignment, &ge).value, Some(true));
        assert_eq!(eval_pb_constraint(&assignment, &le).value, Some(false));
        assert_eq!(eval_pb_constraint(&assignment, &eq).value, Some(true));
        assert_eq!(
            eval_pb_constraint(&assignment, &open),
            PbEval {
                value: None,
                linear: LinearEval {
                    value: None,
                    assigned_sum: 2,
                    unassigned_count: 1,
                },
                rhs: 2,
                comparison: PbComparison::Eq,
            }
        );
    }

    #[test]
    fn dimacs_builders_reject_invalid_literals_and_out_of_range_variables() {
        assert_eq!(clause_from_dimacs(&[1, 0, -2]), Err(CnfError::ZeroLiteral));
        assert_eq!(
            cnf_from_dimacs_clauses(2, &[vec![1], vec![-3]]).unwrap_err(),
            CnfError::VariableOutOfRange { var: 3, max: 2 }
        );
        assert_eq!(
            cnf_from_dimacs_clauses(2, &[vec![1], vec![0]]).unwrap_err(),
            CnfError::ZeroLiteral
        );
        assert!(cnf_from_dimacs_clauses(2, &[vec![1, -2], vec![]])
            .expect("valid cnf")
            .is_valid());
    }

    #[test]
    fn cardinality_and_pb_builders_reject_zero_literals() {
        assert_eq!(
            CardinalityConstraint::new(&[1, 0], 1, CardinalityKind::AtLeast),
            Err(CnfError::ZeroLiteral)
        );
        assert_eq!(
            PbConstraint::new(&[(1, 1), (2, 0)], 1, PbComparison::Ge),
            Err(CnfError::ZeroLiteral)
        );
    }

    #[test]
    fn linear_term_rejects_zero_literal() {
        assert_eq!(PbLinearTerm::new(1, 0), Err(CnfError::ZeroLiteral));
    }
}
