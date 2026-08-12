// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Skolem-style strategy verification for small prenex QBF formulas.
//!
//! The checker is deliberately explicit: every existential variable must have
//! a total truth-table strategy over exactly the preceding universal variables,
//! and the matrix is evaluated on every universal assignment.
//!
//! Every failure path returns [`StrategyError`]; there is no "accept on
//! doubt" branch. A malformed prefix, a missing or mis-shaped Skolem table,
//! an unbound matrix variable, or a single losing universal assignment all
//! reject.

use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;

/// Quantifier kind in a prenex QBF prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    /// Universal variable.
    Universal,
    /// Existential variable.
    Existential,
}

/// One quantified variable in the formula prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedVar {
    /// Variable name.
    pub name: String,
    /// Quantifier kind.
    pub quantifier: Quantifier,
}

impl QuantifiedVar {
    /// Construct a universal variable.
    #[must_use]
    pub fn universal(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            quantifier: Quantifier::Universal,
        }
    }

    /// Construct an existential variable.
    #[must_use]
    pub fn existential(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            quantifier: Quantifier::Existential,
        }
    }
}

/// Boolean matrix expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    /// Boolean constant.
    Const(bool),
    /// Variable reference.
    Var(String),
    /// Negation.
    Not(Box<BoolExpr>),
    /// Conjunction.
    And(Box<BoolExpr>, Box<BoolExpr>),
    /// Disjunction.
    Or(Box<BoolExpr>, Box<BoolExpr>),
    /// Equivalence.
    Iff(Box<BoolExpr>, Box<BoolExpr>),
}

impl BoolExpr {
    /// Boolean variable.
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    /// Negation.
    #[must_use]
    pub fn negate(inner: Self) -> Self {
        Self::Not(Box::new(inner))
    }

    /// Conjunction.
    #[must_use]
    pub fn and(lhs: Self, rhs: Self) -> Self {
        Self::And(Box::new(lhs), Box::new(rhs))
    }

    /// Disjunction.
    #[must_use]
    pub fn or(lhs: Self, rhs: Self) -> Self {
        Self::Or(Box::new(lhs), Box::new(rhs))
    }

    /// Equivalence.
    #[must_use]
    pub fn iff(lhs: Self, rhs: Self) -> Self {
        Self::Iff(Box::new(lhs), Box::new(rhs))
    }

    /// Evaluate under a total assignment.
    ///
    /// SOUNDNESS: an unbound variable is an error, never a default `false`.
    /// Defaulting would let a strategy "win" on a matrix it never constrained.
    fn eval(&self, assignment: &BTreeMap<String, bool>) -> Result<bool, StrategyError> {
        match self {
            Self::Const(value) => Ok(*value),
            Self::Var(name) => assignment
                .get(name)
                .copied()
                .ok_or_else(|| StrategyError::UnassignedMatrixVariable { name: name.clone() }),
            Self::Not(inner) => Ok(!inner.eval(assignment)?),
            Self::And(lhs, rhs) => Ok(lhs.eval(assignment)? && rhs.eval(assignment)?),
            Self::Or(lhs, rhs) => Ok(lhs.eval(assignment)? || rhs.eval(assignment)?),
            Self::Iff(lhs, rhs) => Ok(lhs.eval(assignment)? == rhs.eval(assignment)?),
        }
    }
}

/// Prenex QBF formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QbfFormula {
    /// Quantifier prefix.
    pub prefix: Vec<QuantifiedVar>,
    /// Boolean matrix.
    pub matrix: BoolExpr,
}

impl QbfFormula {
    /// Construct a QBF formula.
    #[must_use]
    pub fn new(prefix: Vec<QuantifiedVar>, matrix: BoolExpr) -> Self {
        Self { prefix, matrix }
    }
}

/// One row in a Skolem truth table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StrategyCase {
    /// Values for the strategy dependencies, in dependency order.
    pub inputs: Vec<bool>,
    /// Existential value returned for those dependency values.
    pub output: bool,
}

impl StrategyCase {
    /// Construct one table row.
    #[must_use]
    pub fn new(inputs: Vec<bool>, output: bool) -> Self {
        Self { inputs, output }
    }
}

/// Truth-table Skolem function for one existential variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkolemFunction {
    /// Universal variables this function depends on.
    pub dependencies: Vec<String>,
    /// Total truth table.
    pub table: Vec<StrategyCase>,
}

impl SkolemFunction {
    /// Construct a Skolem function.
    #[must_use]
    pub fn new(dependencies: Vec<String>, table: Vec<StrategyCase>) -> Self {
        Self {
            dependencies,
            table,
        }
    }

    /// Look up the existential value for one universal assignment.
    ///
    /// SOUNDNESS: a missing dependency or a missing table row rejects. The
    /// table must be total over its declared dependencies (enforced by
    /// [`validate_truth_table`] before this runs), so this path only fires on
    /// an internally inconsistent certificate.
    fn eval(&self, universal_assignment: &BTreeMap<String, bool>) -> Result<bool, StrategyError> {
        let key: Vec<bool> = self
            .dependencies
            .iter()
            .map(|name| {
                universal_assignment
                    .get(name)
                    .copied()
                    .ok_or_else(|| StrategyError::UnknownDependency { name: name.clone() })
            })
            .collect::<Result<_, _>>()?;

        self.table
            .iter()
            .find(|case| case.inputs == key)
            .map(|case| case.output)
            .ok_or(StrategyError::MissingStrategyCase { inputs: key })
    }
}

/// Skolem strategy keyed by existential variable name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QbfStrategy {
    /// Strategy functions for existential variables.
    pub functions: BTreeMap<String, SkolemFunction>,
}

impl QbfStrategy {
    /// Construct a strategy from `(existential_name, function)` pairs.
    #[must_use]
    pub fn new(functions: impl IntoIterator<Item = (String, SkolemFunction)>) -> Self {
        Self {
            functions: functions.into_iter().collect(),
        }
    }
}

/// Successful verification metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StrategyVerification {
    /// Number of universal assignments checked.
    pub checked_universal_assignments: usize,
}

/// QBF strategy verification failures.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum StrategyError {
    /// Prefix contains the same variable twice.
    #[error("duplicate variable in QBF prefix: {name}")]
    DuplicatePrefixVariable {
        /// Duplicate variable name.
        name: String,
    },
    /// Strategy is missing an existential variable.
    #[error("missing strategy function for existential variable {name}")]
    MissingStrategyFunction {
        /// Existential variable name.
        name: String,
    },
    /// Strategy contains an entry for a variable that is not existential.
    #[error("unexpected strategy function for non-existential variable {name}")]
    UnexpectedStrategyFunction {
        /// Variable name.
        name: String,
    },
    /// Strategy has the wrong dependency arity.
    #[error("wrong strategy arity for {name}: expected {expected}, got {got}")]
    WrongArity {
        /// Existential variable name.
        name: String,
        /// Expected number of dependencies.
        expected: usize,
        /// Actual number of dependencies.
        got: usize,
    },
    /// Strategy dependencies must exactly match preceding universals.
    #[error("dependency mismatch for {name}: expected {expected:?}, got {got:?}")]
    DependencyMismatch {
        /// Existential variable name.
        name: String,
        /// Expected dependencies.
        expected: Vec<String>,
        /// Actual dependencies.
        got: Vec<String>,
    },
    /// Truth-table row has the wrong input arity.
    #[error("strategy row for {name} has arity {got}, expected {expected}")]
    StrategyCaseWrongArity {
        /// Existential variable name.
        name: String,
        /// Expected row width.
        expected: usize,
        /// Actual row width.
        got: usize,
    },
    /// Truth-table row appears more than once.
    #[error("duplicate strategy row for {name}: {inputs:?}")]
    DuplicateStrategyCase {
        /// Existential variable name.
        name: String,
        /// Duplicate row inputs.
        inputs: Vec<bool>,
    },
    /// Truth table is not total over its dependency inputs.
    #[error("strategy table for {name} is incomplete: expected {expected}, got {got}")]
    IncompleteStrategyTable {
        /// Existential variable name.
        name: String,
        /// Expected row count.
        expected: usize,
        /// Actual row count.
        got: usize,
    },
    /// Formula has too many universal assignments for exhaustive checking.
    #[error("too many variables to exhaustively enumerate: {count}")]
    TooManyAssignments {
        /// Variable count.
        count: usize,
    },
    /// Dependency was not bound by the universal assignment.
    #[error("unknown dependency {name}")]
    UnknownDependency {
        /// Missing dependency name.
        name: String,
    },
    /// A table row is missing for the current dependency values.
    #[error("missing strategy table row for inputs {inputs:?}")]
    MissingStrategyCase {
        /// Missing input row.
        inputs: Vec<bool>,
    },
    /// The matrix referenced a variable without an assigned value.
    #[error("unassigned matrix variable {name}")]
    UnassignedMatrixVariable {
        /// Variable name.
        name: String,
    },
    /// Strategy loses on one universal assignment.
    #[error("strategy loses on universal assignment {assignment:?}")]
    LosingUniversalAssignment {
        /// Universal assignment that falsifies the matrix.
        assignment: Vec<(String, bool)>,
    },
}

/// Verify a Skolem strategy against a prenex QBF formula.
///
/// Accepts only when the strategy is well shaped (one total truth table per
/// existential variable, over exactly the universals that precede it) AND the
/// matrix evaluates to `true` on every one of the `2^n` universal assignments.
/// Any other outcome is a [`StrategyError`].
pub fn verify_qbf_strategy(
    formula: &QbfFormula,
    strategy: &QbfStrategy,
) -> Result<StrategyVerification, StrategyError> {
    let (universal_names, existential_expected_deps) = validate_prefix(formula)?;
    validate_matrix_vars(formula)?;
    validate_strategy_shape(strategy, &existential_expected_deps)?;

    let assignments = enumerate_assignments(&universal_names)?;
    let checked_universal_assignments = assignments.len();

    for universal_assignment in assignments {
        let mut full_assignment = universal_assignment.clone();
        for var in &formula.prefix {
            if var.quantifier == Quantifier::Existential {
                let func = strategy.functions.get(&var.name).ok_or_else(|| {
                    StrategyError::MissingStrategyFunction {
                        name: var.name.clone(),
                    }
                })?;
                let value = func.eval(&universal_assignment)?;
                full_assignment.insert(var.name.clone(), value);
            }
        }

        if !formula.matrix.eval(&full_assignment)? {
            return Err(StrategyError::LosingUniversalAssignment {
                // Every name in `universal_names` is a key of
                // `universal_assignment` by construction in
                // `enumerate_assignments`; `filter_map` keeps the diagnostic
                // total instead of indexing.
                assignment: universal_names
                    .iter()
                    .filter_map(|name| {
                        universal_assignment
                            .get(name)
                            .map(|value| (name.clone(), *value))
                    })
                    .collect(),
            });
        }
    }

    Ok(StrategyVerification {
        checked_universal_assignments,
    })
}

/// Collect the universal names and, for each existential, the universals that
/// legally precede it.
///
/// SOUNDNESS: a repeated prefix name rejects. Shadowing would make
/// "preceding universals" ambiguous and let a strategy read a variable it must
/// not depend on.
fn validate_prefix(
    formula: &QbfFormula,
) -> Result<(Vec<String>, BTreeMap<String, Vec<String>>), StrategyError> {
    let mut seen = BTreeSet::new();
    let mut universals_so_far = Vec::new();
    let mut existential_expected_deps = BTreeMap::new();

    for var in &formula.prefix {
        if !seen.insert(var.name.clone()) {
            return Err(StrategyError::DuplicatePrefixVariable {
                name: var.name.clone(),
            });
        }

        match var.quantifier {
            Quantifier::Universal => universals_so_far.push(var.name.clone()),
            Quantifier::Existential => {
                existential_expected_deps.insert(var.name.clone(), universals_so_far.clone());
            }
        }
    }

    Ok((universals_so_far, existential_expected_deps))
}

/// Reject a matrix that mentions a variable the prefix does not bind.
///
/// SOUNDNESS: [`BoolExpr::eval`] uses Rust's short-circuiting `&&`/`||`, so a
/// free variable in an unevaluated operand (`e or free` with `e = true`) would
/// never be read and the ill-formed formula would be ACCEPTED. This up-front
/// scan makes that case reject deterministically; the `eval` arm remains as
/// defence in depth.
fn validate_matrix_vars(formula: &QbfFormula) -> Result<(), StrategyError> {
    let bound: BTreeSet<&str> = formula.prefix.iter().map(|var| var.name.as_str()).collect();

    let mut occurring = BTreeSet::new();
    collect_matrix_vars(&formula.matrix, &mut occurring);

    for name in occurring {
        if !bound.contains(name) {
            return Err(StrategyError::UnassignedMatrixVariable {
                name: name.to_string(),
            });
        }
    }

    Ok(())
}

/// Collect every variable name occurring in `expr`.
fn collect_matrix_vars<'expr>(expr: &'expr BoolExpr, out: &mut BTreeSet<&'expr str>) {
    match expr {
        BoolExpr::Const(_) => {}
        BoolExpr::Var(name) => {
            out.insert(name.as_str());
        }
        BoolExpr::Not(inner) => collect_matrix_vars(inner, out),
        BoolExpr::And(lhs, rhs) | BoolExpr::Or(lhs, rhs) | BoolExpr::Iff(lhs, rhs) => {
            collect_matrix_vars(lhs, out);
            collect_matrix_vars(rhs, out);
        }
    }
}

/// Check the strategy covers exactly the existential variables, with exactly
/// the expected dependency list and a total truth table for each.
fn validate_strategy_shape(
    strategy: &QbfStrategy,
    expected_deps: &BTreeMap<String, Vec<String>>,
) -> Result<(), StrategyError> {
    for name in strategy.functions.keys() {
        if !expected_deps.contains_key(name) {
            return Err(StrategyError::UnexpectedStrategyFunction { name: name.clone() });
        }
    }

    for (name, expected) in expected_deps {
        let func = strategy
            .functions
            .get(name)
            .ok_or_else(|| StrategyError::MissingStrategyFunction { name: name.clone() })?;
        if func.dependencies.len() != expected.len() {
            return Err(StrategyError::WrongArity {
                name: name.clone(),
                expected: expected.len(),
                got: func.dependencies.len(),
            });
        }
        // SOUNDNESS: exact list equality, not set containment. A Skolem
        // function that reads a LATER universal would be a cheat, and one that
        // permutes its dependency order would mis-index its own truth table.
        if &func.dependencies != expected {
            return Err(StrategyError::DependencyMismatch {
                name: name.clone(),
                expected: expected.clone(),
                got: func.dependencies.clone(),
            });
        }
        validate_truth_table(name, func)?;
    }

    Ok(())
}

/// Check one Skolem truth table is total and unambiguous: exactly `2^arity`
/// rows, each of width `arity`, with no duplicate input row.
fn validate_truth_table(name: &str, func: &SkolemFunction) -> Result<(), StrategyError> {
    let arity = func.dependencies.len();
    let expected_rows = checked_power_of_two(arity)?;
    if func.table.len() != expected_rows {
        return Err(StrategyError::IncompleteStrategyTable {
            name: name.to_string(),
            expected: expected_rows,
            got: func.table.len(),
        });
    }

    let mut seen = BTreeSet::new();
    for case in &func.table {
        if case.inputs.len() != arity {
            return Err(StrategyError::StrategyCaseWrongArity {
                name: name.to_string(),
                expected: arity,
                got: case.inputs.len(),
            });
        }
        if !seen.insert(case.inputs.clone()) {
            return Err(StrategyError::DuplicateStrategyCase {
                name: name.to_string(),
                inputs: case.inputs.clone(),
            });
        }
    }
    Ok(())
}

/// Enumerate all `2^n` assignments over `names`.
fn enumerate_assignments(names: &[String]) -> Result<Vec<BTreeMap<String, bool>>, StrategyError> {
    let count = checked_power_of_two(names.len())?;
    let mut out = Vec::with_capacity(count);

    for mask in 0..count {
        let mut assignment = BTreeMap::new();
        for (bit, name) in names.iter().enumerate() {
            assignment.insert(name.clone(), (mask & (1usize << bit)) != 0);
        }
        out.push(assignment);
    }

    Ok(out)
}

/// `2^count`, rejecting rather than wrapping when the shift would overflow.
fn checked_power_of_two(count: usize) -> Result<usize, StrategyError> {
    let bits = usize::BITS as usize;
    if count >= bits {
        return Err(StrategyError::TooManyAssignments { count });
    }
    Ok(1usize << count)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn copy_u_strategy() -> QbfStrategy {
        QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(
                vec!["u".to_string()],
                vec![
                    StrategyCase::new(vec![false], false),
                    StrategyCase::new(vec![true], true),
                ],
            ),
        )])
    }

    fn copy_formula() -> QbfFormula {
        QbfFormula::new(
            vec![
                QuantifiedVar::universal("u"),
                QuantifiedVar::existential("e"),
            ],
            BoolExpr::iff(BoolExpr::var("e"), BoolExpr::var("u")),
        )
    }

    #[test]
    fn accepts_valid_copy_strategy() {
        let result = verify_qbf_strategy(&copy_formula(), &copy_u_strategy())
            .expect("copy strategy should satisfy forall u exists e. e iff u");
        assert_eq!(result.checked_universal_assignments, 2);
    }

    #[test]
    fn rejects_strategy_that_loses_one_universal_branch() {
        let bad = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(
                vec!["u".to_string()],
                vec![
                    StrategyCase::new(vec![false], false),
                    StrategyCase::new(vec![true], false),
                ],
            ),
        )]);

        let err = verify_qbf_strategy(&copy_formula(), &bad)
            .expect_err("constant-false strategy loses when u is true");
        assert!(matches!(
            err,
            StrategyError::LosingUniversalAssignment { assignment }
                if assignment == vec![("u".to_string(), true)]
        ));
    }

    #[test]
    fn rejects_wrong_arity_strategy() {
        let bad = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(vec![], vec![StrategyCase::new(vec![], true)]),
        )]);

        let err = verify_qbf_strategy(&copy_formula(), &bad)
            .expect_err("strategy must depend on preceding universal u");
        assert!(matches!(
            err,
            StrategyError::WrongArity {
                name,
                expected: 1,
                got: 0
            } if name == "e"
        ));
    }

    #[test]
    fn rejects_duplicate_prefix_variable() {
        let formula = QbfFormula::new(
            vec![
                QuantifiedVar::universal("u"),
                QuantifiedVar::existential("u"),
            ],
            BoolExpr::var("u"),
        );

        let err = verify_qbf_strategy(&formula, &copy_u_strategy())
            .expect_err("a shadowed prefix name must be rejected");
        assert!(matches!(
            err,
            StrategyError::DuplicatePrefixVariable { name } if name == "u"
        ));
    }

    #[test]
    fn rejects_missing_strategy_function() {
        let empty = QbfStrategy::new([]);
        let err = verify_qbf_strategy(&copy_formula(), &empty)
            .expect_err("every existential needs a strategy function");
        assert!(matches!(
            err,
            StrategyError::MissingStrategyFunction { name } if name == "e"
        ));
    }

    #[test]
    fn rejects_strategy_for_non_existential_variable() {
        let bad = QbfStrategy::new([
            (
                "e".to_string(),
                SkolemFunction::new(
                    vec!["u".to_string()],
                    vec![
                        StrategyCase::new(vec![false], false),
                        StrategyCase::new(vec![true], true),
                    ],
                ),
            ),
            (
                "u".to_string(),
                SkolemFunction::new(vec![], vec![StrategyCase::new(vec![], true)]),
            ),
        ]);

        let err = verify_qbf_strategy(&copy_formula(), &bad)
            .expect_err("a strategy for a universal variable must be rejected");
        assert!(matches!(
            err,
            StrategyError::UnexpectedStrategyFunction { name } if name == "u"
        ));
    }

    #[test]
    fn rejects_dependency_on_later_universal() {
        // exists e. forall u. (e iff u) is false; a strategy that "reads" the
        // later universal u must not be accepted.
        let formula = QbfFormula::new(
            vec![
                QuantifiedVar::existential("e"),
                QuantifiedVar::universal("u"),
            ],
            BoolExpr::iff(BoolExpr::var("e"), BoolExpr::var("u")),
        );

        let err = verify_qbf_strategy(&formula, &copy_u_strategy())
            .expect_err("e precedes u, so e must not depend on u");
        assert!(matches!(
            err,
            StrategyError::WrongArity {
                name,
                expected: 0,
                got: 1
            } if name == "e"
        ));
    }

    #[test]
    fn rejects_permuted_dependency_order() {
        let formula = QbfFormula::new(
            vec![
                QuantifiedVar::universal("a"),
                QuantifiedVar::universal("b"),
                QuantifiedVar::existential("e"),
            ],
            BoolExpr::Const(true),
        );
        let bad = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(
                vec!["b".to_string(), "a".to_string()],
                vec![
                    StrategyCase::new(vec![false, false], true),
                    StrategyCase::new(vec![false, true], true),
                    StrategyCase::new(vec![true, false], true),
                    StrategyCase::new(vec![true, true], true),
                ],
            ),
        )]);

        let err = verify_qbf_strategy(&formula, &bad)
            .expect_err("dependency order must match the prefix order");
        assert!(matches!(
            err,
            StrategyError::DependencyMismatch { name, .. } if name == "e"
        ));
    }

    #[test]
    fn rejects_incomplete_truth_table() {
        let bad = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(
                vec!["u".to_string()],
                vec![StrategyCase::new(vec![true], true)],
            ),
        )]);

        let err = verify_qbf_strategy(&copy_formula(), &bad)
            .expect_err("a partial truth table must be rejected");
        assert!(matches!(
            err,
            StrategyError::IncompleteStrategyTable {
                name,
                expected: 2,
                got: 1
            } if name == "e"
        ));
    }

    #[test]
    fn rejects_duplicate_truth_table_row() {
        let bad = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(
                vec!["u".to_string()],
                vec![
                    StrategyCase::new(vec![true], true),
                    StrategyCase::new(vec![true], false),
                ],
            ),
        )]);

        let err = verify_qbf_strategy(&copy_formula(), &bad)
            .expect_err("an ambiguous truth table must be rejected");
        assert!(matches!(
            err,
            StrategyError::DuplicateStrategyCase { name, inputs }
                if name == "e" && inputs == vec![true]
        ));
    }

    #[test]
    fn rejects_truth_table_row_of_wrong_width() {
        let formula = QbfFormula::new(
            vec![
                QuantifiedVar::universal("a"),
                QuantifiedVar::universal("b"),
                QuantifiedVar::existential("e"),
            ],
            BoolExpr::Const(true),
        );
        let bad = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(
                vec!["a".to_string(), "b".to_string()],
                vec![
                    StrategyCase::new(vec![false, false], true),
                    StrategyCase::new(vec![false, true], true),
                    StrategyCase::new(vec![true, false], true),
                    // Wrong width: three inputs for a binary table.
                    StrategyCase::new(vec![true, true, true], true),
                ],
            ),
        )]);

        let err = verify_qbf_strategy(&formula, &bad)
            .expect_err("a row whose width differs from the arity must be rejected");
        assert!(matches!(
            err,
            StrategyError::StrategyCaseWrongArity {
                name,
                expected: 2,
                got: 3
            } if name == "e"
        ));
    }

    #[test]
    fn rejects_matrix_variable_outside_the_prefix() {
        let formula = QbfFormula::new(
            vec![
                QuantifiedVar::universal("u"),
                QuantifiedVar::existential("e"),
            ],
            BoolExpr::and(BoolExpr::var("e"), BoolExpr::var("free")),
        );

        let err = verify_qbf_strategy(&formula, &copy_u_strategy())
            .expect_err("an unbound matrix variable must reject, not default to false");
        assert!(matches!(
            err,
            StrategyError::UnassignedMatrixVariable { name } if name == "free"
        ));
    }

    #[test]
    fn rejects_free_variable_hidden_behind_short_circuit() {
        // `e or free` with a constant-true strategy for `e` never *evaluates*
        // `free`, so the short-circuit alone would accept an ill-formed
        // formula. The up-front prefix scan must reject it.
        let formula = QbfFormula::new(
            vec![QuantifiedVar::existential("e")],
            BoolExpr::or(BoolExpr::var("e"), BoolExpr::var("free")),
        );
        let strategy = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(vec![], vec![StrategyCase::new(vec![], true)]),
        )]);

        let err = verify_qbf_strategy(&formula, &strategy)
            .expect_err("a free matrix variable must reject even when short-circuited away");
        assert!(matches!(
            err,
            StrategyError::UnassignedMatrixVariable { name } if name == "free"
        ));
    }

    #[test]
    fn rejects_prefix_too_wide_to_enumerate() {
        let prefix: Vec<QuantifiedVar> = (0..usize::BITS)
            .map(|i| QuantifiedVar::universal(format!("u{i}")))
            .collect();
        let formula = QbfFormula::new(prefix, BoolExpr::Const(true));

        let err = verify_qbf_strategy(&formula, &QbfStrategy::new([]))
            .expect_err("an unenumerable prefix must reject rather than wrap the shift");
        assert!(matches!(
            err,
            StrategyError::TooManyAssignments { count } if count == usize::BITS as usize
        ));
    }

    #[test]
    fn accepts_constant_true_matrix_with_no_universals() {
        let formula = QbfFormula::new(
            vec![QuantifiedVar::existential("e")],
            BoolExpr::or(BoolExpr::var("e"), BoolExpr::negate(BoolExpr::var("e"))),
        );
        let strategy = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(vec![], vec![StrategyCase::new(vec![], true)]),
        )]);

        let result = verify_qbf_strategy(&formula, &strategy)
            .expect("a tautological matrix with a total 0-ary strategy verifies");
        assert_eq!(result.checked_universal_assignments, 1);
    }

    #[test]
    fn checks_every_universal_assignment() {
        let formula = QbfFormula::new(
            vec![
                QuantifiedVar::universal("a"),
                QuantifiedVar::universal("b"),
                QuantifiedVar::existential("e"),
            ],
            BoolExpr::iff(
                BoolExpr::var("e"),
                BoolExpr::and(BoolExpr::var("a"), BoolExpr::var("b")),
            ),
        );
        let strategy = QbfStrategy::new([(
            "e".to_string(),
            SkolemFunction::new(
                vec!["a".to_string(), "b".to_string()],
                vec![
                    StrategyCase::new(vec![false, false], false),
                    StrategyCase::new(vec![false, true], false),
                    StrategyCase::new(vec![true, false], false),
                    StrategyCase::new(vec![true, true], true),
                ],
            ),
        )]);

        let result = verify_qbf_strategy(&formula, &strategy)
            .expect("the conjunction strategy is a total winning strategy");
        assert_eq!(result.checked_universal_assignments, 4);
    }
}
