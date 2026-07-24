// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Craig Interpolation
//!
//! Given an unsatisfiable conjunction A AND B, Craig's interpolation theorem
//! guarantees the existence of a formula I (the interpolant) such that:
//!
//! 1. A implies I
//! 2. I AND B is unsatisfiable
//! 3. Vars(I) is a subset of Vars(A) intersect Vars(B)
//!
//! This module implements McMillan's algorithm for extracting interpolants
//! from resolution refutation DAGs, with A/B partition labeling.
//!
//! ## References
//!
//! - Craig (1957): "Three uses of the Herbrand-Gentzen theorem"
//! - McMillan (2003): "Interpolation and SAT-Based Model Checking"
//! - Pudlak (1997): "Lower bounds on the size of interpolants"

pub mod extract;
pub mod farkas;
pub(crate) mod kernel_proofs;
pub mod mcmillan;
pub(crate) mod mcmillan_tree;
pub mod property;
pub mod reverse;
pub mod sequence;
mod spec_registration;
pub mod strength;
pub mod symmetric;
#[cfg(test)]
mod tests_extract;
#[cfg(test)]
mod tests_farkas;
#[cfg(test)]
mod tests_mcmillan;
#[cfg(test)]
mod tests_mcmillan_ext;
#[cfg(test)]
mod tests_mcmillan_tree;
#[cfg(test)]
mod tests_property;
#[cfg(test)]
mod tests_reverse;
#[cfg(test)]
mod tests_sequence;
#[cfg(test)]
mod tests_strength;
#[cfg(test)]
mod tests_symmetric;
#[cfg(test)]
mod tests_verify;
pub mod verify;

use crate::spec::ProofStatus;
use std::collections::HashSet;

/// I01: Craig interpolation existence.
pub const I01_CRAIG_EXISTENCE: ProofStatus = ProofStatus::DerivedPending;

/// I02: McMillan extraction from resolution DAG.
pub const I02_MCMILLAN_EXTRACTION: ProofStatus = ProofStatus::DerivedPending;

/// I03: Shared variable property: Vars(I) subset Vars(A) intersect Vars(B).
pub const I03_SHARED_VARIABLES: ProofStatus = ProofStatus::DerivedPending;

/// I04: Pudlak rule for shared pivots.
pub const I04_PUDLAK_RULE: ProofStatus = ProofStatus::DerivedPending;

/// I05: Sequence interpolation for BMC (re-exported from [`sequence`]).
pub use sequence::I05_SEQUENCE_INTERPOLATION;

/// I06: Fixed point detection (re-exported from [`sequence`]).
pub use sequence::I06_FIXED_POINT_DETECTION;

/// I04 implementation: Pudlak (re-exported from [`reverse`]).
pub use reverse::I04_PUDLAK_IMPL;

/// A propositional formula used to represent interpolants.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropFormula {
    /// A propositional variable.
    Var(u32),
    /// Negation.
    Not(Box<PropFormula>),
    /// Conjunction.
    AndType(Box<PropFormula>, Box<PropFormula>),
    /// Disjunction.
    Or(Box<PropFormula>, Box<PropFormula>),
    /// Implication.
    Implies(Box<PropFormula>, Box<PropFormula>),
    /// Boolean constant true.
    True,
    /// Boolean constant false.
    False,
}

impl PropFormula {
    /// Collect all variable indices appearing in this formula.
    #[must_use]
    pub fn variables(&self) -> HashSet<u32> {
        let mut vars = HashSet::new();
        self.collect_vars(&mut vars);
        vars
    }

    fn collect_vars(&self, vars: &mut HashSet<u32>) {
        match self {
            PropFormula::Var(v) => {
                vars.insert(*v);
            }
            PropFormula::Not(inner) => inner.collect_vars(vars),
            PropFormula::AndType(l, r) | PropFormula::Or(l, r) | PropFormula::Implies(l, r) => {
                l.collect_vars(vars);
                r.collect_vars(vars);
            }
            PropFormula::True | PropFormula::False => {}
        }
    }

    /// Evaluate the formula under a variable assignment (variable -> bool).
    #[must_use]
    pub fn evaluate(&self, assignment: &std::collections::HashMap<u32, bool>) -> bool {
        match self {
            PropFormula::Var(v) => assignment.get(v).copied().unwrap_or(false),
            PropFormula::Not(inner) => !inner.evaluate(assignment),
            PropFormula::AndType(l, r) => l.evaluate(assignment) && r.evaluate(assignment),
            PropFormula::Or(l, r) => l.evaluate(assignment) || r.evaluate(assignment),
            PropFormula::Implies(l, r) => !l.evaluate(assignment) || r.evaluate(assignment),
            PropFormula::True => true,
            PropFormula::False => false,
        }
    }

    /// Simplify constant sub-expressions.
    #[must_use]
    pub fn simplify(&self) -> PropFormula {
        match self {
            PropFormula::Not(inner) => {
                let s = inner.simplify();
                match s {
                    PropFormula::True => PropFormula::False,
                    PropFormula::False => PropFormula::True,
                    PropFormula::Not(x) => *x,
                    other => PropFormula::Not(Box::new(other)),
                }
            }
            PropFormula::AndType(l, r) => {
                let sl = l.simplify();
                let sr = r.simplify();
                match (&sl, &sr) {
                    (PropFormula::True, _) => sr,
                    (_, PropFormula::True) => sl,
                    (PropFormula::False, _) | (_, PropFormula::False) => PropFormula::False,
                    _ => PropFormula::AndType(Box::new(sl), Box::new(sr)),
                }
            }
            PropFormula::Or(l, r) => {
                let sl = l.simplify();
                let sr = r.simplify();
                match (&sl, &sr) {
                    (PropFormula::False, _) => sr,
                    (_, PropFormula::False) => sl,
                    (PropFormula::True, _) | (_, PropFormula::True) => PropFormula::True,
                    _ => PropFormula::Or(Box::new(sl), Box::new(sr)),
                }
            }
            PropFormula::Implies(l, r) => {
                let sl = l.simplify();
                let sr = r.simplify();
                match (&sl, &sr) {
                    (PropFormula::False, _) | (_, PropFormula::True) => PropFormula::True,
                    (PropFormula::True, _) => sr,
                    _ => PropFormula::Implies(Box::new(sl), Box::new(sr)),
                }
            }
            other => other.clone(),
        }
    }
}

impl std::fmt::Display for PropFormula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PropFormula::Var(v) => write!(f, "x{v}"),
            PropFormula::Not(inner) => write!(f, "!({inner})"),
            PropFormula::AndType(l, r) => write!(f, "({l} & {r})"),
            PropFormula::Or(l, r) => write!(f, "({l} | {r})"),
            PropFormula::Implies(l, r) => write!(f, "({l} -> {r})"),
            PropFormula::True => write!(f, "T"),
            PropFormula::False => write!(f, "F"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_prop_formula_variables() {
        let f = PropFormula::AndType(
            Box::new(PropFormula::Var(1)),
            Box::new(PropFormula::Or(
                Box::new(PropFormula::Var(2)),
                Box::new(PropFormula::Var(3)),
            )),
        );
        let vars = f.variables();
        assert_eq!(vars.len(), 3);
        assert!(vars.contains(&1) && vars.contains(&2) && vars.contains(&3));
    }

    #[test]
    fn test_prop_formula_evaluate() {
        let f = PropFormula::AndType(
            Box::new(PropFormula::Var(1)),
            Box::new(PropFormula::Not(Box::new(PropFormula::Var(2)))),
        );
        let mut asgn = HashMap::new();
        asgn.insert(1, true);
        asgn.insert(2, false);
        assert!(f.evaluate(&asgn));

        asgn.insert(2, true);
        assert!(!f.evaluate(&asgn));
    }

    #[test]
    fn test_prop_formula_implies() {
        let f = PropFormula::Implies(Box::new(PropFormula::False), Box::new(PropFormula::Var(1)));
        assert!(f.evaluate(&HashMap::new())); // false -> anything = true
    }

    #[test]
    fn test_prop_formula_simplify_constants() {
        let f = PropFormula::AndType(Box::new(PropFormula::True), Box::new(PropFormula::Var(1)));
        assert_eq!(f.simplify(), PropFormula::Var(1));

        let f2 = PropFormula::Or(Box::new(PropFormula::False), Box::new(PropFormula::Var(2)));
        assert_eq!(f2.simplify(), PropFormula::Var(2));
    }

    #[test]
    fn test_prop_formula_simplify_double_negation() {
        let f = PropFormula::Not(Box::new(PropFormula::Not(Box::new(PropFormula::Var(1)))));
        assert_eq!(f.simplify(), PropFormula::Var(1));
    }

    #[test]
    fn test_prop_formula_display() {
        let f = PropFormula::AndType(
            Box::new(PropFormula::Var(1)),
            Box::new(PropFormula::Or(
                Box::new(PropFormula::Var(2)),
                Box::new(PropFormula::Not(Box::new(PropFormula::Var(3)))),
            )),
        );
        let s = format!("{f}");
        assert!(s.contains("x1"));
        assert!(s.contains("x2"));
        assert!(s.contains("x3"));
    }

    #[test]
    fn test_prop_formula_constants_eval() {
        assert!(PropFormula::True.evaluate(&HashMap::new()));
        assert!(!PropFormula::False.evaluate(&HashMap::new()));
    }

    #[test]
    fn test_prop_formula_variables_empty_for_constants() {
        assert!(PropFormula::True.variables().is_empty());
        assert!(PropFormula::False.variables().is_empty());
    }

    #[test]
    fn test_prop_formula_simplify_implies() {
        let f = PropFormula::Implies(Box::new(PropFormula::True), Box::new(PropFormula::Var(1)));
        assert_eq!(f.simplify(), PropFormula::Var(1));

        let f2 = PropFormula::Implies(Box::new(PropFormula::Var(1)), Box::new(PropFormula::True));
        assert_eq!(f2.simplify(), PropFormula::True);
    }

    #[test]
    fn test_prop_formula_simplify_and_false() {
        let f = PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::False));
        assert_eq!(f.simplify(), PropFormula::False);
    }

    #[test]
    fn test_prop_formula_simplify_or_true() {
        let f = PropFormula::Or(Box::new(PropFormula::True), Box::new(PropFormula::Var(1)));
        assert_eq!(f.simplify(), PropFormula::True);
    }

    #[test]
    fn test_interpolation_status_constants() {
        assert_eq!(I01_CRAIG_EXISTENCE, ProofStatus::DerivedPending);
        assert_eq!(I02_MCMILLAN_EXTRACTION, ProofStatus::DerivedPending);
        assert_eq!(I03_SHARED_VARIABLES, ProofStatus::DerivedPending);
        assert_eq!(I04_PUDLAK_RULE, ProofStatus::DerivedPending);
    }
}
