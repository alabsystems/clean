// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Solver-native CNF types with newtype safety.
//!
//! Provides [`Var`], [`Lit`], [`SatClause`], [`Cnf`], and [`Assignment`]
//! as type-safe wrappers around the raw integer representations used in
//! DIMACS format. These types prevent accidental misuse of variable
//! indices as literals and vice versa.
//!
//! The existing `cdcl::Literal` (= `i32`) and `cdcl::Clause` (= `Vec<i32>`)
//! aliases are retained for backward compatibility. These newtypes are the
//! preferred API for new code.

use std::collections::HashSet;
use std::fmt;

/// A propositional variable, represented as a positive integer.
///
/// Variable 0 is reserved/invalid; DIMACS variables are 1-indexed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub u32);

impl Var {
    /// The underlying variable index.
    #[must_use]
    pub fn index(self) -> u32 {
        self.0
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

/// A literal: a signed reference to a variable. Positive = variable,
/// negative = negation. Zero is invalid (self-negating). Field is
/// `pub(crate)`; outside callers use `Lit::new`/`Lit::from_dimacs` (#3329).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(pub(crate) i32);

impl Lit {
    /// Create a new literal, validating that it is nonzero (#3329).
    ///
    /// # Errors
    ///
    /// Returns `CnfError::ZeroLiteral` if `val == 0`.
    pub fn new(val: i32) -> Result<Lit, CnfError> {
        if val == 0 {
            return Err(CnfError::ZeroLiteral);
        }
        Ok(Lit(val))
    }

    /// The variable this literal refers to.
    #[must_use]
    pub fn var(self) -> Var {
        Var(self.0.unsigned_abs())
    }

    /// Whether this literal has positive polarity.
    #[must_use]
    pub fn polarity(self) -> bool {
        self.0 > 0
    }

    /// The negation of this literal.
    ///
    /// # Panics
    ///
    /// Panics if `self.0 == 0` (release-enforced defense-in-depth; #3329).
    #[must_use]
    pub fn negate(self) -> Lit {
        assert!(self.0 != 0, "Lit(0) is self-negating and invalid");
        Lit(-self.0)
    }

    /// Create a literal from a DIMACS integer.
    ///
    /// # Panics
    ///
    /// Panics if `d` is 0. DIMACS format uses 0 as a clause terminator,
    /// not as a valid literal. Use `Lit::new()` for fallible construction.
    #[must_use]
    pub fn from_dimacs(d: i32) -> Lit {
        assert!(
            d != 0,
            "Lit(0) is invalid: 0 is self-negating and is the DIMACS clause terminator"
        );
        Lit(d)
    }

    /// Convert to DIMACS integer representation.
    #[must_use]
    pub fn to_dimacs(self) -> i32 {
        self.0
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 > 0 {
            write!(f, "x{}", self.0)
        } else {
            write!(f, "~x{}", -self.0)
        }
    }
}

/// A clause: a disjunction of literals.
///
/// Named `SatClause` to avoid conflict with the existing `Clause` type alias
/// in `cdcl::mod.rs`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SatClause(pub Vec<Lit>);

impl SatClause {
    /// Number of literals in this clause (its width).
    #[must_use]
    pub fn width(&self) -> usize {
        self.0.len()
    }

    /// Whether this clause is empty (always false).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Whether the clause contains a given variable (in either polarity).
    #[must_use]
    pub fn contains_var(&self, v: Var) -> bool {
        self.0.iter().any(|l| l.var() == v)
    }

    /// Whether the clause is a tautology (contains both `x` and `~x`
    /// for some variable).
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        let mut pos = HashSet::new();
        let mut neg = HashSet::new();
        for lit in &self.0 {
            if lit.polarity() {
                pos.insert(lit.var());
            } else {
                neg.insert(lit.var());
            }
        }
        pos.intersection(&neg).next().is_some()
    }

    /// Resolve this clause with `other` on the pivot variable.
    ///
    /// The pivot must appear positive in one clause and negative in the
    /// other (or vice versa). Returns `None` if the pivot is not present
    /// in the required polarities.
    #[must_use]
    pub fn resolve(&self, other: &SatClause, pivot: Var) -> Option<SatClause> {
        let self_has_pos = self.0.iter().any(|l| l.var() == pivot && l.polarity());
        let self_has_neg = self.0.iter().any(|l| l.var() == pivot && !l.polarity());
        let other_has_pos = other.0.iter().any(|l| l.var() == pivot && l.polarity());
        let other_has_neg = other.0.iter().any(|l| l.var() == pivot && !l.polarity());

        // One must have positive, the other negative.
        let valid = (self_has_pos && other_has_neg) || (self_has_neg && other_has_pos);
        if !valid {
            return None;
        }

        let mut result: Vec<Lit> = Vec::new();
        for lit in self.0.iter().chain(other.0.iter()) {
            if lit.var() == pivot {
                continue;
            }
            if !result.contains(lit) {
                result.push(*lit);
            }
        }
        result.sort_by_key(|l| (l.var(), !l.polarity()));
        Some(SatClause(result))
    }

    /// Convert to a raw DIMACS literal vector (for interop with existing code).
    #[must_use]
    pub fn to_dimacs(&self) -> Vec<i32> {
        self.0.iter().map(|l| l.to_dimacs()).collect()
    }

    /// Create from a raw DIMACS literal vector.
    #[must_use]
    pub fn from_dimacs(lits: &[i32]) -> SatClause {
        SatClause(lits.iter().map(|&d| Lit::from_dimacs(d)).collect())
    }
}

impl fmt::Display for SatClause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "[]")
        } else {
            write!(f, "(")?;
            for (i, lit) in self.0.iter().enumerate() {
                if i > 0 {
                    write!(f, " v ")?;
                }
                write!(f, "{lit}")?;
            }
            write!(f, ")")
        }
    }
}

/// A CNF formula: a conjunction of clauses.
#[derive(Debug, Clone)]
pub struct Cnf {
    /// Number of distinct variables in the formula.
    pub num_vars: u32,
    /// The clauses.
    pub clauses: Vec<SatClause>,
}

/// Errors from CNF parsing or validation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CnfError {
    /// A variable index exceeds the declared number of variables.
    VariableOutOfRange { var: u32, max: u32 },
    /// Zero literal encountered (invalid in DIMACS).
    ZeroLiteral,
    /// Parse error in DIMACS format.
    ParseError(String),
}

impl fmt::Display for CnfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CnfError::VariableOutOfRange { var, max } => {
                write!(f, "variable {var} exceeds declared max {max}")
            }
            CnfError::ZeroLiteral => write!(f, "zero literal encountered"),
            CnfError::ParseError(msg) => write!(f, "DIMACS parse error: {msg}"),
        }
    }
}

impl std::error::Error for CnfError {}

impl Cnf {
    /// Number of clauses in the formula.
    #[must_use]
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Collect the set of all variables that appear in the formula.
    #[must_use]
    pub fn vars(&self) -> HashSet<Var> {
        let mut s = HashSet::new();
        for clause in &self.clauses {
            for lit in &clause.0 {
                s.insert(lit.var());
            }
        }
        s
    }

    /// Whether every variable in the formula is within the declared range.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        for clause in &self.clauses {
            for lit in &clause.0 {
                if lit.0 == 0 || lit.var().0 > self.num_vars {
                    return false;
                }
            }
        }
        true
    }

    /// Parse a CNF formula from DIMACS format.
    ///
    /// Expects the standard DIMACS-CNF format:
    /// - Comment lines start with `c`
    /// - Problem line: `p cnf <num_vars> <num_clauses>`
    /// - Clause lines: space-separated literals terminated by `0`
    pub fn from_dimacs(input: &str) -> Result<Cnf, CnfError> {
        let mut num_vars = 0u32;
        let mut expected_clauses = 0usize;
        let mut clauses = Vec::new();
        let mut current_lits: Vec<Lit> = Vec::new();
        let mut found_header = false;

        for line in input.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('c') {
                continue;
            }
            if trimmed.starts_with("p cnf") || trimmed.starts_with("p CNF") {
                let parts: Vec<&str> = trimmed.split_whitespace().collect();
                if parts.len() < 4 {
                    return Err(CnfError::ParseError(
                        "problem line must have format: p cnf <vars> <clauses>".to_string(),
                    ));
                }
                num_vars = parts[2]
                    .parse()
                    .map_err(|e| CnfError::ParseError(format!("bad num_vars: {e}")))?;
                expected_clauses = parts[3]
                    .parse()
                    .map_err(|e| CnfError::ParseError(format!("bad num_clauses: {e}")))?;
                found_header = true;
                continue;
            }
            if !found_header {
                return Err(CnfError::ParseError(
                    "expected 'p cnf ...' header before clause data".to_string(),
                ));
            }
            for token in trimmed.split_whitespace() {
                let val: i32 = token
                    .parse()
                    .map_err(|e| CnfError::ParseError(format!("bad literal '{token}': {e}")))?;
                if val == 0 {
                    clauses.push(SatClause(current_lits.clone()));
                    current_lits.clear();
                } else {
                    let var = val.unsigned_abs();
                    if var > num_vars {
                        return Err(CnfError::VariableOutOfRange { var, max: num_vars });
                    }
                    current_lits.push(Lit(val));
                }
            }
        }
        // Handle case where last clause isn't terminated by 0.
        if !current_lits.is_empty() {
            clauses.push(SatClause(current_lits));
        }

        if clauses.len() != expected_clauses {
            return Err(CnfError::ParseError(format!(
                "expected {expected_clauses} clauses, found {}",
                clauses.len()
            )));
        }

        Ok(Cnf { num_vars, clauses })
    }

    /// Convert to raw DIMACS clause vectors (for interop).
    #[must_use]
    pub fn to_dimacs_clauses(&self) -> Vec<Vec<i32>> {
        self.clauses.iter().map(|c| c.to_dimacs()).collect()
    }
}

impl fmt::Display for Cnf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "p cnf {} {}", self.num_vars, self.clauses.len())?;
        for clause in &self.clauses {
            for lit in &clause.0 {
                write!(f, "{} ", lit.0)?;
            }
            writeln!(f, "0")?;
        }
        Ok(())
    }
}

/// A (partial or total) truth assignment over propositional variables.
///
/// Variables are 1-indexed; slot 0 is unused.
#[derive(Debug, Clone)]
pub struct Assignment {
    /// values[v] = Some(true/false) for variable v, None if unassigned.
    /// Index 0 is unused.
    values: Vec<Option<bool>>,
}

impl Assignment {
    /// Create a new empty assignment for `num_vars` variables.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            values: vec![None; (num_vars + 1) as usize],
        }
    }

    /// Set the value of a variable. Overwrites any previous assignment.
    ///
    /// # Panics
    ///
    /// Panics if the variable index is outside the allocated range
    /// (i.e., `v.0 >= num_vars + 1`). Previously this method silently
    /// dropped out-of-range assignments (#3332), which could hide bugs
    /// in callers that construct invalid variable references.
    pub fn set(&mut self, v: Var, val: bool) {
        let idx = v.0 as usize;
        assert!(
            idx < self.values.len(),
            "Assignment::set: variable {} is out of range (max {})",
            v.0,
            self.values.len().saturating_sub(1),
        );
        self.values[idx] = Some(val);
    }

    /// Get the current value of a variable, or `None` if unassigned.
    #[must_use]
    pub fn get(&self, v: Var) -> Option<bool> {
        self.values.get(v.0 as usize).copied().flatten()
    }

    /// Evaluate a literal under this assignment.
    ///
    /// Returns `Some(true)` if satisfied, `Some(false)` if falsified,
    /// `None` if the variable is unassigned.
    #[must_use]
    pub fn eval_lit(&self, l: Lit) -> Option<bool> {
        self.get(l.var())
            .map(|val| if l.polarity() { val } else { !val })
    }

    /// Evaluate a clause under this assignment.
    ///
    /// Returns `Some(true)` if at least one literal is satisfied,
    /// `Some(false)` if all literals are falsified, `None` if some
    /// literals are unassigned and none are satisfied.
    #[must_use]
    pub fn eval_clause(&self, c: &SatClause) -> Option<bool> {
        let mut has_unassigned = false;
        for lit in &c.0 {
            match self.eval_lit(*lit) {
                Some(true) => return Some(true),
                Some(false) => {}
                None => has_unassigned = true,
            }
        }
        if has_unassigned {
            None
        } else {
            Some(false)
        }
    }

    /// Evaluate an entire CNF formula under this assignment.
    ///
    /// Returns `Some(true)` if all clauses are satisfied, `Some(false)` if
    /// any clause is falsified, `None` if the result is indeterminate.
    #[must_use]
    pub fn eval_cnf(&self, f: &Cnf) -> Option<bool> {
        let mut all_true = true;
        for clause in &f.clauses {
            match self.eval_clause(clause) {
                Some(false) => return Some(false),
                Some(true) => {}
                None => all_true = false,
            }
        }
        if all_true {
            Some(true)
        } else {
            None
        }
    }

    /// Whether every variable in the CNF has been assigned.
    #[must_use]
    pub fn is_complete(&self, f: &Cnf) -> bool {
        for var in f.vars() {
            if self.get(var).is_none() {
                return false;
            }
        }
        true
    }

    /// Unassign a variable.
    ///
    /// # Panics
    ///
    /// Panics if the variable index is outside the allocated range.
    pub fn unset(&mut self, v: Var) {
        let idx = v.0 as usize;
        assert!(
            idx < self.values.len(),
            "Assignment::unset: variable {} is out of range (max {})",
            v.0,
            self.values.len().saturating_sub(1),
        );
        self.values[idx] = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Var / Lit basic tests ----

    #[test]
    fn test_var_index() {
        assert_eq!(Var(5).index(), 5);
    }

    #[test]
    fn test_lit_var_and_polarity() {
        let pos = Lit(3);
        assert_eq!(pos.var(), Var(3));
        assert!(pos.polarity());

        let neg = Lit(-3);
        assert_eq!(neg.var(), Var(3));
        assert!(!neg.polarity());
    }

    #[test]
    fn test_lit_negate() {
        assert_eq!(Lit(5).negate(), Lit(-5));
        assert_eq!(Lit(-5).negate(), Lit(5));
    }

    #[test]
    fn test_lit_dimacs_roundtrip() {
        for d in [-7, -1, 1, 42] {
            assert_eq!(Lit::from_dimacs(d).to_dimacs(), d);
        }
    }

    // ---- SatClause tests ----

    #[test]
    fn test_satclause_width_and_empty() {
        let c = SatClause(vec![Lit(1), Lit(-2), Lit(3)]);
        assert_eq!(c.width(), 3);
        assert!(!c.is_empty());

        let empty = SatClause(vec![]);
        assert_eq!(empty.width(), 0);
        assert!(empty.is_empty());
    }

    #[test]
    fn test_satclause_contains_var() {
        let c = SatClause(vec![Lit(1), Lit(-2)]);
        assert!(c.contains_var(Var(1)));
        assert!(c.contains_var(Var(2)));
        assert!(!c.contains_var(Var(3)));
    }

    #[test]
    fn test_satclause_tautology() {
        let taut = SatClause(vec![Lit(1), Lit(-1), Lit(2)]);
        assert!(taut.is_tautology());

        let not_taut = SatClause(vec![Lit(1), Lit(2), Lit(-3)]);
        assert!(!not_taut.is_tautology());
    }

    #[test]
    fn test_satclause_resolve_basic() {
        // (1 v 2) resolve (-1 v 3) on var 1 => (2 v 3)
        let c1 = SatClause(vec![Lit(1), Lit(2)]);
        let c2 = SatClause(vec![Lit(-1), Lit(3)]);
        let res = c1.resolve(&c2, Var(1)).expect("should resolve");
        assert_eq!(res.0.len(), 2);
        assert!(res.0.contains(&Lit(2)));
        assert!(res.0.contains(&Lit(3)));
    }

    #[test]
    fn test_satclause_resolve_to_empty() {
        let c1 = SatClause(vec![Lit(1)]);
        let c2 = SatClause(vec![Lit(-1)]);
        let res = c1.resolve(&c2, Var(1)).expect("should resolve");
        assert!(res.is_empty());
    }

    #[test]
    fn test_satclause_resolve_no_pivot() {
        let c1 = SatClause(vec![Lit(1), Lit(2)]);
        let c2 = SatClause(vec![Lit(3), Lit(4)]);
        assert!(c1.resolve(&c2, Var(1)).is_none());
    }

    #[test]
    fn test_satclause_dimacs_roundtrip() {
        let raw = vec![1, -2, 3];
        let c = SatClause::from_dimacs(&raw);
        assert_eq!(c.to_dimacs(), raw);
    }

    // ---- Cnf tests ----

    #[test]
    fn test_cnf_from_dimacs_simple() {
        let input = "\
c test
p cnf 3 2
1 -2 0
2 3 0
";
        let cnf = Cnf::from_dimacs(input).expect("should parse");
        assert_eq!(cnf.num_vars, 3);
        assert_eq!(cnf.num_clauses(), 2);
        assert!(cnf.is_valid());
    }

    #[test]
    fn test_cnf_from_dimacs_variable_out_of_range() {
        let input = "p cnf 2 1\n5 0\n";
        assert!(Cnf::from_dimacs(input).is_err());
    }

    #[test]
    fn test_cnf_vars() {
        let cnf = Cnf {
            num_vars: 5,
            clauses: vec![
                SatClause(vec![Lit(1), Lit(-3)]),
                SatClause(vec![Lit(2), Lit(5)]),
            ],
        };
        let vars = cnf.vars();
        assert_eq!(vars.len(), 4);
        assert!(vars.contains(&Var(1)));
        assert!(vars.contains(&Var(3)));
        assert!(!vars.contains(&Var(4)));
    }

    #[test]
    fn test_cnf_is_valid() {
        let valid = Cnf {
            num_vars: 3,
            clauses: vec![SatClause(vec![Lit(1), Lit(-2), Lit(3)])],
        };
        assert!(valid.is_valid());

        let invalid = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1), Lit(-3)])],
        };
        assert!(!invalid.is_valid());

        let zero_lit = Cnf {
            num_vars: 3,
            clauses: vec![SatClause(vec![Lit(0)])],
        };
        assert!(!zero_lit.is_valid());
    }

    // ---- Assignment tests ----

    #[test]
    fn test_assignment_set_get() {
        let mut a = Assignment::new(3);
        assert!(a.get(Var(1)).is_none());
        a.set(Var(1), true);
        assert_eq!(a.get(Var(1)), Some(true));
        a.set(Var(2), false);
        assert_eq!(a.get(Var(2)), Some(false));
    }

    #[test]
    fn test_assignment_eval_lit() {
        let mut a = Assignment::new(3);
        a.set(Var(1), true);
        a.set(Var(2), false);
        assert_eq!(a.eval_lit(Lit(1)), Some(true));
        assert_eq!(a.eval_lit(Lit(-1)), Some(false));
        assert_eq!(a.eval_lit(Lit(2)), Some(false));
        assert_eq!(a.eval_lit(Lit(-2)), Some(true));
        assert_eq!(a.eval_lit(Lit(3)), None);
    }

    #[test]
    fn test_assignment_eval_clause() {
        let mut a = Assignment::new(3);
        let clause = SatClause(vec![Lit(1), Lit(-2), Lit(3)]);

        // All unassigned -> None
        assert_eq!(a.eval_clause(&clause), None);

        // One satisfied -> Some(true)
        a.set(Var(1), true);
        assert_eq!(a.eval_clause(&clause), Some(true));

        // Reset, all falsified -> Some(false)
        let mut a2 = Assignment::new(3);
        a2.set(Var(1), false);
        a2.set(Var(2), true);
        a2.set(Var(3), false);
        assert_eq!(a2.eval_clause(&clause), Some(false));
    }

    #[test]
    fn test_assignment_eval_cnf() {
        let cnf = Cnf {
            num_vars: 2,
            clauses: vec![SatClause(vec![Lit(1)]), SatClause(vec![Lit(-2)])],
        };
        let mut a = Assignment::new(2);
        a.set(Var(1), true);
        a.set(Var(2), false);
        assert_eq!(a.eval_cnf(&cnf), Some(true));

        let mut a2 = Assignment::new(2);
        a2.set(Var(1), false);
        a2.set(Var(2), false);
        assert_eq!(a2.eval_cnf(&cnf), Some(false));
    }

    #[test]
    fn test_assignment_is_complete() {
        let cnf = Cnf {
            num_vars: 3,
            clauses: vec![SatClause(vec![Lit(1), Lit(-2)])],
        };
        let mut a = Assignment::new(3);
        assert!(!a.is_complete(&cnf));
        a.set(Var(1), true);
        assert!(!a.is_complete(&cnf));
        a.set(Var(2), false);
        assert!(a.is_complete(&cnf));
    }

    #[test]
    fn test_assignment_unset() {
        let mut a = Assignment::new(3);
        a.set(Var(1), true);
        assert_eq!(a.get(Var(1)), Some(true));
        a.unset(Var(1));
        assert_eq!(a.get(Var(1)), None);
    }

    #[test]
    fn test_cnf_display_roundtrip() {
        let input = "\
p cnf 3 2
1 -2 0
2 3 0
";
        let cnf = Cnf::from_dimacs(input).expect("parse");
        let output = cnf.to_string();
        let cnf2 = Cnf::from_dimacs(&output).expect("reparse");
        assert_eq!(cnf2.num_vars, cnf.num_vars);
        assert_eq!(cnf2.num_clauses(), cnf.num_clauses());
    }

    // ---- #3329: Lit(0) validation ----

    #[test]
    fn test_lit_new_rejects_zero() {
        assert!(Lit::new(0).is_err());
        assert_eq!(Lit::new(0).unwrap_err(), CnfError::ZeroLiteral);
    }

    #[test]
    fn test_lit_new_accepts_nonzero() {
        assert_eq!(Lit::new(1).unwrap(), Lit(1));
        assert_eq!(Lit::new(-5).unwrap(), Lit(-5));
    }

    #[test]
    #[should_panic(expected = "Lit(0) is invalid")]
    fn test_lit_from_dimacs_panics_on_zero() {
        let _ = Lit::from_dimacs(0);
    }

    #[test]
    fn test_lit_negate_is_involutive() {
        // For all nonzero literals, negate(negate(x)) == x.
        for val in [-7, -1, 1, 42] {
            let lit = Lit::new(val).expect("nonzero");
            assert_eq!(lit.negate().negate(), lit);
            assert_ne!(lit.negate(), lit);
        }
    }

    // Additional #3329 invariant tests live in `tests_lit_invariant.rs`.

    // ---- #3332: Assignment.set() panics on out-of-range ----

    #[test]
    #[should_panic(expected = "out of range")]
    fn test_assignment_set_out_of_range_panics() {
        let mut a = Assignment::new(3);
        a.set(Var(4), true); // num_vars=3, max index is 3, so 4 is out of range
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn test_assignment_unset_out_of_range_panics() {
        let mut a = Assignment::new(3);
        a.unset(Var(4));
    }

    #[test]
    fn test_assignment_set_at_boundary_works() {
        // Variable 3 should work with num_vars=3 (slot 3 exists in vec of len 4).
        let mut a = Assignment::new(3);
        a.set(Var(3), true);
        assert_eq!(a.get(Var(3)), Some(true));
    }
}
