// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Literals, clauses, and inference rules for the superposition calculus.

use super::{Position, Substitution, Term};
use std::collections::HashSet;
use std::fmt;

/// A literal in a clause
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal {
    /// Left-hand side of equation
    pub lhs: Term,
    /// Right-hand side of equation
    pub rhs: Term,
    /// True if positive (=), false if negative (≠)
    pub positive: bool,
}

impl Literal {
    /// Create a positive equation
    pub fn eq(lhs: Term, rhs: Term) -> Self {
        Literal {
            lhs,
            rhs,
            positive: true,
        }
    }

    /// Create a negative equation (disequation)
    pub fn neq(lhs: Term, rhs: Term) -> Self {
        Literal {
            lhs,
            rhs,
            positive: false,
        }
    }

    /// Negate this literal
    #[must_use]
    pub fn negate(&self) -> Self {
        Literal {
            lhs: self.lhs.clone(),
            rhs: self.rhs.clone(),
            positive: !self.positive,
        }
    }

    /// Apply a substitution to this literal
    #[must_use]
    pub fn apply_subst(&self, subst: &Substitution) -> Self {
        Literal {
            lhs: self.lhs.apply_subst(subst),
            rhs: self.rhs.apply_subst(subst),
            positive: self.positive,
        }
    }

    /// Check if this is a trivial literal (s = s or s ≠ s)
    pub fn is_trivial(&self) -> bool {
        self.lhs == self.rhs
    }

    /// Check if this is a reflexive positive equation (s = s)
    pub fn is_reflexive(&self) -> bool {
        self.positive && self.lhs == self.rhs
    }

    /// Get all variables in this literal
    pub fn vars(&self) -> HashSet<u32> {
        let mut vars = self.lhs.vars();
        vars.extend(self.rhs.vars());
        vars
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.positive {
            write!(f, "{} = {}", self.lhs, self.rhs)
        } else {
            write!(f, "{} ≠ {}", self.lhs, self.rhs)
        }
    }
}

/// A clause is a disjunction of literals
#[derive(Clone, Debug)]
pub struct Clause {
    /// The literals in this clause
    pub literals: Vec<Literal>,
    /// Unique identifier
    pub id: u64,
    /// Parent clause IDs (for proof reconstruction)
    pub parents: Vec<u64>,
    /// Inference rule that derived this clause
    pub inference: Inference,
}

/// Inference rule that derived a clause
#[derive(Clone, Debug)]
pub enum Inference {
    /// Input clause from the problem
    Input,
    /// Superposition left or right
    Superposition(u64, u64, Position),
    /// Equality resolution
    EqualityResolution(u64),
    /// Equality factoring
    EqualityFactoring(u64),
    /// Demodulation (simplification)
    Demodulation(u64, u64),
    /// Subsumption deletion
    Subsumption(u64),
}

impl Clause {
    /// Create a new input clause
    pub fn new(literals: Vec<Literal>, id: u64) -> Self {
        Clause {
            literals,
            id,
            parents: vec![],
            inference: Inference::Input,
        }
    }

    /// Check if this is the empty clause (contradiction)
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if this is a unit clause
    pub fn is_unit(&self) -> bool {
        self.literals.len() == 1
    }

    /// Check if this is a tautology (contains s=s or both s=t and s≠t)
    pub fn is_tautology(&self) -> bool {
        // Check for reflexive equalities
        for lit in &self.literals {
            if lit.positive && lit.lhs == lit.rhs {
                return true;
            }
        }

        // Check for complementary literals (including symmetric equations)
        for (i, lit1) in self.literals.iter().enumerate() {
            for lit2 in self.literals.iter().skip(i + 1) {
                if lit1.positive != lit2.positive {
                    // Direct: a=b vs a!=b
                    if lit1.lhs == lit2.lhs && lit1.rhs == lit2.rhs {
                        return true;
                    }
                    // Symmetric: a=b vs b!=a (equality is symmetric)
                    if lit1.lhs == lit2.rhs && lit1.rhs == lit2.lhs {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Apply a substitution to this clause
    #[must_use]
    pub fn apply_subst(&self, subst: &Substitution) -> Self {
        Clause {
            literals: self.literals.iter().map(|l| l.apply_subst(subst)).collect(),
            id: self.id,
            parents: self.parents.clone(),
            inference: self.inference.clone(),
        }
    }

    /// Get all variables in this clause
    pub fn vars(&self) -> HashSet<u32> {
        let mut vars = HashSet::new();
        for lit in &self.literals {
            vars.extend(lit.vars());
        }
        vars
    }

    /// Rename variables to avoid conflicts with another clause
    #[must_use]
    pub fn rename_vars(&self, offset: u32) -> Self {
        let subst = Substitution {
            map: self
                .vars()
                .into_iter()
                .map(|v| (v, Term::Var(v + offset)))
                .collect(),
        };
        self.apply_subst(&subst)
    }

    /// Get positive literals
    pub fn positive_literals(&self) -> Vec<(usize, &Literal)> {
        self.literals
            .iter()
            .enumerate()
            .filter(|(_, l)| l.positive)
            .collect()
    }

    /// Get negative literals
    pub fn negative_literals(&self) -> Vec<(usize, &Literal)> {
        self.literals
            .iter()
            .enumerate()
            .filter(|(_, l)| !l.positive)
            .collect()
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.literals.is_empty() {
            write!(f, "□")
        } else {
            for (i, lit) in self.literals.iter().enumerate() {
                if i > 0 {
                    write!(f, " ∨ ")?;
                }
                write!(f, "{lit}")?;
            }
            Ok(())
        }
    }
}
