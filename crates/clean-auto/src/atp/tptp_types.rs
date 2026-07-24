// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TPTP data types: formulas, terms, roles, and problem representation.

use thiserror::Error;

/// TPTP parse error.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum TptpParseError {
    #[error("unexpected end of input at position {0}")]
    UnexpectedEof(usize),
    #[error("unexpected character '{0}' at position {1}")]
    UnexpectedChar(char, usize),
    #[error("expected '{expected}' at position {pos}, found '{found}'")]
    Expected {
        expected: String,
        found: String,
        pos: usize,
    },
    #[error("unknown role '{0}'")]
    UnknownRole(String),
}

/// The role of a formula in a TPTP problem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TptpRole {
    Axiom,
    Hypothesis,
    Conjecture,
    NegatedConjecture,
    /// Any other role treated as axiom-like.
    Other(String),
}

/// A first-order formula (FOF).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FofFormula {
    /// Atomic predicate: `p(t1, ..., tn)` or propositional variable `p`.
    Predicate(String, Vec<FofTerm>),
    /// Equality: `t1 = t2`.
    Equal(FofTerm, FofTerm),
    /// Disequality: `t1 != t2`.
    NotEqual(FofTerm, FofTerm),
    /// Negation: `~F`.
    Not(Box<FofFormula>),
    /// Conjunction: `F1 & F2`.
    And(Box<FofFormula>, Box<FofFormula>),
    /// Disjunction: `F1 | F2`.
    Or(Box<FofFormula>, Box<FofFormula>),
    /// Implication: `F1 => F2`.
    Implies(Box<FofFormula>, Box<FofFormula>),
    /// Bi-implication: `F1 <=> F2`.
    Iff(Box<FofFormula>, Box<FofFormula>),
    /// Universal quantification: `![X1, ..., Xn]: F`.
    Forall(Vec<String>, Box<FofFormula>),
    /// Existential quantification: `?[X1, ..., Xn]: F`.
    Exists(Vec<String>, Box<FofFormula>),
    /// $true.
    True,
    /// $false.
    False,
}

/// A first-order term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FofTerm {
    /// Variable (starts with uppercase in TPTP).
    Var(String),
    /// Function application: `f(t1, ..., tn)` or constant `c`.
    Func(String, Vec<FofTerm>),
}

/// A single annotated formula in a TPTP problem.
#[derive(Clone, Debug)]
pub struct TptpFormula {
    pub _name: String,
    pub role: TptpRole,
    pub formula: FofFormula,
    /// True if this was a `cnf()` declaration (already in clause form).
    pub is_cnf: bool,
}

/// A parsed TPTP problem.
#[derive(Clone, Debug)]
pub struct TptpProblem {
    pub formulas: Vec<TptpFormula>,
}

impl TptpProblem {
    /// Check whether the problem has a conjecture formula.
    pub fn has_conjecture(&self) -> bool {
        self.formulas.iter().any(|f| f.role == TptpRole::Conjecture)
    }
}
