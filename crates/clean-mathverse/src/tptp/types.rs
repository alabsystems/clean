// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TPTP AST types.
//!
//! Represents the structural content of TPTP problem files (`.p` and `.ax`).
//! Covers the main TPTP sub-languages: FOF (first-order formulas),
//! CNF (clause normal form), TFF (typed first-order form), and THF
//! (typed higher-order form).

use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// TPTP language and role
// ════════════════════════════════════════════════════════════════════════════

/// TPTP sub-language tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TptpLanguage {
    /// First-Order Formula.
    Fof,
    /// Clause Normal Form.
    Cnf,
    /// Typed First-order Form.
    Tff,
    /// Typed Higher-order Form.
    Thf,
}

/// Role of a TPTP annotated formula.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TptpRole {
    Axiom,
    Hypothesis,
    Conjecture,
    NegatedConjecture,
    Lemma,
    Theorem,
    Definition,
    Type,
    Plain,
}

impl TptpRole {
    /// Parse a TPTP role string.
    pub(crate) fn from_str_tptp(s: &str) -> Option<Self> {
        match s {
            "axiom" => Some(Self::Axiom),
            "hypothesis" => Some(Self::Hypothesis),
            "conjecture" => Some(Self::Conjecture),
            "negated_conjecture" => Some(Self::NegatedConjecture),
            "lemma" => Some(Self::Lemma),
            "theorem" => Some(Self::Theorem),
            "definition" => Some(Self::Definition),
            "type" => Some(Self::Type),
            "plain" => Some(Self::Plain),
            _ => None,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Formula terms
// ════════════════════════════════════════════════════════════════════════════

/// A TPTP formula / term.
///
/// Represents the logical content of an annotated formula entry. FOF and TFF
/// formulas share this representation; CNF clauses are represented as
/// disjunctions of (possibly negated) atoms.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TptpTerm {
    /// Variable (uppercase identifier): `X`, `Y`, `Var1`.
    Var(String),
    /// Atomic constant (lowercase identifier or single-quoted): `a`, `'name'`.
    Atom(String),
    /// Function/predicate application: `f(a, b, c)`.
    Func(String, Vec<TptpTerm>),
    /// Negation: `~ P`.
    Not(Box<TptpTerm>),
    /// Conjunction: `P & Q`.
    And(Box<TptpTerm>, Box<TptpTerm>),
    /// Disjunction: `P | Q`.
    Or(Box<TptpTerm>, Box<TptpTerm>),
    /// Implication: `P => Q`.
    Implies(Box<TptpTerm>, Box<TptpTerm>),
    /// Biconditional: `P <=> Q`.
    Iff(Box<TptpTerm>, Box<TptpTerm>),
    /// Universal quantification: `! [X, Y] : P`.
    ForAll(Vec<String>, Box<TptpTerm>),
    /// Existential quantification: `? [X] : P`.
    Exists(Vec<String>, Box<TptpTerm>),
    /// Equality: `X = Y`.
    Eq(Box<TptpTerm>, Box<TptpTerm>),
    /// Disequality: `X != Y`.
    Neq(Box<TptpTerm>, Box<TptpTerm>),
    /// Logical true: `$true`.
    True,
    /// Logical false: `$false`.
    False,
}

// ════════════════════════════════════════════════════════════════════════════
// Type expressions (TFF/THF)
// ════════════════════════════════════════════════════════════════════════════

/// TPTP type expression (used in TFF and THF type declarations).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TptpType {
    /// Boolean type: `$o` / `$oType`.
    Bool,
    /// Individual type: `$i` / `$iType`.
    Individual,
    /// Integer type: `$int`.
    Int,
    /// Rational type: `$rat`.
    Rat,
    /// Real type: `$real`.
    Real,
    /// Named type: user-defined or domain-specific.
    Named(String),
    /// Function type: `t1 > t2`.
    Arrow(Box<TptpType>, Box<TptpType>),
    /// Product type: `t1 * t2 * ...` (used in multi-argument function types).
    Product(Vec<TptpType>),
}

// ════════════════════════════════════════════════════════════════════════════
// Annotated formula
// ════════════════════════════════════════════════════════════════════════════

/// A single TPTP annotated formula entry.
///
/// Corresponds to one `fof(name, role, formula).`, `cnf(...)`,
/// `tff(...)`, or `thf(...)` entry in a TPTP file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TptpFormula {
    /// Name of this formula (the first argument).
    pub name: String,
    /// Sub-language.
    pub language: TptpLanguage,
    /// Role (axiom, conjecture, etc.).
    pub role: TptpRole,
    /// The logical content.
    pub formula: TptpTerm,
}

// ════════════════════════════════════════════════════════════════════════════
// Include directive
// ════════════════════════════════════════════════════════════════════════════

/// A TPTP `include('path').` directive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TptpInclude {
    /// The path argument to `include(...)`.
    pub path: String,
}

// ════════════════════════════════════════════════════════════════════════════
// File
// ════════════════════════════════════════════════════════════════════════════

/// A parsed TPTP file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TptpFile {
    /// Include directives.
    pub includes: Vec<TptpInclude>,
    /// Annotated formulas.
    pub formulas: Vec<TptpFormula>,
}

impl TptpFile {
    /// Count formulas by role.
    #[must_use]
    pub fn count_by_role(&self, role: TptpRole) -> usize {
        self.formulas.iter().filter(|f| f.role == role).count()
    }

    /// Whether this file contains any conjectures.
    #[must_use]
    pub fn has_conjectures(&self) -> bool {
        self.formulas.iter().any(|f| f.role == TptpRole::Conjecture)
    }

    /// Whether this file has no formulas.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.formulas.is_empty()
    }
}
