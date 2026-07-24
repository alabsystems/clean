// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ AST types.
//!
//! Represents the structural content of TLA+ `.tla` specification files.
//! Covers modules, declarations (CONSTANT, VARIABLE), operator definitions,
//! theorems, lemmas, and the core expression language.

use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// Expressions
// ════════════════════════════════════════════════════════════════════════════

/// A TLA+ expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TlaExpr {
    /// Identifier (variable, constant, or operator reference).
    Ident(String),
    /// Integer literal.
    IntLit(i64),
    /// String literal.
    StringLit(String),
    /// Boolean literal: TRUE, FALSE.
    BoolLit(bool),
    /// Function/operator application: `Op(arg1, arg2, ...)`.
    App(String, Vec<TlaExpr>),
    /// Binary infix operator: `a \op b`.
    BinOp(String, Box<TlaExpr>, Box<TlaExpr>),
    /// Unary prefix operator: `\neg a`, `ENABLED a`, etc.
    UnaryOp(String, Box<TlaExpr>),
    /// Set enumeration: `{a, b, c}`.
    SetEnum(Vec<TlaExpr>),
    /// Set filter: `{x \in S : P(x)}`.
    SetFilter(String, Box<TlaExpr>, Box<TlaExpr>),
    /// Set map: `{f(x) : x \in S}`.
    SetMap(Box<TlaExpr>, String, Box<TlaExpr>),
    /// Tuple: `<<a, b, c>>`.
    Tuple(Vec<TlaExpr>),
    /// Record: `[field1 |-> val1, field2 |-> val2]`.
    Record(Vec<(String, TlaExpr)>),
    /// Record field access: `r.field`.
    FieldAccess(Box<TlaExpr>, String),
    /// IF-THEN-ELSE.
    IfThenElse(Box<TlaExpr>, Box<TlaExpr>, Box<TlaExpr>),
    /// CASE expression.
    Case(Vec<(TlaExpr, TlaExpr)>, Option<Box<TlaExpr>>),
    /// LET-IN expression.
    LetIn(Vec<(String, TlaExpr)>, Box<TlaExpr>),
    /// Quantified: `\A x \in S : P(x)` or `\E x \in S : P(x)`.
    Quantifier(QuantifierKind, Vec<(String, Option<TlaExpr>)>, Box<TlaExpr>),
    /// CHOOSE x \in S : P(x).
    Choose(String, Option<Box<TlaExpr>>, Box<TlaExpr>),
    /// Primed expression: `x'`.
    Prime(Box<TlaExpr>),
    /// UNCHANGED <<x, y, z>>.
    Unchanged(Vec<TlaExpr>),
    /// Temporal operators: [][Next]_vars, <>P, []P.
    Temporal(String, Box<TlaExpr>),
    /// Raw text that we couldn't parse structurally.
    Raw(String),
}

/// Quantifier kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum QuantifierKind {
    /// Universal: `\A`.
    ForAll,
    /// Existential: `\E`.
    Exists,
}

// ════════════════════════════════════════════════════════════════════════════
// Declarations
// ════════════════════════════════════════════════════════════════════════════

/// Kind of a TLA+ declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TlaDeclKind {
    /// `CONSTANT` declaration.
    Constant,
    /// `VARIABLE` declaration.
    Variable,
    /// Operator definition: `Op == ...`.
    Operator,
    /// `THEOREM` (with optional proof body).
    Theorem,
    /// `LEMMA`.
    Lemma,
    /// `PROPOSITION`.
    Proposition,
    /// `COROLLARY`.
    Corollary,
    /// `AXIOM`.
    Axiom,
    /// `ASSUME` / `ASSUMPTION`.
    Assumption,
    /// `INSTANCE` with substitution.
    Instance,
}

/// A single TLA+ declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TlaDecl {
    /// Name of the declared entity.
    pub name: String,
    /// Kind of declaration.
    pub kind: TlaDeclKind,
    /// Parameters (for operator definitions).
    pub params: Vec<String>,
    /// Body expression (for operators, theorems with statements).
    pub body: Option<TlaExpr>,
}

impl TlaDecl {
    /// Whether this is a constant or variable declaration.
    #[must_use]
    pub fn is_state_component(&self) -> bool {
        matches!(self.kind, TlaDeclKind::Constant | TlaDeclKind::Variable)
    }

    /// Whether this is a theorem-like declaration.
    #[must_use]
    pub fn is_theorem_like(&self) -> bool {
        matches!(
            self.kind,
            TlaDeclKind::Theorem
                | TlaDeclKind::Lemma
                | TlaDeclKind::Proposition
                | TlaDeclKind::Corollary
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Module
// ════════════════════════════════════════════════════════════════════════════

/// A parsed TLA+ module.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TlaModule {
    /// Module name (from `---- MODULE Name ----`).
    pub name: String,
    /// EXTENDS list.
    pub extends: Vec<String>,
    /// All declarations.
    pub declarations: Vec<TlaDecl>,
}

impl TlaModule {
    /// Count declarations by kind.
    #[must_use]
    pub fn count_by_kind(&self, kind: TlaDeclKind) -> usize {
        self.declarations.iter().filter(|d| d.kind == kind).count()
    }

    /// Whether this module has no declarations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.declarations.is_empty()
    }

    /// Number of constants.
    #[must_use]
    pub fn constant_count(&self) -> usize {
        self.count_by_kind(TlaDeclKind::Constant)
    }

    /// Number of variables.
    #[must_use]
    pub fn variable_count(&self) -> usize {
        self.count_by_kind(TlaDeclKind::Variable)
    }

    /// Number of theorems (all theorem-like declarations).
    #[must_use]
    pub fn theorem_count(&self) -> usize {
        self.declarations
            .iter()
            .filter(|d| d.is_theorem_like())
            .count()
    }

    /// Number of operator definitions.
    #[must_use]
    pub fn operator_count(&self) -> usize {
        self.count_by_kind(TlaDeclKind::Operator)
    }

    /// Number of axioms + assumptions.
    #[must_use]
    pub fn axiom_count(&self) -> usize {
        self.count_by_kind(TlaDeclKind::Axiom) + self.count_by_kind(TlaDeclKind::Assumption)
    }

    /// All declared names.
    #[must_use]
    pub fn declared_names(&self) -> Vec<&str> {
        self.declarations.iter().map(|d| d.name.as_str()).collect()
    }
}
