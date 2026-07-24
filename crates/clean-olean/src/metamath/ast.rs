// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AST and resolved-frame types for Metamath.

use hashbrown::HashMap;

/// Parsed Metamath database.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Database {
    /// Top-level statements in source order.
    pub statements: Vec<Statement>,
}

/// Parsed Metamath statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Constants(Vec<String>),
    Variables(Vec<String>),
    Disjoint(Vec<String>),
    Floating {
        label: String,
        typecode: String,
        variable: String,
    },
    Essential {
        label: String,
        formula: Formula,
    },
    Axiom {
        label: String,
        formula: Formula,
    },
    Provable {
        label: String,
        formula: Formula,
        proof: Proof,
    },
    Block(Vec<Statement>),
}

/// Metamath expression: a typecode plus token list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Formula {
    pub typecode: String,
    pub tokens: Vec<String>,
}

impl Formula {
    /// Render the formula in Metamath surface form.
    #[must_use]
    pub fn render(&self) -> String {
        if self.tokens.is_empty() {
            self.typecode.clone()
        } else {
            format!("{} {}", self.typecode, self.tokens.join(" "))
        }
    }
}

/// Parsed Metamath proof payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proof {
    Uncompressed(Vec<String>),
    Compressed(CompressedProof),
}

/// Metamath compressed proof payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompressedProof {
    pub labels: Vec<String>,
    pub code: String,
}

/// Active floating hypothesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FloatingHyp {
    pub label: String,
    pub typecode: String,
    pub variable: String,
}

/// Active essential hypothesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EssentialHyp {
    pub label: String,
    pub formula: Formula,
}

/// Resolved labeled assertion with its active frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedAssertion {
    pub label: String,
    pub kind: &'static str,
    pub formula: Formula,
    pub mandatory_floats: Vec<FloatingHyp>,
    pub essential_hyps: Vec<EssentialHyp>,
    pub disjoints: Vec<(String, String)>,
    pub proof: Option<Proof>,
}

/// Resolved labeled Metamath item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedStatement {
    Floating(FloatingHyp),
    Essential(EssentialHyp),
    Assertion(ResolvedAssertion),
}

impl ResolvedStatement {
    /// Label for this resolved item.
    #[must_use]
    pub fn label(&self) -> &str {
        match self {
            Self::Floating(hyp) => &hyp.label,
            Self::Essential(hyp) => &hyp.label,
            Self::Assertion(assertion) => &assertion.label,
        }
    }
}

/// Resolved database with label lookup.
#[derive(Debug, Clone, Default)]
pub struct ResolvedDatabase {
    pub statements: Vec<ResolvedStatement>,
    pub labels: HashMap<String, usize>,
}

impl ResolvedDatabase {
    /// Lookup a resolved item by label.
    #[must_use]
    pub fn get(&self, label: &str) -> Option<&ResolvedStatement> {
        self.labels
            .get(label)
            .and_then(|idx| self.statements.get(*idx))
    }
}
