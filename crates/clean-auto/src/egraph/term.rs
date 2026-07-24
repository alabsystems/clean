// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term representation and builder for E-graph extraction.

use super::{EClassId, EGraph};

/// A term (for extraction)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    /// A constant
    Const(String),
    /// A function application
    App(String, Vec<Term>),
}

impl Term {
    /// Get the size of this term (number of nodes)
    pub fn size(&self) -> usize {
        match self {
            Term::Const(_) => 1,
            Term::App(_, children) => 1 + children.iter().map(Term::size).sum::<usize>(),
        }
    }

    /// Pretty print the term
    pub fn to_string_pretty(&self) -> String {
        match self {
            Term::Const(name) => name.clone(),
            Term::App(name, children) if children.is_empty() => name.clone(),
            Term::App(name, children) => {
                let args: Vec<String> = children.iter().map(Term::to_string_pretty).collect();
                format!("{}({})", name, args.join(", "))
            }
        }
    }
}

/// Builder for adding complex terms to an e-graph
pub struct TermBuilder<'a> {
    egraph: &'a mut EGraph,
}

impl<'a> TermBuilder<'a> {
    /// Create a new term builder
    pub fn new(egraph: &'a mut EGraph) -> Self {
        TermBuilder { egraph }
    }

    /// Add a term to the e-graph
    pub fn add_term(&mut self, term: &Term) -> EClassId {
        match term {
            Term::Const(name) => self.egraph.add_const(name.as_str()),
            Term::App(name, children) => {
                let child_ids: Vec<EClassId> = children.iter().map(|c| self.add_term(c)).collect();
                self.egraph.add_app(name.as_str(), child_ids)
            }
        }
    }
}
