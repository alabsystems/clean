// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tracks which proofs reference which kernel constants.

use std::collections::{HashMap, HashSet};

use clean_kernel::{Expr, ExprVisitor, LevelVec, Name};
use serde::{Deserialize, Serialize};

use crate::error::DiscoveryError;

#[derive(Default)]
struct ConstDependencyCollector;

impl ExprVisitor for ConstDependencyCollector {
    type Result = HashSet<String>;

    fn combine(&self, mut a: Self::Result, b: Self::Result) -> Self::Result {
        a.extend(b);
        a
    }

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> Self::Result {
        HashSet::from([name.to_string()])
    }
}

/// Extract the set of constant names referenced by an expression.
#[must_use]
pub(crate) fn extract_dependencies(expr: &Expr) -> HashSet<String> {
    let mut collector = ConstDependencyCollector;
    collector.visit_expr(expr)
}

fn serialization_error(error: serde_json::Error) -> DiscoveryError {
    DiscoveryError::Serialization(error.to_string())
}

/// Maps proof names to the kernel constants they reference.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DependencyGraph {
    proof_dependencies: HashMap<String, HashSet<String>>,
}

impl DependencyGraph {
    /// Create an empty dependency graph.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add or replace a proof entry by scanning its proof term.
    pub(crate) fn add_proof(&mut self, proof_name: impl Into<String>, proof_term: &Expr) {
        let dependencies = extract_dependencies(proof_term);
        self.proof_dependencies
            .insert(proof_name.into(), dependencies);
    }

    /// Remove a proof entry if it exists.
    #[must_use]
    pub(crate) fn remove_proof(&mut self, proof_name: &str) -> bool {
        self.proof_dependencies.remove(proof_name).is_some()
    }

    /// Return the proofs that reference any changed constant.
    #[must_use]
    pub(crate) fn affected_proofs<I, S>(&self, changed_consts: I) -> HashSet<String>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let changed: HashSet<String> = changed_consts
            .into_iter()
            .map(|name| name.as_ref().to_string())
            .collect();

        if changed.is_empty() {
            return HashSet::new();
        }

        self.proof_dependencies
            .iter()
            .filter(|(_, dependencies)| dependencies.iter().any(|dep| changed.contains(dep)))
            .map(|(proof_name, _)| proof_name.clone())
            .collect()
    }

    /// Return the dependency set for a named proof.
    #[must_use]
    pub(crate) fn get_dependencies(&self, proof_name: &str) -> Option<&HashSet<String>> {
        self.proof_dependencies.get(proof_name)
    }

    /// Iterate over every proof tracked by the graph.
    pub(crate) fn all_proofs(&self) -> impl Iterator<Item = &str> + '_ {
        self.proof_dependencies.keys().map(String::as_str)
    }

    /// Serialize the graph to JSON.
    pub(crate) fn serialize(&self) -> Result<String, DiscoveryError> {
        serde_json::to_string_pretty(self).map_err(serialization_error)
    }

    /// Deserialize a graph from JSON.
    pub(crate) fn deserialize(json: &str) -> Result<Self, DiscoveryError> {
        serde_json::from_str(json).map_err(serialization_error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_const(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), LevelVec::new())
    }

    fn sorted_dependencies(graph: &DependencyGraph, proof_name: &str) -> Vec<String> {
        let mut values: Vec<String> = graph
            .get_dependencies(proof_name)
            .map(|deps| deps.iter().cloned().collect())
            .unwrap_or_default();
        values.sort();
        values
    }

    #[test]
    fn extract_dependencies_finds_consts() {
        let expr = Expr::app(
            Expr::app(mk_const("Nat.add"), mk_const("Nat.zero")),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                mk_const("Nat"),
                Expr::app(mk_const("Nat.succ"), mk_const("Nat.zero")),
            ),
        );

        let dependencies = extract_dependencies(&expr);

        assert_eq!(dependencies.len(), 4);
        assert!(dependencies.contains("Nat"));
        assert!(dependencies.contains("Nat.add"));
        assert!(dependencies.contains("Nat.succ"));
        assert!(dependencies.contains("Nat.zero"));
    }

    #[test]
    fn add_and_remove_proofs_updates_graph() {
        let mut graph = DependencyGraph::new();

        graph.add_proof("proof.alpha", &Expr::app(mk_const("A"), mk_const("B")));
        graph.add_proof("proof.beta", &Expr::app(mk_const("B"), mk_const("C")));

        assert_eq!(sorted_dependencies(&graph, "proof.alpha"), vec!["A", "B"]);
        assert_eq!(sorted_dependencies(&graph, "proof.beta"), vec!["B", "C"]);

        assert!(graph.remove_proof("proof.alpha"));
        assert!(graph.get_dependencies("proof.alpha").is_none());
        assert!(!graph.remove_proof("proof.alpha"));

        let remaining: HashSet<&str> = graph.all_proofs().collect();
        assert_eq!(remaining, HashSet::from(["proof.beta"]));
    }

    #[test]
    fn affected_proofs_queries_changed_constants() {
        let mut graph = DependencyGraph::new();

        graph.add_proof(
            "proof.one",
            &Expr::app(mk_const("Nat.add"), mk_const("Nat.zero")),
        );
        graph.add_proof(
            "proof.two",
            &Expr::app(mk_const("List.map"), mk_const("Nat.zero")),
        );
        graph.add_proof(
            "proof.three",
            &Expr::app(mk_const("Bool.and"), mk_const("Bool.true")),
        );

        let affected = graph.affected_proofs(["Nat.zero", "List.map"]);

        assert_eq!(affected.len(), 2);
        assert!(affected.contains("proof.one"));
        assert!(affected.contains("proof.two"));
        assert!(!affected.contains("proof.three"));
    }

    #[test]
    fn empty_graph_behaves_and_round_trips() {
        let graph = DependencyGraph::new();

        assert!(graph.all_proofs().next().is_none());
        assert!(graph.affected_proofs(["Nat.zero"]).is_empty());
        assert!(graph.get_dependencies("missing").is_none());

        let json = graph.serialize().expect("empty graph should serialize");
        let decoded = DependencyGraph::deserialize(&json).expect("graph should deserialize");

        assert_eq!(graph, decoded);
        assert!(decoded.all_proofs().next().is_none());
    }
}
