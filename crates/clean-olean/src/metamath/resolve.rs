// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Resolve active Metamath frames for labeled statements.

use super::ast::{
    Database, EssentialHyp, FloatingHyp, Formula, ResolvedAssertion, ResolvedDatabase,
    ResolvedStatement, Statement,
};
use super::{MetamathError, MetamathResult};
use hashbrown::{HashMap, HashSet};

/// Resolve active floating/essential hypotheses and disjoint-variable frames.
pub fn resolve_database(db: &Database) -> MetamathResult<ResolvedDatabase> {
    let mut resolver = Resolver::default();
    resolver.resolve_statements(&db.statements)?;
    Ok(ResolvedDatabase {
        statements: resolver.statements,
        labels: resolver.labels,
    })
}

#[derive(Default)]
struct Resolver {
    statements: Vec<ResolvedStatement>,
    labels: HashMap<String, usize>,
    active_floats: Vec<FloatingHyp>,
    active_essentials: Vec<EssentialHyp>,
    active_disjoints: Vec<(String, String)>,
}

impl Resolver {
    fn resolve_statements(&mut self, statements: &[Statement]) -> MetamathResult<()> {
        for statement in statements {
            match statement {
                Statement::Constants(_) | Statement::Variables(_) => {}
                Statement::Disjoint(vars) => self.add_disjoints(vars),
                Statement::Floating {
                    label,
                    typecode,
                    variable,
                } => {
                    let hyp = FloatingHyp {
                        label: label.clone(),
                        typecode: typecode.clone(),
                        variable: variable.clone(),
                    };
                    self.push_labeled(ResolvedStatement::Floating(hyp.clone()))?;
                    self.active_floats.push(hyp);
                }
                Statement::Essential { label, formula } => {
                    let hyp = EssentialHyp {
                        label: label.clone(),
                        formula: formula.clone(),
                    };
                    self.push_labeled(ResolvedStatement::Essential(hyp.clone()))?;
                    self.active_essentials.push(hyp);
                }
                Statement::Axiom { label, formula } => {
                    let assertion = self.resolve_assertion(label, "axiom", formula, None);
                    self.push_labeled(ResolvedStatement::Assertion(assertion))?;
                }
                Statement::Provable {
                    label,
                    formula,
                    proof,
                } => {
                    let assertion =
                        self.resolve_assertion(label, "provable", formula, Some(proof.clone()));
                    self.push_labeled(ResolvedStatement::Assertion(assertion))?;
                }
                Statement::Block(inner) => {
                    let snapshot = (
                        self.active_floats.len(),
                        self.active_essentials.len(),
                        self.active_disjoints.len(),
                    );
                    self.resolve_statements(inner)?;
                    self.active_floats.truncate(snapshot.0);
                    self.active_essentials.truncate(snapshot.1);
                    self.active_disjoints.truncate(snapshot.2);
                }
            }
        }
        Ok(())
    }

    fn push_labeled(&mut self, statement: ResolvedStatement) -> MetamathResult<()> {
        let label = statement.label().to_string();
        if self.labels.contains_key(&label) {
            return Err(MetamathError::DuplicateLabel(label));
        }
        self.labels.insert(label, self.statements.len());
        self.statements.push(statement);
        Ok(())
    }

    fn add_disjoints(&mut self, vars: &[String]) {
        for i in 0..vars.len() {
            for j in i + 1..vars.len() {
                self.active_disjoints.push(sorted_pair(&vars[i], &vars[j]));
            }
        }
    }

    fn resolve_assertion(
        &self,
        label: &str,
        kind: &'static str,
        formula: &Formula,
        proof: Option<super::ast::Proof>,
    ) -> ResolvedAssertion {
        let mandatory_vars = self.collect_mandatory_vars(formula);
        let mut seen = HashSet::new();
        let mut mandatory_floats = Vec::new();
        for hyp in self.active_floats.iter().rev() {
            if mandatory_vars.contains(&hyp.variable) && seen.insert(hyp.variable.clone()) {
                mandatory_floats.push(hyp.clone());
            }
        }
        mandatory_floats.reverse();
        let disjoints = self
            .active_disjoints
            .iter()
            .filter(|(left, right)| mandatory_vars.contains(left) && mandatory_vars.contains(right))
            .cloned()
            .collect();
        ResolvedAssertion {
            label: label.to_string(),
            kind,
            formula: formula.clone(),
            mandatory_floats,
            essential_hyps: self.active_essentials.clone(),
            disjoints,
            proof,
        }
    }

    fn collect_mandatory_vars(&self, formula: &Formula) -> HashSet<String> {
        let mut vars = HashSet::new();
        self.collect_formula_vars(formula, &mut vars);
        for hyp in &self.active_essentials {
            self.collect_formula_vars(&hyp.formula, &mut vars);
        }
        vars
    }

    fn collect_formula_vars(&self, formula: &Formula, out: &mut HashSet<String>) {
        for token in &formula.tokens {
            if self.lookup_float(token).is_some() {
                out.insert(token.clone());
            }
        }
    }

    fn lookup_float(&self, token: &str) -> Option<&FloatingHyp> {
        self.active_floats
            .iter()
            .rev()
            .find(|hyp| hyp.variable == token)
    }
}

fn sorted_pair(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_string(), right.to_string())
    } else {
        (right.to_string(), left.to_string())
    }
}
