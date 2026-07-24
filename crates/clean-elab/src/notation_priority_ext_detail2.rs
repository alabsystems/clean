// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeSet, HashMap};

use super::{
    analyze_priority_conflicts, conflicts_to_diagnostics, dedup_conflicts, maximal_indices,
    namespace_from_name, suggestions_for, ExtendedConflict, NamespacePriorityOverride,
    NotationPriority, PriorityConflictKind, PriorityDiagnostic, PriorityEntry, PriorityLattice,
    PriorityResolutionError, PriorityResolver,
};

/// A namespace-aware wrapper around `PriorityResolver`.
#[derive(Debug, Default)]
#[non_exhaustive]
pub(crate) struct ExtendedPriorityResolver {
    base: PriorityResolver,
    entries: Vec<PriorityEntry>,
    entry_namespaces: Vec<Option<String>>,
    token_index: HashMap<String, Vec<usize>>,
    scope_entries: Vec<Vec<usize>>,
    lattice: PriorityLattice,
    overrides: HashMap<String, NamespacePriorityOverride>,
    namespace_stack: Vec<String>,
    diagnostics: Vec<PriorityDiagnostic>,
}

impl ExtendedPriorityResolver {
    /// Create an empty resolver.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Create a resolver with a precomputed lattice.
    #[must_use]
    pub(crate) fn with_lattice(lattice: PriorityLattice) -> Self {
        Self {
            lattice,
            ..Self::default()
        }
    }

    /// Register an entry and return its stable index.
    pub(crate) fn register(&mut self, entry: PriorityEntry) -> usize {
        let idx = self.entries.len();
        let token = entry.pattern().leading_token().unwrap_or("").to_owned();
        self.base.register(entry.clone());
        self.lattice.insert(entry.priority());
        self.entries.push(entry.clone());
        self.entry_namespaces.push(
            self.namespace_stack
                .last()
                .cloned()
                .or_else(|| namespace_from_name(entry.name())),
        );
        self.token_index.entry(token).or_default().push(idx);
        if let Some(frame) = self.scope_entries.last_mut() {
            frame.push(idx);
        }
        self.diagnostics = conflicts_to_diagnostics(&self.analyze_conflicts());
        idx
    }

    /// Enter `namespace`, optionally inheriting the outer priority context.
    pub(crate) fn enter_namespace(&mut self, namespace: &str, inherit_priority: bool) {
        self.namespace_stack.push(namespace.to_owned());
        self.base.push_scope(inherit_priority);
        self.scope_entries.push(Vec::new());
        self.diagnostics = conflicts_to_diagnostics(&self.analyze_conflicts());
    }

    /// Exit the innermost namespace.
    pub(crate) fn exit_namespace(&mut self) {
        self.base.pop_scope();
        if let Some(indices) = self.scope_entries.pop() {
            for idx in indices {
                if let Some(entry) = self.entries.get_mut(idx) {
                    entry.deactivate();
                }
            }
        }
        self.namespace_stack.pop();
        self.diagnostics = conflicts_to_diagnostics(&self.analyze_conflicts());
    }

    /// Register a namespace-local priority override.
    pub(crate) fn register_namespace_override(&mut self, override_: NamespacePriorityOverride) {
        self.overrides
            .insert(override_.namespace.clone(), override_);
        self.diagnostics = conflicts_to_diagnostics(&self.analyze_conflicts());
    }

    /// Return accumulated diagnostics.
    #[must_use]
    pub(crate) fn diagnostics(&self) -> &[PriorityDiagnostic] {
        &self.diagnostics
    }

    /// Resolve `token` using effective priority ordering.
    pub(crate) fn resolve(
        &mut self,
        token: &str,
    ) -> Result<Option<&PriorityEntry>, PriorityResolutionError> {
        let candidates = self.active_indices(token);
        let maximal = maximal_indices(&candidates, &self.lattice, |idx| {
            self.effective_priority(*idx)
        });
        if maximal.is_empty() {
            return Ok(None);
        }
        if maximal.len() > 1 {
            return Err(PriorityResolutionError::AmbiguousParse {
                token: token.to_owned(),
                priority: maximal
                    .iter()
                    .map(|idx| self.effective_priority(candidates[*idx]))
                    .max()
                    .unwrap_or(NotationPriority::DEFAULT),
                candidates: maximal
                    .iter()
                    .filter_map(|idx| {
                        self.entries
                            .get(candidates[*idx])
                            .map(|e| e.name().to_owned())
                    })
                    .collect(),
            });
        }
        if let Some(active) = self.active_override(token) {
            if active.token_priorities.contains_key(token) {
                self.diagnostics.push(PriorityDiagnostic {
                    kind: PriorityConflictKind::NamespaceOverride,
                    message: format!(
                        "namespace '{}' overrides the priority of '{}'",
                        active.namespace, token
                    ),
                    suggestions: vec![format!(
                        "remove the '{}' override to restore the outer ordering",
                        token
                    )],
                });
            }
        }
        Ok(self.entries.get(candidates[maximal[0]]))
    }

    /// Analyze the current resolver state for conflicts.
    #[must_use]
    pub(crate) fn analyze_conflicts(&self) -> Vec<ExtendedConflict> {
        let active = self
            .entries
            .iter()
            .filter(|entry| entry.is_active())
            .cloned()
            .collect::<Vec<_>>();
        let mut conflicts = analyze_priority_conflicts(&active, &self.lattice);
        for base in self.base.detect_conflicts() {
            conflicts.push(ExtendedConflict {
                kind: PriorityConflictKind::AssociativityMismatch,
                token: base.token.clone(),
                first: base.first.clone(),
                second: base.second.clone(),
                priority: Some(base.priority),
                namespaces: BTreeSet::new(),
                suggestions: suggestions_for(
                    PriorityConflictKind::AssociativityMismatch,
                    &base.token,
                ),
                base_conflict: Some(base),
            });
        }
        if let Some(namespace) = self.namespace_stack.last() {
            if let Some(override_) = self.overrides.get(namespace) {
                for token in &override_.shadow_tokens {
                    let total = self.token_index.get(token).map_or(0, Vec::len);
                    let local = self.token_index.get(token).map_or(0, |indices| {
                        indices
                            .iter()
                            .filter(|idx| {
                                self.entry_namespaces.get(**idx).and_then(Option::as_deref)
                                    == Some(namespace)
                            })
                            .count()
                    });
                    if local > 0 && total > local {
                        conflicts.push(ExtendedConflict {
                            kind: PriorityConflictKind::ScopeShadowing,
                            token: token.clone(),
                            first: namespace.clone(),
                            second: "outer scope".to_owned(),
                            priority: None,
                            namespaces: BTreeSet::from([namespace.clone()]),
                            suggestions: suggestions_for(
                                PriorityConflictKind::ScopeShadowing,
                                token,
                            ),
                            base_conflict: None,
                        });
                    }
                }
            }
        }
        dedup_conflicts(conflicts)
    }

    fn active_indices(&self, token: &str) -> Vec<usize> {
        let mut indices = self
            .token_index
            .get(token)
            .into_iter()
            .flat_map(|items| items.iter().copied())
            .filter(|idx| self.entries.get(*idx).is_some_and(PriorityEntry::is_active))
            .collect::<Vec<_>>();
        if let Some(namespace) = self.namespace_stack.last() {
            if let Some(override_) = self.overrides.get(namespace) {
                if override_.shadow_tokens.contains(token) {
                    let local = indices
                        .iter()
                        .copied()
                        .filter(|idx| {
                            self.entry_namespaces.get(*idx).and_then(Option::as_deref)
                                == Some(namespace.as_str())
                        })
                        .collect::<Vec<_>>();
                    if !local.is_empty() {
                        indices = local;
                    }
                }
            }
        }
        indices
    }

    fn active_override(&self, token: &str) -> Option<&NamespacePriorityOverride> {
        self.namespace_stack.iter().rev().find_map(|namespace| {
            self.overrides.get(namespace).filter(|ovr| {
                ovr.token_priorities.contains_key(token) || ovr.default_priority.is_some()
            })
        })
    }

    fn effective_priority(&self, idx: usize) -> NotationPriority {
        let Some(entry) = self.entries.get(idx) else {
            return NotationPriority::DEFAULT;
        };
        let token = entry.pattern().leading_token().unwrap_or("");
        for namespace in self.namespace_stack.iter().rev() {
            if let Some(override_) = self.overrides.get(namespace) {
                if let Some(priority) = override_.token_priorities.get(token) {
                    return *priority;
                }
                if self.entry_namespaces.get(idx).and_then(Option::as_deref)
                    == Some(namespace.as_str())
                {
                    if let Some(priority) = override_.default_priority {
                        return priority;
                    }
                }
            }
        }
        entry.priority()
    }
}
