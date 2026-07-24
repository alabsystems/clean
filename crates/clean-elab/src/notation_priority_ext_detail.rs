// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet};

use thiserror::Error;

use super::{
    Associativity, MixfixPattern, NotationPriority, PriorityConflict, PriorityEntry,
    PriorityResolver,
};

#[path = "notation_priority_ext_detail2.rs"]
mod detail2;

#[cfg(test)]
pub(crate) use detail2::ExtendedPriorityResolver;

/// Errors produced by extended priority analysis and disambiguation.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum PriorityResolutionError {
    #[error("priority cycle detected involving {0}")]
    CyclicOrder(NotationPriority),
    #[error("ambiguous notation for '{token}' at priority {priority}{}", format_candidates(.candidates))]
    AmbiguousParse {
        token: String,
        priority: NotationPriority,
        candidates: Vec<String>,
    },
}

/// A partial order over notation priorities with cached transitive closure.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub(crate) struct PriorityLattice {
    edges: HashMap<NotationPriority, BTreeSet<NotationPriority>>,
    closure: HashMap<NotationPriority, BTreeSet<NotationPriority>>,
}

impl PriorityLattice {
    /// Create an empty lattice.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Build a lattice from the priorities present in `entries`.
    #[must_use]
    pub(crate) fn from_entries(entries: &[PriorityEntry]) -> Self {
        let mut lattice = Self::new();
        let mut priorities = BTreeSet::new();
        for entry in entries {
            priorities.insert(entry.priority());
            lattice.insert(entry.priority());
        }
        let ordered: Vec<_> = priorities.into_iter().collect();
        for window in ordered.windows(2) {
            let _ = lattice.declare_tighter(window[1], window[0]);
        }
        lattice
    }

    /// Add an explicit `tighter > looser` relation.
    pub(crate) fn declare_tighter(
        &mut self,
        tighter: NotationPriority,
        looser: NotationPriority,
    ) -> Result<(), PriorityResolutionError> {
        if tighter == looser {
            return Err(PriorityResolutionError::CyclicOrder(tighter));
        }
        self.insert(tighter);
        self.insert(looser);
        self.edges.entry(tighter).or_default().insert(looser);
        self.rebuild_closure();
        if self.is_tighter_than(looser, tighter) {
            if let Some(next) = self.edges.get_mut(&tighter) {
                next.remove(&looser);
            }
            self.rebuild_closure();
            return Err(PriorityResolutionError::CyclicOrder(tighter));
        }
        Ok(())
    }

    /// Return all known priorities in ascending order.
    #[must_use]
    pub(crate) fn priorities(&self) -> Vec<NotationPriority> {
        self.edges
            .keys()
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// Check whether `left` binds more tightly than `right`.
    #[must_use]
    pub(crate) fn is_tighter_than(&self, left: NotationPriority, right: NotationPriority) -> bool {
        self.closure
            .get(&left)
            .is_some_and(|set| set.contains(&right))
    }

    /// Compare priorities inside the partial order.
    #[must_use]
    pub(crate) fn compare(
        &self,
        left: NotationPriority,
        right: NotationPriority,
    ) -> Option<Ordering> {
        if left == right {
            Some(Ordering::Equal)
        } else if self.is_tighter_than(left, right) {
            Some(Ordering::Greater)
        } else if self.is_tighter_than(right, left) {
            Some(Ordering::Less)
        } else {
            None
        }
    }

    /// Insert a priority without adding any ordering relation.
    pub(crate) fn insert(&mut self, priority: NotationPriority) {
        self.edges.entry(priority).or_default();
        self.closure.entry(priority).or_default();
    }

    fn rebuild_closure(&mut self) {
        let keys: Vec<_> = self.edges.keys().copied().collect();
        let mut closure = HashMap::new();
        for start in keys {
            let mut seen = BTreeSet::new();
            let mut stack = self
                .edges
                .get(&start)
                .map_or_else(Vec::new, |next| next.iter().copied().collect::<Vec<_>>());
            while let Some(next) = stack.pop() {
                if seen.insert(next) {
                    if let Some(children) = self.edges.get(&next) {
                        stack.extend(children.iter().copied());
                    }
                }
            }
            closure.insert(start, seen);
        }
        self.closure = closure;
    }
}

/// Categories of extended priority conflicts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum PriorityConflictKind {
    AssociativityMismatch,
    PriorityAmbiguity,
    IncomparablePriority,
    OverlappingPattern,
    ScopeShadowing,
    NamespaceOverride,
}

/// Rich conflict information produced by priority analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) struct ExtendedConflict {
    pub(crate) kind: PriorityConflictKind,
    pub(crate) token: String,
    pub(crate) first: String,
    pub(crate) second: String,
    pub(crate) priority: Option<NotationPriority>,
    pub(crate) namespaces: BTreeSet<String>,
    pub(crate) suggestions: Vec<String>,
    pub(crate) base_conflict: Option<PriorityConflict>,
}

/// A user-facing diagnostic for priority conflicts.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) struct PriorityDiagnostic {
    pub(crate) kind: PriorityConflictKind,
    pub(crate) message: String,
    pub(crate) suggestions: Vec<String>,
}

/// Priority adjustments that become active inside a namespace.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub(crate) struct NamespacePriorityOverride {
    pub(crate) namespace: String,
    pub(crate) default_priority: Option<NotationPriority>,
    pub(crate) token_priorities: HashMap<String, NotationPriority>,
    pub(crate) shadow_tokens: HashSet<String>,
}

impl NamespacePriorityOverride {
    /// Create a namespace override.
    #[must_use]
    pub(crate) fn new(namespace: &str) -> Self {
        Self {
            namespace: namespace.to_owned(),
            ..Self::default()
        }
    }

    /// Override the namespace default priority.
    #[must_use]
    pub(crate) fn with_default_priority(mut self, priority: NotationPriority) -> Self {
        self.default_priority = Some(priority);
        self
    }

    /// Override the effective priority of `token`.
    #[must_use]
    pub(crate) fn with_token_priority(mut self, token: &str, priority: NotationPriority) -> Self {
        self.token_priorities.insert(token.to_owned(), priority);
        self
    }

    /// Prefer same-namespace candidates for `token`.
    #[must_use]
    pub(crate) fn with_shadow_token(mut self, token: &str) -> Self {
        self.shadow_tokens.insert(token.to_owned());
        self
    }
}

/// Build a priority lattice from `entries`.
#[must_use]
pub(crate) fn build_priority_lattice(entries: &[PriorityEntry]) -> PriorityLattice {
    PriorityLattice::from_entries(entries)
}

/// Check whether two mixfix patterns overlap syntactically.
#[must_use]
pub(crate) fn patterns_overlap(left: &MixfixPattern, right: &MixfixPattern) -> bool {
    left.leading_token() == right.leading_token()
        && left.arity() == right.arity()
        && (left.tokens() == right.tokens() || left.is_led() == right.is_led())
}

/// Analyze `entries` for extended priority conflicts.
#[must_use]
pub(crate) fn analyze_priority_conflicts(
    entries: &[PriorityEntry],
    lattice: &PriorityLattice,
) -> Vec<ExtendedConflict> {
    let mut by_token: HashMap<String, Vec<&PriorityEntry>> = HashMap::new();
    for entry in entries.iter().filter(|entry| entry.is_active()) {
        by_token
            .entry(entry.pattern().leading_token().unwrap_or("").to_owned())
            .or_default()
            .push(entry);
    }
    let mut conflicts = Vec::new();
    for (token, group) in by_token {
        for i in 0..group.len() {
            for j in (i + 1)..group.len() {
                let (first, second) = (group[i], group[j]);
                if !patterns_overlap(first.pattern(), second.pattern()) {
                    continue;
                }
                let namespaces = namespaces_for(first, second);
                if associativity_conflict(first.assoc(), second.assoc())
                    && first.priority() == second.priority()
                {
                    conflicts.push(make_conflict(
                        PriorityConflictKind::AssociativityMismatch,
                        &token,
                        first,
                        second,
                        Some(first.priority()),
                        namespaces.clone(),
                        Some(PriorityConflict {
                            token: token.clone(),
                            priority: first.priority(),
                            first: first.name().to_owned(),
                            second: second.name().to_owned(),
                        }),
                    ));
                }
                if first.priority() == second.priority() {
                    conflicts.push(make_conflict(
                        PriorityConflictKind::PriorityAmbiguity,
                        &token,
                        first,
                        second,
                        Some(first.priority()),
                        namespaces.clone(),
                        None,
                    ));
                } else if lattice
                    .compare(first.priority(), second.priority())
                    .is_none()
                {
                    conflicts.push(make_conflict(
                        PriorityConflictKind::IncomparablePriority,
                        &token,
                        first,
                        second,
                        None,
                        namespaces.clone(),
                        None,
                    ));
                }
                if first.pattern().tokens() == second.pattern().tokens() {
                    conflicts.push(make_conflict(
                        PriorityConflictKind::OverlappingPattern,
                        &token,
                        first,
                        second,
                        Some(std::cmp::min(first.priority(), second.priority())),
                        namespaces.clone(),
                        None,
                    ));
                }
            }
        }
    }
    dedup_conflicts(conflicts)
}

/// Resolve candidates using their declared priorities.
pub(crate) fn disambiguate_by_priority<'a>(
    token: &str,
    candidates: &[&'a PriorityEntry],
    lattice: &PriorityLattice,
) -> Result<Option<&'a PriorityEntry>, PriorityResolutionError> {
    let maximal = maximal_indices(candidates, lattice, |entry| entry.priority());
    if maximal.is_empty() {
        return Ok(None);
    }
    if maximal.len() > 1 {
        return Err(PriorityResolutionError::AmbiguousParse {
            token: token.to_owned(),
            priority: maximal
                .iter()
                .map(|idx| candidates[*idx].priority())
                .max()
                .unwrap_or(NotationPriority::DEFAULT),
            candidates: maximal
                .iter()
                .map(|idx| candidates[*idx].name().to_owned())
                .collect(),
        });
    }
    Ok(Some(candidates[maximal[0]]))
}

/// Convert conflicts into user-facing diagnostics.
#[must_use]
pub(crate) fn conflicts_to_diagnostics(conflicts: &[ExtendedConflict]) -> Vec<PriorityDiagnostic> {
    conflicts
        .iter()
        .map(|conflict| PriorityDiagnostic {
            kind: conflict.kind,
            message: match conflict.priority {
                Some(priority) => format!(
                    "priority conflict for '{}' between '{}' and '{}' at {}",
                    conflict.token, conflict.first, conflict.second, priority
                ),
                None => format!(
                    "priority conflict for '{}' between '{}' and '{}'",
                    conflict.token, conflict.first, conflict.second
                ),
            },
            suggestions: conflict.suggestions.clone(),
        })
        .collect()
}

pub(super) fn format_candidates(candidates: &[String]) -> String {
    if candidates.is_empty() {
        String::new()
    } else {
        format!("; candidates: {}", candidates.join(", "))
    }
}

pub(super) fn associativity_conflict(left: Associativity, right: Associativity) -> bool {
    left != right
}

pub(super) fn maximal_indices<T, F>(
    items: &[T],
    lattice: &PriorityLattice,
    priority_of: F,
) -> Vec<usize>
where
    F: Fn(&T) -> NotationPriority,
{
    items
        .iter()
        .enumerate()
        .filter(|(idx, item)| {
            !items.iter().enumerate().any(|(other_idx, other)| {
                *idx != other_idx
                    && lattice.compare(priority_of(other), priority_of(item))
                        == Some(Ordering::Greater)
            })
        })
        .map(|(idx, _)| idx)
        .collect()
}

pub(super) fn namespace_from_name(name: &str) -> Option<String> {
    name.rsplit_once('.')
        .map(|(ns, _)| ns.to_owned())
        .filter(|ns| !ns.is_empty())
}

pub(super) fn namespaces_for(first: &PriorityEntry, second: &PriorityEntry) -> BTreeSet<String> {
    let mut namespaces = BTreeSet::new();
    if let Some(namespace) = namespace_from_name(first.name()) {
        namespaces.insert(namespace);
    }
    if let Some(namespace) = namespace_from_name(second.name()) {
        namespaces.insert(namespace);
    }
    namespaces
}

pub(super) fn make_conflict(
    kind: PriorityConflictKind,
    token: &str,
    first: &PriorityEntry,
    second: &PriorityEntry,
    priority: Option<NotationPriority>,
    namespaces: BTreeSet<String>,
    base_conflict: Option<PriorityConflict>,
) -> ExtendedConflict {
    ExtendedConflict {
        kind,
        token: token.to_owned(),
        first: first.name().to_owned(),
        second: second.name().to_owned(),
        priority,
        namespaces,
        suggestions: suggestions_for(kind, token),
        base_conflict,
    }
}

pub(super) fn dedup_conflicts(conflicts: Vec<ExtendedConflict>) -> Vec<ExtendedConflict> {
    let mut seen = HashSet::new();
    conflicts
        .into_iter()
        .filter(|conflict| {
            seen.insert(format!(
                "{:?}|{}|{}|{}|{:?}",
                conflict.kind, conflict.token, conflict.first, conflict.second, conflict.priority
            ))
        })
        .collect()
}

pub(super) fn suggestions_for(kind: PriorityConflictKind, token: &str) -> Vec<String> {
    match kind {
        PriorityConflictKind::AssociativityMismatch => vec![
            format!("align the associativity of '{token}' across declarations"),
            "assign one declaration a distinct priority".to_owned(),
        ],
        PriorityConflictKind::PriorityAmbiguity => vec![
            format!("raise or lower one '{token}' declaration"),
            "add explicit parentheses to disambiguate parses".to_owned(),
        ],
        PriorityConflictKind::IncomparablePriority => vec![
            "add an explicit priority ordering edge".to_owned(),
            "move one notation into a narrower namespace".to_owned(),
        ],
        PriorityConflictKind::OverlappingPattern => vec![
            "narrow one pattern so the token sequence no longer overlaps".to_owned(),
            "rename one notation entry".to_owned(),
        ],
        PriorityConflictKind::ScopeShadowing => vec![
            "rename the local notation or remove the shadow rule".to_owned(),
            "qualify the namespace at the use site".to_owned(),
        ],
        PriorityConflictKind::NamespaceOverride => vec![
            "remove the namespace-local priority override".to_owned(),
            "document the override near the notation declaration".to_owned(),
        ],
    }
}
