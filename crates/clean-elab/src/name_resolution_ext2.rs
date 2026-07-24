// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Variant names share an enum-prefix by design (e.g., 'KindFoo', 'KindBar' for KindKind enums); renaming is API-breaking.
#![allow(clippy::enum_variant_names)]

//! Extended name resolution analysis (phase 2).
//!
//! Builds on [`crate::name_resolution_ext`] with ambiguity classification,
//! namespace traversal, shadow detection, resolution statistics, completion
//! candidates, import impact analysis, and resolution explanation.

use crate::name_resolution_ext::{
    NameResolutionExt, ResolutionCandidate, ResolutionResult, ResolutionSource,
};
use crate::namespace::NamespaceState;
use clean_kernel::name::Name;
use clean_kernel::Environment;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Errors from extended name resolution analysis.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum NameResolutionExt2Error {
    #[error("namespace not found: {0}")]
    NamespaceNotFound(String),
    #[error("traversal depth limit exceeded (max {max_depth})")]
    DepthLimitExceeded { max_depth: usize },
}

// ---- Ambiguity analysis ---------------------------------------------------

/// Classification of a name ambiguity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AmbiguityKind {
    OpenNamespaceConflict,
    AutoOpenConflict,
    MixedSourceConflict,
}

/// A classified ambiguity with resolution suggestions.
#[derive(Debug, Clone)]
pub(crate) struct AmbiguityReport {
    pub(crate) name: String,
    pub(crate) kind: AmbiguityKind,
    pub(crate) candidates: Vec<ResolutionCandidate>,
    pub(crate) suggestions: Vec<String>,
}

/// Classify an ambiguous resolution result and generate suggestions.
#[must_use]
pub(crate) fn classify_ambiguity(
    name: &str,
    candidates: &[ResolutionCandidate],
) -> AmbiguityReport {
    let (mut has_open, mut has_auto, mut has_other) = (false, false, false);
    for c in candidates {
        match &c.source {
            ResolutionSource::OpenNamespace(_) => has_open = true,
            ResolutionSource::AutoOpen(_) => has_auto = true,
            _ => has_other = true,
        }
    }
    let kind = if has_open && !has_auto && !has_other {
        AmbiguityKind::OpenNamespaceConflict
    } else if has_auto && !has_open && !has_other {
        AmbiguityKind::AutoOpenConflict
    } else {
        AmbiguityKind::MixedSourceConflict
    };

    let mut suggestions: Vec<String> = candidates
        .iter()
        .map(|c| format!("use fully qualified name `{}`", c.name))
        .collect();
    match &kind {
        AmbiguityKind::OpenNamespaceConflict => {
            suggestions.push(format!(
                "close one of the conflicting namespaces for `{name}`"
            ));
        }
        AmbiguityKind::AutoOpenConflict => {
            suggestions.push("disable auto-open or restrict auto-open associations".into());
        }
        AmbiguityKind::MixedSourceConflict => {
            suggestions.push(format!("use a local alias to disambiguate `{name}`"));
        }
    }
    AmbiguityReport {
        name: name.to_string(),
        kind,
        candidates: candidates.to_vec(),
        suggestions,
    }
}

// ---- Namespace traversal --------------------------------------------------

/// Configuration for namespace traversal.
#[derive(Debug, Clone)]
pub(crate) struct TraversalConfig {
    pub(crate) max_depth: usize,
    pub(crate) prefix_filter: Option<String>,
    pub(crate) max_results: usize,
}

impl Default for TraversalConfig {
    fn default() -> Self {
        Self {
            max_depth: 10,
            prefix_filter: None,
            max_results: 1000,
        }
    }
}

/// A node in the namespace hierarchy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NamespaceNode {
    pub(crate) name: Name,
    pub(crate) depth: usize,
    pub(crate) is_constant: bool,
    pub(crate) child_count: usize,
}

/// Walk the namespace hierarchy under `root`, returning nodes up to configured depth.
pub(crate) fn traverse_namespace(
    root: &Name,
    env: &Environment,
    config: &TraversalConfig,
) -> Result<Vec<NamespaceNode>, NameResolutionExt2Error> {
    let root_str = root.to_string();
    let prefix = if root.is_anon() {
        String::new()
    } else {
        format!("{root_str}.")
    };
    let mut nodes: BTreeMap<String, NamespaceNode> = BTreeMap::new();
    let mut count = 0usize;

    for ci in env.constants() {
        let name_str = ci.name.to_string();
        let suffix = if prefix.is_empty() {
            name_str.as_str()
        } else if let Some(s) = name_str.strip_prefix(&prefix) {
            s
        } else {
            continue;
        };
        if let Some(ref pf) = config.prefix_filter {
            if !suffix.starts_with(pf.as_str()) {
                continue;
            }
        }
        let parts: Vec<&str> = suffix.split('.').collect();
        for (i, _) in parts.iter().enumerate() {
            if i > config.max_depth {
                break;
            }
            let comp = if prefix.is_empty() {
                parts[..=i].join(".")
            } else {
                format!("{}{}", prefix, parts[..=i].join("."))
            };
            let is_leaf = i == parts.len() - 1;
            let entry = nodes.entry(comp.clone()).or_insert_with(|| {
                count += 1;
                NamespaceNode {
                    name: Name::from_string(&comp),
                    depth: i,
                    is_constant: false,
                    child_count: 0,
                }
            });
            if is_leaf {
                entry.is_constant = true;
            }
            if i > 0 {
                let parent = if prefix.is_empty() {
                    parts[..i].join(".")
                } else {
                    format!("{}{}", prefix, parts[..i].join("."))
                };
                if let Some(p) = nodes.get_mut(&parent) {
                    p.child_count += 1;
                }
            }
        }
        if count >= config.max_results {
            break;
        }
    }
    if nodes.is_empty() && !root.is_anon() && env.get_const(root).is_none() {
        return Err(NameResolutionExt2Error::NamespaceNotFound(root_str));
    }
    Ok(nodes.into_values().collect())
}

// ---- Shadow detection -----------------------------------------------------

/// A single shadow relationship: `shadower` hides `shadowed`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ShadowEntry {
    pub(crate) short_name: String,
    pub(crate) shadower: ResolutionCandidate,
    pub(crate) shadowed: ResolutionCandidate,
}

/// Detect all shadowed names visible from the current scope.
#[must_use]
pub(crate) fn detect_shadows(
    resolver: &mut NameResolutionExt,
    ns_state: &NamespaceState,
    env: &Environment,
) -> Vec<ShadowEntry> {
    let mut shadows = Vec::new();
    let mut seen: BTreeMap<String, Vec<ResolutionCandidate>> = BTreeMap::new();
    for open_ns in ns_state.open_namespaces() {
        let pfx = format!("{}.", open_ns);
        for ci in env.constants() {
            let ns = ci.name.to_string();
            if let Some(suffix) = ns.strip_prefix(&pfx) {
                if !suffix.contains('.') {
                    seen.entry(suffix.to_string())
                        .or_default()
                        .push(ResolutionCandidate {
                            name: ci.name.clone(),
                            source: ResolutionSource::OpenNamespace(open_ns.clone()),
                        });
                }
            }
        }
    }
    for (short, cands) in &seen {
        let resolved = resolver.resolve(&Name::from_string(short), ns_state, env);
        if let ResolutionResult::Resolved(winner) = resolved {
            for c in cands {
                if c.name != winner.name {
                    shadows.push(ShadowEntry {
                        short_name: short.clone(),
                        shadower: winner.clone(),
                        shadowed: c.clone(),
                    });
                }
            }
        }
    }
    shadows
}

/// Format a shadow chain for display.
#[must_use]
pub(crate) fn format_shadow_chain(shadows: &[ShadowEntry]) -> String {
    if shadows.is_empty() {
        return "no shadows detected".to_string();
    }
    shadows
        .iter()
        .map(|s| {
            format!(
                "`{}`: {} (via {}) shadows {} (via {})",
                s.short_name,
                s.shadower.name,
                format_source(&s.shadower.source),
                s.shadowed.name,
                format_source(&s.shadowed.source),
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

// ---- Resolution statistics ------------------------------------------------

/// Tracks resolution performance metrics.
#[derive(Debug, Clone, Default)]
pub(crate) struct ResolutionStats {
    pub(crate) total_lookups: u64,
    pub(crate) successes: u64,
    pub(crate) ambiguities: u64,
    pub(crate) failures: u64,
    pub(crate) cache_hits: u64,
    pub(crate) total_depth: u64,
}

impl ResolutionStats {
    pub(crate) fn record(&mut self, result: &ResolutionResult, was_cache_hit: bool) {
        self.total_lookups += 1;
        if was_cache_hit {
            self.cache_hits += 1;
        }
        match result {
            ResolutionResult::Resolved(c) => {
                self.successes += 1;
                self.total_depth += source_depth(&c.source);
            }
            ResolutionResult::Ambiguous(_) => self.ambiguities += 1,
            ResolutionResult::Unresolved => self.failures += 1,
        }
    }

    #[must_use]
    pub(crate) fn success_rate(&self) -> f64 {
        if self.total_lookups == 0 {
            0.0
        } else {
            self.successes as f64 / self.total_lookups as f64
        }
    }

    #[must_use]
    pub(crate) fn cache_hit_rate(&self) -> f64 {
        if self.total_lookups == 0 {
            0.0
        } else {
            self.cache_hits as f64 / self.total_lookups as f64
        }
    }

    #[must_use]
    pub(crate) fn avg_lookup_depth(&self) -> f64 {
        if self.successes == 0 {
            0.0
        } else {
            self.total_depth as f64 / self.successes as f64
        }
    }
}

impl fmt::Display for ResolutionStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "lookups={}, success={:.1}%, cache_hit={:.1}%, avg_depth={:.2}",
            self.total_lookups,
            self.success_rate() * 100.0,
            self.cache_hit_rate() * 100.0,
            self.avg_lookup_depth()
        )
    }
}

fn source_depth(source: &ResolutionSource) -> u64 {
    match source {
        ResolutionSource::Local => 0,
        ResolutionSource::OpenNamespace(_) => 1,
        ResolutionSource::Alias(_) => 2,
        ResolutionSource::AutoOpen(_) => 3,
        ResolutionSource::Global => 4,
    }
}

// ---- Completion candidates ------------------------------------------------

/// A completion candidate with relevance metadata.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CompletionCandidate {
    pub(crate) name: Name,
    pub(crate) display_text: String,
    pub(crate) source: CompletionSource,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CompletionSource {
    CurrentNamespace,
    OpenNamespace(Name),
    Alias,
    Global,
}

/// Generate completion candidates for a prefix within the current scope.
#[must_use]
pub(crate) fn get_completion_candidates(
    prefix: &str,
    ns_state: &NamespaceState,
    env: &Environment,
    max_results: usize,
) -> Vec<CompletionCandidate> {
    let mut cands = BTreeSet::new();
    let cur_ns = ns_state.current_namespace();
    if !cur_ns.is_anon() {
        let search = format!("{cur_ns}.{prefix}");
        let strip = format!("{cur_ns}.");
        for ci in env.constants() {
            let ns = ci.name.to_string();
            if ns.starts_with(&search) {
                let short = ns.strip_prefix(&strip).unwrap_or(&ns);
                cands.insert(CompletionCandidate {
                    name: ci.name.clone(),
                    display_text: short.to_string(),
                    source: CompletionSource::CurrentNamespace,
                });
            }
        }
    }
    for open_ns in ns_state.open_namespaces() {
        let search = format!("{open_ns}.{prefix}");
        let strip = format!("{open_ns}.");
        for ci in env.constants() {
            let ns = ci.name.to_string();
            if ns.starts_with(&search) {
                let short = ns.strip_prefix(&strip).unwrap_or(&ns);
                if !short.contains('.') || short.starts_with(prefix) {
                    cands.insert(CompletionCandidate {
                        name: ci.name.clone(),
                        display_text: short.to_string(),
                        source: CompletionSource::OpenNamespace(open_ns.clone()),
                    });
                }
            }
        }
    }
    for ci in env.constants() {
        let ns = ci.name.to_string();
        if ns.starts_with(prefix) {
            cands.insert(CompletionCandidate {
                name: ci.name.clone(),
                display_text: ns,
                source: CompletionSource::Global,
            });
        }
    }
    cands.into_iter().take(max_results).collect()
}

// ---- Import impact analysis -----------------------------------------------

/// The impact of opening a namespace on existing name resolution.
#[derive(Debug, Clone)]
pub(crate) struct ImportImpact {
    pub(crate) namespace: Name,
    pub(crate) new_names: Vec<Name>,
    pub(crate) new_ambiguities: Vec<(String, Vec<Name>)>,
    pub(crate) new_shadows: Vec<ShadowEntry>,
}

/// Analyze the impact of opening a namespace.
#[must_use]
pub(crate) fn analyze_import_impact(
    namespace: &Name,
    resolver: &mut NameResolutionExt,
    ns_state: &NamespaceState,
    env: &Environment,
) -> ImportImpact {
    let ns_prefix = format!("{}.", namespace);
    let mut new_names = Vec::new();
    let mut ambiguity_map: BTreeMap<String, Vec<Name>> = BTreeMap::new();
    let mut new_shadows = Vec::new();
    let mut proposed: BTreeMap<String, Name> = BTreeMap::new();
    for ci in env.constants() {
        let ns = ci.name.to_string();
        if let Some(suffix) = ns.strip_prefix(&ns_prefix) {
            if !suffix.contains('.') {
                proposed.insert(suffix.to_string(), ci.name.clone());
            }
        }
    }
    for (short, full) in &proposed {
        match resolver.resolve(&Name::from_string(short), ns_state, env) {
            ResolutionResult::Unresolved => new_names.push(full.clone()),
            ResolutionResult::Resolved(existing) => {
                if existing.name != *full {
                    new_shadows.push(ShadowEntry {
                        short_name: short.clone(),
                        shadower: existing,
                        shadowed: ResolutionCandidate {
                            name: full.clone(),
                            source: ResolutionSource::OpenNamespace(namespace.clone()),
                        },
                    });
                }
            }
            ResolutionResult::Ambiguous(ref cs) => {
                let mut names: Vec<Name> = cs.iter().map(|c| c.name.clone()).collect();
                names.push(full.clone());
                ambiguity_map.insert(short.clone(), names);
            }
        }
    }
    ImportImpact {
        namespace: namespace.clone(),
        new_names,
        new_ambiguities: ambiguity_map.into_iter().collect(),
        new_shadows,
    }
}

// ---- Resolution explanation -----------------------------------------------

/// A human-readable explanation of why a name resolved (or didn't).
#[derive(Debug, Clone)]
pub(crate) struct ResolutionExplanation {
    pub(crate) input: String,
    pub(crate) result: ResolutionResult,
    pub(crate) steps: Vec<String>,
}

impl fmt::Display for ResolutionExplanation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Resolution of `{}`:", self.input)?;
        for (i, step) in self.steps.iter().enumerate() {
            writeln!(f, "  {}. {step}", i + 1)?;
        }
        match &self.result {
            ResolutionResult::Resolved(c) => write!(
                f,
                "  => resolved to `{}` via {}",
                c.name,
                format_source(&c.source)
            ),
            ResolutionResult::Ambiguous(cs) => {
                let ns: Vec<String> = cs.iter().map(|c| c.name.to_string()).collect();
                write!(f, "  => AMBIGUOUS: {}", ns.join(", "))
            }
            ResolutionResult::Unresolved => write!(f, "  => UNRESOLVED"),
        }
    }
}

/// Generate a step-by-step explanation of name resolution.
#[must_use]
pub(crate) fn explain_resolution(
    name: &Name,
    resolver: &mut NameResolutionExt,
    ns_state: &NamespaceState,
    env: &Environment,
) -> ResolutionExplanation {
    let name_str = name.to_string();
    let mut steps = Vec::new();
    if name.is_anon() {
        steps.push("input is anonymous name, cannot resolve".to_string());
        return ResolutionExplanation {
            input: name_str,
            result: ResolutionResult::Unresolved,
            steps,
        };
    }
    steps.push(format!("looking up `{name_str}`"));
    let cur_ns = ns_state.current_namespace();
    if !cur_ns.is_anon() {
        let q = format!("{cur_ns}.{name_str}");
        if env.get_const(&Name::from_string(&q)).is_some() {
            steps.push(format!("found `{q}` in current namespace `{cur_ns}`"));
        } else {
            steps.push(format!("not found under current namespace `{cur_ns}`"));
        }
    } else {
        steps.push("no active namespace".to_string());
    }
    let opens = ns_state.open_namespaces();
    if opens.is_empty() {
        steps.push("no open namespaces".to_string());
    } else {
        for open_ns in opens {
            let q = format!("{open_ns}.{name_str}");
            if env.get_const(&Name::from_string(&q)).is_some() {
                steps.push(format!("found `{q}` via open namespace `{open_ns}`"));
            }
        }
    }
    if env.get_const(name).is_some() {
        steps.push(format!("`{name_str}` exists as a global constant"));
    }
    let result = resolver.resolve(name, ns_state, env);
    match &result {
        ResolutionResult::Resolved(c) => {
            steps.push(format!(
                "resolved to `{}` via {}",
                c.name,
                format_source(&c.source)
            ));
        }
        ResolutionResult::Ambiguous(cs) => {
            let ns: Vec<String> = cs.iter().map(|c| format!("`{}`", c.name)).collect();
            steps.push(format!("ambiguous between {}", ns.join(", ")));
        }
        ResolutionResult::Unresolved => {
            steps.push("no matching constant found in any scope".into())
        }
    }
    ResolutionExplanation {
        input: name_str,
        result,
        steps,
    }
}

// ---- Helpers --------------------------------------------------------------

/// Format a resolution source for human display.
#[must_use]
pub(crate) fn format_source(source: &ResolutionSource) -> String {
    match source {
        ResolutionSource::Local => "local binding".to_string(),
        ResolutionSource::OpenNamespace(ns) => format!("open namespace `{ns}`"),
        ResolutionSource::Alias(a) => format!("alias `{a}`"),
        ResolutionSource::Global => "global scope".to_string(),
        ResolutionSource::AutoOpen(ns) => format!("auto-open `{ns}`"),
    }
}
