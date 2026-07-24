// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended attribute macro analysis: dependency tracking, conflict detection,
//! expansion analysis, statistics, scope classification, batch expansion,
//! and validation.

use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use clean_kernel::Name;
use clean_parser::Attribute;

use crate::attr_macro::{
    attr_name, expand_attributes, AttrMacroRegistry, AttrMacroResult, ExpansionResult,
};
use crate::error::ElabError;

// ============================================================================
// Error types
// ============================================================================

/// Errors specific to extended attribute macro analysis.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum AttrMacroExtError {
    #[error("conflicting attributes: '{a}' and '{b}' on declaration '{decl}'")]
    ConflictingAttributes { decl: String, a: String, b: String },
    #[error("circular macro dependency: {cycle}")]
    CircularDependency { cycle: String },
    #[error("macro '{macro_name}' depends on unregistered macro '{dependency}'")]
    MissingDependency {
        macro_name: String,
        dependency: String,
    },
    #[error("macro '{name}' has no handler registered")]
    MissingHandler { name: String },
    #[error("elaboration error: {0}")]
    ElabError(#[from] ElabError),
}

// ============================================================================
// Scope analysis
// ============================================================================

/// Visibility scope of an attribute macro.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum MacroScope {
    Local,
    Section,
    Module,
    Global,
}

/// Classify scope: built-in macros are Global, custom/unknown are Module.
#[must_use]
pub(crate) fn classify_scope(name: &str, registry: &AttrMacroRegistry) -> MacroScope {
    if registry.is_registered(name) {
        MacroScope::Global
    } else {
        MacroScope::Module
    }
}

// ============================================================================
// Dependency tracking
// ============================================================================

/// Tracks dependency relationships between attribute macros for
/// composition chains and topological ordering.
#[derive(Debug, Clone, Default)]
pub(crate) struct MacroDependencyGraph {
    pub(super) deps: HashMap<String, HashSet<String>>,
}

impl MacroDependencyGraph {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            deps: HashMap::new(),
        }
    }

    pub(crate) fn add_dependency(&mut self, macro_name: &str, dependency: &str) {
        self.deps
            .entry(macro_name.to_owned())
            .or_default()
            .insert(dependency.to_owned());
    }

    #[must_use]
    pub(crate) fn dependencies_of(&self, macro_name: &str) -> HashSet<String> {
        self.deps.get(macro_name).cloned().unwrap_or_default()
    }

    #[must_use]
    pub(crate) fn has_dependencies(&self, macro_name: &str) -> bool {
        self.deps.get(macro_name).is_some_and(|d| !d.is_empty())
    }

    #[must_use]
    pub(crate) fn macros_with_dependencies(&self) -> Vec<&str> {
        self.deps
            .iter()
            .filter(|(_, d)| !d.is_empty())
            .map(|(k, _)| k.as_str())
            .collect()
    }

    /// Topological sort of `macro_names` respecting dependency edges.
    /// Returns error on cycle.
    pub(crate) fn topological_order(
        &self,
        macro_names: &[&str],
    ) -> Result<Vec<String>, AttrMacroExtError> {
        let name_set: HashSet<&str> = macro_names.iter().copied().collect();
        let mut in_degree: HashMap<&str, usize> = HashMap::new();
        for &name in macro_names {
            in_degree.entry(name).or_insert(0);
            if let Some(deps) = self.deps.get(name) {
                for dep in deps {
                    if name_set.contains(dep.as_str()) {
                        *in_degree.entry(name).or_insert(0) += 1;
                    }
                }
            }
        }
        let mut queue: Vec<&str> = in_degree
            .iter()
            .filter(|(_, &deg)| deg == 0)
            .map(|(&n, _)| n)
            .collect();
        queue.sort();
        let mut result = Vec::new();
        while let Some(current) = queue.pop() {
            result.push(current.to_owned());
            for &name in macro_names {
                if let Some(deps) = self.deps.get(name) {
                    if deps.contains(current) {
                        if let Some(deg) = in_degree.get_mut(name) {
                            *deg = deg.saturating_sub(1);
                            if *deg == 0 {
                                queue.push(name);
                                queue.sort();
                            }
                        }
                    }
                }
            }
        }
        if result.len() != macro_names.len() {
            let remaining: Vec<&str> = macro_names
                .iter()
                .filter(|n| !result.iter().any(|r| r == **n))
                .copied()
                .collect();
            return Err(AttrMacroExtError::CircularDependency {
                cycle: remaining.join(" -> "),
            });
        }
        Ok(result)
    }

    /// Check all declared dependencies exist in the registry.
    pub(crate) fn validate_dependencies(
        &self,
        registry: &AttrMacroRegistry,
    ) -> Vec<AttrMacroExtError> {
        let mut errors = Vec::new();
        for (macro_name, deps) in &self.deps {
            for dep in deps {
                if !registry.is_registered(dep) {
                    errors.push(AttrMacroExtError::MissingDependency {
                        macro_name: macro_name.clone(),
                        dependency: dep.clone(),
                    });
                }
            }
        }
        errors
    }
}

// ============================================================================
// Conflict detection
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConflictRule {
    pub(crate) a: String,
    pub(crate) b: String,
}

/// Registry of known conflicting attribute pairs.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConflictRegistry {
    rules: Vec<ConflictRule>,
}

impl ConflictRegistry {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { rules: Vec::new() }
    }

    #[must_use]
    pub(crate) fn with_defaults() -> Self {
        let mut reg = Self::new();
        reg.add_conflict("inline", "noinline");
        reg.add_conflict("inline", "always_inline");
        reg.add_conflict("noinline", "always_inline");
        reg.add_conflict("inline", "macro_inline");
        reg.add_conflict("noinline", "macro_inline");
        reg.add_conflict("always_inline", "macro_inline");
        reg.add_conflict("specialize", "nospecialize");
        reg.add_conflict("reducible", "irreducible");
        reg.add_conflict("reducible", "semireducible");
        reg.add_conflict("semireducible", "irreducible");
        reg
    }

    pub(crate) fn add_conflict(&mut self, a: &str, b: &str) {
        self.rules.push(ConflictRule {
            a: a.to_owned(),
            b: b.to_owned(),
        });
    }

    pub(crate) fn detect_conflicts(&self, decl: &str, names: &[&str]) -> Vec<AttrMacroExtError> {
        let set: HashSet<&str> = names.iter().copied().collect();
        self.rules
            .iter()
            .filter_map(|r| {
                if set.contains(r.a.as_str()) && set.contains(r.b.as_str()) {
                    Some(AttrMacroExtError::ConflictingAttributes {
                        decl: decl.to_owned(),
                        a: r.a.clone(),
                        b: r.b.clone(),
                    })
                } else {
                    None
                }
            })
            .collect()
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.rules.len()
    }
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}

// ============================================================================
// Statistics collection
// ============================================================================

/// Per-macro expansion statistics.
#[derive(Debug, Clone, Default)]
pub(crate) struct MacroStats {
    pub(crate) success_count: u64,
    pub(crate) failure_count: u64,
    pub(crate) total_duration: Duration,
}

impl MacroStats {
    #[must_use]
    pub(crate) fn total_count(&self) -> u64 {
        self.success_count + self.failure_count
    }

    #[must_use]
    pub(crate) fn failure_rate(&self) -> f64 {
        let total = self.total_count();
        if total == 0 {
            0.0
        } else {
            self.failure_count as f64 / total as f64
        }
    }

    #[must_use]
    pub(crate) fn avg_duration(&self) -> Duration {
        if self.success_count == 0 {
            Duration::ZERO
        } else {
            self.total_duration / self.success_count as u32
        }
    }
}

/// Collects expansion statistics across all macros.
#[derive(Debug, Clone, Default)]
pub(crate) struct StatsCollector {
    stats: HashMap<String, MacroStats>,
}

impl StatsCollector {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            stats: HashMap::new(),
        }
    }

    pub(crate) fn record_success(&mut self, name: &str, duration: Duration) {
        let e = self.stats.entry(name.to_owned()).or_default();
        e.success_count += 1;
        e.total_duration += duration;
    }

    pub(crate) fn record_failure(&mut self, name: &str) {
        self.stats.entry(name.to_owned()).or_default().failure_count += 1;
    }

    #[must_use]
    pub(crate) fn get(&self, name: &str) -> Option<&MacroStats> {
        self.stats.get(name)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&str, &MacroStats)> {
        self.stats.iter().map(|(k, v)| (k.as_str(), v))
    }

    #[must_use]
    pub(crate) fn macro_count(&self) -> usize {
        self.stats.len()
    }
    #[must_use]
    pub(crate) fn total_successes(&self) -> u64 {
        self.stats.values().map(|s| s.success_count).sum()
    }
    #[must_use]
    pub(crate) fn total_failures(&self) -> u64 {
        self.stats.values().map(|s| s.failure_count).sum()
    }
}

// ============================================================================
// Expansion analysis
// ============================================================================

#[derive(Debug, Clone)]
pub(crate) struct ExpansionAnalysis {
    pub(crate) effect_count: usize,
    pub(crate) error_count: usize,
    pub(crate) unhandled_count: usize,
    pub(crate) effect_kinds: Vec<EffectKind>,
}

/// Coarse classification of an [`AttrMacroResult`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EffectKind {
    LemmaRegistration,
    CompilerHint,
    FfiBinding,
    MetadataAnnotation,
    Custom,
}

#[must_use]
pub(crate) fn classify_effect(result: &AttrMacroResult) -> EffectKind {
    match result {
        AttrMacroResult::RegisterSimpLemma { .. }
        | AttrMacroResult::RegisterExtLemma
        | AttrMacroResult::RegisterCongrLemma
        | AttrMacroResult::RegisterReflLemma
        | AttrMacroResult::RegisterSymmLemma
        | AttrMacroResult::RegisterCsimpLemma => EffectKind::LemmaRegistration,
        AttrMacroResult::SetReducibility(_)
        | AttrMacroResult::SetInline(_)
        | AttrMacroResult::SetSpecialize(_) => EffectKind::CompilerHint,
        AttrMacroResult::RegisterExtern { .. }
        | AttrMacroResult::RegisterExport { .. }
        | AttrMacroResult::RegisterImplementedBy { .. } => EffectKind::FfiBinding,
        AttrMacroResult::RegisterDeprecated { .. }
        | AttrMacroResult::RegisterCoercion
        | AttrMacroResult::RegisterMatchPattern
        | AttrMacroResult::RegisterClass
        | AttrMacroResult::RegisterInit
        | AttrMacroResult::RegisterInstance { .. }
        | AttrMacroResult::RegisterDefaultInstance => EffectKind::MetadataAnnotation,
        AttrMacroResult::Custom(_) => EffectKind::Custom,
    }
}

#[must_use]
pub(crate) fn analyze_expansion(result: &ExpansionResult) -> ExpansionAnalysis {
    ExpansionAnalysis {
        effect_count: result.effects.len(),
        error_count: result.errors.len(),
        unhandled_count: result.unhandled.len(),
        effect_kinds: result.effects.iter().map(classify_effect).collect(),
    }
}

// ============================================================================
// Batch expansion
// ============================================================================

#[derive(Debug, Clone)]
pub(crate) struct BatchExpansionResult {
    pub(crate) results: Vec<(String, ExpansionResult)>,
    pub(crate) conflict_errors: Vec<AttrMacroExtError>,
}

/// Expand attributes for multiple declarations with conflict detection
/// and statistics collection.
pub(crate) fn batch_expand(
    declarations: &[(Name, Vec<Attribute>)],
    registry: &AttrMacroRegistry,
    conflict_registry: &ConflictRegistry,
    stats: &mut StatsCollector,
) -> BatchExpansionResult {
    let mut results = Vec::new();
    let mut conflict_errors = Vec::new();
    for (decl_name, attrs) in declarations {
        let names: Vec<&str> = attrs.iter().map(attr_name).collect();
        conflict_errors.extend(conflict_registry.detect_conflicts(&decl_name.to_string(), &names));
        let start = Instant::now();
        let expansion = expand_attributes(decl_name, attrs, registry);
        let elapsed = start.elapsed();
        for name in &names {
            if registry.is_registered(name) {
                if expansion.errors.iter().any(|(n, _)| n == name) {
                    stats.record_failure(name);
                } else {
                    stats.record_success(name, elapsed / names.len().max(1) as u32);
                }
            }
        }
        results.push((decl_name.to_string(), expansion));
    }
    BatchExpansionResult {
        results,
        conflict_errors,
    }
}

// ============================================================================
// Validation
// ============================================================================

#[derive(Debug, Clone)]
pub(crate) struct ValidationResult {
    pub(crate) errors: Vec<AttrMacroExtError>,
    pub(crate) macros_checked: usize,
}

impl ValidationResult {
    #[must_use]
    pub(crate) fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Validate macro definitions: missing handlers, circular deps, unregistered deps.
pub(crate) fn validate_macros(
    registry: &AttrMacroRegistry,
    dep_graph: &MacroDependencyGraph,
) -> ValidationResult {
    let mut errors = Vec::new();
    errors.extend(dep_graph.validate_dependencies(registry));
    let macros_with_deps = dep_graph.macros_with_dependencies();
    if !macros_with_deps.is_empty() {
        if let Err(e) = dep_graph.topological_order(&macros_with_deps) {
            errors.push(e);
        }
    }
    for macro_name in dep_graph.deps.keys() {
        if !registry.is_registered(macro_name) {
            errors.push(AttrMacroExtError::MissingHandler {
                name: macro_name.clone(),
            });
        }
    }
    ValidationResult {
        errors,
        macros_checked: registry.len() + dep_graph.deps.len(),
    }
}
