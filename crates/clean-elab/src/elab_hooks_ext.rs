// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended elaboration hook management: chaining, phase filtering,
//! statistics, conditional hooks, groups, diagnostics, and validation.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::elab_hooks::{
    ElabHookContext, ElabHookEntry, ElabHookFn, ElabHookRegistry, ElabHookResult, ElabPhase,
};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from extended hook operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum HookExtError {
    #[error("duplicate hook name: {0}")]
    DuplicateName(String),
    #[error("duplicate priority {priority} in phase {phase} (hooks: {first}, {second})")]
    DuplicatePriority {
        phase: ElabPhase,
        priority: u32,
        first: String,
        second: String,
    },
    #[error("hook not found: {0}")]
    HookNotFound(String),
    #[error("empty hook chain")]
    EmptyChain,
}

// ---------------------------------------------------------------------------
// PhaseFilter
// ---------------------------------------------------------------------------

/// Set-based filter selecting a subset of [`ElabPhase`] variants.
#[derive(Debug, Clone)]
pub(crate) struct PhaseFilter {
    phases: HashSet<ElabPhase>,
}

impl PhaseFilter {
    #[must_use]
    pub(crate) fn new(phases: &[ElabPhase]) -> Self {
        Self {
            phases: phases.iter().copied().collect(),
        }
    }

    #[must_use]
    pub(crate) fn all() -> Self {
        Self::new(ElabPhase::ALL)
    }

    #[must_use]
    pub(crate) fn none() -> Self {
        Self {
            phases: HashSet::new(),
        }
    }

    #[must_use]
    pub(crate) fn matches(&self, phase: &ElabPhase) -> bool {
        self.phases.contains(phase)
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.phases.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.phases.is_empty()
    }
}

// ---------------------------------------------------------------------------
// HookCondition
// ---------------------------------------------------------------------------

/// Condition that must be satisfied before a conditional hook fires.
#[derive(Clone)]
pub(crate) enum HookCondition {
    NameContains(String),
    PhaseIs(ElabPhase),
    HasExpr,
    HasExpectedType,
    Custom(Arc<dyn Fn(&ElabHookContext) -> bool + Send + Sync>),
}

impl std::fmt::Debug for HookCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NameContains(s) => write!(f, "NameContains({s:?})"),
            Self::PhaseIs(p) => write!(f, "PhaseIs({p:?})"),
            Self::HasExpr => write!(f, "HasExpr"),
            Self::HasExpectedType => write!(f, "HasExpectedType"),
            Self::Custom(_) => write!(f, "Custom(<fn>)"),
        }
    }
}

impl HookCondition {
    #[must_use]
    pub(crate) fn evaluate(&self, ctx: &ElabHookContext) -> bool {
        match self {
            Self::NameContains(pat) => ctx
                .decl_name
                .as_deref()
                .is_some_and(|n| n.contains(pat.as_str())),
            Self::PhaseIs(phase) => ctx.phase == *phase,
            Self::HasExpr => ctx.expr.is_some(),
            Self::HasExpectedType => ctx.expected_type.is_some(),
            Self::Custom(pred) => pred(ctx),
        }
    }
}

// ---------------------------------------------------------------------------
// ConditionalHook
// ---------------------------------------------------------------------------

/// Hook wrapped with a condition; returns Continue when the condition is unmet.
#[derive(Clone)]
pub(crate) struct ConditionalHook {
    pub(crate) condition: HookCondition,
    pub(crate) inner: ElabHookFn,
}

impl std::fmt::Debug for ConditionalHook {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConditionalHook")
            .field("condition", &self.condition)
            .field("inner", &"<fn>")
            .finish()
    }
}

impl ConditionalHook {
    #[must_use]
    pub(crate) fn new(condition: HookCondition, inner: ElabHookFn) -> Self {
        Self { condition, inner }
    }

    #[must_use]
    pub(crate) fn into_hook_fn(self) -> ElabHookFn {
        Arc::new(move |ctx: &ElabHookContext| {
            if self.condition.evaluate(ctx) {
                (self.inner)(ctx)
            } else {
                ElabHookResult::Continue
            }
        })
    }
}

// ---------------------------------------------------------------------------
// HookStats / HookStatsCollector
// ---------------------------------------------------------------------------

/// Per-hook invocation statistics.
#[derive(Debug, Clone, Default)]
pub(crate) struct HookStats {
    pub(crate) invocations: u64,
    pub(crate) successes: u64,
    pub(crate) failures: u64,
    pub(crate) skips: u64,
    pub(crate) total_duration: Duration,
}

impl HookStats {
    #[must_use]
    pub(crate) fn success_rate(&self) -> f64 {
        if self.invocations == 0 {
            0.0
        } else {
            self.successes as f64 / self.invocations as f64
        }
    }

    #[must_use]
    pub(crate) fn avg_duration(&self) -> Duration {
        if self.invocations == 0 {
            Duration::ZERO
        } else {
            self.total_duration / self.invocations as u32
        }
    }
}

/// Collects [`HookStats`] keyed by hook name.
#[derive(Debug, Clone, Default)]
pub(crate) struct HookStatsCollector {
    stats: HashMap<String, HookStats>,
}

impl HookStatsCollector {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn record(&mut self, hook_name: &str, result: &ElabHookResult, duration: Duration) {
        let entry = self.stats.entry(hook_name.to_owned()).or_default();
        entry.invocations += 1;
        entry.total_duration += duration;
        match result {
            ElabHookResult::Continue | ElabHookResult::Replace(_) => entry.successes += 1,
            ElabHookResult::Error(_) => entry.failures += 1,
            ElabHookResult::Skip => entry.skips += 1,
        }
    }

    #[must_use]
    pub(crate) fn get(&self, hook_name: &str) -> Option<&HookStats> {
        self.stats.get(hook_name)
    }

    #[must_use]
    pub(crate) fn hook_count(&self) -> usize {
        self.stats.len()
    }

    pub(crate) fn clear(&mut self) {
        self.stats.clear();
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&str, &HookStats)> {
        self.stats.iter().map(|(k, v)| (k.as_str(), v))
    }
}

// ---------------------------------------------------------------------------
// HookChain
// ---------------------------------------------------------------------------

/// Ordered chain of hook entries with optional stats collection on execution.
#[derive(Debug, Clone, Default)]
pub(crate) struct HookChain {
    entries: Vec<ElabHookEntry>,
}

impl HookChain {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn push(&mut self, entry: ElabHookEntry) {
        let pos = self
            .entries
            .iter()
            .position(|e| e.priority > entry.priority)
            .unwrap_or(self.entries.len());
        self.entries.insert(pos, entry);
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub(crate) fn names(&self) -> Vec<&str> {
        self.entries.iter().map(|e| e.name.as_str()).collect()
    }

    /// Execute hooks in priority order. Returns error on empty chain.
    pub(crate) fn run(
        &self,
        ctx: &ElabHookContext,
        mut stats: Option<&mut HookStatsCollector>,
    ) -> Result<ElabHookResult, HookExtError> {
        if self.entries.is_empty() {
            return Err(HookExtError::EmptyChain);
        }
        for entry in &self.entries {
            let start = Instant::now();
            let result = (entry.hook)(ctx);
            let elapsed = start.elapsed();
            if let Some(ref mut collector) = stats {
                collector.record(&entry.name, &result, elapsed);
            }
            match &result {
                ElabHookResult::Continue => continue,
                ElabHookResult::Replace(_) | ElabHookResult::Error(_) => return Ok(result),
                ElabHookResult::Skip => return Ok(ElabHookResult::Continue),
            }
        }
        Ok(ElabHookResult::Continue)
    }
}

// ---------------------------------------------------------------------------
// HookGroup
// ---------------------------------------------------------------------------

/// Named group of hooks for batch enable/disable operations.
#[derive(Debug, Clone)]
pub(crate) struct HookGroup {
    pub(crate) name: String,
    pub(crate) hook_names: Vec<String>,
    pub(crate) enabled: bool,
}

impl HookGroup {
    #[must_use]
    pub(crate) fn new(name: impl Into<String>, hook_names: Vec<String>) -> Self {
        Self {
            name: name.into(),
            hook_names,
            enabled: true,
        }
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.hook_names.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.hook_names.is_empty()
    }

    pub(crate) fn enable(&mut self, registry: &mut ElabHookRegistry, source: &[ElabHookEntry]) {
        self.enabled = true;
        for entry in source {
            if self.hook_names.contains(&entry.name) {
                registry.register(entry.clone());
            }
        }
    }

    pub(crate) fn disable(&mut self, registry: &mut ElabHookRegistry) {
        self.enabled = false;
        for name in &self.hook_names {
            registry.remove(name);
        }
    }
}

// ---------------------------------------------------------------------------
// DiagnosticHook / DiagnosticCollector
// ---------------------------------------------------------------------------

/// A diagnostic entry collected during elaboration (read-only observation).
#[derive(Debug, Clone)]
pub(crate) struct DiagnosticEntry {
    pub(crate) hook_name: String,
    pub(crate) phase: ElabPhase,
    pub(crate) message: String,
    pub(crate) decl_name: Option<String>,
}

/// Collects [`DiagnosticEntry`] values during hook execution.
#[derive(Debug, Clone, Default)]
pub(crate) struct DiagnosticCollector {
    entries: Vec<DiagnosticEntry>,
}

impl DiagnosticCollector {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn push(&mut self, entry: DiagnosticEntry) {
        self.entries.push(entry);
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub(crate) fn entries(&self) -> &[DiagnosticEntry] {
        &self.entries
    }

    #[must_use]
    pub(crate) fn entries_for_phase(&self, phase: &ElabPhase) -> Vec<&DiagnosticEntry> {
        self.entries.iter().filter(|e| e.phase == *phase).collect()
    }

    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }
}

/// Create an [`ElabHookFn`] that records a diagnostic and returns Continue.
#[must_use]
pub(crate) fn make_diagnostic_hook(
    hook_name: &str,
    message_fn: Arc<dyn Fn(&ElabHookContext) -> String + Send + Sync>,
    collector: Arc<std::sync::Mutex<DiagnosticCollector>>,
) -> ElabHookFn {
    let hook_name = hook_name.to_owned();
    Arc::new(move |ctx: &ElabHookContext| {
        let msg = message_fn(ctx);
        let entry = DiagnosticEntry {
            hook_name: hook_name.clone(),
            phase: ctx.phase,
            message: msg,
            decl_name: ctx.decl_name.clone(),
        };
        if let Ok(mut coll) = collector.lock() {
            coll.push(entry);
        }
        ElabHookResult::Continue
    })
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct ValidationFinding {
    pub(crate) kind: ValidationFindingKind,
    // Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
    // keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
    #[allow(dead_code)]
    pub(crate) message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValidationFindingKind {
    DuplicateName,
    DuplicatePriority,
    EmptyPhase,
}

/// Validate hook entries for common mistakes (duplicate names, priorities).
#[must_use]
pub(crate) fn validate_entries(entries: &[ElabHookEntry]) -> Vec<ValidationFinding> {
    let mut findings = Vec::new();
    let mut seen_names: HashSet<&str> = HashSet::new();
    for entry in entries {
        if !seen_names.insert(&entry.name) {
            findings.push(ValidationFinding {
                kind: ValidationFindingKind::DuplicateName,
                message: format!("duplicate hook name: {}", entry.name),
            });
        }
    }
    let mut phase_prios: HashMap<ElabPhase, HashMap<u32, &str>> = HashMap::new();
    for entry in entries {
        let prio_map = phase_prios.entry(entry.phase).or_default();
        if let Some(existing) = prio_map.get(&entry.priority) {
            findings.push(ValidationFinding {
                kind: ValidationFindingKind::DuplicatePriority,
                message: format!(
                    "duplicate priority {} in phase {} (hooks: {}, {})",
                    entry.priority, entry.phase, existing, entry.name
                ),
            });
        } else {
            prio_map.insert(entry.priority, &entry.name);
        }
    }
    let covered: HashSet<ElabPhase> = entries.iter().map(|e| e.phase).collect();
    for phase in ElabPhase::ALL {
        if !covered.contains(phase) {
            findings.push(ValidationFinding {
                kind: ValidationFindingKind::EmptyPhase,
                message: format!("no hooks registered for phase {phase}"),
            });
        }
    }
    findings
}

/// Register entries into a registry, returning error on first duplicate name.
pub(crate) fn register_validated(
    registry: &mut ElabHookRegistry,
    entries: Vec<ElabHookEntry>,
) -> Result<(), HookExtError> {
    let mut seen: HashSet<String> = HashSet::new();
    for entry in entries {
        if !seen.insert(entry.name.clone()) {
            return Err(HookExtError::DuplicateName(entry.name));
        }
        registry.register(entry);
    }
    Ok(())
}

/// Run hooks for a phase using the registry and collect statistics.
pub(crate) fn run_hooks_with_stats(
    registry: &ElabHookRegistry,
    phase: ElabPhase,
    ctx: &ElabHookContext,
    stats: &mut HookStatsCollector,
) -> ElabHookResult {
    let hooks = registry.hooks_for_phase(&phase);
    for entry in hooks {
        let start = Instant::now();
        let result = (entry.hook)(ctx);
        let elapsed = start.elapsed();
        stats.record(&entry.name, &result, elapsed);
        match &result {
            ElabHookResult::Continue => continue,
            ElabHookResult::Replace(_) | ElabHookResult::Error(_) => return result,
            ElabHookResult::Skip => return ElabHookResult::Continue,
        }
    }
    ElabHookResult::Continue
}
