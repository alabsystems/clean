// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended instance priority: overlap detection, coherence, depth tracking.
//!
//! Builds on [`crate::instance_priority`] / [`crate::instance_priority_ext`].
//! Reference: Lean 4 `src/Lean/Meta/SynthInstance.lean`

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use std::collections::HashMap;

/// Errors during extended instance resolution.
#[derive(Debug, Clone, thiserror::Error)]
pub(crate) enum InstanceResolutionError {
    #[error("ambiguous instances for `{class}` on `{type_name}`: {candidates:?}")]
    AmbiguousOverlap {
        class: Name,
        type_name: Name,
        candidates: Vec<Name>,
    },
    #[error("instance search depth {depth} exceeds limit {limit} for `{class}`")]
    DepthLimitExceeded { class: Name, depth: u32, limit: u32 },
    #[error("incoherent instances for `{class}` on `{type_name}`: {first} and {second}")]
    IncoherentInstances {
        class: Name,
        type_name: Name,
        first: Name,
        second: Name,
    },
    #[error("orphan instance `{instance}` for `{class}` on `{type_name}`")]
    OrphanInstance {
        instance: Name,
        class: Name,
        type_name: Name,
    },
}

/// Strategy for resolving overlapping instances.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum OverlapStrategy {
    /// Most specific type wins (highest argument count).
    MostSpecificWins,
    /// Highest explicit priority wins.
    #[default]
    ExplicitPriorityWins,
    /// Error on any ambiguity.
    ErrorOnAmbiguity,
}

/// A candidate instance with resolved priority and specificity metadata.
#[derive(Debug, Clone)]
pub(crate) struct InstanceCandidate {
    pub(crate) name: Name,
    pub(crate) class: Name,
    pub(crate) expr: Expr,
    pub(crate) type_: Expr,
    /// Effective numeric priority (higher = tried first).
    pub(crate) priority: u32,
    /// Number of type arguments (proxy for specificity).
    pub(crate) specificity: u32,
    pub(crate) is_local: bool,
    pub(crate) defining_module: Option<Name>,
}

/// Record of a detected overlap between two instances.
#[derive(Debug, Clone)]
pub(crate) struct OverlapInfo {
    pub(crate) first: Name,
    pub(crate) second: Name,
    pub(crate) class: Name,
    pub(crate) type_name: Name,
}

/// Statistics collected during instance resolution.
#[derive(Debug, Clone, Default)]
pub(crate) struct ResolutionStats {
    pub(crate) instances_considered: u64,
    pub(crate) overlaps_detected: u64,
    pub(crate) diamonds_resolved: u64,
    pub(crate) depth_limit_hits: u64,
    pub(crate) max_depth_observed: u32,
    pub(crate) local_instances_used: u64,
    pub(crate) coherence_violations: u64,
}

/// Tracks and limits instance search depth.
#[derive(Debug, Clone)]
pub(crate) struct DepthTracker {
    current: u32,
    limit: u32,
    max_observed: u32,
}

/// Default depth limit (matches Lean 4's default of 32).
pub(crate) const DEFAULT_DEPTH_LIMIT: u32 = 32;

impl DepthTracker {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            current: 0,
            limit: DEFAULT_DEPTH_LIMIT,
            max_observed: 0,
        }
    }

    #[must_use]
    pub(crate) fn with_limit(limit: u32) -> Self {
        Self {
            current: 0,
            limit,
            max_observed: 0,
        }
    }

    pub(crate) fn enter(&mut self, class: &Name) -> Result<(), InstanceResolutionError> {
        // Atomic: only commit the increment if it doesn't blow the
        // limit. Otherwise callers who pair `enter(...)` with a
        // matching `leave()` only on the OK path would corrupt the
        // depth counter on every depth-limit-exceeded path.
        let next = self.current.saturating_add(1);
        if next > self.limit {
            return Err(InstanceResolutionError::DepthLimitExceeded {
                class: class.clone(),
                depth: next,
                limit: self.limit,
            });
        }
        self.current = next;
        if self.current > self.max_observed {
            self.max_observed = self.current;
        }
        Ok(())
    }

    pub(crate) fn leave(&mut self) {
        self.current = self.current.saturating_sub(1);
    }

    #[must_use]
    pub(crate) fn current_depth(&self) -> u32 {
        self.current
    }

    #[must_use]
    pub(crate) fn limit(&self) -> u32 {
        self.limit
    }

    #[must_use]
    pub(crate) fn max_observed(&self) -> u32 {
        self.max_observed
    }

    pub(crate) fn reset(&mut self) {
        self.current = 0;
    }
}

impl Default for DepthTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Extended instance priority resolver with overlap detection, coherence
/// checking, and search depth tracking.
#[derive(Debug, Default)]
pub(crate) struct InstancePriorityExt2 {
    candidates: HashMap<Name, Vec<InstanceCandidate>>,
    local_instances: HashMap<Name, Vec<InstanceCandidate>>,
    overlaps: Vec<OverlapInfo>,
    stats: ResolutionStats,
    strategy: OverlapStrategy,
    depth: DepthTracker,
}

impl InstancePriorityExt2 {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn with_config(strategy: OverlapStrategy, depth_limit: u32) -> Self {
        Self {
            strategy,
            depth: DepthTracker::with_limit(depth_limit),
            ..Self::default()
        }
    }

    /// Register a global instance candidate.
    pub(crate) fn register(
        &mut self,
        name: Name,
        class: Name,
        expr: Expr,
        type_: Expr,
        priority: u32,
        specificity: u32,
        defining_module: Option<Name>,
    ) {
        let candidate = InstanceCandidate {
            name,
            class: class.clone(),
            expr,
            type_,
            priority,
            specificity,
            is_local: false,
            defining_module,
        };
        let entry = self.candidates.entry(class).or_default();
        let pos = entry.partition_point(|c| c.priority >= priority);
        entry.insert(pos, candidate);
    }

    /// Register a local instance (from `haveI` / `letI`).
    pub(crate) fn register_local(
        &mut self,
        name: Name,
        class: Name,
        expr: Expr,
        type_: Expr,
        priority: u32,
        specificity: u32,
    ) {
        let candidate = InstanceCandidate {
            name,
            class: class.clone(),
            expr,
            type_,
            priority,
            specificity,
            is_local: true,
            defining_module: None,
        };
        self.local_instances
            .entry(class)
            .or_default()
            .push(candidate);
    }

    /// Remove all local instances.
    pub(crate) fn clear_local_instances(&mut self) {
        self.local_instances.clear();
    }

    /// Default priority based on specificity: base 100, +10 per arg.
    ///
    /// Saturating-adds the `+100` base so pathological inputs (the
    /// `test_default_priority_no_overflow` regression tests pass
    /// `specificity = u32::MAX`) don't panic in debug builds.
    #[must_use]
    pub(crate) fn default_priority_for_specificity(specificity: u32) -> u32 {
        100u32.saturating_add(specificity.saturating_mul(10))
    }

    /// Candidates sorted by priority (highest first). Locals prepended.
    #[must_use]
    pub(crate) fn sorted_candidates(&self, class: &Name) -> Vec<&InstanceCandidate> {
        let mut result: Vec<&InstanceCandidate> = Vec::new();
        if let Some(locals) = self.local_instances.get(class) {
            let mut local_refs: Vec<&InstanceCandidate> = locals.iter().collect();
            local_refs.sort_by_key(|b| std::cmp::Reverse(b.priority));
            result.extend(local_refs);
        }
        if let Some(globals) = self.candidates.get(class) {
            result.extend(globals.iter());
        }
        result
    }

    /// Detect overlaps for a given class and type name.
    pub(crate) fn detect_overlaps(&mut self, class: &Name, type_name: &Name) -> Vec<OverlapInfo> {
        let mut matching: Vec<&InstanceCandidate> = Vec::new();
        if let Some(globals) = self.candidates.get(class) {
            matching.extend(
                globals
                    .iter()
                    .filter(|c| type_matches_name(&c.type_, type_name)),
            );
        }
        if let Some(locals) = self.local_instances.get(class) {
            matching.extend(
                locals
                    .iter()
                    .filter(|c| type_matches_name(&c.type_, type_name)),
            );
        }
        let mut overlaps = Vec::new();
        for i in 0..matching.len() {
            for j in (i + 1)..matching.len() {
                overlaps.push(OverlapInfo {
                    first: matching[i].name.clone(),
                    second: matching[j].name.clone(),
                    class: class.clone(),
                    type_name: type_name.clone(),
                });
            }
        }
        self.stats.overlaps_detected += overlaps.len() as u64;
        self.overlaps.extend(overlaps.clone());
        overlaps
    }

    /// Resolve an overlap according to the configured strategy.
    pub(crate) fn resolve_overlap(
        &self,
        class: &Name,
        type_name: &Name,
        candidates: &[&InstanceCandidate],
    ) -> Result<Name, InstanceResolutionError> {
        if candidates.is_empty() {
            return Err(InstanceResolutionError::AmbiguousOverlap {
                class: class.clone(),
                type_name: type_name.clone(),
                candidates: Vec::new(),
            });
        }
        if candidates.len() == 1 {
            return Ok(candidates[0].name.clone());
        }
        match self.strategy {
            OverlapStrategy::MostSpecificWins => {
                let best = candidates
                    .iter()
                    .max_by_key(|c| c.specificity)
                    .expect("candidates is non-empty");
                let ties: Vec<_> = candidates
                    .iter()
                    .filter(|c| c.specificity == best.specificity)
                    .collect();
                if ties.len() > 1 {
                    return Err(InstanceResolutionError::AmbiguousOverlap {
                        class: class.clone(),
                        type_name: type_name.clone(),
                        candidates: ties.iter().map(|c| c.name.clone()).collect(),
                    });
                }
                Ok(best.name.clone())
            }
            OverlapStrategy::ExplicitPriorityWins => {
                let best = candidates
                    .iter()
                    .max_by_key(|c| c.priority)
                    .expect("candidates is non-empty");
                let ties: Vec<_> = candidates
                    .iter()
                    .filter(|c| c.priority == best.priority)
                    .collect();
                if ties.len() > 1 {
                    return Err(InstanceResolutionError::AmbiguousOverlap {
                        class: class.clone(),
                        type_name: type_name.clone(),
                        candidates: ties.iter().map(|c| c.name.clone()).collect(),
                    });
                }
                Ok(best.name.clone())
            }
            OverlapStrategy::ErrorOnAmbiguity => Err(InstanceResolutionError::AmbiguousOverlap {
                class: class.clone(),
                type_name: type_name.clone(),
                candidates: candidates.iter().map(|c| c.name.clone()).collect(),
            }),
        }
    }

    /// Check orphan rule: class or type must be local to current_module.
    pub(crate) fn check_orphan(
        &self,
        instance: &Name,
        class: &Name,
        type_name: &Name,
        current_module: &Name,
    ) -> Result<(), InstanceResolutionError> {
        if is_name_local(class, current_module) || is_name_local(type_name, current_module) {
            return Ok(());
        }
        Err(InstanceResolutionError::OrphanInstance {
            instance: instance.clone(),
            class: class.clone(),
            type_name: type_name.clone(),
        })
    }

    /// Check coherence: no two instances for the same class and concrete type.
    pub(crate) fn check_coherence(
        &mut self,
        class: &Name,
        type_name: &Name,
    ) -> Result<(), InstanceResolutionError> {
        let mut matching: Vec<Name> = Vec::new();
        if let Some(globals) = self.candidates.get(class) {
            for c in globals {
                if type_matches_name(&c.type_, type_name) {
                    matching.push(c.name.clone());
                }
            }
        }
        if let Some(locals) = self.local_instances.get(class) {
            for c in locals {
                if type_matches_name(&c.type_, type_name) {
                    matching.push(c.name.clone());
                }
            }
        }
        if matching.len() > 1 {
            self.stats.coherence_violations += 1;
            return Err(InstanceResolutionError::IncoherentInstances {
                class: class.clone(),
                type_name: type_name.clone(),
                first: matching[0].clone(),
                second: matching[1].clone(),
            });
        }
        Ok(())
    }

    pub(crate) fn record_diamond_resolved(&mut self) {
        self.stats.diamonds_resolved += 1;
    }

    pub(crate) fn enter_depth(&mut self, class: &Name) -> Result<(), InstanceResolutionError> {
        let result = self.depth.enter(class);
        if result.is_err() {
            self.stats.depth_limit_hits += 1;
        }
        result
    }

    pub(crate) fn leave_depth(&mut self) {
        self.depth.leave();
    }
    pub(crate) fn reset_depth(&mut self) {
        self.depth.reset();
    }

    #[must_use]
    pub(crate) fn stats(&self) -> &ResolutionStats {
        &self.stats
    }

    pub(crate) fn finalize_stats(&mut self) {
        self.stats.max_depth_observed = self.depth.max_observed();
    }

    #[must_use]
    pub(crate) fn strategy(&self) -> OverlapStrategy {
        self.strategy
    }
    #[must_use]
    pub(crate) fn detected_overlaps(&self) -> &[OverlapInfo] {
        &self.overlaps
    }
    #[must_use]
    pub(crate) fn total_candidates(&self) -> usize {
        self.candidates.values().map(Vec::len).sum()
    }
    #[must_use]
    pub(crate) fn total_local_candidates(&self) -> usize {
        self.local_instances.values().map(Vec::len).sum()
    }
    #[must_use]
    pub(crate) fn depth_tracker(&self) -> &DepthTracker {
        &self.depth
    }
}

// Helpers

#[must_use]
fn is_name_local(name: &Name, module: &Name) -> bool {
    // An anonymous module is "current module" by convention — orphan
    // rule is trivially satisfied because there's no foreign module to
    // be foreign to. (Previously this branch compared the rendered
    // string `"[anonymous]"`, which never matched and broke the test.)
    if module.is_anon() {
        return true;
    }
    let name_str = name.to_string();
    let module_str = module.to_string();
    name_str == module_str || name_str.starts_with(&format!("{module_str}."))
}

/// Check whether `type_expr` is an instance signature whose target
/// type is named `type_name`.
///
/// Instance signatures are typically `App(App(...App(Class, T₁), T₂),
/// Tₙ)` — the class is the leftmost head, the type the instance
/// resolves against is the **first argument** to the class (T₁).
/// Walking down the App spine to the leftmost `Const` returns the
/// class name, which is wrong for coherence/overlap checks. Walk to
/// the App whose head is a `Const` (i.e. the outermost class App),
/// then check its argument.
#[must_use]
fn type_matches_name(type_expr: &Expr, type_name: &Name) -> bool {
    use clean_kernel::expr::ExprKind;
    // Strip outer Apps that are themselves `App(class_head, arg)`
    // until we find the first App whose head is a `Const`.
    let mut current = type_expr;
    loop {
        match current.kind() {
            ExprKind::App(func, arg) => match func.kind() {
                ExprKind::Const(_, _) => {
                    return matches!(
                        arg.kind(),
                        ExprKind::Const(n, _) if *n == *type_name
                    );
                }
                _ => current = func.as_ref(),
            },
            ExprKind::Const(n, _) => return *n == *type_name,
            _ => return false,
        }
    }
}
