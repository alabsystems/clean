// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Pass Manager — dependency-aware, phase-grouped pass pipeline.
//!
//! Adds dependency tracking, topological ordering, phase-based grouping,
//! per-pass enable/disable, fixed-point iteration, cycle detection,
//! profiling, diff hooks, and aggregate statistics on top of
//! [`crate::pass_manager`].
//!
//! Part of #3083 — Extensibility.

use crate::ir::IRDecl;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};
use thiserror::Error;

/// Errors from the extended pass manager.
#[derive(Debug, Error)]
#[non_exhaustive]
pub(crate) enum PassManagerExtError {
    #[error("pass `{pass}` depends on unregistered pass `{dependency}`")]
    MissingDependency { pass: String, dependency: String },
    #[error("dependency cycle detected: {cycle}")]
    CycleDetected { cycle: String },
    #[error("duplicate pass name: `{0}`")]
    DuplicatePass(String),
    #[error("pass `{pass}` failed: {reason}")]
    PassFailed { pass: String, reason: String },
    #[error("conflicting requirements between `{a}` and `{b}`: {detail}")]
    ConflictingRequirements {
        a: String,
        b: String,
        detail: String,
    },
}

/// Execution phases. Passes execute in order: Early -> Main -> Late -> Codegen.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ExtPhase {
    Early = 0,
    Main = 1,
    Late = 2,
    Codegen = 3,
}

impl ExtPhase {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Early => "early",
            Self::Main => "main",
            Self::Late => "late",
            Self::Codegen => "codegen",
        }
    }
}

impl std::fmt::Display for ExtPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Metadata attached to a registered pass.
#[derive(Debug, Clone)]
pub(crate) struct PassMeta {
    pub(crate) name: String,
    pub(crate) phase: ExtPhase,
    pub(crate) description: String,
    pub(crate) dependencies: Vec<String>,
    pub(crate) conflicts: Vec<String>,
    pub(crate) fixed_point: bool,
}

/// Callback type for IR-level passes.
pub(crate) type ExtPassFn = Box<dyn Fn(&[IRDecl]) -> Result<Vec<IRDecl>, String> + Send + Sync>;

/// A registered pass with its callback.
pub(crate) struct ExtPass {
    pub(crate) meta: PassMeta,
    pub(crate) run: ExtPassFn,
}

impl std::fmt::Debug for ExtPass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtPass")
            .field("meta", &self.meta)
            .finish_non_exhaustive()
    }
}

/// Configuration controlling which passes run and iteration behaviour.
#[derive(Debug, Clone)]
pub(crate) struct ExtPipelineConfig {
    pub(crate) disabled_passes: HashSet<String>,
    /// Maximum iterations for a fixed-point pass group (0 = single shot).
    pub(crate) max_iterations: u32,
    pub(crate) profiling: bool,
    pub(crate) diff_enabled: bool,
}

impl Default for ExtPipelineConfig {
    fn default() -> Self {
        Self {
            disabled_passes: HashSet::new(),
            max_iterations: 10,
            profiling: true,
            diff_enabled: false,
        }
    }
}

/// Per-pass execution statistics.
#[derive(Debug, Clone, Default)]
pub(crate) struct PassStats {
    pub(crate) runs: u32,
    pub(crate) skips: u32,
    pub(crate) total_time: Duration,
    pub(crate) last_decl_count_in: usize,
    pub(crate) last_decl_count_out: usize,
}

/// Aggregate pipeline statistics.
#[derive(Debug, Clone, Default)]
pub(crate) struct PipelineStats {
    pub(crate) per_pass: BTreeMap<String, PassStats>,
    pub(crate) total_iterations: u32,
    pub(crate) total_time: Duration,
}

/// Diff callback: `(pass_name, before, after)`.
pub(crate) type DiffCallback = Box<dyn Fn(&str, &[IRDecl], &[IRDecl]) + Send + Sync>;

/// Extended pass manager with dependency tracking and phase-based execution.
pub(crate) struct ExtPassManager {
    passes: Vec<ExtPass>,
    name_index: HashMap<String, usize>,
    config: ExtPipelineConfig,
    diff_callback: Option<DiffCallback>,
}

impl std::fmt::Debug for ExtPassManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtPassManager")
            .field("pass_count", &self.passes.len())
            .field("config", &self.config)
            .finish()
    }
}

impl ExtPassManager {
    pub(crate) fn new() -> Self {
        Self {
            passes: Vec::new(),
            name_index: HashMap::new(),
            config: ExtPipelineConfig::default(),
            diff_callback: None,
        }
    }

    pub(crate) fn with_config(config: ExtPipelineConfig) -> Self {
        Self {
            passes: Vec::new(),
            name_index: HashMap::new(),
            config,
            diff_callback: None,
        }
    }

    pub(crate) fn set_diff_callback(&mut self, cb: DiffCallback) {
        self.diff_callback = Some(cb);
    }

    /// Register a new pass. Returns error on duplicate name.
    pub(crate) fn register(&mut self, pass: ExtPass) -> Result<(), PassManagerExtError> {
        if self.name_index.contains_key(&pass.meta.name) {
            return Err(PassManagerExtError::DuplicatePass(pass.meta.name.clone()));
        }
        let idx = self.passes.len();
        self.name_index.insert(pass.meta.name.clone(), idx);
        self.passes.push(pass);
        Ok(())
    }

    pub(crate) fn pass_count(&self) -> usize {
        self.passes.len()
    }

    pub(crate) fn has_pass(&self, name: &str) -> bool {
        self.name_index.contains_key(name)
    }

    pub(crate) fn disable_pass(&mut self, name: &str) {
        self.config.disabled_passes.insert(name.to_owned());
    }

    pub(crate) fn enable_pass(&mut self, name: &str) {
        self.config.disabled_passes.remove(name);
    }

    pub(crate) fn is_pass_enabled(&self, name: &str) -> bool {
        self.name_index.contains_key(name) && !self.config.disabled_passes.contains(name)
    }

    pub(crate) fn passes_in_phase(&self, phase: ExtPhase) -> Vec<&PassMeta> {
        self.passes
            .iter()
            .filter(|p| p.meta.phase == phase)
            .map(|p| &p.meta)
            .collect()
    }

    /// Validate: check for missing deps, cycles, and conflicts.
    pub(crate) fn validate(&self) -> Result<(), PassManagerExtError> {
        for pass in &self.passes {
            for dep in &pass.meta.dependencies {
                if !self.name_index.contains_key(dep) {
                    return Err(PassManagerExtError::MissingDependency {
                        pass: pass.meta.name.clone(),
                        dependency: dep.clone(),
                    });
                }
            }
        }
        for pass in &self.passes {
            for conflict in &pass.meta.conflicts {
                if self.name_index.contains_key(conflict) {
                    return Err(PassManagerExtError::ConflictingRequirements {
                        a: pass.meta.name.clone(),
                        b: conflict.clone(),
                        detail: "conflicting passes registered simultaneously".into(),
                    });
                }
            }
        }
        self.topological_order()?;
        Ok(())
    }

    /// Topological ordering respecting phase order and declared dependencies.
    pub(crate) fn topological_order(&self) -> Result<Vec<String>, PassManagerExtError> {
        let mut in_degree: HashMap<&str, usize> = HashMap::new();
        let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
        for pass in &self.passes {
            in_degree.entry(pass.meta.name.as_str()).or_insert(0);
            adj.entry(pass.meta.name.as_str()).or_default();
        }
        // Phase ordering: every pass in phase N depends on all in phase N-1.
        let mut by_phase: BTreeMap<ExtPhase, Vec<&str>> = BTreeMap::new();
        for pass in &self.passes {
            by_phase
                .entry(pass.meta.phase)
                .or_default()
                .push(pass.meta.name.as_str());
        }
        let phases: Vec<ExtPhase> = by_phase.keys().copied().collect();
        for w in phases.windows(2) {
            if let (Some(prev), Some(next)) = (by_phase.get(&w[0]), by_phase.get(&w[1])) {
                for &n in next {
                    for &p in prev {
                        adj.entry(p).or_default().push(n);
                        *in_degree.entry(n).or_insert(0) += 1;
                    }
                }
            }
        }
        // Explicit dependency edges.
        for pass in &self.passes {
            for dep in &pass.meta.dependencies {
                adj.entry(dep.as_str())
                    .or_default()
                    .push(pass.meta.name.as_str());
                *in_degree.entry(pass.meta.name.as_str()).or_insert(0) += 1;
            }
        }
        // Kahn's algorithm with deterministic tie-breaking.
        let mut queue: VecDeque<&str> = VecDeque::new();
        let mut start: Vec<&str> = in_degree
            .iter()
            .filter(|(_, &d)| d == 0)
            .map(|(&n, _)| n)
            .collect();
        start.sort_unstable();
        queue.extend(start);

        let mut order: Vec<String> = Vec::with_capacity(self.passes.len());
        while let Some(node) = queue.pop_front() {
            order.push(node.to_owned());
            if let Some(neighbors) = adj.get(node) {
                let mut ready: Vec<&str> = Vec::new();
                for &nbr in neighbors {
                    let d = in_degree.get_mut(nbr).expect("in_degree entry");
                    *d -= 1;
                    if *d == 0 {
                        ready.push(nbr);
                    }
                }
                ready.sort_unstable();
                queue.extend(ready);
            }
        }
        if order.len() != self.passes.len() {
            let in_order: HashSet<&str> = order.iter().map(|s| s.as_str()).collect();
            let cycle: Vec<String> = self
                .passes
                .iter()
                .map(|p| p.meta.name.as_str())
                .filter(|n| !in_order.contains(n))
                .map(|s| s.to_owned())
                .collect();
            return Err(PassManagerExtError::CycleDetected {
                cycle: cycle.join(" -> "),
            });
        }
        Ok(order)
    }

    /// Run the full pipeline. Returns transformed IR and statistics.
    pub(crate) fn run(
        &self,
        decls: &[IRDecl],
    ) -> Result<(Vec<IRDecl>, PipelineStats), PassManagerExtError> {
        let t0 = Instant::now();
        let order = self.topological_order()?;
        let mut current = decls.to_vec();
        let mut stats = PipelineStats::default();

        // Group ordered passes by phase for iteration support.
        let mut groups: Vec<(ExtPhase, Vec<&str>)> = Vec::new();
        let mut cur_phase: Option<ExtPhase> = None;
        for name in &order {
            let phase = self.passes[self.name_index[name.as_str()]].meta.phase;
            match cur_phase {
                Some(p) if p == phase => groups.last_mut().expect("non-empty").1.push(name),
                _ => {
                    groups.push((phase, vec![name]));
                    cur_phase = Some(phase);
                }
            }
        }
        for (_, group) in &groups {
            current = self.run_phase_group(group, &current, &mut stats)?;
        }
        stats.total_time = t0.elapsed();
        Ok((current, stats))
    }

    fn run_phase_group(
        &self,
        group: &[&str],
        decls: &[IRDecl],
        stats: &mut PipelineStats,
    ) -> Result<Vec<IRDecl>, PassManagerExtError> {
        let should_iterate = group.iter().any(|name| {
            if self.config.disabled_passes.contains(*name) {
                return false;
            }
            let pass = &self.passes[self.name_index[*name]];
            pass.meta.fixed_point
        });
        let max = if self.config.max_iterations == 0 {
            1
        } else if should_iterate {
            self.config.max_iterations
        } else {
            1
        };
        let mut current = decls.to_vec();
        for _ in 0..max {
            stats.total_iterations += 1;
            let snap = Self::snapshot(&current);
            current = self.run_pass_list(group, &current, stats)?;
            if snap == Self::snapshot(&current) {
                break;
            }
        }
        Ok(current)
    }

    fn run_pass_list(
        &self,
        names: &[&str],
        decls: &[IRDecl],
        stats: &mut PipelineStats,
    ) -> Result<Vec<IRDecl>, PassManagerExtError> {
        let mut current = decls.to_vec();
        for &name in names {
            let ps = stats.per_pass.entry(name.to_owned()).or_default();
            if self.config.disabled_passes.contains(name) {
                ps.skips += 1;
                continue;
            }
            let pass = &self.passes[self.name_index[name]];
            let before = current.clone();
            let t = if self.config.profiling {
                Some(Instant::now())
            } else {
                None
            };
            let result =
                (pass.run)(&current).map_err(|reason| PassManagerExtError::PassFailed {
                    pass: name.to_owned(),
                    reason,
                })?;
            if let Some(t) = t {
                ps.total_time += t.elapsed();
            }
            ps.runs += 1;
            ps.last_decl_count_in = current.len();
            ps.last_decl_count_out = result.len();
            if self.config.diff_enabled {
                if let Some(cb) = &self.diff_callback {
                    cb(name, &before, &result);
                }
            }
            current = result;
        }
        Ok(current)
    }

    fn snapshot(decls: &[IRDecl]) -> Vec<String> {
        let mut v: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();
        v.sort_unstable();
        v
    }
}

impl ExtPass {
    pub(crate) fn new(
        name: impl Into<String>,
        phase: ExtPhase,
        description: impl Into<String>,
        run: impl Fn(&[IRDecl]) -> Result<Vec<IRDecl>, String> + Send + Sync + 'static,
    ) -> Self {
        Self {
            meta: PassMeta {
                name: name.into(),
                phase,
                description: description.into(),
                dependencies: Vec::new(),
                conflicts: Vec::new(),
                fixed_point: false,
            },
            run: Box::new(run),
        }
    }

    pub(crate) fn depends_on(mut self, dep: impl Into<String>) -> Self {
        self.meta.dependencies.push(dep.into());
        self
    }

    pub(crate) fn conflicts_with(mut self, other: impl Into<String>) -> Self {
        self.meta.conflicts.push(other.into());
        self
    }

    pub(crate) fn fixed_point(mut self) -> Self {
        self.meta.fixed_point = true;
        self
    }
}
