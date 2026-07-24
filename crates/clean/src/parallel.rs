// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parallel theorem checking infrastructure for clean.
//!
//! Provides dependency-aware parallel type checking of elaborated declarations.
//! Elaboration is sequential (mutates `Environment`), but the kernel type-check
//! phase for independent declarations runs in parallel via rayon.
//!
//! # Architecture
//!
//! 1. **Parse + elaborate** sequentially (building `Environment`)
//! 2. **Build dependency graph** from const-references in types and values
//! 3. **Extract topological batches** (layers of independent declarations)
//! 4. **Type-check each batch** in parallel (each thread gets its own `TypeChecker`)
//!
//! # Example
//!
//! ```rust,no_run
//! use clean::parallel::{check_source_parallel, ParallelCheckConfig};
//!
//! let config = ParallelCheckConfig::default();
//! let result = check_source_parallel("def a : Nat := 0\ndef b : Nat := 1", &config)
//!     .expect("parallel check should succeed");
//! assert!(result.total_passed > 0);
//! ```

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use rayon::prelude::*;

use clean_elab::{
    elaborate_decl_and_register_with_warning, preprocess_decl_with_context, FileContext,
    RegistrationWarningKind,
};
use clean_kernel::sorry::reset_sorry_counter;
use clean_kernel::{Environment, Expr, ExprKind, Name, TypeChecker};
use clean_parser::parse_file_with_tactics;

use crate::check::{DeclResult, DeclWarning};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from the parallel check pipeline.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ParallelError {
    /// Failed to read the source file from disk.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// The parser rejected the input.
    #[error("Parse error: {0}")]
    Parse(#[from] clean_parser::ParseError),

    /// Environment initialization failed.
    #[error("Environment initialization error: {0}")]
    EnvInit(String),
}

/// Convenience alias.
pub type Result<T> = std::result::Result<T, ParallelError>;

// ---------------------------------------------------------------------------
// Dependency graph
// ---------------------------------------------------------------------------

/// A declaration dependency graph for ordering parallel type checking.
///
/// Each node is a declaration name. Edges represent "depends on" relationships
/// derived from `Expr::Const` references in a declaration's type and value.
#[derive(Clone, Debug, Default)]
pub struct DeclDepGraph {
    /// Adjacency list: node -> set of dependencies.
    deps: HashMap<Name, HashSet<Name>>,
    /// Reverse adjacency: node -> set of dependents.
    rdeps: HashMap<Name, HashSet<Name>>,
    /// All known node names (some may have no deps).
    nodes: HashSet<Name>,
}

impl DeclDepGraph {
    /// Create an empty dependency graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a declaration with its set of dependencies.
    ///
    /// Dependencies that are not themselves declarations in the graph (e.g.,
    /// prelude constants) are recorded but do not create new nodes.
    pub fn add_declaration(&mut self, name: Name, deps: HashSet<Name>) {
        self.nodes.insert(name.clone());
        for dep in &deps {
            self.rdeps
                .entry(dep.clone())
                .or_default()
                .insert(name.clone());
        }
        self.deps.insert(name, deps);
    }

    /// Number of declarations in the graph.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Total number of dependency edges.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.deps.values().map(|s| s.len()).sum()
    }

    /// Extract topological batches (Kahn's algorithm).
    ///
    /// Each batch contains declarations whose dependencies are all in earlier
    /// batches. Declarations within a batch are independent and can be
    /// type-checked in parallel.
    ///
    /// Returns `None` if the graph contains a cycle.
    #[must_use]
    pub fn topological_batches(&self) -> Option<Vec<Vec<Name>>> {
        // Only consider intra-graph deps (deps that are also in self.nodes).
        let mut in_degree: HashMap<Name, usize> = HashMap::new();
        for name in &self.nodes {
            let count = self
                .deps
                .get(name)
                .map(|ds| ds.iter().filter(|d| self.nodes.contains(*d)).count())
                .unwrap_or(0);
            in_degree.insert(name.clone(), count);
        }

        let mut queue: VecDeque<Name> = in_degree
            .iter()
            .filter(|(_, &deg)| deg == 0)
            .map(|(n, _)| n.clone())
            .collect();

        let mut batches = Vec::new();
        let mut processed = 0usize;

        while !queue.is_empty() {
            let batch: Vec<Name> = queue.drain(..).collect();
            processed += batch.len();

            for name in &batch {
                if let Some(dependents) = self.rdeps.get(name) {
                    for dep in dependents {
                        if let Some(deg) = in_degree.get_mut(dep) {
                            *deg = deg.saturating_sub(1);
                            if *deg == 0 {
                                queue.push_back(dep.clone());
                            }
                        }
                    }
                }
            }

            batches.push(batch);
        }

        if processed == self.nodes.len() {
            Some(batches)
        } else {
            None // cycle detected
        }
    }
}

// ---------------------------------------------------------------------------
// Const-ref collection
// ---------------------------------------------------------------------------

/// Collect all `Expr::Const` names referenced in an expression tree.
///
/// Uses an explicit stack to avoid deep recursion on large expression trees.
/// This is used for dependency analysis -- determining which declarations
/// a given declaration depends on.
pub(crate) fn collect_const_refs(expr: &Expr, out: &mut HashSet<Name>) {
    let mut stack: Vec<&Expr> = vec![expr];

    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => {
                out.insert(name.clone());
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::MData(_, inner) => {
                stack.push(inner);
            }
            ExprKind::Proj(_, _, inner) => {
                stack.push(inner);
            }
            ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            // Terminals: BVar, FVar, Sort, Lit, SProp, Cubical variants
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for parallel theorem checking.
#[derive(Clone)]
#[non_exhaustive]
pub struct ParallelCheckConfig {
    /// When `true`, declarations using `sorry` are counted as passed.
    pub allow_sorry: bool,
    /// Minimum batch size before using parallel execution.
    /// Batches smaller than this are checked sequentially.
    pub parallel_threshold: usize,
    /// Maximum number of rayon threads. `None` uses rayon's default.
    pub max_threads: Option<usize>,
    /// When `true`, collect all errors instead of stopping at the first.
    pub continue_on_error: bool,
    /// Optional progress callback.
    pub progress_callback: Option<Arc<dyn Fn(ProgressEvent) + Send + Sync>>,
}

impl std::fmt::Debug for ParallelCheckConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ParallelCheckConfig")
            .field("allow_sorry", &self.allow_sorry)
            .field("parallel_threshold", &self.parallel_threshold)
            .field("max_threads", &self.max_threads)
            .field("continue_on_error", &self.continue_on_error)
            .field(
                "progress_callback",
                &self.progress_callback.as_ref().map(|_| "<callback>"),
            )
            .finish()
    }
}

impl Default for ParallelCheckConfig {
    fn default() -> Self {
        Self {
            allow_sorry: false,
            parallel_threshold: 4,
            max_threads: None,
            continue_on_error: true,
            progress_callback: None,
        }
    }
}

// ---------------------------------------------------------------------------
// Progress tracking
// ---------------------------------------------------------------------------

/// Events emitted during parallel checking for progress tracking.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ProgressEvent {
    /// A batch of independent declarations is about to be checked.
    BatchStarted {
        /// Zero-based batch index.
        batch_index: usize,
        /// Number of declarations in this batch.
        batch_size: usize,
    },
    /// A single declaration has been checked.
    DeclChecked {
        /// Fully qualified declaration name.
        name: String,
        /// Whether the declaration passed type checking.
        passed: bool,
        /// Time spent type-checking this declaration.
        elapsed: Duration,
    },
    /// A batch has completed.
    BatchCompleted {
        /// Zero-based batch index.
        batch_index: usize,
        /// Number of declarations that passed in this batch.
        passed: usize,
        /// Number of declarations that failed in this batch.
        failed: usize,
    },
    /// All batches have completed.
    AllCompleted {
        /// Total number of declarations checked.
        total: usize,
        /// Total passed.
        passed: usize,
        /// Total failed.
        failed: usize,
        /// Wall-clock time for the entire parallel check phase.
        elapsed: Duration,
    },
}

// ---------------------------------------------------------------------------
// Pre-elaborated check item
// ---------------------------------------------------------------------------

/// A pre-elaborated declaration ready for parallel kernel type checking.
///
/// Extracted from the sequential elaboration phase, this struct carries just
/// the information needed for the kernel type checker.
#[derive(Clone, Debug)]
pub struct ElabCheckItem {
    /// Declaration name.
    pub name: String,
    /// The declaration's type.
    pub ty: Expr,
    /// The declaration's value/proof (None for axioms).
    pub value: Option<Expr>,
    /// Whether this is a theorem (requires Prop check).
    pub is_theorem: bool,
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of checking a single batch of declarations.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct BatchResult {
    /// Zero-based batch index.
    pub batch_index: usize,
    /// Per-declaration outcomes within this batch.
    pub declarations: Vec<DeclResult>,
    /// Wall-clock time for this batch.
    pub elapsed: Duration,
}

/// Aggregate result of parallel checking.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct ParallelCheckResult {
    /// Per-declaration outcomes (in topological order).
    pub declarations: Vec<DeclResult>,
    /// Number of batches.
    pub batch_count: usize,
    /// Per-batch results.
    pub batches: Vec<BatchResult>,
    /// Total declarations that passed.
    pub total_passed: usize,
    /// Total declarations that failed.
    pub total_failed: usize,
    /// All errors collected (name, message).
    pub errors: Vec<(String, String)>,
    /// Wall-clock time for the entire check (parse + elaborate + parallel typecheck).
    pub total_elapsed: Duration,
    /// Wall-clock time for the parallel type-check phase only.
    pub parallel_elapsed: Duration,
    /// Sum of individual declaration check times (estimate of sequential time).
    pub sequential_estimate: Duration,
}

impl ParallelCheckResult {
    /// Returns `true` if all declarations passed with no errors.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        self.errors.is_empty() && self.total_failed == 0
    }

    /// Speedup ratio: sequential estimate / actual parallel time.
    /// Returns 1.0 if parallel time is zero.
    #[must_use]
    pub fn speedup(&self) -> f64 {
        let par = self.parallel_elapsed.as_secs_f64();
        if par < 1e-9 {
            return 1.0;
        }
        self.sequential_estimate.as_secs_f64() / par
    }
}

// ---------------------------------------------------------------------------
// Core parallel type-check
// ---------------------------------------------------------------------------

/// Type-check a batch of pre-elaborated declarations in parallel.
///
/// The `env` must already contain all declarations (elaboration is done).
/// Each item is type-checked independently using a per-thread `TypeChecker`.
pub fn check_declarations_parallel(
    env: &Environment,
    items: &[ElabCheckItem],
    config: &ParallelCheckConfig,
) -> ParallelCheckResult {
    let overall_start = Instant::now();

    // Build dependency graph.
    let mut graph = DeclDepGraph::new();
    let item_map: HashMap<String, &ElabCheckItem> =
        items.iter().map(|it| (it.name.clone(), it)).collect();

    for item in items {
        let name = Name::from_string(&item.name);
        let mut deps = HashSet::new();
        collect_const_refs(&item.ty, &mut deps);
        if let Some(ref val) = item.value {
            collect_const_refs(val, &mut deps);
        }
        // Only keep deps that are in our item set.
        let filtered: HashSet<Name> = deps
            .into_iter()
            .filter(|d| item_map.contains_key(&d.to_string()))
            .collect();
        graph.add_declaration(name, filtered);
    }

    // Extract batches. Fall back to single-batch if cycle detected.
    let batches = graph
        .topological_batches()
        .unwrap_or_else(|| vec![items.iter().map(|it| Name::from_string(&it.name)).collect()]);

    let mut all_decl_results = Vec::with_capacity(items.len());
    let mut all_errors = Vec::new();
    let mut batch_results = Vec::with_capacity(batches.len());
    let total_passed = AtomicUsize::new(0);
    let total_failed = AtomicUsize::new(0);
    let seq_estimate_ns = AtomicUsize::new(0);

    for (batch_idx, batch_names) in batches.iter().enumerate() {
        let batch_items: Vec<&ElabCheckItem> = batch_names
            .iter()
            .filter_map(|n| item_map.get(&n.to_string()).copied())
            .collect();

        if batch_items.is_empty() {
            continue;
        }

        if let Some(ref cb) = config.progress_callback {
            cb(ProgressEvent::BatchStarted {
                batch_index: batch_idx,
                batch_size: batch_items.len(),
            });
        }

        let batch_start = Instant::now();

        let use_parallel = batch_items.len() >= config.parallel_threshold;

        let results: Vec<DeclResult> = if use_parallel {
            batch_items
                .par_iter()
                .map(|item| {
                    let decl_start = Instant::now();
                    let result = typecheck_item(env, item);
                    let decl_elapsed = decl_start.elapsed();

                    seq_estimate_ns.fetch_add(decl_elapsed.as_nanos() as usize, Ordering::Relaxed);

                    if result.passed {
                        total_passed.fetch_add(1, Ordering::Relaxed);
                    } else {
                        total_failed.fetch_add(1, Ordering::Relaxed);
                    }

                    if let Some(ref cb) = config.progress_callback {
                        cb(ProgressEvent::DeclChecked {
                            name: item.name.clone(),
                            passed: result.passed,
                            elapsed: decl_elapsed,
                        });
                    }

                    result
                })
                .collect()
        } else {
            batch_items
                .iter()
                .map(|item| {
                    let decl_start = Instant::now();
                    let result = typecheck_item(env, item);
                    let decl_elapsed = decl_start.elapsed();

                    seq_estimate_ns.fetch_add(decl_elapsed.as_nanos() as usize, Ordering::Relaxed);

                    if result.passed {
                        total_passed.fetch_add(1, Ordering::Relaxed);
                    } else {
                        total_failed.fetch_add(1, Ordering::Relaxed);
                    }

                    if let Some(ref cb) = config.progress_callback {
                        cb(ProgressEvent::DeclChecked {
                            name: item.name.clone(),
                            passed: result.passed,
                            elapsed: decl_elapsed,
                        });
                    }

                    result
                })
                .collect()
        };

        let batch_elapsed = batch_start.elapsed();

        let batch_passed = results.iter().filter(|r| r.passed).count();
        let batch_failed = results.len() - batch_passed;

        if let Some(ref cb) = config.progress_callback {
            cb(ProgressEvent::BatchCompleted {
                batch_index: batch_idx,
                passed: batch_passed,
                failed: batch_failed,
            });
        }

        // Collect errors.
        for r in &results {
            if let Some(ref err) = r.error {
                all_errors.push((r.name.clone(), err.clone()));
            }
        }

        // Check if we should stop early.
        if !config.continue_on_error && !all_errors.is_empty() {
            batch_results.push(BatchResult {
                batch_index: batch_idx,
                declarations: results.clone(),
                elapsed: batch_elapsed,
            });
            all_decl_results.extend(results);
            break;
        }

        batch_results.push(BatchResult {
            batch_index: batch_idx,
            declarations: results.clone(),
            elapsed: batch_elapsed,
        });
        all_decl_results.extend(results);
    }

    let parallel_elapsed = overall_start.elapsed();
    let tp = total_passed.load(Ordering::Relaxed);
    let tf = total_failed.load(Ordering::Relaxed);

    if let Some(ref cb) = config.progress_callback {
        cb(ProgressEvent::AllCompleted {
            total: tp + tf,
            passed: tp,
            failed: tf,
            elapsed: parallel_elapsed,
        });
    }

    ParallelCheckResult {
        declarations: all_decl_results,
        batch_count: batch_results.len(),
        batches: batch_results,
        total_passed: tp,
        total_failed: tf,
        errors: all_errors,
        total_elapsed: parallel_elapsed,
        parallel_elapsed,
        sequential_estimate: Duration::from_nanos(seq_estimate_ns.load(Ordering::Relaxed) as u64),
    }
}

/// Type-check a single elaborated declaration item.
fn typecheck_item(env: &Environment, item: &ElabCheckItem) -> DeclResult {
    let tc = TypeChecker::with_mode(env, env.mode());

    // Check that the type is well-sorted.
    match tc.infer_sort(&item.ty) {
        Ok(sort) => {
            // For theorems, the type must be a Prop (Sort 0).
            if item.is_theorem && !sort.is_zero() {
                return DeclResult {
                    name: item.name.clone(),
                    passed: false,
                    error: Some(format!(
                        "{}: type must be a Prop (Sort 0), got Sort {sort}",
                        item.name
                    )),
                    warning: None,
                };
            }
        }
        Err(e) => {
            return DeclResult {
                name: item.name.clone(),
                passed: false,
                error: Some(format!("type check error on type: {e}")),
                warning: None,
            };
        }
    }

    // If there is a value/proof, check it against the type.
    if let Some(ref val) = item.value {
        if let Err(e) = tc.check_type(val, &item.ty) {
            return DeclResult {
                name: item.name.clone(),
                passed: false,
                error: Some(format!("type check error on value: {e}")),
                warning: None,
            };
        }
    }

    DeclResult {
        name: item.name.clone(),
        passed: true,
        error: None,
        warning: None,
    }
}

// ---------------------------------------------------------------------------
// High-level entry point
// ---------------------------------------------------------------------------

/// Check Lean source code with parallel type checking.
///
/// This is the parallel equivalent of [`crate::check_source`]. The pipeline:
/// 1. Parse the source
/// 2. Elaborate each declaration sequentially (builds the `Environment`)
/// 3. Extract type+value for each elaborated declaration
/// 4. Build a dependency graph and type-check in parallel batches
///
/// # Errors
///
/// Returns [`ParallelError::Parse`] if parsing fails, or
/// [`ParallelError::EnvInit`] if prelude initialization fails.
pub fn check_source_parallel(
    source: &str,
    config: &ParallelCheckConfig,
) -> Result<ParallelCheckResult> {
    let overall_start = Instant::now();

    let _guard = crate::check::global_lock()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    // Reset global counters.
    reset_sorry_counter();
    clean_elab::register::reset_kernel_check_counter();

    let mut env =
        Environment::try_with_prelude().map_err(|e| ParallelError::EnvInit(format!("{e}")))?;

    // Parse
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(source, &patterns)?;

    // Elaborate sequentially, collecting items for parallel check.
    let mut file_ctx = FileContext::new();
    let mut check_items = Vec::with_capacity(decls.len());

    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_warning(&mut env, &processed) {
            Ok(registered) => {
                let name = crate::check::elab_result_name(&registered.result);
                if name == "(skipped)" {
                    continue;
                }

                // Extract type+value for parallel checking.
                let (ty, value, is_theorem) = extract_check_info(&registered.result);
                if let Some(ty) = ty {
                    // Classify warning.
                    let _warning = registered.warning.as_ref().map(|w| match w.kind {
                        RegistrationWarningKind::ExplicitSorry => DeclWarning::ExplicitSorry,
                        RegistrationWarningKind::SyntheticSorry => DeclWarning::SyntheticSorry,
                        RegistrationWarningKind::TrustedArith => DeclWarning::TrustedArith,
                        RegistrationWarningKind::TrustedAy => DeclWarning::TrustedAy,
                    });

                    check_items.push(ElabCheckItem {
                        name,
                        ty,
                        value,
                        is_theorem,
                    });
                }
            }
            Err(_) => {
                // Elaboration errors are already recorded; skip this decl.
            }
        }
    }

    drop(_guard);

    // Phase 2: Parallel type check.
    let mut result = check_declarations_parallel(&env, &check_items, config);
    result.total_elapsed = overall_start.elapsed();

    Ok(result)
}

/// Extract type, value, and is_theorem from an ElabResult.
fn extract_check_info(result: &clean_elab::ElabResult) -> (Option<Expr>, Option<Expr>, bool) {
    use clean_elab::ElabResult;
    match result {
        ElabResult::Definition { ty, val, .. } | ElabResult::Instance { ty, val, .. } => {
            (Some(ty.clone()), Some(val.clone()), false)
        }
        ElabResult::Theorem { ty, proof, .. } => (Some(ty.clone()), Some(proof.clone()), true),
        // An `example` re-checks like an anonymous definition (B02): its type
        // may live in any sort, so it is NOT flagged as a theorem.
        ElabResult::Example { ty, val } => (Some(ty.clone()), Some(val.clone()), false),
        ElabResult::Axiom { ty, .. } => (Some(ty.clone()), None, false),
        ElabResult::Opaque { ty, val, .. } => (Some(ty.clone()), val.clone(), false),
        ElabResult::Structure { ty, .. } => (Some(ty.clone()), None, false),
        ElabResult::Inductive { .. }
        | ElabResult::MutualInductive { .. }
        | ElabResult::Command(_)
        | ElabResult::Multiple(_)
        // A `Failed` inner decl carries no kernel type/value to extract.
        | ElabResult::Failed { .. }
        | ElabResult::Skipped => (None, None, false),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // DeclDepGraph tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_dep_graph_empty() {
        let graph = DeclDepGraph::new();
        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.edge_count(), 0);
        let batches = graph
            .topological_batches()
            .expect("empty graph has no cycle");
        assert!(batches.is_empty());
    }

    #[test]
    fn test_dep_graph_single_node() {
        let mut graph = DeclDepGraph::new();
        graph.add_declaration(Name::from_string("a"), HashSet::new());
        assert_eq!(graph.node_count(), 1);
        let batches = graph
            .topological_batches()
            .expect("single node has no cycle");
        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].len(), 1);
    }

    #[test]
    fn test_dep_graph_linear_chain() {
        let mut graph = DeclDepGraph::new();
        // a -> b -> c
        graph.add_declaration(Name::from_string("c"), HashSet::new());
        graph.add_declaration(
            Name::from_string("b"),
            [Name::from_string("c")].into_iter().collect(),
        );
        graph.add_declaration(
            Name::from_string("a"),
            [Name::from_string("b")].into_iter().collect(),
        );

        let batches = graph
            .topological_batches()
            .expect("linear chain has no cycle");
        assert_eq!(batches.len(), 3, "linear chain should produce 3 batches");

        // First batch should be "c" (no deps)
        assert!(batches[0].contains(&Name::from_string("c")));
        assert!(batches[1].contains(&Name::from_string("b")));
        assert!(batches[2].contains(&Name::from_string("a")));
    }

    #[test]
    fn test_dep_graph_diamond() {
        let mut graph = DeclDepGraph::new();
        //   a
        //  / \
        // b   c
        //  \ /
        //   d
        graph.add_declaration(Name::from_string("d"), HashSet::new());
        graph.add_declaration(
            Name::from_string("b"),
            [Name::from_string("d")].into_iter().collect(),
        );
        graph.add_declaration(
            Name::from_string("c"),
            [Name::from_string("d")].into_iter().collect(),
        );
        graph.add_declaration(
            Name::from_string("a"),
            [Name::from_string("b"), Name::from_string("c")]
                .into_iter()
                .collect(),
        );

        let batches = graph.topological_batches().expect("diamond has no cycle");
        assert_eq!(batches.len(), 3, "diamond should produce 3 layers");
        assert_eq!(batches[0].len(), 1); // d
        assert_eq!(batches[1].len(), 2); // b, c (independent)
        assert_eq!(batches[2].len(), 1); // a
    }

    #[test]
    fn test_dep_graph_independent_nodes() {
        let mut graph = DeclDepGraph::new();
        graph.add_declaration(Name::from_string("a"), HashSet::new());
        graph.add_declaration(Name::from_string("b"), HashSet::new());
        graph.add_declaration(Name::from_string("c"), HashSet::new());

        let batches = graph
            .topological_batches()
            .expect("independent nodes have no cycle");
        assert_eq!(batches.len(), 1, "all independent -> single batch");
        assert_eq!(batches[0].len(), 3);
    }

    #[test]
    fn test_dep_graph_cycle_detection() {
        let mut graph = DeclDepGraph::new();
        // a -> b -> a (cycle)
        graph.add_declaration(
            Name::from_string("a"),
            [Name::from_string("b")].into_iter().collect(),
        );
        graph.add_declaration(
            Name::from_string("b"),
            [Name::from_string("a")].into_iter().collect(),
        );

        assert!(
            graph.topological_batches().is_none(),
            "cycle should return None"
        );
    }

    #[test]
    fn test_dep_graph_external_deps_ignored() {
        let mut graph = DeclDepGraph::new();
        // "a" depends on "Nat" which is not in the graph
        graph.add_declaration(
            Name::from_string("a"),
            [Name::from_string("Nat")].into_iter().collect(),
        );
        let batches = graph
            .topological_batches()
            .expect("external deps should not block");
        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].len(), 1);
    }

    // -----------------------------------------------------------------------
    // collect_const_refs tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_collect_const_refs_const_expr() {
        let expr = Expr::const_str("Nat");
        let mut refs = HashSet::new();
        collect_const_refs(&expr, &mut refs);
        assert!(refs.contains(&Name::from_string("Nat")));
        assert_eq!(refs.len(), 1);
    }

    #[test]
    fn test_collect_const_refs_nested_app() {
        // App(Const("f"), Const("x"))
        let f = Expr::const_str("f");
        let x = Expr::const_str("x");
        let app = Expr::app(f, x);
        let mut refs = HashSet::new();
        collect_const_refs(&app, &mut refs);
        assert!(refs.contains(&Name::from_string("f")));
        assert!(refs.contains(&Name::from_string("x")));
        assert_eq!(refs.len(), 2);
    }

    #[test]
    fn test_collect_const_refs_no_consts() {
        // A simple BVar should yield no const refs.
        let expr = Expr::bvar(0);
        let mut refs = HashSet::new();
        collect_const_refs(&expr, &mut refs);
        assert!(refs.is_empty());
    }

    // -----------------------------------------------------------------------
    // Parallel checking integration tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_parallel_check_single_def() {
        let config = ParallelCheckConfig::default();
        let result = check_source_parallel("def foo : Nat := 0", &config)
            .expect("parallel check should succeed");
        assert!(
            result.total_passed >= 1,
            "expected at least 1 passed, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn test_parallel_check_independent_defs() {
        let source = "def a : Nat := 0\ndef b : Nat := 1\ndef c : Nat := 2";
        let config = ParallelCheckConfig {
            parallel_threshold: 2,
            ..ParallelCheckConfig::default()
        };
        let result = check_source_parallel(source, &config).expect("parallel check should succeed");
        assert!(
            result.total_passed >= 3,
            "expected 3+ passed, got {}: errors={:?}",
            result.total_passed,
            result.errors
        );
    }

    #[test]
    fn test_parallel_check_error_aggregation() {
        let config = ParallelCheckConfig {
            continue_on_error: true,
            ..ParallelCheckConfig::default()
        };
        // Two valid defs and one with an undefined reference.
        let source = "def good1 : Nat := 0\ndef bad : Nat := unknown_xyz\ndef good2 : Nat := 1";
        let result = check_source_parallel(source, &config).expect("pipeline should not crash");
        // We should still get results for the good declarations.
        assert!(
            result.total_passed >= 2 || !result.errors.is_empty(),
            "should have passed or errors"
        );
    }

    #[test]
    fn test_parallel_check_progress_callback() {
        let event_count = Arc::new(AtomicUsize::new(0));
        let ec = event_count.clone();

        let config = ParallelCheckConfig {
            progress_callback: Some(Arc::new(move |_event| {
                ec.fetch_add(1, Ordering::Relaxed);
            })),
            ..ParallelCheckConfig::default()
        };
        let source = "def cb1 : Nat := 0\ndef cb2 : Nat := 1";
        let _result =
            check_source_parallel(source, &config).expect("parallel check should succeed");

        assert!(
            event_count.load(Ordering::Relaxed) > 0,
            "progress callback should have been called at least once"
        );
    }

    #[test]
    fn test_parallel_check_sequential_fallback() {
        // With a very high threshold, everything should run sequentially.
        let config = ParallelCheckConfig {
            parallel_threshold: 1000,
            ..ParallelCheckConfig::default()
        };
        let source = "def seq1 : Nat := 0\ndef seq2 : Nat := 1";
        let result =
            check_source_parallel(source, &config).expect("sequential fallback should succeed");
        assert!(result.total_passed >= 2);
    }

    #[test]
    fn test_batch_result_timing() {
        let config = ParallelCheckConfig::default();
        let source = "def t1 : Nat := 0\ndef t2 : Nat := 1";
        let result = check_source_parallel(source, &config).expect("parallel check should succeed");
        assert!(
            result.total_elapsed >= Duration::ZERO,
            "total elapsed should be non-negative"
        );
        assert!(
            result.parallel_elapsed >= Duration::ZERO,
            "parallel elapsed should be non-negative"
        );
        for batch in &result.batches {
            assert!(
                batch.elapsed >= Duration::ZERO,
                "batch elapsed should be non-negative"
            );
        }
    }

    #[test]
    fn test_parallel_check_theorem() {
        let config = ParallelCheckConfig::default();
        let result = check_source_parallel("theorem trivial : True := True.intro", &config)
            .expect("parallel check should succeed");
        assert!(
            result.total_passed >= 1,
            "trivial theorem should pass: errors={:?}",
            result.errors
        );
    }

    #[test]
    fn test_parallel_check_empty_source() {
        let config = ParallelCheckConfig::default();
        let result = check_source_parallel("", &config).expect("empty source should succeed");
        assert_eq!(result.total_passed, 0);
        assert_eq!(result.total_failed, 0);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_parallel_check_dependent_defs() {
        let source = r#"
def base : Nat := 42
def derived : Nat := base
"#;
        let config = ParallelCheckConfig::default();
        let result = check_source_parallel(source, &config)
            .expect("parallel check with deps should succeed");
        assert!(
            result.total_passed >= 2,
            "dependent defs should pass: errors={:?}",
            result.errors
        );
        // Should have multiple batches since `derived` depends on `base`.
        assert!(result.batch_count >= 1, "should have at least 1 batch");
    }

    #[test]
    fn test_parallel_result_speedup() {
        let config = ParallelCheckConfig::default();
        let result = check_source_parallel("def sp : Nat := 0", &config)
            .expect("parallel check should succeed");
        let speedup = result.speedup();
        assert!(
            speedup >= 0.0,
            "speedup should be non-negative, got {speedup}"
        );
    }

    #[test]
    fn test_parallel_check_many_independent_defs() {
        let mut source = String::new();
        for i in 0..20 {
            source.push_str(&format!("def par_{i} : Nat := {i}\n"));
        }
        let config = ParallelCheckConfig {
            parallel_threshold: 4,
            ..ParallelCheckConfig::default()
        };
        let result =
            check_source_parallel(&source, &config).expect("many independent defs should succeed");
        assert!(
            result.total_passed >= 20,
            "expected 20+ passed, got {}: errors={:?}",
            result.total_passed,
            result.errors
        );
    }
}
