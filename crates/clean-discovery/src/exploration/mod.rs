// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theory exploration mode: automatically enumerate consequences of axioms
//! and definitions, discover lemmas, and build up a theory without human
//! guidance.
//!
//! Inspired by Isabelle Hipster / QuickSpec. Given definitions (e.g., Nat
//! arithmetic), the system:
//!
//! 1. Generates candidate lemmas by pattern (commutativity, associativity, etc.)
//! 2. Filters with computational counterexamples
//! 3. Proves survivors using kernel type checking
//! 4. Feeds discovered lemmas back into deeper exploration
//!
//! Part of #3194, Epic #3173 (LLM-Driven Math Research Engine).

use std::collections::HashSet;
use std::time::{Duration, Instant};

use crate::error::DiscoveryError;
use crate::exploration_patterns::{generate_candidates, CandidateEquation, FuncSig, TermPattern};
use clean_kernel::{BatchConfig, BatchVerifier, Declaration, Environment, Expr, Name};

mod nat_eval;

/// Configuration for a theory exploration run.
#[derive(Debug, Clone)]
pub struct ExplorationConfig {
    /// Maximum exploration depth (number of feedback iterations).
    pub max_depth: u32,
    /// Maximum number of candidate terms to generate per iteration.
    pub max_terms: usize,
    /// Which algebraic patterns to explore.
    pub pattern_types: Vec<TermPattern>,
    /// Timeout for the entire exploration run.
    pub timeout: Duration,
    /// Number of random samples for counterexample filtering.
    pub counterexample_samples: u32,
    /// The name of the Eq constant (usually "Eq").
    pub eq_const: String,
    /// Number of threads for batch verification (None = default).
    pub num_threads: Option<usize>,
}

impl Default for ExplorationConfig {
    fn default() -> Self {
        Self {
            max_depth: 3,
            max_terms: 1000,
            pattern_types: TermPattern::ALL.to_vec(),
            timeout: Duration::from_secs(60),
            counterexample_samples: 100,
            eq_const: "Eq".to_string(),
            num_threads: None,
        }
    }
}

/// Mutable state tracked across exploration iterations.
#[derive(Debug, Clone)]
pub struct ExplorationState {
    /// Statements of lemmas discovered so far (as Debug strings for dedup).
    pub(crate) known_lemma_reprs: HashSet<String>,
    /// Discovered lemma statements (kernel Exprs).
    pub known_lemmas: Vec<DiscoveredLemma>,
    /// Types/sorts encountered during exploration.
    pub known_types: Vec<Expr>,
    /// Current exploration depth (0-indexed).
    pub exploration_depth: u32,
}

impl ExplorationState {
    /// Create a fresh exploration state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            known_lemma_reprs: HashSet::new(),
            known_lemmas: Vec::new(),
            known_types: Vec::new(),
            exploration_depth: 0,
        }
    }

    /// Check if a statement is already known.
    #[must_use]
    pub fn is_known(&self, statement: &Expr) -> bool {
        let repr = format!("{statement:?}");
        self.known_lemma_reprs.contains(&repr)
    }

    /// Register a newly discovered lemma.
    pub fn add_lemma(&mut self, lemma: DiscoveredLemma) {
        let repr = format!("{:?}", lemma.statement);
        self.known_lemma_reprs.insert(repr);
        self.known_lemmas.push(lemma);
    }
}

impl Default for ExplorationState {
    fn default() -> Self {
        Self::new()
    }
}

/// A lemma discovered during exploration.
#[derive(Debug, Clone)]
pub struct DiscoveredLemma {
    /// The universally quantified statement.
    pub statement: Expr,
    /// Human-readable description.
    pub description: String,
    /// Which pattern produced this lemma.
    pub pattern: TermPattern,
    /// Names of functions involved.
    pub func_names: Vec<String>,
    /// At which exploration depth this was discovered.
    pub depth: u32,
}

/// Result of a complete exploration run.
#[derive(Debug)]
pub struct ExplorationResult {
    /// All lemmas discovered across all iterations.
    pub discovered_lemmas: Vec<DiscoveredLemma>,
    /// Total candidate equations explored.
    pub explored_count: u64,
    /// Total candidates that survived counterexample filtering.
    pub survived_filter_count: u64,
    /// Total candidates that were proved (type-checked).
    pub proved_count: u64,
    /// Number of exploration iterations completed.
    pub iterations_completed: u32,
    /// Wall-clock time for the entire run.
    pub wall_time: Duration,
}

/// Counterexample filter: tests candidate equations with random inputs.
///
/// For Nat operations, evaluates both sides of an equation with random
/// natural number inputs. If any input produces different results on
/// the two sides, the candidate is falsified.
pub struct CounterexampleFilter {
    /// Number of deterministic samples tested per candidate equation.
    samples: u32,
}

impl CounterexampleFilter {
    /// Create a new filter with the given number of test samples.
    #[must_use]
    pub fn new(samples: u32) -> Self {
        Self { samples }
    }

    /// Attempt to falsify a candidate equation by deterministic testing.
    ///
    /// Returns `true` if the candidate survives (no counterexample found),
    /// `false` if a concrete counterexample was found.
    ///
    /// When both sides of the candidate are closed, evaluable `Nat` expressions
    /// (a universally quantified `@Eq Nat lhs rhs`), this runs a real
    /// computational test on deterministically sampled inputs (see
    /// [`nat_eval`]). The candidate is rejected only when some sample makes both
    /// sides evaluate to definite, different values. For non-`Nat` /
    /// inconclusive candidates (e.g. implications, orderings, or operators the
    /// evaluator does not model), it falls back to the structural heuristic
    /// below, preserving prior behavior.
    #[must_use]
    pub fn survives(&self, candidate: &CandidateEquation) -> bool {
        // Real computational filter: if the statement is a universally
        // quantified equality whose two sides are fully Nat-evaluable, test it
        // on deterministically sampled inputs and trust that verdict directly.
        if let Some((num_binders, lhs, rhs)) = nat_eval::extract_eq_body(&candidate.statement) {
            let seed = nat_eval::deterministic_seed(&candidate.statement, &candidate.func_names);
            match nat_eval::test_equation(&lhs, &rhs, num_binders, self.samples, seed) {
                // Concrete counterexample: definitely reject.
                nat_eval::EquationVerdict::Counterexample => return false,
                // Both sides always evaluable, never disagreed: definitely
                // survive. Do NOT fall through to the heuristic, which could
                // otherwise (unsoundly) reject a true equation.
                nat_eval::EquationVerdict::NoCounterexample => return true,
                // Some side was not Nat-evaluable: fall back to the heuristic.
                nat_eval::EquationVerdict::Inconclusive => {}
            }
        }

        // Structural heuristic: reject patterns that are trivially false
        // based on the pattern type and known algebraic facts.
        match candidate.pattern {
            TermPattern::Idempotency => {
                // Most arithmetic ops are not idempotent (e.g., add(a,a) != a for a > 0)
                // Filter: only allow if function name suggests idempotent behavior
                let name = &candidate.func_names[0];
                name.contains("max")
                    || name.contains("min")
                    || name.contains("or")
                    || name.contains("and")
                    || name.contains("union")
                    || name.contains("inter")
            }
            TermPattern::Absorption => {
                // Absorption is rare outside lattice operations
                let f = &candidate.func_names[0];
                let g = &candidate.func_names[1];
                (f.contains("max") && g.contains("min"))
                    || (f.contains("min") && g.contains("max"))
                    || (f.contains("or") && g.contains("and"))
                    || (f.contains("and") && g.contains("or"))
            }
            TermPattern::Identity => {
                // Right identity with 0: true for add, not for sub or div
                let name = &candidate.func_names[0];
                name.contains("add") || name.contains("or") || name.contains("append")
            }
            TermPattern::Distributivity => {
                // mul distributes over add, but not add over mul
                let f = &candidate.func_names[0];
                let g = &candidate.func_names[1];
                f.contains("mul") && g.contains("add")
            }
            // Conservative: let other patterns through to kernel verification
            _ => true,
        }
    }

    /// Filter a batch of candidates, returning only survivors.
    #[must_use]
    pub fn filter_batch<'a>(
        &self,
        candidates: &'a [CandidateEquation],
    ) -> Vec<&'a CandidateEquation> {
        candidates.iter().filter(|c| self.survives(c)).collect()
    }
}

/// Pattern-based candidate generator.
///
/// Given a set of function signatures, generates candidate equations
/// by instantiating algebraic pattern templates.
pub struct PatternGenerator {
    /// Function signatures available for exploration.
    signatures: Vec<FuncSig>,
    /// Patterns to apply.
    patterns: Vec<TermPattern>,
    /// Eq constant name.
    eq_const: String,
}

impl PatternGenerator {
    /// Create a new generator with the given functions and patterns.
    #[must_use]
    pub fn new(signatures: Vec<FuncSig>, patterns: Vec<TermPattern>, eq_const: &str) -> Self {
        Self {
            signatures,
            patterns,
            eq_const: eq_const.to_string(),
        }
    }

    /// Generate all candidate equations from the configured patterns.
    #[must_use]
    pub fn generate(&self) -> Vec<CandidateEquation> {
        generate_candidates(&self.signatures, &self.patterns, &self.eq_const)
    }

    /// Add new function signatures (e.g., from discovered lemmas).
    pub fn add_signatures(&mut self, new_sigs: Vec<FuncSig>) {
        self.signatures.extend(new_sigs);
    }
}

/// Orchestrates the generate -> filter -> prove -> feedback loop.
///
/// The runner maintains an `ExplorationState` across iterations. Each
/// iteration generates candidates, filters with counterexamples, verifies
/// survivors against the kernel, and feeds discovered lemmas back into the
/// next round.
pub struct ExplorationRunner {
    env: Environment,
    config: ExplorationConfig,
    state: ExplorationState,
    generator: PatternGenerator,
    filter: CounterexampleFilter,
}

impl ExplorationRunner {
    /// Create a new exploration runner.
    ///
    /// # Errors
    ///
    /// Returns `DiscoveryError` if the environment cannot be initialized.
    pub fn new(
        signatures: Vec<FuncSig>,
        config: ExplorationConfig,
    ) -> Result<Self, DiscoveryError> {
        let env = Environment::new();
        Self::with_env(env, signatures, config)
    }

    /// Create a runner with a pre-initialized environment.
    ///
    /// # Errors
    ///
    /// Returns `DiscoveryError` if the configuration is invalid.
    pub fn with_env(
        env: Environment,
        signatures: Vec<FuncSig>,
        config: ExplorationConfig,
    ) -> Result<Self, DiscoveryError> {
        if signatures.is_empty() {
            return Err(DiscoveryError::InvalidConfig {
                reason: "at least one function signature is required".to_string(),
            });
        }
        if config.pattern_types.is_empty() {
            return Err(DiscoveryError::InvalidConfig {
                reason: "at least one pattern type is required".to_string(),
            });
        }

        let generator =
            PatternGenerator::new(signatures, config.pattern_types.clone(), &config.eq_const);
        let filter = CounterexampleFilter::new(config.counterexample_samples);
        let state = ExplorationState::new();

        Ok(Self {
            env,
            config,
            state,
            generator,
            filter,
        })
    }

    /// Run the full exploration loop.
    ///
    /// Iterates up to `max_depth` times, generating candidates, filtering,
    /// proving, and feeding back. Respects the configured timeout.
    pub fn run(&mut self) -> ExplorationResult {
        let start = Instant::now();
        let mut explored_count: u64 = 0;
        let mut survived_filter_count: u64 = 0;
        let mut proved_count: u64 = 0;
        let mut iterations_completed: u32 = 0;

        for depth in 0..self.config.max_depth {
            if start.elapsed() >= self.config.timeout {
                break;
            }
            self.state.exploration_depth = depth;

            // 1. Generate and truncate candidates
            let candidates = self.generator.generate();
            let count = candidates.len().min(self.config.max_terms);
            let candidates = &candidates[..count];
            explored_count += candidates.len() as u64;

            // 2. Filter with counterexamples
            let survivors = self.filter.filter_batch(candidates);
            survived_filter_count += survivors.len() as u64;
            if survivors.is_empty() {
                iterations_completed += 1;
                continue;
            }

            // 3. Prove survivors and 4. Feedback
            proved_count += self.verify_and_feedback(&survivors, depth);
            iterations_completed += 1;
        }

        ExplorationResult {
            discovered_lemmas: self.state.known_lemmas.clone(),
            explored_count,
            survived_filter_count,
            proved_count,
            iterations_completed,
            wall_time: start.elapsed(),
        }
    }

    /// Verify survivors via kernel type checking and register proved lemmas.
    ///
    /// Returns the number of newly proved lemmas.
    fn verify_and_feedback(&mut self, survivors: &[&CandidateEquation], depth: u32) -> u64 {
        let batch_config = BatchConfig {
            num_threads: self.config.num_threads,
            ..BatchConfig::default()
        };
        let verifier = BatchVerifier::with_config(&self.env, batch_config);
        let exprs: Vec<Expr> = survivors.iter().map(|c| c.statement.clone()).collect();
        let (results, _stats) = verifier.batch_check_with_stats(&exprs);

        let mut newly_proved: u64 = 0;
        for (candidate, result) in survivors.iter().zip(results.iter()) {
            if result.valid && !self.state.is_known(&candidate.statement) {
                let lemma = DiscoveredLemma {
                    statement: candidate.statement.clone(),
                    description: candidate.description.clone(),
                    pattern: candidate.pattern,
                    func_names: candidate.func_names.clone(),
                    depth,
                };
                self.state.add_lemma(lemma);
                newly_proved += 1;
            }
        }

        // Feedback: register discovered lemmas as axioms for future iterations.
        for lemma in &self.state.known_lemmas {
            let name_str = format!(
                "Exploration.lemma_{}_{}",
                lemma.pattern,
                lemma.func_names.join("_")
            );
            let name = Name::from_string(&name_str);
            if self.env.get_const(&name).is_none() {
                let _ = self.env.add_decl(Declaration::Axiom {
                    name,
                    level_params: vec![],
                    type_: lemma.statement.clone(),
                });
            }
        }

        newly_proved
    }

    /// Access the current exploration state.
    #[must_use]
    pub fn state(&self) -> &ExplorationState {
        &self.state
    }

    /// Access the underlying environment.
    #[must_use]
    pub fn env(&self) -> &Environment {
        &self.env
    }
}

#[cfg(test)]
mod tests;
