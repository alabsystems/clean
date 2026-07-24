// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pass Manager - Compiler Phase Infrastructure
//!
//! Organizes compiler passes into phases (base → mono → impure) and manages
//! pass execution order.
//!
//! Based on Lean 4's `src/Lean/Compiler/LCNF/PassManager.lean`.
//!
//! # Phases
//!
//! The compiler operates in three phases, with unidirectional progression:
//!
//! 1. **Base** - Initial LCNF, fully polymorphic with type parameters
//! 2. **Mono** - After monomorphization, types erased
//! 3. **Impure** - After mutation/side-effect exposure (for RC)
//!
//! # Usage
//!
//! ```rust,no_run
//! use clean_compiler::pass_manager::{PassManager, Phase, Pass};
//!
//! let mut manager = PassManager::new();
//!
//! // Register passes with their phases
//! manager.register(Pass::new("dce", Phase::Base, |decl, _| Ok(vec![decl.clone()])));
//! manager.register(Pass::new("to_mono", Phase::Base, |decl, _| Ok(vec![decl.clone()])));
//! manager.register(Pass::new("simp", Phase::Mono, |decl, _| Ok(vec![decl.clone()])));
//!
//! // Validate that phases are correctly ordered
//! manager.validate().unwrap();
//!
//! // Execute all passes
//! // let result = manager.run(&decl, &env)?;
//! ```
//!
//! For full batch compilation, use the orchestration helpers in
//! [`crate::pass_manager::compile_lcnf_decls`], [`crate::pass_manager::compile_lcnf_to_c`],
//! and [`crate::pass_manager::compile_lcnf_to_rust`]. These compose the existing
//! monomorphization, optimization, RC, IR lowering, boxing, and emission stages
//! without losing lambda-lifted auxiliary declarations.
//!
//! Part of #1094.

mod defaults;
mod pipeline;
pub(crate) mod validate;

use crate::lcnf::Decl;
use clean_kernel::{Environment, Name};
use std::collections::HashMap;
use std::sync::Arc;
use thiserror::Error;

#[cfg(feature = "trust-ir-backend")]
pub use pipeline::compile_lcnf_to_trust_ir;
pub use pipeline::{
    compile_lcnf_decls, compile_lcnf_to_c, compile_lcnf_to_rust, PipelineArtifacts, PipelineConfig,
    PipelineError,
};

/// Compiler phases (progression is unidirectional).
///
/// Corresponds to Lean 4's `Phase` inductive in PassManager.lean.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Phase {
    /// Initial LCNF, polymorphic code with type parameters.
    Base = 0,
    /// After monomorphization, types erased.
    Mono = 1,
    /// After mutation/side-effect exposure, ready for RC.
    Impure = 2,
}

impl Phase {
    /// Convert phase to numeric representation.
    pub fn to_nat(self) -> u8 {
        self as u8
    }

    /// Convert from numeric representation.
    pub fn from_nat(n: u8) -> Option<Self> {
        match n {
            0 => Some(Phase::Base),
            1 => Some(Phase::Mono),
            2 => Some(Phase::Impure),
            _ => None,
        }
    }

    /// Get human-readable name.
    pub fn name(self) -> &'static str {
        match self {
            Phase::Base => "base",
            Phase::Mono => "mono",
            Phase::Impure => "impure",
        }
    }
}

impl std::fmt::Display for Phase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Pass function signature.
///
/// Takes a declaration and environment, returns one or more transformed
/// declarations. Passes like lambda lifting produce auxiliary declarations
/// alongside the main output.
///
/// Uses `Arc<dyn Fn>` rather than a bare function pointer so that passes
/// can capture configuration (e.g., `OptConfig`, `RCConfig`) in closures.
pub type PassFn = Arc<dyn Fn(&Decl, &Environment) -> Result<Vec<Decl>, PassError> + Send + Sync>;

/// Error during pass execution.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum PassError {
    /// Pass expects a different phase.
    #[error("phase mismatch: expected {expected}, got {actual}")]
    PhaseMismatch { expected: Phase, actual: Phase },
    /// Pass validation failed.
    #[error("validation error: {0}")]
    ValidationError(String),
    /// Generic pass error.
    #[error("{0}")]
    Error(String),
}

/// A single compiler pass.
///
/// Corresponds to Lean 4's `Pass` structure in PassManager.lean.
#[derive(Clone)]
pub struct Pass {
    /// Which occurrence of the pass in the pipeline this is.
    /// Some passes (like simp) run multiple times.
    pub occurrence: usize,
    /// Which phase this pass runs in.
    pub phase: Phase,
    /// Resulting phase (for passes that transition phases).
    pub phase_out: Phase,
    /// Name of the pass for identification and debugging.
    pub name: Name,
    /// The actual pass function.
    pub run: PassFn,
}

impl Pass {
    /// Create a new pass that stays in the same phase.
    pub fn new(
        name: &str,
        phase: Phase,
        run: impl Fn(&Decl, &Environment) -> Result<Vec<Decl>, PassError> + Send + Sync + 'static,
    ) -> Self {
        Self {
            occurrence: 0,
            phase,
            phase_out: phase,
            name: Name::from_string(name),
            run: Arc::new(run),
        }
    }

    /// Create a new pass with phase transition.
    ///
    /// # Panics
    /// Panics if `phase_out < phase` (phases must progress forward).
    pub fn with_transition(
        name: &str,
        phase: Phase,
        phase_out: Phase,
        run: impl Fn(&Decl, &Environment) -> Result<Vec<Decl>, PassError> + Send + Sync + 'static,
    ) -> Self {
        assert!(
            phase_out >= phase,
            "Pass phase_out ({}) must be >= phase ({})",
            phase_out,
            phase
        );
        Self {
            occurrence: 0,
            phase,
            phase_out,
            name: Name::from_string(name),
            run: Arc::new(run),
        }
    }

    /// Create a pass with a specific occurrence number.
    pub fn with_occurrence(mut self, occurrence: usize) -> Self {
        self.occurrence = occurrence;
        self
    }

    /// Execute the pass on a declaration, returning one or more output declarations.
    pub fn execute(&self, decl: &Decl, env: &Environment) -> Result<Vec<Decl>, PassError> {
        (self.run)(decl, env)
    }
}

impl std::fmt::Debug for Pass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Pass")
            .field("name", &self.name.to_string())
            .field("phase", &self.phase)
            .field("phase_out", &self.phase_out)
            .field("occurrence", &self.occurrence)
            .finish()
    }
}

/// Manages compiler passes organized by phase.
///
/// Corresponds to Lean 4's `PassManager` in PassManager.lean.
#[derive(Debug, Default)]
pub struct PassManager {
    /// Passes for the base phase.
    base_passes: Vec<Pass>,
    /// Passes for the mono phase.
    mono_passes: Vec<Pass>,
    /// Passes for the impure phase.
    impure_passes: Vec<Pass>,
    /// Track occurrence counts by pass name.
    occurrence_counts: HashMap<Name, usize>,
}

impl PassManager {
    /// Create a new empty pass manager.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a pass in the appropriate phase.
    ///
    /// Automatically assigns occurrence number for passes with the same name.
    pub fn register(&mut self, mut pass: Pass) {
        // Track occurrence
        let count = self.occurrence_counts.entry(pass.name.clone()).or_insert(0);
        pass.occurrence = *count;
        *count += 1;

        // Add to appropriate phase list
        match pass.phase {
            Phase::Base => self.base_passes.push(pass),
            Phase::Mono => self.mono_passes.push(pass),
            Phase::Impure => self.impure_passes.push(pass),
        }
    }

    /// Validate that all passes are correctly assigned to their phases.
    ///
    /// Returns error if any pass is in the wrong phase list.
    pub fn validate(&self) -> Result<(), PassError> {
        Self::validate_passes(Phase::Base, &self.base_passes)?;
        Self::validate_passes(Phase::Mono, &self.mono_passes)?;
        Self::validate_passes(Phase::Impure, &self.impure_passes)?;
        Ok(())
    }

    fn validate_passes(expected_phase: Phase, passes: &[Pass]) -> Result<(), PassError> {
        for pass in passes {
            if pass.phase != expected_phase {
                return Err(PassError::PhaseMismatch {
                    expected: expected_phase,
                    actual: pass.phase,
                });
            }
        }
        Ok(())
    }

    /// Get passes for a specific phase.
    pub fn passes_for_phase(&self, phase: Phase) -> &[Pass] {
        match phase {
            Phase::Base => &self.base_passes,
            Phase::Mono => &self.mono_passes,
            Phase::Impure => &self.impure_passes,
        }
    }

    /// Find the occurrence bounds for a pass by name.
    ///
    /// Returns (lowest, highest) occurrence numbers.
    pub fn find_occurrence_bounds(&self, name: &Name) -> Option<(usize, usize)> {
        let all_passes = self
            .base_passes
            .iter()
            .chain(self.mono_passes.iter())
            .chain(self.impure_passes.iter());

        let mut lowest: Option<usize> = None;
        let mut highest: Option<usize> = None;

        for pass in all_passes {
            if &pass.name == name {
                lowest = Some(lowest.map_or(pass.occurrence, |l| l.min(pass.occurrence)));
                highest = Some(highest.map_or(pass.occurrence, |h| h.max(pass.occurrence)));
            }
        }

        match (lowest, highest) {
            (Some(l), Some(h)) => Some((l, h)),
            _ => None,
        }
    }

    /// Run all passes on a declaration, progressing through phases.
    ///
    /// Executes passes in phase order (base → mono → impure). Each pass
    /// may produce auxiliary declarations (e.g. lambda lifting); these are
    /// accumulated and also fed through subsequent passes.
    pub fn run(&self, decl: &Decl, env: &Environment) -> Result<Vec<Decl>, PassError> {
        let mut decls = vec![decl.clone()];

        for pass in self
            .base_passes
            .iter()
            .chain(self.mono_passes.iter())
            .chain(self.impure_passes.iter())
        {
            decls = Self::apply_pass(pass, &decls, env)?;
        }

        Ok(decls)
    }

    /// Run passes only up to and including a specific phase.
    ///
    /// - `Phase::Base` - runs only base passes
    /// - `Phase::Mono` - runs base and mono passes
    /// - `Phase::Impure` - runs all passes (same as `run`)
    pub fn run_until_phase(
        &self,
        decl: &Decl,
        env: &Environment,
        target_phase: Phase,
    ) -> Result<Vec<Decl>, PassError> {
        let mut decls = vec![decl.clone()];

        for pass in &self.base_passes {
            decls = Self::apply_pass(pass, &decls, env)?;
        }

        if target_phase >= Phase::Mono {
            for pass in &self.mono_passes {
                decls = Self::apply_pass(pass, &decls, env)?;
            }
        }

        if target_phase >= Phase::Impure {
            for pass in &self.impure_passes {
                decls = Self::apply_pass(pass, &decls, env)?;
            }
        }

        Ok(decls)
    }

    /// Apply a single pass to all declarations, collecting results.
    fn apply_pass(pass: &Pass, decls: &[Decl], env: &Environment) -> Result<Vec<Decl>, PassError> {
        let mut out = Vec::new();
        for decl in decls {
            out.extend(pass.execute(decl, env)?);
        }
        Ok(out)
    }

    /// Run all passes on a batch of declarations, progressing through phases.
    ///
    /// Like [`run`](Self::run) but starts from multiple input declarations.
    /// Each pass is applied to every declaration in the accumulator, and
    /// auxiliary outputs (e.g. from lambda lifting) are accumulated and
    /// carried forward to subsequent passes.
    pub fn run_batch(&self, decls: &[Decl], env: &Environment) -> Result<Vec<Decl>, PassError> {
        let mut current: Vec<Decl> = decls.to_vec();

        for pass in self
            .base_passes
            .iter()
            .chain(self.mono_passes.iter())
            .chain(self.impure_passes.iter())
        {
            current = Self::apply_pass(pass, &current, env)?;
        }

        Ok(current)
    }

    /// Run batch passes up to and including a specific phase.
    ///
    /// Like [`run_until_phase`](Self::run_until_phase) but starts from multiple
    /// input declarations.
    pub fn run_batch_until_phase(
        &self,
        decls: &[Decl],
        env: &Environment,
        target_phase: Phase,
    ) -> Result<Vec<Decl>, PassError> {
        let mut current: Vec<Decl> = decls.to_vec();

        for pass in &self.base_passes {
            current = Self::apply_pass(pass, &current, env)?;
        }

        if target_phase >= Phase::Mono {
            for pass in &self.mono_passes {
                current = Self::apply_pass(pass, &current, env)?;
            }
        }

        if target_phase >= Phase::Impure {
            for pass in &self.impure_passes {
                current = Self::apply_pass(pass, &current, env)?;
            }
        }

        Ok(current)
    }

    /// Count total registered passes.
    pub fn pass_count(&self) -> usize {
        self.base_passes.len() + self.mono_passes.len() + self.impure_passes.len()
    }

    /// Clear all registered passes.
    pub fn clear(&mut self) {
        self.base_passes.clear();
        self.mono_passes.clear();
        self.impure_passes.clear();
        self.occurrence_counts.clear();
    }

    // default_pipeline() and default_pipeline_with_config() are in defaults.rs
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod validate_tests;
