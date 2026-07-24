// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trait-based optimization pass infrastructure for L5CNF.
//!
//! This module provides a composable, trait-based interface for optimization
//! passes that wraps the function-based passes in [`crate::opt`]. While `opt`
//! provides individual pass functions and a fixed pipeline via [`crate::opt::optimize_code`],
//! this module allows dynamic composition of passes through the [`OptPass`] trait
//! and [`OptimizationPipeline`] builder.
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────────────────────────────────────────────────────┐
//! │                   OptimizationPipeline                       │
//! │                                                              │
//! │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │
//! │  │ DeadCodeElim │→ │ ConstantFold │→ │ InlineSmall  │→ ... │
//! │  └──────────────┘  └──────────────┘  └──────────────┘       │
//! │                                                              │
//! │  Iterates until fixpoint or max_iterations reached           │
//! └──────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Usage
//!
//! See tests in `opt_passes_tests.rs` for concrete usage examples.
//!
//! Part of #3084 - Compiler IR optimization passes.

use crate::lcnf::{Code, Decl, DeclValue};
use crate::opt;

/// Trait for a single optimization pass operating on L5CNF [`Code`].
///
/// Each pass transforms a `Code` block, potentially simplifying it.
/// Passes are composed in an [`OptimizationPipeline`].
pub(crate) trait OptPass: std::fmt::Debug {
    /// Human-readable name for diagnostics.
    fn name(&self) -> &str;

    /// Transform a code block.
    fn run_on_code(&self, code: &Code) -> Code;
}

// ---------------------------------------------------------------------------
// Concrete passes
// ---------------------------------------------------------------------------

/// Dead code elimination: removes unused let-bindings and unreachable code.
///
/// Delegates to [`crate::opt::dce::eliminate_dead_code_in_code`].
#[derive(Debug, Clone, Copy)]
pub(crate) struct DeadCodeElimination;

impl OptPass for DeadCodeElimination {
    fn name(&self) -> &str {
        "dce"
    }

    fn run_on_code(&self, code: &Code) -> Code {
        opt::dce::eliminate_dead_code_in_code(code)
    }
}

/// Constant folding: evaluates constant expressions at compile time.
///
/// Folds arithmetic (`Nat.add 2 3` -> `5`), boolean comparisons
/// (`Nat.ble 2 3` -> `true`), and string operations
/// (`String.append "a" "b"` -> `"ab"`).
///
/// Delegates to [`crate::opt::constant_fold::fold_constants_in_code`].
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConstantFolding;

impl OptPass for ConstantFolding {
    fn name(&self) -> &str {
        "constant_fold"
    }

    fn run_on_code(&self, code: &Code) -> Code {
        opt::constant_fold::fold_constants_in_code(code)
    }
}

/// Common subexpression elimination: deduplicates identical let-bindings.
///
/// Delegates to [`crate::opt::cse::eliminate_common_subexpressions_in_code`].
#[derive(Debug, Clone, Copy)]
pub(crate) struct CommonSubexprElimination;

impl OptPass for CommonSubexprElimination {
    fn name(&self) -> &str {
        "cse"
    }

    fn run_on_code(&self, code: &Code) -> Code {
        opt::cse::eliminate_common_subexpressions_in_code(code)
    }
}

/// Value simplification: simplifies projections after constructors, etc.
///
/// Delegates to [`crate::opt::simp_value::simplify_values_in_code`].
#[derive(Debug, Clone, Copy)]
pub(crate) struct SimplifyValues;

impl OptPass for SimplifyValues {
    fn name(&self) -> &str {
        "simp_value"
    }

    fn run_on_code(&self, code: &Code) -> Code {
        opt::simp_value::simplify_values_in_code(code)
    }
}

/// Inline small functions: inlines function bodies below a size threshold.
///
/// Functions whose body size (in operations) is at or below `threshold`
/// are inlined at their call sites.
///
/// Delegates to [`crate::opt::inline::inline_functions_in_code`].
#[derive(Debug, Clone)]
pub(crate) struct InlineSmall {
    /// Maximum function body size (in operations) to inline.
    pub(crate) threshold: usize,
    /// Maximum inline depth to prevent infinite expansion.
    pub(crate) max_depth: usize,
}

impl InlineSmall {
    /// Create with the given size threshold and default max depth (3).
    pub(crate) fn new(threshold: usize) -> Self {
        Self {
            threshold,
            max_depth: 3,
        }
    }
}

impl Default for InlineSmall {
    fn default() -> Self {
        Self {
            threshold: opt::inline::DEFAULT_INLINE_THRESHOLD,
            max_depth: 3,
        }
    }
}

impl OptPass for InlineSmall {
    fn name(&self) -> &str {
        "inline"
    }

    fn run_on_code(&self, code: &Code) -> Code {
        let config = opt::inline::InlineConfig {
            threshold: self.threshold,
            max_depth: self.max_depth,
        };
        opt::inline::inline_functions_in_code(code, &config)
    }
}

/// Join point conversion: converts tail-called local functions to join points.
///
/// Delegates to [`crate::opt::join_points::find_join_points_in_code`].
#[derive(Debug, Clone, Copy)]
pub(crate) struct FindJoinPoints;

impl OptPass for FindJoinPoints {
    fn name(&self) -> &str {
        "find_join_points"
    }

    fn run_on_code(&self, code: &Code) -> Code {
        opt::join_points::find_join_points_in_code(code)
    }
}

// ---------------------------------------------------------------------------
// Pipeline
// ---------------------------------------------------------------------------

/// Composable optimization pipeline for L5CNF declarations.
///
/// Runs a sequence of [`OptPass`] implementations iteratively until
/// fixpoint (no changes) or `max_iterations` is reached. After the
/// iterative loop, optional finalization passes (like join point
/// conversion) run once.
///
/// # Example
///
/// ```text
/// use clean_compiler::opt_passes::{
///     OptimizationPipeline, DeadCodeElimination, ConstantFolding, InlineSmall,
/// };
///
/// let pipeline = OptimizationPipeline::builder()
///     .max_iterations(5)
///     .pass(DeadCodeElimination)
///     .pass(ConstantFolding)
///     .pass(InlineSmall::new(10))
///     .finalize(clean_compiler::opt_passes::FindJoinPoints)
///     .build();
/// ```
#[derive(Debug)]
pub(crate) struct OptimizationPipeline {
    /// Passes to run in the iterative fixpoint loop.
    passes: Vec<Box<dyn OptPass>>,
    /// Passes to run once after the fixpoint loop.
    finalization: Vec<Box<dyn OptPass>>,
    /// Maximum fixpoint iterations.
    max_iterations: u32,
}

impl Default for OptimizationPipeline {
    /// Create the default pipeline matching [`crate::opt::optimize_code`]'s
    /// pass ordering: DCE -> CSE -> ConstantFold -> SimpValue -> Inline,
    /// with FindJoinPoints as finalization.
    fn default() -> Self {
        Self {
            passes: vec![
                Box::new(DeadCodeElimination),
                Box::new(CommonSubexprElimination),
                Box::new(ConstantFolding),
                Box::new(SimplifyValues),
                Box::new(InlineSmall::default()),
            ],
            finalization: vec![Box::new(FindJoinPoints)],
            max_iterations: 5,
        }
    }
}

impl OptimizationPipeline {
    /// Start building a custom pipeline.
    pub(crate) fn builder() -> PipelineBuilder {
        PipelineBuilder {
            passes: Vec::new(),
            finalization: Vec::new(),
            max_iterations: 5,
        }
    }

    /// Run the pipeline on a single `Code` block.
    ///
    /// Returns the optimized code after fixpoint iteration and finalization.
    #[must_use]
    pub(crate) fn run_on_code(&self, code: &Code) -> Code {
        let mut current = code.clone();

        // Iterative fixpoint loop
        for _ in 0..self.max_iterations {
            let before = current.clone();
            for pass in &self.passes {
                current = pass.run_on_code(&current);
            }
            if current == before {
                break;
            }
        }

        // Finalization passes (run once)
        for pass in &self.finalization {
            current = pass.run_on_code(&current);
        }

        current
    }

    /// Run the pipeline on a declaration.
    ///
    /// Extern declarations pass through unchanged.
    #[must_use]
    pub(crate) fn run(&self, decl: &Decl) -> Decl {
        let body = match &decl.body {
            DeclValue::Code(code) => DeclValue::Code(Box::new(self.run_on_code(code))),
            DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
        };

        Decl {
            name: decl.name.clone(),
            level_params: decl.level_params.clone(),
            ty: decl.ty.clone(),
            params: decl.params.clone(),
            body,
            recursive: decl.recursive,
        }
    }

    /// Number of iterative passes in the pipeline.
    pub(crate) fn pass_count(&self) -> usize {
        self.passes.len()
    }

    /// Number of finalization passes.
    pub(crate) fn finalization_count(&self) -> usize {
        self.finalization.len()
    }

    /// Names of all iterative passes in order.
    pub(crate) fn pass_names(&self) -> Vec<&str> {
        self.passes.iter().map(|p| p.name()).collect()
    }
}

/// Builder for [`OptimizationPipeline`].
#[must_use]
#[derive(Debug)]
pub(crate) struct PipelineBuilder {
    passes: Vec<Box<dyn OptPass>>,
    finalization: Vec<Box<dyn OptPass>>,
    max_iterations: u32,
}

impl PipelineBuilder {
    /// Set the maximum number of fixpoint iterations.
    pub(crate) fn max_iterations(mut self, n: u32) -> Self {
        self.max_iterations = n;
        self
    }

    /// Add an iterative pass to the pipeline.
    pub(crate) fn pass(mut self, pass: impl OptPass + 'static) -> Self {
        self.passes.push(Box::new(pass));
        self
    }

    /// Add a finalization pass (runs once after the fixpoint loop).
    pub(crate) fn finalize(mut self, pass: impl OptPass + 'static) -> Self {
        self.finalization.push(Box::new(pass));
        self
    }

    /// Build the pipeline.
    pub(crate) fn build(self) -> OptimizationPipeline {
        OptimizationPipeline {
            passes: self.passes,
            finalization: self.finalization,
            max_iterations: self.max_iterations,
        }
    }
}

#[cfg(test)]
#[path = "opt_passes_tests.rs"]
mod tests;
