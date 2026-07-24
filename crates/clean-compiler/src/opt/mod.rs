// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5CNF Optimization Passes
//!
//! This module contains optimization passes that transform L5CNF code
//! to improve performance. Based on Lean 4's LCNF optimization pipeline.
//!
//! # Passes
//!
//! - `dce`: Dead code elimination - removes unused let-bindings
//! - `cse`: Common subexpression elimination
//! - `constant_fold`: Compile-time constant evaluation
//! - `extract_closed`: Extract closed subexpressions to top-level declarations
//! - `simp_value`: Value simplification (projection after constructor, etc.)
//! - `inline`: Inline small functions
//! - `join_points`: Convert tail-called local functions to join points
//! - `common_jp_args`: Eliminate redundant join point parameters
//! - `reduce_jp_arity`: Remove unused join point parameters
//! - `lambda_lift`: Transform local functions into top-level declarations
//! - `pull_fun_decls`: Pull local functions to outermost valid scope
//! - `pull_let_decls`: Hoist typeclass instance bindings out of nested scopes
//! - `struct_proj_cases`: Optimize struct projection in case alternatives
//! - `specialize`: Function specialization for typeclass instances
//! - `elim_dead_branches`: Eliminate statically-known dead case branches
//! - `extend_jp_context`: Duplicate outer let-bindings into join point bodies
//! - `float_let_in`: Sink let-bindings closer to their use sites
//! - `reduce_arity`: Remove unused top-level function parameters
//!
//! # Usage
//!
//! ## Batch Optimization (Preferred)
//!
//! For multiple declarations, use `optimize_all` which enables cross-declaration
//! optimizations like function specialization:
//!
//! ```rust,no_run
//! use clean_compiler::lcnf::Decl;
//! use clean_compiler::opt::{optimize_all, OptConfig};
//!
//! let decls: Vec<Decl> = todo!();
//! let optimized = optimize_all(&decls, &OptConfig::default());
//! ```
//!
//! ## Single Declaration
//!
//! For a single declaration:
//!
//! ```rust,no_run
//! use clean_compiler::lcnf::Decl;
//! use clean_compiler::opt::{optimize, OptConfig};
//!
//! let decl: Decl = todo!();
//! let optimized = optimize(&decl, &OptConfig::default());
//! ```
//!
//! ## Individual Passes (Manual)
//!
//! Individual passes can be applied directly for fine-grained control:
//!
//! ```rust,no_run
//! use clean_compiler::lcnf::Decl;
//! use clean_compiler::opt::{cse, dce, inline, constant_fold, join_points, simp_value};
//!
//! let decl: Decl = todo!();
//! let opt1 = dce::eliminate_dead_code(&decl);
//! let opt2 = cse::eliminate_common_subexpressions(&opt1);
//! let opt3 = constant_fold::fold_constants(&opt2);
//! let opt4 = simp_value::simplify_values(&opt3);
//! let opt5 = inline::inline_functions(&opt4);
//! let opt6 = join_points::find_join_points(&opt5);
//! ```
//!
//! Part of #963 - Compiler IR infrastructure.

pub mod common_jp_args;
pub mod constant_fold;
pub mod cse;
pub mod dce;
pub mod elim_dead_branches;
pub mod extend_jp_context;
pub mod extract_closed;
pub mod float_let_in;
pub mod inline;
pub mod join_points;
pub mod lambda_lift;
pub mod pull_fun_decls;
pub mod pull_let_decls;
pub mod reduce_arity;
pub mod reduce_jp_arity;
pub mod simp;
pub mod simp_value;
pub mod specialize;
pub mod struct_proj_cases;

use crate::lcnf::{Code, Decl, DeclValue};

/// Configuration for the optimization pipeline.
#[derive(Debug, Clone)]
pub struct OptConfig {
    /// Maximum iterations for fixpoint optimization (default: 5).
    pub max_iterations: u32,
    /// Size threshold for inlining functions (default: 10).
    pub inline_threshold: u32,
    /// Enable common subexpression elimination (default: true).
    pub enable_cse: bool,
    /// Enable constant folding (default: true).
    pub enable_constant_fold: bool,
    /// Enable value simplification (default: true).
    pub enable_simp_value: bool,
    /// Enable dead code elimination (default: true).
    pub enable_dce: bool,
    /// Enable function inlining (default: true).
    pub enable_inline: bool,
    /// Enable join point conversion (default: true).
    pub enable_join_points: bool,
    /// Enable function specialization (default: true).
    pub enable_specialize: bool,
    /// Enable lambda lifting (default: true).
    ///
    /// When enabled, local functions are lifted to top-level declarations
    /// before the optimization loop. This runs as a batch pass in
    /// `optimize_all`, following Lean 4's pipeline ordering where lambda
    /// lifting precedes the Simp/CSE optimization rounds.
    pub enable_lambda_lift: bool,
    /// Enable closed-term extraction (default: true).
    pub enable_extract_closed: bool,
    /// Enable typeclass instance hoisting (default: true).
    pub enable_pull_let_decls: bool,
}

impl Default for OptConfig {
    fn default() -> Self {
        Self {
            max_iterations: 5,
            inline_threshold: 10,
            enable_cse: true,
            enable_constant_fold: true,
            enable_simp_value: true,
            enable_dce: true,
            enable_inline: true,
            enable_join_points: true,
            enable_specialize: true,
            enable_lambda_lift: true,
            enable_extract_closed: true,
            enable_pull_let_decls: true,
        }
    }
}

impl OptConfig {
    /// Create a minimal config with only DCE enabled.
    pub fn minimal() -> Self {
        Self {
            max_iterations: 1,
            inline_threshold: 0,
            enable_cse: false,
            enable_constant_fold: false,
            enable_simp_value: false,
            enable_dce: true,
            enable_inline: false,
            enable_join_points: false,
            enable_specialize: false,
            enable_lambda_lift: false,
            enable_extract_closed: false,
            enable_pull_let_decls: false,
        }
    }

    /// Create a config with all optimizations enabled at maximum.
    pub fn aggressive() -> Self {
        Self {
            max_iterations: 10,
            inline_threshold: 20,
            enable_cse: true,
            enable_constant_fold: true,
            enable_simp_value: true,
            enable_dce: true,
            enable_inline: true,
            enable_join_points: true,
            enable_specialize: true,
            enable_lambda_lift: true,
            enable_extract_closed: true,
            enable_pull_let_decls: true,
        }
    }
}

/// Run all optimization passes on a declaration.
///
/// Runs the optimization loop until fixpoint or max_iterations is reached,
/// then runs FindJoinPoints once at the end.
///
/// # Pipeline Order
///
/// ```text
/// ┌──────────────────────────────────────────────┐
/// │          OPTIMIZATION LOOP (repeat)          │
/// │                                              │
/// │  DCE → CSE → ConstFold → SimpValue → Inline  │
/// │                                              │
/// └──────────────────────────────────────────────┘
///                        │
///                        ▼
///               FindJoinPoints (once)
/// ```
pub fn optimize(decl: &Decl, config: &OptConfig) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => {
            let optimized = optimize_code(code, config);
            DeclValue::Code(Box::new(optimized))
        }
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

/// Run all optimization passes on code.
///
/// This is the core optimization loop that runs passes until fixpoint.
pub fn optimize_code(code: &Code, config: &OptConfig) -> Code {
    let mut current = code.clone();

    // Run optimization loop until fixpoint
    for _ in 0..config.max_iterations {
        let before = current.clone();

        // Pass 1: Dead code elimination
        if config.enable_dce {
            current = dce::eliminate_dead_code_in_code(&current);
        }

        // Pass 2: Common subexpression elimination
        if config.enable_cse {
            current = cse::eliminate_common_subexpressions_in_code(&current);
        }

        // Pass 3: Constant folding
        if config.enable_constant_fold {
            current = constant_fold::fold_constants_in_code(&current);
        }

        // Pass 4: Value simplification
        if config.enable_simp_value {
            current = simp_value::simplify_values_in_code(&current);
        }

        // Pass 5: Function inlining
        if config.enable_inline {
            let inline_config = inline::InlineConfig {
                threshold: config.inline_threshold as usize,
                max_depth: 3,
            };
            current = inline::inline_functions_in_code(&current, &inline_config);
        }

        // Check for fixpoint
        if current == before {
            break;
        }
    }

    // Final pass: Convert eligible functions to join points
    if config.enable_join_points {
        current = join_points::find_join_points_in_code(&current);
    }

    current
}

/// Run all optimization passes with default configuration.
pub fn optimize_default(decl: &Decl) -> Decl {
    optimize(decl, &OptConfig::default())
}

/// Run all optimization passes on a batch of declarations.
///
/// This is the preferred entry point when optimizing multiple declarations
/// together, as it enables cross-declaration optimizations like function
/// specialization.
///
/// # Pipeline Order
///
/// ```text
/// ┌──────────────────────────────────────────────┐
/// │     LAMBDA LIFTING (all decls together)      │
/// │   Lifts local functions to top-level decls,  │
/// │   eliminates closures before optimization    │
/// └──────────────────────────────────────────────┘
///                        │
///                        ▼
/// ┌──────────────────────────────────────────────┐
/// │      SPECIALIZATION (all decls together)     │
/// │   Creates optimized function variants for    │
/// │   typeclass instances and ground arguments   │
/// └──────────────────────────────────────────────┘
///                        │
///                        ▼
/// ┌──────────────────────────────────────────────┐
/// │          PER-DECL OPTIMIZATION LOOP          │
/// │                                              │
/// │  DCE → CSE → ConstFold → SimpValue → Inline  │
/// │                                              │
/// └──────────────────────────────────────────────┘
///                        │
///                        ▼
///               FindJoinPoints (per-decl)
/// ```
pub fn optimize_all(decls: &[Decl], config: &OptConfig) -> Vec<Decl> {
    // Phase 0: Lambda lifting (operates on all decls, produces new top-level decls)
    // Runs first per Lean 4 ordering: lift local functions before optimization.
    let after_lift = if config.enable_lambda_lift {
        lambda_lift::lambda_lift_decls(decls, &lambda_lift::LiftConfig::default())
    } else {
        decls.to_vec()
    };

    // Phase 0b: Extract closed subexpressions to top-level declarations.
    let after_extract = if config.enable_extract_closed {
        extract_closed::extract_closed_decls(
            &after_lift,
            &extract_closed::ExtractClosedConfig::default(),
        )
    } else {
        after_lift
    };

    // Phase 1: Function specialization (operates on all decls)
    let after_spec = if config.enable_specialize {
        let spec_config = specialize::SpecConfig {
            specialize_instances: true,
            specialize_higher_order: false,
            max_depth: config.max_iterations,
        };
        specialize::specialize_all(&after_extract, &spec_config)
    } else {
        after_extract
    };

    // Phase 1b: Hoist typeclass instance bindings out of nested scopes.
    let after_pull_let = if config.enable_pull_let_decls {
        pull_let_decls::pull_let_decls_all(&after_spec)
    } else {
        after_spec
    };

    // Phase 2: Per-declaration optimization
    after_pull_let
        .iter()
        .map(|decl| optimize(decl, config))
        .collect()
}

/// Run all optimization passes on a batch with default configuration.
pub fn optimize_all_default(decls: &[Decl]) -> Vec<Decl> {
    optimize_all(decls, &OptConfig::default())
}

#[cfg(test)]
mod tests;
