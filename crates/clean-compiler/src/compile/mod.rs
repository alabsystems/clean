// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified compile entrypoint for the clean compiler.
//!
//! Provides a single function to compile L5CNF declarations through the
//! full pipeline (monomorphization, optimization, RC, IR lowering, boxing)
//! with a configuration-driven interface.
//!
//!
//! Part of #1123.

use crate::boxing::BoxingConfig;
use crate::ir::IRDecl;
use crate::lcnf::Decl;
use crate::opt::OptConfig;
use crate::pass_manager::{compile_lcnf_decls, PipelineConfig, PipelineError};
use crate::rc::RCConfig;
use clean_kernel::Environment;

/// Optimization level for the compilation pipeline.
///
/// Controls the aggressiveness of optimization passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub enum OptLevel {
    /// No optimizations. Monomorphization and RC only.
    None,
    /// Basic optimizations: DCE, constant folding, value simplification.
    Basic,
    /// Full optimizations: all passes including inlining, CSE, specialization.
    #[default]
    Full,
}

impl std::fmt::Display for OptLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OptLevel::None => write!(f, "none"),
            OptLevel::Basic => write!(f, "basic"),
            OptLevel::Full => write!(f, "full"),
        }
    }
}

/// Configuration for the unified compilation pipeline.
///
/// Controls which passes are enabled, their aggressiveness, and whether
/// diagnostic trace output is collected.
#[derive(Debug, Clone)]
pub struct CompileConfig {
    /// Optimization level (controls which optimization passes run).
    pub optimization_level: OptLevel,
    /// Enable explicit boxing pass in the IR pipeline.
    pub enable_boxing: bool,
    /// Enable lambda lifting before optimization.
    pub enable_lambda_lift: bool,
    /// Collect diagnostic trace messages during compilation.
    pub debug_trace: bool,
}

impl Default for CompileConfig {
    fn default() -> Self {
        Self {
            optimization_level: OptLevel::Full,
            enable_boxing: true,
            enable_lambda_lift: true,
            debug_trace: false,
        }
    }
}

/// Result of a unified compilation run.
///
/// Contains the final IR declarations, metadata about which passes
/// were executed, and any diagnostic messages collected.
#[derive(Debug, Clone)]
pub struct CompileResult {
    /// Final IR declarations after the full pipeline.
    pub decls: Vec<IRDecl>,
    /// Names of passes that were executed, in order.
    pub passes_run: Vec<String>,
    /// Diagnostic messages (warnings, trace output).
    pub diagnostics: Vec<String>,
}

/// Compile L5CNF declarations through the full pipeline.
///
/// Runs monomorphization, optimization, RC transformation, IR lowering,
/// and boxing based on the provided configuration.
///
/// # Errors
///
/// Returns `PipelineError` if any pipeline stage fails (type errors,
/// IR lowering failures, pass errors).
pub fn compile(
    decls: &[Decl],
    env: &Environment,
    config: &CompileConfig,
) -> Result<CompileResult, PipelineError> {
    let mut passes_run = Vec::new();
    let mut diagnostics = Vec::new();

    let pipeline_config = build_pipeline_config(config, &mut passes_run, &mut diagnostics);
    let artifacts = compile_lcnf_decls(decls, env, &pipeline_config)?;

    diagnostics.extend(artifacts.warnings.iter().cloned());

    let output_decls = if config.enable_boxing {
        passes_run.push("explicit_boxing".to_owned());
        if config.debug_trace {
            diagnostics.push(format!(
                "boxing: {} IR decls -> {} boxed IR decls",
                artifacts.ir_decls.len(),
                artifacts.boxed_ir_decls.len(),
            ));
        }
        artifacts.boxed_ir_decls
    } else {
        artifacts.ir_decls
    };

    Ok(CompileResult {
        decls: output_decls,
        passes_run,
        diagnostics,
    })
}

/// Compile with the default configuration (full optimization, boxing enabled).
///
/// Convenience wrapper around [`compile`] with [`CompileConfig::default()`].
///
/// # Errors
///
/// Returns `PipelineError` if any pipeline stage fails.
pub fn compile_default(decls: &[Decl], env: &Environment) -> Result<CompileResult, PipelineError> {
    compile(decls, env, &CompileConfig::default())
}

/// Build a `PipelineConfig` from a `CompileConfig`, recording pass names.
fn build_pipeline_config(
    config: &CompileConfig,
    passes_run: &mut Vec<String>,
    diagnostics: &mut Vec<String>,
) -> PipelineConfig {
    let opt = build_opt_config(config, passes_run, diagnostics);
    let rc = RCConfig::default();
    let boxing = if config.enable_boxing {
        BoxingConfig::default()
    } else {
        BoxingConfig {
            optimize_expensive_constants: false,
            generate_boxed_versions: false,
        }
    };

    passes_run.push("to_mono".to_owned());
    passes_run.push("rc".to_owned());
    passes_run.push("to_ir".to_owned());

    if config.debug_trace {
        diagnostics.push(format!("optimization_level: {}", config.optimization_level));
        diagnostics.push(format!("enable_boxing: {}", config.enable_boxing));
        diagnostics.push(format!("enable_lambda_lift: {}", config.enable_lambda_lift));
    }

    PipelineConfig { opt, rc, boxing }
}

/// Build an `OptConfig` from the compile configuration's optimization level.
fn build_opt_config(
    config: &CompileConfig,
    passes_run: &mut Vec<String>,
    diagnostics: &mut Vec<String>,
) -> OptConfig {
    if config.enable_lambda_lift {
        passes_run.push("lambda_lifting".to_owned());
    }

    match config.optimization_level {
        OptLevel::None => {
            if config.debug_trace {
                diagnostics.push("optimization: disabled".to_owned());
            }
            OptConfig {
                enable_lambda_lift: config.enable_lambda_lift,
                ..OptConfig::minimal()
            }
        }
        OptLevel::Basic => {
            passes_run.extend(
                ["dce", "constant_fold", "simp_value"]
                    .iter()
                    .map(|&s| s.to_owned()),
            );
            if config.debug_trace {
                diagnostics.push("optimization: basic (DCE + const fold + simp)".to_owned());
            }
            OptConfig {
                max_iterations: 3,
                inline_threshold: 0,
                enable_cse: false,
                enable_constant_fold: true,
                enable_simp_value: true,
                enable_dce: true,
                enable_inline: false,
                enable_join_points: true,
                enable_specialize: false,
                enable_lambda_lift: config.enable_lambda_lift,
                enable_extract_closed: false,
                enable_pull_let_decls: false,
            }
        }
        OptLevel::Full => {
            passes_run.push("optimize".to_owned());
            if config.debug_trace {
                diagnostics.push("optimization: full (all passes)".to_owned());
            }
            OptConfig {
                enable_lambda_lift: config.enable_lambda_lift,
                ..OptConfig::default()
            }
        }
    }
}

#[cfg(test)]
mod tests;
