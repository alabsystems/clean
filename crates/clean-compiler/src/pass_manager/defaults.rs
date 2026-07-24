// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Default pipeline construction and built-in pass wrappers.
//!
//! Extracted from `mod.rs` to keep file sizes under 500 lines.

use super::validate::validate_decl;
use super::{Pass, PassError, PassManager, Phase};
use crate::lcnf::Decl;
use clean_kernel::Environment;

impl PassManager {
    /// Create a default pipeline with standard passes and default configs.
    ///
    /// The default pipeline includes:
    /// - **Base phase**: lambda_lifting, then to_mono (transitions to Mono)
    /// - **Mono phase**: optimize (DCE, CSE, constant fold, simp, inline, join points)
    /// - **Impure phase**: RC transformation (borrow inference, reset/reuse, RC insertion, expand)
    ///
    /// Lambda lifting runs first to convert local `Code::Fun` nodes into
    /// top-level declarations. Without this, `Code::Fun` nodes reaching IR
    /// lowering produce `CompilerError::UnexpectedLocalFunction`.
    ///
    /// Lambda lifting's auxiliary declarations are accumulated and fed
    /// through subsequent passes automatically.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use clean_compiler::pass_manager::PassManager;
    /// use clean_kernel::Environment;
    ///
    /// let manager = PassManager::default_pipeline();
    /// // let result = manager.run(&decl, &env)?;
    /// ```
    pub fn default_pipeline() -> Self {
        use crate::opt::OptConfig;
        use crate::rc::RCConfig;
        Self::default_pipeline_with_config(&OptConfig::default(), &RCConfig::default())
    }

    /// Create a pipeline with custom optimization and RC configurations.
    ///
    /// Same phases as [`default_pipeline`](Self::default_pipeline), but with
    /// caller-supplied configurations captured by the optimization and RC passes.
    pub fn default_pipeline_with_config(
        opt_config: &crate::opt::OptConfig,
        rc_config: &crate::rc::RCConfig,
    ) -> Self {
        let mut manager = Self::new();

        // Base phase: lambda lifting (eliminates Code::Fun nodes)
        manager.register(Pass::new("lambda_lifting", Phase::Base, lambda_lift_pass));

        // Base phase: monomorphization (transitions Base -> Mono)
        manager.register(Pass::with_transition(
            "to_mono",
            Phase::Base,
            Phase::Mono,
            to_mono_pass,
        ));

        // Mono phase: optimization (DCE, CSE, constant fold, simp, inline, join points)
        let opt_cfg = opt_config.clone();
        manager.register(Pass::new("optimize", Phase::Mono, move |decl, _env| {
            Ok(vec![crate::opt::optimize(decl, &opt_cfg)])
        }));

        // Mono->Impure phase: RC transformation (borrow -> reset/reuse -> RC insert -> expand)
        let rc_cfg = rc_config.clone();
        manager.register(Pass::with_transition(
            "rc",
            Phase::Mono,
            Phase::Impure,
            move |decl, _env| Ok(vec![crate::rc::transform_decl(decl, &rc_cfg)]),
        ));

        manager
    }

    /// Add a validation pass after every existing pass.
    ///
    /// Inserts an LCNF invariant checker between each pipeline stage. The
    /// checker verifies scope correctness, join point discipline, case
    /// completeness, and duplicate binding absence. If any invariant is
    /// violated, the validation pass returns a `PassError::ValidationError`.
    ///
    /// This is opt-in for development and debugging; production pipelines
    /// can skip validation for throughput.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use clean_compiler::pass_manager::PassManager;
    ///
    /// let manager = PassManager::default_pipeline().with_validation();
    /// ```
    #[must_use]
    pub fn with_validation(self) -> Self {
        let mut validated = Self::new();

        for pass in self
            .base_passes
            .iter()
            .chain(self.mono_passes.iter())
            .chain(self.impure_passes.iter())
        {
            validated.register(pass.clone());
            // Insert a validation pass in the same phase as the preceding pass.
            validated.register(Pass::new("validate", pass.phase_out, validate_pass));
        }

        validated
    }
}

/// Pass wrapper that validates LCNF invariants.
///
/// Returns the declaration unchanged if valid, or a `PassError::ValidationError`
/// describing all violations found.
fn validate_pass(decl: &Decl, _env: &Environment) -> Result<Vec<Decl>, PassError> {
    let errors = validate_decl(decl);
    if errors.is_empty() {
        Ok(vec![decl.clone()])
    } else {
        let msg = errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("; ");
        Err(PassError::ValidationError(format!(
            "LCNF validation failed for '{}': {}",
            decl.name, msg
        )))
    }
}

/// Pass wrapper for lambda lifting.
///
/// Transforms the declaration by removing `Code::Fun` nodes and replacing
/// them with references to lifted top-level functions. Returns the main
/// declaration followed by any auxiliary lifted declarations.
fn lambda_lift_pass(decl: &Decl, _env: &Environment) -> Result<Vec<Decl>, PassError> {
    let result = crate::opt::lambda_lift::lambda_lift_default(decl);
    let mut out = Vec::with_capacity(1 + result.lifted.len());
    out.push(result.decl);
    out.extend(result.lifted);
    Ok(out)
}

/// Pass wrapper for `to_mono` function.
///
/// Wraps `crate::to_mono::to_mono` to match the `PassFn` signature.
fn to_mono_pass(decl: &Decl, env: &Environment) -> Result<Vec<Decl>, PassError> {
    Ok(vec![crate::to_mono::to_mono(decl, env)])
}
