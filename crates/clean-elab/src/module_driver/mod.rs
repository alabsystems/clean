// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One elaboration driver for a Lean module: the per-declaration loop that
//! `clean check` and the LSP run. `clean lake build` runs the same
//! per-declaration pipeline in a loop of its own (`BuildContext::elaborate_module`)
//! and re-validates nothing read-only; routing it here adds that pass per
//! declaration, so it moves with its own measurement. Other commands
//! (`clean project check`, `clean export-cert`, `clean compile`, `clean audit`,
//! the REPL, and the `clean` crate's `check_file`) still keep loops of their
//! own.
//!
//! # Why this exists
//!
//! Until this module, three frontends elaborated a file three ways, and they
//! disagreed on the same input. `clean check` threaded a
//! [`FileContext`](crate::FileContext) through every declaration, flattened
//! `namespace`/`section`/`mutual` blocks to per-declaration verdicts and kept
//! going past a failure. `clean lake build` built a FRESH `ElabCtx` for every
//! surface declaration and aborted the module on the first error, so no
//! `namespace`, `section` or `variable` state survived from one declaration to
//! the next. Measured by the 2026-09-24 dev-surface audit
//! (`reports/lean4-replacement-audit-2026-09-24/dev_surface.json`): the
//! three-line module `namespace A / def x : Nat := 1 / def y : Nat := x + 1`
//! that `clean check` and pinned Lean both accept failed `clean lake build`
//! with `Unknown identifier: x`, and every frontend fix since had reached only
//! `clean check`. The LSP elaborated each declaration context-free as well.
//!
//! # The shape
//!
//! A frontend composes the steps it needs, and every step is the one
//! `clean check` runs:
//!
//! 1. [`module_environment`] — the environment `clean check` checks against.
//! 2. [`parse_module`] — the notation-seeded, recovery-reporting parse.
//! 3. [`module_file_context`] — a [`FileContext`](crate::FileContext) carrying
//!    the file's Lake `.olean` search paths.
//! 4. The frontend's own import resolution — `clean check` elaborates
//!    intra-project imports from source first, the LSP preloads the whole
//!    header.
//! 5. [`elaborate_decls`] — for each declaration: refill the per-declaration
//!    budget, preprocess against the `FileContext`, elaborate and register,
//!    flatten blocks to leaves, re-validate every leaf read-only
//!    ([`validate_decl_read_only`]) and classify it into a [`DeclVerdict`].
//!
//! The frontend observes step 5 through [`ModuleObserver`]. What every
//! frontend shares is the [`LeafOutcome`] of each leaf: the elaboration, the
//! block flattening and the read-only re-validation are the driver's, so no
//! frontend can elaborate or re-check a declaration differently. What a
//! frontend MAKES of an outcome is its own:
//!
//! - The returned [`ModuleReport`] classifies every outcome with
//!   `LeafOutcome::verdict_kind`, the driver's one classifier. No production
//!   frontend reads it today; the driver's tests and `clean check`'s agreement
//!   test (`cmd_core_driver_tests`) do.
//! - `clean check` renders its report rows in its observer
//!   (`crates/clean-cli/src/cmd_core/check_observer.rs`) under its own policy:
//!   `record_checked_decl` with `--allow-sorry`, the imported-cone credit gate,
//!   a trust-debt census through its run-wide closure memo
//!   ([`ModuleObserver::leaf_warning`]) and the process-wide kernel-failure
//!   counter ([`ModuleObserver::kernel_failure_count`]).
//! - The LSP turns failed, rejected and kernel-failing leaves into diagnostics
//!   in its observer.
//!
//! `clean check`'s classification and the driver's agree on the fixture that
//! test pins; nothing else holds them together.

mod drive;
mod setup;
mod source_modules;
mod surface;
mod validation;
mod verdict;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod prelude_census_tests;

pub use drive::{elaborate_decls, ModuleObserver};
pub use setup::{
    elaborate_prelude_header, module_elaboration_lock, module_environment,
    module_environment_for_header_in_world, module_environment_in_world,
    module_environment_with_import_base_in_world, module_file_context,
    module_file_context_in_world, parse_module, parse_module_in_world, DeclBudgetScope,
    EnvironmentSetup, ImportArtifacts, ModuleSetupError, PreludeFlavor,
};
pub use source_modules::{source_closure_needs_world_setup, SourceModuleError, SourceModuleSetup};
pub use surface::{
    line_column_for_offset, registration_warning_label, source_span, surface_decl_name,
    surface_decl_span, surface_name_label,
};
pub use validation::validate_decl_read_only;
pub use verdict::{
    BudgetReading, DeclVerdict, DriverOptions, FailureIsolation, ImportHandling, LeafOutcome,
    ModuleReport, VerdictKind,
};
