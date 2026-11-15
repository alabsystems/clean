// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stable Rust check pipeline for clean (absorbed from the former
//! `clean-lib` crate; rearch stage 9 facade consolidation).
//!
//! This module provides a thin, `#[non_exhaustive]` surface over
//! `clean-kernel`, `clean-parser`, and `clean-elab` for downstream Rust
//! projects that verify Lean proofs programmatically in their `cargo test`
//! suites.
//!
//! The stable test-facing surface is `check_source` for one-shot checks and
//! `load_source_into` for callers that want to keep an `Environment` alive
//! across multiple file loads.
//!
//! # Quick Start
//!
//! ```rust,no_run
//! use clean::{check_file, CheckConfig};
//! use std::path::Path;
//!
//! let result = check_file(Path::new("proofs/MyTheorem.lean"), &CheckConfig::default())
//!     .expect("check should succeed");
//! assert!(result.errors.is_empty(), "no check errors");
//! assert_eq!(result.sorry_count, 0, "no sorry axioms");
//! ```
//!
//! # API Surface
//!
//! | Function | Input | Purpose |
//! |----------|-------|---------|
//! | [`check_file`] | filesystem path | Check a `.lean` file, return structured results |
//! | [`check_source`] | `&str` source code | Check Lean source from a string |
//! | [`load_file_into`] | path + `&mut Environment` | Load declarations into an existing environment |
//! | [`crate::EnvironmentExt::load_lean_source`] | `&mut Environment` + `&str` | Ergonomic incremental loading inside Rust tests |
//!
//! All public types are `#[non_exhaustive]` for semver safety. The main
//! entry points and result types are re-exported at the crate root
//! (`clean::check_source`, `clean::CheckConfig`, …).

use std::path::Path;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use clean_elab::{
    elaborate_decl_and_register_with_warning, kernel_check_failure_count,
    preprocess_decl_with_context, FileContext, RegistrationWarningKind,
};
use clean_kernel::sorry::{reset_sorry_counter, sorry_count};
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file_with_tactics;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from the check/load pipeline.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
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
pub type Result<T> = std::result::Result<T, Error>;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Options controlling the check pipeline.
///
/// Use [`Default::default()`] for the standard configuration.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct CheckConfig {
    /// When `true`, declarations using `sorry` are counted as passed.
    /// Useful for checking type signatures without requiring complete proofs.
    pub allow_sorry: bool,
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Outcome of checking a single declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct DeclResult {
    /// Fully qualified name of the declaration.
    pub name: String,
    /// Whether the declaration passed type checking.
    pub passed: bool,
    /// If the declaration failed, the reason.
    pub error: Option<String>,
    /// Trust warning, if any (sorry, trustedArith, trustedAy).
    pub warning: Option<DeclWarning>,
}

/// Classification of trust debt on a declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum DeclWarning {
    /// The declaration uses an explicit `sorry`.
    ExplicitSorry,
    /// The declaration uses a synthetic (recovery-inserted) `sorry`.
    SyntheticSorry,
    /// The declaration uses `trustedArith`.
    TrustedArith,
    /// The declaration uses `trustedAy`.
    TrustedAy,
}

impl DeclWarning {
    /// Returns `true` when this warning was caused by a `sorry`.
    #[must_use]
    pub fn is_sorry(&self) -> bool {
        matches!(self, Self::ExplicitSorry | Self::SyntheticSorry)
    }
}

/// Aggregate result of checking a file or source string.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CheckResult {
    /// Per-declaration outcomes.
    pub declarations: Vec<DeclResult>,

    /// Count of declarations that passed type checking.
    pub passed_count: usize,

    /// Declarations that failed type checking (name + error message).
    pub errors: Vec<(String, String)>,

    /// Checked declarations whose CONSTANT CLOSURE reaches `sorryAx` (or the
    /// legacy `sorry`) — in any position, behind any alias or lemma.
    ///
    /// Closure-derived since 2026-09-28: it used to be the elaborator's
    /// sorry-creation counter ([`Self::sorry_terms_minted`]), which never sees
    /// a sorry the source writes as a term, so `theorem bad : False :=
    /// @sorryAx False (!true)` checked with `sorry_count: 0`.
    pub sorry_count: u64,

    /// Sorry terms the elaborator created during the check (its own counter;
    /// counts a sorry minted for a declaration that then failed, too).
    pub sorry_terms_minted: u64,

    /// Number of kernel check failures.
    pub kernel_check_failures: u64,

    /// Passed declarations whose verdict rests on a DOMAIN axiom (neither
    /// foundational nor a trust marker), each with those axioms — the same
    /// disclosure `clean check` prints. Such a pass is valid under the axioms
    /// the source states, never unconditional, so a result with any is not
    /// [`Self::is_fully_verified`]. A user `axiom` is disclosed here and is
    /// NOT counted as a sorry.
    pub assumptions: Vec<(String, Vec<String>)>,

    /// Wall-clock duration of the check pipeline (parse + elaborate + typecheck).
    pub elapsed: Duration,
}

impl CheckResult {
    /// Number of declarations that failed the check pipeline.
    #[must_use]
    pub fn failed_count(&self) -> usize {
        self.declarations.iter().filter(|decl| !decl.passed).count()
    }

    /// Returns `true` when any declaration failed or a kernel check failed.
    #[must_use]
    pub fn has_failures(&self) -> bool {
        self.failed_count() > 0 || !self.errors.is_empty() || self.kernel_check_failures > 0
    }

    /// Number of declarations with trust warnings.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.declarations
            .iter()
            .filter(|decl| decl.warning.is_some())
            .count()
    }

    /// Returns `true` when any declaration carries trust debt metadata.
    #[must_use]
    pub fn has_warnings(&self) -> bool {
        self.warning_count() > 0
    }

    /// Returns `true` if all declarations passed with no trust debt — and at
    /// least one declaration was checked: a result that examined nothing has
    /// verified nothing (round-22 repair: a comment-only source reported
    /// `is_fully_verified() == true`).
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        !self.declarations.is_empty()
            && !self.has_failures()
            && !self.has_warnings()
            && self.sorry_count == 0
            && self.sorry_terms_minted == 0
            && self.assumptions.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Global lock — clean uses global counters (sorry, kernel-check) that are not
// reentrant. Serialize library calls to avoid data races.
// ---------------------------------------------------------------------------

pub(crate) fn global_lock() -> &'static Mutex<()> {
    static LOCK: std::sync::OnceLock<Mutex<()>> = std::sync::OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Check a Lean source file at `path`, returning structured results.
///
/// Creates a fresh [`Environment`] with the standard prelude, parses the file,
/// elaborates each declaration, and type-checks the result.
///
/// # Errors
///
/// Returns [`Error::Io`] if the file cannot be read, [`Error::Parse`] if parsing
/// fails, or [`Error::EnvInit`] if the prelude environment cannot be created.
#[must_use = "check result should be inspected"]
pub fn check_file(path: impl AsRef<Path>, config: &CheckConfig) -> Result<CheckResult> {
    let source = std::fs::read_to_string(path.as_ref())?;
    check_source(&source, config)
}

/// Check Lean source code from a string, returning structured results.
///
/// Creates a fresh [`Environment`] with the standard prelude, parses the source,
/// elaborates each declaration, and type-checks the result.
///
/// # Errors
///
/// Returns [`Error::Parse`] if parsing fails, or [`Error::EnvInit`] if the
/// prelude environment cannot be created.
#[must_use = "check result should be inspected"]
pub fn check_source(source: &str, config: &CheckConfig) -> Result<CheckResult> {
    let mut env = Environment::try_with_prelude().map_err(|e| Error::EnvInit(format!("{e}")))?;
    load_source_into(&mut env, source, config)
}

/// Parse and elaborate Lean source from a file, loading declarations into an
/// existing [`Environment`].
///
/// Unlike [`check_file`], this does not create a fresh environment — it appends
/// to `env`, which lets callers build up an environment incrementally across
/// multiple files.
///
/// # Errors
///
/// Returns [`Error::Io`] if the file cannot be read, or [`Error::Parse`] if
/// parsing fails.
#[must_use = "check result should be inspected"]
pub fn load_file_into(
    env: &mut Environment,
    path: impl AsRef<Path>,
    config: &CheckConfig,
) -> Result<CheckResult> {
    let source = std::fs::read_to_string(path.as_ref())?;
    load_source_into(env, &source, config)
}

/// Parse and elaborate Lean source from a string, loading declarations into an
/// existing [`Environment`].
///
/// This is the lowest-level entry point. Both [`check_file`] and
/// [`check_source`] delegate here.
///
/// # Errors
///
/// Returns [`Error::Parse`] if parsing fails.
#[must_use = "check result should be inspected"]
pub fn load_source_into(
    env: &mut Environment,
    source: &str,
    config: &CheckConfig,
) -> Result<CheckResult> {
    let _guard = global_lock()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    // Reset global counters for this check session.
    reset_sorry_counter();
    clean_elab::register::reset_kernel_check_counter();

    let start = Instant::now();

    // Parse
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(source, &patterns)?;

    // Elaborate + typecheck each declaration
    let mut file_ctx = FileContext::new();
    // Grown as declarations are checked, not pre-sized from `decls.len()`:
    // the Trust verified lane cannot bound a capacity read off a parsed
    // collection's length and refutes it as an unbounded bulk allocation
    // (`unbounded_allocation`, crates/clean/src/check.rs, measured
    // 2026-10-19 with trust/9192). A block flattens to several leaves, so the
    // length was never this vector's final size anyway.
    let mut declarations = Vec::new();
    let mut errors: Vec<(String, String)> = Vec::new();
    let mut passed_count: usize = 0;
    // One closure memo for the whole check: every leaf's trust verdict is read
    // off its constant closure (see `check_leaf`).
    let mut closure = clean_kernel::env::DomainAxiomClosure::new();
    let mut sorry_census: u64 = 0;
    let mut assumptions: Vec<(String, Vec<String>)> = Vec::new();

    for decl in &decls {
        let kernel_failures_before = kernel_check_failure_count();
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);

        match elaborate_decl_and_register_with_warning(env, &processed) {
            Ok(registered) => {
                // Flatten `namespace` / `section` / `mutual` blocks to their
                // declaration leaves, exactly as `clean check` does. This loop
                // used to name the whole block "(skipped)" and `continue`, so a
                // namespace holding `theorem bad : 1 = 2 := rfl` produced NO row,
                // no error, and a result with `has_failures() == false` — the
                // K5 vacuous pass, in the library API (round-22 repair).
                // A passing `#guard_msgs` is a checked unit too.
                let mut leaves: Vec<&clean_elab::ElabResult> = Vec::new();
                registered.result.checked_leaves(&mut leaves);
                // A block elaborates (and kernel-checks) every member inside
                // the call above, and each inner failure surfaces as its own
                // `Failed` leaf; sample the counter now so a block's failure is
                // not smeared onto a passing sibling.
                let kernel_before =
                    if matches!(registered.result, clean_elab::ElabResult::Multiple(_)) {
                        kernel_check_failure_count()
                    } else {
                        kernel_failures_before
                    };
                for leaf in leaves {
                    check_leaf(
                        env,
                        &mut closure,
                        leaf,
                        kernel_before,
                        config,
                        &mut declarations,
                        &mut errors,
                        &mut passed_count,
                        &mut sorry_census,
                        &mut assumptions,
                    );
                }
            }
            Err(e) => {
                let msg = format!("{e:?}");
                errors.push(("(elaboration)".to_string(), msg.clone()));
                declarations.push(DeclResult {
                    name: "(elaboration)".to_string(),
                    passed: false,
                    error: Some(msg),
                    warning: None,
                });
            }
        }
    }

    let final_sorry = sorry_count();
    let final_kernel_failures = kernel_check_failure_count();

    // Reset counters on exit to avoid leaking into subsequent calls.
    reset_sorry_counter();
    clean_elab::register::reset_kernel_check_counter();

    Ok(CheckResult {
        declarations,
        passed_count,
        errors,
        sorry_count: sorry_census,
        sorry_terms_minted: final_sorry,
        kernel_check_failures: final_kernel_failures,
        assumptions,
        elapsed: start.elapsed(),
    })
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Check, count and record ONE declaration leaf (a top-level result, or one
/// member of a flattened block).
#[allow(clippy::too_many_arguments)]
fn check_leaf(
    env: &Environment,
    closure: &mut clean_kernel::env::DomainAxiomClosure,
    leaf: &clean_elab::ElabResult,
    kernel_failures_before: u64,
    config: &CheckConfig,
    declarations: &mut Vec<DeclResult>,
    errors: &mut Vec<(String, String)>,
    passed_count: &mut usize,
    sorry_census: &mut u64,
    assumptions: &mut Vec<(String, Vec<String>)>,
) {
    // An inner declaration that already failed elaboration or its kernel
    // check: one failed row, never a pass, never skipped.
    if let clean_elab::ElabResult::Failed { name, error, .. } = leaf {
        let msg = error.to_string();
        errors.push((name.clone(), msg.clone()));
        declarations.push(DeclResult {
            name: name.clone(),
            passed: false,
            error: Some(msg),
            warning: None,
        });
        return;
    }
    let name = elab_result_name(leaf);
    if name == "(skipped)" {
        return;
    }
    let tc = TypeChecker::with_mode(env, env.mode());
    match typecheck_result(leaf, &tc, env) {
        Ok(()) => {
            let kernel_delta = kernel_check_failure_count().saturating_sub(kernel_failures_before);
            // By leaf, not by name: an `example` has no name to look up. The
            // verdict is the leaf's CONSTANT CLOSURE's: `sorryAx` anywhere in
            // it, whatever its arguments, behind any alias or lemma.
            let registration =
                clean_elab::register::registration_warning_for_leaf_in(closure, env, leaf);
            let via = registration
                .as_ref()
                .map(clean_elab::RegistrationWarning::via_suffix)
                .unwrap_or_default();
            let warning = registration.map(|w| match w.kind {
                RegistrationWarningKind::ExplicitSorry => DeclWarning::ExplicitSorry,
                RegistrationWarningKind::SyntheticSorry => DeclWarning::SyntheticSorry,
                RegistrationWarningKind::TrustedArith => DeclWarning::TrustedArith,
                RegistrationWarningKind::TrustedAy => DeclWarning::TrustedAy,
            });
            let has_sorry_warning = warning.as_ref().is_some_and(DeclWarning::is_sorry);
            if has_sorry_warning {
                *sorry_census = sorry_census.saturating_add(1);
            }
            if kernel_delta > 0 {
                errors.push((
                    name.clone(),
                    format!("kernel check failures: {kernel_delta}"),
                ));
                declarations.push(DeclResult {
                    name,
                    passed: false,
                    error: Some("kernel check failure".to_string()),
                    warning,
                });
            } else if has_sorry_warning && !config.allow_sorry {
                // sorry is a trust failure unless allow_sorry is set
                let msg = format!(
                    "uses {}{via}",
                    warning.as_ref().map_or("sorry", |w| match w {
                        DeclWarning::ExplicitSorry => "explicit sorry",
                        DeclWarning::SyntheticSorry => "synthetic sorry",
                        _ => "sorry",
                    })
                );
                errors.push((name.clone(), msg.clone()));
                declarations.push(DeclResult {
                    name,
                    passed: false,
                    error: Some(msg),
                    warning,
                });
            } else {
                *passed_count = passed_count.saturating_add(1);
                let assumed = clean_elab::register::leaf_domain_axioms(closure, env, leaf);
                if !assumed.is_empty() {
                    assumptions.push((
                        name.clone(),
                        // Unambiguous rendering: `«Eq.refl»` never reads as
                        // the kernel's `Eq.refl`.
                        assumed.iter().map(Name::to_unambiguous_string).collect(),
                    ));
                }
                declarations.push(DeclResult {
                    name,
                    passed: true,
                    error: None,
                    warning,
                });
            }
        }
        Err(e) => {
            errors.push((name.clone(), e.clone()));
            declarations.push(DeclResult {
                name,
                passed: false,
                error: Some(e),
                warning: None,
            });
        }
    }
}

/// Extract the declaration name from an elaboration result.
pub(crate) fn elab_result_name(result: &clean_elab::ElabResult) -> String {
    use clean_elab::ElabResult;
    match result {
        ElabResult::Diagnosed { result, .. } => elab_result_name(result),
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Structure { name, .. }
        | ElabResult::Instance { name, .. }
        | ElabResult::Inductive { name, .. } => name.to_string(),
        ElabResult::MutualInductive { decl, .. } => decl
            .types
            .first()
            .map_or_else(|| "(mutual inductive)".to_string(), |t| t.name.to_string()),
        ElabResult::Failed { name, .. } => name.clone(),
        // Anonymous by construction (Lean checks then discards it; lean4
        // `src/Lean/Elab/Declaration.lean`, `elabExample`) — but still ONE
        // genuinely checked declaration, so it must NOT be "(skipped)":
        // before B02 (GAP_SWEEP_2026-07-09) an example-only file reported
        // "Checked 0 declarations … 0 passed" with exit 0.
        ElabResult::Example { .. } => "example".to_string(),
        // A passing `#guard_msgs` that declared nothing: a checked assertion.
        ElabResult::Command(_) if result.is_checked_command() => "#guard_msgs".to_string(),
        ElabResult::Command(_) | ElabResult::Multiple(_) | ElabResult::Skipped => {
            "(skipped)".to_string()
        }
    }
}

/// Type-check an elaboration result against the environment.
///
/// This mirrors the logic in `clean-cli/src/cmd_core.rs::typecheck_elab_result`
/// but returns structured errors instead of printing to stdout.
fn typecheck_result(
    result: &clean_elab::ElabResult,
    tc: &TypeChecker<'_>,
    env: &Environment,
) -> std::result::Result<(), String> {
    use clean_elab::ElabResult;
    match result {
        ElabResult::Skipped | ElabResult::Command(_) | ElabResult::Multiple(_) => Ok(()),
        // A `Failed` inner decl already failed; never report it as a pass.
        ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
        ElabResult::Diagnosed {
            result: registered, ..
        } => {
            typecheck_result(registered, tc, env)?;
            Err(result
                .source_error_message()
                .unwrap_or_else(|| "invalid empty source diagnostic".to_string()))
        }
        ElabResult::Definition { ty, val, .. } | ElabResult::Instance { ty, val, .. } => {
            let _sort = tc
                .infer_sort(ty)
                .map_err(|e| format!("type check error on type: {e}"))?;
            tc.check_type(val, ty)
                .map_err(|e| format!("type check error on value: {e}"))?;
            Ok(())
        }
        ElabResult::Theorem { ty, proof, .. } => {
            let sort = tc
                .infer_sort(ty)
                .map_err(|e| format!("type check error on type: {e}"))?;
            if !sort.is_zero() {
                let name = elab_result_name(result);
                return Err(format!(
                    "{name}: type must be a Prop (Sort 0), got Sort {sort}"
                ));
            }
            tc.check_type(proof, ty)
                .map_err(|e| format!("type check error on proof: {e}"))?;
            Ok(())
        }
        // An `example` is an anonymous, discarded definition (B02; lean4
        // `src/Lean/Elab/Declaration.lean`, `elabExample`): re-check its
        // value against its type exactly like a `Definition`. The type may
        // live in any sort (`example : Nat := 3` is legal), so no Prop
        // restriction.
        ElabResult::Example { ty, val } => {
            let _sort = tc
                .infer_sort(ty)
                .map_err(|e| format!("type check error on type: {e}"))?;
            tc.check_type(val, ty)
                .map_err(|e| format!("type check error on value: {e}"))?;
            Ok(())
        }
        ElabResult::Axiom { ty, .. }
        | ElabResult::Opaque { ty, .. }
        | ElabResult::Structure { ty, .. } => {
            let _sort = tc
                .infer_sort(ty)
                .map_err(|e| format!("type check error: {e}"))?;
            Ok(())
        }
        ElabResult::Inductive { name, .. } => {
            // Inductive types are checked during registration; verify the
            // type constructor is present in the environment.
            if env
                .get_const(&Name::from_string(&name.to_string()))
                .is_none()
            {
                return Err(format!(
                    "inductive {name} not found in environment after registration"
                ));
            }
            Ok(())
        }
        ElabResult::MutualInductive { decl, .. } => {
            // The whole family is kernel-checked during registration; verify
            // every type in the family is present in the environment.
            for ind_ty in &decl.types {
                if env
                    .get_const(&Name::from_string(&ind_ty.name.to_string()))
                    .is_none()
                {
                    return Err(format!(
                        "mutual inductive {} not found in environment after registration",
                        ind_ty.name
                    ));
                }
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[path = "check_sorry_closure_tests.rs"]
mod check_sorry_closure_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::EnvironmentExt;

    #[test]
    fn test_check_source_trivial_def() {
        let source = "def foo : Nat := 0";
        let result = check_source(source, &CheckConfig::default()).expect("check should succeed");
        assert!(
            result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors
        );
        assert!(result.passed_count >= 1, "expected at least 1 passed decl");
    }

    #[test]
    fn test_check_source_elaboration_error() {
        // Reference an undefined name to trigger an elaboration error.
        let source = "def bad : Nat := nonexistent_name_xyz";
        let result = check_source(source, &CheckConfig::default())
            .expect("pipeline should not fail at parse/init stage");
        assert!(
            !result.errors.is_empty(),
            "expected elaboration errors for undefined reference, got 0 errors"
        );
    }

    #[test]
    fn test_error_variant_io() {
        let err = Error::Io(std::io::Error::new(std::io::ErrorKind::NotFound, "gone"));
        let msg = format!("{err}");
        assert!(msg.contains("gone"), "IO error message: {msg}");
    }

    #[test]
    fn test_check_source_sorry_rejected_by_default() {
        let source = "theorem oops : True := sorry";
        let result = check_source(source, &CheckConfig::default())
            .expect("check pipeline should succeed even with sorry");
        // sorry declarations should appear as errors unless allow_sorry
        assert!(
            !result.errors.is_empty() || result.sorry_count > 0,
            "sorry should produce an error or bump sorry_count"
        );
    }

    #[test]
    fn test_check_source_sorry_allowed() {
        let source = "theorem oops : True := sorry";
        let config = CheckConfig {
            allow_sorry: true,
            ..CheckConfig::default()
        };
        let result = check_source(source, &config).expect("check pipeline should succeed");
        // With allow_sorry, the declaration should pass.
        assert!(
            result.passed_count >= 1,
            "sorry should be allowed, but got errors: {:?}",
            result.errors
        );
    }

    #[test]
    fn test_check_result_is_fully_verified() {
        let result = CheckResult {
            declarations: vec![DeclResult {
                name: "ok".to_string(),
                passed: true,
                error: None,
                warning: None,
            }],
            passed_count: 1,
            errors: vec![],
            sorry_count: 0,
            sorry_terms_minted: 0,
            kernel_check_failures: 0,
            assumptions: Vec::new(),
            elapsed: Duration::ZERO,
        };
        assert!(result.is_fully_verified());
    }

    /// A result that checked nothing verified nothing (round-22 repair).
    #[test]
    fn test_check_result_that_checked_nothing_is_not_verified() {
        let result = CheckResult {
            declarations: vec![],
            passed_count: 0,
            errors: vec![],
            sorry_count: 0,
            sorry_terms_minted: 0,
            kernel_check_failures: 0,
            assumptions: Vec::new(),
            elapsed: Duration::ZERO,
        };
        assert!(!result.is_fully_verified());
        let result = check_source("-- only a comment\nopen Nat\n", &CheckConfig::default())
            .expect("check runs");
        assert!(result.declarations.is_empty());
        assert!(!result.is_fully_verified());
    }

    /// Round-22 repair: the library `check_source` named every block
    /// "(skipped)", so a failing or sorry-backed declaration inside a
    /// `namespace` / `section` produced no row and `has_failures() == false`.
    #[test]
    fn test_check_source_checks_every_block_member() {
        for (source, failing) in [
            (
                "namespace A\ntheorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := rfl\nend A\n",
                "A.bad",
            ),
            (
                "section S\ntheorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := rfl\nend S\n",
                "bad",
            ),
            (
                "namespace A\nnamespace B\nsection S\ntheorem good : 1 = 1 := rfl\n\
                 theorem bad : 1 = 2 := rfl\nend S\nend B\nend A\n",
                "A.B.bad",
            ),
            (
                "namespace A\ntheorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := sorry\nend A\n",
                "A.bad",
            ),
            (
                "namespace A\ntheorem good : 1 = 1 := rfl\nexample : 1 = 2 := sorry\nend A\n",
                "example",
            ),
        ] {
            let result = check_source(source, &CheckConfig::default()).expect("check runs");
            assert!(result.has_failures(), "{source}: must fail: {result:?}");
            assert!(!result.is_fully_verified(), "{source}");
            assert_eq!(result.declarations.len(), 2, "{source}: {result:?}");
            assert_eq!(result.passed_count, 1, "{source}: the good sibling passes");
            assert!(
                result
                    .declarations
                    .iter()
                    .any(|d| !d.passed && d.name == failing),
                "{source}: `{failing}` must be a failed row: {result:?}"
            );
        }
    }

    #[test]
    fn test_check_result_not_verified_with_sorry() {
        let result = CheckResult {
            declarations: vec![],
            passed_count: 1,
            errors: vec![],
            sorry_count: 1,
            sorry_terms_minted: 0,
            kernel_check_failures: 0,
            assumptions: Vec::new(),
            elapsed: Duration::ZERO,
        };
        assert!(!result.is_fully_verified());
    }

    #[test]
    fn test_check_result_not_verified_with_trust_warning() {
        let result = CheckResult {
            declarations: vec![DeclResult {
                name: "trusted".to_string(),
                passed: true,
                error: None,
                warning: Some(DeclWarning::TrustedArith),
            }],
            passed_count: 1,
            errors: vec![],
            sorry_count: 0,
            sorry_terms_minted: 0,
            kernel_check_failures: 0,
            assumptions: Vec::new(),
            elapsed: Duration::ZERO,
        };
        assert!(result.has_warnings());
        assert!(!result.is_fully_verified());
    }

    #[test]
    fn test_check_result_not_verified_with_kernel_check_failure() {
        let result = CheckResult {
            declarations: vec![DeclResult {
                name: "kernel".to_string(),
                passed: true,
                error: None,
                warning: None,
            }],
            passed_count: 1,
            errors: vec![],
            sorry_count: 0,
            sorry_terms_minted: 0,
            kernel_check_failures: 1,
            assumptions: Vec::new(),
            elapsed: Duration::ZERO,
        };
        assert!(result.has_failures());
        assert!(!result.is_fully_verified());
    }

    #[test]
    fn test_decl_warning_is_sorry() {
        assert!(DeclWarning::ExplicitSorry.is_sorry());
        assert!(DeclWarning::SyntheticSorry.is_sorry());
        assert!(!DeclWarning::TrustedArith.is_sorry());
        assert!(!DeclWarning::TrustedAy.is_sorry());
    }

    #[test]
    fn test_check_result_failure_and_warning_helpers() {
        let result = CheckResult {
            declarations: vec![
                DeclResult {
                    name: "clean".to_string(),
                    passed: true,
                    error: None,
                    warning: None,
                },
                DeclResult {
                    name: "warned".to_string(),
                    passed: true,
                    error: None,
                    warning: Some(DeclWarning::ExplicitSorry),
                },
                DeclResult {
                    name: "failed".to_string(),
                    passed: false,
                    error: Some("boom".to_string()),
                    warning: None,
                },
            ],
            passed_count: 2,
            errors: vec![("failed".to_string(), "boom".to_string())],
            sorry_count: 1,
            sorry_terms_minted: 0,
            kernel_check_failures: 0,
            assumptions: Vec::new(),
            elapsed: Duration::ZERO,
        };

        assert_eq!(result.failed_count(), 1);
        assert!(result.has_failures());
        assert_eq!(result.warning_count(), 1);
        assert!(result.has_warnings());
        assert!(!result.is_fully_verified());
    }

    #[test]
    fn test_check_config_default() {
        let config = CheckConfig::default();
        assert!(!config.allow_sorry);
    }

    #[test]
    fn test_load_source_into_incremental() {
        let mut env = Environment::try_with_prelude().expect("prelude should initialize");
        let config = CheckConfig::default();

        let result1 = load_source_into(&mut env, "def myNat : Nat := 42", &config)
            .expect("first load should succeed");
        assert!(
            result1.errors.is_empty(),
            "first load errors: {:?}",
            result1.errors
        );

        // The second load sees the first declaration in the environment.
        let result2 = load_source_into(&mut env, "def myNat2 : Nat := myNat", &config)
            .expect("second load should succeed");
        assert!(
            result2.errors.is_empty(),
            "second load errors: {:?}",
            result2.errors
        );
    }

    #[test]
    fn test_check_file_nonexistent() {
        let result = check_file(Path::new("/nonexistent/file.lean"), &CheckConfig::default());
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), Error::Io(_)));
    }

    #[test]
    fn test_check_file_with_tempfile() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("test.lean");
        std::fs::write(&file, "def hello : Nat := 1").expect("write");

        let result = check_file(&file, &CheckConfig::default()).expect("check should succeed");
        assert!(result.errors.is_empty());
        assert!(result.passed_count >= 1);
    }

    #[test]
    fn test_environment_ext_load_lean_source() {
        let mut env = Environment::try_with_prelude().expect("prelude should initialize");
        let result = env
            .load_lean_source("def extNat : Nat := 3", &CheckConfig::default())
            .expect("load should succeed");
        assert!(
            result.errors.is_empty(),
            "unexpected errors: {:?}",
            result.errors
        );
        assert!(
            result.passed_count >= 1,
            "expected at least one passed declaration"
        );
    }

    #[test]
    fn test_environment_ext_load_lean_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("ext.lean");
        std::fs::write(&file, "def extFileNat : Nat := 5").expect("write");

        let mut env = Environment::try_with_prelude().expect("prelude should initialize");
        let result = env
            .load_lean_file(&file, &CheckConfig::default())
            .expect("load should succeed");
        assert!(
            result.errors.is_empty(),
            "unexpected errors: {:?}",
            result.errors
        );
        assert!(
            result.passed_count >= 1,
            "expected at least one passed declaration"
        );
    }
}
