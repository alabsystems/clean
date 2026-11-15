// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What the driver decides about each declaration, and the one classifier that
//! decides it.

use super::validation::validate_decl_read_only;
use crate::{ElabError, ElabResult, RegistrationWarning, RegistrationWarningKind};
use clean_kernel::{Environment, TypeChecker};
use clean_parser::SurfaceDecl;

/// The verdict on one checked declaration.
///
/// Three-way at heart — passed, failed, did not finish — with the pass split by
/// trust debt and the failure split by where it was caught, because the
/// frontends treat those differently: `clean check` counts trust debt as a
/// failure unless `--allow-sorry` admits a `sorry`, while `lake build`, like
/// Lean's, builds past an explicit `sorry` with a warning.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerdictKind {
    /// Elaborated, registered, re-validated read-only, and free of trust debt.
    Passed,
    /// Registered and re-validated, but it depends on a trust marker.
    TrustDebt(RegistrationWarningKind),
    /// Registered and re-validated, but the kernel rejected a check while it
    /// was being elaborated (the kernel-failure counter moved on this thread).
    KernelCheckFailed,
    /// Registered, but the read-only re-validation rejected it.
    ValidationFailed,
    /// Did not elaborate.
    ElaborationFailed,
    /// Registered and kernel-validated, but source processing reported errors.
    SourceError,
    /// Spent the whole per-declaration budget: no verdict at all — neither a
    /// pass (nothing was proved) nor a refutation (nothing was refuted).
    Diverged,
}

impl VerdictKind {
    /// Refuted, or not finished: never a pass under any policy. Trust debt is
    /// NOT a failure here; whether it fails is the frontend's policy.
    #[must_use]
    pub fn is_failure(&self) -> bool {
        matches!(
            self,
            Self::KernelCheckFailed
                | Self::SourceError
                | Self::ValidationFailed
                | Self::ElaborationFailed
                | Self::Diverged
        )
    }
}

/// One declaration's verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclVerdict {
    /// The declaration's name, namespace-qualified where the elaborator
    /// qualified it.
    pub name: String,
    /// The verdict.
    pub kind: VerdictKind,
    /// The 1-based line of the declaration (of the enclosing block for a
    /// member that passed), when it can be located.
    pub line: Option<u32>,
    /// What went wrong, for anything but a clean pass.
    pub detail: Option<String>,
}

/// Every verdict of one module, in source order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ModuleReport {
    /// One entry per counted declaration. Administrative commands (`import`,
    /// `open`, `set_option`, …) that succeed are not declarations and get none.
    pub verdicts: Vec<DeclVerdict>,
    /// The most ambient kernel ticks any one declaration spent.
    pub peak_decl_ticks: u64,
}

/// How [`elaborate_decls`](super::elaborate_decls) treats `import`
/// declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ImportHandling {
    /// Elaborate each `import` through the `FileContext` like any declaration
    /// (`clean check`).
    #[default]
    Elaborate,
    /// The caller already loaded the file's whole import header into the
    /// environment (the LSP's shared import closure); `import` declarations are
    /// skipped outright and get no verdict.
    Preloaded,
}

/// What a declaration that fails to elaborate leaves behind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum FailureIsolation {
    /// Keep the environment as the failed attempt left it (`clean check`).
    #[default]
    Keep,
    /// Restore the environment to its state before the declaration, so a
    /// failed registration leaks no partial state (the LSP's contract). A
    /// failed `deriving` class is not a failed declaration: Lean declares the
    /// type before it runs the handlers, so the type registers and passes and
    /// the class is its own failed leaf (`crate::infer::deriving_log`), with
    /// nothing to restore, as under `Keep`.
    Rollback,
}

/// Knobs of the per-declaration loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct DriverOptions {
    /// How `import` declarations are treated.
    pub imports: ImportHandling,
    /// What a failed declaration leaves behind.
    pub isolation: FailureIsolation,
    /// Apply Lean's safe-context and source-compilation policy. A safe
    /// declaration may not use unsafe constants; an executable definition
    /// receives a source error when a relevant dependency has no code.
    /// Enabled by check, lean, and LSP frontends. Pure logical clients may
    /// leave it disabled: a kernel-valid definition need not be executable.
    pub lean_front_door: bool,
}

/// The ambient budget after one declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BudgetReading {
    /// Ticks the declaration spent (`0` when no budget is armed).
    pub spent: u64,
    /// Whether it spent the whole budget.
    pub exhausted: bool,
    /// The configured per-declaration limit (`0` = unlimited).
    pub limit: u64,
}

/// What happened to one leaf of a registered declaration.
#[derive(Debug)]
#[non_exhaustive]
pub enum LeafOutcome<'a> {
    /// A member of a `namespace`/`section`/`mutual` block that failed to
    /// elaborate or to kernel-check; it carries its own surface declaration.
    Failed {
        /// Best-effort qualified name.
        name: &'a str,
        /// The member's own surface declaration.
        decl: &'a SurfaceDecl,
        /// Why it failed.
        error: &'a ElabError,
    },
    /// Registered and re-validated read-only. `name` is `"(skipped)"` for an
    /// administrative result.
    Checked {
        /// The declaration name.
        name: String,
        /// The leaf itself (the whole registered result for an administrative
        /// one), for a frontend that credits it further.
        leaf: &'a ElabResult,
        /// Its trust debt, if any.
        warning: Option<RegistrationWarning>,
        /// How far the observer's kernel-failure counter moved across it
        /// ([`ModuleObserver::kernel_failure_count`](super::ModuleObserver::kernel_failure_count):
        /// this thread's by default, the process-wide one for `clean check`).
        kernel_failures_delta: u64,
        /// Errors beside a genuine registered and validated declaration.
        source_diagnostics: &'a [crate::source_diagnostics::SourceDiagnostic],
    },
    /// Registered, but the read-only re-validation rejected it.
    ValidationFailed {
        /// The declaration name.
        name: String,
        /// The validator's message.
        message: String,
    },
}

impl LeafOutcome<'_> {
    /// THE classifier. `None` is an administrative result `clean check` does
    /// not count (an `import`, `open`, `set_option`, … that raised nothing).
    ///
    /// Order matters and is `clean check`'s: trust debt first (a `sorry` is
    /// reported as such even if the kernel also complained), then a kernel
    /// failure, then the administrative exemption — which is deliberately NOT
    /// applied to the first two, because `"(skipped)"` also names a whole
    /// mutual block whose `sorry` is real.
    #[must_use]
    pub(crate) fn verdict_kind(&self) -> Option<VerdictKind> {
        match self {
            Self::Failed { .. } => Some(VerdictKind::ElaborationFailed),
            Self::ValidationFailed { .. } => Some(VerdictKind::ValidationFailed),
            Self::Checked {
                name,
                warning,
                kernel_failures_delta,
                source_diagnostics,
                ..
            } => {
                if !source_diagnostics.is_empty() {
                    Some(VerdictKind::SourceError)
                } else if let Some(warning) = warning {
                    Some(VerdictKind::TrustDebt(warning.kind.clone()))
                } else if *kernel_failures_delta > 0 {
                    Some(VerdictKind::KernelCheckFailed)
                } else if name == "(skipped)" {
                    None
                } else {
                    Some(VerdictKind::Passed)
                }
            }
        }
    }
}

/// Re-validate one registered result read-only and name it, or say why it is
/// not valid. Administrative results (`Skipped`, `Command`, `Multiple`) are
/// `"(skipped)"`; a `Failed` leaf is never a pass.
pub(crate) fn typecheck_elab_result(
    result: &ElabResult,
    env: &Environment,
) -> Result<String, String> {
    if let ElabResult::Diagnosed {
        result,
        diagnostics,
    } = result
    {
        typecheck_elab_result(result, env)?;
        return Err(diagnostics
            .iter()
            .map(|d| d.error.to_string())
            .collect::<Vec<_>>()
            .join("\n"));
    }
    if let ElabResult::Failed { name, error, .. } = result {
        return Err(format!("{name}: {error}"));
    }
    // The driver flattens every block before it gets here; a block that still
    // holds declarations is refused loudly rather than answered "(skipped)",
    // which would check none of them.
    if let ElabResult::Multiple(_) = result {
        let mut leaves: Vec<&ElabResult> = Vec::new();
        result.leaf_decls(&mut leaves);
        if !leaves.is_empty() {
            return Err(format!(
                "internal: a namespace/section/mutual block holding {} declaration(s) reached \
                 the single-declaration checker unflattened; it must be flattened with \
                 `leaf_decls` so every member is checked",
                leaves.len()
            ));
        }
    }
    // A passing `#guard_msgs` that declared nothing: its check (a message
    // comparison) already ran, and there is no term to re-validate.
    if result.is_checked_command() {
        return Ok("#guard_msgs".to_string());
    }
    if matches!(
        result,
        ElabResult::Skipped | ElabResult::Command(_) | ElabResult::Multiple(_)
    ) {
        return Ok("(skipped)".to_string());
    }
    let tc = TypeChecker::with_mode(env, env.mode());
    validate_decl_read_only(env, &tc, result).map(|_| elab_result_name(result))
}

/// The name `clean check` reports for an elaboration result.
#[must_use]
pub(crate) fn elab_result_name(result: &ElabResult) -> String {
    match result {
        ElabResult::Diagnosed { result, .. } => elab_result_name(result),
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Structure { name, .. }
        | ElabResult::Instance { name, .. }
        | ElabResult::Inductive { name, .. } => {
            // A private declaration is reported by its user-facing name
            // (`helper`, not `_private.Pkg.A.0.helper`), as Lean's messages
            // name it (G21).
            crate::private_names::user_facing_name(name).to_string()
        }
        // Anonymous by construction (Lean checks then discards it); it is
        // still ONE genuinely checked declaration and must be counted (B02).
        ElabResult::Example { .. } => "example".to_string(),
        ElabResult::MutualInductive { decl, .. } => decl
            .types
            .first()
            .map_or_else(|| "(mutual inductive)".to_string(), |t| t.name.to_string()),
        // A failing inner decl carries its own best-effort name.
        ElabResult::Failed { name, .. } => name.clone(),
        ElabResult::Command(_) | ElabResult::Multiple(_) | ElabResult::Skipped => {
            "(skipped)".to_string()
        }
    }
}
