// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check`'s view of [`clean_elab::module_driver::elaborate_decls`].
//!
//! The per-declaration loop is the driver's — the one the LSP runs — and this
//! observer renders what `clean check` has always reported off it: the
//! `errors` / `trust_failures` / `kernel_failures` / `assumptions` rows, the
//! imported-cone credit gate, the budget rollback to `diverged`, the per-phase
//! timing and the early stop after a refused `import`. The driver's own
//! [`ModuleReport`](clean_elab::module_driver::ModuleReport) verdicts are not
//! read: `clean check`'s policy (`--allow-sorry`, the credit gate) is applied
//! here, to the same [`LeafOutcome`]s the driver's classifier sees.

use super::{
    bind_loaded_imports, check_feedback_from_elab_error, check_feedback_from_message,
    elaboration_error_diagnostic, record_checked_decl, source_span, surface_decl_name,
    surface_decl_span, CheckFailureReason, ElabOutcome, FileCheckOutcome, ImportCheckState,
    OutcomeMark,
};
use clean_elab::module_driver::{BudgetReading, LeafOutcome, ModuleObserver};
use clean_elab::{
    kernel_check_failure_count, ElabError, ElabResult, FileContext, RegisteredElabResult,
    RegistrationWarning, RegistrationWarningKind,
};
use clean_kernel::{Environment, Name};
use clean_parser::SurfaceDecl;
use std::io::Write;
use std::time::Instant;

#[cfg(test)]
mod tests;

/// Everything one file's `clean check` accumulates while the driver runs.
pub(super) struct CheckObserver<'a> {
    pub(super) state: &'a mut ImportCheckState,
    pub(super) outcome: &'a mut FileCheckOutcome,
    pub(super) content: &'a str,
    pub(super) module: &'a str,
    pub(super) is_entry_file: bool,
    pub(super) verbose: bool,
    pub(super) allow_sorry: bool,
    pub(super) json: bool,
    pub(super) budget_trace: bool,
    /// Leaf declarations counted so far, nested block members included.
    pub(super) counted_leaf_decls: usize,
    /// One entry per top-level declaration, for the sibling-import comparison.
    pub(super) elab_outcomes: Vec<ElabOutcome>,
    /// Set when nothing more in this file may be checked (an `import` failed
    /// or loaded an artifact that is not the build of its source).
    pub(super) stopped: bool,
    pub(super) body_environment: Option<Environment>,
    decl_start: Option<Instant>,
    mark: Option<OutcomeMark>,
}

impl<'a> CheckObserver<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        state: &'a mut ImportCheckState,
        outcome: &'a mut FileCheckOutcome,
        content: &'a str,
        module: &'a str,
        is_entry_file: bool,
        verbose: bool,
        allow_sorry: bool,
        json: bool,
        budget_trace: bool,
    ) -> Self {
        Self {
            state,
            outcome,
            content,
            module,
            is_entry_file,
            verbose,
            allow_sorry,
            json,
            budget_trace,
            counted_leaf_decls: 0,
            elab_outcomes: Vec::new(),
            stopped: false,
            body_environment: None,
            decl_start: None,
            mark: None,
        }
    }

    /// A top-level declaration failed to elaborate: one checked unit, with its
    /// name and start line in the diagnostic so downstream verdict consumers
    /// (the tactic-family gates' fail-closed attribution) attribute it
    /// positionally instead of by a whole-word name scan — which a goal dump
    /// mentioning an unrelated declaration poisons into a false failure.
    fn record_elaboration_failure(&mut self, decl: &SurfaceDecl, error: &ElabError) {
        let named = surface_decl_name(decl)
            .map(|name| format!("{name}: "))
            .unwrap_or_default();
        let position = surface_decl_span(decl)
            .and_then(|span| source_span(self.content, span))
            .map(|span| format!(" at line {}", span.line))
            .unwrap_or_default();
        let diagnostic =
            elaboration_error_diagnostic(self.is_entry_file, self.module, &named, &position, error);
        self.outcome
            .structured_failures
            .push(check_feedback_from_elab_error(
                decl,
                self.content,
                self.module,
                error,
                diagnostic.clone(),
            ));
        self.outcome.errors.push(diagnostic);
        self.counted_leaf_decls += 1;
    }

    /// The declaration spent the whole budget: everything it recorded is
    /// replaced by one `diverged` row (see [`OutcomeMark::rollback_as_diverged`]).
    fn rollback_diverged(&mut self, decl: &SurfaceDecl, budget: &BudgetReading) {
        let named = surface_decl_name(decl).unwrap_or_else(|| "(anonymous)".to_owned());
        let position = surface_decl_span(decl)
            .and_then(|span| source_span(self.content, span))
            .map(|span| format!(" at line {}", span.line))
            .unwrap_or_default();
        let limit = budget.limit;
        let module = self.module;
        let row = if self.is_entry_file {
            format!(
                "{named}: did not finish{position} — spent the whole \
                 per-declaration budget of {limit} kernel operations \
                 (raise it with --decl-budget <n>, or 0 for unlimited)"
            )
        } else {
            format!(
                "[{module}] {named}: did not finish{position} — spent the \
                 whole per-declaration budget of {limit} kernel operations \
                 (raise it with --decl-budget <n>, or 0 for unlimited)"
            )
        };
        match self.mark.take() {
            Some(mark) => {
                mark.rollback_as_diverged(self.outcome, &mut self.counted_leaf_decls, row);
            }
            // FAIL CLOSED. No mark means `before_decl` never ran for this
            // declaration (the driver calls it for every declaration it
            // elaborates, so this is an internal error). What the declaration
            // recorded cannot be told apart from its predecessors' rows, so
            // nothing is rolled back; the `diverged` row is still recorded and
            // the missing mark is reported, so an apparent pass off an
            // exhausted budget can never stand alone.
            None => {
                let internal = format!(
                    "internal: {named} spent its budget with no outcome mark, so what it \
                     recorded was not rolled back"
                );
                self.outcome.errors.push(if self.is_entry_file {
                    internal
                } else {
                    format!("[{module}] {internal}")
                });
                self.outcome.diverged.push(row);
            }
        }
    }

    /// Record one re-validated leaf. Administrative `(skipped)` results are not
    /// counted.
    fn record_leaf(&mut self, env: &Environment, decl: &SurfaceDecl, leaf: &LeafOutcome<'_>) {
        let module = self.module;
        match leaf {
            // A member of a namespace / section / mutual block whose
            // elaboration or kernel check failed: a counted, reported failure,
            // exactly as a top-level failure. Never registered, never a pass.
            LeafOutcome::Failed {
                name,
                decl: inner_decl,
                error,
            } => {
                let position = surface_decl_span(inner_decl)
                    .and_then(|span| source_span(self.content, span))
                    .map(|span| format!(" at line {}", span.line))
                    .unwrap_or_default();
                let diagnostic = elaboration_error_diagnostic(
                    self.is_entry_file,
                    module,
                    &format!("{name}: "),
                    &position,
                    error,
                );
                self.outcome.errors.push(diagnostic.clone());
                // The member's own surface decl, so the structured failure
                // carries its own span/diagnostics.
                self.outcome
                    .structured_failures
                    .push(check_feedback_from_elab_error(
                        inner_decl,
                        self.content,
                        module,
                        error,
                        diagnostic,
                    ));
                self.counted_leaf_decls += 1;
            }
            LeafOutcome::ValidationFailed { name, message } => {
                let diagnostic = if self.is_entry_file {
                    format!("{name}: {message}")
                } else {
                    format!("[{module}] {name}: {message}")
                };
                self.outcome.errors.push(diagnostic.clone());
                self.outcome
                    .structured_failures
                    .push(check_feedback_from_message(
                        decl,
                        self.content,
                        module,
                        CheckFailureReason::KernelValidation,
                        diagnostic,
                    ));
                self.counted_leaf_decls += 1;
            }
            LeafOutcome::Checked {
                name,
                leaf,
                warning,
                kernel_failures_delta,
                source_diagnostics,
            } => self.record_checked_leaf(
                env,
                name,
                leaf,
                warning.as_ref(),
                *kernel_failures_delta,
                source_diagnostics,
                decl,
            ),
            // `LeafOutcome` is non-exhaustive: an outcome this checker does not
            // know is a failure, never a pass.
            other => {
                let diagnostic = format!("internal: unclassified leaf outcome {other:?}");
                self.outcome.errors.push(if self.is_entry_file {
                    diagnostic
                } else {
                    format!("[{module}] {diagnostic}")
                });
                self.counted_leaf_decls += 1;
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn record_checked_leaf(
        &mut self,
        env: &Environment,
        name: &str,
        leaf: &ElabResult,
        warning: Option<&RegistrationWarning>,
        kernel_failures_delta: u64,
        source_diagnostics: &[clean_elab::source_diagnostics::SourceDiagnostic],
        decl: &SurfaceDecl,
    ) {
        let module = self.module;
        let mut trust_failures = Vec::new();
        let mut kernel_failures = Vec::new();
        let mut success_count = 0;
        if name != "(skipped)" {
            self.counted_leaf_decls += 1;
        }
        // The `sorry_axioms` census: a checked declaration whose constant
        // closure reaches `sorryAx` / `sorry` (the warning is closure-based,
        // so this counts `@sorryAx False (!true)`, a sorry behind an alias,
        // and a theorem that only cites a sorry'd lemma).
        let is_sorry = |w: &RegistrationWarning| {
            matches!(
                w.kind,
                RegistrationWarningKind::ExplicitSorry | RegistrationWarningKind::SyntheticSorry
            )
        };
        if warning.is_some_and(is_sorry) {
            self.outcome.sorry_axioms = self.outcome.sorry_axioms.saturating_add(1);
        }
        // A declaration that would be credited is credited only if its cited
        // closure re-admits over this run's own base: an imported declaration
        // is kernel-checked here, not believed.
        let would_credit = name != "(skipped)"
            && source_diagnostics.is_empty()
            && kernel_failures_delta == 0
            && warning.is_none_or(|w| self.allow_sorry && is_sorry(w));
        if would_credit {
            if let Some(gate) = self.state.import_gate.as_mut() {
                if let Err(reason) =
                    crate::check_import_gate::gate_declaration(gate, env, leaf, self.allow_sorry)
                {
                    if self.verbose && !self.json {
                        let _ = writeln!(
                            std::io::stdout(),
                            "  \u{2717} {name} (cited closure not credited)"
                        );
                    }
                    let row = format!("{name}: cited closure not credited: {reason}");
                    if self.is_entry_file {
                        self.outcome.trust_failures.push(row);
                    } else {
                        self.outcome
                            .trust_failures
                            .push(format!("[{module}] {row}"));
                    }
                    return;
                }
            }
        }
        record_checked_decl(
            name,
            warning,
            kernel_failures_delta,
            self.verbose && source_diagnostics.is_empty(),
            self.allow_sorry,
            !self.json && self.is_entry_file,
            &mut trust_failures,
            &mut kernel_failures,
            &mut success_count,
        );
        if !source_diagnostics.is_empty() {
            success_count = 0;
            for diagnostic in source_diagnostics {
                let message = format!("{name}: {}", diagnostic.error);
                self.outcome.errors.push(if self.is_entry_file {
                    message.clone()
                } else {
                    format!("[{module}] {message}")
                });
                let mut feedback = check_feedback_from_message(
                    decl,
                    self.content,
                    module,
                    CheckFailureReason::Source,
                    message,
                );
                feedback.declaration = Some(name.to_owned());
                if let Some(span) = diagnostic
                    .span
                    .and_then(|span| source_span(self.content, span))
                {
                    feedback.source_span = Some(span);
                }
                self.outcome.structured_failures.push(feedback);
            }
        }
        // DISCLOSE an assumption-bearing pass (see `FileCheckOutcome::assumptions`).
        if success_count > 0 {
            let assumed =
                clean_elab::register::leaf_domain_axioms(&mut self.state.axiom_closure, env, leaf);
            if !assumed.is_empty() {
                let row = format!(
                    "{name}: rests on axiom(s) {}",
                    // Unambiguous: a one-component `«Eq.refl»` must not read
                    // as the kernel's `Eq.refl`.
                    assumed
                        .iter()
                        .map(Name::to_unambiguous_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                self.outcome.assumptions.push(if self.is_entry_file {
                    row
                } else {
                    format!("[{module}] {row}")
                });
            }
        }
        // Non-entry diagnostics carry the module of origin, so a failure is
        // traced to the imported file rather than a bare declaration name.
        if self.is_entry_file {
            self.outcome.success_count += success_count;
            self.outcome.trust_failures.extend(trust_failures);
            self.outcome.kernel_failures.extend(kernel_failures);
        } else {
            self.outcome.trust_failures.extend(
                trust_failures
                    .into_iter()
                    .map(|f| format!("[{module}] {f}")),
            );
            self.outcome.kernel_failures.extend(
                kernel_failures
                    .into_iter()
                    .map(|f| format!("[{module}] {f}")),
            );
        }
    }
}

impl ModuleObserver for CheckObserver<'_> {
    fn before_body(&mut self, env: &Environment) {
        if self.state.source_setup.is_some()
            || (self.is_entry_file && self.state.export_targets.is_some())
        {
            self.body_environment = Some(env.clone());
        }
    }

    fn before_decl(&mut self, _env: &Environment, _index: usize, _decl: &SurfaceDecl) {
        // PER-DECLARATION BUDGET: the driver refills the ambient fuel next;
        // snapshot the outcome so this declaration's contribution can be
        // replaced wholesale if it turns out not to have finished. The unit is
        // the TOP-LEVEL surface declaration: a `namespace` / `section` /
        // `mutual` block shares one budget among its members.
        self.decl_start = Some(Instant::now());
        self.mark = Some(OutcomeMark::take(self.outcome, self.counted_leaf_decls));
    }

    fn decl_registered(&mut self, _decl: &SurfaceDecl, registered: &RegisteredElabResult) {
        self.elab_outcomes
            .push(ElabOutcome::of_registered(registered));
    }

    fn decl_failed(&mut self, _env: &Environment, decl: &SurfaceDecl, error: &ElabError) {
        self.elab_outcomes.push(ElabOutcome::Refused);
        self.record_elaboration_failure(decl, error);
        // An `import` that failed leaves `env` holding whatever part of its
        // closure loaded before the failure — for a corrupt artifact, the
        // rewritten part. Nothing more in this file is checked against that
        // (module-trust round 27: `(V0.P.mk 0 1).x = 1` was counted `passed`
        // after the import that refused its artifact).
        if matches!(decl, SurfaceDecl::Import { .. }) {
            let module = self.module;
            self.outcome.errors.push(if self.is_entry_file {
                format!(
                    "{module}: not checked — an import failed, so nothing in this file \
                     is checked against the part of it that loaded"
                )
            } else {
                format!(
                    "[{module}] not checked — an import failed, so nothing in this \
                     file is checked against the part of it that loaded"
                )
            });
            self.stopped = true;
        }
    }

    fn leaf_warning(
        &mut self,
        env: &Environment,
        leaf: &ElabResult,
        _driver_default: &dyn Fn() -> Option<RegistrationWarning>,
    ) -> Option<RegistrationWarning> {
        // By leaf, not by name (an `example` has no name, so a by-name lookup
        // never saw the `sorry` in one), and with the run's closure memo: the
        // verdict is the closure's.
        clean_elab::register::registration_warning_for_leaf_in(
            &mut self.state.axiom_closure,
            env,
            leaf,
        )
    }

    fn leaf_checked(&mut self, env: &Environment, decl: &SurfaceDecl, outcome: &LeafOutcome<'_>) {
        self.record_leaf(env, decl, outcome);
    }

    fn kernel_failure_count(&self) -> u64 {
        // `clean check` reports run totals off the process-wide counter under
        // `module_elaboration_lock`; the per-leaf deltas read the same one.
        kernel_check_failure_count()
    }

    fn after_decl(&mut self, file_ctx: &FileContext, decl: &SurfaceDecl, budget: &BudgetReading) {
        if self.stopped {
            // A failed `import`: the file stops before its budget is read.
            return;
        }
        // Did it actually finish? Asked unconditionally, because the ambient
        // budget latches: even if the kernel's `DeclarationBudgetExhausted`
        // was swallowed on the way up and the declaration reported an
        // ordinary pass or failure, the latch still says the work was cut
        // short, and that reading wins over both.
        self.outcome.peak_decl_ticks = self.outcome.peak_decl_ticks.max(budget.spent);
        if self.budget_trace {
            let name = surface_decl_name(decl).unwrap_or_else(|| "(anonymous)".to_owned());
            let _ = writeln!(
                std::io::stderr(),
                "decl-budget\t{}\t{name}\t{}",
                self.module,
                budget.spent
            );
        }
        if budget.exhausted {
            self.rollback_diverged(decl, budget);
        }
        if self.is_entry_file {
            let spent_wall = self
                .decl_start
                .map(|start| start.elapsed())
                .unwrap_or_default();
            if matches!(decl, SurfaceDecl::Import { .. }) {
                self.outcome.timing.import += spent_wall;
            } else {
                self.outcome.timing.elab += spent_wall;
            }
        }
        // An `import` just loaded artifacts: before anything is checked
        // against them, each must be the build of its source where that
        // source is present (`import_binding.rs`).
        if matches!(decl, SurfaceDecl::Import { .. })
            && bind_loaded_imports(
                self.state,
                file_ctx,
                self.outcome,
                self.is_entry_file,
                self.module,
            )
        {
            self.stopped = true;
        }
    }

    fn stop_requested(&self) -> bool {
        self.stopped
    }
}
