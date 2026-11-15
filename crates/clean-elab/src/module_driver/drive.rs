// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The per-declaration loop.

use super::surface::{registration_warning_label, verdict_name, SourceLines};
use super::verdict::{
    elab_result_name, typecheck_elab_result, BudgetReading, DeclVerdict, DriverOptions,
    FailureIsolation, ImportHandling, LeafOutcome, ModuleReport, VerdictKind,
};
use crate::register::{kernel_check_failures_on_this_thread, registration_warning_for_name};
use crate::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext, RegisteredElabResult, RegistrationWarning,
};
use clean_kernel::Environment;
use clean_parser::SurfaceDecl;

/// What a frontend sees of [`elaborate_decls`] while it runs. Every method has
/// a no-op default; `()` observes nothing.
///
/// Events for one top-level declaration arrive in this order: `before_decl`;
/// then either `decl_registered` followed by one `leaf_checked` per leaf, or
/// `decl_failed`; then `after_decl`.
pub trait ModuleObserver {
    /// The leading imports have been processed; the first body declaration
    /// has not. An empty/import-only module reaches this checkpoint at the
    /// end, provided the observer did not stop the header. Imported artifact
    /// effects belong to the closure, not to the source body's own effect.
    fn before_body(&mut self, _env: &Environment) {}

    /// Declaration `index` of the file is about to be elaborated against `env`.
    fn before_decl(&mut self, _env: &Environment, _index: usize, _decl: &SurfaceDecl) {}

    /// `decl` elaborated and registered; its leaves follow.
    fn decl_registered(&mut self, _decl: &SurfaceDecl, _registered: &RegisteredElabResult) {}

    /// `decl` failed to elaborate. `env` is the environment the next
    /// declaration will see (restored first under
    /// [`FailureIsolation::Rollback`]).
    fn decl_failed(&mut self, _env: &Environment, _decl: &SurfaceDecl, _error: &ElabError) {}

    /// One leaf of the registered `decl` was re-validated against `env`.
    fn leaf_checked(
        &mut self,
        _env: &Environment,
        _decl: &SurfaceDecl,
        _outcome: &LeafOutcome<'_>,
    ) {
    }

    /// `decl` is done; `budget` says whether it finished. `file_ctx` is the
    /// context the next declaration will be elaborated in (what an `import`
    /// just loaded is recorded there).
    fn after_decl(
        &mut self,
        _file_ctx: &FileContext,
        _decl: &SurfaceDecl,
        _budget: &BudgetReading,
    ) {
    }

    /// The trust debt of `leaf` in `env`, read before it is re-validated.
    /// `driver_default` is the driver's own reading: for an administrative
    /// result the registration's warning, for a leaf the by-name lookup. An
    /// observer with its own census (`clean check` reads every leaf's constant
    /// closure through a run-wide memo) answers here instead.
    fn leaf_warning(
        &mut self,
        _env: &Environment,
        _leaf: &ElabResult,
        driver_default: &dyn Fn() -> Option<RegistrationWarning>,
    ) -> Option<RegistrationWarning> {
        driver_default()
    }

    /// The kernel-failure counter the driver differences around every leaf.
    /// This thread's counter by default (a module's delta is attributable
    /// only through it when modules elaborate concurrently); `clean check`,
    /// which holds [`module_elaboration_lock`](super::module_elaboration_lock)
    /// and reports run totals, reads the process-wide counter.
    fn kernel_failure_count(&self) -> u64 {
        kernel_check_failures_on_this_thread()
    }

    /// Asked after every `after_decl`: `true` stops the loop there, and the
    /// rest of the module is not elaborated. `clean check` stops a file whose
    /// `import` failed or loaded an artifact it refused.
    fn stop_requested(&self) -> bool {
        false
    }
}

impl ModuleObserver for () {}

/// Elaborate `decls` (the parse of `source`) into `env`, one declaration at a
/// time, threading `file_ctx`, and return every declaration's verdict.
///
/// A failing declaration never stops the loop: its verdict is recorded and the
/// next declaration runs, so a module reports ALL of its failures. Only the
/// observer stops it ([`ModuleObserver::stop_requested`]). Blocks are
/// flattened to their members, and every member is re-validated read-only
/// against the environment it was registered into. The ambient budget is
/// refilled before each top-level declaration and read after it; a declaration
/// that exhausted it has every verdict it minted replaced by one
/// [`VerdictKind::Diverged`], because an apparent pass off an exhausted budget
/// may rest on an under-reduced term.
///
/// The caller arms the budget ([`DeclBudgetScope`](super::DeclBudgetScope))
/// and holds [`module_elaboration_lock`](super::module_elaboration_lock).
pub fn elaborate_decls<O: ModuleObserver + ?Sized>(
    env: &mut Environment,
    decls: &[SurfaceDecl],
    source: &str,
    file_ctx: &mut FileContext,
    options: DriverOptions,
    observer: &mut O,
) -> ModuleReport {
    // Entered only when asked for: an enclosing scope (a test of the front
    // door's refusals) stays in force for a driver run with the default.
    let _front_door = options
        .lean_front_door
        .then(|| crate::lean_compile_checks::FrontDoorScope::enter(true));
    let mut report = ModuleReport::default();
    let lines = SourceLines::new(source);
    let mut body_started = false;
    for (index, decl) in decls.iter().enumerate() {
        if options.imports == ImportHandling::Preloaded
            && matches!(decl, SurfaceDecl::Import { .. })
        {
            continue;
        }
        if !body_started && !matches!(decl, SurfaceDecl::Import { .. }) {
            observer.before_body(env);
            body_started = true;
        }
        observer.before_decl(env, index, decl);
        clean_kernel::tc::reset_declaration_budget();
        let mark = report.verdicts.len();
        let kernel_failures_before = observer.kernel_failure_count();
        let processed = preprocess_decl_with_context(decl, file_ctx);
        let before = (options.isolation == FailureIsolation::Rollback).then(|| env.clone());
        match elaborate_decl_and_register_with_context_and_warning(env, &processed, file_ctx) {
            Ok(registered) => {
                observer.decl_registered(decl, &registered);
                // A passing `#guard_msgs` is a checked unit too.
                let mut leaves: Vec<&ElabResult> = Vec::new();
                registered.result.checked_leaves(&mut leaves);
                if leaves.is_empty() {
                    // Purely administrative (import / set_option / open /
                    // #command): judged as one result with the registration's
                    // own warning and the delta across its whole elaboration.
                    let warning = observer
                        .leaf_warning(env, &registered.result, &|| registered.warning.clone());
                    let outcome = check_leaf(
                        env,
                        &registered.result,
                        warning,
                        kernel_failures_before,
                        &*observer,
                    );
                    record_leaf(&mut report, decl, &lines, &outcome);
                    observer.leaf_checked(env, decl, &outcome);
                } else {
                    // A block elaborated and kernel-checked ALL its members in
                    // the call above, and every inner kernel failure surfaces
                    // as its own `Failed` leaf. Sampling the counter NOW gives
                    // every leaf a zero delta, so a passing member never
                    // inherits a sibling's failure (the namespace-ABORT
                    // regression, where `T.a` took `T.b`'s failure).
                    let kernel_before = observer.kernel_failure_count();
                    for leaf in leaves {
                        let warning = observer.leaf_warning(env, leaf, &|| {
                            leaf.declaration_name()
                                .and_then(|name| registration_warning_for_name(env, name))
                        });
                        let outcome = check_leaf(env, leaf, warning, kernel_before, &*observer);
                        record_leaf(&mut report, decl, &lines, &outcome);
                        observer.leaf_checked(env, decl, &outcome);
                    }
                }
            }
            Err(error) => {
                if let Some(before) = before {
                    *env = before;
                }
                report.verdicts.push(DeclVerdict {
                    name: verdict_name(decl),
                    kind: VerdictKind::ElaborationFailed,
                    line: lines.decl_line(decl),
                    detail: Some(elaboration_detail(decl, &lines, &error)),
                });
                observer.decl_failed(env, decl, &error);
            }
        }

        // Asked AFTER the fact and unconditionally: the ambient budget
        // latches, so even a pass or failure reported off swallowed
        // exhaustion is known to have been cut short, and that reading wins.
        let budget = BudgetReading {
            spent: clean_kernel::tc::declaration_budget_used(),
            exhausted: clean_kernel::tc::declaration_budget_exhausted(),
            limit: clean_kernel::tc::declaration_budget_limit(),
        };
        report.peak_decl_ticks = report.peak_decl_ticks.max(budget.spent);
        if budget.exhausted {
            report.verdicts.truncate(mark);
            report.verdicts.push(DeclVerdict {
                name: verdict_name(decl),
                kind: VerdictKind::Diverged,
                line: lines.decl_line(decl),
                detail: Some(format!(
                    "did not finish — spent the whole per-declaration budget of {} \
                     kernel operations",
                    budget.limit
                )),
            });
        }
        observer.after_decl(file_ctx, decl, &budget);
        if observer.stop_requested() {
            break;
        }
    }
    if !body_started && !observer.stop_requested() {
        observer.before_body(env);
    }
    report
}

/// Re-validate one leaf the way `clean check` always has: a `Failed` member
/// stands on its own error; anything else is re-checked read-only, and the
/// kernel-failure delta is read after the re-check.
fn check_leaf<'a, O: ModuleObserver + ?Sized>(
    env: &Environment,
    leaf: &'a ElabResult,
    warning: Option<RegistrationWarning>,
    kernel_failures_before: u64,
    observer: &O,
) -> LeafOutcome<'a> {
    if let ElabResult::Failed { name, decl, error } = leaf {
        return LeafOutcome::Failed {
            name: name.as_str(),
            decl: decl.as_ref(),
            error: error.as_ref(),
        };
    }
    let (registered, source_diagnostics) = match leaf {
        ElabResult::Diagnosed {
            result,
            diagnostics,
        } => (result.as_ref(), diagnostics.as_slice()),
        _ => (leaf, &[][..]),
    };
    match typecheck_elab_result(registered, env) {
        Ok(name) => LeafOutcome::Checked {
            name,
            leaf,
            warning,
            kernel_failures_delta: observer
                .kernel_failure_count()
                .saturating_sub(kernel_failures_before),
            source_diagnostics,
        },
        Err(message) => LeafOutcome::ValidationFailed {
            name: elab_result_name(leaf),
            message,
        },
    }
}

/// Append the verdict `outcome` earns, if it earns one.
fn record_leaf(
    report: &mut ModuleReport,
    decl: &SurfaceDecl,
    lines: &SourceLines<'_>,
    outcome: &LeafOutcome,
) {
    let Some(kind) = outcome.verdict_kind() else {
        return;
    };
    let verdict = match outcome {
        LeafOutcome::Failed {
            name,
            decl: inner,
            error,
        } => DeclVerdict {
            name: (*name).to_owned(),
            kind,
            line: lines.decl_line(inner),
            detail: Some(elaboration_detail(inner, lines, error)),
        },
        LeafOutcome::ValidationFailed { name, message } => DeclVerdict {
            name: name.clone(),
            kind,
            line: lines.decl_line(decl),
            detail: Some(message.clone()),
        },
        LeafOutcome::Checked {
            name,
            warning,
            kernel_failures_delta,
            source_diagnostics,
            ..
        } => {
            let (name, detail) = match (warning, &kind) {
                (_, VerdictKind::SourceError) => (
                    name.clone(),
                    Some(
                        source_diagnostics
                            .iter()
                            .map(|d| d.error.to_string())
                            .collect::<Vec<_>>()
                            .join("\n"),
                    ),
                ),
                (Some(warning), _) => (
                    // "(skipped)" also names a whole mutual block; its warning
                    // carries the real declaration name.
                    if name == "(skipped)" {
                        crate::private_names::user_facing_name(&warning.decl_name).to_string()
                    } else {
                        name.clone()
                    },
                    Some(format!(
                        "declaration uses {}",
                        registration_warning_label(&warning.kind)
                    )),
                ),
                (None, VerdictKind::KernelCheckFailed) => (
                    name.clone(),
                    Some(format!("kernel check failures: {kernel_failures_delta}")),
                ),
                (None, _) => (name.clone(), None),
            };
            DeclVerdict {
                name,
                kind,
                line: source_diagnostics
                    .first()
                    .and_then(|d| d.span)
                    .and_then(|span| lines.span_line(span))
                    .or_else(|| lines.decl_line(decl)),
                detail,
            }
        }
    };
    report.verdicts.push(verdict);
}

/// `clean check`'s rendering of an elaboration failure, without the name
/// prefix: `elaboration error at line N: <Display of the error>`.
fn elaboration_detail(decl: &SurfaceDecl, lines: &SourceLines<'_>, error: &ElabError) -> String {
    let position = lines
        .decl_line(decl)
        .map(|line| format!(" at line {line}"))
        .unwrap_or_default();
    format!("elaboration error{position}: {error}")
}
