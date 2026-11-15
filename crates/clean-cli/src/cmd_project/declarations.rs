// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Check, count and report each elaborated project declaration leaf, and
//! preserve its trust blockers.

use std::fs;

use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, kernel_check_failure_count,
    preprocess_decl_with_context, ElabResult, FileContext, RegistrationWarning,
    RegistrationWarningKind,
};
use clean_kernel::sorry::sorry_count;
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::SurfaceDecl;
use clean_server::handlers::validate_decl_read_only;

use super::{push_blocking_diagnostic, ParsedProjectModule, ProjectModuleReport, ProjectSource};

use crate::cmd_core::ElabOutcome;

/// What one elaboration of a module did: its effect on every environment
/// component, and how each of its top-level declarations elaborated.
#[derive(Clone, Debug)]
pub(super) struct ModuleElaboration {
    pub(super) effect: clean_kernel::env::EnvEffect,
    pub(super) outcomes: Vec<ElabOutcome>,
}

impl ModuleElaboration {
    /// Why `replayed` — this module re-elaborated next to modules it does not
    /// import, leaving `replayed_env` — does not give an importer what this
    /// module's own check (`self`) gives it, or `None` when it does.
    pub(super) fn disagreement(
        &self,
        replayed: &ModuleElaboration,
        replayed_env: &Environment,
    ) -> Option<String> {
        crate::cmd_core::elab_outcome_difference(&self.outcomes, &replayed.outcomes)
            .or_else(|| self.effect.disagreement(&replayed.effect, replayed_env))
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_project_module_with_env(
    source: &ProjectSource,
    parsed: &ParsedProjectModule,
    env: &mut Environment,
    gate: &mut clean_olean::ImportedConeGate,
    allow_sorry: bool,
    report: &mut ProjectModuleReport,
    outcomes: &mut Vec<ElabOutcome>,
) {
    let sorry_before = sorry_count();
    let kernel_before = kernel_check_failure_count();
    let mut file_ctx = FileContext::new();
    file_ctx.disable_external_import_search();
    // Lean's main module: the name an importer's `import` writes for this
    // file, so its `private` declarations are `_private.<module>.0.<name>`
    // (G21) here and in every replay of it.
    file_ctx.set_main_module(source.identity.clone());
    let mut axioms = clean_kernel::env::DomainAxiomClosure::new();
    // Source text, for span-accurate `at line N` positions on failures. A read
    // failure here cannot hide a verdict: only the position suffix is lost.
    let content = fs::read_to_string(&source.path).unwrap_or_default();

    for decl in &parsed.decls {
        // Skip `import` decls here: topological loading already pre-loaded
        // project-local dependencies into `env`, and external imports were
        // already flagged as authority blockers in the parse phase.
        if matches!(decl, SurfaceDecl::Import { .. }) {
            continue;
        }
        let kernel_failures_before = kernel_check_failure_count();
        let processed_decl = preprocess_decl_with_context(decl, &mut file_ctx);
        let elaborated = elaborate_decl_and_register_with_context_and_warning(
            env,
            &processed_decl,
            &mut file_ctx,
        );
        outcomes.push(ElabOutcome::of(&elaborated));
        match elaborated {
            Ok(registered) => {
                // VACUOUS-PASS FIX (K5, 2026-09-17). A `namespace` / `section` /
                // `mutual` block elaborates to ONE `ElabResult::Multiple` whose
                // members — including every `ElabResult::Failed` member — live
                // inside it. This loop used to hand that block straight to
                // `typecheck_elab_result`, which answered `Ok("(skipped)")`
                // without looking inside, and `record_project_decl` then dropped
                // it. A package whose declarations all live in namespaces (the
                // normal Lean shape: every TSL module opens `namespace TrustIr`)
                // therefore reported `declarations_checked = 0`,
                // `declarations_failed = 0`, `status: pass` — and a deliberate
                // type error inside the block exited 0.
                //
                // `leaf_decls` flattens the block to its declaration leaves,
                // exactly as `clean check` does (`cmd_core::check_file_body`), so
                // each member is type-checked, counted and reported on its own.
                // A passing `#guard_msgs` is a checked unit too.
                let mut leaves: Vec<&ElabResult> = Vec::new();
                registered.result.checked_leaves(&mut leaves);
                if leaves.is_empty() {
                    // Purely administrative (import / set_option / open /
                    // `#command`), or an empty block: route through the single-
                    // result path so `(skipped)` results stay uncounted, exactly
                    // as before.
                    let warning = clean_elab::register::registration_warning_for_leaf_in(
                        &mut axioms,
                        env,
                        &registered.result,
                    );
                    record_project_leaf(
                        source,
                        &registered.result,
                        warning,
                        env,
                        &content,
                        kernel_failures_before,
                        allow_sorry,
                        &mut axioms,
                        gate,
                        report,
                    );
                } else {
                    // The block already elaborated and kernel-checked all of its
                    // members inside the call above, so every inner kernel
                    // failure has already bumped the global counter AND surfaces
                    // here as its own `Failed` leaf. Sample the counter now, so
                    // the block's delta is not smeared onto a passing sibling
                    // (the namespace-ABORT misattribution `cmd_core` documents);
                    // each `Failed` leaf carries its own failure.
                    let kernel_before_leaves = kernel_check_failure_count();
                    for leaf in leaves {
                        // By leaf, not by name: an `example` has no name and
                        // was credited as a pass with a `sorry` in it.
                        let warning = clean_elab::register::registration_warning_for_leaf_in(
                            &mut axioms,
                            env,
                            leaf,
                        );
                        record_project_leaf(
                            source,
                            leaf,
                            warning,
                            env,
                            &content,
                            kernel_before_leaves,
                            allow_sorry,
                            &mut axioms,
                            gate,
                            report,
                        );
                    }
                }
            }
            Err(e) => {
                // A top-level declaration that fails to elaborate is one checked
                // unit that failed. Name it and place it, as `clean check` does:
                // `elaboration error: <Debug>` alone named no declaration.
                let named = crate::cmd_core::surface_decl_name(decl)
                    .map(|name| format!("{name}: "))
                    .unwrap_or_default();
                let position = decl_position_suffix(decl, &content);
                report.checked_count += 1;
                push_project_failure(
                    "checker_error",
                    source,
                    format!("{named}elaboration error{position}: {e}"),
                    report,
                );
            }
        }
    }

    let sorry_delta = sorry_count().saturating_sub(sorry_before);
    let kernel_delta = kernel_check_failure_count().saturating_sub(kernel_before);
    // `sorry_axioms` is the closure census `record_project_leaf` kept (checked
    // declarations whose constant closure reaches `sorryAx` / `sorry`); the
    // elaborator's own counter is reported beside it.
    report.trust_summary.sorry_terms_minted = sorry_delta;
    report.trust_summary.kernel_check_failures = kernel_delta;

    // FAIL CLOSED on a trust event no declaration row accounts for. The two
    // counters above are maintained by the kernel/registration layer,
    // independently of this loop's bookkeeping. A module whose counters moved
    // is not a pass, whether or not a declaration row already failed: retain
    // the event as a MODULE blocker (it is not a declaration, so it does not
    // move `declarations_failed`), rather than assigning it to a sibling. The
    // K5 probe measured exactly this shape (`sorry_axioms: 1` /
    // `kernel_check_failures: 1` inside modules marked `pass`), and an
    // anonymous `example … := by sorry` has no registered name to hang a row on.
    for (kind, count) in [
        (
            "kernel_check_failure",
            report.trust_summary.kernel_check_failures,
        ),
        (
            "sorry_axiom",
            if allow_sorry {
                0
            } else {
                report
                    .trust_summary
                    .sorry_axioms
                    .max(report.trust_summary.sorry_terms_minted)
            },
        ),
    ] {
        if count > 0 {
            push_blocking_diagnostic(
                kind,
                source,
                format!("module recorded {count} {kind} occurrence(s)"),
                &mut report.diagnostics,
                &mut report.authority_blockers,
            );
        }
    }
}

/// Re-elaborate an already-checked module's declarations into `env`, the
/// environment of a module that imports it. Nothing is reported: the module's
/// verdict comes from its own check, and the caller compares what this adds
/// with what that check added.
pub(super) fn replay_project_module(
    parsed: &ParsedProjectModule,
    identity: &Name,
    env: &mut Environment,
) -> Vec<ElabOutcome> {
    let mut file_ctx = FileContext::new();
    file_ctx.disable_external_import_search();
    // The same main module as the module's own check, or every private
    // constant would read as a difference.
    file_ctx.set_main_module(identity.clone());
    let mut outcomes = Vec::new();
    for decl in &parsed.decls {
        if matches!(decl, SurfaceDecl::Import { .. }) {
            continue;
        }
        let processed_decl = preprocess_decl_with_context(decl, &mut file_ctx);
        // A failure here leaves the declaration out of `env`; the caller
        // compares these outcomes, and the effect, with the module's own
        // check.
        let elaborated = elaborate_decl_and_register_with_context_and_warning(
            env,
            &processed_decl,
            &mut file_ctx,
        );
        outcomes.push(ElabOutcome::of(&elaborated));
    }
    outcomes
}

/// Position suffix (` at line N`) for a surface declaration, or empty when the
/// span cannot be resolved.
pub(super) fn decl_position_suffix(decl: &SurfaceDecl, content: &str) -> String {
    crate::cmd_core::surface_decl_span(decl)
        .filter(|span| span.start <= content.len())
        .map(|span| {
            let (line, _column) = crate::cmd_core::line_column_for_offset(content, span.start);
            format!(" at line {line}")
        })
        .unwrap_or_default()
}

/// Check, count and report ONE declaration leaf.
///
/// The leaf is either a top-level declaration's own result or one member of a
/// flattened `namespace` / `section` / `mutual` block. Both are one checked
/// unit; administrative `(skipped)` results are the only thing that stays
/// uncounted.
#[allow(clippy::too_many_arguments)]
pub(super) fn record_project_leaf(
    source: &ProjectSource,
    leaf: &ElabResult,
    warning: Option<RegistrationWarning>,
    env: &Environment,
    content: &str,
    kernel_failures_before: u64,
    allow_sorry: bool,
    axioms: &mut clean_kernel::env::DomainAxiomClosure,
    gate: &mut clean_olean::ImportedConeGate,
    report: &mut ProjectModuleReport,
) {
    // A `Failed` leaf is an inner declaration whose elaboration or kernel check
    // already failed. It is NOT in the environment and can never count as a
    // pass; report it from its own stored error, span-accurately.
    if let ElabResult::Failed {
        name,
        decl: inner_decl,
        error,
    } = leaf
    {
        let position = decl_position_suffix(inner_decl, content);
        report.checked_count += 1;
        push_project_failure(
            "checker_error",
            source,
            format!("{name}: elaboration error{position}: {error}"),
            report,
        );
        return;
    }
    match typecheck_elab_result(leaf, env) {
        Ok(name) => {
            if name == "(skipped)" {
                return;
            }
            let kernel_delta = kernel_check_failure_count().saturating_sub(kernel_failures_before);
            report.checked_count += 1;
            // The `sorry_axioms` census (closure-based warning; see
            // `cmd_core::FileCheckOutcome::sorry_axioms`).
            if warning.as_ref().is_some_and(|w| {
                matches!(
                    w.kind,
                    RegistrationWarningKind::ExplicitSorry
                        | RegistrationWarningKind::SyntheticSorry
                )
            }) {
                report.trust_summary.sorry_axioms =
                    report.trust_summary.sorry_axioms.saturating_add(1);
            }
            // CLOSURE-AWARE CREDIT — the same rule `clean check` applies
            // (`CheckObserver::record_checked_leaf` in
            // `cmd_core/check_observer.rs`). A leaf that would be credited
            // is credited only if its cited closure re-admits over the run's
            // base and reaches no trust marker. Without this,
            // `theorem t : 1 = 2 := A.s` with `A.s := sorry` counted as PASSED
            // (and its module `pass`): `t` itself carries no sorry warning,
            // the sorry lives one citation away (round-24 verification of
            // 29de4ae8b; same on main).
            if would_credit(&name, warning.as_ref(), kernel_delta, allow_sorry) {
                if let Err(reason) =
                    crate::check_import_gate::gate_declaration(gate, env, leaf, allow_sorry)
                {
                    push_project_failure(
                        "cited_closure_not_credited",
                        source,
                        format!("{name}: cited closure not credited: {reason}"),
                        report,
                    );
                    return;
                }
            }
            let passed_before = report.success_count;
            record_project_decl(
                source,
                &name,
                warning.as_ref(),
                kernel_delta,
                allow_sorry,
                report,
            );
            // DISCLOSE an assumption-bearing pass. `axiom bogus : 1 = 2` and a
            // theorem proved from it both passed with nothing in the report
            // saying the verdict rests on an assumption (round-22
            // verification). The pass stands — it is valid under the axioms
            // the source states — but it is never summarised as unconditional.
            if report.success_count > passed_before {
                let assumed = clean_elab::register::leaf_domain_axioms(axioms, env, leaf);
                if !assumed.is_empty() {
                    report.assumptions.push(format!(
                        "{name}: rests on axiom(s) {}",
                        // Unambiguous: a one-component `«Eq.refl»` must not
                        // read as the kernel's `Eq.refl`.
                        assumed
                            .iter()
                            .map(Name::to_unambiguous_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
            }
        }
        Err(message) => {
            report.checked_count += 1;
            push_project_failure(
                "checker_error",
                source,
                format!("{}: {message}", elab_result_name(leaf)),
                report,
            );
        }
    }
}

/// Whether [`record_project_decl`] would count this leaf as passed. Kept
/// beside it so the closure gate runs on exactly the leaves that would
/// otherwise be credited, as in `clean check`.
fn would_credit(
    name: &str,
    warning: Option<&RegistrationWarning>,
    kernel_failures_delta: u64,
    allow_sorry: bool,
) -> bool {
    name != "(skipped)"
        && kernel_failures_delta == 0
        && warning.is_none_or(|w| {
            allow_sorry
                && matches!(
                    w.kind,
                    RegistrationWarningKind::ExplicitSorry
                        | RegistrationWarningKind::SyntheticSorry
                )
        })
}

fn record_project_decl(
    source: &ProjectSource,
    name: &str,
    warning: Option<&RegistrationWarning>,
    kernel_failures_delta: u64,
    allow_sorry: bool,
    report: &mut ProjectModuleReport,
) {
    if name == "(skipped)" {
        return;
    }
    // A kernel check failure is decided BEFORE the sorry policy: `--allow-sorry`
    // waives a `sorry`, never a failed kernel check (origin/main e0b0b8714's
    // ordering, kept through the merge).
    if kernel_failures_delta > 0 {
        push_project_failure(
            "kernel_check_failure",
            source,
            format!("{name}: kernel check failures: {kernel_failures_delta}"),
            report,
        );
        return;
    }
    if let Some(warning) = warning {
        let is_sorry = matches!(
            warning.kind,
            RegistrationWarningKind::ExplicitSorry | RegistrationWarningKind::SyntheticSorry
        );
        if allow_sorry && is_sorry {
            report.success_count += 1;
            return;
        }
        push_project_failure(
            "trust_failure",
            source,
            format!(
                "{}: declaration uses {}{}",
                warning.decl_name,
                registration_warning_label(&warning.kind),
                warning.via_suffix()
            ),
            report,
        );
        return;
    }
    report.success_count += 1;
}

pub(super) fn push_project_failure(
    kind: &'static str,
    source: &ProjectSource,
    message: String,
    report: &mut ProjectModuleReport,
) {
    report.failed_count += 1;
    push_blocking_diagnostic(
        kind,
        source,
        message,
        &mut report.diagnostics,
        &mut report.authority_blockers,
    );
}

fn registration_warning_label(kind: &RegistrationWarningKind) -> &'static str {
    match kind {
        RegistrationWarningKind::ExplicitSorry => "explicit sorry",
        RegistrationWarningKind::SyntheticSorry => "synthetic sorry",
        RegistrationWarningKind::TrustedArith => "trustedArith",
        RegistrationWarningKind::TrustedAy => "trustedAy",
    }
}

fn elab_result_name(result: &ElabResult) -> String {
    match result {
        ElabResult::Diagnosed { result, .. } => elab_result_name(result),
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Structure { name, .. }
        | ElabResult::Instance { name, .. }
        | ElabResult::Inductive { name, .. } => {
            // A private declaration is reported by its user-facing name, as
            // `clean check` and Lean's messages name it (G21).
            clean_elab::private_names::user_facing_name(name).to_string()
        }
        ElabResult::MutualInductive { decl, .. } => decl.types.first().map_or_else(
            || "(mutual inductive)".to_string(),
            |t| clean_elab::private_names::user_facing_name(&t.name).to_string(),
        ),
        ElabResult::Failed { name, .. } => name.clone(),
        // Anonymous, checked-then-discarded (B02) — still one checked unit.
        ElabResult::Example { .. } => "example".to_string(),
        ElabResult::Command(_) | ElabResult::Multiple(_) | ElabResult::Skipped => {
            "(skipped)".to_string()
        }
    }
}

pub(super) fn typecheck_elab_result(
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
    // Never report a `Failed` inner decl as a (false) pass.
    if let ElabResult::Failed { name, error, .. } = result {
        return Err(format!("{name}: {error}"));
    }
    // FAIL CLOSED on an unflattened block. This is the K5 vacuous pass, pinned
    // where it happened: answering `Ok("(skipped)")` for a `Multiple` that still
    // holds declarations is what let a whole namespace — every declaration in it
    // — pass unchecked and uncounted. Callers must flatten with `leaf_decls`
    // first; a block that really holds nothing (empty namespace, or one holding
    // only `#command` / `set_option`) still answers `(skipped)`.
    if let Some(refusal) = result.unflattened_block_refusal() {
        return Err(refusal);
    }
    // A passing `#guard_msgs` that declared nothing: its message comparison
    // already ran, and there is no term to re-validate.
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
