// Copyright 2026 Andrew Yates
// Author: dbx-clean-ai
// SPDX-License-Identifier: Apache-2.0

//! Project-specific wrapper around `mathverse`.
//!
//! `cert_mathverse` is a deterministic normalization and diagnostics layer for
//! certificate/PB/SAT arithmetic obligations. It does not bypass mathverse's
//! proof-reconstruction boundary.

use std::fmt::Write;

use clean_kernel::{Environment, Expr, ExprKind};

use crate::stack_safe;

use super::arith_mathverse_parse::{expr_to_mathverse_constraint, extract_constant};
use super::cast::{
    rewrite_local_decls_with_cast_lemmas, rewrite_target_with_cast_lemmas, CastRewriteFlavor,
};
use super::cert_simp::{cert_simp_blocker_heads, cert_simp_with_config, CertSimpConfig};
use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::display::{format_expr, ExprFormatter};
use super::omega_tactic::omega;

/// Configuration for the project mathverse wrapper.
#[derive(Debug, Clone)]
pub struct ProjectMathverseConfig {
    /// Whether to run the project/certificate simplifier hook.
    pub normalize_cert_terms: bool,
    /// Configuration used by the certificate simplifier hook.
    pub cert_simp: CertSimpConfig,
    /// Whether to attempt cast/numeric closeout normalization before mathverse.
    pub normalize_casts: bool,
    /// Policy for Nat-to-Int coercion.
    pub coerce_nat: NatCoercionPolicy,
    /// Maximum blockers to render in human-facing errors.
    pub blocker_limit: usize,
    /// Whether callers should retain the structured report.
    pub emit_telemetry: bool,
}

impl Default for ProjectMathverseConfig {
    fn default() -> Self {
        Self {
            normalize_cert_terms: true,
            cert_simp: CertSimpConfig::default(),
            normalize_casts: true,
            coerce_nat: NatCoercionPolicy::LinearSafe,
            blocker_limit: 4,
            emit_telemetry: true,
        }
    }
}

/// How aggressively the wrapper may coerce Nat-facing arithmetic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatCoercionPolicy {
    /// Do not add Nat-specific coercion facts.
    Off,
    /// Accept only the linear Nat fragment whose casts are already justified.
    LinearSafe,
    /// Future mode: synthesize side-condition-backed facts.
    WithSideConditions,
}

/// Structured outcome from a project mathverse run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjectMathverseOutcome {
    /// The wrapper closed the current goal.
    Closed,
    /// The wrapper did not make progress.
    NoProgress,
    /// The underlying mathverse call failed.
    MathverseFailed { reason: String },
    /// A normalization step failed before mathverse could run.
    NormalizationFailed { reason: String },
}

/// Report returned by the wrapper implementation.
#[derive(Debug, Clone)]
pub struct ProjectMathverseReport {
    pub normalized_target_changed: bool,
    pub normalized_hyp_count: usize,
    pub parsed_constraint_count: usize,
    pub nat_coercion_count: usize,
    pub synthetic_fact_count: usize,
    pub mathverse_result: ProjectMathverseOutcome,
    pub blockers: Vec<MathverseBlocker>,
}

impl Default for ProjectMathverseReport {
    fn default() -> Self {
        Self {
            normalized_target_changed: false,
            normalized_hyp_count: 0,
            parsed_constraint_count: 0,
            nat_coercion_count: 0,
            synthetic_fact_count: 0,
            mathverse_result: ProjectMathverseOutcome::NoProgress,
            blockers: Vec::new(),
        }
    }
}

/// Origin of a reported blocker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockerOrigin {
    Target,
    Hypothesis { name: String },
}

/// Stable blocker classes for wrapper diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MathverseBlockerKind {
    UnsupportedHead,
    NonLinearTerm,
    NatSubWithoutSideCondition,
    UnsupportedCast,
    UnsupportedModulo,
    MissingRewriteLemma,
    NoParseableConstraint,
    ProofReplayFailed,
    MathverseReturnedSatOrUnknown,
}

/// A compact diagnostic explaining why the normalized goal was not sent to or
/// closed by mathverse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MathverseBlocker {
    pub origin: BlockerOrigin,
    pub kind: MathverseBlockerKind,
    pub unsimplified: String,
    pub normalized: Option<String>,
    pub head: Option<String>,
    pub suggestion: Option<String>,
}

#[derive(Debug, Clone)]
struct ExprSnapshot {
    origin: BlockerOrigin,
    unsimplified: Expr,
    normalized: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DiagnosticClass {
    Parsed,
    Irrelevant,
    Blocked(MathverseBlockerKind),
}

/// Project mathverse tactic entry point.
///
/// NOTE: this is the `cert-omega` implementation (a certified wrapper around
/// the `omega` decision procedure). The registered tactic name
/// `cert_mathverse` and this function name are kept unchanged for
/// compatibility; a deprecation cycle to an `omega`-based name will follow
/// later.
pub fn cert_mathverse(state: &mut ProofState) -> TacticResult {
    let config = ProjectMathverseConfig::default();
    let report = cert_mathverse_with_config(state, &config)?;
    if matches!(report.mathverse_result, ProjectMathverseOutcome::Closed) {
        Ok(())
    } else {
        Err(TacticError::ArithmeticFailed {
            tactic: "cert_mathverse".into(),
            reason: render_project_mathverse_failure(&report, config.blocker_limit),
        })
    }
}

/// Run `cert_mathverse` and return the structured report.
///
/// On failure, the input proof state is left unchanged. On success, the closed
/// scratch state is committed back to `state`.
pub fn cert_mathverse_with_report(
    state: &mut ProofState,
) -> Result<ProjectMathverseReport, TacticError> {
    cert_mathverse_with_config(state, &ProjectMathverseConfig::default())
}

/// Configurable implementation for tests and future command surfaces.
pub fn cert_mathverse_with_config(
    state: &mut ProofState,
    config: &ProjectMathverseConfig,
) -> Result<ProjectMathverseReport, TacticError> {
    let original_goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut base = state.clone();
    let mut base_report = ProjectMathverseReport::default();

    if let Err(err) = run_base_normalizers(&mut base, &mut base_report, config) {
        base_report.mathverse_result = ProjectMathverseOutcome::NormalizationFailed {
            reason: err.to_string(),
        };
        if base_report.blockers.is_empty() {
            base_report.blockers.push(make_blocker(
                state.env(),
                ExprSnapshot {
                    origin: BlockerOrigin::Target,
                    unsimplified: original_goal.target.clone(),
                    normalized: original_goal.target.clone(),
                },
                normalization_failure_blocker_kind(&err),
            ));
        }
        return Ok(base_report);
    }

    if base.current_goal().is_none() {
        base_report.mathverse_result = ProjectMathverseOutcome::Closed;
        *state = base;
        return Ok(base_report);
    }

    let mut failures = Vec::new();

    if !matches!(config.coerce_nat, NatCoercionPolicy::Off) {
        let mut coerced = base.clone();
        let mut coerced_report = base_report.clone();
        match run_nat_coercion_normalizer(&mut coerced, &mut coerced_report, config) {
            Ok(()) if coerced.current_goal().is_none() => {
                coerced_report.mathverse_result = ProjectMathverseOutcome::Closed;
                *state = coerced;
                return Ok(coerced_report);
            }
            Ok(())
                if coerced_report.nat_coercion_count > base_report.nat_coercion_count
                    || !coerced_report.blockers.is_empty() =>
            {
                match try_mathverse_attempt(
                    state.env(),
                    &original_goal,
                    coerced,
                    coerced_report,
                    config,
                ) {
                    MathverseAttempt::Closed {
                        state: closed_state,
                        report,
                    } => {
                        *state = closed_state;
                        return Ok(report);
                    }
                    MathverseAttempt::Failed(report) => failures.push(report),
                }
            }
            Ok(()) => {}
            Err(err) => {
                let mut report = coerced_report;
                report.mathverse_result = ProjectMathverseOutcome::NormalizationFailed {
                    reason: err.to_string(),
                };
                if report.blockers.is_empty() {
                    report.blockers.push(make_blocker(
                        state.env(),
                        ExprSnapshot {
                            origin: BlockerOrigin::Target,
                            unsimplified: original_goal.target.clone(),
                            normalized: coerced
                                .current_goal()
                                .map(|goal| goal.target.clone())
                                .unwrap_or_else(|| original_goal.target.clone()),
                        },
                        normalization_failure_blocker_kind(&err),
                    ));
                }
                failures.push(report);
            }
        }
    }

    match try_mathverse_attempt(state.env(), &original_goal, base, base_report, config) {
        MathverseAttempt::Closed {
            state: closed_state,
            report,
        } => {
            *state = closed_state;
            Ok(report)
        }
        MathverseAttempt::Failed(report) => {
            failures.push(report);
            Ok(merge_failure_reports(failures, config.blocker_limit))
        }
    }
}

enum MathverseAttempt {
    Closed {
        state: ProofState,
        report: ProjectMathverseReport,
    },
    Failed(ProjectMathverseReport),
}

fn try_mathverse_attempt(
    env: &Environment,
    original_goal: &Goal,
    mut candidate: ProofState,
    mut report: ProjectMathverseReport,
    config: &ProjectMathverseConfig,
) -> MathverseAttempt {
    let normalized_goal = match candidate.current_goal() {
        Some(goal) => goal.clone(),
        None => {
            report.mathverse_result = ProjectMathverseOutcome::Closed;
            return MathverseAttempt::Closed {
                state: candidate,
                report,
            };
        }
    };

    collect_diagnostics(
        env,
        original_goal,
        &normalized_goal,
        &mut report,
        config.blocker_limit,
    );
    if matches!(config.coerce_nat, NatCoercionPolicy::WithSideConditions) {
        append_missing_nat_sub_side_condition_support(&mut report, config.blocker_limit);
    }
    append_cert_simp_blockers(&candidate, &mut report, config.blocker_limit);

    if has_fatal_blocker(&report) {
        report.mathverse_result = ProjectMathverseOutcome::NoProgress;
        return MathverseAttempt::Failed(report);
    }

    match omega(&mut candidate) {
        Ok(()) => {
            report.mathverse_result = ProjectMathverseOutcome::Closed;
            MathverseAttempt::Closed {
                state: candidate,
                report,
            }
        }
        Err(err) => {
            let blocker_kind = mathverse_failure_blocker_kind(&err);
            report.mathverse_result = ProjectMathverseOutcome::MathverseFailed {
                reason: err.to_string(),
            };
            if report.blockers.is_empty() {
                report.blockers.push(make_blocker(
                    env,
                    ExprSnapshot {
                        origin: BlockerOrigin::Target,
                        unsimplified: original_goal.target.clone(),
                        normalized: normalized_goal.target.clone(),
                    },
                    blocker_kind,
                ));
            }
            MathverseAttempt::Failed(report)
        }
    }
}

fn run_base_normalizers(
    scratch: &mut ProofState,
    report: &mut ProjectMathverseReport,
    config: &ProjectMathverseConfig,
) -> Result<(), TacticError> {
    if config.normalize_cert_terms {
        run_cert_simp_normalizer(scratch, report, config)?;
        if scratch.current_goal().is_none() {
            return Ok(());
        }
    }

    if config.normalize_casts {
        run_closeout_normalizer(scratch, report, super::norm_num);
        if scratch.current_goal().is_none() {
            return Ok(());
        }
        run_cast_rewrite_pass(scratch, report, CastRewriteFlavor::NormCast, false)?;
        if scratch.current_goal().is_none() {
            return Ok(());
        }
    }

    Ok(())
}

fn run_nat_coercion_normalizer(
    scratch: &mut ProofState,
    report: &mut ProjectMathverseReport,
    config: &ProjectMathverseConfig,
) -> Result<(), TacticError> {
    run_cast_rewrite_pass(scratch, report, CastRewriteFlavor::Zify, true)?;
    if scratch.current_goal().is_none() {
        return Ok(());
    }

    if config.normalize_casts {
        run_closeout_normalizer(scratch, report, super::norm_num);
    }

    Ok(())
}

fn run_cert_simp_normalizer(
    scratch: &mut ProofState,
    report: &mut ProjectMathverseReport,
    config: &ProjectMathverseConfig,
) -> Result<(), TacticError> {
    let before_goal = scratch.current_goal().cloned();
    let mut candidate = scratch.clone();
    let mut cert_config = config.cert_simp.clone();
    cert_config.diagnostics = false;

    match cert_simp_with_config(&mut candidate, &cert_config) {
        Ok(()) if proof_state_goal_changed(scratch, &candidate) => {
            *scratch = candidate;
            record_goal_delta(before_goal.as_ref(), scratch.current_goal(), report);
        }
        Ok(()) => {}
        Err(TacticError::NoProgress { .. }) | Err(TacticError::SearchExhausted { .. }) => {}
        Err(err) => return Err(err),
    }

    Ok(())
}

fn run_closeout_normalizer(
    scratch: &mut ProofState,
    report: &mut ProjectMathverseReport,
    tactic: fn(&mut ProofState) -> TacticResult,
) {
    let before_goal = scratch.current_goal().cloned();
    let mut candidate = scratch.clone();
    if tactic(&mut candidate).is_ok() && proof_state_goal_changed(scratch, &candidate) {
        *scratch = candidate;
        record_goal_delta(before_goal.as_ref(), scratch.current_goal(), report);
    }
}

fn run_cast_rewrite_pass(
    scratch: &mut ProofState,
    report: &mut ProjectMathverseReport,
    flavor: CastRewriteFlavor,
    nat_coercion: bool,
) -> Result<(), TacticError> {
    let before_goal = scratch.current_goal().cloned();
    let target_rewrites =
        rewrite_target_with_cast_lemmas(scratch, "cert_mathverse", flavor).map(usize::from)?;
    let local_rewrites = rewrite_local_decls_with_cast_lemmas(scratch, "cert_mathverse", flavor)?;
    let total_rewrites = target_rewrites + local_rewrites;
    if total_rewrites > 0 {
        record_goal_delta(before_goal.as_ref(), scratch.current_goal(), report);
        if nat_coercion {
            report.nat_coercion_count += total_rewrites;
        }
    }
    Ok(())
}

fn proof_state_goal_changed(before: &ProofState, after: &ProofState) -> bool {
    match (before.current_goal(), after.current_goal()) {
        (Some(before_goal), Some(after_goal)) => {
            before_goal.target != after_goal.target
                || before_goal.local_ctx.len() != after_goal.local_ctx.len()
                || before_goal
                    .local_ctx
                    .iter()
                    .zip(after_goal.local_ctx.iter())
                    .any(|(old, new)| {
                        old.name != new.name || old.ty != new.ty || old.value != new.value
                    })
        }
        (Some(_), None) => true,
        (None, Some(_)) => true,
        (None, None) => false,
    }
}

fn record_goal_delta(
    before: Option<&Goal>,
    after: Option<&Goal>,
    report: &mut ProjectMathverseReport,
) {
    let (Some(before), Some(after)) = (before, after) else {
        report.normalized_target_changed = true;
        return;
    };
    report.normalized_target_changed |= before.target != after.target;
    report.normalized_hyp_count += before
        .local_ctx
        .iter()
        .zip(after.local_ctx.iter())
        .filter(|(old, new)| old.ty != new.ty)
        .count();
    report.normalized_hyp_count += before.local_ctx.len().abs_diff(after.local_ctx.len());
}

fn append_missing_nat_sub_side_condition_support(
    report: &mut ProjectMathverseReport,
    blocker_limit: usize,
) {
    if report.blockers.len() >= blocker_limit {
        return;
    }
    let Some(mut blocker) = report
        .blockers
        .iter()
        .find(|blocker| blocker.kind == MathverseBlockerKind::NatSubWithoutSideCondition)
        .cloned()
    else {
        return;
    };
    blocker.kind = MathverseBlockerKind::MissingRewriteLemma;
    blocker.suggestion = suggestion_for(MathverseBlockerKind::MissingRewriteLemma);
    report.blockers.push(blocker);
}

fn append_cert_simp_blockers(
    candidate: &ProofState,
    report: &mut ProjectMathverseReport,
    blocker_limit: usize,
) {
    if report.blockers.len() >= blocker_limit {
        return;
    }
    let should_report = report.parsed_constraint_count == 0
        || report.blockers.iter().any(|blocker| {
            matches!(
                blocker.kind,
                MathverseBlockerKind::NoParseableConstraint | MathverseBlockerKind::UnsupportedHead
            )
        });
    if !should_report {
        return;
    }

    for head in cert_simp_blocker_heads(candidate, blocker_limit - report.blockers.len()) {
        if report
            .blockers
            .iter()
            .any(|blocker| blocker.head.as_deref() == Some(head.as_str()))
        {
            continue;
        }
        report.blockers.push(MathverseBlocker {
            origin: BlockerOrigin::Target,
            kind: MathverseBlockerKind::MissingRewriteLemma,
            unsimplified: head.clone(),
            normalized: None,
            head: Some(head),
            suggestion: suggestion_for(MathverseBlockerKind::MissingRewriteLemma),
        });
        if report.blockers.len() >= blocker_limit {
            break;
        }
    }
}

fn merge_failure_reports(
    mut failures: Vec<ProjectMathverseReport>,
    blocker_limit: usize,
) -> ProjectMathverseReport {
    let Some(mut primary) = failures.pop() else {
        return ProjectMathverseReport::default();
    };

    for failure in failures {
        primary.normalized_target_changed |= failure.normalized_target_changed;
        primary.normalized_hyp_count = primary
            .normalized_hyp_count
            .max(failure.normalized_hyp_count);
        primary.parsed_constraint_count = primary
            .parsed_constraint_count
            .max(failure.parsed_constraint_count);
        primary.nat_coercion_count = primary.nat_coercion_count.max(failure.nat_coercion_count);
        primary.synthetic_fact_count = primary
            .synthetic_fact_count
            .max(failure.synthetic_fact_count);
        for blocker in failure.blockers {
            if primary.blockers.len() >= blocker_limit {
                break;
            }
            if !primary.blockers.iter().any(|existing| {
                existing.kind == blocker.kind
                    && existing.origin == blocker.origin
                    && existing.unsimplified == blocker.unsimplified
            }) {
                primary.blockers.push(blocker);
            }
        }
    }

    primary
}

fn collect_diagnostics(
    env: &Environment,
    original: &Goal,
    normalized: &Goal,
    report: &mut ProjectMathverseReport,
    blocker_limit: usize,
) {
    let target = ExprSnapshot {
        origin: BlockerOrigin::Target,
        unsimplified: original.target.clone(),
        normalized: normalized.target.clone(),
    };
    record_snapshot_diagnostic(env, &target, report, blocker_limit);

    for (old, new) in original.local_ctx.iter().zip(normalized.local_ctx.iter()) {
        let snapshot = ExprSnapshot {
            origin: BlockerOrigin::Hypothesis {
                name: old.name.clone(),
            },
            unsimplified: old.ty.clone(),
            normalized: new.ty.clone(),
        };
        record_snapshot_diagnostic(env, &snapshot, report, blocker_limit);
    }

    if report.parsed_constraint_count == 0 && report.blockers.is_empty() {
        report.blockers.push(no_parseable_blocker(
            env,
            BlockerOrigin::Target,
            &original.target,
            &normalized.target,
        ));
    }
}

fn record_snapshot_diagnostic(
    env: &Environment,
    snapshot: &ExprSnapshot,
    report: &mut ProjectMathverseReport,
    blocker_limit: usize,
) {
    // Unfolding `Nat.sub` to `Nat.rec`/`Nat.pred` does not prove its side
    // condition. Preserve the actionable source-level blocker unless the
    // normalized expression is now an actually parseable constraint.
    let diagnostic = if expr_to_mathverse_constraint(&snapshot.normalized, None).is_none()
        && contains_nat_sub(&snapshot.unsimplified)
    {
        DiagnosticClass::Blocked(MathverseBlockerKind::NatSubWithoutSideCondition)
    } else {
        classify_mathverse_expr(&snapshot.normalized)
    };
    match diagnostic {
        DiagnosticClass::Parsed => report.parsed_constraint_count += 1,
        DiagnosticClass::Irrelevant => {}
        DiagnosticClass::Blocked(kind) => {
            if report.blockers.len() < blocker_limit {
                report
                    .blockers
                    .push(make_blocker(env, snapshot.clone(), kind));
            }
        }
    }
}

fn classify_mathverse_expr(expr: &Expr) -> DiagnosticClass {
    if expr_to_mathverse_constraint(expr, None).is_some() {
        return DiagnosticClass::Parsed;
    }
    if contains_nat_sub(expr) {
        return DiagnosticClass::Blocked(MathverseBlockerKind::NatSubWithoutSideCondition);
    }
    if contains_non_linear_mul(expr) {
        return DiagnosticClass::Blocked(MathverseBlockerKind::NonLinearTerm);
    }
    if contains_hmod(expr) {
        return DiagnosticClass::Blocked(MathverseBlockerKind::UnsupportedModulo);
    }
    if contains_unsupported_cast(expr) {
        return DiagnosticClass::Blocked(MathverseBlockerKind::UnsupportedCast);
    }
    if looks_like_arithmetic_prop(expr) {
        return DiagnosticClass::Blocked(MathverseBlockerKind::UnsupportedHead);
    }
    DiagnosticClass::Irrelevant
}

fn has_fatal_blocker(report: &ProjectMathverseReport) -> bool {
    report.blockers.iter().any(|blocker| {
        matches!(
            blocker.kind,
            MathverseBlockerKind::NatSubWithoutSideCondition
                | MathverseBlockerKind::UnsupportedCast
        )
    })
}

fn make_blocker(
    env: &Environment,
    snapshot: ExprSnapshot,
    kind: MathverseBlockerKind,
) -> MathverseBlocker {
    let formatter = ExprFormatter::default();
    let unsimplified = format_expr(&snapshot.unsimplified, env, &formatter);
    let normalized = if snapshot.unsimplified != snapshot.normalized {
        Some(format_expr(&snapshot.normalized, env, &formatter))
    } else {
        None
    };

    MathverseBlocker {
        origin: snapshot.origin,
        kind,
        unsimplified,
        normalized,
        head: expr_head_name(&snapshot.normalized),
        suggestion: suggestion_for(kind),
    }
}

fn no_parseable_blocker(
    env: &Environment,
    origin: BlockerOrigin,
    unsimplified: &Expr,
    normalized: &Expr,
) -> MathverseBlocker {
    make_blocker(
        env,
        ExprSnapshot {
            origin,
            unsimplified: unsimplified.clone(),
            normalized: normalized.clone(),
        },
        MathverseBlockerKind::NoParseableConstraint,
    )
}

fn mathverse_failure_blocker_kind(err: &TacticError) -> MathverseBlockerKind {
    let reason = err.to_string();
    if reason.contains("proof") || reason.contains("certificate") || reason.contains("replay") {
        MathverseBlockerKind::ProofReplayFailed
    } else {
        MathverseBlockerKind::MathverseReturnedSatOrUnknown
    }
}

fn normalization_failure_blocker_kind(err: &TacticError) -> MathverseBlockerKind {
    match err {
        TacticError::EnvironmentMissing { .. } => MathverseBlockerKind::MissingRewriteLemma,
        TacticError::TypeCheckFailed(_) => MathverseBlockerKind::ProofReplayFailed,
        _ => MathverseBlockerKind::UnsupportedHead,
    }
}

fn suggestion_for(kind: MathverseBlockerKind) -> Option<String> {
    let suggestion = match kind {
        MathverseBlockerKind::NatSubWithoutSideCondition => {
            "prove the Nat.sub side condition or rewrite to a linear Int fact"
        }
        MathverseBlockerKind::NonLinearTerm => {
            "split nonlinear multiplication before cert_mathverse"
        }
        MathverseBlockerKind::UnsupportedCast => "add a proof-carrying cast lemma",
        MathverseBlockerKind::UnsupportedModulo => {
            "rewrite modulo to a supported literal congruence"
        }
        MathverseBlockerKind::MissingRewriteLemma => "add the missing project simp lemma",
        MathverseBlockerKind::NoParseableConstraint => {
            "run cert_simp to expose a linear constraint"
        }
        MathverseBlockerKind::ProofReplayFailed => "inspect mathverse proof replay",
        MathverseBlockerKind::MathverseReturnedSatOrUnknown => "add missing hypotheses or bounds",
        MathverseBlockerKind::UnsupportedHead => "normalize the arithmetic proposition first",
    };
    Some(suggestion.to_string())
}

fn expr_head_name(expr: &Expr) -> Option<String> {
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn contains_nat_sub(expr: &Expr) -> bool {
    contains_const_where(expr, &|name| name == "Nat.sub")
}

fn contains_hmod(expr: &Expr) -> bool {
    contains_const_where(expr, &|name| {
        name == "HMod.hMod" || name == "Nat.mod" || name == "Int.mod"
    })
}

fn contains_unsupported_cast(expr: &Expr) -> bool {
    contains_const_where(expr, &|name| {
        name.contains("cast") && !matches!(name, "Int.ofNat" | "Real.ofNat" | "Rat.ofInt")
    })
}

fn contains_non_linear_mul(expr: &Expr) -> bool {
    stack_safe(|| {
        if let ExprKind::App(_, _) = expr.kind() {
            if let Some((lhs, rhs)) =
                binary_operands_if(expr, |name| name.contains("mul") || name.contains("Mul"))
            {
                if extract_constant(&lhs).is_none() && extract_constant(&rhs).is_none() {
                    return true;
                }
            }
        }
        expr_children_any(expr, &contains_non_linear_mul)
    })
}

fn looks_like_arithmetic_prop(expr: &Expr) -> bool {
    contains_const_where(expr, &|name| {
        name.contains("LE.le")
            || name.contains("LT.lt")
            || name.contains("GE.ge")
            || name.contains("GT.gt")
            || name.contains("Eq")
            || name.contains("add")
            || name.contains("sub")
            || name.contains("mul")
    })
}

fn contains_const_where(expr: &Expr, pred: &dyn Fn(&str) -> bool) -> bool {
    stack_safe(|| {
        if let ExprKind::Const(name, _) = expr.get_app_fn().kind() {
            if pred(&name.to_string()) {
                return true;
            }
        }
        expr_children_any(expr, &|child| contains_const_where(child, pred))
    })
}

fn expr_children_any(expr: &Expr, pred: &dyn Fn(&Expr) -> bool) -> bool {
    match expr.kind() {
        ExprKind::App(f, arg) => pred(f) || pred(arg),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => pred(ty) || pred(body),
        ExprKind::Let(_, ty, val, body, _) => pred(ty) || pred(val) || pred(body),
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            pred(inner)
        }
        _ => false,
    }
}

fn binary_operands_if(expr: &Expr, pred: impl Fn(&str) -> bool) -> Option<(Expr, Expr)> {
    let ExprKind::Const(name, _) = expr.get_app_fn().kind() else {
        return None;
    };
    if !pred(&name.to_string()) {
        return None;
    }
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }
    Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()))
}

fn render_project_mathverse_failure(
    report: &ProjectMathverseReport,
    blocker_limit: usize,
) -> String {
    let mut out = String::new();
    match &report.mathverse_result {
        ProjectMathverseOutcome::Closed => out.push_str("closed"),
        ProjectMathverseOutcome::NoProgress => out.push_str("no progress"),
        ProjectMathverseOutcome::MathverseFailed { reason } => {
            write!(out, "mathverse failed: {reason}").expect("infallible: write to String");
        }
        ProjectMathverseOutcome::NormalizationFailed { reason } => {
            write!(out, "normalization failed: {reason}").expect("infallible: write to String");
        }
    }

    let limit = blocker_limit.min(report.blockers.len());
    if limit > 0 {
        out.push_str("; blockers:");
        for blocker in report.blockers.iter().take(limit) {
            write!(
                out,
                " {:?} at {}: {}",
                blocker.kind,
                render_origin(&blocker.origin),
                blocker.unsimplified
            )
            .expect("infallible: write to String");
        }
    }
    out
}

fn render_origin(origin: &BlockerOrigin) -> String {
    match origin {
        BlockerOrigin::Target => "target".to_string(),
        BlockerOrigin::Hypothesis { name } => format!("hypothesis {name}"),
    }
}
