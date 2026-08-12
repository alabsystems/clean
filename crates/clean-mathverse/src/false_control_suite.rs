// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! False-control rejection report vocabulary for release/ingest gating.
//!
//! A "false control" is a deliberately known-bad input that a sound verifier
//! MUST reject. The false-control gate is the anti-vacuity check on every other
//! gate: if the pipeline stopped rejecting bad input, an "accepted" verdict from
//! any other gate is worthless.
//!
//! Both halves are present: the REPORT vocabulary with its replay-readiness
//! accounting, and the PROBE ENGINE ([`run_false_control_suite`]) that actually
//! feeds bad input to the five lanes. A report is replay-ready only when it
//! covers the complete required control set with no duplicates and every
//! control rejected. Callers may still supply a report they produced elsewhere;
//! [`validate_false_control_report_artifact`] re-derives the accounting from the
//! control rows rather than trusting a supplied summary.
//!
//! Read every probe as an inverted test. `Rejected` is the healthy outcome;
//! [`FalseControlStatus::AcceptedBadInput`] is a soundness alarm, and
//! `PendingBackend` / `ProbeError` are blocking because an unrun control is not
//! evidence that bad input would have been rejected.
//!
//! Backend wiring, and one crate-graph constraint worth knowing:
//!
//! - `changed_llvm2_denotation` runs the real cross-validator,
//!   [`clean_c_sem::denotation::validate_denotation_hash`].
//! - `direct_false_proof` runs the real [`clean_kernel::Environment`] type
//!   checker plus its axiom-dependency audit.
//! - `invalid_farkas_multiplier`, `broken_branch_cover` and
//!   `invalid_qbf_strategy` run local fail-closed adapters. They would rather
//!   call `clean_verify`'s `verify_branch_cover` / `verify_qbf_strategy`, but
//!   `clean-verify` depends on `clean-elab`, which depends (behind its
//!   `mathverse-library` feature) on this crate, so a normal dependency edge
//!   from here to `clean-verify` is a Cargo package cycle. `clean-verify` is
//!   therefore a DEV-dependency, and the unit tests below run the real
//!   verifiers on the same known-bad inputs the probes use — the constants are
//!   shared, so probe and verifier cannot drift apart silently. Hoisting those
//!   two backends into a cycle-free crate would let the probes call them
//!   directly.

use std::collections::BTreeSet;
use std::fmt;
use std::path::Path;

use clean_c_sem::denotation::{
    validate_denotation_hash, DenotationHashClaim, TranslationDenotationStep,
};
use clean_kernel::{ConstantKind, Declaration, EnvError, Environment, Expr, ExprKind, Name};
use serde::{Serialize, Serializer};
use serde_json::Value;

use crate::attempt_log::{
    put_artifact, record_authority_gate_attempt, ArtifactRef, AttemptStatus, AuthorityGateAttempt,
    ProofAttempt,
};
use crate::authority_scope::authority_gate_goal_hash;
use crate::env_fingerprint::EnvFingerprint;
use crate::error::{MathverseError, MathverseResult};
use crate::types::TrustLevel;

/// Absolute slack applied to float comparisons inside the probe adapters.
///
/// Matches the tolerance `clean_verify::nn_verify::certificate::branch_cover`
/// uses, so a gap this side of the tolerance is a gap for both.
const EPSILON: f64 = 1e-9;

/// Report contract version.
pub const FALSE_CONTROL_REPORT_SCHEMA_VERSION: &str = "Clean-false-control-report-v1";
/// Stable authority-gate name for false-control evidence.
pub const FALSE_CONTROL_AUTHORITY_GATE: &str = "false_controls";
/// The goal shape this gate attests.
pub const FALSE_CONTROL_GOAL_SHAPE: &str =
    "clean false-control authority gate v2: all scoped bad inputs must be rejected";

/// Artifact kind for the persisted false-control gate report.
pub const FALSE_CONTROL_REPORT_ARTIFACT_KIND: &str = "authority-gate/false-control-report";

/// Logical filename for the persisted false-control gate report.
pub const FALSE_CONTROL_REPORT_ARTIFACT_LOGICAL_NAME: &str = "false-control-report.json";

/// Artifact kind for the replay/command evidence attached to an accepted gate.
const FALSE_CONTROL_COMMAND_EVIDENCE_ARTIFACT_KIND: &str =
    "authority-gate/false-control-command-evidence";

/// Logical filename for the replay/command evidence attached to an accepted gate.
const FALSE_CONTROL_COMMAND_EVIDENCE_LOGICAL_NAME: &str = "false-control-command-evidence.json";

/// One false-control lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FalseControlId {
    /// Invalid Farkas multiplier rejection.
    InvalidFarkasMultiplier,
    /// Broken branch-cover rejection.
    BrokenBranchCover,
    /// Changed LLVM2 denotation rejection.
    ChangedLlvm2Denotation,
    /// Direct proof of `False` rejection/audit.
    DirectFalseProof,
    /// Invalid QBF strategy rejection.
    InvalidQbfStrategy,
}

const ALL_FALSE_CONTROL_IDS: [FalseControlId; 5] = [
    FalseControlId::InvalidFarkasMultiplier,
    FalseControlId::BrokenBranchCover,
    FalseControlId::ChangedLlvm2Denotation,
    FalseControlId::DirectFalseProof,
    FalseControlId::InvalidQbfStrategy,
];

impl FalseControlId {
    /// Canonical false-control set required for accepted replay evidence.
    #[must_use]
    pub fn all() -> &'static [Self] {
        &ALL_FALSE_CONTROL_IDS
    }

    /// Stable machine-readable control identifier.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::InvalidFarkasMultiplier => "invalid_farkas_multiplier",
            Self::BrokenBranchCover => "broken_branch_cover",
            Self::ChangedLlvm2Denotation => "changed_llvm2_denotation",
            Self::DirectFalseProof => "direct_false_proof",
            Self::InvalidQbfStrategy => "invalid_qbf_strategy",
        }
    }

    /// Decode a stable wire identifier.
    #[must_use]
    pub fn from_wire(value: &str) -> Option<Self> {
        match value {
            "invalid_farkas_multiplier" => Some(Self::InvalidFarkasMultiplier),
            "broken_branch_cover" => Some(Self::BrokenBranchCover),
            "changed_llvm2_denotation" => Some(Self::ChangedLlvm2Denotation),
            "direct_false_proof" => Some(Self::DirectFalseProof),
            "invalid_qbf_strategy" => Some(Self::InvalidQbfStrategy),
            _ => None,
        }
    }

    /// Stable description of the known-bad input this lane feeds its backend.
    ///
    /// This string is hashed into
    /// [`FalseControlReplayEvidence::input_hash`], so it is part of the wire
    /// contract: changing the bad input MUST change this description, and
    /// changing this description invalidates previously recorded evidence.
    const fn replay_input_description(self) -> &'static str {
        match self {
            Self::InvalidFarkasMultiplier => {
                "false-control-input-v1:invalid_farkas_multiplier:multipliers=[-1.0]"
            }
            Self::BrokenBranchCover => {
                "false-control-input-v1:broken_branch_cover:domain=[0.0,1.0];branches=[0.0,0.4],[0.6,1.0]"
            }
            Self::ChangedLlvm2Denotation => {
                "false-control-input-v1:changed_llvm2_denotation:actual=LLVM2:i32@f-ret-1=>CleanExpr:CValue.int-1;claim=swapped-ret-0"
            }
            Self::DirectFalseProof => {
                "false-control-input-v1:direct_false_proof:True.intro-as-False;axiom-backed-False-theorem"
            }
            Self::InvalidQbfStrategy => {
                "false-control-input-v1:invalid_qbf_strategy:forall-u-exists-e:iff(e,u);strategy=e=false"
            }
        }
    }
}

impl fmt::Display for FalseControlId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Outcome for one control.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FalseControlStatus {
    /// Bad input was rejected by the relevant verifier/audit.
    Rejected,
    /// Bad input was accepted; this is a release-blocking failure.
    AcceptedBadInput,
    /// No sound backend hook is available yet.
    PendingBackend,
    /// The control probe itself failed before it could test rejection.
    ProbeError,
}

impl FalseControlStatus {
    /// Stable machine-readable status spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Rejected => "rejected",
            Self::AcceptedBadInput => "accepted_bad_input",
            Self::PendingBackend => "pending_backend",
            Self::ProbeError => "probe_error",
        }
    }

    /// Decode a stable wire status.
    #[must_use]
    pub fn from_wire(value: &str) -> Option<Self> {
        match value {
            "rejected" => Some(Self::Rejected),
            "accepted_bad_input" => Some(Self::AcceptedBadInput),
            "pending_backend" => Some(Self::PendingBackend),
            "probe_error" => Some(Self::ProbeError),
            _ => None,
        }
    }
}

/// Stable per-control replay evidence emitted into report artifacts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FalseControlReplayEvidence {
    /// BLAKE3 hash of the known-bad input shape for this control.
    pub input_hash: String,
    /// BLAKE3 hash of the observed control result.
    pub result_hash: String,
    /// Stable replay diagnostic detail.
    pub detail: String,
}

/// Result for one false-control lane.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FalseControlResult {
    /// Stable control identifier.
    pub id: FalseControlId,
    /// Human-readable control name.
    pub label: &'static str,
    /// Probe outcome.
    pub status: FalseControlStatus,
    /// Diagnostic detail.
    pub detail: String,
    /// TODO or backend gap, when pending.
    pub todo: Option<&'static str>,
}

impl Serialize for FalseControlResult {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[derive(Serialize)]
        struct WireResult<'a> {
            id: FalseControlId,
            label: &'static str,
            status: FalseControlStatus,
            detail: &'a str,
            todo: Option<&'static str>,
            replay_evidence: FalseControlReplayEvidence,
        }

        WireResult {
            id: self.id,
            label: self.label,
            status: self.status,
            detail: &self.detail,
            todo: self.todo,
            replay_evidence: self.replay_evidence(),
        }
        .serialize(serializer)
    }
}

impl FalseControlResult {
    /// Stable replay evidence for this control result.
    #[must_use]
    pub fn replay_evidence(&self) -> FalseControlReplayEvidence {
        false_control_replay_evidence(self.id, self.status, &self.detail, self.todo)
    }

    fn rejected(id: FalseControlId, label: &'static str, detail: impl Into<String>) -> Self {
        Self {
            id,
            label,
            status: FalseControlStatus::Rejected,
            detail: detail.into(),
            todo: None,
        }
    }

    fn accepted_bad_input(
        id: FalseControlId,
        label: &'static str,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            id,
            label,
            status: FalseControlStatus::AcceptedBadInput,
            detail: detail.into(),
            todo: None,
        }
    }

    #[cfg(test)]
    fn pending(
        id: FalseControlId,
        label: &'static str,
        detail: impl Into<String>,
        todo: &'static str,
    ) -> Self {
        Self {
            id,
            label,
            status: FalseControlStatus::PendingBackend,
            detail: detail.into(),
            todo: Some(todo),
        }
    }

    fn probe_error(id: FalseControlId, label: &'static str, detail: impl Into<String>) -> Self {
        Self {
            id,
            label,
            status: FalseControlStatus::ProbeError,
            detail: detail.into(),
            todo: None,
        }
    }
}

/// Deterministic replay-readiness summary for false-control gate output.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FalseControlReplaySummary {
    /// Total controls in the report.
    pub total: usize,
    /// Total controls required by this Clean release.
    pub expected_total: usize,
    /// Controls that correctly rejected bad input.
    pub rejected: usize,
    /// Controls waiting on backend hooks.
    pub pending: usize,
    /// Controls that accepted known-bad input.
    pub accepted_bad_input: usize,
    /// Controls whose probes failed before testing rejection.
    pub probe_errors: usize,
    /// Stable ids for every control that did not reject its bad input.
    pub non_rejected_control_ids: Vec<&'static str>,
    /// Required controls missing from the report.
    pub missing_control_ids: Vec<&'static str>,
    /// Required controls repeated in the report.
    pub duplicate_control_ids: Vec<&'static str>,
    /// Whether this report is ready to serve as replay gate evidence.
    pub replay_ready: bool,
}

impl FalseControlReplaySummary {
    fn from_controls(controls: &[FalseControlResult]) -> Self {
        let rejected = controls
            .iter()
            .filter(|control| control.status == FalseControlStatus::Rejected)
            .count();
        let pending = controls
            .iter()
            .filter(|control| control.status == FalseControlStatus::PendingBackend)
            .count();
        let accepted_bad_input = controls
            .iter()
            .filter(|control| control.status == FalseControlStatus::AcceptedBadInput)
            .count();
        let probe_errors = controls
            .iter()
            .filter(|control| control.status == FalseControlStatus::ProbeError)
            .count();
        let non_rejected_control_ids = controls
            .iter()
            .filter(|control| control.status != FalseControlStatus::Rejected)
            .map(|control| control.id.as_str())
            .collect();
        let diagnostics = false_control_set_diagnostics(controls.iter().map(|control| control.id));
        let complete_control_set = diagnostics.is_complete();

        Self {
            total: controls.len(),
            expected_total: FalseControlId::all().len(),
            rejected,
            pending,
            accepted_bad_input,
            probe_errors,
            non_rejected_control_ids,
            missing_control_ids: diagnostics.missing_control_ids,
            duplicate_control_ids: diagnostics.duplicate_control_ids,
            replay_ready: complete_control_set && rejected == controls.len(),
        }
    }
}

/// Aggregate false-control report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FalseControlReport {
    /// Individual controls in deterministic order.
    pub controls: Vec<FalseControlResult>,
}

impl Serialize for FalseControlReport {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[derive(Serialize)]
        struct WireReport<'a> {
            schema_version: &'static str,
            summary: FalseControlReplaySummary,
            controls: &'a [FalseControlResult],
        }

        WireReport {
            schema_version: FALSE_CONTROL_REPORT_SCHEMA_VERSION,
            summary: self.replay_summary(),
            controls: &self.controls,
        }
        .serialize(serializer)
    }
}

impl FalseControlReport {
    /// Deterministic machine-readable replay-readiness summary.
    #[must_use]
    pub fn replay_summary(&self) -> FalseControlReplaySummary {
        FalseControlReplaySummary::from_controls(&self.controls)
    }

    /// Number of controls that correctly rejected bad input.
    #[must_use]
    pub fn rejected_count(&self) -> usize {
        self.replay_summary().rejected
    }

    /// Number of controls waiting on a backend hook.
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.replay_summary().pending
    }

    /// Number of controls whose known-bad input was accepted.
    #[must_use]
    pub fn accepted_bad_input_count(&self) -> usize {
        self.replay_summary().accepted_bad_input
    }

    /// Number of controls whose probe failed before testing rejection.
    #[must_use]
    pub fn probe_error_count(&self) -> usize {
        self.replay_summary().probe_errors
    }

    /// Controls that did NOT reject their bad input, for any reason.
    ///
    /// Pending and probe-error controls are blocking: an unrun control is not
    /// evidence that bad input would have been rejected.
    #[must_use]
    pub fn blocking_controls(&self) -> Vec<&FalseControlResult> {
        self.controls
            .iter()
            .filter(|control| control.status != FalseControlStatus::Rejected)
            .collect()
    }

    /// Controls whose bad input was accepted or whose probe failed.
    #[must_use]
    pub fn failing_controls(&self) -> Vec<&FalseControlResult> {
        self.controls
            .iter()
            .filter(|control| {
                matches!(
                    control.status,
                    FalseControlStatus::AcceptedBadInput | FalseControlStatus::ProbeError
                )
            })
            .collect()
    }

    /// Whether every control is fully green.
    ///
    /// Green means the complete required control set is present exactly once
    /// AND every control rejected its bad input; a partial report is never
    /// green, however many of its rows say `rejected`.
    #[must_use]
    pub fn all_controls_rejected(&self) -> bool {
        self.replay_summary().replay_ready
    }

    /// Fail closed unless the report has every required control exactly once.
    pub fn validate_complete_control_set(&self) -> MathverseResult<()> {
        let controls = self
            .controls
            .iter()
            .map(|control| (control.id, control.status))
            .collect::<Vec<_>>();
        validate_required_control_set(&controls)
    }
}

/// Validated contents of a persisted false-control report artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FalseControlReportArtifactValidation {
    /// Report replay-readiness summary reconstructed from control rows.
    pub summary: FalseControlReplaySummary,
    /// Failure mode expected when the corresponding attempt is rejected.
    pub expected_failure_mode: Option<String>,
}

/// Validate a persisted false-control report artifact and reconstruct its summary.
///
/// The summary carried by the artifact is never trusted: it is recomputed from
/// the control rows and compared, and every row's replay evidence is
/// recomputed and compared too. An artifact whose summary flatters its rows is
/// rejected rather than believed.
pub fn validate_false_control_report_artifact(
    bytes: &[u8],
) -> MathverseResult<FalseControlReportArtifactValidation> {
    let value: Value = serde_json::from_slice(bytes)?;
    let object = value
        .as_object()
        .ok_or_else(|| kernel_error("false-control report artifact must be a JSON object"))?;
    let schema_version = object
        .get("schema_version")
        .and_then(Value::as_str)
        .ok_or_else(|| kernel_error("false-control report artifact is missing schema_version"))?;
    if schema_version != FALSE_CONTROL_REPORT_SCHEMA_VERSION {
        return Err(kernel_error(format!(
            "unsupported false-control report schema_version `{schema_version}`"
        )));
    }
    let controls = object
        .get("controls")
        .and_then(Value::as_array)
        .ok_or_else(|| kernel_error("false-control report artifact is missing controls"))?;

    let mut parsed = Vec::with_capacity(controls.len());
    for (index, control) in controls.iter().enumerate() {
        let control = control
            .as_object()
            .ok_or_else(|| kernel_error(format!("control {index} must be a JSON object")))?;
        let id = control
            .get("id")
            .and_then(Value::as_str)
            .and_then(FalseControlId::from_wire)
            .ok_or_else(|| kernel_error(format!("control {index} has unknown id")))?;
        let status = control
            .get("status")
            .and_then(Value::as_str)
            .and_then(FalseControlStatus::from_wire)
            .ok_or_else(|| kernel_error(format!("control {index} has unknown status")))?;
        let detail = control
            .get("detail")
            .and_then(Value::as_str)
            .ok_or_else(|| kernel_error(format!("control {index} is missing detail")))?;
        let todo = match control.get("todo") {
            None | Some(Value::Null) => None,
            Some(Value::String(value)) => Some(value.as_str()),
            _ => return Err(kernel_error(format!("control {index} has non-string todo"))),
        };
        let expected_evidence = false_control_replay_evidence(id, status, detail, todo);
        let expected_evidence_value = serde_json::to_value(&expected_evidence)?;
        let actual_evidence = control.get("replay_evidence").ok_or_else(|| {
            kernel_error(format!(
                "control {} is missing replay_evidence",
                id.as_str()
            ))
        })?;
        if actual_evidence != &expected_evidence_value {
            return Err(kernel_error(format!(
                "control {} replay_evidence mismatch",
                id.as_str()
            )));
        }
        parsed.push((id, status));
    }
    validate_required_control_set(&parsed)?;

    let summary = replay_summary_from_wire_controls(&parsed);
    let expected_summary = serde_json::to_value(&summary)?;
    let actual_summary = object
        .get("summary")
        .ok_or_else(|| kernel_error("false-control report artifact is missing summary"))?;
    if actual_summary != &expected_summary {
        return Err(kernel_error(
            "false-control report summary does not match control rows",
        ));
    }

    let expected_failure_mode = if summary.replay_ready {
        None
    } else {
        Some(false_control_failure_mode_from_summary(&summary))
    };
    Ok(FalseControlReportArtifactValidation {
        summary,
        expected_failure_mode,
    })
}

// ────────────────────────────────────────────────────────────────────────────
// Probe engine
// ────────────────────────────────────────────────────────────────────────────

/// Run all known false-control probes.
///
/// Every lane feeds its backend an input that is known to be wrong, so a
/// healthy run returns five [`FalseControlStatus::Rejected`] rows. Treat any
/// other status as a finding, not as a passing test.
#[must_use]
pub fn run_false_control_suite() -> FalseControlReport {
    FalseControlReport {
        controls: vec![
            run_invalid_farkas_multiplier_control(),
            run_broken_branch_cover_control(),
            run_changed_llvm2_denotation_control(),
            run_direct_false_control(),
            run_invalid_qbf_strategy_control(),
        ],
    }
}

/// Known-bad Farkas certificate: a negative multiplier.
///
/// Farkas combinations must be non-negative, so a `-1.0` coefficient cannot
/// come from a sound certificate.
const INVALID_FARKAS_MULTIPLIERS: [f64; 1] = [-1.0];

/// Known-bad branch cover: `[0.0, 1.0]` with the slice `(0.4, 0.6)` missing.
const BROKEN_BRANCH_COVER_DOMAIN: (f64, f64) = (0.0, 1.0);

/// Branch boxes of the known-bad cover, leaving a hole far wider than [`EPSILON`].
const BROKEN_BRANCH_COVER_BRANCHES: [(f64, f64); 2] = [(0.0, 0.4), (0.6, 1.0)];

/// Universal variable of the known-bad QBF probe.
const QBF_UNIVERSAL_VAR: &str = "u";

/// Existential variable of the known-bad QBF probe.
const QBF_EXISTENTIAL_VAR: &str = "e";

/// Output of the known-bad constant Skolem function for [`QBF_EXISTENTIAL_VAR`].
const QBF_CONSTANT_FALSE_STRATEGY_OUTPUT: bool = false;

fn run_invalid_farkas_multiplier_control() -> FalseControlResult {
    let label = "invalid Farkas multiplier";

    if has_negative_farkas_multiplier(&INVALID_FARKAS_MULTIPLIERS) {
        FalseControlResult::rejected(
            FalseControlId::InvalidFarkasMultiplier,
            label,
            "local adapter rejected negative multiplier precondition",
        )
    } else {
        FalseControlResult::accepted_bad_input(
            FalseControlId::InvalidFarkasMultiplier,
            label,
            "negative multiplier certificate was accepted by local adapter",
        )
    }
}

fn run_broken_branch_cover_control() -> FalseControlResult {
    let label = "broken branch cover";
    let domain = Interval1d::new(BROKEN_BRANCH_COVER_DOMAIN.0, BROKEN_BRANCH_COVER_DOMAIN.1);
    let branches = BROKEN_BRANCH_COVER_BRANCHES.map(|(lower, upper)| Interval1d::new(lower, upper));

    match first_uncovered_branch_witness(domain, &branches) {
        Some(witness) => FalseControlResult::rejected(
            FalseControlId::BrokenBranchCover,
            label,
            format!("local adapter rejected uncovered witness {witness}"),
        ),
        None => FalseControlResult::accepted_bad_input(
            FalseControlId::BrokenBranchCover,
            label,
            "gap cover was accepted by local adapter",
        ),
    }
}

fn run_changed_llvm2_denotation_control() -> FalseControlResult {
    let label = "changed LLVM2 denotation";
    let actual = TranslationDenotationStep::new(
        "llvm2-to-clean",
        "LLVM2",
        "define i32 @f() { entry: ret i32 1 }",
        "CleanExpr",
        "CValue.int 1",
    );
    let swapped = TranslationDenotationStep::new(
        "llvm2-to-clean",
        "LLVM2",
        "define i32 @f() { entry: ret i32 0 }",
        "CleanExpr",
        "CValue.int 0",
    );
    let bad_claim = DenotationHashClaim::new(actual.phase(), swapped.hash());

    match validate_denotation_hash(&actual, &bad_claim) {
        Ok(()) => FalseControlResult::accepted_bad_input(
            FalseControlId::ChangedLlvm2Denotation,
            label,
            "swapped LLVM2 denotation hash was accepted by local cross-validator",
        ),
        Err(err) => FalseControlResult::rejected(
            FalseControlId::ChangedLlvm2Denotation,
            label,
            format!("local denotation cross-validator rejected swapped hash: {err}"),
        ),
    }
}

fn run_direct_false_control() -> FalseControlResult {
    let label = "direct proof of False";
    match direct_false_probe() {
        Ok(detail) => FalseControlResult::rejected(FalseControlId::DirectFalseProof, label, detail),
        Err(DirectFalseProbeError::AcceptedBadTerm) => FalseControlResult::accepted_bad_input(
            FalseControlId::DirectFalseProof,
            label,
            "True.intro was accepted as a proof of False",
        ),
        Err(err) => FalseControlResult::probe_error(
            FalseControlId::DirectFalseProof,
            label,
            err.to_string(),
        ),
    }
}

fn run_invalid_qbf_strategy_control() -> FalseControlResult {
    let label = "invalid QBF strategy";
    match first_losing_universal_assignment() {
        Some(universal) => FalseControlResult::rejected(
            FalseControlId::InvalidQbfStrategy,
            label,
            format!(
                "local adapter rejected losing branch [(\"{QBF_UNIVERSAL_VAR}\", {universal})]: \
                 strategy answered {QBF_EXISTENTIAL_VAR}={QBF_CONSTANT_FALSE_STRATEGY_OUTPUT}"
            ),
        ),
        None => FalseControlResult::accepted_bad_input(
            FalseControlId::InvalidQbfStrategy,
            label,
            "losing strategy was accepted after checking every universal assignment",
        ),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Probe adapters
// ────────────────────────────────────────────────────────────────────────────

/// Whether any multiplier is negative beyond the float tolerance.
fn has_negative_farkas_multiplier(multipliers: &[f64]) -> bool {
    multipliers.iter().any(|multiplier| *multiplier < -EPSILON)
}

/// One closed interval `[lower, upper]` on a single axis.
///
/// The one-dimensional shadow of
/// `clean_verify::nn_verify::certificate::branch_cover::NumericInterval`; see
/// the module docs for why the probe cannot use that type directly.
#[derive(Debug, Clone, Copy)]
struct Interval1d {
    lower: f64,
    upper: f64,
}

impl Interval1d {
    const fn new(lower: f64, upper: f64) -> Self {
        Self { lower, upper }
    }

    fn contains(self, value: f64) -> bool {
        value >= self.lower - EPSILON && value <= self.upper + EPSILON
    }
}

/// First point of `domain` that no branch covers, if any.
///
/// Every branch bound is a breakpoint, so any hole between two branches is a
/// whole cell of the induced partition and its midpoint witnesses the hole.
/// Fail-closed by construction: an uncovered midpoint is always reported, and
/// only a genuinely complete cover yields `None`.
fn first_uncovered_branch_witness(domain: Interval1d, branches: &[Interval1d]) -> Option<f64> {
    let mut bounds = vec![domain.lower, domain.upper];
    for branch in branches {
        bounds.push(branch.lower);
        bounds.push(branch.upper);
    }
    bounds.sort_by(f64::total_cmp);
    bounds.dedup_by(|lhs, rhs| (*lhs - *rhs).abs() <= EPSILON);

    bounds.windows(2).find_map(|pair| {
        let witness = f64::midpoint(pair[0], pair[1]);
        if domain.contains(witness) && !branches.iter().any(|branch| branch.contains(witness)) {
            Some(witness)
        } else {
            None
        }
    })
}

/// First universal value on which the known-bad QBF strategy loses, if any.
///
/// The probe formula is the "copy" QBF `∀u. ∃e. (e ↔ u)`, whose only winning
/// Skolem function for `e` is the identity on `u`. The probe strategy answers
/// the constant [`QBF_CONSTANT_FALSE_STRATEGY_OUTPUT`] regardless of `u`, so
/// the matrix `e ↔ u` is falsified exactly on the universal values that differ
/// from that constant — here `u = true`. The whole `2^1` universal space is
/// enumerated, so this is exhaustive for the probe input; it is not a general
/// QBF strategy verifier. The general verifier is
/// `clean_verify::qbf_verify::strategy::verify_qbf_strategy`, which the tests
/// below run on the same formula/strategy pair.
fn first_losing_universal_assignment() -> Option<bool> {
    [false, true]
        .into_iter()
        .find(|universal| *universal != QBF_CONSTANT_FALSE_STRATEGY_OUTPUT)
}

/// Failures of the direct-`False` probe.
///
/// [`Self::AcceptedBadTerm`] is the soundness alarm; every other variant means
/// the probe could not be run, which is blocking but not a kernel finding.
#[derive(Debug, thiserror::Error)]
enum DirectFalseProbeError {
    /// `True`/`False` could not be registered, so nothing could be probed.
    #[error("True/False initialization failed: {0}")]
    Init(#[from] EnvError),
    /// The kernel accepted `True.intro` as a proof of `False`.
    #[error("bad proof term was accepted")]
    AcceptedBadTerm,
    /// The synthetic `False` axiom could not be registered.
    #[error("synthetic False axiom registration failed: {0}")]
    Axiom(EnvError),
    /// The axiom-backed `False` theorem could not be registered.
    #[error("axiom-backed False theorem registration failed: {0}")]
    Theorem(EnvError),
    /// The axiom audit failed to attribute the theorem to its axiom.
    #[error("False theorem audit did not flag dependency {dependency}")]
    MissingAuditDependency {
        /// Axiom the theorem provably depends on.
        dependency: Name,
    },
}

/// Feed the kernel a proof of `False` and require it to be rejected.
///
/// Two things are probed, both fail-closed:
///
/// 1. `True.intro : False` must NOT type-check. Acceptance is
///    [`DirectFalseProbeError::AcceptedBadTerm`].
/// 2. A theorem whose proof term is an added `False` axiom must still be
///    ATTRIBUTED to that axiom by the audit, and must be visible to the
///    `False`-theorem census. A silent audit is as dangerous as a bad accept,
///    so a missing dependency is an error, not a pass.
fn direct_false_probe() -> Result<String, DirectFalseProbeError> {
    let mut env = Environment::new();
    env.init_true_false()?;

    let false_type = Expr::const_str("False");
    let malformed_name = Name::from_string("FalseControlSuite.bad_true_intro_as_false");
    let malformed = env.add_decl(Declaration::Theorem {
        name: malformed_name,
        level_params: vec![],
        type_: false_type.clone(),
        value: Expr::const_str("True.intro"),
    });
    if malformed.is_ok() {
        return Err(DirectFalseProbeError::AcceptedBadTerm);
    }

    let axiom_name = Name::from_string("FalseControlSuite.false_axiom");
    env.add_decl(Declaration::Axiom {
        name: axiom_name.clone(),
        level_params: vec![],
        type_: false_type.clone(),
    })
    .map_err(DirectFalseProbeError::Axiom)?;

    let theorem_name = Name::from_string("FalseControlSuite.bad_false_theorem");
    env.add_decl(Declaration::Theorem {
        name: theorem_name.clone(),
        level_params: vec![],
        type_: false_type,
        value: Expr::const_(axiom_name.clone(), vec![]),
    })
    .map_err(DirectFalseProbeError::Theorem)?;

    let deps = env.axiom_deps(&theorem_name).unwrap_or_default();
    if deps.contains(&axiom_name) && false_theorem_names(&env).contains(&theorem_name) {
        Ok(format!(
            "bad proof term rejected and axiom-backed False theorem depends on {axiom_name}"
        ))
    } else {
        Err(DirectFalseProbeError::MissingAuditDependency {
            dependency: axiom_name,
        })
    }
}

/// Names of every theorem in `env` whose statement is exactly `False`.
fn false_theorem_names(env: &Environment) -> Vec<Name> {
    env.constants()
        .filter(|constant| constant.kind == ConstantKind::Theorem)
        .filter(|constant| {
            matches!(
                constant.type_.kind(),
                ExprKind::Const(name, levels) if name.to_string() == "False" && levels.is_empty()
            )
        })
        .map(|constant| constant.name.clone())
        .collect()
}

// ────────────────────────────────────────────────────────────────────────────
// Authority-gate evidence plumbing
// ────────────────────────────────────────────────────────────────────────────

/// Record a false-control report as an append-only authority-gate proof attempt.
///
/// Refuses to record an incomplete or duplicated control set at all: a partial
/// report must not become gate evidence even as a rejection row.
pub fn record_false_control_authority_gate_attempt(
    root: impl AsRef<Path>,
    report: &FalseControlReport,
    wall_time_ms: u64,
) -> MathverseResult<ProofAttempt> {
    let root = root.as_ref();
    report.validate_complete_control_set()?;
    let env = EnvFingerprint::capture(root)?;
    let report_json = serde_json::to_vec_pretty(report)?;
    let report_artifact = put_artifact(
        root,
        &report_json,
        Some(FALSE_CONTROL_REPORT_ARTIFACT_KIND),
        Some(FALSE_CONTROL_REPORT_ARTIFACT_LOGICAL_NAME),
    )?;
    let goal_hash = false_control_authority_goal_hash(root, report)?;
    let mut attempt =
        build_false_control_authority_gate_attempt(report, env, wall_time_ms, goal_hash)?;
    attempt.trust_audit_hash = report_artifact.blake3.clone();
    attempt.solver_artifact = Some(report_artifact);
    if report.all_controls_rejected() {
        attempt.trust_level = Some(TrustLevel::KernelVerified);
        attempt.command_evidence = Some(false_control_command_evidence(
            root,
            report,
            &attempt.goal_hash,
            &attempt.trust_audit_hash,
        )?);
    }
    record_authority_gate_attempt(root, attempt)
}

fn false_control_command_evidence(
    root: &Path,
    report: &FalseControlReport,
    goal_hash: &str,
    trust_audit_hash: &str,
) -> MathverseResult<ArtifactRef> {
    let control_ids = report
        .controls
        .iter()
        .map(|control| control.id.as_str())
        .collect::<Vec<_>>();
    let evidence = serde_json::json!({
        "schema_version": "clean.false-control-command-evidence.v1",
        "authority_gate": FALSE_CONTROL_AUTHORITY_GATE,
        "replay": {
            "kind": "in_process_false_control_suite",
            "function": "run_false_control_suite",
            "controls": control_ids,
        },
        "goal_hash": goal_hash,
        "report_hash": trust_audit_hash,
    });
    let bytes = serde_json::to_vec_pretty(&evidence)?;
    put_artifact(
        root,
        &bytes,
        Some(FALSE_CONTROL_COMMAND_EVIDENCE_ARTIFACT_KIND),
        Some(FALSE_CONTROL_COMMAND_EVIDENCE_LOGICAL_NAME),
    )
}

/// Goal hash for a project-scoped false-control authority-gate report.
pub fn false_control_authority_goal_hash(
    root: impl AsRef<Path>,
    report: &FalseControlReport,
) -> MathverseResult<String> {
    let mut ids = report
        .controls
        .iter()
        .map(|control| control.id.as_str())
        .collect::<Vec<_>>();
    ids.sort_unstable();
    ids.dedup();
    authority_gate_goal_hash(
        root,
        FALSE_CONTROL_AUTHORITY_GATE,
        &false_control_goal_scope(&ids),
    )
}

/// Expected project-scoped goal hash for a complete false-control report.
pub fn false_control_expected_authority_goal_hash(
    root: impl AsRef<Path>,
) -> MathverseResult<String> {
    let mut ids = FalseControlId::all()
        .iter()
        .map(|id| id.as_str())
        .collect::<Vec<_>>();
    ids.sort_unstable();
    authority_gate_goal_hash(
        root,
        FALSE_CONTROL_AUTHORITY_GATE,
        &false_control_goal_scope(&ids),
    )
}

fn false_control_goal_scope(ids: &[&str]) -> String {
    format!("{};controls={}", FALSE_CONTROL_GOAL_SHAPE, ids.join(","))
}

fn build_false_control_authority_gate_attempt(
    report: &FalseControlReport,
    env: EnvFingerprint,
    wall_time_ms: u64,
    goal_hash: String,
) -> MathverseResult<AuthorityGateAttempt> {
    let report_json = serde_json::to_vec(report)?;
    let status = if report.all_controls_rejected() {
        AttemptStatus::Accepted
    } else {
        AttemptStatus::Rejected {
            reason: false_control_rejection_reason(report),
        }
    };
    let mut attempt = AuthorityGateAttempt::new(
        FALSE_CONTROL_AUTHORITY_GATE,
        goal_hash,
        status,
        blake3_hex(&report_json),
        env,
    );
    attempt.wall_time_ms = wall_time_ms;
    if !report.all_controls_rejected() {
        attempt.failure_mode = Some(false_control_failure_mode(report));
    }
    Ok(attempt)
}

fn false_control_rejection_reason(report: &FalseControlReport) -> String {
    let summary = report.replay_summary();
    format!(
        "false-control suite blocked: {}/{} rejected (expected {} controls), {} pending, {} accepted_bad_input, {} probe_errors; non_rejected=[{}]; missing=[{}]; duplicate=[{}]",
        summary.rejected,
        summary.total,
        summary.expected_total,
        summary.pending,
        summary.accepted_bad_input,
        summary.probe_errors,
        summary.non_rejected_control_ids.join(", "),
        summary.missing_control_ids.join(", "),
        summary.duplicate_control_ids.join(", ")
    )
}

fn false_control_failure_mode(report: &FalseControlReport) -> String {
    let summary = report.replay_summary();
    false_control_failure_mode_from_summary(&summary)
}

fn false_control_failure_mode_from_summary(summary: &FalseControlReplaySummary) -> String {
    if !summary.missing_control_ids.is_empty() || !summary.duplicate_control_ids.is_empty() {
        "false_control_incomplete_control_set".to_owned()
    } else if summary.accepted_bad_input > 0 {
        "false_control_accepted_bad_input".to_owned()
    } else if summary.probe_errors > 0 {
        "false_control_probe_error".to_owned()
    } else if summary.pending > 0 {
        "false_control_pending_backend".to_owned()
    } else {
        "false_control_blocking_controls".to_owned()
    }
}

fn blake3_hex(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

fn false_control_replay_evidence(
    id: FalseControlId,
    status: FalseControlStatus,
    detail: &str,
    todo: Option<&str>,
) -> FalseControlReplayEvidence {
    let input_hash = blake3_hex(id.replay_input_description().as_bytes());
    let result_hash = blake3_hex(
        format!(
            "false-control-result-v1\nid={}\nstatus={}\ninput_hash={}\ndetail={}\ntodo={}\n",
            id.as_str(),
            status.as_str(),
            input_hash,
            detail,
            todo.unwrap_or("")
        )
        .as_bytes(),
    );
    FalseControlReplayEvidence {
        input_hash,
        result_hash,
        detail: detail.to_owned(),
    }
}

fn replay_summary_from_wire_controls(
    controls: &[(FalseControlId, FalseControlStatus)],
) -> FalseControlReplaySummary {
    let rejected = controls
        .iter()
        .filter(|(_, status)| *status == FalseControlStatus::Rejected)
        .count();
    let pending = controls
        .iter()
        .filter(|(_, status)| *status == FalseControlStatus::PendingBackend)
        .count();
    let accepted_bad_input = controls
        .iter()
        .filter(|(_, status)| *status == FalseControlStatus::AcceptedBadInput)
        .count();
    let probe_errors = controls
        .iter()
        .filter(|(_, status)| *status == FalseControlStatus::ProbeError)
        .count();
    let non_rejected_control_ids = controls
        .iter()
        .filter(|(_, status)| *status != FalseControlStatus::Rejected)
        .map(|(id, _)| id.as_str())
        .collect();
    let diagnostics = false_control_set_diagnostics(controls.iter().map(|(id, _)| *id));
    let complete_control_set = diagnostics.is_complete();
    FalseControlReplaySummary {
        total: controls.len(),
        expected_total: FalseControlId::all().len(),
        rejected,
        pending,
        accepted_bad_input,
        probe_errors,
        non_rejected_control_ids,
        missing_control_ids: diagnostics.missing_control_ids,
        duplicate_control_ids: diagnostics.duplicate_control_ids,
        replay_ready: complete_control_set && rejected == controls.len(),
    }
}

struct FalseControlSetDiagnostics {
    missing_control_ids: Vec<&'static str>,
    duplicate_control_ids: Vec<&'static str>,
}

impl FalseControlSetDiagnostics {
    fn is_complete(&self) -> bool {
        self.missing_control_ids.is_empty() && self.duplicate_control_ids.is_empty()
    }
}

fn false_control_set_diagnostics(
    ids: impl IntoIterator<Item = FalseControlId>,
) -> FalseControlSetDiagnostics {
    let mut seen = BTreeSet::new();
    let mut duplicates = BTreeSet::new();
    for id in ids {
        if !seen.insert(id) {
            duplicates.insert(id);
        }
    }
    let missing_control_ids = FalseControlId::all()
        .iter()
        .copied()
        .filter(|id| !seen.contains(id))
        .map(FalseControlId::as_str)
        .collect();
    let duplicate_control_ids = duplicates.into_iter().map(FalseControlId::as_str).collect();
    FalseControlSetDiagnostics {
        missing_control_ids,
        duplicate_control_ids,
    }
}

fn validate_required_control_set(
    controls: &[(FalseControlId, FalseControlStatus)],
) -> MathverseResult<()> {
    let diagnostics = false_control_set_diagnostics(controls.iter().map(|(id, _)| *id));
    if diagnostics.is_complete() {
        return Ok(());
    }
    let mut parts = Vec::new();
    if !diagnostics.missing_control_ids.is_empty() {
        parts.push(format!(
            "missing required false-control id(s): {}",
            diagnostics.missing_control_ids.join(", ")
        ));
    }
    if !diagnostics.duplicate_control_ids.is_empty() {
        parts.push(format!(
            "duplicate false-control id(s): {}",
            diagnostics.duplicate_control_ids.join(", ")
        ));
    }
    Err(kernel_error(parts.join("; ")))
}

fn kernel_error(message: impl Into<String>) -> MathverseError {
    MathverseError::Kernel(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::attempt_log::{
        iter_from, read_artifact, AttemptFilter, AttemptStatusFilter, AuthorityReceipt,
    };
    use clean_verify::nn_verify::certificate::branch_cover::{
        verify_branch_cover, BranchCoverCertificate, BranchCoverError, BranchDomain,
        NumericInterval,
    };
    use clean_verify::qbf_verify::strategy::{
        verify_qbf_strategy, BoolExpr, QbfFormula, QbfStrategy, QuantifiedVar, SkolemFunction,
        StrategyCase, StrategyError,
    };

    fn control(id: FalseControlId, status: FalseControlStatus) -> FalseControlResult {
        FalseControlResult {
            id,
            label: "test false control",
            status,
            detail: "test".to_owned(),
            todo: None,
        }
    }

    fn green_report() -> FalseControlReport {
        FalseControlReport {
            controls: FalseControlId::all()
                .iter()
                .copied()
                .map(|id| control(id, FalseControlStatus::Rejected))
                .collect(),
        }
    }

    fn complete_rejected_controls() -> Vec<FalseControlResult> {
        vec![
            FalseControlResult::rejected(
                FalseControlId::InvalidFarkasMultiplier,
                "invalid Farkas multiplier",
                "rejected",
            ),
            FalseControlResult::rejected(
                FalseControlId::BrokenBranchCover,
                "broken branch cover",
                "rejected",
            ),
            FalseControlResult::rejected(
                FalseControlId::ChangedLlvm2Denotation,
                "changed LLVM2 denotation",
                "rejected",
            ),
            FalseControlResult::rejected(
                FalseControlId::DirectFalseProof,
                "direct proof of False",
                "rejected",
            ),
            FalseControlResult::rejected(
                FalseControlId::InvalidQbfStrategy,
                "invalid QBF strategy",
                "rejected",
            ),
        ]
    }

    fn accepted_false_control_report() -> FalseControlReport {
        FalseControlReport {
            controls: complete_rejected_controls(),
        }
    }

    fn rejected_false_control_report() -> FalseControlReport {
        let mut controls = complete_rejected_controls();
        controls[2] = FalseControlResult::accepted_bad_input(
            FalseControlId::ChangedLlvm2Denotation,
            "changed LLVM2 denotation",
            "accepted",
        );
        FalseControlReport { controls }
    }

    fn mixed_status_report() -> FalseControlReport {
        FalseControlReport {
            controls: vec![
                FalseControlResult::rejected(
                    FalseControlId::InvalidFarkasMultiplier,
                    "invalid Farkas multiplier",
                    "rejected",
                ),
                FalseControlResult::pending(
                    FalseControlId::BrokenBranchCover,
                    "broken branch cover",
                    "pending",
                    "backend hook",
                ),
                FalseControlResult::accepted_bad_input(
                    FalseControlId::ChangedLlvm2Denotation,
                    "changed LLVM2 denotation",
                    "accepted",
                ),
                FalseControlResult::probe_error(
                    FalseControlId::DirectFalseProof,
                    "direct proof of False",
                    "probe failed",
                ),
            ],
        }
    }

    /// The `broken_branch_cover` probe input, in `clean-verify`'s
    /// n-dimensional certificate form. Built from the same constants the probe
    /// itself uses, so the two cannot drift apart.
    fn broken_branch_cover_certificate() -> BranchCoverCertificate {
        BranchCoverCertificate::new(
            vec![NumericInterval::new(
                BROKEN_BRANCH_COVER_DOMAIN.0,
                BROKEN_BRANCH_COVER_DOMAIN.1,
            )],
            BROKEN_BRANCH_COVER_BRANCHES
                .iter()
                .enumerate()
                .map(|(index, (lower, upper))| {
                    BranchDomain::new(
                        format!("branch{index}"),
                        vec![NumericInterval::new(*lower, *upper)],
                    )
                })
                .collect(),
        )
    }

    /// The copy QBF `∀u. ∃e. (e ↔ u)` that the `invalid_qbf_strategy` probe
    /// describes, in `clean-verify`'s form.
    fn qbf_copy_formula() -> QbfFormula {
        QbfFormula::new(
            vec![
                QuantifiedVar::universal(QBF_UNIVERSAL_VAR),
                QuantifiedVar::existential(QBF_EXISTENTIAL_VAR),
            ],
            BoolExpr::iff(
                BoolExpr::var(QBF_EXISTENTIAL_VAR),
                BoolExpr::var(QBF_UNIVERSAL_VAR),
            ),
        )
    }

    /// The losing constant strategy `e := QBF_CONSTANT_FALSE_STRATEGY_OUTPUT`.
    fn qbf_constant_false_strategy() -> QbfStrategy {
        QbfStrategy::new([(
            QBF_EXISTENTIAL_VAR.to_owned(),
            SkolemFunction::new(
                vec![QBF_UNIVERSAL_VAR.to_owned()],
                vec![
                    StrategyCase::new(vec![false], QBF_CONSTANT_FALSE_STRATEGY_OUTPUT),
                    StrategyCase::new(vec![true], QBF_CONSTANT_FALSE_STRATEGY_OUTPUT),
                ],
            ),
        )])
    }

    #[test]
    fn test_complete_all_rejected_report_is_replay_ready() {
        let summary = green_report().replay_summary();

        assert!(summary.replay_ready);
        assert_eq!(summary.total, 5);
        assert_eq!(summary.rejected, 5);
        assert!(summary.missing_control_ids.is_empty());
        assert!(summary.duplicate_control_ids.is_empty());
    }

    #[test]
    fn test_incomplete_control_set_is_not_replay_ready() {
        let report = FalseControlReport {
            controls: vec![control(
                FalseControlId::InvalidFarkasMultiplier,
                FalseControlStatus::Rejected,
            )],
        };
        let summary = report.replay_summary();

        assert!(!summary.replay_ready);
        assert_eq!(
            summary.missing_control_ids,
            vec![
                "broken_branch_cover",
                "changed_llvm2_denotation",
                "direct_false_proof",
                "invalid_qbf_strategy",
            ]
        );
    }

    #[test]
    fn test_duplicate_control_ids_are_reported() {
        let report = FalseControlReport {
            controls: FalseControlId::all()
                .iter()
                .copied()
                .chain(std::iter::once(FalseControlId::DirectFalseProof))
                .map(|id| control(id, FalseControlStatus::Rejected))
                .collect(),
        };
        let summary = report.replay_summary();

        assert!(!summary.replay_ready);
        assert_eq!(summary.duplicate_control_ids, vec!["direct_false_proof"]);
    }

    #[test]
    fn test_pending_and_probe_error_controls_block() {
        let mut report = green_report();
        report.controls[1].status = FalseControlStatus::PendingBackend;
        report.controls[2].status = FalseControlStatus::ProbeError;

        let blocking: Vec<_> = report
            .blocking_controls()
            .iter()
            .map(|control| control.id)
            .collect();

        assert_eq!(
            blocking,
            vec![
                FalseControlId::BrokenBranchCover,
                FalseControlId::ChangedLlvm2Denotation
            ]
        );
        assert!(!report.replay_summary().replay_ready);
    }

    #[test]
    fn test_accepted_bad_input_is_a_failing_control() {
        let mut report = green_report();
        report.controls[0].status = FalseControlStatus::AcceptedBadInput;

        assert_eq!(report.failing_controls().len(), 1);
        assert_eq!(report.rejected_count(), 4);
    }

    #[test]
    fn test_suite_reports_all_five_controls() {
        let report = run_false_control_suite();

        assert_eq!(report.controls.len(), 5);
        assert_eq!(report.replay_summary().expected_total, 5);
        assert!(report.controls.iter().any(|control| control.id
            == FalseControlId::ChangedLlvm2Denotation
            && control.status == FalseControlStatus::Rejected));
        assert!(report.blocking_controls().is_empty());
        assert!(report.failing_controls().is_empty());
        assert!(report.all_controls_rejected());
    }

    #[test]
    fn test_concrete_controls_reject_bad_inputs() {
        let report = run_false_control_suite();

        assert_eq!(report.rejected_count(), 5);
        assert_eq!(report.pending_count(), 0);
        assert_eq!(report.accepted_bad_input_count(), 0);
        assert_eq!(report.probe_error_count(), 0);
    }

    #[test]
    fn test_control_ids_have_stable_machine_names() {
        assert_eq!(
            [
                FalseControlId::InvalidFarkasMultiplier.as_str(),
                FalseControlId::BrokenBranchCover.as_str(),
                FalseControlId::ChangedLlvm2Denotation.as_str(),
                FalseControlId::DirectFalseProof.as_str(),
                FalseControlId::InvalidQbfStrategy.as_str(),
            ],
            [
                "invalid_farkas_multiplier",
                "broken_branch_cover",
                "changed_llvm2_denotation",
                "direct_false_proof",
                "invalid_qbf_strategy",
            ]
        );
    }

    #[test]
    fn test_invalid_farkas_multiplier_control_rejects_negative_multiplier() {
        let result = run_invalid_farkas_multiplier_control();

        assert_eq!(result.status, FalseControlStatus::Rejected);
        assert!(result.detail.contains("negative multiplier"));
        assert!(result.todo.is_none());
    }

    #[test]
    fn test_broken_branch_cover_control_rejects_gap_cover() {
        let result = run_broken_branch_cover_control();

        assert_eq!(result.status, FalseControlStatus::Rejected);
        assert!(result.detail.contains("uncovered witness"));
        assert!(result.todo.is_none());
    }

    /// The probe's local adapter and `clean-verify`'s real n-dimensional
    /// verifier must agree on the SAME known-bad cover.
    #[test]
    fn test_broken_branch_cover_probe_input_is_rejected_by_verify_branch_cover() {
        let err = verify_branch_cover(&broken_branch_cover_certificate())
            .expect_err("the false-control cover has a hole and must be rejected");

        let BranchCoverError::UncoveredWitness { witness } = err else {
            panic!("expected an uncovered-witness rejection, got {err:?}");
        };
        assert_eq!(witness.len(), 1);
        assert!(
            witness[0] > BROKEN_BRANCH_COVER_BRANCHES[0].1
                && witness[0] < BROKEN_BRANCH_COVER_BRANCHES[1].0,
            "witness {} must land in the (0.4, 0.6) hole",
            witness[0]
        );
    }

    #[test]
    fn test_changed_llvm2_denotation_control_rejects_swapped_hash() {
        let result = run_changed_llvm2_denotation_control();

        assert_eq!(result.status, FalseControlStatus::Rejected);
        assert!(result.detail.contains("swapped hash"));
        assert!(result.todo.is_none());
    }

    #[test]
    fn test_direct_false_control_rejects_bad_proof_term() {
        let result = run_direct_false_control();

        assert_eq!(result.status, FalseControlStatus::Rejected);
        assert!(result.detail.contains("bad proof term rejected"));
        assert!(result.detail.contains("FalseControlSuite.false_axiom"));
        assert!(result.todo.is_none());
    }

    #[test]
    fn test_invalid_qbf_strategy_control_rejects_losing_branch() {
        let result = run_invalid_qbf_strategy_control();

        assert_eq!(result.status, FalseControlStatus::Rejected);
        assert!(result.detail.contains("rejected losing branch"));
        assert!(result.detail.contains("(\"u\", true)"));
        assert!(result.todo.is_none());
    }

    /// The probe's local adapter and `clean-verify`'s real strategy verifier
    /// must agree on the SAME known-bad formula/strategy pair, down to the
    /// losing assignment.
    #[test]
    fn test_invalid_qbf_strategy_probe_input_is_rejected_by_verify_qbf_strategy() {
        let err = verify_qbf_strategy(&qbf_copy_formula(), &qbf_constant_false_strategy())
            .expect_err("a constant-false strategy loses the copy QBF and must be rejected");

        assert_eq!(
            err,
            StrategyError::LosingUniversalAssignment {
                assignment: vec![(QBF_UNIVERSAL_VAR.to_owned(), true)],
            }
        );
        assert_eq!(first_losing_universal_assignment(), Some(true));
    }

    #[test]
    fn test_authority_gate_attempt_record_is_appended_and_queryable() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let accepted_report = accepted_false_control_report();
        let rejected_report = rejected_false_control_report();

        let accepted = record_false_control_authority_gate_attempt(root, &accepted_report, 17)
            .expect("record accepted false-control gate");
        let rejected = record_false_control_authority_gate_attempt(root, &rejected_report, 19)
            .expect("record rejected false-control gate");

        assert_eq!(
            accepted.goal_hash,
            false_control_expected_authority_goal_hash(root).expect("expected false-control hash")
        );
        assert_eq!(accepted.authority_gate.as_deref(), Some("false_controls"));
        assert!(matches!(accepted.status, AttemptStatus::Accepted));
        assert_eq!(accepted.wall_time_ms, 17);
        assert!(accepted.failure_mode.is_none());
        assert!(accepted.trust_level.is_some());
        let accepted_receipt = AuthorityReceipt::from_attempt(&accepted);
        assert_eq!(
            accepted_receipt
                .command_evidence
                .as_ref()
                .and_then(|artifact| artifact.kind.as_deref()),
            Some(FALSE_CONTROL_COMMAND_EVIDENCE_ARTIFACT_KIND)
        );
        assert_eq!(rejected.authority_gate.as_deref(), Some("false_controls"));
        assert!(matches!(rejected.status, AttemptStatus::Rejected { .. }));
        assert_eq!(
            rejected.failure_mode.as_deref(),
            Some("false_control_accepted_bad_input")
        );

        let accepted_attempts: Vec<_> = iter_from(
            root,
            AttemptFilter {
                authority_gate: Some("false_controls".to_owned()),
                status: Some(AttemptStatusFilter::Accepted),
                ..AttemptFilter::default()
            },
        )
        .expect("query accepted false-control gate")
        .collect();
        assert_eq!(accepted_attempts, vec![accepted]);

        let rejected_attempts: Vec<_> = iter_from(
            root,
            AttemptFilter {
                authority_gate: Some("false_controls".to_owned()),
                status: Some(AttemptStatusFilter::Rejected),
                failure_mode: Some("false_control_accepted_bad_input".to_owned()),
                ..AttemptFilter::default()
            },
        )
        .expect("query rejected false-control gate")
        .collect();
        assert_eq!(rejected_attempts, vec![rejected.clone()]);

        let artifact = rejected
            .solver_artifact
            .as_ref()
            .expect("false-control report artifact");
        let artifact_json = serde_json::from_slice::<Value>(
            &read_artifact(root, artifact).expect("read false-control report artifact"),
        )
        .expect("report artifact json");
        assert_eq!(
            artifact_json["summary"]["non_rejected_control_ids"],
            serde_json::json!(["changed_llvm2_denotation"])
        );
        assert!(
            artifact_json["controls"][0]["replay_evidence"]["input_hash"]
                .as_str()
                .is_some_and(|hash| hash.len() == 64)
        );
        assert_eq!(
            artifact_json["controls"][2]["replay_evidence"]["detail"],
            "accepted"
        );
        let validation = validate_false_control_report_artifact(
            &read_artifact(root, artifact).expect("read false-control report artifact"),
        )
        .expect("validate false-control report artifact");
        assert_eq!(
            validation.expected_failure_mode.as_deref(),
            Some("false_control_accepted_bad_input")
        );
    }

    #[test]
    fn test_report_json_includes_replay_readiness_summary() {
        let report = mixed_status_report();

        let summary = report.replay_summary();
        assert_eq!(summary.total, 4);
        assert_eq!(summary.expected_total, 5);
        assert_eq!(summary.rejected, 1);
        assert_eq!(summary.pending, 1);
        assert_eq!(summary.accepted_bad_input, 1);
        assert_eq!(summary.probe_errors, 1);
        assert_eq!(report.pending_count(), 1);
        assert_eq!(report.accepted_bad_input_count(), 1);
        assert_eq!(report.probe_error_count(), 1);
        assert_eq!(
            summary.non_rejected_control_ids,
            [
                "broken_branch_cover",
                "changed_llvm2_denotation",
                "direct_false_proof",
            ]
        );
        assert_eq!(summary.missing_control_ids, ["invalid_qbf_strategy"]);
        assert!(summary.duplicate_control_ids.is_empty());
        assert!(!summary.replay_ready);

        let json = serde_json::to_value(&report).expect("serialize false-control report");
        assert_eq!(json["schema_version"], FALSE_CONTROL_REPORT_SCHEMA_VERSION);
        assert_eq!(json["summary"]["total"], 4);
        assert_eq!(json["summary"]["expected_total"], 5);
        assert_eq!(json["summary"]["rejected"], 1);
        assert_eq!(json["summary"]["pending"], 1);
        assert_eq!(json["summary"]["accepted_bad_input"], 1);
        assert_eq!(json["summary"]["probe_errors"], 1);
        assert_eq!(
            json["summary"]["non_rejected_control_ids"],
            serde_json::json!([
                "broken_branch_cover",
                "changed_llvm2_denotation",
                "direct_false_proof"
            ])
        );
        assert_eq!(
            json["summary"]["missing_control_ids"],
            serde_json::json!(["invalid_qbf_strategy"])
        );
        assert_eq!(
            json["summary"]["duplicate_control_ids"],
            serde_json::json!([])
        );
        assert_eq!(json["summary"]["replay_ready"], false);
        assert_eq!(json["controls"][0]["id"], "invalid_farkas_multiplier");
        assert!(json["controls"][0]["replay_evidence"]["input_hash"]
            .as_str()
            .is_some_and(|hash| hash.len() == 64));
        assert!(json["controls"][0]["replay_evidence"]["result_hash"]
            .as_str()
            .is_some_and(|hash| hash.len() == 64));
        assert_eq!(json["controls"][0]["replay_evidence"]["detail"], "rejected");
        assert_eq!(json["controls"][1]["status"], "pending_backend");
        assert_eq!(json["controls"][1]["detail"], "pending");
        assert_eq!(json["controls"][1]["todo"], "backend hook");
        assert_eq!(json["controls"][2]["status"], "accepted_bad_input");
        assert_eq!(json["controls"][2]["detail"], "accepted");
        assert_eq!(json["controls"][3]["status"], "probe_error");
        assert_eq!(json["controls"][3]["detail"], "probe failed");
    }

    #[test]
    fn test_blocking_controls_include_pending_accepted_and_probe_errors() {
        let report = mixed_status_report();

        let blocking_ids: Vec<_> = report
            .blocking_controls()
            .into_iter()
            .map(|control| control.id.as_str())
            .collect();

        assert_eq!(
            blocking_ids,
            [
                "broken_branch_cover",
                "changed_llvm2_denotation",
                "direct_false_proof",
            ]
        );
    }

    #[test]
    fn test_recording_rejects_incomplete_false_control_set() {
        let temp = tempfile::tempdir().expect("tempdir");
        let report = FalseControlReport {
            controls: vec![FalseControlResult::rejected(
                FalseControlId::InvalidFarkasMultiplier,
                "invalid Farkas multiplier",
                "rejected",
            )],
        };

        let err = record_false_control_authority_gate_attempt(temp.path(), &report, 1)
            .expect_err("incomplete false-control reports must not be recorded");
        assert!(err
            .to_string()
            .contains("missing required false-control id"));
    }

    #[test]
    fn test_artifact_validation_rejects_missing_or_duplicate_control_set() {
        let missing = serde_json::to_vec(&FalseControlReport {
            controls: vec![FalseControlResult::rejected(
                FalseControlId::InvalidFarkasMultiplier,
                "invalid Farkas multiplier",
                "rejected",
            )],
        })
        .expect("serialize incomplete report");
        validate_false_control_report_artifact(&missing)
            .expect_err("missing controls must fail artifact validation");

        let mut duplicate_controls = complete_rejected_controls();
        duplicate_controls.push(FalseControlResult::rejected(
            FalseControlId::InvalidFarkasMultiplier,
            "invalid Farkas multiplier",
            "rejected again",
        ));
        let duplicate = serde_json::to_vec(&FalseControlReport {
            controls: duplicate_controls,
        })
        .expect("serialize duplicated report");
        validate_false_control_report_artifact(&duplicate)
            .expect_err("duplicate controls must fail artifact validation");
    }

    #[test]
    fn test_artifact_validation_rejects_flattering_summary() {
        let report = accepted_false_control_report();
        let mut json =
            serde_json::to_value(&report).expect("serialize complete false-control report");
        json["summary"]["rejected"] = serde_json::json!(99);
        let bytes = serde_json::to_vec(&json).expect("serialize tampered report");

        validate_false_control_report_artifact(&bytes)
            .expect_err("a summary that disagrees with its rows must not validate");
    }

    #[test]
    fn test_artifact_validation_rejects_tampered_replay_evidence() {
        let report = accepted_false_control_report();
        let mut json =
            serde_json::to_value(&report).expect("serialize complete false-control report");
        json["controls"][0]["detail"] = serde_json::json!("tampered");
        let bytes = serde_json::to_vec(&json).expect("serialize tampered report");

        validate_false_control_report_artifact(&bytes)
            .expect_err("replay evidence must be recomputed, not trusted");
    }
}
