// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! First-class spec ↔ source cross-reference IR objects.
//!
//! A [`SpecModule`] is the TrustIr-native lowering of an authored state-machine
//! model (a TLA+-style `Model`): its abstract variables, named actions, named
//! invariants, plus the **bidirectional anchors** that bind each action to a
//! concrete Rust symbol/span, and the **waivers** that explicitly exempt an
//! action from requiring a source binding.
//!
//! `SpecModule` is the meeting point of the source↔spec cross-reference: a
//! frontend (e.g. aterm's `Model::lower_to_ir`) emits one `SpecModule` per
//! machine into a [`crate::Module`], and the `spec-link` pass
//! ([`link_spec_modules`]) enforces, at compile/CI time, the structural
//! obligations that today nothing checks:
//!
//! * **Ob.1 — action exists** (spec→source closure): every anchor, waiver, and
//!   proof names a real action in its machine's `SpecModule`.
//! * **Ob.3 — total coverage** (no silent gaps): every action of a
//!   [`SpecEnforcementMode::Linked`] machine is covered by ≥1 anchor **or** an
//!   explicit [`SpecWaiver`], even when the machine has zero anchors.
//! * **Ob.4 — machine exists** (no dangling spec name): every anchor, waiver,
//!   and proof names a `SpecModule` present in the module.
//!
//! Behavioral source resolution remains frontend-specific, but an anchor emitted
//! together with executable TrustIr can bind directly to a module-local
//! [`FuncId`]. [`SpecAnchor::rust_symbol`] remains opaque diagnostic/provenance
//! text for external specifications and for source-facing reports.

use std::collections::{BTreeMap, BTreeSet};

use crate::spec_proof::{HarnessManifest, HarnessManifestError, link_proofs};
use crate::value::FuncId;
use crate::{Module, Ty};

/// Origin of a [`SpecModule`]: whether the model is authored in-source
/// (embedded, e.g. a `ty_model!` literal) or parsed from an external `.tla`
/// file.
///
/// Both kinds bind to source identically — obligation 4 resolves either — so
/// external TLA specs are not an island. The `External` variant carries the
/// path/identifier of the originating artifact for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SpecOrigin {
    /// Authored in-source (e.g. an embedded `ty_model!` `Model` literal).
    Embedded,
    /// Parsed from an external `.tla` file; carries the source path/identifier.
    External(String),
}

impl SpecOrigin {
    /// Human-readable one-line description used by `Display`/diagnostics.
    pub fn label(&self) -> String {
        match self {
            SpecOrigin::Embedded => "embedded".to_string(),
            SpecOrigin::External(path) => format!("external({path})"),
        }
    }
}

/// An abstract state variable of a [`SpecModule`].
///
/// `ty` is an opaque textual type tag (e.g. `"Int"`, `"Bool"`, `"0..7"`) — the
/// standalone IR does not interpret it; it is carried for documentation and for
/// the consuming checker.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecVar {
    /// Variable name (matches a TLA+ `VARIABLES` entry / `Model` var).
    pub name: String,
    /// Opaque textual type/domain tag (e.g. `"Int"`, `"Bool"`, `"0..7"`).
    pub ty: String,
}

impl SpecVar {
    /// Construct a variable with the given name and opaque type tag.
    pub fn new(name: impl Into<String>, ty: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ty: ty.into(),
        }
    }
}

/// A named invariant of a [`SpecModule`].
///
/// `formula` is an opaque textual predicate (TLA+ / DSL surface syntax); the
/// standalone IR does not parse it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecInvariant {
    /// Invariant label (e.g. `"BoundedSeq"`).
    pub name: String,
    /// Opaque textual predicate (TLA+/DSL surface syntax).
    pub formula: String,
}

impl SpecInvariant {
    /// Construct an invariant with the given label and opaque formula.
    pub fn new(name: impl Into<String>, formula: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            formula: formula.into(),
        }
    }
}

/// Whether a [`SpecModule`] is descriptive design material or a link-time
/// certification claim.
///
/// This is explicit in every current-format artifact. Pre-v27 binary and
/// legacy serde/text artifacts map through [`SpecEnforcementMode::legacy_compatibility`]
/// to [`DesignOnly`](Self::DesignOnly); legacy data is never silently promoted
/// to the stronger [`Linked`](Self::Linked) contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SpecEnforcementMode {
    /// Descriptive/non-certifying model material. Bindings are structurally
    /// checked when present, but total action coverage is not claimed.
    #[default]
    DesignOnly,
    /// A certifying source↔spec link. Every action must be anchored or waived,
    /// even when the machine currently has zero anchors.
    Linked,
}

impl SpecEnforcementMode {
    /// Explicit compatibility mapping for artifacts predating the enforcement
    /// field. Old heuristic intent cannot establish a certification claim, so
    /// the only sound mapping is `DesignOnly`.
    pub const fn legacy_compatibility() -> Self {
        Self::DesignOnly
    }

    /// Stable lowercase tag used by the text codec and diagnostics.
    pub const fn tag(self) -> &'static str {
        match self {
            Self::DesignOnly => "design-only",
            Self::Linked => "linked",
        }
    }
}

/// Typed resolution state for an anchor's concrete→abstract projection.
///
/// `project` remains the human-facing name. This enum is the semantic target:
/// a module-local function, a versioned intrinsic understood by Trust, or an
/// explicitly unresolved target belonging to an external specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SpecProjectionTarget {
    /// A module-local projection function. Module validation checks existence,
    /// body presence, name agreement, and the `(&T) -> R` signature contract.
    Function(FuncId),
    /// The versioned temporal field-path projection encoded by the machine's
    /// variable-path invariants.
    TemporalFieldPathsV1,
    /// Explicitly unresolved because the source model is external to this
    /// executable module. Never valid for an embedded linked model.
    ExternalUnresolved,
}

impl SpecProjectionTarget {
    /// Explicit compatibility mapping for artifacts predating typed projection
    /// resolution. Absence cannot establish a semantic target.
    pub const fn legacy_compatibility() -> Option<Self> {
        None
    }

    /// Stable text/diagnostic tag for non-function targets.
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Function(_) => "function",
            Self::TemporalFieldPathsV1 => "temporal-field-paths-v1",
            Self::ExternalUnresolved => "external-unresolved",
        }
    }
}

/// Canonical diagnostic name for [`SpecProjectionTarget::TemporalFieldPathsV1`].
pub const TEMPORAL_FIELD_PATH_PROJECTION_V1: &str = "trust-ir.temporal-field-paths.v1";

/// A bidirectional anchor binding a model action to a concrete Rust symbol.
///
/// `machine`/`action` point into the spec; `function` optionally points at the
/// exact module-local executable TrustIr function. Together with the
/// containing [`Module`](crate::Module)'s name, that [`FuncId`] is the
/// executable identity; `rust_symbol`/`span` retain source provenance.
/// `project` names the projection function or frontend projection scheme that
/// maps concrete `&self` state to the model's abstract vars.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecAnchor {
    /// Name of the [`SpecModule`] this anchor targets (must resolve — Ob.4).
    pub machine: String,
    /// Name of the action within that machine (must exist — Ob.1).
    pub action: String,
    /// Opaque Rust symbol reference (path/`DefId` text). Not resolved by the
    /// standalone CLI — carried verbatim for diagnostics and provenance.
    pub rust_symbol: String,
    /// Source span of the annotated symbol, as opaque text (e.g.
    /// `"src/foo.rs:120:4"`). Carried for diagnostics.
    pub span: String,
    /// Optional projection function path (`&self` → abstract vars), or a named
    /// frontend projection scheme whose meaning is carried by the module (for
    /// example, temporal field-path invariants). It must agree with
    /// [`Self::projection_target`] when that target is typed or versioned.
    ///
    /// No `skip_serializing_if` — see the note on [`SpecModule::vars`] for why
    /// the compact MessagePack codec requires every field to be positional.
    #[cfg_attr(feature = "serde", serde(default))]
    pub project: Option<String>,
    /// Exact module-local TrustIr function implementing this action. Frontends
    /// that emit an anchor together with executable IR should populate this.
    /// Every `Linked` anchor requires it; `None` is retained only for
    /// design-only/legacy unresolved source anchors.
    ///
    /// Compact MessagePack encodes structs positionally. This was appended in
    /// v26 so legacy five-field anchors deserialize through `serde(default)`
    /// without shifting an existing field.
    #[cfg_attr(feature = "serde", serde(default))]
    pub function: Option<FuncId>,
    /// Typed projection resolution, appended in v27. Legacy six-field anchors
    /// map explicitly to `None`; a `Linked` module must provide a target for
    /// every anchor.
    #[cfg_attr(
        feature = "serde",
        serde(default = "SpecProjectionTarget::legacy_compatibility")
    )]
    pub projection_target: Option<SpecProjectionTarget>,
}

/// An explicit waiver exempting a model action from requiring a source anchor.
///
/// A waiver is the audited escape hatch for an action that has no shipping
/// handler (yet). It satisfies coverage (Ob.3) for that action **with a reason**
/// — making the gap visible and reviewable rather than silent.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecWaiver {
    /// Name of the [`SpecModule`] this waiver targets (must resolve — Ob.4).
    pub machine: String,
    /// Name of the action being waived (must exist — Ob.1).
    pub action: String,
    /// Human-readable justification (reviewed; not a silent hatch).
    pub reason: String,
}

/// The kind of proof a [`SpecProof`] names. Today the only producer is aterm's
/// kani harness manifest, so the sole variant is [`ProofKind::Kani`]; the enum
/// exists so future proof technologies (e.g. a Lean discharge) can be carried
/// without a breaking schema change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofKind {
    /// A `#[kani::proof]` bounded-model-checking harness.
    Kani,
}

impl ProofKind {
    /// Short lowercase tag (`"kani"`) used by the text codec and diagnostics.
    pub fn tag(&self) -> &'static str {
        match self {
            ProofKind::Kani => "kani",
        }
    }
}

/// A first-class proof binding: a claim that a model `action` (of `machine`) is
/// discharged by a named external proof harness (`proof_name`) of a given
/// [`ProofKind`].
///
/// This is the IR analogue of aterm's `proof_anchor!`. The standalone IR cannot
/// resolve `proof_name` to a live Rust symbol (Ob.2 is out of scope), so the
/// `spec-link` pass resolves it against a **`HarnessManifest`** handed in from
/// the build — see [`crate::spec_proof::link_proofs`]. Like an anchor, the
/// `machine`/`action` must still satisfy Ob.4/Ob.1.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecProof {
    /// Name of the [`SpecModule`] this proof targets (must resolve — Ob.4).
    pub machine: String,
    /// Name of the action this proof discharges (must exist — Ob.1).
    pub action: String,
    /// Name of the proof harness function (e.g. a `#[kani::proof] fn`). Must
    /// resolve against a supplied `HarnessManifest` (L1).
    pub proof_name: String,
    /// What kind of proof `proof_name` refers to.
    pub kind: ProofKind,
}

/// A first-class spec ↔ source cross-reference IR object.
///
/// Carries the lowered model (`vars`/`actions`/`invariants`) and its bindings
/// (`anchors`/`waivers`). See the module docs for the obligations the
/// `spec-link` pass enforces over a set of these.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecModule {
    /// Machine name — matches the TLA+ MODULE / `Model::name`. Anchors and
    /// waivers reference a `SpecModule` by this name.
    pub name: String,
    /// Abstract state variables.
    ///
    /// Note: the inner `SpecModule` fields deliberately do **not** use
    /// `skip_serializing_if`. The CLI's MessagePack codec is the compact
    /// (positional) `rmp_serde` encoding, which decodes structs as fixed-length
    /// sequences — omitting a field there desyncs the positional layout. A bare
    /// `#[serde(default)]` keeps forward-compatibility without that hazard.
    #[cfg_attr(feature = "serde", serde(default))]
    pub vars: Vec<SpecVar>,
    /// Named actions (the binding targets). Order is preserved.
    #[cfg_attr(feature = "serde", serde(default))]
    pub actions: Vec<String>,
    /// Named invariants.
    #[cfg_attr(feature = "serde", serde(default))]
    pub invariants: Vec<SpecInvariant>,
    /// Action ↔ Rust-symbol anchors.
    #[cfg_attr(feature = "serde", serde(default))]
    pub anchors: Vec<SpecAnchor>,
    /// Explicit per-action waivers.
    #[cfg_attr(feature = "serde", serde(default))]
    pub waivers: Vec<SpecWaiver>,
    /// Action ↔ proof-harness bindings (the IR analogue of `proof_anchor!`).
    ///
    /// Positional / `#[serde(default)]` and version-gated in the binary codec
    /// (bin v10+), so pre-proof artifacts deserialize to an empty vector — the
    /// same forward-compatibility pattern as the other `SpecModule` fields (see
    /// the note on [`SpecModule::vars`]).
    #[cfg_attr(feature = "serde", serde(default))]
    pub proofs: Vec<SpecProof>,
    /// Where this model came from (embedded vs external `.tla`).
    pub origin: SpecOrigin,
    /// Explicit enforcement contract, appended in binary v27 and as the final
    /// positional serde field. Missing legacy values map only through the
    /// named compatibility function below, never to `Linked`.
    #[cfg_attr(
        feature = "serde",
        serde(default = "SpecEnforcementMode::legacy_compatibility")
    )]
    pub enforcement: SpecEnforcementMode,
}

impl SpecModule {
    /// Construct an empty embedded, non-certifying `SpecModule`.
    ///
    /// New certification-producing emitters should call [`Self::linked`]
    /// explicitly. `new` remains the conservative design-only constructor for
    /// source compatibility.
    pub fn new(name: impl Into<String>) -> Self {
        Self::design_only(name)
    }

    /// Construct an empty embedded design-only module.
    pub fn design_only(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            vars: Vec::new(),
            actions: Vec::new(),
            invariants: Vec::new(),
            anchors: Vec::new(),
            waivers: Vec::new(),
            proofs: Vec::new(),
            origin: SpecOrigin::Embedded,
            enforcement: SpecEnforcementMode::DesignOnly,
        }
    }

    /// Construct an empty embedded linked module whose coverage and proof
    /// obligations are certifying by default.
    pub fn linked(name: impl Into<String>) -> Self {
        Self {
            enforcement: SpecEnforcementMode::Linked,
            ..Self::design_only(name)
        }
    }

    /// True when `action` is a declared action of this machine.
    pub fn has_action(&self, action: &str) -> bool {
        self.actions.iter().any(|a| a == action)
    }

    /// Set of actions that are anchored (bound to ≥1 Rust symbol) — those whose
    /// name appears in at least one of this machine's `anchors`.
    fn anchored_actions(&self) -> BTreeSet<&str> {
        self.anchors
            .iter()
            .filter(|anchor| {
                !is_blank(&self.name)
                    && anchor.machine == self.name
                    && !is_blank(&anchor.action)
                    && !is_blank(&anchor.rust_symbol)
            })
            .map(|anchor| anchor.action.as_str())
            .collect()
    }

    /// Set of actions that are explicitly waived.
    fn waived_actions(&self) -> BTreeSet<&str> {
        self.waivers
            .iter()
            .filter(|waiver| {
                !is_blank(&self.name)
                    && waiver.machine == self.name
                    && !is_blank(&waiver.action)
                    && !is_blank(&waiver.reason)
            })
            .map(|waiver| waiver.action.as_str())
            .collect()
    }

    /// True when this machine contains at least one structurally owned anchor.
    ///
    /// This is a reporting statistic only. [`SpecEnforcementMode::Linked`], not
    /// anchor count, controls whether coverage (Ob.3) is a hard gate.
    pub fn is_actively_anchored(&self) -> bool {
        !self.anchored_actions().is_empty()
    }

    /// Coverage ratio in `[0.0, 1.0]`: fraction of declared actions that are
    /// anchored or waived. A machine with no actions has ratio `1.0` (vacuously
    /// covered).
    pub fn coverage_ratio(&self) -> f64 {
        if self.actions.is_empty() {
            return 1.0;
        }
        let anchored = self.anchored_actions();
        let waived = self.waived_actions();
        let covered = self
            .actions
            .iter()
            .filter(|a| anchored.contains(a.as_str()) || waived.contains(a.as_str()))
            .count();
        covered as f64 / self.actions.len() as f64
    }
}

// ---------------------------------------------------------------------------
// spec-link pass
// ---------------------------------------------------------------------------

/// A single obligation violation found by [`link_spec_modules`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecLinkViolation {
    /// Structural identity: more than one `SpecModule` claims this machine name.
    DuplicateMachineIdentity { machine: String },
    /// Structural identity: a machine repeats an action, variable, or invariant
    /// name whose meaning is name-addressed.
    DuplicateMemberIdentity {
        machine: String,
        member: &'static str,
        name: String,
    },
    /// Structural identity/reference data that is empty after trimming.
    BlankSemanticValue {
        container: String,
        subject: &'static str,
        field: &'static str,
    },
    /// The same binding identity appears more than once in one machine.
    DuplicateBindingIdentity {
        machine: String,
        binding: &'static str,
        identity: String,
    },
    /// One action is simultaneously source-bound and waived as absent.
    AnchorWaiverConflict { machine: String, action: String },
    /// Structural ownership: a binding stored by one `SpecModule` names a
    /// different machine. The containing module owns its bindings.
    ReferenceContainerMismatch {
        container: String,
        machine: String,
        action: String,
        from: &'static str,
    },
    /// S2: a linked binding omitted a required typed action or projection
    /// target. Origin never weakens this requirement.
    TypedTargetRequired {
        machine: String,
        action: String,
        target: &'static str,
    },
    /// S2: a typed projection target is incompatible with its origin or label.
    ProjectionTargetIncompatible {
        machine: String,
        action: String,
        detail: String,
    },
    /// S2: a populated module-local action/projection target is stale or has an
    /// incompatible executable shape.
    ExecutableTargetInvalid {
        machine: String,
        action: String,
        target: &'static str,
        function: u32,
        detail: String,
    },
    /// Ob.1: an anchor, waiver, or proof names an action absent from its machine.
    ActionMissing {
        machine: String,
        action: String,
        /// Where the dangling reference came from (`"anchor"`, `"waiver"`, or
        /// `"proof"`).
        from: &'static str,
        /// Opaque Rust symbol / reason carried along for diagnostics.
        detail: String,
    },
    /// Ob.4: an anchor, waiver, or proof names a missing `SpecModule`.
    MachineMissing {
        machine: String,
        action: String,
        from: &'static str,
        detail: String,
    },
    /// Ob.3: a linked machine has an action with no anchor and no waiver.
    ActionUncovered { machine: String, action: String },
    /// L2: a present owned anchor carries no projection name (`project` is
    /// absent, empty, or whitespace-only).
    ProjectionMissing { machine: String, action: String },
    /// L1: a [`SpecProof`]'s `proof_name` does not resolve to any entry in the
    /// supplied `HarnessManifest`. Catches a typo'd / dead `proof_anchor!`.
    ProofUnresolved {
        machine: String,
        action: String,
        proof_name: String,
    },
    /// L1: certifying linkage of this machine requires a harness manifest.
    ProofManifestRequired { machine: String },
}

impl SpecLinkViolation {
    /// Short obligation tag (`"Ob.1"` / `"Ob.3"` / `"Ob.4"`) — used by the CLI
    /// report and asserted by the teeth tests.
    pub fn obligation(&self) -> &'static str {
        match self {
            SpecLinkViolation::DuplicateMachineIdentity { .. }
            | SpecLinkViolation::DuplicateMemberIdentity { .. }
            | SpecLinkViolation::BlankSemanticValue { .. }
            | SpecLinkViolation::DuplicateBindingIdentity { .. }
            | SpecLinkViolation::AnchorWaiverConflict { .. } => "S0",
            SpecLinkViolation::ReferenceContainerMismatch { .. } => "S1",
            SpecLinkViolation::TypedTargetRequired { .. }
            | SpecLinkViolation::ProjectionTargetIncompatible { .. }
            | SpecLinkViolation::ExecutableTargetInvalid { .. } => "S2",
            SpecLinkViolation::ActionMissing { .. } => "Ob.1",
            SpecLinkViolation::MachineMissing { .. } => "Ob.4",
            SpecLinkViolation::ActionUncovered { .. } => "Ob.3",
            SpecLinkViolation::ProjectionMissing { .. } => "L2",
            SpecLinkViolation::ProofUnresolved { .. }
            | SpecLinkViolation::ProofManifestRequired { .. } => "L1",
        }
    }

    /// One-line human-readable rendering for the per-machine report.
    pub fn describe(&self) -> String {
        match self {
            SpecLinkViolation::DuplicateMachineIdentity { machine } => {
                format!("[S0 unique-identity] duplicate SpecModule machine name {machine:?}")
            }
            SpecLinkViolation::DuplicateMemberIdentity {
                machine,
                member,
                name,
            } => format!(
                "[S0 unique-identity] machine {machine:?}: duplicate {member} name {name:?}"
            ),
            SpecLinkViolation::BlankSemanticValue {
                container,
                subject,
                field,
            } => format!(
                "[S0 nonblank-metadata] container {container:?}: {subject} has blank {field}"
            ),
            SpecLinkViolation::DuplicateBindingIdentity {
                machine,
                binding,
                identity,
            } => format!(
                "[S0 unique-binding] machine {machine:?}: duplicate {binding} binding {identity}"
            ),
            SpecLinkViolation::AnchorWaiverConflict { machine, action } => format!(
                "[S0 binding-conflict] machine {machine:?}: action {action:?} is both anchored and waived"
            ),
            SpecLinkViolation::ReferenceContainerMismatch {
                container,
                machine,
                action,
                from,
            } => format!(
                "[S1 container-owns-binding] machine {container:?}: stored {from} for action \
                 {action:?} names different machine {machine:?}"
            ),
            SpecLinkViolation::TypedTargetRequired {
                machine,
                action,
                target,
            } => format!(
                "[S2 typed-resolution] linked machine {machine:?}: anchor for action \
                 {action:?} has no typed {target} target"
            ),
            SpecLinkViolation::ProjectionTargetIncompatible {
                machine,
                action,
                detail,
            } => format!(
                "[S2 typed-resolution] machine {machine:?}: anchor for action {action:?} has an \
                 incompatible projection target ({detail})"
            ),
            SpecLinkViolation::ExecutableTargetInvalid {
                machine,
                action,
                target,
                function,
                detail,
            } => format!(
                "[S2 typed-resolution] machine {machine:?}: anchor for action {action:?} has \
                 invalid {target} function #{function} ({detail})"
            ),
            SpecLinkViolation::ActionMissing {
                machine,
                action,
                from,
                detail,
            } => format!(
                "[Ob.1 action-exists] machine {machine:?}: {from} references action {action:?} \
                 which is not declared by the machine ({detail})"
            ),
            SpecLinkViolation::MachineMissing {
                machine,
                action,
                from,
                detail,
            } => format!(
                "[Ob.4 machine-resolves] {from} for action {action:?} names machine {machine:?} \
                 which has no SpecModule in the input ({detail})"
            ),
            SpecLinkViolation::ActionUncovered { machine, action } => format!(
                "[Ob.3 coverage] machine {machine:?}: action {action:?} is neither anchored \
                 nor waived"
            ),
            SpecLinkViolation::ProjectionMissing { machine, action } => format!(
                "[L2 projection-present] machine {machine:?}: anchor for action {action:?} \
                 carries no projection name (project is absent or blank) — fill a real \
                 projection fn path, or remove the anchor and use a waiver"
            ),
            SpecLinkViolation::ProofUnresolved {
                machine,
                action,
                proof_name,
            } => format!(
                "[L1 proof-resolves] machine {machine:?}: proof for action {action:?} names \
                 harness {proof_name:?} which is not in the supplied harness manifest"
            ),
            SpecLinkViolation::ProofManifestRequired { machine } => format!(
                "[L1 proof-manifest-required] machine {machine:?} declares proof bindings \
                 but no harness manifest was supplied"
            ),
        }
    }
}

/// Per-machine coverage summary line for the report.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecCoverage {
    /// Machine name.
    pub machine: String,
    /// Origin label (`"embedded"` / `"external(path)"`).
    pub origin: String,
    /// Explicit enforcement mode.
    pub enforcement: SpecEnforcementMode,
    /// Total declared actions.
    pub total_actions: usize,
    /// Actions covered by an anchor.
    pub anchored: usize,
    /// Actions covered (only) by a waiver.
    pub waived: usize,
    /// Coverage ratio in `[0.0, 1.0]`.
    pub ratio: f64,
    /// Whether this machine has ≥1 structurally owned anchor. This is a
    /// statistic only; [`SpecEnforcementMode::Linked`] controls the gate.
    pub actively_anchored: bool,
}

/// Policy inputs for [`link_spec_modules`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SpecLinkOptions {
    /// Explicitly allow linked proof bindings to remain unresolved when no
    /// manifest is supplied. This always makes the returned report
    /// non-certifying, even if it has no violations.
    pub allow_unverified_linked_proofs: bool,
    /// Require a manifest for proof bindings in design-only modules too. This
    /// preserves the CLI's stronger `--require-manifest` audit switch.
    pub require_manifest_for_design_only: bool,
}

/// Machine-readable reason a violation-free link analysis still cannot certify
/// a source↔spec relationship.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SpecNonCertificationReason {
    /// The input explicitly disclaims linkage completeness.
    DesignOnlyMachine { machine: String },
    /// An external projection has no executable target in this module.
    ExternalProjectionUnresolved { machine: String, action: String },
    /// Proof bindings were intentionally analyzed without a manifest.
    ProofManifestUnverified { machine: String },
}

impl SpecNonCertificationReason {
    /// Stable identifier for CLI/automation output.
    pub const fn code(&self) -> &'static str {
        match self {
            Self::DesignOnlyMachine { .. } => "design-only",
            Self::ExternalProjectionUnresolved { .. } => "external-projection-unresolved",
            Self::ProofManifestUnverified { .. } => "proof-manifest-unverified",
        }
    }

    /// Human-readable deterministic description.
    pub fn describe(&self) -> String {
        match self {
            Self::DesignOnlyMachine { machine } => {
                format!("machine {machine:?} is explicitly design-only")
            }
            Self::ExternalProjectionUnresolved { machine, action } => format!(
                "machine {machine:?} action {action:?} uses an external-unresolved projection"
            ),
            Self::ProofManifestUnverified { machine } => {
                format!("machine {machine:?} has proof bindings with no verified manifest")
            }
        }
    }
}

impl SpecLinkOptions {
    /// Explicit exploratory policy. The resulting report cannot certify a
    /// source↔spec link when it uses this allowance.
    pub const fn exploratory_allow_unverified_proofs() -> Self {
        Self {
            allow_unverified_linked_proofs: true,
            require_manifest_for_design_only: false,
        }
    }
}

/// The full result of running the `spec-link` pass over a set of `SpecModule`s.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecLinkReport {
    /// Per-machine coverage summaries (sorted by machine name).
    pub coverage: Vec<SpecCoverage>,
    /// All obligation violations found (sorted deterministically).
    pub violations: Vec<SpecLinkViolation>,
    /// Deterministically sorted reasons this report is non-certifying even when
    /// it has no obligation violations.
    pub non_certifying_reasons: Vec<SpecNonCertificationReason>,
}

impl SpecLinkReport {
    /// True when no obligation was violated. This does not by itself imply a
    /// certification verdict; use [`Self::is_certifying`] for that boundary.
    pub fn is_ok(&self) -> bool {
        self.violations.is_empty()
    }

    /// True only for a violation-free report over entirely linked modules with
    /// all required proof names resolved through a valid manifest.
    pub fn is_certifying(&self) -> bool {
        self.is_ok() && !self.coverage.is_empty() && self.non_certifying_reasons.is_empty()
    }

    /// Merge additional violations (for example manifest-backed L1 results)
    /// while preserving the report's deterministic, duplicate-free contract.
    pub fn extend_violations(&mut self, violations: impl IntoIterator<Item = SpecLinkViolation>) {
        self.violations.extend(violations);
        normalize_violations(&mut self.violations);
    }
}

/// Validate name-addressed spec identities, ownership, reference closure, and
/// projection presence.
///
/// This is the shared structural authority used by both the core linker and the
/// full module validator. It enforces S0/S1, unconditional Ob.1/Ob.4, and L2.
/// It deliberately excludes executable `FuncId` closure, Ob.3 coverage policy,
/// and L1 harness resolution, which require the containing `Module`, an active
/// enforcement decision, or a manifest.
pub fn validate_spec_structure(specs: &[SpecModule]) -> Vec<SpecLinkViolation> {
    let duplicate_machines = duplicate_names(specs.iter().map(|spec| spec.name.as_str()));
    let by_name: BTreeMap<&str, Option<&SpecModule>> = specs
        .iter()
        .map(|spec| {
            let unique = (!is_blank(&spec.name)
                && !duplicate_machines.contains(spec.name.as_str()))
            .then_some(spec);
            (spec.name.as_str(), unique)
        })
        .collect();
    let machine_names: BTreeSet<&str> = specs
        .iter()
        .map(|spec| spec.name.as_str())
        .filter(|name| !is_blank(name))
        .collect();
    let mut violations: Vec<SpecLinkViolation> = duplicate_machines
        .iter()
        .map(|machine| SpecLinkViolation::DuplicateMachineIdentity {
            machine: (*machine).to_string(),
        })
        .collect();

    for spec in specs {
        if is_blank(&spec.name) {
            violations.push(SpecLinkViolation::BlankSemanticValue {
                container: spec.name.clone(),
                subject: "SpecModule",
                field: "name",
            });
        }
        for action in duplicate_names(spec.actions.iter().map(String::as_str)) {
            violations.push(SpecLinkViolation::DuplicateMemberIdentity {
                machine: spec.name.clone(),
                member: "action",
                name: action.to_string(),
            });
        }
        for variable in duplicate_names(spec.vars.iter().map(|variable| variable.name.as_str())) {
            violations.push(SpecLinkViolation::DuplicateMemberIdentity {
                machine: spec.name.clone(),
                member: "variable",
                name: variable.to_string(),
            });
        }
        for invariant in duplicate_names(
            spec.invariants
                .iter()
                .map(|invariant| invariant.name.as_str()),
        ) {
            violations.push(SpecLinkViolation::DuplicateMemberIdentity {
                machine: spec.name.clone(),
                member: "invariant",
                name: invariant.to_string(),
            });
        }

        for action in &spec.actions {
            push_blank(&mut violations, spec, "action", "name", action);
        }
        for variable in &spec.vars {
            push_blank(&mut violations, spec, "variable", "name", &variable.name);
            push_blank(&mut violations, spec, "variable", "type", &variable.ty);
        }
        for invariant in &spec.invariants {
            push_blank(&mut violations, spec, "invariant", "name", &invariant.name);
            push_blank(
                &mut violations,
                spec,
                "invariant",
                "formula",
                &invariant.formula,
            );
        }
        if let SpecOrigin::External(path) = &spec.origin {
            push_blank(&mut violations, spec, "external origin", "path", path);
        }

        let mut anchor_ids = BTreeSet::new();
        let mut duplicate_anchor_ids = BTreeSet::new();
        let mut waiver_actions = BTreeSet::new();
        let mut duplicate_waiver_actions = BTreeSet::new();
        let mut proof_ids = BTreeSet::new();
        let mut duplicate_proof_ids = BTreeSet::new();
        let mut owned_anchor_actions = BTreeSet::new();
        let mut owned_waiver_actions = BTreeSet::new();

        for anchor in &spec.anchors {
            push_blank(&mut violations, spec, "anchor", "machine", &anchor.machine);
            push_blank(&mut violations, spec, "anchor", "action", &anchor.action);
            push_blank(
                &mut violations,
                spec,
                "anchor",
                "rust_symbol",
                &anchor.rust_symbol,
            );
            push_container_mismatch(
                &mut violations,
                spec,
                &machine_names,
                &anchor.machine,
                &anchor.action,
                "anchor",
            );
            if spec.enforcement == SpecEnforcementMode::Linked {
                if anchor.function.is_none() {
                    violations.push(SpecLinkViolation::TypedTargetRequired {
                        machine: spec.name.clone(),
                        action: anchor.action.clone(),
                        target: "action function",
                    });
                }
                if anchor.projection_target.is_none() {
                    violations.push(SpecLinkViolation::TypedTargetRequired {
                        machine: spec.name.clone(),
                        action: anchor.action.clone(),
                        target: "projection",
                    });
                }
            }
            match anchor.projection_target {
                Some(SpecProjectionTarget::TemporalFieldPathsV1)
                    if anchor.project.as_deref() != Some(TEMPORAL_FIELD_PATH_PROJECTION_V1) =>
                {
                    violations.push(SpecLinkViolation::ProjectionTargetIncompatible {
                        machine: spec.name.clone(),
                        action: anchor.action.clone(),
                        detail: format!(
                            "temporal-field-paths-v1 requires project {:?}",
                            TEMPORAL_FIELD_PATH_PROJECTION_V1
                        ),
                    });
                }
                Some(SpecProjectionTarget::ExternalUnresolved)
                    if matches!(spec.origin, SpecOrigin::Embedded) =>
                {
                    violations.push(SpecLinkViolation::ProjectionTargetIncompatible {
                        machine: spec.name.clone(),
                        action: anchor.action.clone(),
                        detail: "embedded models cannot use external-unresolved projections"
                            .to_string(),
                    });
                }
                _ => {}
            }
            if reference_belongs_to_container(spec, &anchor.machine, &anchor.action) {
                owned_anchor_actions.insert(anchor.action.as_str());
                let identity = match anchor.function {
                    Some(function) => {
                        format!("{:?} -> function #{}", anchor.action, function.index())
                    }
                    None => format!(
                        "{:?} -> rust_symbol {:?}",
                        anchor.action, anchor.rust_symbol
                    ),
                };
                if !anchor_ids.insert(identity.clone())
                    && duplicate_anchor_ids.insert(identity.clone())
                {
                    violations.push(SpecLinkViolation::DuplicateBindingIdentity {
                        machine: spec.name.clone(),
                        binding: "anchor",
                        identity,
                    });
                }
            }
        }
        for waiver in &spec.waivers {
            push_blank(&mut violations, spec, "waiver", "machine", &waiver.machine);
            push_blank(&mut violations, spec, "waiver", "action", &waiver.action);
            push_blank(&mut violations, spec, "waiver", "reason", &waiver.reason);
            push_container_mismatch(
                &mut violations,
                spec,
                &machine_names,
                &waiver.machine,
                &waiver.action,
                "waiver",
            );
            if reference_belongs_to_container(spec, &waiver.machine, &waiver.action) {
                owned_waiver_actions.insert(waiver.action.as_str());
                if !waiver_actions.insert(waiver.action.as_str())
                    && duplicate_waiver_actions.insert(waiver.action.as_str())
                {
                    violations.push(SpecLinkViolation::DuplicateBindingIdentity {
                        machine: spec.name.clone(),
                        binding: "waiver",
                        identity: format!("action {:?}", waiver.action),
                    });
                }
            }
        }
        for proof in &spec.proofs {
            push_blank(&mut violations, spec, "proof", "machine", &proof.machine);
            push_blank(&mut violations, spec, "proof", "action", &proof.action);
            push_blank(
                &mut violations,
                spec,
                "proof",
                "proof_name",
                &proof.proof_name,
            );
            push_container_mismatch(
                &mut violations,
                spec,
                &machine_names,
                &proof.machine,
                &proof.action,
                "proof",
            );
            if reference_belongs_to_container(spec, &proof.machine, &proof.action)
                && !is_blank(&proof.proof_name)
            {
                let identity = format!(
                    "action {:?}, kind {}, proof_name {:?}",
                    proof.action,
                    proof.kind.tag(),
                    proof.proof_name
                );
                if !proof_ids.insert(identity.clone())
                    && duplicate_proof_ids.insert(identity.clone())
                {
                    violations.push(SpecLinkViolation::DuplicateBindingIdentity {
                        machine: spec.name.clone(),
                        binding: "proof",
                        identity,
                    });
                }
            }
        }
        for action in owned_anchor_actions.intersection(&owned_waiver_actions) {
            violations.push(SpecLinkViolation::AnchorWaiverConflict {
                machine: spec.name.clone(),
                action: (*action).to_string(),
            });
        }
    }

    // Ob.4 + Ob.1 for every machine/action reference. A known foreign target
    // is already an S1 ownership error; a missing foreign target remains Ob.4.
    // Proof closure is unconditional: only proof-name-to-harness resolution
    // (L1) needs a manifest.
    for spec in specs {
        for anchor in &spec.anchors {
            if reference_needs_resolution(&by_name, spec, &anchor.machine, &anchor.action) {
                check_ref(
                    &by_name,
                    &anchor.machine,
                    &anchor.action,
                    "anchor",
                    &format!(
                        "function={}, rust_symbol={:?}",
                        anchor
                            .function
                            .map(|function| function.index().to_string())
                            .unwrap_or_else(|| "unresolved".to_string()),
                        anchor.rust_symbol
                    ),
                    &mut violations,
                );
            }
        }
        for waiver in &spec.waivers {
            if reference_needs_resolution(&by_name, spec, &waiver.machine, &waiver.action) {
                check_ref(
                    &by_name,
                    &waiver.machine,
                    &waiver.action,
                    "waiver",
                    &format!("reason={:?}", waiver.reason),
                    &mut violations,
                );
            }
        }
        for proof in &spec.proofs {
            if reference_needs_resolution(&by_name, spec, &proof.machine, &proof.action) {
                check_ref(
                    &by_name,
                    &proof.machine,
                    &proof.action,
                    "proof",
                    &format!("proof_name={:?}", proof.proof_name),
                    &mut violations,
                );
            }
        }
    }

    // L2 is structural integrity of every present, owned anchor. An explicit
    // waiver can cover an absent binding for Ob.3, but cannot legitimize a
    // malformed anchor that is present.
    for spec in specs {
        for anchor in spec
            .anchors
            .iter()
            .filter(|anchor| reference_belongs_to_container(spec, &anchor.machine, &anchor.action))
        {
            let present = anchor
                .project
                .as_deref()
                .is_some_and(|p| !p.trim().is_empty());
            if !present {
                violations.push(SpecLinkViolation::ProjectionMissing {
                    machine: spec.name.clone(),
                    action: anchor.action.clone(),
                });
            }
        }
    }

    normalize_violations(&mut violations);
    violations
}

/// Validate every populated module-local action and projection target.
///
/// This is module-aware S2 integrity shared by the public linker and the full
/// module validator. Projection functions must be body-bearing, name-agreeing,
/// non-variadic functions with exactly one immutable-reference parameter and
/// exactly one result: the canonical `(&Concrete) -> Abstract` contract.
pub fn validate_spec_executable_links(module: &Module) -> Vec<SpecLinkViolation> {
    let mut violations = Vec::new();
    for spec in &module.spec_modules {
        for anchor in &spec.anchors {
            if !reference_belongs_to_container(spec, &anchor.machine, &anchor.action) {
                continue;
            }
            if let Some(function) = anchor.function {
                check_executable_target(
                    module,
                    spec,
                    anchor,
                    "action",
                    function,
                    anchor.rust_symbol.as_str(),
                    false,
                    &mut violations,
                );
            }
            if let Some(SpecProjectionTarget::Function(function)) = anchor.projection_target {
                check_executable_target(
                    module,
                    spec,
                    anchor,
                    "projection",
                    function,
                    anchor.project.as_deref().unwrap_or_default(),
                    true,
                    &mut violations,
                );
            }
        }
    }
    normalize_violations(&mut violations);
    violations
}

#[allow(clippy::too_many_arguments)]
fn check_executable_target(
    module: &Module,
    spec: &SpecModule,
    anchor: &SpecAnchor,
    target: &'static str,
    function: FuncId,
    expected_name: &str,
    require_projection_signature: bool,
    violations: &mut Vec<SpecLinkViolation>,
) {
    let invalid = |detail: String, violations: &mut Vec<SpecLinkViolation>| {
        violations.push(SpecLinkViolation::ExecutableTargetInvalid {
            machine: spec.name.clone(),
            action: anchor.action.clone(),
            target,
            function: function.index(),
            detail,
        });
    };

    let definition_count = module
        .functions
        .iter()
        .filter(|candidate| candidate.id == function)
        .count();
    if definition_count > 1 {
        invalid(
            format!("function id is ambiguous ({definition_count} definitions)"),
            violations,
        );
        return;
    }
    let Some(linked) = module.function_by_id(function) else {
        invalid(
            format!("function id is not present in module {:?}", module.name),
            violations,
        );
        return;
    };
    if linked.is_declaration() {
        invalid("function is a bodyless declaration".to_string(), violations);
        return;
    }
    if !is_blank(expected_name) && linked.name != expected_name {
        invalid(
            format!(
                "{} {:?} does not match typed target {:?}",
                if target == "action" {
                    "rust_symbol"
                } else {
                    "project"
                },
                expected_name,
                linked.name
            ),
            violations,
        );
        return;
    }
    if !require_projection_signature {
        return;
    }

    let Some(signature) = module.func_type(linked.ty) else {
        invalid(
            format!(
                "function references missing signature type #{}",
                linked.ty.index()
            ),
            violations,
        );
        return;
    };
    let conforms = !signature.is_vararg
        && signature.params.len() == 1
        && signature.returns.len() == 1
        && matches!(signature.params[0], Ty::Ref(_));
    if !conforms {
        invalid(
            format!(
                "projection signature must be non-variadic (&T) -> R, got params={:?}, \
                 returns={:?}, vararg={}",
                signature.params, signature.returns, signature.is_vararg
            ),
            violations,
        );
    }
}

/// Run the certifying `spec-link` pass over a module's `SpecModule`s.
///
/// Enforces S0/S1/S2, obligations 1, 3, and 4, and L1/L2 (see module docs).
/// Returns a [`SpecLinkReport`] carrying the per-machine coverage, every
/// violation, and machine-readable non-certification reasons. A supplied
/// manifest is structurally validated before L1 resolution. Linked proof
/// bindings require one by default; the only override is the explicit
/// exploratory option.
///
/// This is the single source of truth for the obligation logic — both the
/// `trust-ir-cli spec-link` subcommand and the teeth tests call it.
pub fn link_spec_modules(
    module: &Module,
    manifest: Option<&HarnessManifest>,
    options: SpecLinkOptions,
) -> Result<SpecLinkReport, HarnessManifestError> {
    let specs = &module.spec_modules;
    let mut violations = validate_spec_structure(specs);
    if is_blank(&module.name) {
        violations.push(SpecLinkViolation::BlankSemanticValue {
            container: module.name.clone(),
            subject: "Module",
            field: "name",
        });
    }
    violations.extend(validate_spec_executable_links(module));
    let mut non_certifying_reasons = Vec::new();

    // Ob.3 coverage is controlled solely by the explicit mode. Removing the
    // last anchor from a Linked machine therefore exposes every unwaived action
    // instead of silently downgrading the machine to design intent.
    for spec in specs {
        if spec.enforcement != SpecEnforcementMode::Linked {
            non_certifying_reasons.push(SpecNonCertificationReason::DesignOnlyMachine {
                machine: spec.name.clone(),
            });
            continue;
        }
        let anchored = spec.anchored_actions();
        let waived = spec.waived_actions();
        for action in &spec.actions {
            let covered = anchored.contains(action.as_str()) || waived.contains(action.as_str());
            if !covered {
                violations.push(SpecLinkViolation::ActionUncovered {
                    machine: spec.name.clone(),
                    action: action.clone(),
                });
            }
        }
        for anchor in spec
            .anchors
            .iter()
            .filter(|anchor| reference_belongs_to_container(spec, &anchor.machine, &anchor.action))
        {
            if matches!(
                anchor.projection_target,
                Some(SpecProjectionTarget::ExternalUnresolved)
            ) {
                non_certifying_reasons.push(
                    SpecNonCertificationReason::ExternalProjectionUnresolved {
                        machine: spec.name.clone(),
                        action: anchor.action.clone(),
                    },
                );
            }
        }
    }

    match manifest {
        Some(manifest) => violations.extend(link_proofs(specs, manifest)?),
        None => {
            for spec in specs.iter().filter(|spec| !spec.proofs.is_empty()) {
                let linked = spec.enforcement == SpecEnforcementMode::Linked;
                let exploratory = linked && options.allow_unverified_linked_proofs;
                if (linked || options.require_manifest_for_design_only) && !exploratory {
                    violations.push(SpecLinkViolation::ProofManifestRequired {
                        machine: spec.name.clone(),
                    });
                }
                if linked {
                    non_certifying_reasons.push(
                        SpecNonCertificationReason::ProofManifestUnverified {
                            machine: spec.name.clone(),
                        },
                    );
                }
            }
        }
    }

    // Coverage summary, deterministically ordered by machine name.
    let mut coverage: Vec<SpecCoverage> = specs
        .iter()
        .map(|spec| {
            let anchored = spec.anchored_actions();
            let waived = spec.waived_actions();
            let anchored_count = spec
                .actions
                .iter()
                .filter(|a| anchored.contains(a.as_str()))
                .count();
            let waived_only = spec
                .actions
                .iter()
                .filter(|a| !anchored.contains(a.as_str()) && waived.contains(a.as_str()))
                .count();
            SpecCoverage {
                machine: spec.name.clone(),
                origin: spec.origin.label(),
                enforcement: spec.enforcement,
                total_actions: spec.actions.len(),
                anchored: anchored_count,
                waived: waived_only,
                ratio: spec.coverage_ratio(),
                actively_anchored: spec.is_actively_anchored(),
            }
        })
        .collect();
    coverage.sort_by(|a, b| {
        a.machine
            .cmp(&b.machine)
            .then_with(|| a.origin.cmp(&b.origin))
            .then_with(|| a.enforcement.tag().cmp(b.enforcement.tag()))
            .then_with(|| a.total_actions.cmp(&b.total_actions))
            .then_with(|| a.anchored.cmp(&b.anchored))
            .then_with(|| a.waived.cmp(&b.waived))
            .then_with(|| a.actively_anchored.cmp(&b.actively_anchored))
            .then_with(|| a.ratio.total_cmp(&b.ratio))
    });
    normalize_violations(&mut violations);
    non_certifying_reasons.sort();
    non_certifying_reasons.dedup();

    Ok(SpecLinkReport {
        coverage,
        violations,
        non_certifying_reasons,
    })
}

/// Return each repeated name exactly once, in deterministic lexical order.
fn duplicate_names<'a>(names: impl IntoIterator<Item = &'a str>) -> BTreeSet<&'a str> {
    let mut seen = BTreeSet::new();
    let mut duplicates = BTreeSet::new();
    for name in names {
        if !is_blank(name) && !seen.insert(name) {
            duplicates.insert(name);
        }
    }
    duplicates
}

fn is_blank(value: &str) -> bool {
    value.trim().is_empty()
}

fn push_blank(
    violations: &mut Vec<SpecLinkViolation>,
    container: &SpecModule,
    subject: &'static str,
    field: &'static str,
    value: &str,
) {
    if is_blank(value) {
        violations.push(SpecLinkViolation::BlankSemanticValue {
            container: container.name.clone(),
            subject,
            field,
        });
    }
}

fn push_container_mismatch(
    violations: &mut Vec<SpecLinkViolation>,
    container: &SpecModule,
    machine_names: &BTreeSet<&str>,
    machine: &str,
    action: &str,
    from: &'static str,
) {
    if !is_blank(&container.name)
        && !is_blank(machine)
        && machine != container.name
        && machine_names.contains(machine)
    {
        violations.push(SpecLinkViolation::ReferenceContainerMismatch {
            container: container.name.clone(),
            machine: machine.to_string(),
            action: action.to_string(),
            from,
        });
    }
}

fn reference_belongs_to_container(container: &SpecModule, machine: &str, action: &str) -> bool {
    !is_blank(&container.name)
        && !is_blank(machine)
        && !is_blank(action)
        && machine == container.name
}

fn reference_needs_resolution(
    by_name: &BTreeMap<&str, Option<&SpecModule>>,
    container: &SpecModule,
    machine: &str,
    action: &str,
) -> bool {
    !is_blank(&container.name)
        && !is_blank(machine)
        && !is_blank(action)
        && (machine == container.name || !by_name.contains_key(machine))
}

fn violation_key(violation: &SpecLinkViolation) -> (u8, &str, &str, &str, &str, &str, u32) {
    match violation {
        SpecLinkViolation::DuplicateMachineIdentity { machine } => {
            (0, machine, "machine", "", "", "", 0)
        }
        SpecLinkViolation::DuplicateMemberIdentity {
            machine,
            member,
            name,
        } => (1, machine, member, name, "", "", 0),
        SpecLinkViolation::BlankSemanticValue {
            container,
            subject,
            field,
        } => (2, container, subject, field, "", "", 0),
        SpecLinkViolation::DuplicateBindingIdentity {
            machine,
            binding,
            identity,
        } => (3, machine, binding, identity, "", "", 0),
        SpecLinkViolation::AnchorWaiverConflict { machine, action } => {
            (4, machine, action, "", "", "", 0)
        }
        SpecLinkViolation::ReferenceContainerMismatch {
            container,
            machine,
            action,
            from,
        } => (5, container, machine, action, from, "", 0),
        SpecLinkViolation::TypedTargetRequired {
            machine,
            action,
            target,
        } => (6, machine, action, target, "", "", 0),
        SpecLinkViolation::ProjectionTargetIncompatible {
            machine,
            action,
            detail,
        } => (7, machine, action, detail, "", "", 0),
        SpecLinkViolation::ExecutableTargetInvalid {
            machine,
            action,
            target,
            function,
            detail,
        } => (8, machine, action, target, detail, "", *function),
        SpecLinkViolation::ActionMissing {
            machine,
            action,
            from,
            detail,
        } => (9, machine, action, from, detail, "", 0),
        SpecLinkViolation::ProjectionMissing { machine, action } => {
            (10, machine, action, "", "", "", 0)
        }
        SpecLinkViolation::ActionUncovered { machine, action } => {
            (11, machine, action, "", "", "", 0)
        }
        SpecLinkViolation::MachineMissing {
            machine,
            action,
            from,
            detail,
        } => (12, machine, action, from, detail, "", 0),
        SpecLinkViolation::ProofUnresolved {
            machine,
            action,
            proof_name,
        } => (13, machine, action, proof_name, "", "", 0),
        SpecLinkViolation::ProofManifestRequired { machine } => (14, machine, "", "", "", "", 0),
    }
}

pub(crate) fn normalize_violations(violations: &mut Vec<SpecLinkViolation>) {
    violations.sort_by(|left, right| violation_key(left).cmp(&violation_key(right)));
    violations.dedup();
}

/// Shared Ob.4-then-Ob.1 check for a single (machine, action) reference. Pushes
/// a `MachineMissing` if the machine does not resolve, otherwise an
/// `ActionMissing` if the action is not declared by that machine.
fn check_ref(
    by_name: &BTreeMap<&str, Option<&SpecModule>>,
    machine: &str,
    action: &str,
    from: &'static str,
    detail: &str,
    violations: &mut Vec<SpecLinkViolation>,
) {
    match by_name.get(machine) {
        None => violations.push(SpecLinkViolation::MachineMissing {
            machine: machine.to_string(),
            action: action.to_string(),
            from,
            detail: detail.to_string(),
        }),
        Some(None) => {}
        Some(Some(spec)) => {
            if !spec.has_action(action) {
                violations.push(SpecLinkViolation::ActionMissing {
                    machine: machine.to_string(),
                    action: action.to_string(),
                    from,
                    detail: detail.to_string(),
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Block, BlockId, FuncTy, Function, Inst, InstrNode};

    fn module_with_specs(specs: Vec<SpecModule>) -> Module {
        let mut module = Module::new("spec-tests");
        let ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "action", ty, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(entry);
        module.add_function(function);
        module.spec_modules = specs;
        module
    }

    fn link(specs: Vec<SpecModule>) -> SpecLinkReport {
        let module = module_with_specs(specs);
        link_spec_modules(
            &module,
            None,
            SpecLinkOptions::exploratory_allow_unverified_proofs(),
        )
        .expect("no manifest to validate")
    }

    fn ring_pass() -> SpecModule {
        SpecModule {
            name: "ring".to_string(),
            vars: vec![SpecVar::new("seq", "Int")],
            actions: vec!["Push".to_string(), "Pop".to_string()],
            invariants: vec![SpecInvariant::new("BoundedSeq", "seq <= 7")],
            anchors: vec![SpecAnchor {
                machine: "ring".to_string(),
                action: "Push".to_string(),
                function: Some(FuncId::new(0)),
                rust_symbol: "action".to_string(),
                span: "src/ring.rs:42:4".to_string(),
                project: Some("ring::project".to_string()),
                projection_target: Some(SpecProjectionTarget::ExternalUnresolved),
            }],
            waivers: vec![SpecWaiver {
                machine: "ring".to_string(),
                action: "Pop".to_string(),
                reason: "pop has no shipping handler yet".to_string(),
            }],
            proofs: vec![],
            origin: SpecOrigin::External("ring.tla".to_string()),
            enforcement: SpecEnforcementMode::Linked,
        }
    }

    #[test]
    fn passing_module_has_no_violations() {
        let report = link(vec![ring_pass()]);
        assert!(report.is_ok(), "violations: {:?}", report.violations);
        assert!(!report.is_certifying());
        assert!(report.non_certifying_reasons.iter().any(|reason| matches!(
            reason,
            SpecNonCertificationReason::ExternalProjectionUnresolved { machine, action }
                if machine == "ring" && action == "Push"
        )));
        assert_eq!(report.coverage.len(), 1);
        assert!((report.coverage[0].ratio - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn duplicate_identities_are_single_and_order_independent() {
        let mut first = SpecModule::new("same");
        first.actions.push("A".to_string());
        let mut second = SpecModule::new("same");
        second.actions.push("B".to_string());
        let mut third = SpecModule::new("same");
        third.actions.push("C".to_string());

        let forward = link(vec![first.clone(), second.clone(), third.clone()]);
        let reverse = link(vec![third, second, first]);
        assert_eq!(forward, reverse);
        assert_eq!(
            forward
                .violations
                .iter()
                .filter(|violation| matches!(
                    violation,
                    SpecLinkViolation::DuplicateMachineIdentity { machine } if machine == "same"
                ))
                .count(),
            1
        );

        let mut members = SpecModule::new("members");
        members.actions = vec!["Step".into(), "Step".into(), "Step".into()];
        members.vars = vec![SpecVar::new("state", "Int"), SpecVar::new("state", "Nat")];
        members.invariants = vec![
            SpecInvariant::new("Safe", "TRUE"),
            SpecInvariant::new("Safe", "FALSE"),
        ];
        let structural = validate_spec_structure(&[members]);
        assert_eq!(
            structural
                .iter()
                .filter(|violation| matches!(
                    violation,
                    SpecLinkViolation::DuplicateMemberIdentity { .. }
                ))
                .count(),
            3
        );
    }

    #[test]
    fn blank_semantic_values_and_duplicate_bindings_fail_closed() {
        let mut m = ring_pass();
        m.vars[0].ty = "  ".to_string();
        m.invariants[0].formula = "\t".to_string();
        m.origin = SpecOrigin::External(" ".to_string());

        m.anchors.push(m.anchors[0].clone());
        m.waivers.push(m.waivers[0].clone());
        m.waivers.push(SpecWaiver {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            reason: "temporary absence".to_string(),
        });
        let proof = SpecProof {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            proof_name: "ring_push_refines".to_string(),
            kind: ProofKind::Kani,
        };
        m.proofs.extend([proof.clone(), proof]);

        let violations = validate_spec_structure(&[m]);
        for (subject, field) in [
            ("variable", "type"),
            ("invariant", "formula"),
            ("external origin", "path"),
        ] {
            assert!(violations.iter().any(|violation| matches!(
                violation,
                SpecLinkViolation::BlankSemanticValue {
                    subject: actual_subject,
                    field: actual_field,
                    ..
                } if *actual_subject == subject && *actual_field == field
            )));
        }
        for binding in ["anchor", "waiver", "proof"] {
            assert!(violations.iter().any(|violation| matches!(
                violation,
                SpecLinkViolation::DuplicateBindingIdentity {
                    binding: actual,
                    ..
                } if *actual == binding
            )));
        }
        assert!(violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::AnchorWaiverConflict { action, .. } if action == "Push"
        )));
    }

    #[test]
    fn ob1_bogus_action() {
        let mut m = ring_pass();
        m.anchors.push(SpecAnchor {
            machine: "ring".to_string(),
            action: "Nonexistent".to_string(),
            function: Some(FuncId::new(0)),
            rust_symbol: "action".to_string(),
            span: "x:1:1".to_string(),
            // Non-empty projection so L2 does not also fire — this fixture
            // isolates Ob.1.
            project: Some("ring::project".to_string()),
            projection_target: Some(SpecProjectionTarget::ExternalUnresolved),
        });
        let report = link(vec![m]);
        assert!(!report.is_ok());
        assert!(report.violations.iter().any(|v| v.obligation() == "Ob.1"));
        assert!(
            report.violations.iter().all(|v| v.obligation() == "Ob.1"),
            "only Ob.1 should fire: {:?}",
            report.violations
        );
    }

    #[test]
    fn ob4_dangling_machine() {
        let mut m = ring_pass();
        m.anchors.push(SpecAnchor {
            machine: "ghost".to_string(),
            action: "Push".to_string(),
            function: Some(FuncId::new(0)),
            rust_symbol: "action".to_string(),
            span: "x:1:1".to_string(),
            // Non-empty projection so L2 does not also fire — this fixture
            // isolates Ob.4.
            project: Some("ghost::project".to_string()),
            projection_target: Some(SpecProjectionTarget::ExternalUnresolved),
        });
        let report = link(vec![m]);
        assert!(!report.is_ok());
        assert!(
            report.violations.iter().all(|v| v.obligation() == "Ob.4"),
            "only Ob.4 should fire: {:?}",
            report.violations
        );
    }

    #[test]
    fn proof_action_closure_is_unconditional_without_a_manifest() {
        let mut m = ring_pass();
        m.proofs.push(SpecProof {
            machine: "ring".to_string(),
            action: "Nonexistent".to_string(),
            proof_name: "irrelevant_until_l1".to_string(),
            kind: ProofKind::Kani,
        });

        let report = link(vec![m]);
        assert_eq!(report.violations.len(), 1, "got: {:?}", report.violations);
        assert!(matches!(
            &report.violations[0],
            SpecLinkViolation::ActionMissing { from: "proof", action, .. }
                if action == "Nonexistent"
        ));
    }

    #[test]
    fn proof_machine_closure_is_unconditional_without_a_manifest() {
        let mut m = ring_pass();
        m.proofs.push(SpecProof {
            machine: "ghost".to_string(),
            action: "Push".to_string(),
            proof_name: "irrelevant_until_l1".to_string(),
            kind: ProofKind::Kani,
        });

        let report = link(vec![m]);
        assert_eq!(report.violations.len(), 1, "got: {:?}", report.violations);
        assert!(matches!(
            &report.violations[0],
            SpecLinkViolation::MachineMissing { from: "proof", machine, .. }
                if machine == "ghost"
        ));
    }

    #[test]
    fn ob3_uncovered_action() {
        let mut m = ring_pass();
        // Remove the waiver so linked action Pop is neither anchored nor waived.
        m.waivers.clear();
        let report = link(vec![m]);
        assert!(!report.is_ok());
        assert!(
            report.violations.iter().all(|v| v.obligation() == "Ob.3"),
            "only Ob.3 should fire: {:?}",
            report.violations
        );
        assert_eq!(report.violations.len(), 1);
    }

    #[test]
    fn design_only_machine_skips_coverage_gate() {
        // DesignOnly explicitly declines the total-coverage claim.
        let m = SpecModule {
            name: "design_only".to_string(),
            vars: vec![],
            actions: vec!["A".to_string(), "B".to_string()],
            invariants: vec![],
            anchors: vec![],
            waivers: vec![],
            proofs: vec![],
            origin: SpecOrigin::External("Sandbox.tla".to_string()),
            enforcement: SpecEnforcementMode::DesignOnly,
        };
        let report = link(vec![m]);
        assert!(report.is_ok(), "violations: {:?}", report.violations);
        assert!(!report.coverage[0].actively_anchored);
    }

    #[test]
    fn foreign_anchor_cannot_cover_or_activate_its_container() {
        // Both machines deliberately share the same action name. Counting by
        // action alone used to let an anchor stored under A but targeting B make
        // A look fully covered while B remained unanchored.
        let mut a = SpecModule::new("A");
        a.actions.push("Step".to_string());
        a.anchors.push(SpecAnchor {
            machine: "B".to_string(),
            action: "Step".to_string(),
            function: None,
            rust_symbol: "b::step".to_string(),
            span: "b.rs:1:1".to_string(),
            project: Some("b::project".to_string()),
            projection_target: None,
        });
        let mut b = SpecModule::new("B");
        b.actions.push("Step".to_string());

        let report = link(vec![a, b]);
        let a_coverage = report
            .coverage
            .iter()
            .find(|coverage| coverage.machine == "A")
            .unwrap();
        assert!(report.violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::ReferenceContainerMismatch {
                container,
                machine,
                action,
                from: "anchor",
            } if container == "A" && machine == "B" && action == "Step"
        )));
        assert!(!a_coverage.actively_anchored);
        assert_eq!(a_coverage.anchored, 0);
        assert_eq!(a_coverage.ratio, 0.0);
    }

    #[test]
    fn l2_anchor_with_none_projection_fires() {
        // Every present owned anchor whose `project` is None produces L2.
        let mut m = ring_pass();
        m.anchors[0].project = None;
        let report = link(vec![m]);
        assert!(!report.is_ok());
        assert!(
            report.violations.iter().any(|v| matches!(
                v,
                SpecLinkViolation::ProjectionMissing { action, .. } if action == "Push"
            )),
            "L2 must fire for Push: {:?}",
            report.violations
        );
        assert!(
            report.violations.iter().all(|v| v.obligation() == "L2"),
            "only L2 should fire: {:?}",
            report.violations
        );
    }

    #[test]
    fn l2_anchor_with_empty_projection_fires() {
        // `Some("")` is just as inert as `None` — the audit's literal `project=""`.
        let mut m = ring_pass();
        m.anchors[0].project = Some(String::new());
        let report = link(vec![m]);
        assert!(!report.is_ok());
        assert!(
            report.violations.iter().all(|v| v.obligation() == "L2"),
            "only L2 should fire: {:?}",
            report.violations
        );
    }

    #[test]
    fn l2_anchor_with_whitespace_only_projection_fires() {
        let mut m = ring_pass();
        m.anchors[0].project = Some(" \t\n ".to_string());
        let report = link(vec![m]);
        assert!(!report.is_ok());
        assert!(
            report.violations.iter().all(|v| v.obligation() == "L2"),
            "only L2 should fire: {:?}",
            report.violations
        );
    }

    #[test]
    fn l2_waiver_cannot_legitimize_a_malformed_anchor() {
        // A waiver may stand in for an absent anchor, but once an anchor is
        // present it must independently satisfy projection integrity.
        let mut m = ring_pass();
        m.anchors[0].project = None;
        m.waivers.push(SpecWaiver {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            reason: "covered by waiver, not projection".to_string(),
        });
        let report = link(vec![m]);
        assert!(!report.is_ok());
        assert!(report.violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::ProjectionMissing { machine, action }
                if machine == "ring" && action == "Push"
        )));
    }

    #[test]
    fn l2_machine_without_anchors_has_no_projection_to_validate() {
        let m = SpecModule {
            name: "design_only".to_string(),
            vars: vec![],
            actions: vec!["A".to_string()],
            invariants: vec![],
            anchors: vec![],
            waivers: vec![],
            proofs: vec![],
            origin: SpecOrigin::External("Sandbox.tla".to_string()),
            enforcement: SpecEnforcementMode::DesignOnly,
        };
        let report = link(vec![m]);
        assert!(report.is_ok(), "violations: {:?}", report.violations);
    }

    #[test]
    fn explicit_mode_replaces_the_last_anchor_heuristic() {
        let mut linked = SpecModule::linked("Machine");
        linked.origin = SpecOrigin::External("Machine.tla".to_string());
        linked.actions = vec!["A".to_string(), "B".to_string()];
        let linked_report = link(vec![linked]);
        assert_eq!(
            linked_report
                .violations
                .iter()
                .filter(|violation| matches!(violation, SpecLinkViolation::ActionUncovered { .. }))
                .count(),
            2,
            "Linked must enforce Ob.3 with zero anchors"
        );

        let mut design = SpecModule::design_only("Machine");
        design.origin = SpecOrigin::External("Machine.tla".to_string());
        design.actions = vec!["A".to_string(), "B".to_string()];
        let design_report = link(vec![design]);
        assert!(design_report.is_ok());
        assert!(!design_report.is_certifying());
        assert!(matches!(
            design_report.non_certifying_reasons.as_slice(),
            [SpecNonCertificationReason::DesignOnlyMachine { machine }] if machine == "Machine"
        ));
    }

    #[test]
    fn linked_anchor_requires_both_typed_targets_regardless_of_origin() {
        let mut spec = SpecModule::linked("Machine");
        spec.actions.push("Step".to_string());
        spec.anchors.push(SpecAnchor {
            machine: "Machine".to_string(),
            action: "Step".to_string(),
            rust_symbol: "crate::Machine::step".to_string(),
            span: "fixture.rs:1:1".to_string(),
            project: Some("crate::Machine::project".to_string()),
            function: None,
            projection_target: None,
        });

        for origin in [
            SpecOrigin::Embedded,
            SpecOrigin::External("Machine.tla".to_string()),
        ] {
            spec.origin = origin;
            let violations = validate_spec_structure(&[spec.clone()]);
            let targets: Vec<_> = violations
                .iter()
                .filter_map(|violation| match violation {
                    SpecLinkViolation::TypedTargetRequired { target, .. } => Some(*target),
                    _ => None,
                })
                .collect();
            assert_eq!(targets, vec!["action function", "projection"]);
        }
    }

    #[test]
    fn linked_proof_manifest_policy_is_fail_closed_and_exploratory_is_noncertifying() {
        let mut spec = ring_pass();
        spec.anchors[0].projection_target = Some(SpecProjectionTarget::TemporalFieldPathsV1);
        spec.anchors[0].project = Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.to_string());
        spec.proofs.push(SpecProof {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            proof_name: "ring_push_refines".to_string(),
            kind: ProofKind::Kani,
        });
        let mut module = module_with_specs(vec![spec]);
        module.name = "proof-policy".to_string();

        let required = link_spec_modules(&module, None, SpecLinkOptions::default())
            .expect("no manifest to validate");
        assert!(required.violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::ProofManifestRequired { machine } if machine == "ring"
        )));

        let exploratory = link_spec_modules(
            &module,
            None,
            SpecLinkOptions::exploratory_allow_unverified_proofs(),
        )
        .expect("no manifest to validate");
        assert!(exploratory.is_ok());
        assert!(!exploratory.is_certifying());
        assert!(exploratory.non_certifying_reasons.iter().any(|reason| matches!(
            reason,
            SpecNonCertificationReason::ProofManifestUnverified { machine } if machine == "ring"
        )));

        let manifest = HarnessManifest::from_names(["ring_push_refines"]);
        let certified = link_spec_modules(&module, Some(&manifest), SpecLinkOptions::default())
            .expect("valid manifest");
        assert!(certified.is_certifying(), "got: {certified:?}");
    }

    fn executable_link_module(projection_param: Ty) -> Module {
        let mut module = Module::new("executable-links");
        let action_ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let projection_ty = module.add_func_type(FuncTy {
            params: vec![projection_param],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        for (id, name, ty) in [(0, "action", action_ty), (1, "project", projection_ty)] {
            let mut function = Function::new(FuncId::new(id), name, ty, BlockId::new(0));
            let mut entry = Block::new(BlockId::new(0));
            entry
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            function.blocks.push(entry);
            module.add_function(function);
        }

        let mut spec = SpecModule::linked("Machine");
        spec.actions.push("Step".to_string());
        spec.anchors.push(SpecAnchor {
            machine: "Machine".to_string(),
            action: "Step".to_string(),
            rust_symbol: "action".to_string(),
            span: "fixture.rs:1:1".to_string(),
            project: Some("project".to_string()),
            function: Some(FuncId::new(0)),
            projection_target: Some(SpecProjectionTarget::Function(FuncId::new(1))),
        });
        module.spec_modules.push(spec);
        module
    }

    #[test]
    fn typed_projection_requires_exact_target_name_body_and_signature() {
        let valid = executable_link_module(Ty::Ref(Box::new(Ty::I32)));
        let report = link_spec_modules(&valid, None, SpecLinkOptions::default())
            .expect("no manifest to validate");
        assert!(report.is_certifying(), "got: {report:?}");

        let mut blank_module_identity = valid.clone();
        blank_module_identity.name = " \t ".to_string();
        let report = link_spec_modules(&blank_module_identity, None, SpecLinkOptions::default())
            .expect("no manifest to validate");
        assert!(report.violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::BlankSemanticValue {
                subject: "Module",
                field: "name",
                ..
            }
        )));

        let invalid = executable_link_module(Ty::I32);
        let violations = validate_spec_executable_links(&invalid);
        assert!(violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::ExecutableTargetInvalid {
                target: "projection",
                detail,
                ..
            } if detail.contains("(&T) -> R")
        )));

        let mut ambiguous = valid.clone();
        ambiguous.functions.push(ambiguous.functions[1].clone());
        let violations = validate_spec_executable_links(&ambiguous);
        assert!(violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::ExecutableTargetInvalid {
                target: "projection",
                detail,
                ..
            } if detail.contains("ambiguous (2 definitions)")
        )));
    }
}
