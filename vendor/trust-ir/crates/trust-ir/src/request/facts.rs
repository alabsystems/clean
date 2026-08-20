// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Stable id for a request inside a native verification bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeRequestId(pub u32);

impl NativeRequestId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    pub const fn index(self) -> u32 {
        self.0
    }
}

impl core::fmt::Display for NativeRequestId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Producer of a native verification bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeBundleProducer {
    /// Direct typed Rust/source frontend lowering (THIR-derived, before the
    /// retained MIR-compatibility path) into TrustIr.
    #[cfg_attr(feature = "serde", serde(rename = "Trust"))]
    TRust,
    /// tSwift frontend. DEPRECATED producer (never shipped) — the variant
    /// and its serde name are retained for wire compatibility only.
    #[cfg_attr(feature = "serde", serde(rename = "tSwift"))]
    TSwift,
    /// tC frontend. DEPRECATED producer (never shipped) — the variant and
    /// its serde name are retained for wire compatibility only.
    #[cfg_attr(feature = "serde", serde(rename = "tC"))]
    TC,
    /// Native TrustIr transform, MIR-compatibility bridge, or verifier pipeline.
    #[cfg_attr(feature = "serde", serde(rename = "TrustIr"))]
    TrustIr,
}

/// Native input artifact that backs a verification bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeAdapterInput {
    /// rustc MIR body exported by tRust before TrustIr lowering.
    RustMir { body_digest: ProofDigest },
    /// Already-native TrustIr input. The bundle's `trust_ir_module_digest` is the
    /// artifact digest.
    TrustIrModule,
}

/// TrustVc operation requested by a native bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustVcVerificationMode {
    ImportProofCertificates,
    MergeProofCertificates,
    /// Ask trust-vc to DISCHARGE the request's obligations itself, rather than
    /// checking certificates someone else produced.
    ///
    /// APPEND-ONLY. The three stable tag tables in `request::digest`
    /// (`write_trust_vc_mode_stable`, `native_request_mode_tag`,
    /// `native_evidence_bundle_mode_tag`) spell their tags as literals, and the
    /// evidence-bundle sort key orders by that tag, so appending preserves every
    /// existing bundle digest byte-for-byte. INSERTING a variant ahead of these
    /// would reorder that sort and rewrite every digest in the constellation.
    ///
    /// "Discharge", not "solve": ay solves, trust-vc discharges — matching
    /// `ProofStatus::Discharged` and this enum's verb+object convention.
    DischargeProofObligations,
}

/// TrustMc operation requested by a native bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustMcVerificationMode {
    BoundedModelCheck,
    Chc,
    Pdr,
}

/// TrustWp operation requested by a native bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustWpVerificationMode {
    WeakestPrecondition,
    StrongestPostcondition,
    Abduction,
}

/// Source language that produced the native verification bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeSourceLanguage {
    #[default]
    Unknown,
    Rust,
    Swift,
    C,
    TrustIr,
    Other,
}

/// Stable identity for a producer, frontend, verifier, or solver binary.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeToolIdentity {
    pub name: String,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub version: Option<String>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub revision: Option<String>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub digest: Option<ProofDigest>,
}

impl NativeToolIdentity {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: None,
            revision: None,
            digest: None,
        }
    }

    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = Some(version.into());
        self
    }

    pub fn with_revision(mut self, revision: impl Into<String>) -> Self {
        self.revision = Some(revision.into());
        self
    }

    pub fn with_digest(mut self, digest: ProofDigest) -> Self {
        self.digest = Some(digest);
        self
    }

    /// Canonical, audit-stable spelling of the tool name.
    ///
    /// Native bundles preserve the producer-provided display name, but Trust
    /// boundary checks and stable digests use this normalized form so
    /// `TrustMc`, `trust_mc`, and `trust_mc.native` cannot split verifier identity.
    pub fn canonical_name(&self) -> String {
        canonical_tool_name(&self.name)
    }
}

impl Default for NativeToolIdentity {
    fn default() -> Self {
        Self::new("unknown")
    }
}

/// Structured verifier family for native request provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeVerifierSuite {
    #[default]
    Unknown,
    TrustVc,
    TrustMc,
    TrustWp,
    #[cfg_attr(feature = "serde", serde(rename = "ay"))]
    AY,
    // Wire branding for the Trust frontend is canonically `"Trust"` post-rename
    // (commit d44dabf renamed the serde producer variant tRust -> Trust); this
    // must match `NativeBundleProducer::TRust`'s `"Trust"` rename so a producer
    // and its verifier suite serialize the frontend identity with one spelling
    // across the cross-repo handoff. The stable digest is unaffected either way
    // — it encodes this variant via an integer tag and `code()` ("trust"), not
    // the serde string (see `digest::write_verifier_suite_stable`).
    #[cfg_attr(feature = "serde", serde(rename = "Trust"))]
    TRust,
    #[cfg_attr(feature = "serde", serde(rename = "TrustIr"))]
    TrustIr,
    Other,
}

impl core::fmt::Display for NativeVerifierSuite {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            NativeVerifierSuite::Unknown => "unknown",
            NativeVerifierSuite::TrustVc => "trust_vc",
            NativeVerifierSuite::TrustMc => "trust_mc",
            NativeVerifierSuite::TrustWp => "trust_wp",
            NativeVerifierSuite::AY => "ay",
            NativeVerifierSuite::TRust => "Trust",
            NativeVerifierSuite::TrustIr => "TrustIr",
            NativeVerifierSuite::Other => "other",
        })
    }
}

impl NativeVerifierSuite {
    pub const fn code(self) -> &'static str {
        match self {
            NativeVerifierSuite::Unknown => "unknown",
            NativeVerifierSuite::TrustVc => "trust_vc",
            NativeVerifierSuite::TrustMc => "trust_mc",
            NativeVerifierSuite::TrustWp => "trust_wp",
            NativeVerifierSuite::AY => "ay",
            NativeVerifierSuite::TRust => "trust",
            NativeVerifierSuite::TrustIr => "trust-ir",
            NativeVerifierSuite::Other => "other",
        }
    }

    pub fn canonical_family(self) -> Option<&'static str> {
        match self {
            NativeVerifierSuite::TrustVc
            | NativeVerifierSuite::TrustMc
            | NativeVerifierSuite::TrustWp
            | NativeVerifierSuite::AY
            | NativeVerifierSuite::TRust
            | NativeVerifierSuite::TrustIr => Some(self.code()),
            NativeVerifierSuite::Unknown | NativeVerifierSuite::Other => None,
        }
    }
}

/// Bundle-level provenance for replaying and auditing native handoffs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeBundleProvenance {
    pub producer_version: String,
    pub source_language: NativeSourceLanguage,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub source_artifact: Option<String>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub source_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub toolchain: Vec<NativeToolIdentity>,
}

impl Default for NativeBundleProvenance {
    fn default() -> Self {
        Self {
            producer_version: "unknown".to_string(),
            source_language: NativeSourceLanguage::Unknown,
            source_artifact: None,
            source_digest: None,
            toolchain: Vec::new(),
        }
    }
}

/// Stable serialization knobs expected by Trust handoff consumers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeUnknownFieldPolicy {
    Reject,
    Preserve,
    Ignore,
}

/// Serialization contract pinned beside the typed request payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeSerializationPolicy {
    pub schema_version: u32,
    pub canonical_order: bool,
    pub sort_unordered_sets: bool,
    pub messagepack_named_fields: bool,
    pub unknown_fields: NativeUnknownFieldPolicy,
}

impl Default for NativeSerializationPolicy {
    fn default() -> Self {
        Self {
            schema_version: NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION,
            canonical_order: true,
            sort_unordered_sets: true,
            messagepack_named_fields: true,
            unknown_fields: NativeUnknownFieldPolicy::Reject,
        }
    }
}

/// Diagnostic detail level requested from native verifier consumers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeDiagnosticLevel {
    Off,
    Error,
    Warn,
    #[default]
    Info,
    Trace,
}

/// Machine-readable diagnostic policy shared by TrustVc, TrustMc, and TrustWp.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeDiagnosticsPolicy {
    pub level: NativeDiagnosticLevel,
    pub include_source_spans: bool,
    pub include_lineage: bool,
    pub emit_counterexamples: bool,
    pub emit_unsat_cores: bool,
    pub emit_proof_traces: bool,
    pub max_counterexamples: u32,
}

impl Default for NativeDiagnosticsPolicy {
    fn default() -> Self {
        Self {
            level: NativeDiagnosticLevel::Info,
            include_source_spans: true,
            include_lineage: true,
            emit_counterexamples: true,
            emit_unsat_cores: true,
            emit_proof_traces: false,
            max_counterexamples: 1,
        }
    }
}

/// Optional per-request provenance for a specific verifier run.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeRequestProvenance {
    #[cfg_attr(feature = "serde", serde(default))]
    pub verifier_suite: NativeVerifierSuite,
    #[cfg_attr(feature = "serde", serde(default))]
    pub expected_verifier: NativeToolIdentity,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub solvers: Vec<NativeToolIdentity>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub replay: Option<ProofReplayIdentity>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "NativeReplayContext::is_empty")
    )]
    pub replay_context: NativeReplayContext,
}

impl NativeRequestProvenance {
    pub fn new(verifier_suite: NativeVerifierSuite, expected_verifier: NativeToolIdentity) -> Self {
        Self {
            verifier_suite,
            expected_verifier,
            solvers: Vec::new(),
            replay: None,
            replay_context: NativeReplayContext::default(),
        }
    }

    pub fn trust_vc(expected_verifier: NativeToolIdentity) -> Self {
        Self::new(NativeVerifierSuite::TrustVc, expected_verifier)
    }

    pub fn trust_mc(expected_verifier: NativeToolIdentity) -> Self {
        Self::new(NativeVerifierSuite::TrustMc, expected_verifier)
    }

    pub fn trust_wp(expected_verifier: NativeToolIdentity) -> Self {
        Self::new(NativeVerifierSuite::TrustWp, expected_verifier)
    }

    pub fn verifier_suite(&self) -> NativeVerifierSuite {
        self.verifier_suite
    }

    pub fn expected_verifier(&self) -> &NativeToolIdentity {
        &self.expected_verifier
    }

    pub fn solver_identities(&self) -> &[NativeToolIdentity] {
        &self.solvers
    }

    pub fn replay_identity(&self) -> Option<&ProofReplayIdentity> {
        self.replay.as_ref()
    }

    pub fn replay_context(&self) -> &NativeReplayContext {
        &self.replay_context
    }

    pub fn with_solver(mut self, solver: NativeToolIdentity) -> Self {
        self.solvers.push(solver);
        self
    }

    pub fn with_replay(mut self, replay: ProofReplayIdentity) -> Self {
        self.replay = Some(replay);
        self
    }

    pub fn with_replay_context(mut self, context: NativeReplayContext) -> Self {
        self.replay_context = context;
        self
    }
}

/// Stable id for a typed compiler fact in a native verification bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeCompilerFactId(pub u32);

impl NativeCompilerFactId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    pub const fn index(self) -> u32 {
        self.0
    }
}

impl core::fmt::Display for NativeCompilerFactId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Stable frontend assertion id for verifier diagnostics and replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeAssertionId(pub u32);

impl NativeAssertionId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    pub const fn index(self) -> u32 {
        self.0
    }
}

impl core::fmt::Display for NativeAssertionId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Stable id for one verifier replay atom.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeReplayAtomId(pub u32);

impl NativeReplayAtomId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    pub const fn index(self) -> u32 {
        self.0
    }
}

impl core::fmt::Display for NativeReplayAtomId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Verifier-side role for one replay atom.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeReplayAtomKind {
    Assumption,
    Assertion,
}

/// One typed formula atom used by verifier replay or VC generation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeReplayAtom {
    pub id: NativeReplayAtomId,
    pub kind: NativeReplayAtomKind,
    pub formula: ProofFormula,
    pub payload_digest: ProofDigest,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub obligation: Option<ProofId>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub assertion_id: Option<NativeAssertionId>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub span: Option<SourceSpan>,
}

impl NativeReplayAtom {
    pub fn new(id: NativeReplayAtomId, kind: NativeReplayAtomKind, formula: ProofFormula) -> Self {
        let mut atom = Self {
            id,
            kind,
            formula,
            payload_digest: ProofDigest::sha256([0; 32]),
            obligation: None,
            assertion_id: None,
            span: None,
        };
        atom.payload_digest = atom.expected_payload_digest();
        atom
    }

    pub fn assumption(id: NativeReplayAtomId, formula: ProofFormula) -> Self {
        Self::new(id, NativeReplayAtomKind::Assumption, formula)
    }

    pub fn assertion(id: NativeReplayAtomId, formula: ProofFormula) -> Self {
        Self::new(id, NativeReplayAtomKind::Assertion, formula)
    }

    pub fn with_obligation(mut self, obligation: ProofId) -> Self {
        self.obligation = Some(obligation);
        self
    }

    pub fn with_assertion_id(mut self, assertion_id: NativeAssertionId) -> Self {
        self.assertion_id = Some(assertion_id);
        self
    }

    pub fn with_span(mut self, span: SourceSpan) -> Self {
        self.span = Some(span);
        self
    }

    pub fn expected_payload_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_replay_atom_kind_stable(&mut bytes, self.kind);
        write_proof_formula_stable(&mut bytes, &self.formula);
        ProofDigest::sha256_domain("trust_ir.native.replay.atom.payload.v2", &bytes)
    }
}

/// Structured reason a native verifier mode cannot be admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeUnsupportedModeReason {
    UnsupportedVerifierMode,
    UnsupportedFormulaSchema,
    UnsupportedCompilerFact,
    MissingSourceSpan,
    MissingReplayTranscript,
    Other,
}

/// Fail-closed unsupported-mode metadata for downstream adapters.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeUnsupportedMode {
    pub reason: NativeUnsupportedModeReason,
    pub detail: String,
}

impl NativeUnsupportedMode {
    pub fn new(reason: NativeUnsupportedModeReason, detail: impl Into<String>) -> Self {
        Self {
            reason,
            detail: detail.into(),
        }
    }
}

/// Typed replay context shared by TrustVc, TrustMc, and TrustWp request adapters.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeReplayContext {
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub atoms: Vec<NativeReplayAtom>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub unsupported_modes: Vec<NativeUnsupportedMode>,
}

impl NativeReplayContext {
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty() && self.unsupported_modes.is_empty()
    }

    pub fn with_atom(mut self, atom: NativeReplayAtom) -> Self {
        self.atoms.push(atom);
        self
    }

    pub fn with_unsupported_mode(mut self, unsupported: NativeUnsupportedMode) -> Self {
        self.unsupported_modes.push(unsupported);
        self
    }
}

/// Domain relation represented by a native function when a semantic bridge is
/// admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeSemanticRelationKind {
    /// Generic native successor relation for state-space exploration.
    NativeSuccessor,
    /// TY Petri net plan-cache successor enumeration.
    PetriSuccessor,
}

impl NativeSemanticRelationKind {
    pub const fn code(self) -> &'static str {
        match self {
            NativeSemanticRelationKind::NativeSuccessor => "native_successor",
            NativeSemanticRelationKind::PetriSuccessor => "petri_successor",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeSemanticRelationKind::NativeSuccessor => "native successor",
            NativeSemanticRelationKind::PetriSuccessor => "Petri successor",
        }
    }
}

impl core::fmt::Display for NativeSemanticRelationKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Stable query describing the semantic relation a native entry function must
/// represent before downstream native execution can be selected.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeSemanticBridge {
    pub schema_version: u32,
    pub relation: NativeSemanticRelationKind,
    pub function: FuncId,
    pub formula_schema: String,
}

impl NativeSemanticBridge {
    pub const SCHEMA: &'static str = NATIVE_SEMANTIC_BRIDGE_SCHEMA;
    pub const SCHEMA_VERSION: u32 = NATIVE_SEMANTIC_BRIDGE_SCHEMA_VERSION;

    pub fn new(
        relation: NativeSemanticRelationKind,
        function: FuncId,
        formula_schema: impl Into<String>,
    ) -> Self {
        Self {
            schema_version: Self::SCHEMA_VERSION,
            relation,
            function,
            formula_schema: formula_schema.into(),
        }
    }

    pub fn petri_successor_plan_cache_equivalence(function: FuncId) -> Self {
        Self::new(
            NativeSemanticRelationKind::PetriSuccessor,
            function,
            PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA,
        )
    }

    pub const fn schema(&self) -> &'static str {
        Self::SCHEMA
    }

    pub fn is_petri_successor_plan_cache_equivalence(&self) -> bool {
        self.relation == NativeSemanticRelationKind::PetriSuccessor
            && self.formula_schema == PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_u32_stable(&mut bytes, self.schema_version);
        write_semantic_relation_kind_stable(&mut bytes, self.relation);
        write_u32_stable(&mut bytes, self.function.index());
        write_str_stable(&mut bytes, &self.formula_schema);
        ProofDigest::sha256_domain(NATIVE_SEMANTIC_BRIDGE_SCHEMA, &bytes)
    }
}

/// Whether verifier evidence for the selected semantic proof obligation is
/// present in the native bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeSemanticBridgeEvidenceStatus {
    Missing,
    Present,
}

impl NativeSemanticBridgeEvidenceStatus {
    pub const fn code(self) -> &'static str {
        match self {
            NativeSemanticBridgeEvidenceStatus::Missing => "missing",
            NativeSemanticBridgeEvidenceStatus::Present => "present",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeSemanticBridgeEvidenceStatus::Missing => "missing evidence",
            NativeSemanticBridgeEvidenceStatus::Present => "evidence present",
        }
    }
}

impl core::fmt::Display for NativeSemanticBridgeEvidenceStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Admission status for a native semantic bridge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeSemanticBridgeStatus {
    Represented,
    Blocked,
}

impl NativeSemanticBridgeStatus {
    pub const fn code(self) -> &'static str {
        match self {
            NativeSemanticBridgeStatus::Represented => "represented",
            NativeSemanticBridgeStatus::Blocked => "blocked",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeSemanticBridgeStatus::Represented => "semantic relation represented",
            NativeSemanticBridgeStatus::Blocked => "semantic relation blocked",
        }
    }
}

impl core::fmt::Display for NativeSemanticBridgeStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Stable fail-closed reason for a native semantic bridge report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeSemanticBridgeReason {
    Represented,
    BundleInvalid,
    MissingFunction,
    MissingProofObligation,
    MissingObligationSource,
    FunctionMismatch,
    UnsupportedObligationKind,
    ProofPending,
    ProofFailed,
    TrustedProofNotAdmitted,
    MissingEvidence,
}

impl NativeSemanticBridgeReason {
    pub const fn code(self) -> &'static str {
        match self {
            NativeSemanticBridgeReason::Represented => "represented",
            NativeSemanticBridgeReason::BundleInvalid => "bundle_invalid",
            NativeSemanticBridgeReason::MissingFunction => "missing_function",
            NativeSemanticBridgeReason::MissingProofObligation => "missing_proof_obligation",
            NativeSemanticBridgeReason::MissingObligationSource => "missing_obligation_source",
            NativeSemanticBridgeReason::FunctionMismatch => "function_mismatch",
            NativeSemanticBridgeReason::UnsupportedObligationKind => "unsupported_obligation_kind",
            NativeSemanticBridgeReason::ProofPending => "proof_pending",
            NativeSemanticBridgeReason::ProofFailed => "proof_failed",
            NativeSemanticBridgeReason::TrustedProofNotAdmitted => "trusted_proof_not_admitted",
            NativeSemanticBridgeReason::MissingEvidence => "missing_evidence",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeSemanticBridgeReason::Represented => "represented",
            NativeSemanticBridgeReason::BundleInvalid => "bundle invalid",
            NativeSemanticBridgeReason::MissingFunction => "missing function",
            NativeSemanticBridgeReason::MissingProofObligation => "missing proof obligation",
            NativeSemanticBridgeReason::MissingObligationSource => "missing obligation source",
            NativeSemanticBridgeReason::FunctionMismatch => "function mismatch",
            NativeSemanticBridgeReason::UnsupportedObligationKind => "unsupported obligation kind",
            NativeSemanticBridgeReason::ProofPending => "proof pending",
            NativeSemanticBridgeReason::ProofFailed => "proof failed",
            NativeSemanticBridgeReason::TrustedProofNotAdmitted => "trusted proof not admitted",
            NativeSemanticBridgeReason::MissingEvidence => "missing evidence",
        }
    }
}

impl core::fmt::Display for NativeSemanticBridgeReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Fail-closed semantic bridge report derived from a validated native bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeSemanticBridgeReport {
    pub schema: String,
    pub schema_version: u32,
    pub bridge: NativeSemanticBridge,
    pub bridge_digest: ProofDigest,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub proof_obligation: Option<ProofId>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub proof_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub proof_status: Option<ProofStatus>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub evidence_digest: Option<ProofDigest>,
    pub evidence_status: NativeSemanticBridgeEvidenceStatus,
    pub status: NativeSemanticBridgeStatus,
    pub reason: NativeSemanticBridgeReason,
}

impl NativeSemanticBridgeReport {
    pub fn is_represented(&self) -> bool {
        self.status == NativeSemanticBridgeStatus::Represented
            && self.reason == NativeSemanticBridgeReason::Represented
    }

    pub fn fail_closed(&self) -> bool {
        !self.is_represented()
    }

    pub fn status_code(&self) -> &'static str {
        self.status.code()
    }

    pub fn reason_code(&self) -> &'static str {
        self.reason.code()
    }

    pub fn evidence_status_code(&self) -> &'static str {
        self.evidence_status.code()
    }

    pub const fn proof_identity_schema(&self) -> &'static str {
        NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA
    }

    pub const fn proof_identity_schema_version(&self) -> u32 {
        NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION
    }

    /// Stable TrustIr-owned identity for this bridge/proof/evidence decision.
    ///
    /// Downstream native/JIT admission gates can bind their own rows to this
    /// digest instead of reconstructing a weaker identity from string fields.
    pub fn proof_identity_digest(&self) -> ProofDigest {
        native_semantic_bridge_proof_identity_digest(self)
    }

    /// Emit stable semantic-bridge proof/evidence identity rows.
    pub fn proof_identity_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        let proof_identity_digest = self.proof_identity_digest();

        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.schema",
            self.proof_identity_schema(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.schema_version",
            self.proof_identity_schema_version().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.digest.context",
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.digest.algorithm",
            proof_digest_algorithm_code(proof_identity_digest.algorithm),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.digest",
            proof_identity_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.bridge.schema",
            self.bridge.schema(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.bridge.schema_version",
            self.bridge.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.bridge.digest",
            self.bridge_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.bridge.relation",
            self.bridge.relation.code(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.bridge.function",
            self.bridge.function.index().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.bridge.formula_schema",
            self.bridge.formula_schema.as_str(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.report.schema",
            self.schema.as_str(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.report.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.report.status",
            self.status_code(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.report.reason",
            self.reason_code(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.report.fail_closed",
            bool_code(self.fail_closed()),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.report.evidence_status",
            self.evidence_status_code(),
        );
        push_optional_u32_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.proof.obligation",
            self.proof_obligation.map(ProofId::index),
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.proof.digest",
            self.proof_digest,
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.proof.status",
            self.proof_status.map(proof_status_code).unwrap_or("none"),
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity.evidence.digest",
            self.evidence_digest,
        );

        rows
    }

    /// Emit escaped `key=value` semantic-bridge proof identity rows.
    pub fn proof_identity_key_value_lines(&self) -> Vec<String> {
        self.proof_identity_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit stable line-oriented semantic-bridge proof identity text.
    pub fn proof_identity_key_value_text(&self) -> String {
        format!("{}\n", self.proof_identity_key_value_lines().join("\n"))
    }

    /// Validate persisted semantic-bridge proof identity rows against this report.
    pub fn proof_identity_replay_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> NativeSemanticBridgeProofIdentityReplayReport {
        self.proof_identity_replay_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate persisted semantic-bridge proof identity `key=value` lines.
    pub fn proof_identity_replay_report_for_key_value_lines(
        &self,
        lines: &[String],
    ) -> NativeSemanticBridgeProofIdentityReplayReport {
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.proof_identity_replay_report_with_invalid_lines(&rows, invalid_lines)
    }

    /// Validate persisted semantic-bridge proof identity line-oriented text.
    pub fn proof_identity_replay_report_for_key_value_text(
        &self,
        text: &str,
    ) -> NativeSemanticBridgeProofIdentityReplayReport {
        let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
        self.proof_identity_replay_report_for_key_value_lines(&lines)
    }

    fn proof_identity_replay_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> NativeSemanticBridgeProofIdentityReplayReport {
        let expected_rows = self.proof_identity_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_bool_keys = Vec::new();
        let mut invalid_usize_keys = Vec::new();
        let reconstructed_schema =
            observed_single_value(&observed_by_key, "semantic_bridge_proof_identity.schema")
                .map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "semantic_bridge_proof_identity.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_identity_digest =
            observed_single_value(&observed_by_key, "semantic_bridge_proof_identity.digest")
                .map(str::to_string);
        let reconstructed_bridge_digest = observed_single_value(
            &observed_by_key,
            "semantic_bridge_proof_identity.bridge.digest",
        )
        .map(str::to_string);
        let reconstructed_bridge_function = observed_usize_value(
            &observed_by_key,
            "semantic_bridge_proof_identity.bridge.function",
            &mut invalid_usize_keys,
        );
        let reconstructed_status = observed_single_value(
            &observed_by_key,
            "semantic_bridge_proof_identity.report.status",
        )
        .map(str::to_string);
        let reconstructed_reason = observed_single_value(
            &observed_by_key,
            "semantic_bridge_proof_identity.report.reason",
        )
        .map(str::to_string);
        let reconstructed_fail_closed = observed_bool_value(
            &observed_by_key,
            "semantic_bridge_proof_identity.report.fail_closed",
            &mut invalid_bool_keys,
        );
        let reconstructed_evidence_status = observed_single_value(
            &observed_by_key,
            "semantic_bridge_proof_identity.report.evidence_status",
        )
        .map(str::to_string);

        for key in [
            "semantic_bridge_proof_identity.bridge.schema_version",
            "semantic_bridge_proof_identity.report.schema_version",
            "semantic_bridge_proof_identity.proof.obligation",
        ] {
            let _ = observed_usize_value(&observed_by_key, key, &mut invalid_usize_keys);
        }

        let expected_identity_digest = self.proof_identity_digest().to_string();
        let expected_bridge_digest = self.bridge_digest.to_string();
        let schema_matches = reconstructed_schema.as_deref() == Some(self.proof_identity_schema())
            && reconstructed_schema_version == Some(self.proof_identity_schema_version() as usize);
        let identity_digest_matches =
            reconstructed_identity_digest.as_deref() == Some(expected_identity_digest.as_str());
        let bridge_digest_matches =
            reconstructed_bridge_digest.as_deref() == Some(expected_bridge_digest.as_str());
        let bridge_function_matches =
            reconstructed_bridge_function == Some(self.bridge.function.index() as usize);
        let status_matches = reconstructed_status.as_deref() == Some(self.status_code());
        let reason_matches = reconstructed_reason.as_deref() == Some(self.reason_code());
        let fail_closed_matches = reconstructed_fail_closed == Some(self.fail_closed());
        let evidence_status_matches =
            reconstructed_evidence_status.as_deref() == Some(self.evidence_status_code());

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
            && invalid_usize_keys.is_empty()
            && invalid_lines.is_empty()
            && schema_matches
            && identity_digest_matches
            && bridge_digest_matches
            && bridge_function_matches
            && status_matches
            && reason_matches
            && fail_closed_matches
            && evidence_status_matches
        {
            NativeSemanticBridgeProofIdentityReplayStatus::Replayable
        } else {
            NativeSemanticBridgeProofIdentityReplayStatus::Invalid
        };

        NativeSemanticBridgeProofIdentityReplayReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                NativeSemanticBridgeProofIdentityReplayStatus::Replayable
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            invalid_usize_keys,
            invalid_lines,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_identity_digest,
            reconstructed_bridge_digest,
            reconstructed_bridge_function,
            reconstructed_status,
            reconstructed_reason,
            reconstructed_fail_closed,
            reconstructed_evidence_status,
            schema_matches,
            identity_digest_matches,
            bridge_digest_matches,
            bridge_function_matches,
            status_matches,
            reason_matches,
            fail_closed_matches,
            evidence_status_matches,
        }
    }

    pub fn represents_petri_successor_plan_cache_equivalence(&self) -> bool {
        self.is_represented() && self.bridge.is_petri_successor_plan_cache_equivalence()
    }
}

/// Replay-validation status for persisted semantic-bridge proof identity rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeSemanticBridgeProofIdentityReplayStatus {
    Replayable,
    Invalid,
}

impl NativeSemanticBridgeProofIdentityReplayStatus {
    pub const fn code(self) -> &'static str {
        match self {
            NativeSemanticBridgeProofIdentityReplayStatus::Replayable => "replayable",
            NativeSemanticBridgeProofIdentityReplayStatus::Invalid => "invalid",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeSemanticBridgeProofIdentityReplayStatus::Replayable => {
                "semantic bridge proof identity rows replayable"
            }
            NativeSemanticBridgeProofIdentityReplayStatus::Invalid => {
                "semantic bridge proof identity rows invalid"
            }
        }
    }
}

impl core::fmt::Display for NativeSemanticBridgeProofIdentityReplayStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Round-trip status for persisted semantic-bridge replay health summaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus {
    Valid,
    Invalid,
}

impl NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus {
    pub const fn code(self) -> &'static str {
        match self {
            NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Valid => "valid",
            NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Invalid => {
                "invalid"
            }
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Valid => {
                "semantic bridge proof identity replay health summary valid"
            }
            NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Invalid => {
                "semantic bridge proof identity replay health summary invalid"
            }
        }
    }
}

impl core::fmt::Display for NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Validation report for persisted semantic-bridge replay health summaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport {
    pub status: NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_status: Option<String>,
    pub reconstructed_fail_closed: Option<bool>,
    pub reconstructed_diagnostic_count: Option<usize>,
    pub schema_matches: bool,
    pub status_matches: bool,
    pub fail_closed_matches: bool,
    pub diagnostic_count_matches: bool,
}

impl NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport {
    pub fn is_valid(&self) -> bool {
        matches!(
            self.status,
            NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Valid
        ) && !self.fail_closed
    }

    pub fn diagnostic_count(&self) -> usize {
        self.duplicate_keys.len()
            + self.missing_keys.len()
            + self.unexpected_keys.len()
            + self.mismatched_value_keys.len()
            + self.invalid_bool_keys.len()
            + self.invalid_usize_keys.len()
            + self.invalid_lines.len()
    }
}

/// Validation report for persisted semantic-bridge proof identity rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeSemanticBridgeProofIdentityReplayReport {
    pub status: NativeSemanticBridgeProofIdentityReplayStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_identity_digest: Option<String>,
    pub reconstructed_bridge_digest: Option<String>,
    pub reconstructed_bridge_function: Option<usize>,
    pub reconstructed_status: Option<String>,
    pub reconstructed_reason: Option<String>,
    pub reconstructed_fail_closed: Option<bool>,
    pub reconstructed_evidence_status: Option<String>,
    pub schema_matches: bool,
    pub identity_digest_matches: bool,
    pub bridge_digest_matches: bool,
    pub bridge_function_matches: bool,
    pub status_matches: bool,
    pub reason_matches: bool,
    pub fail_closed_matches: bool,
    pub evidence_status_matches: bool,
}

impl NativeSemanticBridgeProofIdentityReplayReport {
    pub fn is_replayable(&self) -> bool {
        matches!(
            self.status,
            NativeSemanticBridgeProofIdentityReplayStatus::Replayable
        ) && !self.fail_closed
    }

    pub fn diagnostic_count(&self) -> usize {
        self.duplicate_keys.len()
            + self.missing_keys.len()
            + self.unexpected_keys.len()
            + self.mismatched_value_keys.len()
            + self.invalid_bool_keys.len()
            + self.invalid_usize_keys.len()
            + self.invalid_lines.len()
    }

    /// Emit component-addressed replay health rows for compact readiness sidecars.
    pub fn component_health_summary_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        let prefix = "semantic_bridge_proof_identity_replay_component_summary";

        push_manifest_row(
            &mut rows,
            format!("{prefix}.schema"),
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            format!("{prefix}.schema_version"),
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION.to_string(),
        );
        push_manifest_row(&mut rows, format!("{prefix}.status"), self.status_code);
        push_manifest_row(
            &mut rows,
            format!("{prefix}.fail_closed"),
            bool_code(self.fail_closed),
        );
        push_manifest_row(
            &mut rows,
            format!("{prefix}.diagnostic_count"),
            self.diagnostic_count().to_string(),
        );
        push_manifest_row(&mut rows, format!("{prefix}.component.count"), "8");
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "schema",
            self.reconstructed_schema.as_deref().unwrap_or("none"),
            self.schema_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "identity_digest",
            self.reconstructed_identity_digest
                .as_deref()
                .unwrap_or("none"),
            self.identity_digest_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "bridge_digest",
            self.reconstructed_bridge_digest
                .as_deref()
                .unwrap_or("none"),
            self.bridge_digest_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "bridge_function",
            self.reconstructed_bridge_function
                .map(|function| function.to_string())
                .unwrap_or_else(|| "none".to_string()),
            self.bridge_function_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "status",
            self.reconstructed_status.as_deref().unwrap_or("none"),
            self.status_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "reason",
            self.reconstructed_reason.as_deref().unwrap_or("none"),
            self.reason_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "fail_closed",
            self.reconstructed_fail_closed
                .map(bool_code)
                .unwrap_or("none"),
            self.fail_closed_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "evidence_status",
            self.reconstructed_evidence_status
                .as_deref()
                .unwrap_or("none"),
            self.evidence_status_matches,
        );

        rows
    }

    /// Emit escaped `key=value` component health rows.
    pub fn component_health_summary_key_value_lines(&self) -> Vec<String> {
        self.component_health_summary_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit line-oriented component health text for readiness sidecars.
    pub fn component_health_summary_key_value_text(&self) -> String {
        format!(
            "{}\n",
            self.component_health_summary_key_value_lines().join("\n")
        )
    }

    /// Emit deterministic health rows for semantic-bridge sidecar persistence.
    pub fn compact_health_summary_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.schema",
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.schema_version",
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.status",
            self.status_code,
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.fail_closed",
            bool_code(self.fail_closed),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.count.expected_rows",
            self.expected_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.count.observed_rows",
            self.observed_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.count.unique_keys",
            self.unique_key_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.count.diagnostics",
            self.diagnostic_count().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.schema",
            self.reconstructed_schema.as_deref().unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.schema_version",
            self.reconstructed_schema_version
                .map(|version| version.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.identity_digest",
            self.reconstructed_identity_digest
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.bridge_digest",
            self.reconstructed_bridge_digest
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.bridge_function",
            self.reconstructed_bridge_function
                .map(|function| function.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.status",
            self.reconstructed_status.as_deref().unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.reason",
            self.reconstructed_reason.as_deref().unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.fail_closed",
            self.reconstructed_fail_closed
                .map(bool_code)
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.reconstructed.evidence_status",
            self.reconstructed_evidence_status
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.schema",
            bool_code(self.schema_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.identity_digest",
            bool_code(self.identity_digest_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.bridge_digest",
            bool_code(self.bridge_digest_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.bridge_function",
            bool_code(self.bridge_function_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.status",
            bool_code(self.status_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.reason",
            bool_code(self.reason_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.fail_closed",
            bool_code(self.fail_closed_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.agreement.evidence_status",
            bool_code(self.evidence_status_matches),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.diagnostic.duplicate_keys",
            self.duplicate_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.diagnostic.missing_keys",
            self.missing_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.diagnostic.unexpected_keys",
            self.unexpected_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.diagnostic.mismatched_value_keys",
            self.mismatched_value_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.diagnostic.invalid_bool_keys",
            self.invalid_bool_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.diagnostic.invalid_usize_keys",
            self.invalid_usize_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge_proof_identity_replay_report.diagnostic.invalid_lines",
            self.invalid_lines.len().to_string(),
        );

        rows
    }

    /// Emit escaped `key=value` rows for semantic-bridge health persistence.
    pub fn compact_health_summary_key_value_lines(&self) -> Vec<String> {
        self.compact_health_summary_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit stable line-oriented semantic-bridge replay health text.
    pub fn compact_health_summary_key_value_text(&self) -> String {
        format!(
            "{}\n",
            self.compact_health_summary_key_value_lines().join("\n")
        )
    }

    /// Emit compact JSON for non-Rust sidecar validation.
    pub fn compact_health_summary_json_text(&self) -> String {
        let optional_string = |value: Option<&str>| {
            value
                .map(json_string_literal)
                .unwrap_or_else(|| "null".to_string())
        };
        let optional_usize = |value: Option<usize>| {
            value
                .map(|value| value.to_string())
                .unwrap_or_else(|| "null".to_string())
        };
        let optional_bool = |value: Option<bool>| value.map(bool_code).unwrap_or("null");

        format!(
            "{{\"schema\":{},\"schema_version\":{},\"status\":{},\"fail_closed\":{},\"expected_row_count\":{},\"observed_row_count\":{},\"unique_key_count\":{},\"diagnostic_count\":{},\"reconstructed_schema\":{},\"reconstructed_schema_version\":{},\"reconstructed_identity_digest\":{},\"reconstructed_bridge_digest\":{},\"reconstructed_bridge_function\":{},\"reconstructed_status\":{},\"reconstructed_reason\":{},\"reconstructed_fail_closed\":{},\"reconstructed_evidence_status\":{},\"schema_matches\":{},\"identity_digest_matches\":{},\"bridge_digest_matches\":{},\"bridge_function_matches\":{},\"status_matches\":{},\"reason_matches\":{},\"fail_closed_matches\":{},\"evidence_status_matches\":{},\"duplicate_key_count\":{},\"missing_key_count\":{},\"unexpected_key_count\":{},\"mismatched_value_key_count\":{},\"invalid_bool_key_count\":{},\"invalid_usize_key_count\":{},\"invalid_line_count\":{}}}\n",
            json_string_literal(NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA),
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION,
            json_string_literal(self.status_code),
            bool_code(self.fail_closed),
            self.expected_row_count,
            self.observed_row_count,
            self.unique_key_count,
            self.diagnostic_count(),
            optional_string(self.reconstructed_schema.as_deref()),
            optional_usize(self.reconstructed_schema_version),
            optional_string(self.reconstructed_identity_digest.as_deref()),
            optional_string(self.reconstructed_bridge_digest.as_deref()),
            optional_usize(self.reconstructed_bridge_function),
            optional_string(self.reconstructed_status.as_deref()),
            optional_string(self.reconstructed_reason.as_deref()),
            optional_bool(self.reconstructed_fail_closed),
            optional_string(self.reconstructed_evidence_status.as_deref()),
            bool_code(self.schema_matches),
            bool_code(self.identity_digest_matches),
            bool_code(self.bridge_digest_matches),
            bool_code(self.bridge_function_matches),
            bool_code(self.status_matches),
            bool_code(self.reason_matches),
            bool_code(self.fail_closed_matches),
            bool_code(self.evidence_status_matches),
            self.duplicate_keys.len(),
            self.missing_keys.len(),
            self.unexpected_keys.len(),
            self.mismatched_value_keys.len(),
            self.invalid_bool_keys.len(),
            self.invalid_usize_keys.len(),
            self.invalid_lines.len()
        )
    }

    /// Validate persisted semantic-bridge health rows against this replay report.
    pub fn compact_health_summary_round_trip_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport {
        self.compact_health_summary_round_trip_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate persisted semantic-bridge health `key=value` lines.
    pub fn compact_health_summary_round_trip_report_for_key_value_lines(
        &self,
        lines: &[String],
    ) -> NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport {
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.compact_health_summary_round_trip_report_with_invalid_lines(&rows, invalid_lines)
    }

    /// Validate persisted semantic-bridge health line-oriented text.
    pub fn compact_health_summary_round_trip_report_for_key_value_text(
        &self,
        text: &str,
    ) -> NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport {
        let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
        self.compact_health_summary_round_trip_report_for_key_value_lines(&lines)
    }

    fn compact_health_summary_round_trip_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport {
        let expected_rows = self.compact_health_summary_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_bool_keys = Vec::new();
        let mut invalid_usize_keys = Vec::new();
        let reconstructed_schema = observed_single_value(
            &observed_by_key,
            "semantic_bridge_proof_identity_replay_report.schema",
        )
        .map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "semantic_bridge_proof_identity_replay_report.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_status = observed_single_value(
            &observed_by_key,
            "semantic_bridge_proof_identity_replay_report.status",
        )
        .map(str::to_string);
        let reconstructed_fail_closed = observed_bool_value(
            &observed_by_key,
            "semantic_bridge_proof_identity_replay_report.fail_closed",
            &mut invalid_bool_keys,
        );
        let reconstructed_diagnostic_count = observed_usize_value(
            &observed_by_key,
            "semantic_bridge_proof_identity_replay_report.count.diagnostics",
            &mut invalid_usize_keys,
        );

        for key in [
            "semantic_bridge_proof_identity_replay_report.count.expected_rows",
            "semantic_bridge_proof_identity_replay_report.count.observed_rows",
            "semantic_bridge_proof_identity_replay_report.count.unique_keys",
            "semantic_bridge_proof_identity_replay_report.reconstructed.schema_version",
            "semantic_bridge_proof_identity_replay_report.reconstructed.bridge_function",
            "semantic_bridge_proof_identity_replay_report.diagnostic.duplicate_keys",
            "semantic_bridge_proof_identity_replay_report.diagnostic.missing_keys",
            "semantic_bridge_proof_identity_replay_report.diagnostic.unexpected_keys",
            "semantic_bridge_proof_identity_replay_report.diagnostic.mismatched_value_keys",
            "semantic_bridge_proof_identity_replay_report.diagnostic.invalid_bool_keys",
            "semantic_bridge_proof_identity_replay_report.diagnostic.invalid_usize_keys",
            "semantic_bridge_proof_identity_replay_report.diagnostic.invalid_lines",
        ] {
            let _ = observed_usize_value(&observed_by_key, key, &mut invalid_usize_keys);
        }

        for key in [
            "semantic_bridge_proof_identity_replay_report.reconstructed.fail_closed",
            "semantic_bridge_proof_identity_replay_report.agreement.schema",
            "semantic_bridge_proof_identity_replay_report.agreement.identity_digest",
            "semantic_bridge_proof_identity_replay_report.agreement.bridge_digest",
            "semantic_bridge_proof_identity_replay_report.agreement.bridge_function",
            "semantic_bridge_proof_identity_replay_report.agreement.status",
            "semantic_bridge_proof_identity_replay_report.agreement.reason",
            "semantic_bridge_proof_identity_replay_report.agreement.fail_closed",
            "semantic_bridge_proof_identity_replay_report.agreement.evidence_status",
        ] {
            let _ = observed_bool_value(&observed_by_key, key, &mut invalid_bool_keys);
        }

        let schema_matches = reconstructed_schema.as_deref()
            == Some(NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA)
            && reconstructed_schema_version
                == Some(NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION as usize);
        let status_matches = reconstructed_status.as_deref() == Some(self.status_code);
        let fail_closed_matches = reconstructed_fail_closed == Some(self.fail_closed);
        let diagnostic_count_matches =
            reconstructed_diagnostic_count == Some(self.diagnostic_count());

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
            && invalid_usize_keys.is_empty()
            && invalid_lines.is_empty()
            && schema_matches
            && status_matches
            && fail_closed_matches
            && diagnostic_count_matches
        {
            NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Valid
        } else {
            NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Invalid
        };

        NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Valid
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            invalid_usize_keys,
            invalid_lines,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_status,
            reconstructed_fail_closed,
            reconstructed_diagnostic_count,
            schema_matches,
            status_matches,
            fail_closed_matches,
            diagnostic_count_matches,
        }
    }
}

/// Binding status for Petri successor TrustMc CHC request/evidence handoff.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcBindingStatus {
    Bound,
    Blocked,
}

impl PetriSuccessorTrustMcChcBindingStatus {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcBindingStatus::Bound => "bound",
            PetriSuccessorTrustMcChcBindingStatus::Blocked => "blocked",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcBindingStatus::Bound => "Petri TrustMc CHC binding present",
            PetriSuccessorTrustMcChcBindingStatus::Blocked => "Petri TrustMc CHC binding blocked",
        }
    }
}

impl core::fmt::Display for PetriSuccessorTrustMcChcBindingStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Fail-closed reason for Petri successor TrustMc CHC request/evidence binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcBindingReason {
    Bound,
    BundleInvalid,
    SemanticBridgeBlocked,
    MissingBridgeProofObligation,
    MissingTrustMcChcRequest,
    MissingTrustMcChcEvidence,
    EvidenceBindingMismatch,
    MissingHornClauseArtifact,
}

impl PetriSuccessorTrustMcChcBindingReason {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcBindingReason::Bound => "bound",
            PetriSuccessorTrustMcChcBindingReason::BundleInvalid => "bundle_invalid",
            PetriSuccessorTrustMcChcBindingReason::SemanticBridgeBlocked => {
                "semantic_bridge_blocked"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingBridgeProofObligation => {
                "missing_bridge_proof_obligation"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcRequest => {
                "missing_trust_mc_chc_request"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcEvidence => {
                "missing_trust_mc_chc_evidence"
            }
            PetriSuccessorTrustMcChcBindingReason::EvidenceBindingMismatch => {
                "evidence_binding_mismatch"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingHornClauseArtifact => {
                "missing_horn_clause_artifact"
            }
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcBindingReason::Bound => "bound",
            PetriSuccessorTrustMcChcBindingReason::BundleInvalid => "bundle invalid",
            PetriSuccessorTrustMcChcBindingReason::SemanticBridgeBlocked => {
                "semantic bridge blocked"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingBridgeProofObligation => {
                "missing bridge proof obligation"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcRequest => {
                "missing TrustMc CHC request"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcEvidence => {
                "missing TrustMc CHC evidence"
            }
            PetriSuccessorTrustMcChcBindingReason::EvidenceBindingMismatch => {
                "evidence binding mismatch"
            }
            PetriSuccessorTrustMcChcBindingReason::MissingHornClauseArtifact => {
                "missing Horn-clause artifact"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorTrustMcChcBindingReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Typed Petri successor TrustMc CHC request/evidence/artifact binding report.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PetriSuccessorTrustMcChcBindingReport {
    pub schema: String,
    pub schema_version: u32,
    pub function: FuncId,
    pub semantic_bridge_report: NativeSemanticBridgeReport,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub request: Option<NativeRequestId>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub request_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub evidence_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub expected_evidence_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub horn_clause_artifact: Option<NativeEvidenceArtifact>,
    pub status: PetriSuccessorTrustMcChcBindingStatus,
    pub reason: PetriSuccessorTrustMcChcBindingReason,
}

impl PetriSuccessorTrustMcChcBindingReport {
    pub fn is_bound(&self) -> bool {
        self.status == PetriSuccessorTrustMcChcBindingStatus::Bound
            && self.reason == PetriSuccessorTrustMcChcBindingReason::Bound
    }

    pub fn fail_closed(&self) -> bool {
        !self.is_bound()
    }

    pub fn status_code(&self) -> &'static str {
        self.status.code()
    }

    pub fn reason_code(&self) -> &'static str {
        self.reason.code()
    }
}

/// Proof-handoff readiness for Petri successor TrustMc CHC evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcProofHandoffStatus {
    Ready,
    Blocked,
}

impl PetriSuccessorTrustMcChcProofHandoffStatus {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofHandoffStatus::Ready => "ready",
            PetriSuccessorTrustMcChcProofHandoffStatus::Blocked => "blocked",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofHandoffStatus::Ready => {
                "Petri TrustMc CHC proof handoff ready"
            }
            PetriSuccessorTrustMcChcProofHandoffStatus::Blocked => {
                "Petri TrustMc CHC proof handoff blocked"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorTrustMcChcProofHandoffStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Fail-closed reason for Petri successor TrustMc CHC proof handoff readiness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcProofHandoffReason {
    Ready,
    BindingBlocked,
    MissingTrustMcChcEvidence,
    MissingReplayTranscriptDigest,
    MissingReplayTranscriptArtifact,
    ReplayTranscriptDigestMismatch,
}

impl PetriSuccessorTrustMcChcProofHandoffReason {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofHandoffReason::Ready => "ready",
            PetriSuccessorTrustMcChcProofHandoffReason::BindingBlocked => "binding_blocked",
            PetriSuccessorTrustMcChcProofHandoffReason::MissingTrustMcChcEvidence => {
                "missing_trust_mc_chc_evidence"
            }
            PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptDigest => {
                "missing_replay_transcript_digest"
            }
            PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptArtifact => {
                "missing_replay_transcript_artifact"
            }
            PetriSuccessorTrustMcChcProofHandoffReason::ReplayTranscriptDigestMismatch => {
                "replay_transcript_digest_mismatch"
            }
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofHandoffReason::Ready => "ready",
            PetriSuccessorTrustMcChcProofHandoffReason::BindingBlocked => "binding blocked",
            PetriSuccessorTrustMcChcProofHandoffReason::MissingTrustMcChcEvidence => {
                "missing TrustMc CHC evidence"
            }
            PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptDigest => {
                "missing replay transcript digest"
            }
            PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptArtifact => {
                "missing replay transcript artifact"
            }
            PetriSuccessorTrustMcChcProofHandoffReason::ReplayTranscriptDigestMismatch => {
                "replay transcript digest mismatch"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorTrustMcChcProofHandoffReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Typed proof-handoff readiness report for Petri successor TrustMc CHC evidence.
///
/// The report does not validate solver output itself. It only exposes the
/// TrustIr-owned CHC lowering/proof replay identity needed by TrustMc, TrustIr, and
/// TY to decide whether they can hand off to solver proof/model validation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PetriSuccessorTrustMcChcProofHandoffReport {
    pub schema: String,
    pub schema_version: u32,
    pub function: FuncId,
    pub binding_report: PetriSuccessorTrustMcChcBindingReport,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub proof_identity_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub replay: Option<ProofReplayIdentity>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub replay_transcript_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub replay_transcript_artifact: Option<NativeEvidenceArtifact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub model_artifact: Option<NativeEvidenceArtifact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub solver_identities: Vec<NativeToolIdentity>,
    pub status: PetriSuccessorTrustMcChcProofHandoffStatus,
    pub reason: PetriSuccessorTrustMcChcProofHandoffReason,
}

impl PetriSuccessorTrustMcChcProofHandoffReport {
    pub fn is_ready(&self) -> bool {
        self.status == PetriSuccessorTrustMcChcProofHandoffStatus::Ready
            && self.reason == PetriSuccessorTrustMcChcProofHandoffReason::Ready
    }

    pub fn fail_closed(&self) -> bool {
        !self.is_ready()
    }

    pub fn status_code(&self) -> &'static str {
        self.status.code()
    }

    pub fn reason_code(&self) -> &'static str {
        self.reason.code()
    }

    /// Stable TrustIr-owned identity for Petri proof/evidence handoff rows.
    ///
    /// Downstream MCC/TY sidecars can persist this digest and the matching
    /// rows instead of reconstructing proof, evidence, replay, and solver
    /// identity fields from nested reports.
    pub fn proof_evidence_identity_digest(&self) -> ProofDigest {
        petri_successor_trust_mc_chc_proof_evidence_identity_digest(self)
    }

    /// Emit stable proof/evidence identity rows for sidecar persistence.
    pub fn proof_evidence_identity_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        let identity_digest = self.proof_evidence_identity_digest();
        let semantic_bridge_report = &self.binding_report.semantic_bridge_report;
        let proof_identity_digest = semantic_bridge_report.proof_identity_digest();
        let mut solver_identities = self.solver_identities.clone();
        solver_identities.sort();

        push_manifest_row(
            &mut rows,
            "proof_evidence_identity.schema",
            PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity.schema_version",
            PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity.digest.context",
            PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT,
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity.digest.algorithm",
            proof_digest_algorithm_code(identity_digest.algorithm),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity.digest",
            identity_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity.function",
            self.function.index().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.schema",
            semantic_bridge_report.schema.as_str(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.schema_version",
            semantic_bridge_report.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.status",
            semantic_bridge_report.status_code(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.reason",
            semantic_bridge_report.reason_code(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.evidence_status",
            semantic_bridge_report.evidence_status_code(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.proof_identity.schema",
            semantic_bridge_report.proof_identity_schema(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.proof_identity.schema_version",
            semantic_bridge_report
                .proof_identity_schema_version()
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "semantic_bridge.proof_identity.digest",
            proof_identity_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "binding.schema",
            self.binding_report.schema.as_str(),
        );
        push_manifest_row(
            &mut rows,
            "binding.schema_version",
            self.binding_report.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "binding.status",
            self.binding_report.status_code(),
        );
        push_manifest_row(
            &mut rows,
            "binding.reason",
            self.binding_report.reason_code(),
        );
        push_manifest_row(
            &mut rows,
            "binding.fail_closed",
            bool_code(self.binding_report.fail_closed()),
        );
        push_optional_u32_manifest_row(
            &mut rows,
            "binding.request.id",
            self.binding_report.request.map(NativeRequestId::index),
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "binding.request.digest",
            self.binding_report.request_digest,
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "binding.evidence.digest",
            self.binding_report.evidence_digest,
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "binding.expected_evidence.digest",
            self.binding_report.expected_evidence_digest,
        );
        push_optional_artifact_manifest_rows(
            &mut rows,
            "binding.horn_clause_artifact",
            self.binding_report.horn_clause_artifact.as_ref(),
        );
        push_manifest_row(&mut rows, "proof_handoff.schema", self.schema.as_str());
        push_manifest_row(
            &mut rows,
            "proof_handoff.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(&mut rows, "proof_handoff.status", self.status_code());
        push_manifest_row(&mut rows, "proof_handoff.reason", self.reason_code());
        push_manifest_row(
            &mut rows,
            "proof_handoff.fail_closed",
            bool_code(self.fail_closed()),
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "proof_handoff.proof_identity.digest",
            self.proof_identity_digest,
        );
        push_manifest_row(
            &mut rows,
            "proof_handoff.replay.engine",
            self.replay
                .as_ref()
                .map(|replay| replay.engine.as_str())
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_handoff.replay.invocation",
            self.replay
                .as_ref()
                .map(|replay| replay.invocation.as_str())
                .unwrap_or("none"),
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "proof_handoff.replay.transcript_digest",
            self.replay_transcript_digest,
        );
        push_optional_artifact_manifest_rows(
            &mut rows,
            "proof_handoff.replay_transcript_artifact",
            self.replay_transcript_artifact.as_ref(),
        );
        push_optional_artifact_manifest_rows(
            &mut rows,
            "proof_handoff.model_artifact",
            self.model_artifact.as_ref(),
        );
        push_manifest_row(
            &mut rows,
            "proof_handoff.solver_identity.count",
            solver_identities.len().to_string(),
        );
        for (index, solver) in solver_identities.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("proof_handoff.solver_identity.{index}.name"),
                &solver.name,
            );
            push_manifest_row(
                &mut rows,
                format!("proof_handoff.solver_identity.{index}.canonical_name"),
                solver.canonical_name(),
            );
            push_manifest_row(
                &mut rows,
                format!("proof_handoff.solver_identity.{index}.version"),
                solver.version.as_deref().unwrap_or("none"),
            );
            push_manifest_row(
                &mut rows,
                format!("proof_handoff.solver_identity.{index}.revision"),
                solver.revision.as_deref().unwrap_or("none"),
            );
            push_optional_digest_manifest_row(
                &mut rows,
                format!("proof_handoff.solver_identity.{index}.digest"),
                solver.digest,
            );
        }

        rows
    }

    /// Emit stable escaped `key=value` proof/evidence identity rows.
    pub fn proof_evidence_identity_key_value_lines(&self) -> Vec<String> {
        self.proof_evidence_identity_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit stable line-oriented proof/evidence identity text.
    pub fn proof_evidence_identity_key_value_text(&self) -> String {
        format!(
            "{}\n",
            self.proof_evidence_identity_key_value_lines().join("\n")
        )
    }

    /// Validate persisted proof/evidence identity rows against this report.
    pub fn proof_evidence_identity_replay_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport {
        self.proof_evidence_identity_replay_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate persisted proof/evidence identity `key=value` lines.
    pub fn proof_evidence_identity_replay_report_for_key_value_lines(
        &self,
        lines: &[String],
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport {
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.proof_evidence_identity_replay_report_with_invalid_lines(&rows, invalid_lines)
    }

    /// Validate persisted proof/evidence identity line-oriented text.
    pub fn proof_evidence_identity_replay_report_for_key_value_text(
        &self,
        text: &str,
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport {
        let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
        self.proof_evidence_identity_replay_report_for_key_value_lines(&lines)
    }

    fn proof_evidence_identity_replay_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport {
        let expected_rows = self.proof_evidence_identity_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_bool_keys = Vec::new();
        let mut invalid_usize_keys = Vec::new();
        let reconstructed_schema =
            observed_single_value(&observed_by_key, "proof_evidence_identity.schema")
                .map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "proof_evidence_identity.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_identity_digest =
            observed_single_value(&observed_by_key, "proof_evidence_identity.digest")
                .map(str::to_string);
        let reconstructed_function = observed_usize_value(
            &observed_by_key,
            "proof_evidence_identity.function",
            &mut invalid_usize_keys,
        );
        let reconstructed_proof_handoff_status =
            observed_single_value(&observed_by_key, "proof_handoff.status").map(str::to_string);
        let reconstructed_proof_handoff_reason =
            observed_single_value(&observed_by_key, "proof_handoff.reason").map(str::to_string);
        let reconstructed_proof_handoff_fail_closed = observed_bool_value(
            &observed_by_key,
            "proof_handoff.fail_closed",
            &mut invalid_bool_keys,
        );
        let reconstructed_solver_identity_count = observed_usize_value(
            &observed_by_key,
            "proof_handoff.solver_identity.count",
            &mut invalid_usize_keys,
        );

        let expected_identity_digest = self.proof_evidence_identity_digest().to_string();
        let schema_matches = reconstructed_schema.as_deref()
            == Some(PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA)
            && reconstructed_schema_version
                == Some(
                    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION as usize,
                );
        let identity_digest_matches =
            reconstructed_identity_digest.as_deref() == Some(expected_identity_digest.as_str());
        let function_matches = reconstructed_function == Some(self.function.index() as usize);
        let proof_handoff_status_matches = reconstructed_proof_handoff_status.as_deref()
            == Some(self.status_code())
            && reconstructed_proof_handoff_reason.as_deref() == Some(self.reason_code());
        let proof_handoff_fail_closed_matches =
            reconstructed_proof_handoff_fail_closed == Some(self.fail_closed());
        let solver_identity_count_matches =
            reconstructed_solver_identity_count == Some(self.solver_identities.len());

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
            && invalid_usize_keys.is_empty()
            && invalid_lines.is_empty()
            && schema_matches
            && identity_digest_matches
            && function_matches
            && proof_handoff_status_matches
            && proof_handoff_fail_closed_matches
            && solver_identity_count_matches
        {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Replayable
        } else {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Invalid
        };

        PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport {
            schema: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA,
            schema_version:
                PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA_VERSION,
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Replayable
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            invalid_usize_keys,
            invalid_lines,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_identity_digest,
            reconstructed_function,
            reconstructed_proof_handoff_status,
            reconstructed_proof_handoff_reason,
            reconstructed_proof_handoff_fail_closed,
            reconstructed_solver_identity_count,
            schema_matches,
            identity_digest_matches,
            function_matches,
            proof_handoff_status_matches,
            proof_handoff_fail_closed_matches,
            solver_identity_count_matches,
        }
    }
}

/// Replay-validation status for persisted Petri proof/evidence identity rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus {
    Replayable,
    Invalid,
}

impl PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Replayable => "replayable",
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Invalid => "invalid",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Replayable => {
                "proof evidence identity rows replayable"
            }
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Invalid => {
                "proof evidence identity rows invalid"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Round-trip status for persisted proof/evidence replay health summaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus {
    Valid,
    Invalid,
}

impl PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Valid => {
                "valid"
            }
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Invalid => {
                "invalid"
            }
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Valid => {
                "proof evidence identity replay health summary valid"
            }
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Invalid => {
                "proof evidence identity replay health summary invalid"
            }
        }
    }
}

impl core::fmt::Display
    for PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Validation report for persisted proof/evidence replay health summaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport {
    pub status: PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_status: Option<String>,
    pub reconstructed_fail_closed: Option<bool>,
    pub reconstructed_diagnostic_count: Option<usize>,
    pub schema_matches: bool,
    pub status_matches: bool,
    pub fail_closed_matches: bool,
    pub diagnostic_count_matches: bool,
}

impl PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport {
    pub fn is_valid(&self) -> bool {
        matches!(
            self.status,
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Valid
        ) && !self.fail_closed
    }

    pub fn diagnostic_count(&self) -> usize {
        self.duplicate_keys.len()
            + self.missing_keys.len()
            + self.unexpected_keys.len()
            + self.mismatched_value_keys.len()
            + self.invalid_bool_keys.len()
            + self.invalid_usize_keys.len()
            + self.invalid_lines.len()
    }
}

/// Compact health summary for persisted proof/evidence identity rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport {
    pub schema: &'static str,
    pub schema_version: u32,
    pub status: PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_identity_digest: Option<String>,
    pub reconstructed_function: Option<usize>,
    pub reconstructed_proof_handoff_status: Option<String>,
    pub reconstructed_proof_handoff_reason: Option<String>,
    pub reconstructed_proof_handoff_fail_closed: Option<bool>,
    pub reconstructed_solver_identity_count: Option<usize>,
    pub schema_matches: bool,
    pub identity_digest_matches: bool,
    pub function_matches: bool,
    pub proof_handoff_status_matches: bool,
    pub proof_handoff_fail_closed_matches: bool,
    pub solver_identity_count_matches: bool,
}

impl PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport {
    pub fn is_replayable(&self) -> bool {
        matches!(
            self.status,
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Replayable
        ) && !self.fail_closed
    }

    pub fn diagnostic_count(&self) -> usize {
        self.duplicate_keys.len()
            + self.missing_keys.len()
            + self.unexpected_keys.len()
            + self.mismatched_value_keys.len()
            + self.invalid_bool_keys.len()
            + self.invalid_usize_keys.len()
            + self.invalid_lines.len()
    }

    /// Emit component-addressed replay health rows for compact readiness sidecars.
    pub fn component_health_summary_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        let prefix = "proof_evidence_identity_replay_component_summary";
        let proof_handoff_reason_matches = self.reconstructed_proof_handoff_reason.is_some()
            && !self
                .missing_keys
                .iter()
                .any(|key| key == "proof_handoff.reason")
            && !self
                .duplicate_keys
                .iter()
                .any(|key| key == "proof_handoff.reason")
            && !self
                .mismatched_value_keys
                .iter()
                .any(|key| key == "proof_handoff.reason");

        push_manifest_row(&mut rows, format!("{prefix}.schema"), self.schema);
        push_manifest_row(
            &mut rows,
            format!("{prefix}.schema_version"),
            self.schema_version.to_string(),
        );
        push_manifest_row(&mut rows, format!("{prefix}.status"), self.status_code);
        push_manifest_row(
            &mut rows,
            format!("{prefix}.fail_closed"),
            bool_code(self.fail_closed),
        );
        push_manifest_row(
            &mut rows,
            format!("{prefix}.diagnostic_count"),
            self.diagnostic_count().to_string(),
        );
        push_manifest_row(&mut rows, format!("{prefix}.component.count"), "7");
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "schema",
            self.reconstructed_schema.as_deref().unwrap_or("none"),
            self.schema_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "identity_digest",
            self.reconstructed_identity_digest
                .as_deref()
                .unwrap_or("none"),
            self.identity_digest_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "function",
            self.reconstructed_function
                .map(|function| function.to_string())
                .unwrap_or_else(|| "none".to_string()),
            self.function_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "proof_handoff_status",
            self.reconstructed_proof_handoff_status
                .as_deref()
                .unwrap_or("none"),
            self.proof_handoff_status_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "proof_handoff_reason",
            self.reconstructed_proof_handoff_reason
                .as_deref()
                .unwrap_or("none"),
            proof_handoff_reason_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "proof_handoff_fail_closed",
            self.reconstructed_proof_handoff_fail_closed
                .map(bool_code)
                .unwrap_or("none"),
            self.proof_handoff_fail_closed_matches,
        );
        push_replay_component_health_summary_rows(
            &mut rows,
            prefix,
            "solver_identity_count",
            self.reconstructed_solver_identity_count
                .map(|count| count.to_string())
                .unwrap_or_else(|| "none".to_string()),
            self.solver_identity_count_matches,
        );

        rows
    }

    /// Emit escaped `key=value` component health rows.
    pub fn component_health_summary_key_value_lines(&self) -> Vec<String> {
        self.component_health_summary_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit line-oriented component health text for readiness sidecars.
    pub fn component_health_summary_key_value_text(&self) -> String {
        format!(
            "{}\n",
            self.component_health_summary_key_value_lines().join("\n")
        )
    }

    /// Emit deterministic health rows for sidecar persistence.
    pub fn compact_health_summary_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.schema",
            self.schema,
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.status",
            self.status_code,
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.fail_closed",
            bool_code(self.fail_closed),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.count.expected_rows",
            self.expected_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.count.observed_rows",
            self.observed_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.count.unique_keys",
            self.unique_key_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.count.diagnostics",
            self.diagnostic_count().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.schema",
            self.reconstructed_schema.as_deref().unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.schema_version",
            self.reconstructed_schema_version
                .map(|version| version.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.identity_digest",
            self.reconstructed_identity_digest
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.function",
            self.reconstructed_function
                .map(|function| function.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.proof_handoff.status",
            self.reconstructed_proof_handoff_status
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.proof_handoff.reason",
            self.reconstructed_proof_handoff_reason
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.proof_handoff.fail_closed",
            self.reconstructed_proof_handoff_fail_closed
                .map(bool_code)
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.reconstructed.solver_identity.count",
            self.reconstructed_solver_identity_count
                .map(|count| count.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.agreement.schema",
            bool_code(self.schema_matches),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.agreement.identity_digest",
            bool_code(self.identity_digest_matches),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.agreement.function",
            bool_code(self.function_matches),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.agreement.proof_handoff_status",
            bool_code(self.proof_handoff_status_matches),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.agreement.proof_handoff_fail_closed",
            bool_code(self.proof_handoff_fail_closed_matches),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.agreement.solver_identity_count",
            bool_code(self.solver_identity_count_matches),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.diagnostic.duplicate_keys",
            self.duplicate_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.diagnostic.missing_keys",
            self.missing_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.diagnostic.unexpected_keys",
            self.unexpected_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.diagnostic.mismatched_value_keys",
            self.mismatched_value_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.diagnostic.invalid_bool_keys",
            self.invalid_bool_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.diagnostic.invalid_usize_keys",
            self.invalid_usize_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_evidence_identity_replay_report.diagnostic.invalid_lines",
            self.invalid_lines.len().to_string(),
        );

        rows
    }

    /// Emit escaped `key=value` rows for compact health persistence.
    pub fn compact_health_summary_key_value_lines(&self) -> Vec<String> {
        self.compact_health_summary_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit stable line-oriented compact health text.
    pub fn compact_health_summary_key_value_text(&self) -> String {
        format!(
            "{}\n",
            self.compact_health_summary_key_value_lines().join("\n")
        )
    }

    /// Emit compact JSON for non-Rust sidecar validation.
    pub fn compact_health_summary_json_text(&self) -> String {
        let optional_string = |value: Option<&str>| {
            value
                .map(json_string_literal)
                .unwrap_or_else(|| "null".to_string())
        };
        let optional_usize = |value: Option<usize>| {
            value
                .map(|value| value.to_string())
                .unwrap_or_else(|| "null".to_string())
        };
        let optional_bool = |value: Option<bool>| value.map(bool_code).unwrap_or("null");

        format!(
            "{{\"schema\":{},\"schema_version\":{},\"status\":{},\"fail_closed\":{},\"expected_row_count\":{},\"observed_row_count\":{},\"unique_key_count\":{},\"diagnostic_count\":{},\"reconstructed_schema\":{},\"reconstructed_schema_version\":{},\"reconstructed_identity_digest\":{},\"reconstructed_function\":{},\"reconstructed_proof_handoff_status\":{},\"reconstructed_proof_handoff_reason\":{},\"reconstructed_proof_handoff_fail_closed\":{},\"reconstructed_solver_identity_count\":{},\"schema_matches\":{},\"identity_digest_matches\":{},\"function_matches\":{},\"proof_handoff_status_matches\":{},\"proof_handoff_fail_closed_matches\":{},\"solver_identity_count_matches\":{},\"duplicate_key_count\":{},\"missing_key_count\":{},\"unexpected_key_count\":{},\"mismatched_value_key_count\":{},\"invalid_bool_key_count\":{},\"invalid_usize_key_count\":{},\"invalid_line_count\":{}}}\n",
            json_string_literal(self.schema),
            self.schema_version,
            json_string_literal(self.status_code),
            bool_code(self.fail_closed),
            self.expected_row_count,
            self.observed_row_count,
            self.unique_key_count,
            self.diagnostic_count(),
            optional_string(self.reconstructed_schema.as_deref()),
            optional_usize(self.reconstructed_schema_version),
            optional_string(self.reconstructed_identity_digest.as_deref()),
            optional_usize(self.reconstructed_function),
            optional_string(self.reconstructed_proof_handoff_status.as_deref()),
            optional_string(self.reconstructed_proof_handoff_reason.as_deref()),
            optional_bool(self.reconstructed_proof_handoff_fail_closed),
            optional_usize(self.reconstructed_solver_identity_count),
            bool_code(self.schema_matches),
            bool_code(self.identity_digest_matches),
            bool_code(self.function_matches),
            bool_code(self.proof_handoff_status_matches),
            bool_code(self.proof_handoff_fail_closed_matches),
            bool_code(self.solver_identity_count_matches),
            self.duplicate_keys.len(),
            self.missing_keys.len(),
            self.unexpected_keys.len(),
            self.mismatched_value_keys.len(),
            self.invalid_bool_keys.len(),
            self.invalid_usize_keys.len(),
            self.invalid_lines.len()
        )
    }

    /// Validate persisted compact health rows against this replay report.
    pub fn compact_health_summary_round_trip_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport {
        self.compact_health_summary_round_trip_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate persisted compact health `key=value` lines against this replay report.
    pub fn compact_health_summary_round_trip_report_for_key_value_lines(
        &self,
        lines: &[String],
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport {
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.compact_health_summary_round_trip_report_with_invalid_lines(&rows, invalid_lines)
    }

    /// Validate persisted compact health line-oriented text against this replay report.
    pub fn compact_health_summary_round_trip_report_for_key_value_text(
        &self,
        text: &str,
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport {
        let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
        self.compact_health_summary_round_trip_report_for_key_value_lines(&lines)
    }

    fn compact_health_summary_round_trip_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport {
        let expected_rows = self.compact_health_summary_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_bool_keys = Vec::new();
        let mut invalid_usize_keys = Vec::new();
        let reconstructed_schema = observed_single_value(
            &observed_by_key,
            "proof_evidence_identity_replay_report.schema",
        )
        .map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "proof_evidence_identity_replay_report.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_status = observed_single_value(
            &observed_by_key,
            "proof_evidence_identity_replay_report.status",
        )
        .map(str::to_string);
        let reconstructed_fail_closed = observed_bool_value(
            &observed_by_key,
            "proof_evidence_identity_replay_report.fail_closed",
            &mut invalid_bool_keys,
        );
        let reconstructed_diagnostic_count = observed_usize_value(
            &observed_by_key,
            "proof_evidence_identity_replay_report.count.diagnostics",
            &mut invalid_usize_keys,
        );

        for key in [
            "proof_evidence_identity_replay_report.count.expected_rows",
            "proof_evidence_identity_replay_report.count.observed_rows",
            "proof_evidence_identity_replay_report.count.unique_keys",
            "proof_evidence_identity_replay_report.reconstructed.schema_version",
            "proof_evidence_identity_replay_report.reconstructed.function",
            "proof_evidence_identity_replay_report.reconstructed.solver_identity.count",
            "proof_evidence_identity_replay_report.diagnostic.duplicate_keys",
            "proof_evidence_identity_replay_report.diagnostic.missing_keys",
            "proof_evidence_identity_replay_report.diagnostic.unexpected_keys",
            "proof_evidence_identity_replay_report.diagnostic.mismatched_value_keys",
            "proof_evidence_identity_replay_report.diagnostic.invalid_bool_keys",
            "proof_evidence_identity_replay_report.diagnostic.invalid_usize_keys",
            "proof_evidence_identity_replay_report.diagnostic.invalid_lines",
        ] {
            let _ = observed_usize_value(&observed_by_key, key, &mut invalid_usize_keys);
        }

        for key in [
            "proof_evidence_identity_replay_report.reconstructed.proof_handoff.fail_closed",
            "proof_evidence_identity_replay_report.agreement.schema",
            "proof_evidence_identity_replay_report.agreement.identity_digest",
            "proof_evidence_identity_replay_report.agreement.function",
            "proof_evidence_identity_replay_report.agreement.proof_handoff_status",
            "proof_evidence_identity_replay_report.agreement.proof_handoff_fail_closed",
            "proof_evidence_identity_replay_report.agreement.solver_identity_count",
        ] {
            let _ = observed_bool_value(&observed_by_key, key, &mut invalid_bool_keys);
        }

        let schema_matches = reconstructed_schema.as_deref() == Some(self.schema)
            && reconstructed_schema_version == Some(self.schema_version as usize);
        let status_matches = reconstructed_status.as_deref() == Some(self.status_code);
        let fail_closed_matches = reconstructed_fail_closed == Some(self.fail_closed);
        let diagnostic_count_matches =
            reconstructed_diagnostic_count == Some(self.diagnostic_count());

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
            && invalid_usize_keys.is_empty()
            && invalid_lines.is_empty()
            && schema_matches
            && status_matches
            && fail_closed_matches
            && diagnostic_count_matches
        {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Valid
        } else {
            PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Invalid
        };

        PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Valid
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            invalid_usize_keys,
            invalid_lines,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_status,
            reconstructed_fail_closed,
            reconstructed_diagnostic_count,
            schema_matches,
            status_matches,
            fail_closed_matches,
            diagnostic_count_matches,
        }
    }
}

/// Readiness status for solver-owned Petri successor TrustMc CHC model validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcModelValidationReadinessStatus {
    ReadyForSolverValidation,
    Blocked,
}

impl PetriSuccessorTrustMcChcModelValidationReadinessStatus {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcModelValidationReadinessStatus::ReadyForSolverValidation => {
                "ready_for_solver_validation"
            }
            PetriSuccessorTrustMcChcModelValidationReadinessStatus::Blocked => "blocked",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcModelValidationReadinessStatus::ReadyForSolverValidation => {
                "ready for solver model validation"
            }
            PetriSuccessorTrustMcChcModelValidationReadinessStatus::Blocked => {
                "model validation readiness blocked"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorTrustMcChcModelValidationReadinessStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Fail-closed reason for Petri successor TrustMc CHC model validation readiness.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorTrustMcChcModelValidationReadinessReason {
    SolverValidationRequired,
    ProofHandoffBlocked,
    MissingModelArtifact,
}

impl PetriSuccessorTrustMcChcModelValidationReadinessReason {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcModelValidationReadinessReason::SolverValidationRequired => {
                "solver_validation_required"
            }
            PetriSuccessorTrustMcChcModelValidationReadinessReason::ProofHandoffBlocked => {
                "proof_handoff_blocked"
            }
            PetriSuccessorTrustMcChcModelValidationReadinessReason::MissingModelArtifact => {
                "missing_model_artifact"
            }
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorTrustMcChcModelValidationReadinessReason::SolverValidationRequired => {
                "solver validation required"
            }
            PetriSuccessorTrustMcChcModelValidationReadinessReason::ProofHandoffBlocked => {
                "proof handoff blocked"
            }
            PetriSuccessorTrustMcChcModelValidationReadinessReason::MissingModelArtifact => {
                "missing model artifact"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorTrustMcChcModelValidationReadinessReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Typed readiness report for solver-owned Petri successor TrustMc CHC model validation.
///
/// TrustIr can identify the model artifact and proof handoff needed by a solver,
/// but it does not validate the model. The report therefore remains fail-closed
/// for acceptance even when the inputs are ready for TrustMc/AY validation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PetriSuccessorTrustMcChcModelValidationReadinessReport {
    pub schema: String,
    pub schema_version: u32,
    pub function: FuncId,
    pub proof_handoff_report: PetriSuccessorTrustMcChcProofHandoffReport,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub model_artifact: Option<NativeEvidenceArtifact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub model_artifact_digest: Option<ProofDigest>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub solver_identities: Vec<NativeToolIdentity>,
    pub model_validated: bool,
    pub status: PetriSuccessorTrustMcChcModelValidationReadinessStatus,
    pub reason: PetriSuccessorTrustMcChcModelValidationReadinessReason,
}

impl PetriSuccessorTrustMcChcModelValidationReadinessReport {
    pub fn is_ready_for_solver_validation(&self) -> bool {
        self.status
            == PetriSuccessorTrustMcChcModelValidationReadinessStatus::ReadyForSolverValidation
            && self.reason
                == PetriSuccessorTrustMcChcModelValidationReadinessReason::SolverValidationRequired
            && self.model_artifact.is_some()
            && !self.model_validated
    }

    pub fn fail_closed(&self) -> bool {
        !self.model_validated
    }

    pub fn status_code(&self) -> &'static str {
        self.status.code()
    }

    pub fn reason_code(&self) -> &'static str {
        self.reason.code()
    }
}

/// Admission status for a Petri successor semantic bridge proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorSemanticBridgeProofAdmissionStatus {
    Admitted,
    Blocked,
}

impl PetriSuccessorSemanticBridgeProofAdmissionStatus {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorSemanticBridgeProofAdmissionStatus::Admitted => "admitted",
            PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked => "blocked",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorSemanticBridgeProofAdmissionStatus::Admitted => {
                "semantic bridge proof admitted"
            }
            PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked => {
                "semantic bridge proof admission blocked"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorSemanticBridgeProofAdmissionStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Fail-closed reason for Petri successor semantic bridge proof admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PetriSuccessorSemanticBridgeProofAdmissionReason {
    Admitted,
    ProofHandoffBlocked,
    ArtifactResolutionBlocked,
}

impl PetriSuccessorSemanticBridgeProofAdmissionReason {
    pub const fn code(self) -> &'static str {
        match self {
            PetriSuccessorSemanticBridgeProofAdmissionReason::Admitted => "admitted",
            PetriSuccessorSemanticBridgeProofAdmissionReason::ProofHandoffBlocked => {
                "proof_handoff_blocked"
            }
            PetriSuccessorSemanticBridgeProofAdmissionReason::ArtifactResolutionBlocked => {
                "artifact_resolution_blocked"
            }
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            PetriSuccessorSemanticBridgeProofAdmissionReason::Admitted => "admitted",
            PetriSuccessorSemanticBridgeProofAdmissionReason::ProofHandoffBlocked => {
                "proof handoff blocked"
            }
            PetriSuccessorSemanticBridgeProofAdmissionReason::ArtifactResolutionBlocked => {
                "artifact resolution blocked"
            }
        }
    }
}

impl core::fmt::Display for PetriSuccessorSemanticBridgeProofAdmissionReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Typed admission report for Petri successor semantic bridge proof evidence.
///
/// The report admits only byte-backed artifacts resolved by TrustIr. It does not
/// validate solver model semantics; consumers must still require solver-owned
/// acceptance before treating a model as checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriSuccessorSemanticBridgeProofAdmissionReport<'a> {
    pub schema: String,
    pub schema_version: u32,
    pub function: FuncId,
    pub proof_handoff_report: PetriSuccessorTrustMcChcProofHandoffReport,
    pub required_artifact_kinds: Vec<NativeEvidenceArtifactKind>,
    pub artifact_resolutions: Vec<NativeEvidenceArtifactAttachmentResolution<'a>>,
    pub blocked_artifact_kind: Option<NativeEvidenceArtifactKind>,
    pub blocked_artifact_reason: Option<NativeEvidenceArtifactResolutionReason>,
    pub status: PetriSuccessorSemanticBridgeProofAdmissionStatus,
    pub reason: PetriSuccessorSemanticBridgeProofAdmissionReason,
}

impl<'a> PetriSuccessorSemanticBridgeProofAdmissionReport<'a> {
    pub fn is_admitted(&self) -> bool {
        self.status == PetriSuccessorSemanticBridgeProofAdmissionStatus::Admitted
            && self.reason == PetriSuccessorSemanticBridgeProofAdmissionReason::Admitted
            && self
                .artifact_resolutions
                .iter()
                .all(NativeEvidenceArtifactAttachmentResolution::is_authoritative)
    }

    pub fn fail_closed(&self) -> bool {
        !self.is_admitted()
    }

    pub fn status_code(&self) -> &'static str {
        self.status.code()
    }

    pub fn reason_code(&self) -> &'static str {
        self.reason.code()
    }

    pub fn blocked_artifact_reason_code(&self) -> Option<&'static str> {
        self.blocked_artifact_reason
            .map(NativeEvidenceArtifactResolutionReason::code)
    }

    pub fn artifact_resolution_for_kind(
        &self,
        kind: NativeEvidenceArtifactKind,
    ) -> Option<&NativeEvidenceArtifactAttachmentResolution<'a>> {
        self.artifact_resolutions
            .iter()
            .find(|resolution| resolution.required_kind == kind)
    }

    pub fn authoritative_bytes_for_kind(
        &self,
        kind: NativeEvidenceArtifactKind,
    ) -> Option<&'a [u8]> {
        self.artifact_resolution_for_kind(kind)
            .and_then(NativeEvidenceArtifactAttachmentResolution::authoritative_bytes)
    }

    pub fn authoritative_byte_count(&self) -> usize {
        self.artifact_resolutions
            .iter()
            .filter_map(NativeEvidenceArtifactAttachmentResolution::authoritative_bytes)
            .map(<[u8]>::len)
            .sum()
    }

    /// Emit stable admission rows for downstream sidecars.
    ///
    /// The row shape is producer-owned so TY and MCC consumers can persist
    /// admission facts without reconstructing report serialization locally.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();

        push_manifest_row(&mut rows, "proof_admission.schema", self.schema.as_str());
        push_manifest_row(
            &mut rows,
            "proof_admission.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "proof_admission.function",
            self.function.index().to_string(),
        );
        push_manifest_row(&mut rows, "proof_admission.status", self.status_code());
        push_manifest_row(&mut rows, "proof_admission.reason", self.reason_code());
        push_manifest_row(
            &mut rows,
            "proof_admission.fail_closed",
            bool_code(self.fail_closed()),
        );
        push_manifest_row(
            &mut rows,
            "proof_admission.proof_handoff.status",
            self.proof_handoff_report.status_code(),
        );
        push_manifest_row(
            &mut rows,
            "proof_admission.proof_handoff.reason",
            self.proof_handoff_report.reason_code(),
        );
        push_manifest_row(
            &mut rows,
            "proof_admission.proof_handoff.fail_closed",
            bool_code(self.proof_handoff_report.fail_closed()),
        );
        push_manifest_row(
            &mut rows,
            "proof_admission.required_artifact_kind.count",
            self.required_artifact_kinds.len().to_string(),
        );
        for (index, kind) in self.required_artifact_kinds.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("proof_admission.required_artifact_kind.{index}"),
                kind.code(),
            );
        }
        push_manifest_row(
            &mut rows,
            "proof_admission.blocked_artifact.kind",
            self.blocked_artifact_kind
                .map(NativeEvidenceArtifactKind::code)
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_admission.blocked_artifact.reason",
            self.blocked_artifact_reason
                .map(NativeEvidenceArtifactResolutionReason::code)
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "proof_admission.artifact_resolution.count",
            self.artifact_resolutions.len().to_string(),
        );
        for (index, resolution) in self.artifact_resolutions.iter().enumerate() {
            let prefix = format!("proof_admission.artifact_resolution.{index}");
            let authority = resolution
                .resolution
                .as_ref()
                .map(|resolution| resolution.report.authority_code())
                .unwrap_or("none");
            let authoritative_byte_count = resolution
                .authoritative_bytes()
                .map(<[u8]>::len)
                .unwrap_or(0);

            push_manifest_row(
                &mut rows,
                format!("{prefix}.required_kind"),
                resolution.required_kind.code(),
            );
            push_manifest_row(
                &mut rows,
                format!("{prefix}.artifact_kind"),
                resolution
                    .artifact
                    .map(|artifact| artifact.kind.code())
                    .unwrap_or("none"),
            );
            push_manifest_row(
                &mut rows,
                format!("{prefix}.status"),
                resolution.status_code(),
            );
            push_manifest_row(
                &mut rows,
                format!("{prefix}.reason"),
                resolution.reason_code(),
            );
            push_manifest_row(&mut rows, format!("{prefix}.authority"), authority);
            push_manifest_row(
                &mut rows,
                format!("{prefix}.bytes_present"),
                bool_code(resolution.bytes().is_some()),
            );
            push_manifest_row(
                &mut rows,
                format!("{prefix}.authoritative_bytes_available"),
                bool_code(resolution.authoritative_bytes().is_some()),
            );
            push_manifest_row(
                &mut rows,
                format!("{prefix}.authoritative_byte_count"),
                authoritative_byte_count.to_string(),
            );
        }
        push_manifest_row(
            &mut rows,
            "proof_admission.authoritative_byte_count",
            self.authoritative_byte_count().to_string(),
        );

        rows
    }

    /// Emit stable escaped `key=value` admission rows.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit stable line-oriented admission text.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }
}

/// Stable id for one frontend monomorphization instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeMonomorphizationId(pub u32);

impl NativeMonomorphizationId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    pub const fn index(self) -> u32 {
        self.0
    }
}

impl core::fmt::Display for NativeMonomorphizationId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Frontend enum tag strategy, carried as data for verifier encoders.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeEnumTagEncoding {
    /// A concrete discriminant/tag field is present in memory.
    Direct,
    /// One or more invalid payload values encode at least one variant.
    Niche,
    /// No runtime tag is needed for this layout.
    Untagged,
}

/// Integer range used by niche-optimized enum layout facts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeIntegerRange {
    #[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_i128"))]
    pub start: i128,
    #[cfg_attr(feature = "serde", serde(with = "crate::wide_int_serde::wide_i128"))]
    pub end: i128,
}

/// Niche encoding details for an enum layout.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEnumNicheFact {
    pub variant_index: u32,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub field: Option<u32>,
    pub valid_range: NativeIntegerRange,
}

/// Concrete layout of one enum variant payload.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEnumVariantLayoutFact {
    pub variant_index: u32,
    pub name: String,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub discriminant: Option<i128>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub fields: Vec<FieldOffsetShape>,
    pub size_bits: u64,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub align_bits: Option<u64>,
}

/// Rust enum layout fact supplied by a frontend with rustc layout knowledge.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEnumLayoutFact {
    pub enum_id: EnumId,
    pub tag_encoding: NativeEnumTagEncoding,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub tag_bits: Option<u32>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub discriminant_offset_bits: Option<u64>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub niche: Option<NativeEnumNicheFact>,
    pub variants: Vec<NativeEnumVariantLayoutFact>,
}

/// Layout fact for an ADT. Struct facts use `layout.kind == Struct`; enum
/// facts use `layout.kind == Enum` plus the optional enum-specific details.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeAdtLayoutFact {
    pub id: NativeCompilerFactId,
    pub ty: Ty,
    pub layout: TyLayoutShape,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub enum_layout: Option<NativeEnumLayoutFact>,
}

/// Wide pointer metadata fact for slices, `str`, and trait objects.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeFatPointerFact {
    pub id: NativeCompilerFactId,
    pub ty: Ty,
    pub layout: PointerLayoutShape,
}

/// Concrete trait-object metadata identity supplied by a frontend with rustc
/// vtable/upcast knowledge.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeTraitObjectMetadataFact {
    pub id: NativeCompilerFactId,
    pub ty: Ty,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub source_ty: Option<Ty>,
    pub trait_id: u32,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub source_trait_id: Option<u32>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub upcast_path: Vec<u32>,
    pub vtable_symbol: String,
    pub stable_digest: ProofDigest,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub function: Option<FuncId>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub obligations: Vec<ProofId>,
}

/// Provenance outcome for a Rust raw-pointer offset fact.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativePointerOffsetProvenance {
    /// The result pointer keeps the same allocation/provenance identity as the
    /// base pointer and changes only its byte offset.
    SameAsBase,
    /// The producer encountered an offset form that this schema cannot encode.
    /// Any obligation source that binds this fact is rejected fail-closed.
    Unsupported(NativeUnsupportedMode),
}

/// Rust raw-pointer `Offset`/GEP provenance fact tied to a produced TrustIr value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativePointerOffsetFact {
    pub id: NativeCompilerFactId,
    pub function: FuncId,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub result: Option<ValueId>,
    pub base: ValueId,
    pub base_ty: Ty,
    pub pointee_ty: Ty,
    pub element_layout: TyLayoutShape,
    pub stride_bits: u64,
    pub offset: ValueId,
    pub offset_ty: Ty,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub signed_offset_const: Option<i128>,
    pub provenance: NativePointerOffsetProvenance,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub span: Option<SourceSpan>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub obligations: Vec<ProofId>,
}

/// Layout-sensitive cast/transmute fact tied to a produced TrustIr value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeCastFact {
    pub id: NativeCompilerFactId,
    pub function: FuncId,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub result: Option<ValueId>,
    pub op: CastOp,
    pub source_ty: Ty,
    pub target_ty: Ty,
    pub evidence: CastLayoutEvidence,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub span: Option<SourceSpan>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub obligations: Vec<ProofId>,
}

/// Generic argument identity after frontend monomorphization.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeGenericArg {
    Ty(Ty),
    Const { ty: Ty, value: Constant },
    LifetimeErased,
    Placeholder { index: u32 },
}

/// Frontend monomorphization identity for mapping verifier output back to
/// generic Rust items without parsing symbol names.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeMonomorphizationFact {
    pub id: NativeMonomorphizationId,
    pub source_item: String,
    pub symbol: String,
    pub generic_args: Vec<NativeGenericArg>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub function: Option<FuncId>,
    pub stable_digest: ProofDigest,
}

/// Why a verifier obligation was emitted at a source location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeObligationCause {
    Precondition,
    Postcondition,
    Assert,
    BoundsCheck,
    OverflowCheck,
    LayoutCheck,
    CastCheck,
    PointerOffset,
    BorrowCheck,
    Translation,
    Panic,
    Temporal,
    Other,
}

/// Typed reference from an obligation source map entry to a compiler fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeCompilerFactRef {
    AdtLayout(NativeCompilerFactId),
    FatPointer(NativeCompilerFactId),
    TraitObjectMetadata(NativeCompilerFactId),
    PointerOffset(NativeCompilerFactId),
    Cast(NativeCompilerFactId),
    Monomorphization(NativeMonomorphizationId),
}

/// Source location and typed compiler facts responsible for an obligation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeObligationSource {
    pub obligation: ProofId,
    /// Exact public verifier obligation identity that this native proof unit
    /// discharges. This is required proof-authority data: consumers must not
    /// infer it from ordering, descriptions, spans, or replay formulas.
    pub public_obligation_id: String,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub function: Option<FuncId>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub span: Option<SourceSpan>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub assertion_id: Option<NativeAssertionId>,
    pub cause: NativeObligationCause,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub monomorphization: Option<NativeMonomorphizationId>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub facts: Vec<NativeCompilerFactRef>,
}

/// Typed compiler facts that verifiers need for Rust bootstrap MIR without
/// scraping diagnostics or rustc-formatted strings.
#[derive(Debug, Clone, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeCompilerFacts {
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub adt_layouts: Vec<NativeAdtLayoutFact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub fat_pointers: Vec<NativeFatPointerFact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub trait_object_metadata: Vec<NativeTraitObjectMetadataFact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub pointer_offsets: Vec<NativePointerOffsetFact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub casts: Vec<NativeCastFact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub monomorphizations: Vec<NativeMonomorphizationFact>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub obligation_sources: Vec<NativeObligationSource>,
}

impl NativeCompilerFacts {
    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_compiler_facts_stable(&mut bytes, self);
        ProofDigest::sha256_domain("trust_ir.native.compiler.facts.v4", &bytes)
    }

    pub fn obligation_source(&self, obligation: ProofId) -> Option<&NativeObligationSource> {
        self.obligation_sources
            .iter()
            .find(|source| source.obligation == obligation)
    }

    /// Resolve one frontend monomorphization by its bundle-local typed id.
    pub fn monomorphization(
        &self,
        id: NativeMonomorphizationId,
    ) -> Option<&NativeMonomorphizationFact> {
        self.monomorphizations.iter().find(|fact| fact.id == id)
    }

    /// Resolve one frontend monomorphization by its cross-process stable
    /// identity. Validation rejects duplicate stable digests, so this lookup is
    /// unambiguous for admitted bundles.
    pub fn monomorphization_by_stable_digest(
        &self,
        digest: ProofDigest,
    ) -> Option<&NativeMonomorphizationFact> {
        self.monomorphizations
            .iter()
            .find(|fact| fact.stable_digest == digest)
    }

    pub fn obligation_source_by_public_id(
        &self,
        public_obligation_id: &str,
    ) -> Option<&NativeObligationSource> {
        self.obligation_sources
            .iter()
            .find(|source| source.public_obligation_id == public_obligation_id)
    }

    pub fn obligations_for_assertion(&self, assertion_id: NativeAssertionId) -> Vec<ProofId> {
        let mut obligations: Vec<ProofId> = self
            .obligation_sources
            .iter()
            .filter_map(|source| {
                (source.assertion_id == Some(assertion_id)).then_some(source.obligation)
            })
            .collect();
        obligations.sort();
        obligations.dedup();
        obligations
    }
}
