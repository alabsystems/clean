// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// TrustVc memory semantics for imported or merged certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustVcMemorySemantics {
    RustMir,
    TrustIr,
    StackedBorrows,
}

/// Policy for trusted evidence encountered through TrustVc certificate refs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustVcTrustedEvidencePolicy {
    Reject,
    AllowWithDiagnostic,
    Allow,
}

/// Merge rule for multiple TrustVc certificates targeting the same bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustVcMergeStrategy {
    RequireSameObligation,
    UnionDischargedObligations,
    PreferNewestLineage,
}

/// TrustVc-specific request semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustVcRequestOptions {
    pub memory_semantics: TrustVcMemorySemantics,
    pub trusted_evidence: TrustVcTrustedEvidencePolicy,
    pub merge_strategy: TrustVcMergeStrategy,
    /// Compatibility flag retained for older TrustVc request producers.
    /// Native bundle validation now requires replay identity on every request.
    pub require_replay_identity: bool,
}

impl Default for TrustVcRequestOptions {
    fn default() -> Self {
        Self {
            memory_semantics: TrustVcMemorySemantics::RustMir,
            trusted_evidence: TrustVcTrustedEvidencePolicy::AllowWithDiagnostic,
            merge_strategy: TrustVcMergeStrategy::RequireSameObligation,
            require_replay_identity: true,
        }
    }
}

/// Memory encoding selected for TrustMc queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustMcMemoryModel {
    TrustIrPlaces,
    FlatArrays,
    StackedBorrows,
}

/// Arithmetic encoding selected for TrustMc queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustMcArithmeticModel {
    FixedWidthBitvectors,
    MathematicalIntegers,
    RustChecked,
}

/// TrustMc CHC/PDR backend selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustMcChcEngine {
    Z3Fixedpoint,
    Spacer,
    NativePdr,
}

/// Invariant source used to seed or check CHC/PDR solving.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustMcInvariantSource {
    None,
    TrustIrProofObligations,
    TrustWp,
    TrustVc,
    UserSupplied,
}

/// PDR generalization strategy for TrustMc.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustMcPdrGeneralization {
    None,
    Cubes,
    Interpolants,
}

/// Slicing strategy before TrustMc encodes a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustMcSlicingMode {
    None,
    ObligationBackwardSlice,
    ConstraintIndependence,
}

/// BMC settings for TrustMc.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustMcBmcOptions {
    pub unwind_limit: u32,
    pub unwinding_assertions: bool,
}

impl Default for TrustMcBmcOptions {
    fn default() -> Self {
        Self {
            unwind_limit: 1,
            unwinding_assertions: true,
        }
    }
}

/// PDR settings carried by TrustMc CHC/PDR requests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustMcPdrOptions {
    pub enabled: bool,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub max_frames: Option<u32>,
    pub generalization: TrustMcPdrGeneralization,
}

impl Default for TrustMcPdrOptions {
    fn default() -> Self {
        Self {
            enabled: false,
            max_frames: None,
            generalization: TrustMcPdrGeneralization::Cubes,
        }
    }
}

/// CHC settings for TrustMc.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustMcChcOptions {
    pub engine: TrustMcChcEngine,
    pub invariant_source: TrustMcInvariantSource,
    pub pdr: TrustMcPdrOptions,
    pub emit_horn_clauses: bool,
}

impl Default for TrustMcChcOptions {
    fn default() -> Self {
        Self {
            engine: TrustMcChcEngine::Spacer,
            invariant_source: TrustMcInvariantSource::TrustIrProofObligations,
            pdr: TrustMcPdrOptions::default(),
            emit_horn_clauses: false,
        }
    }
}

/// TrustMc-specific request semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustMcRequestOptions {
    pub memory_model: TrustMcMemoryModel,
    pub arithmetic_model: TrustMcArithmeticModel,
    pub bmc: TrustMcBmcOptions,
    pub chc: TrustMcChcOptions,
    pub slicing: TrustMcSlicingMode,
}

impl Default for TrustMcRequestOptions {
    fn default() -> Self {
        Self {
            memory_model: TrustMcMemoryModel::TrustIrPlaces,
            arithmetic_model: TrustMcArithmeticModel::FixedWidthBitvectors,
            bmc: TrustMcBmcOptions::default(),
            chc: TrustMcChcOptions::default(),
            slicing: TrustMcSlicingMode::ObligationBackwardSlice,
        }
    }
}

/// Heap model selected for TrustWp deductive verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustWpHeapModel {
    TrustIrMemory,
    RustBorrowGraph,
    SeparationLogic,
}

/// Loop treatment selected for TrustWp.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustWpLoopStrategy {
    RequireInvariants,
    InferInvariants,
    Havoc,
}

/// Frame condition policy selected for TrustWp.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustWpFramePolicy {
    Minimal,
    BorrowRegions,
    FullHeap,
}

/// Panic handling semantics selected for TrustWp.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrustWpPanicSemantics {
    PanicFreeRequired,
    EncodePanicsAsErrors,
    Unwind,
}

/// TrustWp-specific request semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustWpRequestOptions {
    pub heap_model: TrustWpHeapModel,
    pub loop_strategy: TrustWpLoopStrategy,
    pub frame_policy: TrustWpFramePolicy,
    pub panic_semantics: TrustWpPanicSemantics,
    pub max_abduced_preconditions: u32,
    pub emit_verification_conditions: bool,
}

impl Default for TrustWpRequestOptions {
    fn default() -> Self {
        Self {
            heap_model: TrustWpHeapModel::RustBorrowGraph,
            loop_strategy: TrustWpLoopStrategy::RequireInvariants,
            frame_policy: TrustWpFramePolicy::BorrowRegions,
            panic_semantics: TrustWpPanicSemantics::PanicFreeRequired,
            max_abduced_preconditions: 8,
            emit_verification_conditions: true,
        }
    }
}

/// Native TrustVc request: import or merge proof certificates for obligations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustVcNativeRequest {
    pub id: NativeRequestId,
    pub mode: TrustVcVerificationMode,
    pub obligations: Vec<ProofId>,
    pub certificates: Vec<ProofCertificateRef>,
    pub lineage_roots: Vec<ProofLineageId>,
    #[cfg_attr(feature = "serde", serde(default))]
    pub options: TrustVcRequestOptions,
    #[cfg_attr(feature = "serde", serde(default))]
    pub diagnostics: NativeDiagnosticsPolicy,
    #[cfg_attr(feature = "serde", serde(default))]
    pub provenance: NativeRequestProvenance,
    /// Function these obligations are discharged against.
    ///
    /// Trailing, and `skip_serializing_if`, ON PURPOSE — see the digest note in
    /// `write_native_request_stable`. `None` must stay wire-invisible.
    ///
    /// This crate sets `deny_unknown_fields` nowhere, so an OLD consumer reading
    /// a new bundle silently DROPS this key, recomputes a 4-bytes-shorter digest,
    /// and reports `EvidenceRequestDigestMismatch` rather than a version error.
    /// That is why a producer may only start emitting `Some` after every consumer
    /// has been advanced.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub function: Option<FuncId>,
}

/// Native TrustMc request: run BMC/CHC over a TrustIr function.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustMcNativeRequest {
    pub id: NativeRequestId,
    pub mode: TrustMcVerificationMode,
    pub function: FuncId,
    pub obligations: Vec<ProofId>,
    pub lineage_roots: Vec<ProofLineageId>,
    #[cfg_attr(feature = "serde", serde(default))]
    pub options: TrustMcRequestOptions,
    #[cfg_attr(feature = "serde", serde(default))]
    pub diagnostics: NativeDiagnosticsPolicy,
    #[cfg_attr(feature = "serde", serde(default))]
    pub provenance: NativeRequestProvenance,
}

/// Native TrustWp request: run deductive analysis over a TrustIr function.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustWpNativeRequest {
    pub id: NativeRequestId,
    pub mode: TrustWpVerificationMode,
    pub function: FuncId,
    pub obligations: Vec<ProofId>,
    pub lineage_roots: Vec<ProofLineageId>,
    #[cfg_attr(feature = "serde", serde(default))]
    pub options: TrustWpRequestOptions,
    #[cfg_attr(feature = "serde", serde(default))]
    pub diagnostics: NativeDiagnosticsPolicy,
    #[cfg_attr(feature = "serde", serde(default))]
    pub provenance: NativeRequestProvenance,
}

/// One typed verifier request. Variants intentionally encode the consumer and
/// mode instead of naming an adapter by string.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeVerificationRequest {
    TrustVc(TrustVcNativeRequest),
    TrustMc(TrustMcNativeRequest),
    TrustWp(TrustWpNativeRequest),
}

impl NativeVerificationRequest {
    pub fn id(&self) -> NativeRequestId {
        match self {
            NativeVerificationRequest::TrustVc(request) => request.id,
            NativeVerificationRequest::TrustMc(request) => request.id,
            NativeVerificationRequest::TrustWp(request) => request.id,
        }
    }

    pub fn obligations(&self) -> &[ProofId] {
        match self {
            NativeVerificationRequest::TrustVc(request) => &request.obligations,
            NativeVerificationRequest::TrustMc(request) => &request.obligations,
            NativeVerificationRequest::TrustWp(request) => &request.obligations,
        }
    }

    pub fn lineage_roots(&self) -> &[ProofLineageId] {
        match self {
            NativeVerificationRequest::TrustVc(request) => &request.lineage_roots,
            NativeVerificationRequest::TrustMc(request) => &request.lineage_roots,
            NativeVerificationRequest::TrustWp(request) => &request.lineage_roots,
        }
    }

    pub fn certificates(&self) -> &[ProofCertificateRef] {
        match self {
            NativeVerificationRequest::TrustVc(request) => &request.certificates,
            NativeVerificationRequest::TrustMc(_) | NativeVerificationRequest::TrustWp(_) => &[],
        }
    }

    pub fn function(&self) -> Option<FuncId> {
        match self {
            NativeVerificationRequest::TrustVc(request) => request.function,
            NativeVerificationRequest::TrustMc(request) => Some(request.function),
            NativeVerificationRequest::TrustWp(request) => Some(request.function),
        }
    }

    pub fn diagnostics(&self) -> &NativeDiagnosticsPolicy {
        match self {
            NativeVerificationRequest::TrustVc(request) => &request.diagnostics,
            NativeVerificationRequest::TrustMc(request) => &request.diagnostics,
            NativeVerificationRequest::TrustWp(request) => &request.diagnostics,
        }
    }

    pub fn provenance(&self) -> &NativeRequestProvenance {
        match self {
            NativeVerificationRequest::TrustVc(request) => &request.provenance,
            NativeVerificationRequest::TrustMc(request) => &request.provenance,
            NativeVerificationRequest::TrustWp(request) => &request.provenance,
        }
    }

    pub fn verifier_suite(&self) -> NativeVerifierSuite {
        match self {
            NativeVerificationRequest::TrustVc(_) => NativeVerifierSuite::TrustVc,
            NativeVerificationRequest::TrustMc(_) => NativeVerifierSuite::TrustMc,
            NativeVerificationRequest::TrustWp(_) => NativeVerifierSuite::TrustWp,
        }
    }

    pub fn expected_verifier_identity(&self) -> &NativeToolIdentity {
        self.provenance().expected_verifier()
    }

    pub fn solver_identities(&self) -> &[NativeToolIdentity] {
        self.provenance().solver_identities()
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_native_request_stable(&mut bytes, self);
        ProofDigest::sha256_domain("trust_ir.native.verification.request.v2", &bytes)
    }
}
