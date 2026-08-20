// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

pub mod alloc_bound;
pub mod bridge;
pub mod constant;
pub mod dialect;
pub mod display;
pub mod inst;
pub mod interpret;
pub mod mem2reg;
pub mod node;
pub mod pred;
pub mod proof;
/// Forward, sound, decidable propagation over the [`pred`] lattice.
pub mod propagate;
pub mod request;
pub mod shape;
pub mod spec;
pub mod spec_proof;
pub mod ty;
pub mod value;
#[cfg(feature = "serde")]
pub(crate) mod wide_int_serde;

#[cfg(feature = "fmt")]
pub mod format;

#[cfg(feature = "parser")]
pub mod parser;

#[cfg(feature = "binary")]
pub mod binary;
// Module identity is security-critical even when callers do not request the
// public binary codec API. Compile the one canonical serializer privately so
// `Module::stable_digest` and native-bundle validation never fall back to a
// producer-supplied digest or a redundant encoding.
#[cfg(not(feature = "binary"))]
#[allow(dead_code)]
mod binary;

#[cfg(feature = "diff")]
pub mod diff;

// FUSION (design 2026-06-20): per-obligation-kind `Expr` encoders that the
// lowering site calls to mint the on-node `ProofAnnotation::Goal`. Gated so the
// default zero-dep format build never references clean-kernel.
#[cfg(feature = "clean-expr")]
pub mod clean_expr_lowering;

pub use bridge::{
    ConformanceSubset, SubsetSite, SubsetViolation, TypedValueMetadata, ValueMetadataOrigin,
};
pub use constant::Constant;
pub use dialect::{
    AttrEntry, AttrValue, Dialect, DialectError, DialectInst, DialectRegistry, LoweringPass,
    LoweringResult, RewriteOutcome,
};
pub use inst::{
    AtomicRMWOp, BinOp, CastOp, FCmpOp, ICmpOp, Inst, Ordering, OverflowOp, SwitchCase, UnOp,
};
pub use interpret::{
    InterpretError, InterpretErrorCode, InterpretInt, InterpretOptions, InterpretOutcome,
    InterpretResult, InterpretValue, InterpretValueKind, Interpreter,
};
// Re-export new types added for TrustIr backend requirements (issue #26)
// CallingConv, Linkage, Endianness, TargetInfo are defined below in this file.
pub use node::InstrNode;
#[cfg(feature = "clean-expr")]
pub use proof::ExprObligation;
// The real Clean-kernel `CleanCicRechecker` a kernel-capable orchestrator injects
// into `obligation_has_kernel_rechecked_clean_cic` to close the trusted-on-read
// surface (decode + kernel-re-check the certificate's proof term). Only exists in
// the `clean-expr` build that can run the kernel; kernel-less builds use the
// fail-closed `RejectingCleanCicRechecker`.
#[cfg(feature = "clean-expr")]
pub use clean_expr_lowering::contract::KernelCleanCicRechecker;
pub use proof::{
    CleanCicKernelRecheck, CleanCicProofAuthorityRechecker, CleanCicRechecker, DiagnosticSeverity,
    Divergence, LINEAGE_TRANSFORM_BINDING_SCHEMA, LineageGap, ObligationDiagnostic, ObligationKind,
    ObligationSite, PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES, ProofAnnotation,
    ProofAnnotationFilters, ProofAuthorityRechecker, ProofCertificate, ProofCertificateRef,
    ProofDigest, ProofDigestAlgorithm, ProofEvidence, ProofFormula, ProofLineageError,
    ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofReplayIdentity, ProofStatus,
    ProofSummary, ProofTransform, ProofTransformStage, PublicObligationIdentity,
    RejectingCleanCicRechecker, RejectingProofAuthorityRechecker, clean_cic_lineage_digest,
    is_canonical_public_obligation_id, is_valid_proof_obligation_source_text_id, lineage_closed,
    lineage_closed_with_authority, lineage_transform_binding_digest,
    lineage_transform_binding_formula, obligation_has_kernel_rechecked_clean_cic,
    obligation_has_matching_clean_cic, obligation_has_replayed_authority,
};
// Crate-root re-export of the cross-repo verification-request/bundle schema.
// Gated behind the default-on `request-reexports` feature (audit #55): ON by
// default so external consumers (ty/ay/TrustCg) keep importing
// `trust_ir::NativeVerificationBundle` etc. unchanged; OFF
// (`default-features = false`) de-clutters the crate root so the core IR API is
// not buried under ~330 schema symbols. The schema is always reachable via its
// canonical `trust_ir::request::` path regardless of this feature.
pub use pred::{Pred, PredTable, Space, Universe};
pub use propagate::{assumed_fact, derive_result_fact, integer_value_range};
#[cfg(feature = "request-reexports")]
pub use request::{
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION,
    AY_MODEL_BLOCKING_CLAUSE_SCHEMA, AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA, AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION,
    CHC_X86_HARDWARE_VECTOR_CONTRACT_HARDWARE_MODEL,
    CHC_X86_HARDWARE_VECTOR_CONTRACT_MASK_SEMANTICS, CHC_X86_HARDWARE_VECTOR_CONTRACT_SET_NAME,
    CHC_X86_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE,
    CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY,
    CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY,
    CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_OPERATIONS, CHC_X86_V8_I16_MASK_TO_BITS_COMPOSITION,
    CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS, CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_OPERATIONS, CHC_X86_V16_I8_MASK_TO_BITS_COMPOSITION,
    CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS, HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA,
    HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION, HARDWARE_VECTOR_CONTRACT_REASON_CODES,
    HARDWARE_VECTOR_CONTRACT_SCHEMA, HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION,
    HARDWARE_VECTOR_CONTRACT_STATUS_CODES, HardwareVectorContractDescriptor,
    HardwareVectorContractReason, HardwareVectorContractStatus,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR, NATIVE_BUNDLE_IDENTITY_CONTRACT_DIGEST_CONTEXTS,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS, NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA_VERSION, NATIVE_EVIDENCE_ARTIFACT_ATTACHMENT_SCHEMA,
    NATIVE_EVIDENCE_ARTIFACT_ATTACHMENT_SCHEMA_VERSION,
    NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_REPORT_ROW_KEYS,
    NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_RESOLUTION_ROW_KEYS,
    NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_DESCRIPTOR,
    NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA,
    NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION,
    NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA, NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA_VERSION,
    NATIVE_PUBLIC_OBLIGATION_ID_MAX_BYTES, NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA,
    NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION, NATIVE_SEMANTIC_BRIDGE_SCHEMA,
    NATIVE_SEMANTIC_BRIDGE_SCHEMA_VERSION, NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA,
    NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA_VERSION,
    NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA, NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA_VERSION,
    NATIVE_TRANSPORT_IDENTITY_SCHEMA, NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION,
    NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION, NativeAdapterInput, NativeAdtLayoutFact,
    NativeAssertionId, NativeBundleIdentityContractDescriptor, NativeBundleProducer,
    NativeBundleProvenance, NativeCastFact, NativeCompilerFactId, NativeCompilerFactRef,
    NativeCompilerFacts, NativeDiagnosticLevel, NativeDiagnosticsPolicy, NativeEnumLayoutFact,
    NativeEnumNicheFact, NativeEnumTagEncoding, NativeEnumVariantLayoutFact,
    NativeEvidenceArtifact, NativeEvidenceArtifactAttachment, NativeEvidenceArtifactAttachmentKey,
    NativeEvidenceArtifactAttachmentResolution, NativeEvidenceArtifactAuthority,
    NativeEvidenceArtifactAuthorityRow, NativeEvidenceArtifactAuthorityRowDescriptor,
    NativeEvidenceArtifactAuthorityRowsKind, NativeEvidenceArtifactAuthorityRowsValidationReport,
    NativeEvidenceArtifactKind, NativeEvidenceArtifactResolution,
    NativeEvidenceArtifactResolutionReason, NativeEvidenceArtifactResolutionReport,
    NativeEvidenceArtifactResolutionStatus, NativeEvidenceBundle, NativeEvidenceConsumptionEntry,
    NativeEvidenceConsumptionReport, NativeEvidenceDigestIdentity, NativeFatPointerFact,
    NativeGenericArg, NativeIntegerRange, NativeMonomorphizationFact, NativeMonomorphizationId,
    NativeObligationCause, NativeObligationSource, NativePointerOffsetFact,
    NativePointerOffsetProvenance, NativeReplayAtom, NativeReplayAtomId, NativeReplayAtomKind,
    NativeReplayContext, NativeRequestDigestIdentity, NativeRequestId, NativeRequestProvenance,
    NativeSemanticBridge, NativeSemanticBridgeEvidenceStatus,
    NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripReport,
    NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus,
    NativeSemanticBridgeProofIdentityReplayReport, NativeSemanticBridgeProofIdentityReplayStatus,
    NativeSemanticBridgeReason, NativeSemanticBridgeReport, NativeSemanticBridgeStatus,
    NativeSemanticRelationKind, NativeSerializationPolicy,
    NativeSharedPrimitiveArtifactRequirement, NativeSharedPrimitiveArtifactRole,
    NativeSharedPrimitiveContractDescriptor, NativeSharedPrimitiveContractManifestRow,
    NativeSharedPrimitiveSolverEvidenceDescriptor, NativeSharedPrimitiveVerificationMode,
    NativeSourceLanguage, NativeTargetAbiIdentity, NativeToolIdentity, NativeTransportIdentity,
    NativeTransportIdentityReplayHealthSummaryRoundTripReport,
    NativeTransportIdentityReplayHealthSummaryRoundTripStatus, NativeTransportIdentityReplayReport,
    NativeTransportIdentityReplayStatus, NativeUnknownFieldPolicy, NativeUnsupportedMode,
    NativeUnsupportedModeReason, NativeVerificationBundle, NativeVerificationBundleError,
    NativeVerificationRequest, NativeVerifierSuite,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DOWNSTREAM_CONSUMER_RESPONSIBILITIES,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_MISSING_ROW_KEYS,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_FIXTURE_NAMES,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_HELPER_NAMES,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA_VERSION,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA_VERSION,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_NAMES,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_VALUES,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA_VERSION,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_VALIDATOR_NAMES,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA_VERSION,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION,
    PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA,
    PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_REASON_CODES,
    PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA,
    PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA_VERSION,
    PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_STATUS_CODES,
    PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_REASON_CODES,
    PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_REQUIRED_ARTIFACT_KINDS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA,
    PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA_VERSION,
    PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_STATUS_CODES,
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME,
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR,
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_PROVIDED_FIELDS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA,
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA_VERSION,
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFICATION_MODE,
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFIER_SUITE,
    PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME,
    PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_REASON_CODES,
    PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA,
    PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION,
    PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_STATUS_CODES,
    PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRED_ARTIFACT_KINDS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRES_SOLVER_ACCEPTANCE,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OPTIONAL_ARTIFACT_KINDS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OWNER_SUITE,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_REQUIREMENTS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_REQUIRES_EMITTED_SOLVER_ARTIFACTS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA_VERSION,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_OPTIONAL_ARTIFACT_KINDS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_REASON_CODES,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_REQUIRED_ARTIFACT_KINDS,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA_VERSION,
    PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_STATUS_CODES,
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
    PETRI_SUCCESSOR_TRUST_MC_CHC_SOLVER_EVIDENCE_DESCRIPTOR,
    PetriNativeVerificationBundleHandoffCompletenessReport,
    PetriNativeVerificationBundleHandoffCompletenessStatus,
    PetriNativeVerificationBundleHandoffContractHealthReport,
    PetriNativeVerificationBundleHandoffContractHealthStatus,
    PetriNativeVerificationBundleHandoffDescriptor,
    PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest,
    PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry,
    PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport,
    PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus,
    PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture,
    PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture,
    PetriNativeVerificationBundleHandoffManifestIdentity,
    PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic,
    PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport,
    PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus,
    PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture,
    PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport,
    PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus,
    PetriNativeVerificationBundleHandoffReplayContractSurface,
    PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport,
    PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport,
    PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus,
    PetriNativeVerificationBundleHandoffRequiredRow, PetriNativeVerificationBundleHandoffRow,
    PetriNativeVerificationBundleHandoffRowKind, PetriSuccessorSemanticBridgeProofAdmissionReason,
    PetriSuccessorSemanticBridgeProofAdmissionReport,
    PetriSuccessorSemanticBridgeProofAdmissionStatus, PetriSuccessorTrustMcChcBindingReason,
    PetriSuccessorTrustMcChcBindingReport, PetriSuccessorTrustMcChcBindingStatus,
    PetriSuccessorTrustMcChcContractDescriptor,
    PetriSuccessorTrustMcChcModelValidationReadinessReason,
    PetriSuccessorTrustMcChcModelValidationReadinessReport,
    PetriSuccessorTrustMcChcModelValidationReadinessStatus,
    PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripReport,
    PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus,
    PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport,
    PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus,
    PetriSuccessorTrustMcChcProofHandoffReason, PetriSuccessorTrustMcChcProofHandoffReport,
    PetriSuccessorTrustMcChcProofHandoffStatus, SourceGenerationAuthority,
    SourceGenerationAuthorityMintError, TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION,
    TY_SHARED_PRIMITIVE_MANIFEST, TY_SHARED_PRIMITIVE_MANIFEST_COMPONENT_NAMES,
    TY_SHARED_PRIMITIVE_MANIFEST_REASON_CODES, TY_SHARED_PRIMITIVE_MANIFEST_SCHEMA,
    TY_SHARED_PRIMITIVE_MANIFEST_SCHEMA_VERSION, TY_SHARED_PRIMITIVE_MANIFEST_SOURCE_PACKAGE,
    TY_SHARED_PRIMITIVE_MANIFEST_SOURCE_PACKAGE_VERSION, TY_SHARED_PRIMITIVE_MANIFEST_STATUS_CODES,
    TrustMcArithmeticModel, TrustMcBmcOptions, TrustMcChcEngine, TrustMcChcOptions,
    TrustMcInvariantSource, TrustMcMemoryModel, TrustMcNativeEvidenceBundle, TrustMcNativeRequest,
    TrustMcPdrGeneralization, TrustMcPdrOptions, TrustMcRequestOptions, TrustMcSlicingMode,
    TrustMcVerificationMode, TrustVcMemorySemantics, TrustVcMergeStrategy,
    TrustVcNativeEvidenceBundle, TrustVcNativeRequest, TrustVcRequestOptions,
    TrustVcTrustedEvidencePolicy, TrustVcVerificationMode, TrustWpFramePolicy, TrustWpHeapModel,
    TrustWpLoopStrategy, TrustWpNativeEvidenceBundle, TrustWpNativeRequest, TrustWpPanicSemantics,
    TrustWpRequestOptions, TrustWpVerificationMode, TySharedPrimitiveManifest,
    TySharedPrimitiveManifestReason, TySharedPrimitiveManifestStatus,
    chc_x86_hardware_vector_contract_descriptors, chc_x86_hardware_vector_contract_manifest_digest,
    chc_x86_hardware_vector_contract_manifest_key_value_lines,
    chc_x86_hardware_vector_contract_manifest_key_value_text,
    chc_x86_hardware_vector_contract_manifest_row_count,
    chc_x86_hardware_vector_contract_manifest_rows,
    chc_x86_hardware_vector_contract_manifest_sha256, native_bundle_identity_contract_descriptor,
    native_evidence_artifact_authority_row_descriptor,
    petri_native_verification_bundle_handoff_contract_health_report,
    petri_native_verification_bundle_handoff_descriptor,
    petri_native_verification_bundle_handoff_diagnostic_fixture_manifest,
    petri_native_verification_bundle_handoff_healthy_diagnostic_fixture,
    petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture,
    petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_healthy_fixture,
    petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_stale_fixture,
    petri_native_verification_bundle_handoff_replay_contract_surface,
    petri_successor_trust_mc_chc_contract_descriptor,
    petri_successor_trust_mc_chc_shared_primitive_contract_descriptor,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_digest,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_lines,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_text,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_row_count,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_rows,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_sha256,
    ty_shared_primitive_manifest, ty_shared_primitive_manifest_digest,
    ty_shared_primitive_manifest_key_value_lines, ty_shared_primitive_manifest_key_value_text,
    ty_shared_primitive_manifest_row_count, ty_shared_primitive_manifest_rows,
    ty_shared_primitive_manifest_sha256,
    validate_native_evidence_artifact_authority_key_value_lines,
    validate_native_evidence_artifact_authority_rows,
};
pub use shape::{
    CastLayoutEvidence, CastShape, ConstantShape, DEFAULT_POINTER_BITS, EnumLayoutShape,
    FieldOffsetShape, LayoutError, PointerLayoutShape, PointerMetadataShape, TyLayoutKind,
    TyLayoutShape, TyShape, pointer_sized_unsigned_ty,
};
pub use spec::{
    ProofKind, SpecAnchor, SpecCoverage, SpecEnforcementMode, SpecInvariant, SpecLinkOptions,
    SpecLinkReport, SpecLinkViolation, SpecModule, SpecNonCertificationReason, SpecOrigin,
    SpecProjectionTarget, SpecProof, SpecVar, SpecWaiver, TEMPORAL_FIELD_PATH_PROJECTION_V1,
    link_spec_modules, validate_spec_executable_links, validate_spec_structure,
};
pub use spec_proof::{HarnessEntry, HarnessManifest, HarnessManifestError, link_proofs};
pub use ty::{
    ClosureTy, EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FatPtrKind, FieldDef, FuncTy, RecordDef, SetRepr, StructDef, StructRepr, Ty,
    stable_trait_object_id, stable_vtable_global_name,
};
pub use value::{
    BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, PredId, ProofId, ProofTag, RecordId, ScopeData,
    SourceSpan, StructId, TyId, UnivId, ValueId,
};

/// Calling convention for functions.
///
/// Determines how arguments are passed, registers are allocated, and
/// the stack frame is laid out. TrustIr uses this to emit correct
/// target-specific code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CallingConv {
    /// Default C calling convention (cdecl).
    #[default]
    C,
    /// Fast calling convention -- may use registers aggressively.
    Fast,
    /// Cold calling convention -- optimized for infrequently called paths.
    Cold,
    /// Rust calling convention.
    Rust,
    /// Swift calling convention (self/error return conventions).
    Swift,
}

impl core::fmt::Display for CallingConv {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            CallingConv::C => "ccc",
            CallingConv::Fast => "fastcc",
            CallingConv::Cold => "coldcc",
            CallingConv::Rust => "rustcc",
            CallingConv::Swift => "swiftcc",
        })
    }
}

/// Linkage type for functions and globals.
///
/// Controls symbol visibility and linking behavior. Maps directly
/// to LLVM linkage types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Linkage {
    /// Externally visible (default).
    #[default]
    External,
    /// Only visible within the module.
    Internal,
    /// Like Internal but may be discarded if unused.
    Private,
    /// May be replaced by a stronger definition at link time.
    Weak,
    /// Like Weak but only one copy is kept after linking.
    LinkOnce,
}

impl core::fmt::Display for Linkage {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Linkage::External => "external",
            Linkage::Internal => "internal",
            Linkage::Private => "private",
            Linkage::Weak => "weak",
            Linkage::LinkOnce => "linkonce",
        })
    }
}

/// Per-function producer provenance: which frontend or tool emitted this
/// function (binary v23, Program CK1 contract ladder).
///
/// This is the *format-core* producer vocabulary. It deliberately duplicates
/// (rather than reuses) [`request::facts::NativeBundleProducer`] so the format
/// core does not couple to the verification-request schema's evolution, and so
/// it can carry the `Other(String)` escape a closed cross-repo wire enum
/// cannot. The mapping to `NativeBundleProducer` is:
///
/// | `Producer` | `NativeBundleProducer` | serde name |
/// |------------|------------------------|------------|
/// | `TRust`    | `TRust`                | `"Trust"`  |
/// | `Clean`    | (none — Clean emits modules, not bundles, today) | `"Clean"` |
/// | `TrustIr`  | `TrustIr`              | `"TrustIr"`|
/// | `TSwift`   | `TSwift` (deprecated)  | `"tSwift"` |
/// | `TC`       | `TC` (deprecated)      | `"tC"`     |
/// | `Other(_)` | (none — escape hatch)  | `"Other"`  |
///
/// Like `CallingConv`/`Linkage`, this is claim-style provenance metadata: it
/// has no operational semantics and carries no proof obligation. Its consumers
/// are diagnostics (WS3), the cert cache (WS4), and lineage closure reporting
/// (WS7).
///
/// # Stable wire tags (binary codec, v23)
///
/// `TRust`=0, `Clean`=1, `TrustIr`=2, `TSwift`=3, `TC`=4, `Other`=5 followed
/// by the string payload. These tags are frozen; new producers append.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Producer {
    /// Direct typed Rust/source frontend lowering (THIR-derived, before the
    /// retained MIR-compatibility path) into TrustIr.
    #[cfg_attr(feature = "serde", serde(rename = "Trust"))]
    TRust,
    /// The Clean fused proof language (`clean compile --emit trustir`).
    Clean,
    /// Native TrustIr transform, builder, or verifier pipeline.
    TrustIr,
    /// tSwift frontend. DEPRECATED producer (never shipped) — retained for
    /// wire compatibility only, mirroring `NativeBundleProducer::TSwift`.
    #[cfg_attr(feature = "serde", serde(rename = "tSwift"))]
    TSwift,
    /// tC frontend. DEPRECATED producer (never shipped) — retained for wire
    /// compatibility only, mirroring `NativeBundleProducer::TC`.
    #[cfg_attr(feature = "serde", serde(rename = "tC"))]
    TC,
    /// A producer outside the stable vocabulary. The string is a free-form
    /// tool identifier; it round-trips verbatim through every codec.
    Other(String),
}

impl Producer {
    /// The canonical text-format token for this producer (the `; #producer:`
    /// clause payload). `Other` has no bare token — the text format prints it
    /// as a quoted string — so this returns `None` for it.
    #[must_use]
    pub fn token(&self) -> Option<&'static str> {
        match self {
            Producer::TRust => Some("trust"),
            Producer::Clean => Some("clean"),
            Producer::TrustIr => Some("trust-ir"),
            Producer::TSwift => Some("tswift"),
            Producer::TC => Some("tc"),
            Producer::Other(_) => None,
        }
    }
}

impl core::fmt::Display for Producer {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match (self.token(), self) {
            (Some(tok), _) => f.write_str(tok),
            (None, Producer::Other(s)) => write!(f, "{s:?}"),
            (None, _) => unreachable!("every non-Other producer has a token"),
        }
    }
}

/// serde skip predicate for "skip if false". Used by `ParamAttrs`/`FuncAttrs`;
/// the repo otherwise only has `Option::is_none`/`Vec::is_empty` predicates.
#[cfg(feature = "serde")]
fn is_false(b: &bool) -> bool {
    !*b
}

/// Per-parameter optimization attributes (claim-style; TrustCg-facing hints).
///
/// These mirror LLVM parameter attributes. They are NOT proof-carrying: like
/// `CallingConv`/`Linkage` they are assertions a frontend makes that the backend
/// may exploit. A `Default` (all-`false`/`None`) `ParamAttrs` is the conservative
/// "no information" state and is what every legacy module deserializes to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParamAttrs {
    // R3 #6: the canonical Module MessagePack codec (`rmp_serde::to_vec`) serializes
    // structs POSITIONALLY (as arrays) and may only skip a TRAILING field — a skipped
    // NON-LAST field shifts every later field into the wrong slot (e.g. `nonnull:true`
    // with `dereferenceable:None` skipped failed to decode: the bool landed in
    // `dereferenceable`'s u64 slot). So every non-last field must ALWAYS be emitted;
    // only the trailing `sret` may skip. (`readonly` skipped while it was the trailing
    // field; the abi-pinning `byval`/`sret` additions moved the skip to `sret`.)
    // `default` preserves backward-compatible decode of shorter legacy arrays.
    /// Pointer is dereferenceable for at least N bytes (LLVM `dereferenceable`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub dereferenceable: Option<u64>,
    /// Pointer is never null (LLVM `nonnull`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub nonnull: bool,
    /// Pointer is aligned to N bytes (LLVM `align`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub align: Option<u64>,
    /// Pointer does not alias other arguments (LLVM `noalias`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub noalias: bool,
    /// Pointee is not written through this parameter (LLVM `readonly`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub readonly: bool,
    /// Pointer parameter is an aggregate passed BY VALUE through memory: the
    /// caller makes a hidden copy and passes its address (LLVM `byval`).
    ///
    /// ABI pinning (abi-pinning.md): together with `sret` this is the
    /// by-value-vs-by-reference classification of aggregate passing at a call
    /// edge, so two frontends state — rather than independently invent — how a
    /// memory-classed struct crosses an FFI boundary. Unlike the hint-style
    /// attributes above, disagreement here changes the call's byte-level ABI.
    /// Binary codec: v20, flag bit 3; pre-v20 blobs decode to `false`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub byval: bool,
    /// Pointer parameter is the caller-allocated slot for an aggregate RETURNED
    /// through memory (LLVM `sret`): the callee writes the return value there
    /// instead of returning it in registers.
    ///
    /// ABI pinning: the return-position half of the `byval` classification.
    /// Binary codec: v20, flag bit 4; pre-v20 blobs decode to `false`.
    /// Trailing field — the only one that may `skip_serializing_if` (positional
    /// MessagePack, R3 #6 above).
    #[cfg_attr(feature = "serde", serde(default, skip_serializing_if = "is_false"))]
    pub sret: bool,
}

impl ParamAttrs {
    /// True when no attribute is set (the legacy/empty state). Used by the
    /// binary codec to skip writing empty per-parameter records.
    pub fn is_empty(&self) -> bool {
        self.dereferenceable.is_none()
            && !self.nonnull
            && self.align.is_none()
            && !self.noalias
            && !self.readonly
            && !self.byval
            && !self.sret
    }
}

/// Function-level optimization attributes (claim-style; TrustCg-facing hints).
///
/// `readonly`/`readnone` describe memory effects; `inlinehint`/`cold` are
/// codegen hints. Like `ParamAttrs`, these are claims, not proofs. `params` is
/// positional and may be shorter than the function's parameter list — a missing
/// entry means `ParamAttrs::default()` for that parameter.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FuncAttrs {
    // R3 #7: positional MessagePack (`rmp_serde::to_vec`) may only skip a TRAILING
    // field — skipping a non-last `is_false` bool shifted a later set bool into the
    // wrong slot (e.g. readonly=false/readnone=true silently round-tripped back as
    // readonly=true/readnone=false). Always emit every non-last field; only the
    // trailing `params` may skip. `default` keeps backward-compatible decode of
    // shorter legacy arrays.
    /// Does not write memory (LLVM `readonly` on a function).
    #[cfg_attr(feature = "serde", serde(default))]
    pub readonly: bool,
    /// Reads no memory and writes no memory (LLVM `readnone`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub readnone: bool,
    /// Prefer inlining (LLVM `inlinehint`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub inlinehint: bool,
    /// Rarely executed; deprioritize (LLVM `cold`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub cold: bool,
    /// Per-parameter attributes, positional. May be empty or shorter than the
    /// parameter list; missing entries default to `ParamAttrs::default()`.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub params: Vec<ParamAttrs>,
}

impl FuncAttrs {
    /// True when no function- or parameter-level attribute is set.
    pub fn is_empty(&self) -> bool {
        !self.readonly
            && !self.readnone
            && !self.inlinehint
            && !self.cold
            && self.params.iter().all(ParamAttrs::is_empty)
    }
}

/// Thread-local storage model for globals.
///
/// This is target-neutral metadata. A missing model on [`Global`] means the
/// global is an ordinary non-TLS symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TlsModel {
    LocalExec,
    InitialExec,
    GeneralDynamic,
    LocalDynamic,
}

impl core::fmt::Display for TlsModel {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            TlsModel::LocalExec => "local_exec",
            TlsModel::InitialExec => "initial_exec",
            TlsModel::GeneralDynamic => "general_dynamic",
            TlsModel::LocalDynamic => "local_dynamic",
        })
    }
}

/// Byte order of the target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Endianness {
    Little,
    Big,
}

impl core::fmt::Display for Endianness {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Endianness::Little => "little",
            Endianness::Big => "big",
        })
    }
}

/// Module-wide policy for how by-value aggregates cross call edges.
///
/// ABI pinning (docs/roadmap/abi-pinning.md): this is the *contract* half of
/// aggregate passing — the classification scheme every frontend that
/// contributes to a link agreed to. trust-cg owns the *realization* (the
/// actual register moves and stack slots for the pinned target).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StructPassingPolicy {
    /// The pinned target's native C ABI classification rules decide register
    /// vs memory placement per aggregate (SysV x86-64, AAPCS64, ...). A
    /// producer marks the memory-classed parameters/returns `byval`/`sret`
    /// ([`ParamAttrs`]) per those rules.
    #[default]
    NativeC,
    /// Every by-value aggregate crosses call edges through memory — a `byval`
    /// pointer parameter or an `sret` return slot — regardless of size. The
    /// conservative scheme that needs no per-target classification table.
    AlwaysMemory,
    /// The producer performs NO aggregate classification, and says so.
    ///
    /// Both schemes above are CLAIMS: each requires the producer to mark memory-classed
    /// parameters and returns `byval`/`sret` ([`ParamAttrs`]). A producer that emits no
    /// `ParamAttrs` satisfies neither, so stamping either asserts a contract the module does not
    /// carry — and since `struct_passing` feeds `Module::stable_digest`, that false claim travels
    /// in the module's identity too.
    ///
    /// This lets such a producer pin the parts of `TargetInfo` that ARE facts about the target
    /// (`triple`, `pointer_size`, `endianness`) while stating honestly that aggregate passing is
    /// unclassified. A CONSUMER MUST NOT infer either scheme from it — it is a declaration of
    /// absence, not a third convention. A backend needing a classification must refuse the module
    /// rather than pick one.
    ///
    /// Binary codec: tag 2, VERSION 36 (additive; a pre-v36 reader rejects the blob on the
    /// version gate before reaching this byte, so MIN_READ_VERSION is unchanged).
    Unclassified,
}

impl core::fmt::Display for StructPassingPolicy {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            StructPassingPolicy::NativeC => "native_c",
            StructPassingPolicy::AlwaysMemory => "always_memory",
            StructPassingPolicy::Unclassified => "unclassified",
        })
    }
}

/// Target machine information for code generation.
///
/// TrustIr uses this to configure its backend: register allocation,
/// instruction selection, data layout, and ABI conformance.
// Positional-MessagePack note (R3 #6 precedent): no field here uses
// `skip_serializing_if` — every field is always emitted, so the positional
// array shape is fixed. The two v20 fields are trailing additions with
// serde(default), so shorter pre-v20 arrays (and JSON without the keys) still
// decode.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TargetInfo {
    /// Target triple string (e.g. "aarch64-apple-darwin", "x86_64-unknown-linux-gnu").
    pub triple: String,
    /// Pointer size in bytes (typically 4 or 8).
    pub pointer_size: u32,
    /// Byte order.
    pub endianness: Endianness,
    /// Stable ABI identifier beyond the triple string (e.g. "aapcs64",
    /// "sysv64", "win64"). Two modules with the same `abi` assert they were
    /// produced against the same calling-convention/layout ruleset even if
    /// their triples differ in vendor/OS spelling; `None` means "derived from
    /// the triple" (the legacy state). Binary codec: v20; serde-`default`.
    ///
    /// Because `target_info` is serialized, this flows into
    /// [`Module::stable_digest`] automatically.
    #[cfg_attr(feature = "serde", serde(default))]
    pub abi: Option<String>,
    /// How by-value aggregates cross call edges ([`StructPassingPolicy`]).
    /// Binary codec: v20; serde-`default` (`NativeC`). Also digest-bearing,
    /// like `abi`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub struct_passing: StructPassingPolicy,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Module {
    pub name: String,
    pub functions: Vec<Function>,
    pub structs: Vec<StructDef>,
    pub enums: Vec<EnumDef>,
    /// Named-field record definitions (ty-style labeled tuples, no layout).
    /// Referenced from `Ty::Record(RecordId)`. See `RecordDef` in `ty`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub records: Vec<RecordDef>,
    /// Closure type definitions (function signature + typed captures).
    /// Referenced from `Ty::Closure(ClosureTyId)`. See `ClosureTy` in `ty`.
    /// The ty#4145 soundness lesson (stale cached closure body) lives here:
    /// captures are part of the type identity, not an opaque env pointer.
    #[cfg_attr(feature = "serde", serde(default))]
    pub closure_types: Vec<ClosureTy>,
    pub globals: Vec<Global>,
    pub func_types: Vec<FuncTy>,
    pub types: Vec<Ty>,
    pub proof_obligations: Vec<ProofObligation>,
    pub proof_certificates: Vec<ProofCertificate>,
    /// Target machine information. None means target-independent IR.
    pub target_info: Option<TargetInfo>,
    /// Debug-info source-file table. `SourceSpan::file` is an index into this
    /// vector; an empty table means spans carry only line/col (no file). The
    /// table makes `SourceSpan` usable end-to-end — without it a span's `file`
    /// field is a dangling integer. Populate via [`Module::intern_file`].
    #[cfg_attr(feature = "serde", serde(default))]
    pub files: Vec<String>,
    /// Verifier diagnostics keyed by obligation id (a failed/annotated proof
    /// obligation's actionable payload). A module-level sidecar so attaching
    /// diagnostics does not change the `ProofObligation` wire shape. Each entry
    /// must reference an obligation present in `proof_obligations`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub obligation_diagnostics: Vec<ObligationDiagnostic>,
    /// Spec ↔ source cross-reference objects (Phase 3). Each entry is a lowered
    /// state-machine model with its bidirectional anchors; the `spec-link` pass
    /// ([`crate::spec::link_spec_modules`]) enforces the closure obligations over
    /// these. Default-empty for legacy modules; the binary codec gates it on the
    /// format version so pre-spec blobs deserialize to an empty vector.
    // R3 #5 (the positional-serde rule, same as `ProofFormula::smtlib` and
    // `ProofObligation::formula`): the canonical MessagePack codec
    // (`rmp_serde::to_vec`) serializes structs POSITIONALLY and may only skip a
    // TRAILING field — a skipped non-last field shifts every later field into
    // the wrong slot. `spec_modules` was the trailing skippable field until
    // v30; appending `universes`/`predicates` after it FLIPS IT TO
    // ALWAYS-EMITTED in the same change, exactly as `source` (v28) and
    // `producer` (v23) landed. `default` preserves backward-compatible decode
    // of shorter legacy arrays.
    #[cfg_attr(feature = "serde", serde(default))]
    pub spec_modules: Vec<SpecModule>,
    /// **Content-interned** finite universes (v30), referenced from
    /// `Pred::InUniverse(UnivId, Space)`. Identity is the extension and
    /// nothing else — no name, no provenance — for the same reason
    /// [`Module::predicates`] is interned. Mint entries through
    /// [`Module::intern_universe`], never `push`.
    ///
    /// Not the trailing field, so it is ALWAYS emitted (see the note above).
    #[cfg_attr(feature = "serde", serde(default))]
    pub universes: Vec<Universe>,
    /// **Content-interned** refinement predicates (v30), referenced from
    /// `Ty::Refine(_, PredId)`. See [`crate::pred`] for the lattice.
    ///
    /// The interning is load-bearing, not an optimization: two predicates with
    /// the same content are the SAME `PredId` no matter which proof cited
    /// them, which is what makes a control-flow join over two carriers of the
    /// same universe merge instead of dropping the shape and reverting the
    /// value to its raw encoding convention. Mint entries through
    /// [`Module::intern_pred`] (never `push`) and the invariant holds by
    /// construction; `validate_module` re-derives it structurally so a decoded
    /// or hand-built module cannot smuggle in the un-interned shape.
    ///
    /// Append-only, so a child id inside a `Conj`/`Disj` is always strictly
    /// less than its parent's — the predicate graph is acyclic by
    /// construction.
    ///
    /// The SOLE trailing conditionally-skipped field (see the note above).
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub predicates: Vec<Pred>,
}

impl Module {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            functions: Vec::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            records: Vec::new(),
            closure_types: Vec::new(),
            globals: Vec::new(),
            func_types: Vec::new(),
            types: Vec::new(),
            proof_obligations: Vec::new(),
            proof_certificates: Vec::new(),
            target_info: None,
            files: Vec::new(),
            obligation_diagnostics: Vec::new(),
            spec_modules: Vec::new(),
            universes: Vec::new(),
            predicates: Vec::new(),
        }
    }

    /// Interns a debug-info source-file path, returning its index for use in
    /// [`SourceSpan::file`]. Idempotent: a path already in the table returns
    /// its existing index rather than appending a duplicate.
    pub fn intern_file(&mut self, path: impl Into<String>) -> u32 {
        let path = path.into();
        if let Some(i) = self.files.iter().position(|p| *p == path) {
            return i as u32;
        }
        let idx = u32::try_from(self.files.len()).expect("file table exceeds u32 id space");
        self.files.push(path);
        idx
    }

    /// Returns the source-file path for a [`SourceSpan::file`] index, if the
    /// table has an entry for it.
    pub fn file_name(&self, index: u32) -> Option<&str> {
        self.files.get(index as usize).map(String::as_str)
    }

    /// Resolves a [`SourceSpan`] against the file table to a
    /// `(path, line, col)` triple, or `None` when `span.file` has no table
    /// entry (a dangling index or an empty table).
    pub fn resolve_span(&self, span: &SourceSpan) -> Option<(&str, u32, u32)> {
        self.file_name(span.file)
            .map(|path| (path, span.line, span.col))
    }

    /// Resolve the exact public/source identity for `obligation`.
    ///
    /// Canonical producers store proof id `N` at index `N`; the fallback
    /// preserves correctness for sparse or externally assigned ids.
    pub fn proof_obligation_source(
        &self,
        obligation: ProofId,
    ) -> Option<&ProofObligationSourceIdentity> {
        self.proof_obligations
            .get(obligation.as_usize())
            .filter(|candidate| candidate.id == obligation)
            .or_else(|| {
                self.proof_obligations
                    .iter()
                    .find(|candidate| candidate.id == obligation)
            })
            .and_then(|candidate| candidate.source.as_ref())
    }

    /// Renders an [`ObligationDiagnostic`] as a compiler-style one-liner:
    /// `path:line:col: severity: message [detail]`. The location prefix is
    /// present only when the diagnostic's span resolves via
    /// [`resolve_span`](Self::resolve_span); the bracketed detail only when
    /// the diagnostic carries one.
    pub fn render_diagnostic(&self, diagnostic: &ObligationDiagnostic) -> String {
        use core::fmt::Write;
        let mut out = String::new();
        if let Some((path, line, col)) = diagnostic
            .location
            .as_ref()
            .and_then(|span| self.resolve_span(span))
        {
            // Infallible: fmt::Write on String never errors.
            let _ = write!(out, "{path}:{line}:{col}: ");
        }
        let _ = write!(out, "{}: {}", diagnostic.severity, diagnostic.message);
        if let Some(detail) = &diagnostic.detail {
            let _ = write!(out, " [{detail}]");
        }
        out
    }

    /// ABI pinning: description of the first FFI boundary in this module, or
    /// `None` when the module has none.
    ///
    /// An *FFI boundary* is either
    /// 1. a **bodyless `external` declaration** — an import resolved against a
    ///    separately compiled object at link time (a contract-only declaration
    ///    with a [`FunctionSummary`] included: the summary aids verification,
    ///    but the symbol still crosses an object boundary), or
    /// 2. a **call edge whose calling convention differs from the enclosing
    ///    function's** — a direct `Call` to a callee with a different
    ///    `Function::calling_conv`, or a `CallIndirect` declaring a different
    ///    edge convention.
    ///
    /// Either way, two independently produced objects must agree byte-for-byte
    /// on the ABI, which is only well-defined against a pinned target. This is
    /// the predicate behind [`Module::requires_target_info`]; the returned
    /// description feeds the validator's `TargetInfoRequired` diagnostic.
    pub fn first_ffi_boundary(&self) -> Option<String> {
        for func in &self.functions {
            // Trust (#180): a bodyless external declaration is an FFI boundary only when its
            // calling convention is FOREIGN. "No body here, linked externally" is equally true of
            // an ordinary Rust CROSS-CRATE call, and a target must be pinned for byte-level ABI
            // agreement between SEPARATELY COMPILED objects — which Rust-to-Rust under one
            // compiler already has by construction. Same conflation the repr(Rust) check had.
            if func.blocks.is_empty()
                && matches!(func.linkage, Linkage::External)
                && func.calling_conv != CallingConv::Rust
            {
                return Some(format!("bodyless external declaration `{}`", func.name));
            }
        }
        for func in &self.functions {
            for block in &func.blocks {
                for node in &block.body {
                    match &node.inst {
                        crate::inst::Inst::Call { callee, .. } => {
                            // A direct call's edge convention IS the callee's
                            // `calling_conv` (see `Inst::Call` docs); a dangling
                            // callee id is flagged by the validator, not here.
                            if let Some(callee_func) =
                                self.functions.iter().find(|f| f.id == *callee)
                                && callee_func.calling_conv != func.calling_conv
                            {
                                return Some(format!(
                                    "cross-convention call edge `{}` ({}) -> `{}` ({})",
                                    func.name,
                                    func.calling_conv,
                                    callee_func.name,
                                    callee_func.calling_conv
                                ));
                            }
                        }
                        // Invoke is a direct call with an unwind edge: its
                        // edge convention is the callee's, same as Call.
                        crate::inst::Inst::Invoke { callee, .. } => {
                            if let Some(callee_func) =
                                self.functions.iter().find(|f| f.id == *callee)
                                && callee_func.calling_conv != func.calling_conv
                            {
                                return Some(format!(
                                    "cross-convention invoke edge `{}` ({}) -> `{}` ({})",
                                    func.name,
                                    func.calling_conv,
                                    callee_func.name,
                                    callee_func.calling_conv
                                ));
                            }
                        }
                        crate::inst::Inst::CallIndirect { calling_conv, .. }
                            if *calling_conv != func.calling_conv =>
                        {
                            return Some(format!(
                                "cross-convention indirect call edge in `{}` ({}) declaring {}",
                                func.name, func.calling_conv, calling_conv
                            ));
                        }
                        _ => {}
                    }
                }
            }
        }
        None
    }

    /// ABI pinning: true when this module contains an FFI boundary (see
    /// [`Module::first_ffi_boundary`]) and therefore MUST carry a
    /// [`TargetInfo`]. `validate_module` (trust-ir-build) rejects a module for
    /// which this returns `true` while `target_info` is `None`; modules without
    /// FFI boundaries may stay target-independent (`target_info: None`).
    pub fn requires_target_info(&self) -> bool {
        self.first_ffi_boundary().is_some()
    }

    pub fn add_func_type(&mut self, ft: FuncTy) -> FuncTyId {
        let id = FuncTyId::new(
            u32::try_from(self.func_types.len()).expect("func-type table exceeds u32 id space"),
        );
        self.func_types.push(ft);
        id
    }

    /// Raw registration: push `sd` and return its declared id, verbatim.
    ///
    /// This legacy constructor performs NO dedup and NO id-collision check —
    /// reconstruction paths (codecs) and callers that manage their own id
    /// space rely on that verbatim behavior. New producer code should prefer
    /// [`Module::add_struct_def`], which dedups structurally-identical defs
    /// and never lets two defs share an id.
    pub fn add_struct(&mut self, sd: StructDef) -> StructId {
        let id = sd.id;
        self.structs.push(sd);
        id
    }

    /// Raw registration: push `ed` and return its declared id, verbatim.
    ///
    /// Legacy counterpart of [`Module::add_enum_def`] — no dedup, no
    /// id-collision check. See [`Module::add_struct`] for when that is the
    /// right tool.
    pub fn add_enum(&mut self, ed: EnumDef) -> EnumId {
        let id = ed.id;
        self.enums.push(ed);
        id
    }

    /// Allocate the next free `StructId`: one past the highest id currently
    /// in the struct table (0 for an empty table), so it can never collide
    /// with an existing def.
    ///
    /// Intended for recursive/forward-referencing definitions, where the id
    /// must exist *before* the fields that mention `Ty::Struct(id)` can be
    /// built. Reserve-by-insert: register a def under the allocated id (e.g.
    /// via [`Module::add_struct_def`]) before allocating another, or the next
    /// call returns the same id.
    pub fn allocate_struct_id(&self) -> StructId {
        StructId::new(
            self.structs
                .iter()
                .map(|sd| {
                    sd.id
                        .index()
                        .checked_add(1)
                        .expect("struct table exceeds u32 id space")
                })
                .max()
                .unwrap_or(0),
        )
    }

    /// Allocate the next free `EnumId` — the enum-table counterpart of
    /// [`Module::allocate_struct_id`], with the same reserve-by-insert
    /// contract.
    pub fn allocate_enum_id(&self) -> EnumId {
        EnumId::new(
            self.enums
                .iter()
                .map(|ed| {
                    ed.id
                        .index()
                        .checked_add(1)
                        .expect("enum table exceeds u32 id space")
                })
                .max()
                .unwrap_or(0),
        )
    }

    /// Register a struct definition with **mandatory dedup** and a collision-
    /// free id guarantee (roadmap §1.2). Callers must use the *returned* id:
    ///
    /// 1. If the table already holds a def structurally identical to `sd`
    ///    (equal in everything but `id`), nothing is inserted and the existing
    ///    def's id is returned.
    /// 2. Otherwise, if `sd.id` is unused, `sd` is inserted verbatim.
    /// 3. Otherwise (`sd.id` names a *different* existing def), `sd` is
    ///    inserted under a freshly allocated id — two defs can never share an
    ///    id through this constructor.
    pub fn add_struct_def(&mut self, sd: StructDef) -> StructId {
        if let Some(existing) = self
            .structs
            .iter()
            .find(|other| struct_def_structurally_eq(other, &sd))
        {
            return existing.id;
        }
        let id = if self.structs.iter().any(|other| other.id == sd.id) {
            self.allocate_struct_id()
        } else {
            sd.id
        };
        self.structs.push(StructDef { id, ..sd });
        id
    }

    /// Register an enum definition with **mandatory dedup** and a collision-
    /// free id guarantee — the enum-table counterpart of
    /// [`Module::add_struct_def`] (same three-step contract; callers must use
    /// the returned id).
    pub fn add_enum_def(&mut self, ed: EnumDef) -> EnumId {
        if let Some(existing) = self
            .enums
            .iter()
            .find(|other| enum_def_structurally_eq(other, &ed))
        {
            return existing.id;
        }
        let id = if self.enums.iter().any(|other| other.id == ed.id) {
            self.allocate_enum_id()
        } else {
            ed.id
        };
        self.enums.push(EnumDef { id, ..ed });
        id
    }

    /// Register a record definition in the module's record table.
    /// Returns the `RecordId` (taken from `rd.id`) so callers can reference
    /// the record via `Ty::Record(id)`.
    pub fn add_record(&mut self, rd: RecordDef) -> RecordId {
        let id = rd.id;
        self.records.push(rd);
        id
    }

    /// Register a closure type in the module's closure-type table and return
    /// its positional `ClosureTyId`. Callers reference the result via
    /// `Ty::Closure(id)`.
    pub fn add_closure_type(&mut self, ct: ClosureTy) -> ClosureTyId {
        let id = ClosureTyId::new(
            u32::try_from(self.closure_types.len())
                .expect("closure-type table exceeds u32 id space"),
        );
        self.closure_types.push(ct);
        id
    }

    pub fn add_type(&mut self, ty: Ty) -> TyId {
        let id =
            TyId::new(u32::try_from(self.types.len()).expect("type table exceeds u32 id space"));
        self.types.push(ty);
        id
    }

    // ── The typed value model: interned predicate / universe tables ────────
    //
    // These are the ONLY sanctioned way to mint a `PredId`/`UnivId`. They
    // intern by CONTENT, which is not a size optimization: it is the
    // structural fix for the join-drop miscompile class. Two carriers over the
    // same universe, minted independently by two different proofs, come back
    // with the SAME id, so a control-flow join merges them instead of dropping
    // the shape and reverting the value to the raw encoding convention.
    //
    // Interning is append-only, so a `Conj`/`Disj` child id is always strictly
    // less than its parent's and the predicate graph is acyclic by
    // construction. `validate_module` re-derives both properties structurally
    // rather than trusting that a module came through here.

    /// Interns a [`Universe`] by CONTENT, returning its id. Idempotent: the
    /// same extension always returns the same [`UnivId`].
    ///
    /// The universe is canonicalized on the way in (member lists are sorted
    /// and deduplicated), so `{3, 1, 2}` and `{1, 2, 3}` are the same id.
    /// Returns `None` for a non-canonicalizable universe (empty, over
    /// [`pred::MAX_ENUMERATED_MEMBERS`], or containing a constant with no
    /// total order such as a float) — a fail-closed refusal, never a silent
    /// widening.
    pub fn intern_universe(&mut self, universe: Universe) -> Option<UnivId> {
        let canonical = match universe {
            Universe::IntRange { lo, hi } => Universe::range(lo, hi)?,
            Universe::Members(items) => Universe::members(items)?,
        };
        if let Some(i) = self.universes.iter().position(|u| *u == canonical) {
            return Some(UnivId::new(u32::try_from(i).expect("checked on insert")));
        }
        let id = UnivId::new(
            u32::try_from(self.universes.len()).expect("universe table exceeds u32 id space"),
        );
        self.universes.push(canonical);
        Some(id)
    }

    /// Interns a [`Pred`] by CONTENT, returning its id. Idempotent.
    ///
    /// Canonicalizes on the way in: finite-set extensions are sorted and
    /// deduped, and `Conj`/`Disj` child lists are sorted and deduped (a
    /// single-child connective collapses to that child, matching the lattice's
    /// one-spelling-per-construct rule). Returns `None` when the predicate
    /// cannot be made canonical, or when it references an id this module does
    /// not have — a dangling `PredId`/`UnivId` is refused at the door rather
    /// than deferred to the validator.
    pub fn intern_pred(&mut self, pred: Pred) -> Option<PredId> {
        let canonical = match pred {
            Pred::Interval { lo, hi } => Pred::interval(lo, hi)?,
            Pred::FiniteSet(items) => Pred::finite_set(items)?,
            Pred::InUniverse(u, space) => {
                if u.as_usize() >= self.universes.len() {
                    return None;
                }
                Pred::InUniverse(u, space)
            }
            Pred::Conj(children) => self.canonical_connective(children, true)?,
            Pred::Disj(children) => self.canonical_connective(children, false)?,
            other @ (Pred::NonZero | Pred::NonNull | Pred::Top | Pred::Bottom) => other,
        };
        if let Some(i) = self.predicates.iter().position(|p| *p == canonical) {
            return Some(PredId::new(u32::try_from(i).expect("checked on insert")));
        }
        let id = PredId::new(
            u32::try_from(self.predicates.len()).expect("predicate table exceeds u32 id space"),
        );
        self.predicates.push(canonical);
        Some(id)
    }

    fn canonical_connective(&self, children: Vec<PredId>, conj: bool) -> Option<Pred> {
        let mut children = children;
        if children
            .iter()
            .any(|c| c.as_usize() >= self.predicates.len())
        {
            return None;
        }
        children.sort_unstable();
        children.dedup();
        match children.len() {
            0 => None,
            // A one-element connective IS its child; collapsing keeps one
            // spelling per construct so interning stays a true identity.
            1 => self.predicates.get(children[0].as_usize()).cloned(),
            n if n <= pred::MAX_CONNECTIVE_ARITY => Some(if conj {
                Pred::Conj(children)
            } else {
                Pred::Disj(children)
            }),
            _ => None,
        }
    }

    /// Convenience: intern `Pred::InUniverse(universe, space)` in one step.
    pub fn intern_in_universe(&mut self, universe: Universe, space: Space) -> Option<PredId> {
        let u = self.intern_universe(universe)?;
        self.intern_pred(Pred::InUniverse(u, space))
    }

    /// A read-only view of the predicate + universe tables, carrying the
    /// decision procedures ([`PredTable::implies`], [`PredTable::join_pred`],
    /// [`PredTable::describe`]).
    pub fn pred_table(&self) -> PredTable<'_> {
        PredTable::new(&self.predicates, &self.universes)
    }

    /// Does `actual` entail `required`? Both are optional because **an absent
    /// predicate is [`Pred::Top`]** — the "no information" element — not a
    /// waiver.
    ///
    /// This is the consumption rule in one function: a value carrying no
    /// refinement can satisfy only a site that requires nothing.
    pub fn pred_implies(&self, actual: Option<PredId>, required: Option<PredId>) -> bool {
        let table = self.pred_table();
        match (actual, required) {
            // Nothing required: anything (including a lost fact) is fine.
            (_, None) => true,
            // A fact required, none carried: TOP entails nothing non-trivial.
            (None, Some(req)) => matches!(table.pred(req), Some(Pred::Top)),
            (Some(act), Some(req)) => table.implies(act, req),
        }
    }

    /// The **join** of two facts meeting at a control-flow join, interned.
    ///
    /// Join is disjunction and every fallback is toward [`Pred::Top`]: a merge
    /// may only lose information, and a lost fact then FAILS at its
    /// consumption site instead of silently reverting to the raw convention.
    /// An absent side is `Top`, so joining a refined carrier with an unrefined
    /// one yields `Top` — exactly the WP-28 mechanism, made loud.
    pub fn join_preds(&mut self, a: Option<PredId>, b: Option<PredId>) -> PredId {
        let joined = match (a, b) {
            (Some(a), Some(b)) => self.pred_table().join_pred(a, b),
            // One side carries no fact: the merge carries no fact.
            _ => Pred::Top,
        };
        self.intern_pred(joined)
            .expect("join_pred yields a canonical, in-range node")
    }

    /// The `RefinementType` obligations in this module that cite `pred`
    /// through the existing [`ProofFormula`] channel
    /// (`schema == pred::PRED_FORMULA_SCHEMA`, `payload == "pred.N"`).
    ///
    /// Reuse, not rebuild: `ObligationKind::RefinementType` already exists and
    /// is already a contract kind, so it is the only replayable-authority path
    /// there is. The consumption half was never the gap — the CARRIER was. A
    /// predicate may be cited by SEVERAL obligations (that is the WP-28 shape:
    /// two proofs, one universe) and the citation multiplicity has no effect
    /// on the predicate's identity, which is content and content only.
    pub fn refinement_obligations_for(&self, pred: PredId) -> Vec<&ProofObligation> {
        let citation = format!("pred.{}", pred.index());
        self.proof_obligations
            .iter()
            .filter(|o| {
                matches!(o.kind, crate::proof::ObligationKind::RefinementType)
                    && o.formula.as_ref().is_some_and(|f| {
                        f.schema == pred::PRED_FORMULA_SCHEMA && f.payload == citation
                    })
            })
            .collect()
    }

    /// Does some `RefinementType` obligation citing `pred` carry REPLAYED
    /// KERNEL AUTHORITY, as judged by the shared
    /// [`crate::proof::obligation_has_replayed_authority`] gate?
    ///
    /// This is the admission question a consumer asks before acting on a
    /// refinement as a PROVEN fact (e.g. eliding a guard). It is deliberately
    /// separate from validation: `validate_module` enforces the consumption
    /// rule STRUCTURALLY — the lattice is decidable, so no authority is needed
    /// to know that `top` does not imply a membership convention — while this
    /// answers the different question of whether the fact has been *proven*
    /// rather than merely *declared*. A `Discharged`-on-faith obligation is not
    /// authority; the shared gate already encodes that.
    pub fn refinement_has_replayed_authority(
        &self,
        pred: PredId,
        rechecker: &dyn crate::proof::ProofAuthorityRechecker,
    ) -> bool {
        self.refinement_obligations_for(pred).into_iter().any(|o| {
            crate::proof::obligation_has_replayed_authority(o, &self.proof_certificates, rechecker)
        })
    }

    /// Resolve a type through any refinement layer to its representation type.
    ///
    /// `Refine(b, p)` has EXACTLY the representation of `b`, so every
    /// layout/width/codegen question must be asked of the result of this
    /// function, never of the `Refine` spelling itself.
    pub fn representation_ty<'a>(&'a self, ty: &'a Ty) -> Option<&'a Ty> {
        match ty {
            Ty::Refine(base, _) => self.types.get(base.as_usize()),
            other => Some(other),
        }
    }

    /// Register a function in the module, synthesizing proof-obligation table
    /// entries from its function-level [`ProofAnnotation`]s (roadmap §1.1).
    ///
    /// Synthesis is **unconditional in this constructor** — a module built
    /// through `add_function` never carries a claim-bearing function with a
    /// half-populated obligation table. For each annotation whose
    /// [`ProofAnnotation::obligation_kind`] is `Some(kind)`, one `Pending`
    /// obligation scoped to this function (`function == Some(f.id)`, B4) is
    /// appended, deduplicated two ways:
    ///
    /// * within the call — multiple claims mapping to the same kind (e.g.
    ///   `NoOverflow` + `DivNonZero` → `ArithmeticSafety`) yield ONE entry
    ///   whose description names every originating claim;
    /// * against the table — if the module already carries an obligation of
    ///   that kind scoped to this function (e.g. a producer emitted a richer,
    ///   formula-bearing entry first, or the same function is re-added), no
    ///   duplicate is synthesized.
    ///
    /// Deserialization paths (`binary::deserialize_module`,
    /// `parser::parse_module`) intentionally bypass this constructor: they
    /// *reconstruct* an existing module byte/text-faithfully rather than
    /// construct new IR, so a serialized obligation table always round-trips
    /// unchanged.
    pub fn add_function(&mut self, f: Function) {
        self.synthesize_function_obligations(&f);
        self.functions.push(f);
    }

    /// The synthesis half of [`Module::add_function`]: map the function's
    /// claims to obligation kinds, dedup, and append `Pending` entries.
    fn synthesize_function_obligations(&mut self, f: &Function) {
        // Distinct kinds in first-appearance order, each with the (deduped)
        // display names of the claims that gave rise to it. Vec keeps the
        // synthesis deterministic (no HashMap iteration order).
        let mut kinds: Vec<(ObligationKind, Vec<String>)> = Vec::new();
        for annotation in &f.proofs {
            let Some(kind) = annotation.obligation_kind() else {
                continue;
            };
            let name = annotation.to_string();
            match kinds.iter_mut().find(|(k, _)| *k == kind) {
                Some((_, names)) => {
                    if !names.contains(&name) {
                        names.push(name);
                    }
                }
                None => kinds.push((kind, vec![name])),
            }
        }
        if kinds.is_empty() {
            return;
        }
        // Allocate ids after every existing obligation id (never reuse or
        // collide, even when the table carries sparse producer-assigned ids).
        let mut next_id = self
            .proof_obligations
            .iter()
            .map(|o| {
                o.id.index()
                    .checked_add(1)
                    .expect("proof-obligation table exceeds u32 id space")
            })
            .max()
            .unwrap_or(0);
        for (kind, names) in kinds {
            if self
                .proof_obligations
                .iter()
                .any(|o| o.kind == kind && o.function == Some(f.id))
            {
                continue;
            }
            let description = format!(
                "synthesized from function-level annotation(s) [{}] on `{}`",
                names.join(", "),
                f.name
            );
            self.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(next_id),
                    kind,
                    ProofStatus::Pending,
                    description,
                )
                .with_function(f.id),
            );
            next_id = next_id
                .checked_add(1)
                .expect("proof-obligation table exceeds u32 id space");
        }
    }

    /// Resolve a function by `FuncId` without assuming declaration order.
    ///
    /// Canonical modules usually store function `N` at `functions[N]`; the
    /// fallback scan keeps this API correct for frontends that preserve sparse
    /// or externally assigned IDs while still making the common path cheap.
    pub fn function_by_id(&self, id: FuncId) -> Option<&Function> {
        self.functions
            .get(id.as_usize())
            .filter(|func| func.id == id)
            .or_else(|| self.functions.iter().find(|func| func.id == id))
    }

    /// Mutable counterpart to [`Module::function_by_id`].
    pub fn function_by_id_mut(&mut self, id: FuncId) -> Option<&mut Function> {
        if self
            .functions
            .get(id.as_usize())
            .is_some_and(|func| func.id == id)
        {
            return self.functions.get_mut(id.as_usize());
        }
        self.functions.iter_mut().find(|func| func.id == id)
    }

    /// Resolve a function by its stable symbol/name.
    pub fn function_by_name(&self, name: &str) -> Option<&Function> {
        self.functions.iter().find(|func| func.name == name)
    }

    /// Resolve a function type by `FuncTyId`.
    pub fn func_type(&self, id: FuncTyId) -> Option<&FuncTy> {
        self.func_types.get(id.as_usize())
    }

    /// Resolve a registered type by `TyId`.
    pub fn ty(&self, id: TyId) -> Option<&Ty> {
        self.types.get(id.as_usize())
    }

    /// Resolve a struct definition by `StructId` without assuming table order.
    pub fn struct_def(&self, id: StructId) -> Option<&StructDef> {
        self.structs
            .get(id.as_usize())
            .filter(|def| def.id == id)
            .or_else(|| self.structs.iter().find(|def| def.id == id))
    }

    /// Resolve an enum definition by `EnumId` without assuming table order.
    pub fn enum_def(&self, id: EnumId) -> Option<&EnumDef> {
        self.enums
            .get(id.as_usize())
            .filter(|def| def.id == id)
            .or_else(|| self.enums.iter().find(|def| def.id == id))
    }

    /// Resolve a record definition by `RecordId` without assuming table order.
    pub fn record_def(&self, id: RecordId) -> Option<&RecordDef> {
        self.records
            .get(id.as_usize())
            .filter(|def| def.id == id)
            .or_else(|| self.records.iter().find(|def| def.id == id))
    }

    /// Resolve a closure type by `ClosureTyId`.
    pub fn closure_type(&self, id: ClosureTyId) -> Option<&ClosureTy> {
        self.closure_types.get(id.as_usize())
    }

    /// Iterate over every instruction node in module order.
    ///
    /// This is the in-process bridge surface for consumers that need to inspect
    /// TrustIr directly; it avoids round-tripping through text or JSON just to
    /// discover instruction-level facts.
    pub fn instructions(&self) -> impl Iterator<Item = &InstrNode> {
        self.functions.iter().flat_map(Function::instructions)
    }

    /// Returns a summary of proof obligation statuses in this module.
    ///
    /// TrustIr uses this to quickly determine whether a module is fully verified
    /// before attempting cross-target synthesis (GPU/ANE/SIMD).
    pub fn proof_summary(&self) -> ProofSummary {
        let mut summary = ProofSummary::default();
        for obligation in &self.proof_obligations {
            match obligation.status {
                ProofStatus::Pending => summary.pending += 1,
                ProofStatus::Discharged => summary.discharged += 1,
                ProofStatus::Failed => summary.failed += 1,
                ProofStatus::Trusted => summary.trusted += 1,
                ProofStatus::Certified => summary.certified += 1,
            }
        }
        summary
    }

    /// Census of faith-stamped evidence: every certificate in
    /// `proof_certificates` whose evidence is [`ProofEvidence::Trusted`],
    /// as `(obligation id, audit justification)` pairs in table order.
    ///
    /// This is the CI hook for Program CK1's zero-`Trusted` flagship-lane
    /// gate: a lane claiming closed lineage must have an EMPTY census (the
    /// same rungs [`proof::lineage_closed`] reports as
    /// [`proof::LineageGap::TrustedRung`] gaps — the census enumerates every
    /// occurrence module-wide, where `lineage_closed` stops at the first gap
    /// on the manifest's reachable chain). An empty census does not by itself
    /// mean "closed" (obligations can still be `Pending`/`Failed`, or the
    /// manifest can have holes); it means no obligation was discharged by a
    /// manual audit taken on faith.
    pub fn trusted_evidence_census(&self) -> Vec<(ProofId, &str)> {
        self.proof_certificates
            .iter()
            .filter_map(|cert| match &cert.evidence {
                ProofEvidence::Trusted(justification) => {
                    Some((cert.obligation, justification.as_str()))
                }
                _ => None,
            })
            .collect()
    }

    /// Compute the whole-module stable structural digest — the build-determinism
    /// (G19) fingerprint of this artifact.
    ///
    /// This is the reusable form of the previously-inline digest computed at the
    /// point of signing (`trust-ir-build`'s `ModuleBuilder::sign`). It serializes
    /// the module via [`crate::binary::serialize_module`] — which walks every
    /// arena/table (functions, blocks, instructions, constants, globals, types,
    /// func-types, structs, enums, records, closure-types, proof obligations and
    /// certificates, target info, files, diagnostics, spec modules) in
    /// **declared / insertion (Vec) order** — and then hashes the bytes with the
    /// domain-separated [`crate::proof::ProofDigest::sha256_domain`] hasher
    /// under the domain `"trust_ir.module.v2"`. Module digests cross untrusted
    /// transport and lineage boundaries, so the legacy structural checksum is
    /// not an admissible identity here.
    ///
    /// # Determinism contract (G19)
    ///
    /// The result MUST be a pure function of the module's *value* and MUST NOT
    /// depend on `HashMap`/`HashSet` iteration order (which Rust's `std`
    /// randomizes per process via `RandomState`). The only interning performed
    /// during serialization (`binary::collect_strings` / the string pool) uses a
    /// `BTreeMap`, and every table is emitted in `Vec` order — so two builds of
    /// the same module in *separate processes* (different hash seeds) produce
    /// byte-identical serialization and therefore an identical digest. Any future
    /// edit to the serialization path that introduces `HashMap`/`HashSet`
    /// iteration into the emitted bytes breaks this contract and will be caught
    /// by the determinism test
    /// (`trust-ir-conformance/tests/build_determinism.rs`).
    ///
    /// Float values (`Constant::Float`) are encoded via raw IEEE-754 bits
    /// (`f64::to_bits().to_le_bytes()`), so `-0.0` and NaN payloads are captured
    /// bit-exactly and identically across runs (no `format!`-based float
    /// formatting feeds the digest).
    ///
    /// The canonical serializer is compiled privately when the public `binary`
    /// API feature is disabled, so this identity is available in every build.
    pub fn stable_digest(&self) -> crate::proof::ProofDigest {
        let bytes = crate::binary::serialize_module(self);
        crate::proof::ProofDigest::sha256_domain("trust_ir.module.v2", &bytes)
    }

    /// Hash the exact containing module and target function while excluding
    /// every [`Function::source_provenance`] field.
    ///
    /// The target function is retained as the sole function in the digest
    /// image, while module/type/global tables and the module name remain. This
    /// binds a carrier to its function and compilation artifact without making
    /// the digest recursively depend on itself or on a sibling carrier.
    pub fn source_provenance_semantic_digest(
        &self,
        function: FuncId,
    ) -> Result<crate::proof::ProofDigest, String> {
        if self
            .functions
            .iter()
            .filter(|candidate| candidate.id == function)
            .count()
            != 1
        {
            return Err(format!(
                "source provenance target function #{} is missing or duplicated",
                function.index(),
            ));
        }
        let mut semantic = self.clone();
        semantic
            .functions
            .retain(|candidate| candidate.id == function);
        semantic.functions[0].source_provenance = None;
        let module_digest = semantic.stable_digest();
        let mut bytes = Vec::with_capacity(4 + 1 + 32);
        bytes.extend_from_slice(&function.index().to_be_bytes());
        bytes.push(match module_digest.algorithm {
            crate::proof::ProofDigestAlgorithm::Sha256 => 0,
            crate::proof::ProofDigestAlgorithm::TrustIrStableV1 => 1,
        });
        bytes.extend_from_slice(&module_digest.bytes);
        Ok(crate::proof::ProofDigest::sha256_domain(
            "trust_ir.source_provenance.semantic_function.v1",
            &bytes,
        ))
    }

    /// Content-address a `(module, obligation)` pair (v23): the SHA-256
    /// [`ObligationDigest`] used as the WS4-M2 cert-cache key. Returns `None`
    /// when `id` names no obligation in this module, or when the obligation's
    /// `function` scope names no function (a dangling scope has no
    /// addressable content).
    ///
    /// # Identity contract
    ///
    /// The digest is a pure function of the obligation's *claim* and its
    /// owning function's *content*:
    ///
    /// - obligation kind, description, and full formula (schema, payload,
    ///   smtlib, sort);
    /// - when the obligation is function-scoped: the owning function's name,
    ///   its **canonical text form** ([`format::canonical`]'s per-function
    ///   slice: dense SSA renumbering, stable block order), its `entry`
    ///   block, and its `summary` contract (`requires`/`ensures`/`params`).
    ///   `entry` and `summary` are hashed explicitly because the canonical
    ///   text carries neither, yet both are proof-relevant: `entry` decides
    ///   execution order, and a cached certificate may have *assumed* the
    ///   `requires` clauses — weakening a contract MUST invalidate its slot.
    ///
    /// Deliberately EXCLUDED: the obligation's [`ProofStatus`] and the
    /// summary's `proved` flag — verification progress is mutable
    /// bookkeeping, not identity (a cache keyed on it would self-invalidate
    /// on discharge) — and the obligation's own `ProofId`/`FuncId` plus every
    /// SSA `ValueId` (densely renumbered by the canonical form).
    ///
    /// # Why `fmt`-gated
    ///
    /// The function content is encoded via the canonical formatter
    /// (`format::canonical`, the `fmt` feature) precisely so the digest is
    /// arena-order/value-renumbering insensitive. The eventual WS4-M2
    /// contract is **digest-equal ⟺ `trust-ir-diff`-clean** (for the scoped
    /// function and claim); the canonical form is the current best
    /// approximation. Known residues — all in the safe direction
    /// (over-invalidation: a spurious cache *miss*, never a stale *hit*):
    ///
    /// - the `functy.N` signature index (module-level type-table renumbering
    ///   shifts it; `trust-ir-diff` aligns structurally and would not report
    ///   that);
    /// - raw `bbN` block labels (block-id renumbering shifts the digest;
    ///   `trust-ir-diff` pairs blocks positionally by DFS and ignores it);
    /// - raw `ProofId` indices inside per-call `; #proof_ctx:` clauses
    ///   (proof-table renumbering shifts the digest; `trust-ir-diff` resolves
    ///   them to claim fingerprints).
    #[cfg(feature = "fmt")]
    pub fn obligation_digest(&self, id: ProofId) -> Option<ObligationDigest> {
        let obligation = self.proof_obligations.iter().find(|o| o.id == id)?;
        let function = match obligation.function {
            None => None,
            Some(fid) => Some(self.functions.iter().find(|f| f.id == fid)?),
        };
        let content = function.map(|f| (f, format::canonical_function(f)));
        Some(ObligationDigest(proof::obligation_content_digest(
            obligation,
            content.as_ref().map(|(func, text)| (*func, text.as_str())),
        )))
    }
}

/// Content-address of a `(module, obligation)` pair — the WS4-M2 cert-cache
/// key produced by [`Module::obligation_digest`] (v23). Wraps the SHA-256
/// [`ProofDigest`] of the obligation's claim plus its owning function's
/// canonical content; see the producing method for the exact identity
/// contract ("body edit invalidates exactly its digest and dependents").
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ObligationDigest(pub ProofDigest);

impl core::fmt::Display for ObligationDigest {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Structural identity of two struct defs: equal in everything but `id`.
///
/// The exhaustive destructuring is deliberate — adding a field to `StructDef`
/// fails compilation here, forcing the dedup contract of
/// [`Module::add_struct_def`] to account for it.
fn struct_def_structurally_eq(a: &StructDef, b: &StructDef) -> bool {
    let StructDef {
        id: _,
        name,
        fields,
        size,
        align,
        repr,
    } = a;
    *name == b.name
        && *fields == b.fields
        && *size == b.size
        && *align == b.align
        && *repr == b.repr
}

/// Structural identity of two enum defs: equal in everything but `id`.
/// Exhaustively destructured for the same reason as
/// [`struct_def_structurally_eq`].
fn enum_def_structurally_eq(a: &EnumDef, b: &EnumDef) -> bool {
    let EnumDef {
        id: _,
        name,
        variants,
        discriminants,
        repr,
        layout,
    } = a;
    *name == b.name
        && *variants == b.variants
        && *discriminants == b.discriminants
        && *repr == b.repr
        && *layout == b.layout
}

/// Current schema for the semantic source-loop/place provenance carrier.
pub const SOURCE_PROVENANCE_SCHEMA_V1: u32 = 1;

/// An exact SSA parameter place that the MIR consumer can reconstruct without
/// consulting debug names or guessing from instruction order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SourcePlace {
    /// Parameter `index` of the function entry block.
    FunctionParameter { index: u32 },
    /// Parameter `index` of the owning [`SourceLoopProvenance::header`] block.
    LoopParameter { index: u32 },
}

/// One compiler-owned source identifier and its exact reconstructed place.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceBindingProvenance {
    /// Source spelling authenticated by the compiler contract query.
    pub name: String,
    /// Compiler-owned HIR-local binding identity in the owning function.
    pub hir_local_id: u32,
    /// Exact entry/header parameter that reconstructs the MIR whole-local.
    pub place: SourcePlace,
}

/// One compiler-owned source loop and its exact TrustIR natural-loop header.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceLoopProvenance {
    /// Dense source-loop identity from the compiler contract query.
    pub source_loop_id: u32,
    /// HIR-local identity of the source loop expression.
    pub hir_local_id: u32,
    /// TrustIR block reconstructed as the MIR natural-loop header.
    pub header: BlockId,
    /// Canonical, name-sorted source binding map for clauses on this loop.
    pub bindings: Vec<SourceBindingProvenance>,
}

/// Semantic source-loop/place authority for one function (v35).
///
/// This is deliberately separate from [`Function::value_names`] and lexical
/// scopes: those fields are cosmetic debugger claims. A consumer may use this
/// carrier only after all three independent bindings hold:
///
/// * `compiler_source_digest` exactly matches a digest freshly regenerated
///   from the compiler-owned HIR/query catalog for the same function;
/// * `semantic_body_digest` matches [`Module::source_provenance_semantic_digest`],
///   which hashes the containing module/function after removing every source
///   provenance field and therefore avoids a circular self-hash;
/// * `binding_digest` passes [`SourceProvenance::binding_digest_is_valid`],
///   binding the exact injective loop/name/place map to both identities.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceProvenance {
    pub schema: u32,
    pub compiler_source_digest: crate::proof::ProofDigest,
    pub semantic_body_digest: crate::proof::ProofDigest,
    pub binding_digest: crate::proof::ProofDigest,
    pub loops: Vec<SourceLoopProvenance>,
}

impl SourceProvenance {
    /// Construct a v1 carrier and seal its mapping digest. The semantic digest
    /// is supplied by the owning module's non-circular digest helper.
    #[must_use]
    pub fn new(
        compiler_source_digest: crate::proof::ProofDigest,
        semantic_body_digest: crate::proof::ProofDigest,
        loops: Vec<SourceLoopProvenance>,
    ) -> Self {
        let mut provenance = Self {
            schema: SOURCE_PROVENANCE_SCHEMA_V1,
            compiler_source_digest,
            semantic_body_digest,
            binding_digest: crate::proof::ProofDigest::zero(),
            loops,
        };
        provenance.binding_digest = provenance.compute_binding_digest();
        provenance
    }

    /// Check the domain-separated digest of the source identity, semantic body
    /// identity, and complete ordered loop/name/place map. There is
    /// intentionally no public refresh/reseal operation: ordinary transforms
    /// must drop the carrier, while a compiler producer constructs a fresh one
    /// with [`SourceProvenance::new`].
    #[must_use]
    pub fn binding_digest_is_valid(&self) -> bool {
        self.binding_digest == self.compute_binding_digest()
    }

    fn compute_binding_digest(&self) -> crate::proof::ProofDigest {
        fn u32_bytes(out: &mut Vec<u8>, value: u32) {
            out.extend_from_slice(&value.to_be_bytes());
        }
        fn digest_bytes(out: &mut Vec<u8>, digest: crate::proof::ProofDigest) {
            out.push(match digest.algorithm {
                crate::proof::ProofDigestAlgorithm::Sha256 => 0,
                crate::proof::ProofDigestAlgorithm::TrustIrStableV1 => 1,
            });
            out.extend_from_slice(&digest.bytes);
        }
        fn string_bytes(out: &mut Vec<u8>, value: &str) {
            let len = u32::try_from(value.len()).unwrap_or(u32::MAX);
            u32_bytes(out, len);
            out.extend_from_slice(value.as_bytes());
        }

        let mut bytes = Vec::new();
        u32_bytes(&mut bytes, self.schema);
        digest_bytes(&mut bytes, self.compiler_source_digest);
        digest_bytes(&mut bytes, self.semantic_body_digest);
        u32_bytes(
            &mut bytes,
            u32::try_from(self.loops.len()).unwrap_or(u32::MAX),
        );
        for source_loop in &self.loops {
            u32_bytes(&mut bytes, source_loop.source_loop_id);
            u32_bytes(&mut bytes, source_loop.hir_local_id);
            u32_bytes(&mut bytes, source_loop.header.index());
            u32_bytes(
                &mut bytes,
                u32::try_from(source_loop.bindings.len()).unwrap_or(u32::MAX),
            );
            for binding in &source_loop.bindings {
                string_bytes(&mut bytes, &binding.name);
                u32_bytes(&mut bytes, binding.hir_local_id);
                match binding.place {
                    SourcePlace::FunctionParameter { index } => {
                        bytes.push(0);
                        u32_bytes(&mut bytes, index);
                    }
                    SourcePlace::LoopParameter { index } => {
                        bytes.push(1);
                        u32_bytes(&mut bytes, index);
                    }
                }
            }
        }
        crate::proof::ProofDigest::sha256_domain("trust_ir.source_provenance.binding.v1", &bytes)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Function {
    pub id: FuncId,
    pub name: String,
    pub ty: FuncTyId,
    pub entry: BlockId,
    pub blocks: Vec<Block>,
    pub proofs: Vec<ProofAnnotation>,
    /// Calling convention. Defaults to C.
    pub calling_conv: CallingConv,
    /// Linkage type. Defaults to External.
    pub linkage: Linkage,
    /// Optimization attributes (function + per-parameter). Default-empty for
    /// legacy modules. Claim-style hints; not proof-carrying (fast-2).
    ///
    /// ALWAYS emitted by serde (no `skip_serializing_if`): the canonical
    /// MessagePack codec (`rmp_serde::to_vec`, the CLI) is POSITIONAL, and a
    /// positional struct can carry at most ONE trailing conditionally-skipped field.
    /// `producer` is that field as of v23 (`summary` was, through v22); `attrs`
    /// must therefore be always-present so it keeps its index. This is also what
    /// preserves BACKWARD-COMPAT: a pre-v18 blob whose `attrs` was non-empty (and
    /// thus emitted at `attrs`'s index) still decodes, because `attrs` is still
    /// read at that same index (audit 2026-06-25 F2).
    #[cfg_attr(feature = "serde", serde(default))]
    pub attrs: FuncAttrs,
    /// Separate-compilation contract (`requires`/`ensures`). Present iff this
    /// function publishes a callee contract for modular verification. A body-less
    /// function (`blocks.is_empty()`) carrying a summary is a *contract-only
    /// declaration* — the IR-level "body `None` ⇒ summary" state that lets a caller
    /// be verified against this function's contract without its body
    /// (`designs/2026-06-25-trust-ir-composition-design.md`). Default-`None` for
    /// legacy modules.
    ///
    /// ALWAYS emitted by serde since v23 (no `skip_serializing_if`; `None`
    /// encodes as nil): the canonical MessagePack codec is POSITIONAL, and a
    /// positional struct may carry at most ONE trailing conditionally-skipped
    /// field. Through v22 `summary` was that field; v23's `producer` now is, so
    /// `summary` must be always-present to keep its index. Backward compat is
    /// preserved by `serde(default)` in both directions of history: a pre-v18
    /// array stops at `attrs`, a v18..=v22 array stops at `attrs` or `summary`,
    /// and each shorter form decodes with the missing trailing fields as
    /// `None`. When adding the NEXT optional field, repeat this move: make
    /// `producer` always-emitted and append the newcomer as the sole trailing
    /// skipped field.
    #[cfg_attr(feature = "serde", serde(default))]
    pub summary: Option<FunctionSummary>,
    /// Producer provenance: which frontend/tool emitted this function (v23).
    /// `None` for legacy modules and producers that do not stamp provenance.
    /// Claim-style metadata — no operational semantics; see [`Producer`].
    ///
    /// ALWAYS emitted by serde since v32 (no `skip_serializing_if`; `None`
    /// encodes as nil) — the v23 move re-applied per its own instruction:
    /// `value_names` is now the sole trailing conditionally-skipped field, so
    /// `producer` must be always-present to keep its positional index.
    #[cfg_attr(feature = "serde", serde(default))]
    pub producer: Option<Producer>,
    /// Trust (C2-names, v32): debug names for SSA values — the producer's
    /// record of the source-level binding each value carries. Entry-block
    /// params are values too, so ONE field covers parameters and locals; the
    /// MIR shim consumes it to mint `var_debug_info` for derived bodies.
    /// Claim-style metadata — no operational semantics, never proof-bearing.
    /// `None` for legacy modules and producers that do not stamp names.
    ///
    /// ALWAYS emitted by serde since v33 (no `skip_serializing_if`; `None`
    /// encodes as nil) — the v23/v32 move re-applied per its own instruction:
    /// `scopes` is now the sole trailing conditionally-skipped field, so
    /// `value_names` must be always-present to keep its positional index.
    #[cfg_attr(feature = "serde", serde(default))]
    pub value_names: Option<Vec<(ValueId, String)>>,
    /// Trust (C2-scopes, v33): the function's LEXICAL SCOPE TREE — the other
    /// half of debug location, with [`crate::node::InstrNode::scope`] naming an
    /// entry per instruction. Index 0 is the outermost (whole-body) scope; see
    /// [`ScopeData`] for the ordering invariant.
    ///
    /// Claim-style metadata, never proof-bearing: a wrong scope makes a
    /// debugger show the wrong variable list, it cannot make a false verdict.
    /// `None` for legacy modules, for producers that do not stamp scopes, and
    /// deliberately for a body whose tree is JUST the outermost scope — that
    /// case carries no information a consumer could not supply itself, and
    /// `Some(vec![root])` would only invite a reader to think it did.
    ///
    /// ALWAYS emitted by serde since v35: source provenance is now the sole
    /// trailing conditionally-skipped field, so `scopes` keeps its positional
    /// index even when absent.
    #[cfg_attr(feature = "serde", serde(default))]
    pub scopes: Option<Vec<ScopeData>>,
    /// Trust (E4/E5 source provenance, v35): compiler-authenticated source-loop
    /// identity plus an injective source-identifier-to-reconstructible-place
    /// map. This is semantic authority, not debug metadata. Consumers must
    /// recheck its compiler, semantic-body, and binding digests before use.
    ///
    /// Declared LAST and conditionally skipped so all pre-v35 positional serde
    /// arrays continue to decode with `None`.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub source_provenance: Option<SourceProvenance>,
}

/// A function's separate-compilation contract: the preconditions a caller must
/// establish and the postconditions the callee guarantees.
///
/// This is the IR-level carrier of a callee CONTRACT — the thing a separately
/// compiled caller is verified against instead of the callee body. Clauses are
/// [`crate::ProofFormula`]s (a stable `schema` + opaque `payload` string), **not**
/// a solver `Formula`: that keeps `trust-ir`'s zero-required-dependency guarantee
/// intact (the verifier-side `trust_ir_contract::Formula` is a `#[non_exhaustive]`
/// serde type and must not leak into the format core). The
/// `ProofFormula::trust_types_json` schema round-trips losslessly to the verifier
/// `Formula` in the `trust-ir-bridge` layer.
// Field-level `skip_serializing_if` is deliberately NOT used here: the canonical
// MessagePack codec (`rmp_serde::to_vec`, used by the `trust-ir` CLI) encodes
// structs POSITIONALLY, where a skipped non-trailing field shifts every later
// field out of position on decode. Keeping all four fields always-present makes
// the contract round-trip safely through positional MessagePack as well as JSON.
#[derive(Debug, Clone, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FunctionSummary {
    /// Preconditions the caller must establish at each call site.
    #[cfg_attr(feature = "serde", serde(default))]
    pub requires: Vec<ProofFormula>,
    /// Postconditions the callee guarantees on return. A caller may *assume* these
    /// only when [`FunctionSummary::proved`] is set.
    #[cfg_attr(feature = "serde", serde(default))]
    pub ensures: Vec<ProofFormula>,
    /// Formal parameter names, in declaration order. These are the substitution
    /// keys the verifier rebinds to actual arguments at a call site (formals → args,
    /// the result symbol → the caller's destination). Without them a contract
    /// cannot be instantiated, so a non-trivial summary should always carry them.
    #[cfg_attr(feature = "serde", serde(default))]
    pub params: Vec<String>,
    /// True iff every clause is backed by a discharged module obligation. A caller
    /// may assume the `ensures` at a call site only when this holds; an unproved
    /// summary contributes nothing (the call stays havoced).
    #[cfg_attr(feature = "serde", serde(default))]
    pub proved: bool,
}

impl FunctionSummary {
    /// An empty, unproved summary.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// True when the summary carries no clauses at all (neither requires nor
    /// ensures). Used by serialization to omit trivial summaries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty()
    }

    /// True when the summary carries at least one postcondition clause.
    #[must_use]
    pub fn has_ensures(&self) -> bool {
        !self.ensures.is_empty()
    }

    /// Set the formal parameter names (declaration order).
    #[must_use]
    pub fn with_params(mut self, params: Vec<String>) -> Self {
        self.params = params;
        self
    }

    /// Append a precondition clause.
    #[must_use]
    pub fn requiring(mut self, clause: ProofFormula) -> Self {
        self.requires.push(clause);
        self
    }

    /// Append a postcondition clause.
    #[must_use]
    pub fn ensuring(mut self, clause: ProofFormula) -> Self {
        self.ensures.push(clause);
        self
    }

    /// Mark the summary's clauses as discharged (assumable by callers).
    #[must_use]
    pub fn proved(mut self) -> Self {
        self.proved = true;
        self
    }
}

/// A borrowed view of a function's body: its entry block and its block list.
///
/// Returned by [`Function::body`]; `Some` for a defined function, `None` for a
/// contract-only declaration. This is the `Option`-typed body the composition
/// design names — the field layout stays `entry` + `blocks` (the ecosystem reads
/// those directly in thousands of sites) while the `Option` semantics are exposed
/// through this accessor.
#[derive(Debug, Clone, Copy)]
pub struct FunctionBodyRef<'a> {
    /// The entry block id.
    pub entry: BlockId,
    /// The function's basic blocks, in declaration order.
    pub blocks: &'a [Block],
}

impl Function {
    /// Returns the maximum `ValueId` currently used in this function (parameters or instructions).
    pub fn max_value_id(&self) -> u32 {
        let mut max = 0u32;
        for block in &self.blocks {
            for (id, _) in &block.params {
                max = max.max(id.index());
            }
            for node in &block.body {
                for id in &node.results {
                    max = max.max(id.index());
                }
            }
        }
        max
    }
}

/// Return the worst (most conservative) of two `Divergence` classes.
///
/// Ordering: `High` > `Low` > `Uniform`. Used by
/// [`Function::divergence_class`] so that multiple `DivergenceClass`
/// annotations cannot be softened by combination.
fn divergence_worst(
    a: crate::proof::Divergence,
    b: crate::proof::Divergence,
) -> crate::proof::Divergence {
    use crate::proof::Divergence;
    // Rank: Uniform = 0, Low = 1, High = 2. Max wins.
    fn rank(d: Divergence) -> u8 {
        match d {
            Divergence::Uniform => 0,
            Divergence::Low => 1,
            Divergence::High => 2,
        }
    }
    if rank(a) >= rank(b) { a } else { b }
}

impl Function {
    pub fn new(id: FuncId, name: impl Into<String>, ty: FuncTyId, entry: BlockId) -> Self {
        Self {
            id,
            name: name.into(),
            ty,
            entry,
            blocks: Vec::new(),
            proofs: Vec::new(),
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            attrs: FuncAttrs::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }
    }

    /// Construct a *contract-only declaration*: a body-less function that carries
    /// a [`FunctionSummary`] instead of blocks (the IR-level "body `None` ⇒
    /// summary" state). Used to build a trusted-prelude module — a [`Module`]
    /// whose functions are all such declarations — so a separately compiled caller
    /// is verified against this contract rather than the (absent) body. The
    /// declaration has `External` linkage and no blocks; `entry` is set to the
    /// conventional `BlockId(0)` but is never resolved (there is no body).
    #[must_use]
    pub fn declaration(
        id: FuncId,
        name: impl Into<String>,
        ty: FuncTyId,
        summary: FunctionSummary,
    ) -> Self {
        Self {
            id,
            name: name.into(),
            ty,
            entry: BlockId(0),
            blocks: Vec::new(),
            proofs: Vec::new(),
            calling_conv: CallingConv::default(),
            linkage: Linkage::External,
            attrs: FuncAttrs::default(),
            summary: Some(summary),
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }
    }

    /// Attach a separate-compilation [`FunctionSummary`] (contract) to this
    /// function. A defined function may publish its contract for modular
    /// verification; a body-less one becomes a contract-only declaration.
    #[must_use]
    pub fn with_summary(mut self, summary: FunctionSummary) -> Self {
        self.summary = Some(summary);
        self
    }

    /// Stamp producer provenance on this function (v23). See [`Producer`].
    #[must_use]
    pub fn with_producer(mut self, producer: Producer) -> Self {
        self.producer = Some(producer);
        self
    }

    /// True iff this function has a body (at least one basic block).
    ///
    /// A function with no blocks is a *declaration*: either a contract-only
    /// function (`summary.is_some()`) or an opaque external symbol.
    #[must_use]
    pub fn has_body(&self) -> bool {
        !self.blocks.is_empty()
    }

    /// True iff this function is a body-less declaration (no basic blocks).
    #[must_use]
    pub fn is_declaration(&self) -> bool {
        self.blocks.is_empty()
    }

    /// The `Option`-typed body the composition design names: `Some(entry, blocks)`
    /// for a defined function, `None` for a contract-only declaration. The field
    /// layout stays `entry` + `blocks`; this exposes the `Option` semantics without
    /// breaking the thousands of direct field reads across the ecosystem.
    #[must_use]
    pub fn body(&self) -> Option<FunctionBodyRef<'_>> {
        if self.has_body() {
            Some(FunctionBodyRef {
                entry: self.entry,
                blocks: &self.blocks,
            })
        } else {
            None
        }
    }

    /// Returns true if this function has the given proof annotation.
    pub fn has_proof(&self, annotation: &ProofAnnotation) -> bool {
        self.proofs.contains(annotation)
    }

    /// Returns true if this function is annotated as pure (no side effects).
    ///
    /// A pure function can be safely moved to GPU/ANE for cross-target synthesis.
    pub fn is_pure(&self) -> bool {
        self.proofs.contains(&ProofAnnotation::Pure)
    }

    /// Returns true if this function is annotated as deterministic.
    ///
    /// Deterministic functions produce the same output for the same input regardless
    /// of execution order, making them safe to distribute across GPU threads.
    pub fn is_deterministic(&self) -> bool {
        self.proofs.contains(&ProofAnnotation::Deterministic)
    }

    /// Returns true if this function has the minimum annotations required
    /// for safe GPU/ANE offloading.
    ///
    /// TrustIr requires at minimum: `Pure` (no side effects) + `NoPanic`
    /// (GPU has no unwinding) + `Deterministic` (safe to distribute across
    /// GPU threads).
    ///
    /// **Contract — frozen (see `designs/2026-04-18-ty-supremacy-trust-ir-scope.md`
    /// §3.2).** This predicate is intentionally *not* tightened by the
    /// memory-role, parallel-purity, or divergence annotations introduced in
    /// TrustIr#30. Pre-existing TrustIr blobs and pre-existing downstream consumers
    /// (tRust, TrustIr CPU/SIMD paths) rely on this exact three-annotation
    /// check. The stricter GPU gate TrustIr `KernelExtract` queries is
    /// [`Function::is_gpu_eligible`], which composes this predicate with
    /// `ParallelMap` + `DivergenceClass(Uniform | Low)`.
    ///
    /// This is a conservative check; individual instructions within the
    /// function may have additional annotations (memory-role, `ParallelMap`,
    /// `BoundedLoop`, `DivergenceClass(_)`) that enable further GPU
    /// optimisations.
    pub fn is_safe_for_gpu(&self) -> bool {
        self.proofs.contains(&ProofAnnotation::Pure)
            && self.proofs.contains(&ProofAnnotation::NoPanic)
            && self.proofs.contains(&ProofAnnotation::Deterministic)
    }

    /// Returns the function's `DivergenceClass` annotation if one is present.
    ///
    /// If multiple `DivergenceClass(_)` annotations are attached, the most
    /// conservative (i.e. worst) class is returned so a single `High`
    /// annotation cannot be masked by a later `Uniform`. Returns `None` when
    /// the function carries no divergence annotation at all.
    pub fn divergence_class(&self) -> Option<crate::proof::Divergence> {
        use crate::proof::Divergence;
        let mut worst: Option<Divergence> = None;
        for p in &self.proofs {
            if let ProofAnnotation::DivergenceClass(d) = p {
                worst = Some(match worst {
                    None => *d,
                    Some(existing) => divergence_worst(existing, *d),
                });
            }
        }
        worst
    }

    /// Stronger GPU eligibility gate — the predicate TrustIr `KernelExtract`
    /// queries when planning GPU kernel extraction.
    ///
    /// `is_gpu_eligible` layers the richer TrustIr#30 annotations on top of the
    /// frozen [`Function::is_safe_for_gpu`] contract:
    ///
    /// 1. `is_safe_for_gpu()` — `Pure + NoPanic + Deterministic`.
    /// 2. `ParallelMap` is present — the function body is a data-parallel
    ///    map that is safe to dispatch across GPU lanes.
    /// 3. A `DivergenceClass` annotation is attached **and** its class is
    ///    `Uniform` or `Low`. A missing annotation or `High` disqualifies
    ///    GPU kernel extraction under the default conservative policy
    ///    (TrustIr falls back to CPU/SIMD).
    ///
    /// See `designs/2026-04-18-ty-supremacy-trust-ir-scope.md` §3.2 for the
    /// rationale for splitting the two helpers.
    pub fn is_gpu_eligible(&self) -> bool {
        use crate::proof::Divergence;
        self.is_safe_for_gpu()
            && self.has_proof(&ProofAnnotation::ParallelMap)
            && matches!(
                self.divergence_class(),
                Some(Divergence::Uniform | Divergence::Low)
            )
    }

    /// Returns references to all GPU-relevant proof annotations on this function.
    ///
    /// TrustIr uses these during cross-target synthesis planning to determine
    /// which target capabilities (GPU, ANE, SIMD) a function can exploit.
    pub fn gpu_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::gpu_proofs(self.proofs.as_slice())
    }

    /// Returns references to all memory safety proof annotations on this function.
    pub fn memory_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::memory_proofs(self.proofs.as_slice())
    }

    /// Returns references to all arithmetic safety proof annotations on this function.
    pub fn arithmetic_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::arithmetic_proofs(self.proofs.as_slice())
    }

    /// Returns references to all functional correctness proof annotations on this function.
    pub fn functional_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::functional_proofs(self.proofs.as_slice())
    }

    /// Returns references to all concurrency proof annotations on this function.
    /// (Added to match `InstrNode`'s filter set — the two had drifted.)
    pub fn concurrency_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::concurrency_proofs(self.proofs.as_slice())
    }

    /// Returns references to all aliasing proof annotations on this function.
    pub fn aliasing_proofs(&self) -> Vec<&ProofAnnotation> {
        ProofAnnotationFilters::aliasing_proofs(self.proofs.as_slice())
    }

    /// Resolve a basic block by `BlockId` without assuming declaration order.
    pub fn block(&self, id: BlockId) -> Option<&Block> {
        self.blocks
            .get(id.as_usize())
            .filter(|block| block.id == id)
            .or_else(|| self.blocks.iter().find(|block| block.id == id))
    }

    /// Mutable counterpart to [`Function::block`].
    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut Block> {
        if self
            .blocks
            .get(id.as_usize())
            .is_some_and(|block| block.id == id)
        {
            return self.blocks.get_mut(id.as_usize());
        }
        self.blocks.iter_mut().find(|block| block.id == id)
    }

    /// Resolve the function entry block.
    pub fn entry_block(&self) -> Option<&Block> {
        self.block(self.entry)
    }

    /// Iterate over every instruction node in block declaration order.
    pub fn instructions(&self) -> impl Iterator<Item = &InstrNode> {
        self.blocks.iter().flat_map(Block::instructions)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Block {
    pub id: BlockId,
    pub params: Vec<(ValueId, Ty)>,
    pub body: Vec<InstrNode>,
}

impl Block {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            params: Vec::new(),
            body: Vec::new(),
        }
    }

    pub fn with_param(mut self, value: ValueId, ty: Ty) -> Self {
        self.params.push((value, ty));
        self
    }

    pub fn terminator(&self) -> Option<&InstrNode> {
        self.body.last().filter(|n| n.is_terminator())
    }

    /// Iterate over the instruction nodes in this block.
    pub fn instructions(&self) -> impl Iterator<Item = &InstrNode> {
        self.body.iter()
    }

    /// Mutable instruction iterator for in-process bridge construction passes.
    pub fn instructions_mut(&mut self) -> impl Iterator<Item = &mut InstrNode> {
        self.body.iter_mut()
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Global {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    pub initializer: Option<Constant>,
    /// Linkage type. Defaults to External.
    pub linkage: Linkage,
    /// TLS model. `None` means this is an ordinary non-TLS global.
    ///
    /// `default` (not `skip_serializing_if`) so the field keeps a stable
    /// POSITION under rmp-serde's compact array encoding: once a later optional
    /// field (`align`) exists, skipping a middle field would shift every
    /// following field's array index and mis-decode. `default` still lets an
    /// older payload that lacks the field decode to `None`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub tls: Option<TlsModel>,
    /// Declared byte alignment of the global's storage, a power of two.
    ///
    /// `None` means "no explicit over-alignment request": a consumer derives
    /// the alignment from the global's [`Ty`] layout (falling back to the
    /// natural alignment). `Some(n)` pins the storage alignment to `n` bytes —
    /// this is how a producer communicates a `#[repr(align(N))]` static or a
    /// SIMD-vector static whose alignment exceeds what its lowered byte-image
    /// type (`Array(U8, N)`) would otherwise report. TrustCg aligns the global's
    /// offset within its section up to this value and widens the section's own
    /// alignment to cover it (binary v29). Accepted binary v23..=v25 inputs
    /// default to `None`; ambiguous-lineage v26..=v28 module blobs are rejected.
    #[cfg_attr(feature = "serde", serde(default))]
    pub align: Option<u32>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_func(proofs: Vec<ProofAnnotation>) -> Function {
        let mut f = Function::new(FuncId::new(0), "test", FuncTyId::new(0), BlockId::new(0));
        f.proofs = proofs;
        f
    }

    #[test]
    fn func_new_has_empty_attrs() {
        let f = Function::new(FuncId::new(0), "test", FuncTyId::new(0), BlockId::new(0));
        assert!(f.attrs.is_empty());
    }

    #[test]
    fn defined_function_is_not_a_declaration() {
        let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        f.blocks.push(Block::new(BlockId::new(0)));
        assert!(f.has_body());
        assert!(!f.is_declaration());
        let body = f.body().expect("defined function has a body");
        assert_eq!(body.entry, f.entry);
        assert_eq!(body.blocks.len(), 1);
        assert!(f.summary.is_none());
    }

    #[test]
    fn contract_only_declaration_has_no_body_but_a_summary() {
        let summary = FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(ProofFormula::smtlib2("(> result 0)", "Bool"))
            .proved();
        let decl =
            Function::declaration(FuncId::new(1), "helper", FuncTyId::new(0), summary.clone());
        assert!(!decl.has_body());
        assert!(decl.is_declaration());
        assert!(decl.body().is_none());
        assert_eq!(decl.summary.as_ref(), Some(&summary));
        // A declaration is External so the bodyless-declaration validity holds.
        assert_eq!(decl.linkage, Linkage::External);
    }

    #[test]
    fn function_summary_builders_and_predicates() {
        let empty = FunctionSummary::new();
        assert!(empty.is_empty());
        assert!(!empty.has_ensures());
        assert!(!empty.proved);

        let s = FunctionSummary::new()
            .requiring(ProofFormula::smtlib2("(>= x 0)", "Bool"))
            .ensuring(ProofFormula::smtlib2("(> result 0)", "Bool"))
            .with_params(vec!["x".to_string()])
            .proved();
        assert!(!s.is_empty());
        assert!(s.has_ensures());
        assert!(s.proved);
        assert_eq!(s.params, vec!["x".to_string()]);
        assert_eq!(s.requires.len(), 1);
        assert_eq!(s.ensures.len(), 1);
    }

    #[test]
    fn defined_function_may_also_publish_a_summary() {
        // A function with a body MAY also publish its contract for separate
        // compilation — body and summary are independent.
        let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        f.blocks.push(Block::new(BlockId::new(0)));
        let f = f.with_summary(FunctionSummary::new().proved());
        assert!(f.has_body());
        assert!(f.summary.is_some());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn function_summary_serde_round_trips() {
        // The positional-MessagePack discipline in one assertion: EVERY field is
        // always-emitted except the sole trailing skipped optional, which is
        // absent. Stating it as the exact key SET rather than a hand-picked pair
        // is what keeps it honest — the old form asserted `!contains("producer")`
        // and stayed unmaintained when v32 made `producer` always-emitted, so it
        // sat RED through that release instead of catching anything. Adding a
        // field now FAILS here until this list is updated, which is the point.
        let plain = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        let json = serde_json::to_string(&plain).expect("serialize");
        let value: serde_json::Value = serde_json::from_str(&json).expect("parse");
        let mut keys: Vec<&str> = value
            .as_object()
            .expect("Function serializes as a JSON object")
            .keys()
            .map(String::as_str)
            .collect();
        keys.sort_unstable();
        let mut expected = vec![
            "id",
            "name",
            "ty",
            "entry",
            "blocks",
            "proofs",
            "calling_conv",
            "linkage",
            "attrs",
            "summary",
            "producer",
            "value_names",
            "scopes",
            // `source_provenance` is NOT here: as of v35 it is the sole trailing
            // skipped optional. `scopes` is now always emitted at its stable
            // positional index.
        ];
        expected.sort_unstable();
        assert_eq!(keys, expected, "positional-index discipline broken: {json}");
        let back: Function = serde_json::from_str(&json).expect("deserialize");
        assert!(back.summary.is_none());
        assert!(back.producer.is_none());
        assert!(back.value_names.is_none());
        assert!(back.scopes.is_none());
        assert!(back.source_provenance.is_none());

        // Present summary round-trips losslessly through JSON.
        let summary = FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .requiring(ProofFormula::trust_types_json(
                "{\"x\":0}",
                "(>= x 0)",
                "Bool",
            ))
            .ensuring(ProofFormula::smtlib2("(> result 0)", "Bool"))
            .proved();
        let decl =
            Function::declaration(FuncId::new(1), "helper", FuncTyId::new(0), summary.clone());
        let json = serde_json::to_string(&decl).expect("serialize");
        let back: Function = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back.summary.as_ref(), Some(&summary));
        assert!(back.is_declaration());
    }

    /// audit 2026-06-25 F2: a PRE-v18 MessagePack blob (no `summary` field, `attrs`
    /// always at its index because it is now always-emitted) must still decode under
    /// the v18 layout — for BOTH empty and non-empty `attrs`. The positional codec
    /// (`rmp_serde::to_vec`) is the one the CLI uses, and it is the regression-prone
    /// path (named JSON is order/optional-insensitive).
    #[cfg(feature = "serde")]
    #[test]
    fn pre_v18_msgpack_with_attrs_still_decodes() {
        // Mirror the EXACT pre-v18 serde layout: the 8 required fields then a single
        // trailing `attrs` (skip-if-empty), with NO `summary`.
        #[derive(serde::Serialize)]
        struct LegacyFunction {
            id: FuncId,
            name: String,
            ty: FuncTyId,
            entry: BlockId,
            blocks: Vec<Block>,
            proofs: Vec<ProofAnnotation>,
            calling_conv: CallingConv,
            linkage: Linkage,
            #[serde(skip_serializing_if = "FuncAttrs::is_empty")]
            attrs: FuncAttrs,
        }
        let mk = |attrs: FuncAttrs| LegacyFunction {
            id: FuncId::new(7),
            name: "legacy".into(),
            ty: FuncTyId::new(0),
            entry: BlockId::new(0),
            blocks: vec![],
            proofs: vec![],
            calling_conv: CallingConv::C,
            linkage: Linkage::External,
            attrs,
        };
        // Empty attrs (attrs skipped in the legacy blob).
        let bytes = rmp_serde::to_vec(&mk(FuncAttrs::default())).expect("encode");
        let back: Function = rmp_serde::from_slice(&bytes).expect("decode empty-attrs legacy blob");
        assert_eq!(back.name, "legacy");
        assert!(back.summary.is_none());
        // NON-empty attrs (attrs emitted at its index — the case the audit caught).
        let attrs = FuncAttrs {
            readonly: true,
            ..Default::default()
        };
        let bytes = rmp_serde::to_vec(&mk(attrs)).expect("encode");
        let back: Function =
            rmp_serde::from_slice(&bytes).expect("decode non-empty-attrs legacy blob");
        assert!(back.attrs.readonly, "legacy attrs preserved");
        assert!(back.summary.is_none());
    }

    /// v23 mirror of the F2 audit test above: a PRE-v23 (v18..=v22 layout)
    /// positional MessagePack blob — `summary` as the trailing skip-if-None
    /// optional, NO `producer` field — must still decode under the v23 layout
    /// (summary always-emitted, producer the new sole trailing optional), for
    /// BOTH the 9-element (summary skipped) and 10-element (summary present)
    /// legacy arrays. Real pinned v22 blobs are additionally decoded in
    /// `trust-ir-conformance/tests/back_compat.rs`.
    #[cfg(feature = "serde")]
    #[test]
    fn pre_v23_msgpack_with_summary_still_decodes() {
        // Mirror the EXACT v18..=v22 serde layout.
        #[derive(serde::Serialize)]
        struct V22Function {
            id: FuncId,
            name: String,
            ty: FuncTyId,
            entry: BlockId,
            blocks: Vec<Block>,
            proofs: Vec<ProofAnnotation>,
            calling_conv: CallingConv,
            linkage: Linkage,
            attrs: FuncAttrs,
            #[serde(skip_serializing_if = "Option::is_none")]
            summary: Option<FunctionSummary>,
        }
        let mk = |summary: Option<FunctionSummary>| V22Function {
            id: FuncId::new(3),
            name: "v22".into(),
            ty: FuncTyId::new(0),
            entry: BlockId::new(0),
            blocks: vec![],
            proofs: vec![],
            calling_conv: CallingConv::C,
            linkage: Linkage::External,
            attrs: FuncAttrs::default(),
            summary,
        };
        // 9-element legacy array (summary skipped).
        let bytes = rmp_serde::to_vec(&mk(None)).expect("encode");
        let back: Function = rmp_serde::from_slice(&bytes).expect("decode summary-less v22 blob");
        assert_eq!(back.name, "v22");
        assert!(back.summary.is_none());
        assert!(
            back.producer.is_none(),
            "pre-v23 blob decodes producer=None"
        );
        // 10-element legacy array (summary present at the old trailing slot).
        let summary = FunctionSummary::new().proved();
        let bytes = rmp_serde::to_vec(&mk(Some(summary.clone()))).expect("encode");
        let back: Function =
            rmp_serde::from_slice(&bytes).expect("decode summary-carrying v22 blob");
        assert_eq!(back.summary.as_ref(), Some(&summary));
        assert!(
            back.producer.is_none(),
            "pre-v23 blob decodes producer=None"
        );
    }

    /// C2-names backward compatibility: the v31 positional layout ended with
    /// `producer` as its sole skipped optional. Both possible array lengths must
    /// still decode after v32/v33 appended `value_names` and `scopes`.
    #[cfg(feature = "serde")]
    #[test]
    fn v31_msgpack_with_producer_still_decodes() {
        #[derive(serde::Serialize)]
        struct V31Function {
            id: FuncId,
            name: String,
            ty: FuncTyId,
            entry: BlockId,
            blocks: Vec<Block>,
            proofs: Vec<ProofAnnotation>,
            calling_conv: CallingConv,
            linkage: Linkage,
            attrs: FuncAttrs,
            summary: Option<FunctionSummary>,
            #[serde(skip_serializing_if = "Option::is_none")]
            producer: Option<Producer>,
        }

        let mk = |producer| V31Function {
            id: FuncId::new(31),
            name: "v31".into(),
            ty: FuncTyId::new(0),
            entry: BlockId::new(0),
            blocks: vec![],
            proofs: vec![],
            calling_conv: CallingConv::C,
            linkage: Linkage::External,
            attrs: FuncAttrs::default(),
            summary: None,
            producer,
        };

        for producer in [None, Some(Producer::TRust)] {
            let bytes = rmp_serde::to_vec(&mk(producer.clone())).expect("encode v31 function");
            let back: Function =
                rmp_serde::from_slice(&bytes).expect("decode v31 function under v33 layout");
            assert_eq!(back.producer, producer);
            assert!(back.value_names.is_none());
            assert!(back.scopes.is_none());
        }
    }

    /// C2-scopes backward compatibility: the v32 positional layout always
    /// emitted `producer` and ended with `value_names` as its sole skipped
    /// optional. Adding `scopes` must preserve both the short and long forms.
    #[cfg(feature = "serde")]
    #[test]
    fn v32_msgpack_with_value_names_still_decodes() {
        #[derive(serde::Serialize)]
        struct V32Function {
            id: FuncId,
            name: String,
            ty: FuncTyId,
            entry: BlockId,
            blocks: Vec<Block>,
            proofs: Vec<ProofAnnotation>,
            calling_conv: CallingConv,
            linkage: Linkage,
            attrs: FuncAttrs,
            summary: Option<FunctionSummary>,
            producer: Option<Producer>,
            #[serde(skip_serializing_if = "Option::is_none")]
            value_names: Option<Vec<(ValueId, String)>>,
        }

        let mk = |value_names| V32Function {
            id: FuncId::new(32),
            name: "v32".into(),
            ty: FuncTyId::new(0),
            entry: BlockId::new(0),
            blocks: vec![],
            proofs: vec![],
            calling_conv: CallingConv::C,
            linkage: Linkage::External,
            attrs: FuncAttrs::default(),
            summary: None,
            producer: Some(Producer::TRust),
            value_names,
        };

        for value_names in [None, Some(vec![(ValueId::new(7), "source binding".into())])] {
            let bytes = rmp_serde::to_vec(&mk(value_names.clone())).expect("encode v32 function");
            let back: Function =
                rmp_serde::from_slice(&bytes).expect("decode v32 function under v33 layout");
            assert_eq!(back.producer, Some(Producer::TRust));
            assert_eq!(back.value_names, value_names);
            assert!(back.scopes.is_none());
            assert!(back.source_provenance.is_none());
        }
    }

    /// v35 source-provenance backward compatibility: v33/v34 ended with
    /// `scopes` as the sole skipped optional. Both the short and long v34
    /// positional arrays decode with no invented source authority.
    #[cfg(feature = "serde")]
    #[test]
    fn v34_msgpack_with_scopes_still_decodes_without_source_provenance() {
        #[derive(serde::Serialize)]
        struct V34Function {
            id: FuncId,
            name: String,
            ty: FuncTyId,
            entry: BlockId,
            blocks: Vec<Block>,
            proofs: Vec<ProofAnnotation>,
            calling_conv: CallingConv,
            linkage: Linkage,
            attrs: FuncAttrs,
            summary: Option<FunctionSummary>,
            producer: Option<Producer>,
            value_names: Option<Vec<(ValueId, String)>>,
            #[serde(skip_serializing_if = "Option::is_none")]
            scopes: Option<Vec<ScopeData>>,
        }

        let mk = |scopes| V34Function {
            id: FuncId::new(34),
            name: "v34".into(),
            ty: FuncTyId::new(0),
            entry: BlockId::new(0),
            blocks: vec![],
            proofs: vec![],
            calling_conv: CallingConv::C,
            linkage: Linkage::External,
            attrs: FuncAttrs::default(),
            summary: None,
            producer: Some(Producer::TRust),
            value_names: Some(vec![(ValueId::new(4), "x".into())]),
            scopes,
        };

        for scopes in [
            None,
            Some(vec![ScopeData {
                parent: None,
                span: None,
            }]),
        ] {
            let bytes = rmp_serde::to_vec(&mk(scopes.clone())).expect("encode v34 function");
            let back: Function =
                rmp_serde::from_slice(&bytes).expect("decode v34 function under v35 layout");
            assert_eq!(back.scopes, scopes);
            assert!(
                back.source_provenance.is_none(),
                "legacy bytes must never synthesize source authority"
            );
        }
    }

    /// C2-scopes backward compatibility for instructions: v32 ended at the
    /// conditionally skipped `proof_context`; v33 appends `scope`.
    #[cfg(feature = "serde")]
    #[test]
    fn v32_msgpack_instr_node_with_proof_context_still_decodes() {
        #[derive(serde::Serialize)]
        struct V32InstrNode {
            inst: Inst,
            results: Vec<ValueId>,
            proofs: Vec<ProofAnnotation>,
            span: Option<SourceSpan>,
            #[serde(skip_serializing_if = "Option::is_none")]
            proof_context: Option<crate::proof::ProofContext>,
        }

        let mk = |proof_context| V32InstrNode {
            inst: Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            },
            results: vec![],
            proofs: vec![],
            span: None,
            proof_context,
        };
        let populated = crate::proof::ProofContext {
            assumes: vec![ProofId::new(1)],
            establishes: vec![ProofId::new(2)],
        };

        for proof_context in [None, Some(populated)] {
            let bytes =
                rmp_serde::to_vec(&mk(proof_context.clone())).expect("encode v32 instruction");
            let back: InstrNode =
                rmp_serde::from_slice(&bytes).expect("decode v32 instruction under v33 layout");
            assert_eq!(back.proof_context, proof_context);
            assert!(back.scope.is_none());
        }
    }

    /// R3 #6/#7: positional MessagePack round-trip for NON-default Param/FuncAttrs.
    /// Before the always-emit fix, skipping a non-LAST field shifted later fields —
    /// `ParamAttrs{nonnull:true}` HARD-FAILED to decode (bool into `dereferenceable`'s
    /// u64 slot) and `FuncAttrs{readnone:true}` silently FLIPPED to `readonly:true`.
    #[cfg(feature = "serde")]
    #[test]
    fn non_default_attrs_survive_positional_msgpack() {
        for pa in [
            ParamAttrs {
                nonnull: true,
                ..Default::default()
            },
            ParamAttrs {
                readonly: true,
                ..Default::default()
            },
            ParamAttrs {
                align: Some(16),
                ..Default::default()
            },
            ParamAttrs {
                dereferenceable: Some(8),
                noalias: true,
                readonly: true,
                ..Default::default()
            },
        ] {
            let bytes = rmp_serde::to_vec(&pa).expect("encode ParamAttrs");
            let back: ParamAttrs = rmp_serde::from_slice(&bytes).expect("decode ParamAttrs");
            assert_eq!(back, pa, "ParamAttrs must survive positional msgpack");
        }
        for fa in [
            FuncAttrs {
                readnone: true,
                ..Default::default()
            },
            FuncAttrs {
                cold: true,
                ..Default::default()
            },
            FuncAttrs {
                inlinehint: true,
                ..Default::default()
            },
            FuncAttrs {
                readonly: true,
                params: vec![ParamAttrs {
                    nonnull: true,
                    ..Default::default()
                }],
                ..Default::default()
            },
        ] {
            let bytes = rmp_serde::to_vec(&fa).expect("encode FuncAttrs");
            let back: FuncAttrs = rmp_serde::from_slice(&bytes).expect("decode FuncAttrs");
            assert_eq!(
                back, fa,
                "FuncAttrs must survive positional msgpack (no field flip)"
            );
        }
    }

    /// R3 #6/#7 backward-compat: a legacy SHORTER positional array (written before the
    /// always-emit fix) still decodes — the missing trailing fields default. `(true,)`
    /// is the 1-element `[true]` legacy `readonly`-only encoding.
    #[cfg(feature = "serde")]
    #[test]
    fn legacy_short_attr_arrays_decode_via_default() {
        let bytes = rmp_serde::to_vec(&(true,)).expect("encode 1-tuple");
        let back: FuncAttrs = rmp_serde::from_slice(&bytes).expect("decode legacy short FuncAttrs");
        assert!(
            back.readonly && !back.readnone && back.params.is_empty(),
            "missing fields default"
        );
        let bytes = rmp_serde::to_vec(&(Option::<u64>::None,)).expect("encode 1-tuple");
        let back: ParamAttrs =
            rmp_serde::from_slice(&bytes).expect("decode legacy short ParamAttrs");
        assert!(
            back.dereferenceable.is_none() && !back.nonnull,
            "missing fields default"
        );
    }

    /// R3 #5: a `ProofFormula` contract clause (the live separate-compilation carrier)
    /// with `smtlib=None, sort=Some` used to round-trip back as `smtlib=Some, sort=None`
    /// through the positional Module msgpack codec. All field combinations must survive.
    #[cfg(feature = "serde")]
    #[test]
    fn proof_formula_smtlib_sort_survive_positional_msgpack() {
        let mk = |smtlib: Option<&str>, sort: Option<&str>| crate::ProofFormula {
            schema: "trust-types.Formula@1".into(),
            payload: "p".into(),
            smtlib: smtlib.map(str::to_string),
            sort: sort.map(str::to_string),
        };
        for pf in [
            mk(None, Some("Bool")),
            mk(Some("(>= x 0)"), None),
            mk(None, None),
            mk(Some("(>= x 0)"), Some("Bool")),
        ] {
            let bytes = rmp_serde::to_vec(&pf).expect("encode ProofFormula");
            let back: crate::ProofFormula =
                rmp_serde::from_slice(&bytes).expect("decode ProofFormula");
            assert_eq!(
                back, pf,
                "ProofFormula smtlib/sort must survive positional msgpack"
            );
        }
    }

    #[test]
    fn func_param_attrs_is_empty_semantics() {
        assert!(ParamAttrs::default().is_empty());
        let pa = ParamAttrs {
            nonnull: true,
            ..ParamAttrs::default()
        };
        assert!(!pa.is_empty());
        let mut fa = FuncAttrs::default();
        assert!(fa.is_empty());
        // An all-default params vector keeps FuncAttrs empty.
        fa.params.push(ParamAttrs::default());
        assert!(fa.is_empty());
        // A non-empty ParamAttrs makes the whole set non-empty.
        fa.params.push(pa);
        assert!(!fa.is_empty());
    }

    #[test]
    fn function_has_proof_present() {
        let f = make_func(vec![ProofAnnotation::Pure, ProofAnnotation::NoOverflow]);
        assert!(f.has_proof(&ProofAnnotation::Pure));
        assert!(f.has_proof(&ProofAnnotation::NoOverflow));
    }

    #[test]
    fn function_has_proof_absent() {
        let f = make_func(vec![ProofAnnotation::Pure]);
        assert!(!f.has_proof(&ProofAnnotation::NoOverflow));
        assert!(!f.has_proof(&ProofAnnotation::InBounds));
    }

    #[test]
    fn function_has_proof_empty() {
        let f = make_func(vec![]);
        assert!(!f.has_proof(&ProofAnnotation::Pure));
    }

    #[test]
    fn function_is_pure_true() {
        let f = make_func(vec![ProofAnnotation::Pure, ProofAnnotation::Deterministic]);
        assert!(f.is_pure());
    }

    #[test]
    fn function_is_pure_false() {
        let f = make_func(vec![ProofAnnotation::NoOverflow]);
        assert!(!f.is_pure());
    }

    #[test]
    fn function_is_pure_empty() {
        let f = make_func(vec![]);
        assert!(!f.is_pure());
    }

    #[test]
    fn module_proof_summary_empty() {
        let module = Module::new("empty");
        let summary = module.proof_summary();
        assert_eq!(summary.total(), 0);
        assert!(summary.is_fully_verified());
    }

    #[test]
    fn module_proof_summary_counts() {
        let mut module = Module::new("test");
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::MemorySafety,
            status: ProofStatus::Pending,
            description: "p1".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(1),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "p2".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(2),
            kind: ObligationKind::Precondition,
            status: ProofStatus::Discharged,
            description: "p3".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(3),
            kind: ObligationKind::Postcondition,
            status: ProofStatus::Failed,
            description: "p4".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(4),
            kind: ObligationKind::TranslationValidation,
            status: ProofStatus::Trusted,
            description: "p5".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });

        let summary = module.proof_summary();
        assert_eq!(summary.pending, 1);
        assert_eq!(summary.discharged, 2);
        assert_eq!(summary.failed, 1);
        assert_eq!(summary.trusted, 1);
        assert_eq!(summary.total(), 5);
        assert!(!summary.is_fully_verified());
    }

    #[test]
    fn module_proof_summary_fully_verified() {
        let mut module = Module::new("verified");
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::MemorySafety,
            status: ProofStatus::Discharged,
            description: "ok".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(1),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Trusted,
            description: "trusted".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });

        let summary = module.proof_summary();
        assert!(summary.is_fully_verified());
        assert_eq!(summary.total(), 2);
    }

    // --- Block tests ---

    #[test]
    fn block_with_param_builds_correctly() {
        let block = Block::new(BlockId::new(0))
            .with_param(ValueId::new(0), Ty::I32)
            .with_param(ValueId::new(1), Ty::I64);
        assert_eq!(block.params.len(), 2);
        assert_eq!(block.params[0], (ValueId::new(0), Ty::I32));
        assert_eq!(block.params[1], (ValueId::new(1), Ty::I64));
    }

    #[test]
    fn block_with_param_chaining() {
        let block = Block::new(BlockId::new(5))
            .with_param(ValueId::new(10), Ty::F64)
            .with_param(ValueId::new(11), Ty::Bool)
            .with_param(ValueId::new(12), Ty::Ptr);
        assert_eq!(block.id, BlockId::new(5));
        assert_eq!(block.params.len(), 3);
        assert!(block.body.is_empty());
    }

    #[test]
    fn block_terminator_returns_some() {
        use crate::inst::Inst;
        let mut block = Block::new(BlockId::new(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        assert!(block.terminator().is_some());
    }

    #[test]
    fn block_terminator_returns_none_empty() {
        let block = Block::new(BlockId::new(0));
        assert!(block.terminator().is_none());
    }

    #[test]
    fn block_terminator_returns_none_non_terminator() {
        use crate::inst::{BinOp, Inst};
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
        );
        assert!(block.terminator().is_none());
    }

    #[test]
    fn block_terminator_br() {
        use crate::inst::Inst;
        let mut block = Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Br {
            target: BlockId::new(1),
            args: vec![],
        }));
        let term = block.terminator();
        assert!(term.is_some());
        assert!(term.unwrap().is_terminator());
    }

    #[test]
    fn block_terminator_unreachable() {
        use crate::inst::Inst;
        let mut block = Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Unreachable));
        assert!(block.terminator().is_some());
    }

    // --- Module::add_type tests ---

    #[test]
    fn module_add_type_returns_sequential_ids() {
        let mut module = Module::new("types");
        let t0 = module.add_type(Ty::I32);
        let t1 = module.add_type(Ty::I64);
        let t2 = module.add_type(Ty::F64);
        assert_eq!(t0, TyId::new(0));
        assert_eq!(t1, TyId::new(1));
        assert_eq!(t2, TyId::new(2));
        assert_eq!(module.types.len(), 3);
        assert_eq!(module.types[0], Ty::I32);
        assert_eq!(module.types[1], Ty::I64);
        assert_eq!(module.types[2], Ty::F64);
    }

    #[test]
    fn module_add_func_type_returns_sequential_ids() {
        let mut module = Module::new("ftypes");
        let ft0 = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let ft1 = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        assert_eq!(ft0, FuncTyId::new(0));
        assert_eq!(ft1, FuncTyId::new(1));
        assert_eq!(module.func_types.len(), 2);
    }

    #[test]
    fn module_add_struct_returns_correct_id() {
        let mut module = Module::new("structs");
        let sid = module.add_struct(StructDef {
            id: StructId::new(42),
            name: "Foo".to_string(),
            fields: vec![],
            size: None,
            align: None,

            repr: Default::default(),
        });
        assert_eq!(sid, StructId::new(42));
        assert_eq!(module.structs.len(), 1);
        assert_eq!(module.structs[0].name, "Foo");
    }

    // --- roadmap §1.2: aggregate builder API with mandatory dedup ---

    fn point_struct(id: u32, name: &str, field_ty: Ty) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: name.to_string(),
            fields: vec![FieldDef {
                name: "x".to_string(),
                ty: field_ty,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: Default::default(),
        }
    }

    fn option_enum(id: u32, name: &str, payload: Ty) -> EnumDef {
        EnumDef {
            id: EnumId::new(id),
            name: name.to_string(),
            variants: vec![
                EnumVariant {
                    name: "None".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Some".to_string(),
                    fields: vec![payload],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
        }
    }

    #[test]
    fn add_struct_def_dedups_structurally_identical_defs() {
        let mut module = Module::new("dedup");
        let a = module.add_struct_def(point_struct(0, "Point", Ty::I64));
        // Same def again — even under a DIFFERENT declared id — returns the
        // original id and inserts nothing.
        let b = module.add_struct_def(point_struct(9, "Point", Ty::I64));
        assert_eq!(a, b);
        assert_eq!(module.structs.len(), 1);
        // A structurally different def (other field type) is a new entry.
        let c = module.add_struct_def(point_struct(1, "Point", Ty::F64));
        assert_ne!(a, c);
        assert_eq!(module.structs.len(), 2);
    }

    #[test]
    fn add_struct_def_never_allows_colliding_ids() {
        let mut module = Module::new("collide");
        let a = module.add_struct_def(point_struct(0, "A", Ty::I64));
        // Different content under the SAME declared id: gets a fresh id.
        let b = module.add_struct_def(point_struct(0, "B", Ty::I64));
        assert_eq!(a, StructId::new(0));
        assert_ne!(a, b);
        assert_eq!(module.structs.len(), 2);
        let mut ids: Vec<u32> = module.structs.iter().map(|sd| sd.id.index()).collect();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), module.structs.len(), "ids stay unique");
        // Both remain resolvable by their (distinct) ids.
        assert_eq!(module.struct_def(a).unwrap().name, "A");
        assert_eq!(module.struct_def(b).unwrap().name, "B");
    }

    #[test]
    fn allocate_struct_id_skips_sparse_ids_and_reserves_by_insert() {
        let mut module = Module::new("alloc");
        assert_eq!(module.allocate_struct_id(), StructId::new(0));
        // A sparse producer-assigned id pushes the allocator past it.
        module.add_struct(point_struct(7, "Sparse", Ty::I64));
        let id = module.allocate_struct_id();
        assert_eq!(id, StructId::new(8));
        // Reserve-by-insert: registering under the allocated id advances it.
        let mut sd = point_struct(0, "Next", Ty::F64);
        sd.id = id;
        assert_eq!(module.add_struct_def(sd), id);
        assert_eq!(module.allocate_struct_id(), StructId::new(9));
    }

    #[test]
    fn add_enum_def_dedups_and_never_collides() {
        let mut module = Module::new("enums");
        let a = module.add_enum_def(option_enum(0, "Option", Ty::I32));
        // Structural duplicate under another id dedups to the original.
        let b = module.add_enum_def(option_enum(5, "Option", Ty::I32));
        assert_eq!(a, b);
        assert_eq!(module.enums.len(), 1);
        // Different payload type = different def; same declared id must not
        // collide.
        let c = module.add_enum_def(option_enum(0, "Option", Ty::I64));
        assert_ne!(a, c);
        assert_eq!(module.enums.len(), 2);
        assert_eq!(
            module.enum_def(c).unwrap().variants[1].fields,
            vec![Ty::I64]
        );
        // Allocator sits past both.
        assert_eq!(module.allocate_enum_id(), EnumId::new(2));
    }

    #[test]
    fn add_struct_and_add_enum_stay_verbatim() {
        // Backward compatibility: the legacy constructors keep raw-push
        // semantics (no dedup, declared id honored verbatim).
        let mut module = Module::new("legacy");
        module.add_struct(point_struct(3, "Same", Ty::I64));
        module.add_struct(point_struct(3, "Same", Ty::I64));
        assert_eq!(module.structs.len(), 2, "legacy add_struct never dedups");
        module.add_enum(option_enum(4, "Same", Ty::I32));
        module.add_enum(option_enum(4, "Same", Ty::I32));
        assert_eq!(module.enums.len(), 2, "legacy add_enum never dedups");
    }

    // --- Global tests ---

    #[test]
    fn global_with_initializer() {
        let g = Global {
            name: "COUNTER".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        };
        assert_eq!(g.name, "COUNTER");
        assert_eq!(g.ty, Ty::I64);
        assert!(g.mutable);
        assert_eq!(g.initializer, Some(Constant::Int(0)));
    }

    #[test]
    fn global_without_initializer() {
        let g = Global {
            name: "UNINIT".to_string(),
            ty: Ty::I32,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
        };
        assert_eq!(g.name, "UNINIT");
        assert!(!g.mutable);
        assert!(g.initializer.is_none());
    }

    #[test]
    fn global_with_aggregate_initializer() {
        let g = Global {
            name: "TABLE".to_string(),
            ty: Ty::Ptr,
            mutable: false,
            initializer: Some(Constant::Aggregate(vec![
                Constant::Int(1),
                Constant::Int(2),
                Constant::Int(3),
            ])),
            linkage: Linkage::External,
            tls: None,
            align: None,
        };
        if let Some(Constant::Aggregate(elems)) = &g.initializer {
            assert_eq!(elems.len(), 3);
        } else {
            panic!("expected Aggregate initializer");
        }
    }

    // --- Module construction tests ---

    #[test]
    fn module_new_is_empty() {
        let module = Module::new("empty");
        assert_eq!(module.name, "empty");
        assert!(module.functions.is_empty());
        assert!(module.structs.is_empty());
        assert!(module.enums.is_empty());
        assert!(module.records.is_empty());
        assert!(module.closure_types.is_empty());
        assert!(module.globals.is_empty());
        assert!(module.func_types.is_empty());
        assert!(module.types.is_empty());
        assert!(module.proof_obligations.is_empty());
        assert!(module.proof_certificates.is_empty());
        assert!(module.spec_modules.is_empty());
    }

    #[test]
    fn module_add_record_returns_id() {
        let mut module = Module::new("records");
        let rd = RecordDef {
            id: RecordId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
        };
        let id = module.add_record(rd);
        assert_eq!(id, RecordId::new(0));
        assert_eq!(module.records.len(), 1);
        assert_eq!(module.records[0].name, "Point");
    }

    #[test]
    fn module_add_closure_type_returns_sequential_ids() {
        let mut module = Module::new("closures");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let c0 = module.add_closure_type(ClosureTy::bare(ft));
        let c1 = module.add_closure_type(ClosureTy {
            func: ft,
            captures: vec![Ty::I32, Ty::Bool],
        });
        assert_eq!(c0, ClosureTyId::new(0));
        assert_eq!(c1, ClosureTyId::new(1));
        assert_eq!(module.closure_types.len(), 2);
        assert_eq!(module.closure_types[0].captures.len(), 0);
        assert_eq!(module.closure_types[1].captures.len(), 2);
    }

    #[test]
    fn module_ty_record_roundtrip() {
        // A Ty::Record(id) can be added via add_type and resolved via records.
        let mut module = Module::new("t");
        let rid = module.add_record(RecordDef {
            id: RecordId::new(0),
            name: "R".to_string(),
            fields: vec![],
        });
        let tid = module.add_type(Ty::Record(rid));
        assert_eq!(module.types[tid.as_usize()], Ty::Record(rid));
    }

    #[test]
    fn module_ty_closure_roundtrip() {
        let mut module = Module::new("tc");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let cid = module.add_closure_type(ClosureTy::bare(ft));
        let tid = module.add_type(Ty::Closure(cid));
        assert_eq!(module.types[tid.as_usize()], Ty::Closure(cid));
    }

    #[test]
    fn module_add_function() {
        let mut module = Module::new("test");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let func = Function::new(FuncId::new(0), "noop", ft, BlockId::new(0));
        module.add_function(func);
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "noop");
        // A claim-free function synthesizes no obligations.
        assert!(module.proof_obligations.is_empty());
    }

    // --- roadmap §1.1: add_function obligation synthesis ---

    #[test]
    fn add_function_synthesizes_obligations_from_claims() {
        let mut module = Module::new("synth");
        let mut func = Function::new(
            FuncId::new(3),
            "checked_math",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        func.proofs = vec![
            ProofAnnotation::NoOverflow,
            ProofAnnotation::DivNonZero,
            ProofAnnotation::NoPanic,
            ProofAnnotation::InBounds,
            ProofAnnotation::Terminates,
        ];
        module.add_function(func);

        // NoOverflow + DivNonZero collapse into ONE ArithmeticSafety entry;
        // NoPanic, InBounds, Terminates each map to their own kind.
        assert_eq!(module.proof_obligations.len(), 4);
        let kinds: Vec<&ObligationKind> =
            module.proof_obligations.iter().map(|o| &o.kind).collect();
        assert_eq!(
            kinds,
            vec![
                &ObligationKind::ArithmeticSafety,
                &ObligationKind::PanicFreedom,
                &ObligationKind::BoundsCheck,
                &ObligationKind::Liveness,
            ]
        );
        for (i, ob) in module.proof_obligations.iter().enumerate() {
            assert_eq!(ob.id, ProofId::new(i as u32), "dense id allocation");
            assert_eq!(ob.status, ProofStatus::Pending, "claims are undischarged");
            assert_eq!(
                ob.function,
                Some(FuncId::new(3)),
                "scoped to the function (B4)"
            );
            assert!(
                ob.formula.is_none(),
                "synthesized entries carry no formula yet"
            );
        }
        // The combined arithmetic entry names both originating claims.
        assert!(
            module.proof_obligations[0]
                .description
                .contains("no_overflow")
        );
        assert!(
            module.proof_obligations[0]
                .description
                .contains("div_nonzero")
        );
        assert!(
            module.proof_obligations[0]
                .description
                .contains("checked_math")
        );
        // Summary now reflects the synthesized pending claims.
        assert_eq!(module.proof_summary().pending, 4);
    }

    #[test]
    fn add_function_synthesis_skips_hint_only_annotations() {
        // Negative control: markers and claim-style hints carry no obligation.
        let mut module = Module::new("hints");
        let mut func = Function::new(FuncId::new(0), "hinted", FuncTyId::new(0), BlockId::new(0));
        func.proofs = vec![
            ProofAnnotation::Wrapping,
            ProofAnnotation::Pure,
            ProofAnnotation::Deterministic,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::BoundedLoop(16),
            ProofAnnotation::DivergenceClass(proof::Divergence::Uniform),
            ProofAnnotation::ValueRange { lo: 0, hi: 255 },
            ProofAnnotation::KnownBits { zeros: 1, ones: 0 },
            ProofAnnotation::BranchWeights(vec![1, 2]),
            ProofAnnotation::ReadonlyTable,
            ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
            ProofAnnotation::ProofRef(ProofId::new(7)),
            ProofAnnotation::Custom(ProofTag::new(9)),
        ];
        module.add_function(func);
        assert!(
            module.proof_obligations.is_empty(),
            "hint/marker annotations must not synthesize obligations"
        );
    }

    #[test]
    fn add_function_synthesis_dedups_against_existing_scoped_obligation() {
        let mut module = Module::new("dedup");
        // A producer already emitted a richer, formula-bearing entry for this
        // function's arithmetic safety.
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(11),
                ObligationKind::ArithmeticSafety,
                ProofStatus::Discharged,
                "producer-emitted",
            )
            .with_function(FuncId::new(2)),
        );
        let mut func = Function::new(
            FuncId::new(2),
            "prover_ready",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        func.proofs = vec![ProofAnnotation::NoOverflow, ProofAnnotation::NoPanic];
        module.add_function(func);

        // ArithmeticSafety is NOT duplicated; PanicFreedom is added with an id
        // allocated past the sparse producer id (12, not 0).
        assert_eq!(module.proof_obligations.len(), 2);
        assert_eq!(
            module.proof_obligations[1].kind,
            ObligationKind::PanicFreedom
        );
        assert_eq!(module.proof_obligations[1].id, ProofId::new(12));

        // Re-adding the same function is idempotent on the obligation table.
        let mut again = Function::new(
            FuncId::new(2),
            "prover_ready",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        again.proofs = vec![ProofAnnotation::NoOverflow, ProofAnnotation::NoPanic];
        module.add_function(again);
        assert_eq!(module.proof_obligations.len(), 2);
    }

    #[test]
    fn add_function_synthesis_scopes_per_function() {
        // The same claim on two different functions yields two obligations,
        // each scoped to its own function.
        let mut module = Module::new("scoped");
        let mut f0 = Function::new(FuncId::new(0), "a", FuncTyId::new(0), BlockId::new(0));
        f0.proofs = vec![ProofAnnotation::NoOverflow];
        let mut f1 = Function::new(FuncId::new(1), "b", FuncTyId::new(0), BlockId::new(0));
        f1.proofs = vec![ProofAnnotation::NoOverflow];
        module.add_function(f0);
        module.add_function(f1);
        assert_eq!(module.proof_obligations.len(), 2);
        assert_eq!(module.proof_obligations[0].function, Some(FuncId::new(0)));
        assert_eq!(module.proof_obligations[1].function, Some(FuncId::new(1)));
        assert!(
            module.proof_obligations[0].id != module.proof_obligations[1].id,
            "ids never collide"
        );
    }

    #[test]
    fn module_typed_lookup_helpers_do_not_require_text_roundtrip() {
        let mut module = Module::new("bridge");
        let ty = module.add_type(Ty::I64);
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let cid = module.add_closure_type(ClosureTy::bare(ft));
        let sid = module.add_struct(StructDef {
            id: StructId::new(8),
            name: "Pair".to_string(),
            fields: vec![FieldDef {
                name: "x".to_string(),
                ty: Ty::I64,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),

            repr: Default::default(),
        });
        let eid = module.add_enum(EnumDef {
            id: EnumId::new(4),
            name: "Maybe".to_string(),
            variants: vec![EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::I64],
                field_names: Vec::new(),
            }],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
        });
        let rid = module.add_record(RecordDef {
            id: RecordId::new(6),
            name: "Rec".to_string(),
            fields: vec![FieldDef {
                name: "y".to_string(),
                ty: Ty::Bool,
                offset: None,
            }],
        });

        let mut func = Function::new(FuncId::new(7), "bridge_fn", ft, BlockId::new(3));
        let mut block = Block::new(BlockId::new(3));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        assert_eq!(module.ty(ty), Some(&Ty::I64));
        assert_eq!(module.func_type(ft).unwrap().params, vec![Ty::I64]);
        assert_eq!(module.closure_type(cid).unwrap().func, ft);
        assert_eq!(module.struct_def(sid).unwrap().name, "Pair");
        assert_eq!(module.enum_def(eid).unwrap().name, "Maybe");
        assert_eq!(module.record_def(rid).unwrap().name, "Rec");
        assert_eq!(
            module.function_by_id(FuncId::new(7)).unwrap().name,
            "bridge_fn"
        );
        assert!(module.function_by_name("bridge_fn").is_some());
        assert_eq!(module.instructions().count(), 1);
    }

    #[test]
    fn function_and_block_lookup_helpers_use_typed_ids() {
        let ft = FuncTyId::new(0);
        let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(9));
        let mut block = Block::new(BlockId::new(9));
        block.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.push(block);

        assert!(func.entry_block().unwrap().terminator().is_some());
        assert_eq!(
            func.block(BlockId::new(9)).unwrap().instructions().count(),
            1
        );

        let entry = func.block_mut(BlockId::new(9)).unwrap();
        entry.body.clear();
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        assert_eq!(func.instructions().count(), 1);
        assert!(func.entry_block().unwrap().terminator().is_some());
    }

    // --- Function tests ---

    #[test]
    fn function_new_has_no_blocks() {
        let f = Function::new(FuncId::new(0), "test", FuncTyId::new(0), BlockId::new(0));
        assert!(f.blocks.is_empty());
        assert!(f.proofs.is_empty());
        assert_eq!(f.name, "test");
        assert_eq!(f.id, FuncId::new(0));
        assert_eq!(f.entry, BlockId::new(0));
    }

    #[test]
    fn function_multiple_proofs() {
        let mut f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::Terminates,
            ProofAnnotation::Deterministic,
        ]);
        assert!(f.has_proof(&ProofAnnotation::Pure));
        assert!(f.has_proof(&ProofAnnotation::Terminates));
        assert!(f.has_proof(&ProofAnnotation::Deterministic));
        assert!(!f.has_proof(&ProofAnnotation::InBounds));
        assert!(f.is_pure());

        // Remove Pure, check is_pure returns false
        f.proofs.retain(|p| p != &ProofAnnotation::Pure);
        assert!(!f.is_pure());
    }

    // --- Function is_deterministic tests ---

    #[test]
    fn function_is_deterministic_true() {
        let f = make_func(vec![ProofAnnotation::Pure, ProofAnnotation::Deterministic]);
        assert!(f.is_deterministic());
    }

    #[test]
    fn function_is_deterministic_false() {
        let f = make_func(vec![ProofAnnotation::Pure]);
        assert!(!f.is_deterministic());
    }

    #[test]
    fn function_is_deterministic_empty() {
        let f = make_func(vec![]);
        assert!(!f.is_deterministic());
    }

    // --- Function is_safe_for_gpu tests ---

    #[test]
    fn function_is_safe_for_gpu_all_three() {
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
        ]);
        assert!(f.is_safe_for_gpu());
    }

    #[test]
    fn function_is_safe_for_gpu_missing_pure() {
        let f = make_func(vec![
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
        ]);
        assert!(!f.is_safe_for_gpu());
    }

    #[test]
    fn function_is_safe_for_gpu_missing_nopanic() {
        let f = make_func(vec![ProofAnnotation::Pure, ProofAnnotation::Deterministic]);
        assert!(!f.is_safe_for_gpu());
    }

    #[test]
    fn function_is_safe_for_gpu_missing_deterministic() {
        let f = make_func(vec![ProofAnnotation::Pure, ProofAnnotation::NoPanic]);
        assert!(!f.is_safe_for_gpu());
    }

    #[test]
    fn function_is_safe_for_gpu_empty() {
        let f = make_func(vec![]);
        assert!(!f.is_safe_for_gpu());
    }

    #[test]
    fn function_is_safe_for_gpu_with_extras() {
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::Terminates,
            ProofAnnotation::NoOverflow,
        ]);
        assert!(f.is_safe_for_gpu());
    }

    // --- Function gpu_proofs tests ---

    #[test]
    fn function_gpu_proofs_filters_correctly() {
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::DataRaceFree, // not GPU-relevant
            ProofAnnotation::Monotonic,    // not GPU-relevant
        ]);
        let gpu = f.gpu_proofs();
        assert_eq!(gpu.len(), 3);
        assert!(gpu.contains(&&ProofAnnotation::Pure));
        assert!(gpu.contains(&&ProofAnnotation::NoPanic));
        assert!(gpu.contains(&&ProofAnnotation::Deterministic));
    }

    #[test]
    fn function_gpu_proofs_empty() {
        let f = make_func(vec![ProofAnnotation::DataRaceFree]);
        assert!(f.gpu_proofs().is_empty());
    }

    #[test]
    fn function_concurrency_and_aliasing_proofs_match_node_set() {
        // Function previously lacked these filters (drift vs InstrNode); #117
        // added them via the shared ProofAnnotationFilters trait.
        let f = make_func(vec![
            ProofAnnotation::DataRaceFree, // concurrency
            ProofAnnotation::NoAlias,      // aliasing
            ProofAnnotation::Pure,         // neither
        ]);
        let conc = f.concurrency_proofs();
        assert_eq!(conc.len(), 1);
        assert!(conc.contains(&&ProofAnnotation::DataRaceFree));
        let alias = f.aliasing_proofs();
        assert_eq!(alias.len(), 1);
        assert!(alias.contains(&&ProofAnnotation::NoAlias));
    }

    // --- is_safe_for_gpu contract-freeze tests (TrustIr#39) ---
    //
    // The contract in designs/2026-04-18-ty-supremacy-trust-ir-scope.md §3.2 is
    // frozen at `Pure + NoPanic + Deterministic`. DivergenceClass(_) must NOT
    // affect `is_safe_for_gpu` — the stricter gate is `is_gpu_eligible`.

    #[test]
    fn function_is_safe_for_gpu_ignores_divergence_high() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::DivergenceClass(Divergence::High),
        ]);
        assert!(
            f.is_safe_for_gpu(),
            "DivergenceClass(High) must NOT affect is_safe_for_gpu (design §3.2)"
        );
    }

    #[test]
    fn function_is_safe_for_gpu_ignores_divergence_uniform() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
        ]);
        assert!(f.is_safe_for_gpu());
    }

    #[test]
    fn function_is_safe_for_gpu_ignores_divergence_low() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::DivergenceClass(Divergence::Low),
        ]);
        assert!(f.is_safe_for_gpu());
    }

    #[test]
    fn function_is_safe_for_gpu_ignores_parallel_map() {
        // Adding the new ParallelMap annotation must not change the contract.
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::ParallelMap,
        ]);
        assert!(f.is_safe_for_gpu());
    }

    // --- is_gpu_eligible tests (TrustIr#39) ---
    //
    // is_gpu_eligible is the stricter gate TrustIr KernelExtract queries. It
    // composes `is_safe_for_gpu` with `ParallelMap` and
    // `DivergenceClass(Uniform | Low)`.

    #[test]
    fn function_is_gpu_eligible_requires_all_three_base_plus_parallel_and_low_divergence() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::DivergenceClass(Divergence::Low),
        ]);
        assert!(f.is_safe_for_gpu(), "base contract must hold");
        assert!(f.is_gpu_eligible());
    }

    #[test]
    fn function_is_gpu_eligible_accepts_uniform_divergence() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
        ]);
        assert!(f.is_gpu_eligible());
    }

    #[test]
    fn function_is_gpu_eligible_rejects_high_divergence_but_is_safe_for_gpu_still_true() {
        // KEY DIVERGENT-BEHAVIOR TEST (TrustIr#39 quality bar):
        // same function, is_safe_for_gpu = true, is_gpu_eligible = false.
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::DivergenceClass(Divergence::High),
        ]);
        assert!(
            f.is_safe_for_gpu(),
            "is_safe_for_gpu ignores DivergenceClass(High) (contract frozen §3.2)"
        );
        assert!(
            !f.is_gpu_eligible(),
            "is_gpu_eligible must reject DivergenceClass(High)"
        );
    }

    #[test]
    fn function_is_gpu_eligible_rejects_missing_parallel_map() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
        ]);
        assert!(f.is_safe_for_gpu());
        assert!(!f.is_gpu_eligible(), "is_gpu_eligible requires ParallelMap");
    }

    #[test]
    fn function_is_gpu_eligible_rejects_missing_divergence_annotation() {
        // Unknown divergence disqualifies under the default conservative
        // policy (design §3.2: `divergence_class().is_some_and(|d| d <= Low)`).
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::ParallelMap,
        ]);
        assert!(f.is_safe_for_gpu());
        assert!(
            !f.is_gpu_eligible(),
            "is_gpu_eligible requires an explicit DivergenceClass annotation"
        );
    }

    #[test]
    fn function_is_gpu_eligible_rejects_missing_base_contract() {
        use crate::proof::Divergence;
        // Missing Deterministic — base contract fails, so eligibility fails.
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
        ]);
        assert!(!f.is_safe_for_gpu());
        assert!(!f.is_gpu_eligible());
    }

    #[test]
    fn function_is_gpu_eligible_empty_is_false() {
        let f = make_func(vec![]);
        assert!(!f.is_safe_for_gpu());
        assert!(!f.is_gpu_eligible());
    }

    #[test]
    fn function_is_gpu_eligible_worst_divergence_wins_for_mixed_annotations() {
        // Multiple DivergenceClass annotations: the worst class dominates.
        // Uniform + High must behave as if only High were present.
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::NoPanic,
            ProofAnnotation::Deterministic,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
            ProofAnnotation::DivergenceClass(Divergence::High),
        ]);
        assert_eq!(f.divergence_class(), Some(Divergence::High));
        assert!(
            !f.is_gpu_eligible(),
            "A High annotation must not be masked by a Uniform annotation"
        );
    }

    #[test]
    fn function_divergence_class_none_when_absent() {
        let f = make_func(vec![ProofAnnotation::Pure]);
        assert_eq!(f.divergence_class(), None);
    }

    #[test]
    fn function_divergence_class_reports_single_annotation() {
        use crate::proof::Divergence;
        for d in [Divergence::Uniform, Divergence::Low, Divergence::High] {
            let f = make_func(vec![ProofAnnotation::DivergenceClass(d)]);
            assert_eq!(f.divergence_class(), Some(d));
        }
    }

    #[test]
    fn function_divergence_class_low_plus_uniform_is_low() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
            ProofAnnotation::DivergenceClass(Divergence::Low),
        ]);
        assert_eq!(f.divergence_class(), Some(Divergence::Low));
    }

    #[test]
    fn function_gpu_proofs_includes_new_annotations() {
        use crate::proof::Divergence;
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::ReadonlyTable,
            ProofAnnotation::AppendOnlyBuffer,
            ProofAnnotation::AtomicSetInsert,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::BoundedLoop(256),
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
            ProofAnnotation::DivergenceClass(Divergence::High), // excluded
        ]);
        let gpu = f.gpu_proofs();
        assert!(gpu.contains(&&ProofAnnotation::Pure));
        assert!(gpu.contains(&&ProofAnnotation::ReadonlyTable));
        assert!(gpu.contains(&&ProofAnnotation::AppendOnlyBuffer));
        assert!(gpu.contains(&&ProofAnnotation::AtomicSetInsert));
        assert!(gpu.contains(&&ProofAnnotation::ParallelMap));
        assert!(gpu.contains(&&ProofAnnotation::BoundedLoop(256)));
        assert!(gpu.contains(&&ProofAnnotation::DivergenceClass(Divergence::Uniform)));
        assert!(!gpu.contains(&&ProofAnnotation::DivergenceClass(Divergence::High)));
    }

    // --- Function memory_proofs tests ---

    #[test]
    fn function_memory_proofs_filters_correctly() {
        let f = make_func(vec![
            ProofAnnotation::InBounds,
            ProofAnnotation::ValidBorrow,
            ProofAnnotation::Pure,
        ]);
        let mem = f.memory_proofs();
        assert_eq!(mem.len(), 2);
        assert!(mem.contains(&&ProofAnnotation::InBounds));
        assert!(mem.contains(&&ProofAnnotation::ValidBorrow));
    }

    // --- Function arithmetic_proofs tests ---

    #[test]
    fn function_arithmetic_proofs_filters_correctly() {
        let f = make_func(vec![
            ProofAnnotation::NoOverflow,
            ProofAnnotation::DivNonZero,
            ProofAnnotation::Pure,
        ]);
        let arith = f.arithmetic_proofs();
        assert_eq!(arith.len(), 2);
        assert!(arith.contains(&&ProofAnnotation::NoOverflow));
        assert!(arith.contains(&&ProofAnnotation::DivNonZero));
    }

    // --- Function functional_proofs tests ---

    #[test]
    fn function_functional_proofs_filters_correctly() {
        let f = make_func(vec![
            ProofAnnotation::Pure,
            ProofAnnotation::Deterministic,
            ProofAnnotation::Commutative,
            ProofAnnotation::InBounds,
        ]);
        let func_proofs = f.functional_proofs();
        assert_eq!(func_proofs.len(), 3);
        assert!(func_proofs.contains(&&ProofAnnotation::Pure));
        assert!(func_proofs.contains(&&ProofAnnotation::Deterministic));
        assert!(func_proofs.contains(&&ProofAnnotation::Commutative));
    }

    // --- Module clone and equality ---

    #[test]
    fn module_clone_equals_original() {
        let mut module = Module::new("clone_test");
        module.add_type(Ty::I32);
        module.add_type(Ty::F64);
        module.globals.push(Global {
            name: "G".to_string(),
            ty: Ty::Bool,
            mutable: false,
            initializer: Some(Constant::Bool(true)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        let cloned = module.clone();
        assert_eq!(module, cloned);
    }
}

#[cfg(all(test, feature = "serde"))]
mod serde_tests {
    use super::*;

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    /// Helper: JSON round-trip for any serializable/deserializable type.
    fn json_round_trip<T>(val: &T) -> T
    where
        T: serde::Serialize + serde::de::DeserializeOwned + std::fmt::Debug + PartialEq,
    {
        let json = serde_json::to_string_pretty(val).expect("serialize to JSON");
        let back: T = serde_json::from_str(&json).expect("deserialize from JSON");
        assert_eq!(val, &back, "JSON round-trip mismatch");
        back
    }

    /// Helper: MessagePack round-trip for any serializable/deserializable type.
    fn msgpack_round_trip<T>(val: &T) -> T
    where
        T: serde::Serialize + serde::de::DeserializeOwned + std::fmt::Debug + PartialEq,
    {
        let bytes = rmp_serde::to_vec(val).expect("serialize to MessagePack");
        let back: T = rmp_serde::from_slice(&bytes).expect("deserialize from MessagePack");
        assert_eq!(val, &back, "MessagePack round-trip mismatch");
        back
    }

    /// Original round-trip test: build a Module, serialize to JSON, deserialize back.
    #[test]
    fn module_json_round_trip() {
        let mut module = Module::new("test_module");

        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),

            repr: Default::default(),
        });

        module.add_type(Ty::I32);

        module.globals.push(Global {
            name: "COUNTER".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });

        let func_id = FuncId::new(0);
        let entry = BlockId::new(0);
        let mut func = Function::new(func_id, "add", ft, entry);
        func.proofs.push(ProofAnnotation::Pure);
        func.proofs.push(ProofAnnotation::NoOverflow);

        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));

        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::NoOverflow),
        );

        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module.add_function(func);

        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "add does not overflow".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });

        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::Trusted("manual review".to_string()),
        });

        let json = serde_json::to_string_pretty(&module).expect("serialize to JSON");
        assert!(json.contains("test_module"));
        assert!(json.contains("add"));
        assert!(json.contains("Point"));
        assert!(json.contains("COUNTER"));

        let deserialized: Module = serde_json::from_str(&json).expect("deserialize from JSON");
        assert_eq!(module, deserialized);
    }

    // ---- MessagePack round-trip ----

    #[test]
    fn module_msgpack_round_trip() {
        let mut module = Module::new("msgpack_test");

        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::Bool],
            is_vararg: false,
        });

        let mut func = Function::new(FuncId::new(0), "is_positive", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));

        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));

        func.blocks.push(block);
        module.add_function(func);

        msgpack_round_trip(&module);
    }

    fn vector_instruction_module(name: &str) -> Module {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);

        let mut module = Module::new(name);
        module.add_type(v4i32.clone());
        module.add_type(v4bool.clone());
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, v4i32.clone(), v4i32.clone()],
            returns: vec![v4i32.clone(), v4bool.clone()],
            is_vararg: false,
        });

        let mut func = Function::new(FuncId::new(0), "batch_i32", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), v4i32.clone()));
        block.params.push((v(2), v4i32.clone()));

        block.body.push(
            InstrNode::new(Inst::Load {
                ty: v4i32.clone(),
                ptr: v(0),
                volatile: false,
                align: Some(16),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: v4i32.clone(),
                lhs: v(1),
                rhs: v(2),
            })
            .with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: v4i32.clone(),
                lhs: v(4),
                rhs: v(3),
            })
            .with_result(v(5)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: v4i32.clone(),
                lhs: v(5),
                rhs: v(2),
            })
            .with_result(v(6)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::And,
                ty: v4i32.clone(),
                lhs: v(6),
                rhs: v(1),
            })
            .with_result(v(7)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Or,
                ty: v4i32.clone(),
                lhs: v(7),
                rhs: v(2),
            })
            .with_result(v(8)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Xor,
                ty: v4i32.clone(),
                lhs: v(8),
                rhs: v(3),
            })
            .with_result(v(9)),
        );
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: v4i32.clone(),
                lhs: v(9),
                rhs: v(3),
            })
            .with_result(v(10)),
        );
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: v4i32.clone(),
                cond: v(10),
                then_val: v(9),
                else_val: v(3),
            })
            .with_result(v(11)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: v4i32.clone(),
            ptr: v(0),
            value: v(11),
            volatile: false,
            align: Some(16),
        }));
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(11), v(10)],
        }));

        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn serde_vector_instruction_module_round_trip() {
        let module = vector_instruction_module("vector_serde");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn msgpack_is_compact() {
        let module = Module::new("compact_test");
        let json = serde_json::to_string(&module).expect("JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("MessagePack");
        // MessagePack should be smaller than JSON for the same data
        assert!(
            msgpack.len() < json.len(),
            "MessagePack ({} bytes) should be smaller than JSON ({} bytes)",
            msgpack.len(),
            json.len()
        );
    }

    // ---- All instruction variants ----

    #[test]
    fn serde_all_binop_variants() {
        let ops = [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::UDiv,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::SRem,
            BinOp::FAdd,
            BinOp::FSub,
            BinOp::FMul,
            BinOp::FDiv,
            BinOp::FRem,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
        ];
        for op in &ops {
            let inst = Inst::BinOp {
                op: *op,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            };
            let node = InstrNode::new(inst).with_result(v(2));
            json_round_trip(&node);
            msgpack_round_trip(&node);
        }
    }

    #[test]
    fn serde_all_unop_variants() {
        let ops = [UnOp::Neg, UnOp::FNeg, UnOp::Not, UnOp::CtPop];
        for op in &ops {
            let node = InstrNode::new(Inst::UnOp {
                op: *op,
                ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1));
            json_round_trip(&node);
            msgpack_round_trip(&node);
        }
    }

    #[test]
    fn serde_all_overflow_variants() {
        let ops = [
            OverflowOp::AddOverflow,
            OverflowOp::SubOverflow,
            OverflowOp::MulOverflow,
        ];
        for op in &ops {
            let node = InstrNode::new(Inst::Overflow {
                op: *op,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2));
            json_round_trip(&node);
            msgpack_round_trip(&node);
        }
    }

    #[test]
    fn serde_all_icmp_variants() {
        let ops = [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ];
        for op in &ops {
            let node = InstrNode::new(Inst::ICmp {
                op: *op,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2));
            json_round_trip(&node);
        }
    }

    #[test]
    fn serde_all_fcmp_variants() {
        let ops = [
            FCmpOp::OEq,
            FCmpOp::ONe,
            FCmpOp::OLt,
            FCmpOp::OLe,
            FCmpOp::OGt,
            FCmpOp::OGe,
            FCmpOp::UEq,
            FCmpOp::UNe,
            FCmpOp::ULt,
            FCmpOp::ULe,
            FCmpOp::UGt,
            FCmpOp::UGe,
        ];
        for op in &ops {
            let node = InstrNode::new(Inst::FCmp {
                op: *op,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2));
            json_round_trip(&node);
        }
    }

    #[test]
    fn serde_all_cast_variants() {
        let ops = [
            CastOp::Trunc,
            CastOp::ZExt,
            CastOp::SExt,
            CastOp::FPTrunc,
            CastOp::FPExt,
            CastOp::FPToUI,
            CastOp::FPToSI,
            CastOp::UIToFP,
            CastOp::SIToFP,
            CastOp::PtrToInt,
            CastOp::IntToPtr,
            CastOp::Bitcast,
            CastOp::FPToSISat,
            CastOp::FPToUISat,
        ];
        for op in &ops {
            let node = InstrNode::new(Inst::Cast {
                op: *op,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(1));
            json_round_trip(&node);
        }
    }

    #[test]
    fn serde_memory_instructions() {
        let instructions: Vec<InstrNode> = vec![
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(3)),
                align: None,
            })
            .with_result(v(4)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![v(1), v(2)],
                inbounds: false,
            })
            .with_result(v(3)),
        ];
        for node in &instructions {
            json_round_trip(node);
            msgpack_round_trip(node);
        }
    }

    #[test]
    fn serde_atomic_instructions() {
        let instructions: Vec<InstrNode> = vec![
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: v(0),
                ordering: Ordering::Acquire,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::AtomicStore {
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::Release,
            }),
            InstrNode::new(Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::SeqCst,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: v(0),
                expected: v(1),
                desired: v(2),
                success: Ordering::AcqRel,
                failure: Ordering::Relaxed,
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Fence {
                ordering: Ordering::SeqCst,
            }),
        ];
        for node in &instructions {
            json_round_trip(node);
            msgpack_round_trip(node);
        }
    }

    #[test]
    fn serde_all_atomic_rmw_ops() {
        let ops = [
            AtomicRMWOp::Xchg,
            AtomicRMWOp::Add,
            AtomicRMWOp::Sub,
            AtomicRMWOp::And,
            AtomicRMWOp::Or,
            AtomicRMWOp::Xor,
            AtomicRMWOp::Max,
            AtomicRMWOp::Min,
            AtomicRMWOp::UMax,
            AtomicRMWOp::UMin,
        ];
        for op in &ops {
            let node = InstrNode::new(Inst::AtomicRMW {
                op: *op,
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::SeqCst,
            })
            .with_result(v(2));
            json_round_trip(&node);
        }
    }

    #[test]
    fn serde_all_ordering_variants() {
        let orderings = [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ];
        for ord in &orderings {
            let node = InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: v(0),
                ordering: *ord,
            })
            .with_result(v(1));
            json_round_trip(&node);
        }
    }

    #[test]
    fn serde_control_flow_br() {
        let node = InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        });
        json_round_trip(&node);
        msgpack_round_trip(&node);
    }

    #[test]
    fn serde_control_flow_condbr() {
        let node = InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![v(1)],
            else_target: b(2),
            else_args: vec![v(2), v(3)],
        });
        json_round_trip(&node);
        msgpack_round_trip(&node);
    }

    #[test]
    fn serde_control_flow_switch() {
        let node = InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(10),
            default_args: vec![],
            cases: vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: b(1),
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: b(2),
                    args: vec![v(1)],
                },
                SwitchCase {
                    value: Constant::Int(42),
                    target: b(3),
                    args: vec![v(2), v(3)],
                },
            ],
            exhaustive_enum_unreachable: false,
        });
        json_round_trip(&node);
        msgpack_round_trip(&node);
    }

    #[test]
    fn serde_call_instructions() {
        let call = InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![v(0), v(1)],
        })
        .with_result(v(2));
        json_round_trip(&call);

        let call_indirect = InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![v(1)],

            calling_conv: crate::CallingConv::C,
        })
        .with_result(v(2));
        json_round_trip(&call_indirect);
        msgpack_round_trip(&call_indirect);
    }

    #[test]
    fn serde_aggregate_instructions() {
        let instructions: Vec<InstrNode> = vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(0),
                field: 1,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::InsertField {
                ty: Ty::I32,
                aggregate: v(0),
                field: 1,
                value: v(2),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::InsertElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
                value: v(2),
            })
            .with_result(v(3)),
        ];
        for node in &instructions {
            json_round_trip(node);
            msgpack_round_trip(node);
        }
    }

    #[test]
    fn serde_constant_and_special_instructions() {
        let instructions: Vec<InstrNode> = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(1.25),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::NullPtr).with_result(v(3)),
            InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(v(4)),
        ];
        for node in &instructions {
            json_round_trip(node);
            msgpack_round_trip(node);
        }
    }

    #[test]
    fn serde_proof_and_pseudo_instructions() {
        let instructions: Vec<InstrNode> = vec![
            InstrNode::new(Inst::Assume { cond: v(0) }),
            InstrNode::new(Inst::Assert { cond: v(0) }),
            InstrNode::new(Inst::Unreachable),
            InstrNode::new(Inst::Copy {
                ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Return { values: vec![] }),
            InstrNode::new(Inst::Return {
                values: vec![v(0), v(1)],
            }),
        ];
        for node in &instructions {
            json_round_trip(node);
            msgpack_round_trip(node);
        }
    }

    // ---- Binding frame instructions (item 4 of TrustIr#30) ----

    #[test]
    fn serde_binding_frame_instructions() {
        use crate::inst::{BindingFrameDef, BindingSlot};
        use crate::value::BindingFrameId;

        let def = BindingFrameDef::new(
            BindingFrameId::new(3),
            "exists_i",
            vec![
                BindingSlot::new("i", Ty::I64),
                BindingSlot::new("flag", Ty::Bool),
            ],
        );
        let instructions: Vec<InstrNode> = vec![
            InstrNode::new(Inst::OpenFrame { def: def.clone() }).with_result(v(10)),
            InstrNode::new(Inst::BindSlot {
                frame: v(10),
                slot: 0,
                value: v(11),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::LoadSlot {
                frame: v(12),
                slot: 1,
                ty: Ty::Bool,
            })
            .with_result(v(13)),
            InstrNode::new(Inst::CloseFrame { frame: v(12) }),
        ];
        for node in &instructions {
            json_round_trip(node);
            msgpack_round_trip(node);
        }
        // Also round-trip the def by itself.
        json_round_trip(&def);
        msgpack_round_trip(&def);
    }

    // ---- Proof annotation variants ----

    #[test]
    fn serde_all_proof_annotation_variants() {
        let annotations = vec![
            ProofAnnotation::InBounds,
            ProofAnnotation::NotNull,
            ProofAnnotation::ValidBorrow,
            ProofAnnotation::UniqueBorrow,
            ProofAnnotation::SharedBorrow,
            ProofAnnotation::ValidDealloc,
            ProofAnnotation::NoOverflow,
            ProofAnnotation::NoWrap,
            ProofAnnotation::DivNonZero,
            ProofAnnotation::ShiftInRange,
            ProofAnnotation::Pure,
            ProofAnnotation::Terminates,
            ProofAnnotation::Deterministic,
            ProofAnnotation::Associative,
            ProofAnnotation::Commutative,
            ProofAnnotation::DataRaceFree,
            ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
            ProofAnnotation::AtomicOrdering(Ordering::Relaxed),
            ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 },
            ProofAnnotation::Monotonic,
            ProofAnnotation::NoAlias,
            ProofAnnotation::Aligned(16),
            ProofAnnotation::Aligned(64),
            ProofAnnotation::NoPanic,
            ProofAnnotation::NoUndef,
            ProofAnnotation::Custom(ProofTag::new(42)),
        ];
        for ann in &annotations {
            json_round_trip(ann);
            msgpack_round_trip(ann);
        }
    }

    // ---- Proof evidence variants ----

    #[test]
    fn serde_all_proof_evidence_variants() {
        let evidences = vec![
            ProofEvidence::SmtProof(vec![0xDE, 0xAD, 0xBE, 0xEF]),
            ProofEvidence::LeanProof("theorem foo : True := trivial".to_string()),
            ProofEvidence::KaniHarness("check_bounds".to_string()),
            ProofEvidence::GammaCrownBound {
                epsilon: 0.001,
                verified_layers: 12,
            },
            ProofEvidence::TranslationValidation {
                rule_name: "inline_expansion".to_string(),
                smt_hash: [0xAB; 32],
            },
            ProofEvidence::Trusted("manual audit 2026-04-16".to_string()),
        ];
        for ev in &evidences {
            json_round_trip(ev);
            msgpack_round_trip(ev);
        }
    }

    #[test]
    fn serde_proof_lineage_manifest_round_trip() {
        let cert = ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![1, 2, 3]),
        };
        let mut node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::SolverAdapter,
                "trust-ir-ay",
                "TrustIr",
                "0.1.0",
            ),
            ProofDigest::sha256([1; 32]),
            ProofDigest::sha256([2; 32]),
        );
        node.obligations.push(ProofId::new(0));
        node.certificates.push(cert.lineage_ref());
        node.replay = Some(
            ProofReplayIdentity::new("stage2-tcargo", "cargo test -p trust-ir-ay")
                .with_transcript_digest(ProofDigest::sha256_domain("serde-test.v1", b"ok")),
        );

        let manifest = ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![node],
            roots: vec![ProofLineageId::new(0)],
        };

        manifest.validate().expect("lineage manifest validates");
        json_round_trip(&manifest);
        msgpack_round_trip(&manifest);
    }

    // ---- Constant types including nested aggregates ----

    #[test]
    fn serde_all_constant_types_json() {
        // Note: JSON does not support Infinity/NaN, so those are tested
        // only via MessagePack below.
        let constants = vec![
            Constant::Int(0),
            Constant::Int(-1),
            Constant::Int(i128::MAX),
            Constant::Int(i128::MIN),
            Constant::Float(0.0),
            Constant::Float(1.25),
            Constant::Float(-2.75),
            Constant::Bool(true),
            Constant::Bool(false),
            Constant::Aggregate(vec![]),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2), Constant::Int(3)]),
        ];
        for c in &constants {
            json_round_trip(c);
            msgpack_round_trip(c);
        }
    }

    #[test]
    fn serde_float_special_values_msgpack() {
        // Infinity and NaN are not representable in JSON but work in MessagePack.
        let special = vec![
            Constant::Float(f64::INFINITY),
            Constant::Float(f64::NEG_INFINITY),
        ];
        for c in &special {
            msgpack_round_trip(c);
        }
        // NaN requires special handling since NaN != NaN
        let nan_bytes = rmp_serde::to_vec(&Constant::Float(f64::NAN)).expect("serialize NaN");
        let nan_back: Constant = rmp_serde::from_slice(&nan_bytes).expect("deserialize NaN");
        match nan_back {
            Constant::Float(v) => assert!(v.is_nan(), "expected NaN"),
            other => panic!("expected Float(NaN), got {:?}", other),
        }
    }

    #[test]
    fn serde_nested_aggregate_constants() {
        let nested = Constant::Aggregate(vec![
            Constant::Aggregate(vec![Constant::Int(1), Constant::Float(2.0)]),
            Constant::Aggregate(vec![
                Constant::Bool(true),
                Constant::Aggregate(vec![Constant::Int(3)]),
            ]),
            Constant::Float(4.0),
        ]);
        json_round_trip(&nested);
        msgpack_round_trip(&nested);
    }

    // ---- All type variants ----

    #[test]
    fn serde_all_type_variants() {
        let types = vec![
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::I128,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::U128,
            Ty::F16,
            Ty::F32,
            Ty::F64,
            Ty::Bool,
            Ty::Ptr,
            Ty::Unit,
            Ty::Never,
            Ty::Struct(StructId::new(0)),
            Ty::Struct(StructId::new(42)),
            Ty::Array(TyId::new(0), 16),
            Ty::Array(TyId::new(5), 0),
            Ty::Tuple(vec![]),
            Ty::Tuple(vec![Ty::I32, Ty::Bool]),
            Ty::Tuple(vec![Ty::U64, Ty::F32, Ty::Never]),
            Ty::Enum(EnumId::new(0)),
            Ty::Enum(EnumId::new(42)),
            Ty::Func(FuncTyId::new(0)),
            Ty::Func(FuncTyId::new(99)),
            Ty::Ref(Box::new(Ty::I32)),
            Ty::RefMut(Box::new(Ty::I64)),
            Ty::PtrConst(Box::new(Ty::U32)),
            Ty::PtrMut(Box::new(Ty::F64)),
            Ty::Rc(Box::new(Ty::Bool)),
            // Nested reference types
            Ty::Ref(Box::new(Ty::RefMut(Box::new(Ty::I32)))),
            Ty::Rc(Box::new(Ty::Tuple(vec![Ty::I32, Ty::U64]))),
        ];
        for ty in &types {
            json_round_trip(ty);
            msgpack_round_trip(ty);
        }
    }

    // ---- Multi-function module ----

    #[test]
    fn serde_multi_function_module() {
        let mut module = Module::new("multi_func");

        // Two function types
        let ft_add = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let ft_main = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let ft_vararg = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: true,
        });

        // Two struct definitions
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Vec2".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F32,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F32,
                    offset: Some(4),
                },
            ],
            size: Some(8),
            align: Some(4),

            repr: Default::default(),
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Pair".to_string(),
            fields: vec![
                FieldDef {
                    name: "first".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
                FieldDef {
                    name: "second".to_string(),
                    ty: Ty::I64,
                    offset: None,
                },
            ],
            size: None,
            align: None,

            repr: Default::default(),
        });

        // Types
        module.add_type(Ty::I32);
        module.add_type(Ty::Array(TyId::new(0), 10));
        module.add_type(Ty::Struct(StructId::new(0)));

        // Globals
        module.globals.push(Global {
            name: "GLOBAL_FLAG".to_string(),
            ty: Ty::Bool,
            mutable: true,
            initializer: Some(Constant::Bool(false)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        module.globals.push(Global {
            name: "CONST_ARRAY".to_string(),
            ty: Ty::Array(TyId::new(0), 3),
            mutable: false,
            initializer: Some(Constant::Aggregate(vec![
                Constant::Int(10),
                Constant::Int(20),
                Constant::Int(30),
            ])),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });

        // Function 1: add
        let mut f_add = Function::new(FuncId::new(0), "add", ft_add, b(0));
        f_add.proofs.push(ProofAnnotation::Pure);
        f_add.proofs.push(ProofAnnotation::Terminates);
        let mut block_add = Block::new(b(0));
        block_add.params.push((v(0), Ty::I32));
        block_add.params.push((v(1), Ty::I32));
        block_add.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::NoOverflow),
        );
        block_add
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f_add.blocks.push(block_add);
        module.add_function(f_add);

        // Function 2: main (calls add, has control flow)
        let mut f_main = Function::new(FuncId::new(1), "main", ft_main, b(0));
        let mut entry_block = Block::new(b(0));
        entry_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            })
            .with_result(v(0)),
        );
        entry_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(20),
            })
            .with_result(v(1)),
        );
        entry_block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        entry_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f_main.blocks.push(entry_block);
        module.add_function(f_main);

        // Function 3: vararg printf-like
        let mut f_va = Function::new(FuncId::new(2), "printf_wrapper", ft_vararg, b(0));
        let mut va_block = Block::new(b(0));
        va_block.params.push((v(0), Ty::Ptr));
        va_block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        va_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        f_va.blocks.push(va_block);
        module.add_function(f_va);

        // Proof obligations and certificates
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "add is panic-free".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(1),
            kind: ObligationKind::MemorySafety,
            status: ProofStatus::Pending,
            description: "main memory safety".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![0x01, 0x02]),
        });

        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    // ---- Control flow with CondBr and Switch ----

    #[test]
    fn serde_module_with_control_flow() {
        let mut module = Module::new("control_flow");

        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut func = Function::new(FuncId::new(0), "abs", ft, b(0));

        // Entry block: compare and branch
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::I32));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        entry.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: v(2),
            then_target: b(1),
            then_args: vec![v(0)],
            else_target: b(2),
            else_args: vec![v(0)],
        }));
        func.blocks.push(entry);

        // Negative block: negate
        let mut neg_block = Block::new(b(1));
        neg_block.params.push((v(3), Ty::I32));
        neg_block.body.push(
            InstrNode::new(Inst::UnOp {
                op: UnOp::Neg,
                ty: Ty::I32,
                operand: v(3),
            })
            .with_result(v(4)),
        );
        neg_block.body.push(InstrNode::new(Inst::Br {
            target: b(2),
            args: vec![v(4)],
        }));
        func.blocks.push(neg_block);

        // Merge block: return
        let mut merge_block = Block::new(b(2));
        merge_block.params.push((v(5), Ty::I32));
        merge_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
        func.blocks.push(merge_block);

        module.add_function(func);

        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn serde_module_with_switch() {
        let mut module = Module::new("switch_demo");

        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut func = Function::new(FuncId::new(0), "classify", ft, b(0));

        // Entry: switch on input
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::I32));
        entry.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(4),
            default_args: vec![],
            cases: vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: b(1),
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: b(2),
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(2),
                    target: b(3),
                    args: vec![],
                },
            ],
            exhaustive_enum_unreachable: false,
        }));
        func.blocks.push(entry);

        // Case blocks: each returns a different constant
        for (i, block_idx) in [1u32, 2, 3, 4].iter().enumerate() {
            let mut block = Block::new(b(*block_idx));
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int((i as i128 + 1) * 100),
                })
                .with_result(v(*block_idx + 10)),
            );
            block.body.push(InstrNode::new(Inst::Return {
                values: vec![v(*block_idx + 10)],
            }));
            func.blocks.push(block);
        }

        module.add_function(func);

        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    // ---- InstrNode with all metadata (results, proofs, span) ----

    #[test]
    fn serde_instr_node_with_full_metadata() {
        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2))
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::NoWrap)
        .with_proof(ProofAnnotation::BoundedOutput { lo: 0.0, hi: 100.0 })
        .with_span(SourceSpan {
            file: 1,
            line: 42,
            col: 10,
        });

        json_round_trip(&node);
        msgpack_round_trip(&node);
    }

    // ---- JSON schema documentation: verify key field names ----

    #[test]
    fn json_field_names_documented() {
        let module = Module::new("schema_test");
        let json = serde_json::to_string_pretty(&module).expect("serialize");

        // Verify top-level Module field names
        assert!(json.contains("\"name\""));
        assert!(json.contains("\"functions\""));
        assert!(json.contains("\"structs\""));
        assert!(json.contains("\"globals\""));
        assert!(json.contains("\"func_types\""));
        assert!(json.contains("\"types\""));
        assert!(json.contains("\"proof_obligations\""));
        assert!(json.contains("\"proof_certificates\""));
    }

    #[test]
    fn json_function_field_names() {
        let mut module = Module::new("fn_schema");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "test_fn", ft, b(0));
        func.proofs.push(ProofAnnotation::Pure);
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1))
            .with_span(SourceSpan {
                file: 0,
                line: 1,
                col: 0,
            }),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module.add_function(func);

        let json = serde_json::to_string_pretty(&module).expect("serialize");

        // Function fields
        assert!(json.contains("\"id\""));
        assert!(json.contains("\"name\""));
        assert!(json.contains("\"ty\""));
        assert!(json.contains("\"entry\""));
        assert!(json.contains("\"blocks\""));
        assert!(json.contains("\"proofs\""));

        // Block fields
        assert!(json.contains("\"params\""));
        assert!(json.contains("\"body\""));

        // InstrNode fields
        assert!(json.contains("\"inst\""));
        assert!(json.contains("\"results\""));
        assert!(json.contains("\"span\""));

        // SourceSpan fields
        assert!(json.contains("\"file\""));
        assert!(json.contains("\"line\""));
        assert!(json.contains("\"col\""));
    }

    #[test]
    fn json_proof_obligation_field_names() {
        let obligation = ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::MemorySafety,
            status: ProofStatus::Pending,
            description: "test".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        };
        let json = serde_json::to_string_pretty(&obligation).expect("serialize");
        assert!(json.contains("\"id\""));
        assert!(json.contains("\"kind\""));
        assert!(json.contains("\"status\""));
        assert!(json.contains("\"description\""));
    }

    // ---- Proof obligation/certificate round-trips ----

    #[test]
    fn serde_all_obligation_kinds() {
        let kinds = vec![
            ObligationKind::Precondition,
            ObligationKind::Postcondition,
            ObligationKind::LoopInvariant,
            ObligationKind::TypeInvariant,
            ObligationKind::RefinementType,
            ObligationKind::TranslationValidation,
            ObligationKind::MemorySafety,
            ObligationKind::PanicFreedom,
            ObligationKind::TemporalSafety,
            ObligationKind::Liveness,
            ObligationKind::ArithmeticSafety,
            ObligationKind::BoundsCheck,
            ObligationKind::GiveBackRefinement,
        ];
        for kind in &kinds {
            json_round_trip(kind);
            msgpack_round_trip(kind);
        }
    }

    #[test]
    fn serde_all_proof_statuses() {
        let statuses = vec![
            ProofStatus::Pending,
            ProofStatus::Discharged,
            ProofStatus::Failed,
            ProofStatus::Trusted,
            ProofStatus::Certified,
        ];
        for status in &statuses {
            json_round_trip(status);
            msgpack_round_trip(status);
        }
    }

    // ---- Edge cases ----

    #[test]
    fn serde_empty_module() {
        let module = Module::new("empty");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn serde_global_without_initializer() {
        let global = Global {
            name: "uninit".to_string(),
            ty: Ty::I64,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
        };
        json_round_trip(&global);
        msgpack_round_trip(&global);
    }

    #[test]
    fn serde_non_tls_global_round_trips_and_accepts_legacy_json() {
        let global = Global {
            name: "ordinary".to_string(),
            ty: Ty::I64,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
        };

        // `tls`/`align` use `serde(default)` (NOT `skip_serializing_if`) so they
        // keep a STABLE array position under rmp-serde's compact encoding — see the
        // field docs. So a non-TLS global's JSON legitimately carries `"tls": null`;
        // what matters is that it round-trips and that a legacy payload lacking the
        // fields still decodes to `None` (the `default`).
        let json = serde_json::to_string_pretty(&global).expect("serialize");
        let round: Global = serde_json::from_str(&json).expect("round-trip");
        assert_eq!(round, global);

        let legacy_json = r#"{
  "name": "ordinary",
  "ty": "I64",
  "mutable": false,
  "initializer": null,
  "linkage": "External"
}"#;
        let back: Global = serde_json::from_str(legacy_json).expect("deserialize legacy Global");
        assert_eq!(back, global);
    }

    #[test]
    fn serde_tls_global_round_trip() {
        let global = Global {
            name: "thread_counter".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::Internal,
            tls: Some(TlsModel::LocalExec),
            align: None,
        };

        let json = serde_json::to_string_pretty(&global).expect("serialize");
        assert!(json.contains("\"tls\""));
        let back: Global = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back.tls, Some(TlsModel::LocalExec));

        msgpack_round_trip(&global);
    }

    #[test]
    fn serde_struct_def() {
        let sd = StructDef {
            id: StructId::new(0),
            name: "Empty".to_string(),
            fields: vec![],
            size: None,
            align: None,

            repr: Default::default(),
        };
        json_round_trip(&sd);
        msgpack_round_trip(&sd);
    }

    #[test]
    fn serde_func_ty_vararg() {
        let ft = FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![],
            is_vararg: true,
        };
        json_round_trip(&ft);
        msgpack_round_trip(&ft);
    }

    #[test]
    fn serde_source_span() {
        let span = SourceSpan {
            file: 0,
            line: u32::MAX,
            col: 0,
        };
        json_round_trip(&span);
        msgpack_round_trip(&span);
    }

    #[test]
    fn serde_all_typed_ids() {
        json_round_trip(&ValueId::new(0));
        json_round_trip(&ValueId::new(u32::MAX));
        json_round_trip(&BlockId::new(42));
        json_round_trip(&FuncId::new(7));
        json_round_trip(&StructId::new(99));
        json_round_trip(&TyId::new(1));
        json_round_trip(&FuncTyId::new(3));
        json_round_trip(&ProofId::new(0));
        json_round_trip(&ProofTag::new(100));

        msgpack_round_trip(&ValueId::new(0));
        msgpack_round_trip(&BlockId::new(42));
        msgpack_round_trip(&FuncId::new(u32::MAX));
        json_round_trip(&EnumId::new(0));
        json_round_trip(&EnumId::new(u32::MAX));
        msgpack_round_trip(&EnumId::new(42));
    }

    #[test]
    fn serde_enum_def() {
        let ed = EnumDef {
            id: EnumId::new(0),
            name: "Option".to_string(),
            variants: vec![
                EnumVariant {
                    name: "None".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Some".to_string(),
                    fields: vec![Ty::I32],
                    field_names: vec!["value".to_string()],
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Direct { tag_offset: 4 },
                size: 8,
                align: 4,
                variant_field_offsets: vec![vec![], vec![0]],
            }),
        };
        json_round_trip(&ed);
        msgpack_round_trip(&ed);
    }

    #[test]
    fn serde_enum_def_with_complex_variants() {
        let ed = EnumDef {
            id: EnumId::new(1),
            name: "Result".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Ok".to_string(),
                    fields: vec![Ty::Tuple(vec![Ty::I32, Ty::Bool])],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Err".to_string(),
                    fields: vec![Ty::Ref(Box::new(Ty::U8))],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
        };
        json_round_trip(&ed);
        msgpack_round_trip(&ed);
    }

    #[test]
    fn serde_enum_def_with_discriminants_and_repr() {
        // Canonical-layout fields survive JSON and positional MessagePack:
        // explicit + implicit discriminant mix, negative values, and a tag
        // repr hint. `formula`-style positional hazards are avoided because
        // `discriminants` is always emitted (only trailing `repr` could skip).
        let ed = EnumDef::new(
            EnumId::new(2),
            "Sparse",
            vec![
                EnumVariant {
                    name: "A".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "B".to_string(),
                    fields: vec![Ty::I64],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "C".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
        )
        .with_discriminants(vec![Some(-5), None, Some(i64::MAX as i128)])
        .with_repr(EnumTagRepr::I64);
        assert_eq!(
            ed.effective_discriminants(),
            Some(vec![-5, -4, i64::MAX as i128])
        );
        assert_eq!(ed.canonical_tag_repr(), Some(EnumTagRepr::I64));
        json_round_trip(&ed);
        msgpack_round_trip(&ed);
    }

    #[test]
    fn serde_reference_types_round_trip() {
        let types = vec![
            Ty::Ref(Box::new(Ty::I32)),
            Ty::RefMut(Box::new(Ty::U64)),
            Ty::PtrConst(Box::new(Ty::F32)),
            Ty::PtrMut(Box::new(Ty::Bool)),
            Ty::Rc(Box::new(Ty::Struct(StructId::new(0)))),
            // Nested references
            Ty::Ref(Box::new(Ty::Ref(Box::new(Ty::I32)))),
            Ty::Rc(Box::new(Ty::Tuple(vec![Ty::U32, Ty::U64]))),
        ];
        for ty in &types {
            json_round_trip(ty);
            msgpack_round_trip(ty);
        }
    }

    #[test]
    fn serde_tuple_types_round_trip() {
        let tuples = vec![
            Ty::Tuple(vec![]),
            Ty::Tuple(vec![Ty::I32]),
            Ty::Tuple(vec![Ty::I32, Ty::Bool, Ty::U64]),
            Ty::Tuple(vec![Ty::Tuple(vec![Ty::I32, Ty::I64]), Ty::F64]),
        ];
        for ty in &tuples {
            json_round_trip(ty);
            msgpack_round_trip(ty);
        }
    }

    #[test]
    fn serde_module_with_enums() {
        let mut module = Module::new("enum_test");
        module.add_enum(EnumDef {
            id: EnumId::new(0),
            name: "Color".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Red".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Green".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Blue".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
        });
        module.add_type(Ty::Enum(EnumId::new(0)));
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn serde_dialect_op_round_trip() {
        use crate::dialect::{AttrValue, DialectInst};
        use crate::inst::Inst;
        use crate::node::InstrNode;

        let mut module = Module::new("serde_dialect");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I64));

        let op = DialectInst::new("verif", "bfs_step")
            .with_operand(v(0))
            .with_operand(v(1))
            .with_result_ty(Ty::Ptr)
            .with_attr("parallel", AttrValue::Bool(true))
            .with_attr("delta", AttrValue::I64(-9))
            .with_attr("size", AttrValue::U64(2048))
            .with_attr("weight", AttrValue::F64(2.75))
            .with_attr("label", AttrValue::Str("hot".to_string()))
            .with_attr("blob", AttrValue::Bytes(vec![0x00, 0xff, 0x10]))
            .with_attr("elem_ty", AttrValue::Ty(Ty::I32))
            .with_version(2);
        let mut node = InstrNode::new(Inst::DialectOp(Box::new(op)));
        node.results = vec![v(2)];
        block.body.push(node);
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module.add_function(func);

        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn serde_dialect_inst_standalone_round_trip() {
        use crate::dialect::{AttrValue, DialectInst};
        let op = DialectInst::new("verif", "fingerprint_batch")
            .with_operand(v(0))
            .with_operand(v(1))
            .with_result_ty(Ty::Ptr)
            .with_attr("batch", AttrValue::U64(64));
        json_round_trip(&op);
        msgpack_round_trip(&op);
    }
}
