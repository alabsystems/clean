// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

pub mod semr_bool_body;

use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "fmt")]
use std::collections::{HashMap, HashSet};

// Declared first: `variant_shape!` is textually scoped, and `inst` / `proof`
// use it to generate their `Copy` shape projections.
#[macro_use]
mod variant_shape;

pub mod alloc_bound;
pub mod analysis;
pub mod blob;
pub mod bridge;
pub mod build_info;
pub mod bv_meaning;
mod canonicalize;
pub mod clean_boxed_u32;
pub mod closure_storage;
/// Format identification (`sniff_format`): zero-dep byte checks shared by the CLIs.
pub mod codec;
pub mod conditional_facts;
pub mod constant;
pub mod dialect;
pub mod display;
pub mod effects;
mod func_ty_equality_observed;
pub mod function_dependencies;
pub mod imports;
mod inhabit;
pub use inhabit::Inhabitedness;
pub mod inst;
pub mod interpret;
pub mod layout_table;
pub mod level;
pub mod mem2reg;
mod module_aggregate_slot_observed;
mod module_catalog_observed;
mod module_catalog_queries_observed;
mod module_drop_glue_observed;
pub use module_drop_glue_observed::ObservedDropGlueIndex;
pub mod node;
pub mod pred;
pub mod proof;
/// Forward, sound, decidable propagation over the [`pred`] lattice.
pub mod propagate;
mod reach;
pub use reach::ByValueStorageQuery;
pub mod request;
pub mod shape;
pub mod signature_abi;
pub mod storage;
pub mod storage_usage;
pub use storage::StorageLayout;
pub use storage_usage::{StorageSite, StorageViolation, StorageViolationKind};
mod source_provenance_observed;
pub mod spec;
pub mod spec_proof;
pub mod spec_surface;
pub mod template;
pub mod text_directives;
pub mod text_loss;
pub mod ty;
mod type_reachability;
mod type_walk;
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
pub use build_info::{BUILD_IDENTITY, BuildIdentity, SourceAttestation};
pub use constant::{Constant, ConstantG};
pub use dialect::{
    AttrEntry, AttrValue, Dialect, DialectError, DialectInst, DialectRegistry, LoweringPass,
    LoweringResult, RewriteOutcome,
};
pub use effects::{EffectPlace, EffectSet, EffectSummary};
pub use imports::{
    ExternRefSite, HashedModule, IdentityScheme, ImportVerificationError, MODULE_IDENTITY_DOMAIN,
    MODULE_IDENTITY_DOMAIN_V2, ResolvedExternRef, VerifiedImport, signatures_compatible,
    ty_structurally_eq_across,
};
pub use inst::{
    AssertKind, AssertOverflowOp, AtomicRMWOp, BinOp, CallShape, CallTarget, CallUnwindDisposition,
    CastOp, Edge, EdgeKind, FCmpOp, ICmpOp, Inst, InstG, InstShape, Ordering, OverflowOp,
    PanicLocation, PanicSite, SwitchCase, TensorIndexExpr, TensorMapNode, TensorReduceOp,
    TensorReduceOrder, UnOp, tensor_view_index_phase,
};
pub use interpret::{
    ArrayValue, HostCalls, HostRcOp, HostRcRole, HostState, InterpretError, InterpretErrorCode,
    InterpretInt, InterpretOptions, InterpretOutcome, InterpretPanic, InterpretPanicSite,
    InterpretResult, InterpretValue, InterpretValueKind, Interpreter, PanicLocationValue,
};
// Re-export new types added for TrustIr backend requirements (issue #26)
// CallingConv, Linkage, Endianness, TargetInfo are defined below in this file.
pub use level::{Extension, NoExt, TemplateRef};
pub use node::{InstrNode, InstrNodeG};
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
    CertificateBinding, CleanCicKernelRecheck, CleanCicModuleProofAuthority,
    CleanCicProofAuthorityRechecker, CleanCicRechecker, DiagnosticSeverity, Divergence,
    KernelClaimFamily, LINEAGE_TRANSFORM_BINDING_SCHEMA, LineageAppendError, LineageGap,
    ModuleCleanCicRechecker, ObligationDiagnostic, ObligationKind, ObligationKindShape,
    ObligationSite, PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES, ProofAnnotation,
    ProofAnnotationFilters, ProofAuthorityRechecker, ProofCertificate, ProofCertificateRef,
    ProofDigest, ProofDigestAlgorithm, ProofDigestSha256DomainStream, ProofDigestStreamError,
    ProofEvidence, ProofEvidenceShape, ProofFormula, ProofLineageError, ProofLineageId,
    ProofLineageManifest, ProofLineageNode, ProofObligation, ProofObligationSourceIdentity,
    ProofObligationSourceRange, ProofReplayIdentity, ProofStatus, ProofSummary, ProofTransform,
    ProofTransformStage, PublicObligationIdentity, RejectingCleanCicRechecker,
    RejectingProofAuthorityRechecker, SourceDefinitionRef, clean_cic_lineage_digest,
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
/// The writer's refusal, reachable in every feature configuration (the
/// `binary` module itself is public only under the `binary` feature), so
/// [`Module::wire_image_refusal`] can name it.
pub use binary::{BinaryProjectionError, WireNodeSite};
pub use layout_table::{LayoutMemo, LayoutTable, LayoutTableStats};
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
    CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY, CHC_X86_ICMP_CERTIFICATE_RULE,
    CHC_X86_ICMP_INSTRUCTION_MODEL_OPERATIONS, CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY,
    CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_OPERATIONS, CHC_X86_V8_I16_MASK_TO_BITS_COMPOSITION,
    CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS, CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_OPERATIONS, CHC_X86_V16_I8_MASK_TO_BITS_COMPOSITION,
    CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS, ChcX86IcmpCertificateRule, ChcX86IcmpCertifyingBuild,
    ChcX86IcmpGround, ChcX86VectorIcmpCell, HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA,
    HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION, HARDWARE_VECTOR_CONTRACT_REASON_CODES,
    HARDWARE_VECTOR_CONTRACT_SCHEMA, HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION,
    HARDWARE_VECTOR_CONTRACT_STATUS_CODES, HardwareVectorContractDescriptor,
    HardwareVectorContractReason, HardwareVectorContractStatus,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR, NATIVE_BUNDLE_IDENTITY_CONTRACT_DIGEST_CONTEXTS,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS, NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA,
    NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA_VERSION, NATIVE_COVERAGE_ATTESTATION_DIGEST_DOMAIN,
    NATIVE_COVERAGE_ATTESTATION_SCHEMA_VERSION, NATIVE_COVERAGE_REPLAY_CONTEXT_DIGEST_DOMAIN,
    NATIVE_EVIDENCE_ARTIFACT_ATTACHMENT_SCHEMA, NATIVE_EVIDENCE_ARTIFACT_ATTACHMENT_SCHEMA_VERSION,
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
    NativeCompilerFacts, NativeCoverageAttestation, NativeCoverageAttestationError,
    NativeCoverageAttestationRow, NativeCoverageReplayInconclusive, NativeCoverageReplayRefusal,
    NativeCoverageResultReplay, NativeDiagnosticLevel, NativeDiagnosticsPolicy,
    NativeEnumLayoutFact, NativeEnumNicheFact, NativeEnumTagEncoding, NativeEnumVariantLayoutFact,
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
    NativeReplayContext, NativeReplayContextDigest, NativeReplayContextUnavailable,
    NativeReplayedResult, NativeReplayedStrength, NativeRequestDigestIdentity, NativeRequestId,
    NativeRequestProvenance, NativeSemanticBridge, NativeSemanticBridgeEvidenceStatus,
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
    TySharedPrimitiveManifestReason, TySharedPrimitiveManifestStatus, ValidatedNativeBundle,
    chc_x86_hardware_vector_contract_descriptors, chc_x86_hardware_vector_contract_manifest_digest,
    chc_x86_hardware_vector_contract_manifest_key_value_lines,
    chc_x86_hardware_vector_contract_manifest_key_value_text,
    chc_x86_hardware_vector_contract_manifest_row_count,
    chc_x86_hardware_vector_contract_manifest_rows,
    chc_x86_hardware_vector_contract_manifest_sha256, chc_x86_vector_icmp_cell_ground,
    chc_x86_vector_icmp_cell_status, chc_x86_vector_icmp_lowering_row, chc_x86_vector_icmp_spec,
    native_bundle_identity_contract_descriptor, native_evidence_artifact_authority_row_descriptor,
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
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_sha256, physical_mask_lane,
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
    KernelCertifiedTheorems, ProofKind, SpecAnchor, SpecCoverage, SpecEnforcementMode,
    SpecInvariant, SpecLinkOptions, SpecLinkReport, SpecLinkViolation, SpecModule,
    SpecNonCertificationReason, SpecOrigin, SpecProjectionTarget, SpecProof, SpecTemporal, SpecVar,
    SpecWaiver, TEMPORAL_FIELD_PATH_PROJECTION_V1, TemporalForm, link_spec_modules,
    link_spec_modules_with_theorems, validate_clean_theorem_bindings, validate_linked_spec_surface,
    validate_spec_executable_links, validate_spec_executable_links_observed,
    validate_spec_structure, validate_spec_structure_observed,
};
pub use spec_proof::{HarnessEntry, HarnessManifest, HarnessManifestError, link_proofs};
pub use ty::{
    ClosureTy, DialectTy, DialectTyError, EnumDef, EnumDefG, EnumLayoutDescriptor, EnumTagEncoding,
    EnumTagRepr, EnumVariant, EnumVariantG, FatPtrKind, FieldDef, FieldDefG, FuncTy, FuncTyG,
    HandleTy, HandleTyError, RecordDef, SetRepr, StructDef, StructDefG, StructRepr, Ty, TyG,
    stable_trait_object_id, stable_vtable_global_name,
};
pub use type_reachability::{
    CallableCarriers, DialectTypeReachability, NominalTypeReachability,
    ObservedNominalTypeReachability,
};
pub use value::{
    BlockId, ClosureTyId, EnumId, FreshIds, FuncId, FuncTyId, HoleId, IdRun, IdSpaceExhausted,
    ImportId, InlinedAt, ParamId, PredId, ProofId, ProofTag, RecordId, ScopeData, SourceSpan,
    StructId, TyId, TypedId, UnivId, ValueId,
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
    /// Rust `extern "C-unwind"` (v45, roadmap WS3.12 / F-059): the C
    /// convention on a function that MAY unwind across the boundary. Under the
    /// ratified panic=abort policy (`docs/ub-numerics-policy.md` §4) this is
    /// RECORDED, never given unwind semantics: the consumer must not treat it
    /// as plain `C` when it matters (an unwind table), and nothing here models
    /// an unwind. Must-refuse corpus row
    /// `refuse/calling_conv_c_unwind_definition`: a definition with this
    /// convention is well-formed here, and a consumer that would lower it as
    /// `C` must refuse it instead.
    CUnwind,
    /// `extern "sysv64"`: the System V AMD64 convention, explicitly (v45).
    SysV64,
    /// `extern "win64"`: the Microsoft x64 convention, explicitly (v45).
    Win64,
    /// `extern "aapcs"`: the 32-bit Arm AAPCS convention (v45).
    Aapcs,
    /// `extern "efiapi"`: the UEFI convention (v45).
    EfiApi,
    /// `extern "vectorcall"`: the x86 vector-register convention (v45).
    VectorCall,
    /// `extern "rust-cold"`: Rust's cold-path convention (v45).
    RustCold,
    // No `Other(String)` escape, deliberately (WS3.12): it would break
    // `Copy`, and a foreign ABI this enum cannot name must be a PRODUCER
    // refusal, never an opaque string a consumer lowers as C.
}

impl CallingConv {
    /// True for the conventions added in wire v45 (WS3.12). The binary
    /// writer selects v45 exactly when one of these occurs.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::cc_abi_surface_*` (gate 13).
    #[must_use]
    pub fn is_abi_surface(self) -> bool {
        matches!(
            self,
            CallingConv::CUnwind
                | CallingConv::SysV64
                | CallingConv::Win64
                | CallingConv::Aapcs
                | CallingConv::EfiApi
                | CallingConv::VectorCall
                | CallingConv::RustCold
        )
    }

    /// Every convention, in wire-tag order. The text parser resolves a token
    /// through this list and [`core::fmt::Display`], so the two spellings
    /// cannot drift.
    pub const ALL: [CallingConv; 12] = [
        CallingConv::C,
        CallingConv::Fast,
        CallingConv::Cold,
        CallingConv::Rust,
        CallingConv::Swift,
        CallingConv::CUnwind,
        CallingConv::SysV64,
        CallingConv::Win64,
        CallingConv::Aapcs,
        CallingConv::EfiApi,
        CallingConv::VectorCall,
        CallingConv::RustCold,
    ];
}

impl core::fmt::Display for CallingConv {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            CallingConv::C => "ccc",
            CallingConv::Fast => "fastcc",
            CallingConv::Cold => "coldcc",
            CallingConv::Rust => "rustcc",
            CallingConv::Swift => "swiftcc",
            CallingConv::CUnwind => "c_unwindcc",
            CallingConv::SysV64 => "sysv64cc",
            CallingConv::Win64 => "win64cc",
            CallingConv::Aapcs => "aapcscc",
            CallingConv::EfiApi => "efiapicc",
            CallingConv::VectorCall => "vectorcallcc",
            CallingConv::RustCold => "rust_coldcc",
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
    /// Available for inlining but never emitted; the definition lives
    /// elsewhere (LLVM `available_externally`). v41.
    ///
    /// A consumer emits no body for it and binds every use to the symbol. It
    /// MAY splice the body into a direct call instead of calling the symbol
    /// (an inline-only body: a runtime helper's fast path shipped beside its
    /// one out-of-line definition). Doing so rests on the one-definition-rule
    /// premise that the body computes what the definition the symbol binds to
    /// computes, which nothing in this module can check. A consumer that makes
    /// a proof claim about what it compiled therefore must not splice such a
    /// body unless a `Module.imports` dependency authenticated by
    /// [`Module::verify_import`] exports a structurally equal definition; it
    /// keeps the call (and still compiles the module). Must-refuse corpus row
    /// `refuse/available_externally_inline_unauthenticated` is the `none` row
    /// for this obligation: a semantics-preservation premise with no refusable
    /// module, whose rung is the consumer's own test.
    AvailableExternally,
    /// A weak DECLARATION: resolves to null rather than failing the link when
    /// no definition exists (LLVM `extern_weak`). v41.
    ///
    /// Body-less, it is an import exactly like a body-less [`Linkage::External`]
    /// function (validator declaration rule, FFI boundary for
    /// [`Module::first_ffi_boundary`]), except that its address is NULLABLE:
    /// see [`Function::is_weak_declaration`] for the spellings the validator
    /// admits. (A body-less `AvailableExternally` is NOT a declaration: that
    /// linkage is by definition a copy of a body.) Must-refuse corpus rows
    /// `refuse/extern_weak_direct_call` (a direct `Call` of the declaration)
    /// and `refuse/extern_weak_as_fn_def` (a `Constant::FnDef` of it) pin the
    /// two spellings the validator refuses.
    ExternalWeak,
    /// `Weak` under the one-definition rule: all copies are known equivalent,
    /// so the linker may drop duplicates (LLVM `weak_odr`). v41.
    WeakOdr,
    /// `LinkOnce` under the one-definition rule (LLVM `linkonce_odr`). v41.
    LinkOnceOdr,
}

impl Linkage {
    /// Whether this linkage lets the linker bind a DIFFERENT definition than
    /// the one a module carries (or none): `Weak`, `LinkOnce` and
    /// `ExternalWeak`.
    ///
    /// Exhaustive on purpose — a linkage added later must be classified here
    /// rather than admitted by a wildcard arm. `WeakOdr` / `LinkOnceOdr` /
    /// `AvailableExternally` are NOT interposable under the
    /// one-definition-rule premise (every copy is the same definition), which
    /// is disclosed, not verified. Import authentication refuses an
    /// interposable site on either end of a proof-bearing edge
    /// ([`ImportVerificationError::InterposableFarSite`], WS8.14), and
    /// trust-ir-build's WS3.8 rule refuses a non-null pointer constant into an
    /// interposable global (`PointerConstantRefusal::InterposableLinkage`);
    /// both read this table.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::interposable_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_interposable(self) -> bool {
        match self {
            Linkage::Weak | Linkage::LinkOnce | Linkage::ExternalWeak => true,
            Linkage::External
            | Linkage::Internal
            | Linkage::Private
            | Linkage::AvailableExternally
            | Linkage::WeakOdr
            | Linkage::LinkOnceOdr => false,
        }
    }

    /// Whether a symbol of this linkage is MODULE-LOCAL — `Internal` or
    /// `Private` — and so is neither exported to nor importable by another
    /// module. Its negation is "exported": import authentication refuses a
    /// module-local far symbol (`ImportVerificationError::SymbolNotExported`),
    /// the linked walk's export index skips one, and a module-local function
    /// may not claim `Hidden`/`Protected` visibility
    /// (`ContradictoryFunctionVisibility`, `trust_ir_laws::visibility_contradicts_linkage`).
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::module_local_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_module_local(self) -> bool {
        matches!(self, Linkage::Internal | Linkage::Private)
    }

    /// Whether this linkage is one of the four v41 additions
    /// (`AvailableExternally`, `ExternalWeak`, `WeakOdr`, `LinkOnceOdr`), so a
    /// function or global carrying it selects the v41 contract-surface wire
    /// version. The binary writer selects v41 through this table.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::contract_surface_linkage_*`
    /// (gate 13).
    #[inline]
    #[must_use]
    pub const fn requires_contract_surface(self) -> bool {
        matches!(
            self,
            Linkage::AvailableExternally
                | Linkage::ExternalWeak
                | Linkage::WeakOdr
                | Linkage::LinkOnceOdr
        )
    }
}

/// Symbol visibility (v41) — orthogonal to [`Linkage`].
///
/// Linkage answers "may another module define this?"; visibility answers "may
/// another module SEE it once linked". Consumers that conflate the two cannot
/// express a hidden-but-external symbol, which is the whole staticlib/cdylib
/// boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Visibility {
    /// Normal, externally visible (ELF `STV_DEFAULT`). The legacy value.
    #[default]
    Default,
    /// Not visible outside the linked image (ELF `STV_HIDDEN`).
    Hidden,
    /// Visible, but never preemptible (ELF `STV_PROTECTED`).
    Protected,
}

impl core::fmt::Display for Visibility {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Visibility::Default => "default",
            Visibility::Hidden => "hidden",
            Visibility::Protected => "protected",
        })
    }
}

impl core::fmt::Display for Linkage {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Linkage::External => "external",
            Linkage::AvailableExternally => "available_externally",
            Linkage::ExternalWeak => "external_weak",
            Linkage::WeakOdr => "weak_odr",
            Linkage::LinkOnceOdr => "linkonce_odr",
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
/// | `Clean`    | `Clean` (bundle schema 8, WS4.16) | `"Clean"` |
/// | `TrustIr`  | `TrustIr`              | `"TrustIr"`|
/// | `TSwift`   | `TSwift` (deprecated)  | `"tSwift"` |
/// | `TC`       | `TC` (deprecated)      | `"tC"`     |
/// | `Other(_)` | (none — escape hatch)  | `"Other"`  |
///
/// A bundle over a module must also COVER every function's `Producer` with
/// its declared language set — the total map is
/// [`request::facts::NativeSourceLanguage::candidates_for_producer`], and
/// `None` is covered only by an explicit `Unknown` member.
///
/// Like `CallingConv`/`Linkage`, this is claim-style provenance metadata: it
/// has no operational semantics and carries no proof obligation. Its consumers
/// are diagnostics (WS3), the cert cache (WS4), and lineage closure reporting
/// (WS7). Since 2026-10-08 it also selects ONE well-formedness rule: a
/// function stamped [`Producer::TRust`] carries no `Borrow` / `BorrowMut` /
/// `EndBorrow` (`docs/SPEC_RATIFICATIONS.md`, "A Rust reference carries no
/// permission instruction"; `ValidationError::RustReferenceAsPermissionBorrow`
/// in `trust-ir-build`). Being claim metadata, the stamp catches a producer
/// regression, not an adversary.
///
/// In particular the `clean_backend_tv` kernel anchor is PRODUCER-AGNOSTIC
/// (ratified 2026-09-18, finding F-016, option A): its re-check proves that the
/// emitted body denotes the recorded comparand, whatever `producer` says, so
/// relabelling a certified function's producer neither earns nor forfeits its
/// `Certified` status. What binds a certificate to identity is the call-edge
/// composition rule (every call bound to the callee actually called and to that
/// callee's own kernel TV) and, once it lands, comparand↔source binding — never
/// this field.
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

/// The machine-checkable CODEGEN LICENSE for a function body (binary v41).
///
/// The two-language design of record forbids codegen consumption of a
/// below-tier function body and names an in-band "ungated-body" attribute as
/// the refusal hook consumers must honor. This is that hook, in-band and
/// typed — rather than a JSON substring inside a `SpecInvariant` formula
/// string, which no consumer can be expected to parse.
///
/// # Three states, and why `Option` carries one of them
///
/// [`Function::body_gate`] is `Option<BodyGate>`, and the `None` is
/// load-bearing:
///
/// * `None` — NO LICENSING CLAIM IS MADE. Every v38-and-older blob decodes to
///   this, as does any producer outside the licensing regime. It is the
///   GRANDFATHER state: a consumer may permit it, because refusing it would
///   refuse every module written before v41. It is **not** `Ungated`.
/// * `Some(BodyGate::Ungated)` — an AFFIRMATIVE claim that no gate was applied
///   to this body. A codegen consumer MUST REFUSE it.
/// * `Some(BodyGate::Gated { authority })` — the body passed the gate owned by
///   `authority`. A consumer may proceed only if it RECOGNIZES `authority`; an
///   unrecognized authority is a refusal, never a pass. Some authorities are
///   also BOUND TO EVIDENCE the module must carry (`trust-ir-build`'s
///   `EVIDENCE_BOUND_GATE_AUTHORITIES`: `clean-kernel-tv` requires exactly one
///   kernel-rechecked `clean_backend_tv` certificate scoped to the function),
///   and a `Failed` TranslationValidation / Postcondition / Precondition row
///   scoped to the function revokes any `Gated` license; the codegen
///   validator enforces both.
///
/// # Evidence (binary v61, roadmap WS1.12(c) / WS6.7(b))
///
/// `Gated` may carry [`GateEvidence`]: the obligation the license rests on and
/// [`Module::function_body_digest`] of the body it was granted to. A present
/// evidence is never taken on faith — `trust-ir-build` requires the obligation
/// to be a `Certified` `TranslationValidation` row scoped to THIS function and
/// the digest to recompute equal (`GatedEvidenceMismatch`), so a license
/// stamped on one body and left on a rewritten one is refused. `None` is NO
/// EVIDENCE RECORDED (every pre-v61 license), refused only under a policy
/// that requires evidence for an evidence-bound authority. A transform that
/// rewrites a licensed body must drop the evidence (or the whole license); a
/// body digest that survives a rewrite would name the old body.
///
/// `None` and `Ungated` must never be conflated by any codec, fingerprint or
/// digest: the first permits and the second refuses. That distinction is why
/// the wire tag is three-valued rather than a presence byte over two states —
/// a v41 blob has to be able to spell "no claim", or re-serializing a decoded
/// legacy module would silently upgrade it into an affirmative refusal.
///
/// # Producer conformance rule (checked on the decoded-provenance path)
///
/// A v41-or-later producer MUST emit `Ungated` or `Gated` for every function
/// WITH A BODY. Wire tag `0` (`None`) at v41+ is admitted on a bodyless
/// declaration only, which produces no code and needs no license.
///
/// This is checkable, because the decoder need not drop the header version:
/// `binary::deserialize_module_with_wire_version` returns the declared
/// version beside the module as a `binary::WireVersion` — a type only the
/// decoder can mint, so the version it reports is one a blob actually
/// declared — and `trust_ir_build::validate_module_as_decoded` refuses, by
/// name (`ValidationError::ProducerOmittedBodyGate`), a bodied `None` in a
/// blob whose header is v41 or later, and grandfathers it below v41.
///
/// # Must-refuse corpus
///
/// Each rule above is pinned as a wire artifact a consumer must refuse
/// (`crates/trust-ir-conformance/tests/fixtures/refuse/MANIFEST.tsv`, run by
/// `trust_ir_conformance::refuse`): `refuse/body_gate_ungated` (the
/// affirmative `Ungated`), `refuse/body_gate_unknown_authority` (an authority
/// no consumer recognizes; refused once the consumer names its recognized
/// set), `refuse/body_gate_kernel_tv_without_certificate` (the evidence-bound
/// authority worn without its certificate),
/// `refuse/body_gate_refuted_by_failed_tv` (a `Failed` TranslationValidation
/// row revokes the license), `refuse/body_gate_evidence_stale_body_digest` (a
/// license's [`GateEvidence`] naming another body's digest),
/// `refuse/body_gate_kernel_tv_evidence_unrecorded` (an evidence-bound license
/// with no evidence, refused under the evidence policy) and
/// `refuse/body_gate_omitted_at_contract_surface`
/// (a bodied `None` in a v41+ blob: refused by the decoded-provenance layer as
/// the producer's fault, and by the codegen gate's fail-closed default as an
/// unlicensed body — a grandfathering consumer permits the second by name).
/// `trust-ir validate` applies it to every binary input, `--link`
/// dependencies included, and states, for text / JSON / MessagePack input,
/// that no wire version exists to check.
///
/// The rule used to carry an exception — tag `0` "legitimate as the faithful
/// re-emission of pre-v41 content" — and the check does NOT honour it,
/// because nothing can: a blob does not record what its content once was,
/// and the header version is the WRITER's claim, never the content's. The
/// exception is retired (2026-09-24); what it was for is a measured property
/// of the writer instead. `binary::serialize_module` selects the MINIMUM
/// lossless version for the module it is given, so a faithful re-emission of
/// pre-v41 content keeps its pre-v41 header and stays grandfathered
/// (`a_faithful_re_emission_of_pre_v41_content_keeps_its_header`); a
/// re-emission reaches v41+ only when the module carries a v41+ feature, and
/// whoever put it there is the v41+ producer of that module, held to the
/// rule like any other. The three-valued tag still lets every writer spell
/// `None`, so a transcoder never upgrades a legacy body into an affirmative
/// `Ungated`; the decoded-path validator then refuses that body BY NAME,
/// which is the loud form of what a two-valued tag would have done silently.
///
/// Residual, stated on the types rather than around them: a [`Module`] itself
/// carries no wire version — not as a field, which would change its serde
/// shape and put decode provenance into content identity — so a hand-built
/// module, one parsed from text / JSON / MessagePack, or one decoded through
/// the plain `binary::deserialize_module` has no provenance, and the rule
/// cannot apply to it. Plain `validate_module` accepts a bodied `None` for
/// exactly that reason. The MUST binds producers regardless; the check is
/// what a consumer can now run against the artifact it was actually handed
/// (`docs/binary-format.md`, v41).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BodyGate {
    /// No verification gate was applied to this body. Codegen must refuse
    /// (must-refuse corpus row `refuse/body_gate_ungated`).
    Ungated,
    /// Gated by the named authority. Free-form; round-trips verbatim.
    Gated {
        /// The gate's owner, e.g. `clean-kernel-tv`. Recognition is the
        /// consumer's decision; this crate never interprets it.
        authority: String,
        /// What the license rests on (binary v61, tag 3); `None` = NO
        /// EVIDENCE RECORDED. See the type docs. Sole trailing skipped field
        /// of this variant, so every evidence-free license keeps its serde
        /// bytes.
        #[cfg_attr(
            feature = "serde",
            serde(default, skip_serializing_if = "Option::is_none")
        )]
        evidence: Option<GateEvidence>,
    },
}

/// The evidence a [`BodyGate::Gated`] license rests on (binary v61, roadmap
/// WS1.12(c)): the obligation it cites and the digest of the body it was
/// granted to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateEvidence {
    /// The obligation the license cites: for `clean-kernel-tv`, the
    /// `Certified` `TranslationValidation` row scoped to the function.
    pub obligation: ProofId,
    /// [`Module::function_body_digest`] of the licensed body at the time the
    /// license was granted.
    pub body_digest: crate::proof::ProofDigest,
}

/// Digest domain of [`Module::function_body_digest`] (roadmap WS1.12(c)):
/// the identity [`GateEvidence::body_digest`] names.
pub const FUNCTION_BODY_DIGEST_V1_DOMAIN: &str = "trust_ir.function.body.v1";

impl BodyGate {
    /// `Gated` by `authority` with NO evidence recorded — the spelling of
    /// every pre-v61 license.
    #[must_use]
    pub fn gated(authority: impl Into<String>) -> Self {
        BodyGate::Gated {
            authority: authority.into(),
            evidence: None,
        }
    }

    /// The evidence a `Gated` license carries, if any.
    #[must_use]
    pub fn evidence(&self) -> Option<&GateEvidence> {
        match self {
            BodyGate::Ungated => None,
            BodyGate::Gated { evidence, .. } => evidence.as_ref(),
        }
    }

    /// Canonical text token for the `; #body-gate:` clause. `Gated` has no
    /// bare token — its text form is `gated "<authority>"` — so it returns
    /// `None`, mirroring [`Producer::token`].
    #[must_use]
    pub fn token(&self) -> Option<&'static str> {
        match self {
            BodyGate::Ungated => Some("ungated"),
            BodyGate::Gated { .. } => None,
        }
    }

    /// True iff this gate makes any positive licensing claim at all.
    /// `Ungated` never does. Whether the `authority` is TRUSTED is the
    /// consumer's call, not this crate's.
    #[must_use]
    pub fn is_gated(&self) -> bool {
        matches!(self, BodyGate::Gated { .. })
    }
}

impl core::fmt::Display for BodyGate {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BodyGate::Ungated => f.write_str("ungated"),
            BodyGate::Gated {
                authority,
                evidence: None,
            } => write!(f, "gated {authority:?}"),
            BodyGate::Gated {
                authority,
                evidence: Some(evidence),
            } => write!(
                f,
                "gated {authority:?} evidence #{} \"{}\"",
                evidence.obligation.index(),
                evidence.body_digest
            ),
        }
    }
}

/// serde skip predicate for "skip if false". Used by `ParamAttrs`/`FuncAttrs`;
/// the repo otherwise only has `Option::is_none`/`Vec::is_empty` predicates.
#[cfg(feature = "serde")]
fn is_false(b: &bool) -> bool {
    !*b
}

/// Integer-extension ABI attribute for an argument or return slot (v45,
/// roadmap WS3.11 / F-054), the `zeroext` / `signext` LLVM parameter
/// attributes.
///
/// It says how a slot NARROWER than the ABI's register lane reaches the
/// callee: zero-extended, sign-extended, or unrecorded. Names and variants are
/// taken verbatim from the v2 `FnAbiDescriptor` design so that descriptor can
/// EXTEND this rather than rename it.
///
/// `None` is UNRECORDED, never "no extension needed": a consumer that needs a
/// concrete extension for a narrow slot (DarwinPCS is the case that forced
/// this) must refuse rather than pick one. Like the rest of [`ParamAttrs`]
/// this is a producer CLAIM; the validator checks that it is well-placed
/// (integer / `Bool` / `Char`, narrower than 64 bits), not that it is true.
/// Must-refuse corpus row `refuse/narrow_arg_ext_unrecorded_darwin`: an
/// `i8`/`u16` FFI declaration on aarch64-apple-darwin with a `ParamAttrs`
/// slot recorded per parameter and `None` on both, well-formed here, and a
/// DarwinPCS consumer must refuse it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ArgExt {
    /// No extension recorded. The pre-v45 state of every slot.
    #[default]
    None,
    /// Zero-extended to the ABI lane (LLVM `zeroext`).
    ZeroExt,
    /// Sign-extended to the ABI lane (LLVM `signext`).
    SignExt,
}

impl ArgExt {
    /// The canonical text token, or `None` for the unrecorded state (which
    /// the text form spells by OMITTING the attribute).
    #[must_use]
    pub fn token(self) -> Option<&'static str> {
        match self {
            ArgExt::None => None,
            ArgExt::ZeroExt => Some("zeroext"),
            ArgExt::SignExt => Some("signext"),
        }
    }
}

/// How one argument or return slot crosses a call edge (v45, roadmap WS3.11 /
/// F-054) — the minimal, plan-of-record subset of the v2 `FnAbiDescriptor`
/// `PassMode`, with its names and variants kept verbatim so v2 extends rather
/// than renames.
///
/// **The `pass = None` rule, stated here once.** A slot with `pass = None` is
/// UNRECORDED. A consumer places it only by a classification it ESTABLISHES
/// under the module's [`StructPassingPolicy`] (under `NativeC`, the target's
/// ruleset for the edge's convention; under `AlwaysMemory` and `Unclassified`
/// no by-value aggregate slot is placed from inside the module), and REFUSES a
/// slot it cannot place, never defaulting it
/// (`refuse/struct_passing_unclassified_by_value_aggregate` for an aggregate,
/// `refuse/narrow_arg_ext_unrecorded_darwin` for the sibling `ext` fact). A
/// recorded mode is a producer CLAIM about that placement. The validator
/// checks where it may sit (`InvalidAbiSlotFact`). That it AGREES is a
/// consumer obligation
/// (`refuse/struct_passing_native_c_pass_mode_contradicts_target`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PassMode {
    /// The slot is not passed at all: a zero-sized type. Well-formed only on
    /// a slot whose layout is computable and empty.
    Ignore,
    /// Passed directly in one lane.
    Direct,
    /// Passed as two scalar lanes (an aggregate of two scalars, or a fat
    /// pointer).
    Pair,
    /// Passed as the named sequence of closed scalar lanes whose total size
    /// covers the slot's layout size (LLVM's "coerced to" shape).
    Cast {
        /// The lane types, each a closed scalar.
        pieces: Vec<crate::ty::Ty>,
    },
    /// Passed through memory: the value is materialized in a caller-made
    /// copy.
    Indirect {
        /// `true`: the copy itself occupies the outgoing argument area
        /// (System V `byval`, rustc `Indirect { on_stack: true }`). `false`:
        /// the copy's address travels as an ordinary pointer argument (AAPCS64
        /// and Win64 memory class).
        on_stack: bool,
    },
}

impl PassMode {
    /// The canonical text token of the mode's head.
    #[must_use]
    pub fn token(&self) -> &'static str {
        match self {
            PassMode::Ignore => "ignore",
            PassMode::Direct => "direct",
            PassMode::Pair => "pair",
            PassMode::Cast { .. } => "cast",
            PassMode::Indirect { .. } => "indirect",
        }
    }
}

/// Per-parameter optimization attributes (claim-style; TrustCg-facing hints).
///
/// These mirror LLVM parameter attributes. They are NOT proof-carrying: like
/// `CallingConv`/`Linkage` they are assertions a frontend makes that the backend
/// may exploit. A `Default` (all-`false`/`None`) `ParamAttrs` is the conservative
/// "no information" state and is what every legacy module deserializes to.
// NOT `Copy` since v45: `PassMode::Cast` carries the lane types.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
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
    /// The PRE-LOWERED spelling of a by-value argument
    /// ([`StructPassingPolicy`]): the callee receives its own copy. How the
    /// copy crosses is recorded by `pass = indirect { on_stack }` on this
    /// slot, and is otherwise UNRECORDED: the consumer places it by the
    /// target's ruleset when it establishes one and refuses the slot otherwise
    /// (the [`PassMode`] `pass = None` rule). No policy requires or
    /// re-classifies it.
    ///
    /// Unlike the hint-style attributes above, disagreement here changes the
    /// call's byte-level ABI. Binary codec: v20, flag bit 3; pre-v20 blobs
    /// decode to `false`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub byval: bool,
    /// Pointer parameter is the caller-allocated slot for an aggregate RETURNED
    /// through memory (LLVM `sret`): the callee writes the return value there
    /// instead of returning it in registers.
    ///
    /// ABI pinning: the return-position half of the `byval` classification.
    /// Binary codec: v20, flag bit 4; pre-v20 blobs decode to `false`.
    /// ALWAYS emitted by serde since v45 (the R3 #6 rule re-applied: `pass`
    /// was appended after it, and positional MessagePack may only skip a
    /// TRAILING field).
    #[cfg_attr(feature = "serde", serde(default))]
    pub sret: bool,
    /// Integer extension for this slot (v45). See [`ArgExt`]; `None` is
    /// UNRECORDED, never "no extension needed".
    #[cfg_attr(feature = "serde", serde(default))]
    pub ext: ArgExt,
    /// How this slot crosses the call edge (v45). See [`PassMode`]; `None` is
    /// UNRECORDED and falls under the `pass = None` rule stated there: the
    /// consumer places the slot by a classification it establishes, or
    /// refuses it (`refuse/narrow_arg_ext_unrecorded_darwin` is that refusal
    /// for the sibling `ext` fact).
    ///
    /// Trailing field — the only one that may `skip_serializing_if`.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub pass: Option<PassMode>,
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
            && self.ext == ArgExt::None
            && self.pass.is_none()
    }
}

/// Function-level optimization attributes (TrustCg-facing).
///
/// `readonly`/`readnone` describe memory effects; `inlinehint`/`cold` are
/// codegen hints. `params` is positional and may be shorter than the function's
/// parameter list — a missing entry means `ParamAttrs::default()` for that
/// parameter.
///
/// **What is checked (WS2.7).** On a function WITH a body, `readnone` (LLVM
/// `memory(none)`) and `readonly` (LLVM `memory(read)`) are CHECKED by
/// `trust_ir_build::validate_module` (`ValidationError::FuncAttrClaimViolated`):
/// no write (and for `readnone` no read) through an address that does not root
/// at one of the function's own `Alloca`s, no synchronizing atomic, fence,
/// heap or reference-count operation, no indirect call, and every direct callee
/// carrying the same claim (`readonly` admits a `readnone` callee). On a
/// bodyless declaration they remain a claim — there is no body to check. The
/// other attributes, and every `ParamAttrs` entry, are claims, not proofs.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FuncAttrs {
    // R3 #7: positional MessagePack (`rmp_serde::to_vec`) may only skip a TRAILING
    // field — skipping a non-last `is_false` bool shifted a later set bool into the
    // wrong slot (e.g. readonly=false/readnone=true silently round-tripped back as
    // readonly=true/readnone=false). Always emit every non-last field; only the
    // trailing `params` may skip. `default` keeps backward-compatible decode of
    // shorter legacy arrays.
    /// Does not write memory (LLVM `readonly` on a function). Checked on a
    /// defined body (see the type docs); a claim on a declaration.
    #[cfg_attr(feature = "serde", serde(default))]
    pub readonly: bool,
    /// Reads no memory and writes no memory (LLVM `readnone`). Checked on a
    /// defined body (see the type docs); a claim on a declaration.
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
    ///
    /// ALWAYS emitted by serde since v41 (no `skip_serializing_if`): the R3 #7
    /// rule above, re-applied — `target_features` was appended after it, and
    /// positional MessagePack may only skip a TRAILING field.
    #[cfg_attr(feature = "serde", serde(default))]
    pub params: Vec<ParamAttrs>,
    /// The function is `#[naked]`: it has no compiler-generated prologue or
    /// epilogue and its body is entirely the producer's (v41).
    #[cfg_attr(feature = "serde", serde(default))]
    pub naked: bool,
    /// Target features this function may assume, e.g. `["neon", "aes"]` (v41).
    ///
    /// A consumer must not compile a body that names a feature the target does
    /// not have; nothing in `TargetInfo` could express this before, so
    /// `#[target_feature]` had no representation at any level. Must-refuse
    /// corpus row `refuse/target_feature_unknown` (`avx512f` on an aarch64
    /// target): well-formed here — the validator knows no target's feature
    /// set — and a consumer must refuse it.
    ///
    /// ALWAYS emitted by serde since v45 (the R3 #7 rule re-applied: `ret`
    /// was appended after it).
    #[cfg_attr(feature = "serde", serde(default))]
    pub target_features: Vec<String>,
    /// The RETURN slot's ABI facts (v45, roadmap WS3.11): `ext`, `pass`, and
    /// the pointer attributes that describe a returned pointer
    /// (`noalias` / `nonnull` / `align` / `dereferenceable`).
    ///
    /// Before this there was no return slot at all: `sret` on a PARAMETER was
    /// the only return-position ABI fact expressible, so a `u8`-returning C
    /// declaration could not say `zeroext` and a returned aggregate could not
    /// say how it comes back.
    ///
    /// Declared LAST and conditionally skipped (empty): the sole trailing
    /// skip, so every pre-v45 positional serde array still decodes.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "ParamAttrs::is_empty")
    )]
    pub ret: ParamAttrs,
}

impl FuncAttrs {
    /// True when no function- or parameter-level attribute is set.
    pub fn is_empty(&self) -> bool {
        !self.readonly
            && !self.readnone
            && !self.inlinehint
            && !self.cold
            // v41: a naked or feature-gated function is NOT attribute-empty.
            // Omitting these makes the canonical printer skip the `; #attrs:`
            // line for a naked-only function, which is silent data loss the
            // text round-trip would then report as a mismatch.
            && !self.naked
            && self.target_features.is_empty()
            // v45: a function whose only ABI fact is on the RETURN slot is
            // not attribute-empty either.
            && self.ret.is_empty()
            && self.params.iter().all(ParamAttrs::is_empty)
    }

    /// True iff any slot uses a v45 ABI fact (an extension, a pass mode, or
    /// any return-slot attribute). The binary writer selects v45 exactly when
    /// this holds for some function.
    #[must_use]
    pub fn uses_abi_surface(&self) -> bool {
        !self.ret.is_empty()
            || self
                .params
                .iter()
                .any(|p| p.ext != ArgExt::None || p.pass.is_some())
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

/// Module-wide policy for by-value aggregates at call edges: WHO classifies
/// them, and what the producer claims by stamping the value.
///
/// A *by-value aggregate slot* is a parameter or return of any `FuncTy` of the
/// module whose type, looking through `Ty::Refine` to its base, is a `Struct`,
/// `Tuple`, `Array`, `Enum`, `Record`, `Sequence`, `Set`, `Closure` or
/// `Vector` ([`Module::is_by_value_aggregate_slot`]; ONE predicate, read by the
/// validator's `AlwaysMemory` rule and its `pass = indirect` placement rule,
/// and the set a consumer's policy gate must use). Scalars, thin pointers,
/// `Handle`, `FatPtr` (two scalar lanes), `Unit` and `Never` are not. A
/// *pre-lowered* crossing is spelled with pointers: an argument as a pointer
/// parameter marked [`ParamAttrs::byval`], a returned aggregate as the single
/// `sret` pointer parameter of a signature that returns nothing. No policy
/// re-classifies a pre-lowered pointer.
///
/// ONE RULE for all three values: a consumer places a by-value aggregate slot
/// only by a classification it ESTABLISHES, and refuses a slot it cannot
/// place, never by a default. The values differ only in where that
/// classification comes from (`docs/SPEC_RATIFICATIONS.md` §17). No value
/// requires `ParamAttrs`. The rule covers a module that pins a target: one
/// with `target_info: None` carries no policy, and §17 states that scope and
/// the residual it leaves open.
///
/// `struct_passing` feeds `Module::stable_digest`, so the claim a value makes
/// travels in the module's identity too.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StructPassingPolicy {
    /// The CONSUMER classifies. Each by-value aggregate slot crosses where the
    /// target's ruleset for the edge's `CallingConv` places that layout. The
    /// target is `TargetInfo::abi` when present, else the triple. The ruleset
    /// is:
    /// - the target's C ruleset for `C`, `CUnwind`, `Rust`, `RustCold`, `Fast`
    ///   and `Cold` (the format defines no other aggregate ruleset for the last
    ///   four);
    /// - the named ruleset for `SysV64` / `Win64` / `Aapcs` / `EfiApi` /
    ///   `VectorCall`;
    /// - swiftcall for `Swift`.
    ///
    /// A consumer that implements no ruleset for an edge's convention refuses
    /// the slot.
    ///
    /// The PRODUCER claims that placement is the one the other side of every
    /// edge it emits uses (for foreign code: the foreign side's actual
    /// convention), and marks nothing to say so. A slot whose intended
    /// placement differs must be pre-lowered or refused by the producer. A
    /// producer that establishes this for no slot stamps `Unclassified`.
    /// Whether the claim is true is not decidable here.
    ///
    /// A recorded [`ParamAttrs::pass`] or [`FuncAttrs::ret`] fact on any slot
    /// is a second statement of the placement the consumer computes and must
    /// AGREE with it. The validator checks only where a fact may sit
    /// (`InvalidAbiSlotFact`). A consumer that cannot establish agreement MUST
    /// refuse the module rather than prefer either statement. Must-refuse
    /// corpus row `refuse/struct_passing_native_c_pass_mode_contradicts_target`.
    #[default]
    NativeC,
    /// Every aggregate crossing is PRE-LOWERED: no `FuncTy` of the module has a
    /// by-value aggregate slot. Decided by `validate_module`
    /// (`AlwaysMemoryByValueAggregate`). Must-refuse corpus row
    /// `refuse/struct_passing_always_memory_by_value_aggregate`. Target-free
    /// as a SIGNATURE SHAPE only: where a `byval` copy lives is recorded by
    /// `pass` or is UNRECORDED ([`ParamAttrs::byval`]), and `FatPtr` pairs and
    /// multi-value returns are placed by the consumer's non-aggregate rules.
    AlwaysMemory,
    /// The producer did NOT establish that the native classification of its
    /// by-value aggregate slots is the placement the other side of its edges
    /// uses, and says so. It is a declaration of absence, not a third
    /// convention, and a consumer MUST NOT infer any classification from it. A
    /// consumer that would pass or return a by-value aggregate slot MUST refuse
    /// the module, unless it establishes THAT EDGE's placement from an
    /// authority outside the module (the producer's own ABI source), writing
    /// nothing back. Must-refuse corpus rows:
    /// `refuse/struct_passing_unclassified_by_value_aggregate`,
    /// `refuse/struct_passing_unclassified_refined_aggregate`,
    /// `refuse/struct_passing_unclassified_vector_by_value` and
    /// `refuse/struct_passing_unclassified_closure_by_value`.
    /// A module with no by-value aggregate slot needs no classification under
    /// any value.
    ///
    /// This lets such a producer pin the parts of `TargetInfo` that ARE facts
    /// about the target (`triple`, `pointer_size`, `endianness`) while stating
    /// honestly that aggregate passing is unclassified, rather than stamping a
    /// claim it did not establish into the module's identity.
    ///
    /// Binary codec: tag 2, VERSION 36 (additive; a pre-v36 reader rejects the
    /// blob on the version gate before reaching this byte, so MIN_READ_VERSION
    /// is unchanged).
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

/// One authenticated CROSS-CRATE dependency of a module (v41).
///
/// A `Module` was flat and self-contained before this: it carried no crate
/// identity, no dependency list, and no reference that could name an entity in
/// another module. `ProofEvidence::InheritedFromCallee` was therefore two
/// module-local `u32`s the validator forced to resolve HERE, so cross-crate
/// proof inheritance — the whole point of separate compilation with contracts
/// — could not be SPELLED, let alone checked.
///
/// This is the referent table those references resolve against. It is
/// deliberately NOT a new identity layer: identity is
/// [`Module::stable_digest_under`] the row's [`ModuleImport::scheme`], and
/// the digest here is exactly that value taken over the imported module.
///
/// # What a consumer must do with one
///
/// `digest` is an OBLIGATION, not a decoration. A consumer that composes a
/// proof across this edge must re-derive `Module::stable_digest_under(scheme)`
/// of the artifact it actually loaded and compare; a mismatch means the module it
/// holds is not the module the proof was about, and it must refuse. Matching
/// `name` is never sufficient — names are producer-chosen and collide.
/// Must-refuse corpus: `refuse/import_backed_summary_unauthenticated` pins
/// the single-module half (a `backed_by` claim the authority lane refuses
/// unauthenticated); the digest mismatch itself needs a root plus dependency
/// pair, which one wire artifact cannot carry
/// (`refuse/import_digest_mismatch_pair`, see `crate::imports`).
///
/// The API that does exactly this is [`Module::verify_import`] (one edge:
/// digest, name, producer, target — see [`crate::imports`]); the closure walk
/// that composes it with the module validator is
/// `trust_ir_build::validate_linked_module`.
///
/// # Content-interned
///
/// Identity is the whole row — today `(name, digest, producer, scheme)` —
/// and nothing else, exactly as for [`Module::universes`] /
/// [`Module::predicates`]. Mint entries with [`Module::intern_import`], never
/// `push`: two `ExternRef`s naming the same edge must carry the same
/// [`ImportId`]. `trust_ir_build::validate_module` enforces it
/// (`ValidationError::ImportTableNotInterned`) by comparing whole rows with
/// `==`, so a field added to this struct joins the key automatically.
///
/// # One row per `(artifact, producer)` edge
///
/// A row is a DEPENDENCY EDGE, not an artifact: [`ModuleImport::producer`] is
/// single-valued and the resolver pairs it with the far function's producer,
/// so a MIXED Rust+Clean dependency is imported through two rows — one per
/// producer — that carry the SAME `name` and `digest`. That is normative
/// (`docs/SPEC_RATIFICATIONS.md` §6) and not a violation of interning, since
/// the rows differ. A consumer deduplicating ARTIFACTS (for example to load or
/// hash each dependency once) keys on `(scheme, digest)` — or on the module's
/// current-scheme digest once loaded — never on [`ImportId`].
///
/// Rows that share a `digest` share a `name` (WS1.16): one artifact has one
/// [`Module::name`], so a second name for the same digest is a mislabelled
/// row, refused by `trust_ir_build::validate_module` as
/// `ValidationError::ImportIdentityConflict`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModuleImport {
    /// The imported module's own [`Module::name`].
    ///
    /// Diagnostic and lookup aid ONLY. It is not the identity — `digest` is —
    /// because nothing in the format makes a module name unique.
    pub name: String,
    /// [`Module::stable_digest_under`] `scheme` of the EXACT imported module.
    ///
    /// This is what makes an [`ExternRef`] checkable rather than asserted.
    pub digest: crate::proof::ProofDigest,
    /// Which frontend emitted the imported module, when recorded.
    ///
    /// `None` means UNRECORDED and must never be read as a wildcard or as
    /// agreement with the importer's own producer — the v34 `site = None`
    /// precedent. A consumer whose rule depends on the producer fails closed
    /// on `None`.
    ///
    /// Always emitted by serde since v44 (`null` when unrecorded): `scheme`
    /// follows it, and a positional MessagePack struct may carry at most ONE
    /// trailing skipped field. An absent key still decodes as `None`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub producer: Option<Producer>,
    /// The digest construction `digest` was recorded under (v44,
    /// [`crate::imports::IdentityScheme`]). The verifier hashes the candidate
    /// under THIS scheme, so a row minted before a domain bump keeps meaning
    /// what it meant.
    ///
    /// A row decoded from a pre-v44 blob, or from serde input without the
    /// key, is [`crate::imports::IdentityScheme::V2`]; [`ModuleImport::new`]
    /// records [`crate::imports::IdentityScheme::CURRENT`] (V3), the scheme
    /// [`Module::stable_digest`] computes. Part of the interned row identity:
    /// the same digest recorded under two schemes is two rows (and at most one
    /// of them can ever authenticate a given module).
    ///
    /// Sole trailing conditionally-skipped field of this struct (skipped when
    /// V2, so a legacy row's JSON and MessagePack spelling is unchanged).
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "crate::imports::IdentityScheme::is_v2")
    )]
    pub scheme: crate::imports::IdentityScheme,
}

impl ModuleImport {
    /// A dependency edge on `name` pinned to `digest`, with no recorded
    /// producer, recorded under [`crate::imports::IdentityScheme::CURRENT`]
    /// (V3) — so `digest` must be the dependency's [`Module::stable_digest`].
    /// A row recorded under another scheme is spelled with
    /// [`ModuleImport::with_scheme`].
    pub fn new(name: impl Into<String>, digest: crate::proof::ProofDigest) -> Self {
        Self {
            name: name.into(),
            digest,
            producer: None,
            scheme: crate::imports::IdentityScheme::CURRENT,
        }
    }

    /// Record that `digest` was taken under `scheme` (for example a legacy
    /// [`crate::imports::IdentityScheme::V2`] row minted before v44).
    #[must_use]
    pub fn with_scheme(mut self, scheme: crate::imports::IdentityScheme) -> Self {
        self.scheme = scheme;
        self
    }

    /// Record which frontend emitted the imported module.
    #[must_use]
    pub fn with_producer(mut self, producer: Producer) -> Self {
        self.producer = Some(producer);
        self
    }
}

/// A reference to an entity in ANOTHER module (v41).
///
/// The cross-crate half of the identity story `ModuleImport` opens: `module`
/// says WHICH module (by interned import, hence by authenticated digest),
/// `symbol` says which entity in it, and `obligation` optionally says which of
/// that module's proof obligations is being relied upon.
///
/// # Why `symbol` and not an id
///
/// A `FuncId` is a module-local arena index and means nothing in another
/// module's numbering. `symbol` is the LINK-TIME SYMBOL — the identity v41
/// ratified [`Function::name`] to be — so it is the one function-naming string
/// that is stable across the module boundary and agrees with what the linker
/// will actually resolve.
///
/// # `obligation` lives in the IMPORTED module's id space
///
/// [`ProofId`] is likewise arena-local. The id here indexes the IMPORTED
/// module's `proof_obligations`, never this module's; a consumer resolves it
/// only after authenticating that module against
/// [`ModuleImport::digest`]. `None` means the reference names the entity and
/// makes NO proof claim about it — never "any obligation" and never "the
/// obvious one".
///
/// [`Module::resolve_extern_ref`] is the resolver: it binds `symbol` to
/// exactly one exported, non-interposable far function whose producer and
/// signature agree with the local declaration, and `obligation` to a scoped, discharged obligation
/// whose kind the citing site may rely on (see [`crate::imports`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExternRef {
    /// Index into [`Module::imports`] — the module this reference is INTO.
    pub module: ImportId,
    /// Link-time symbol of the referenced entity inside that module.
    pub symbol: String,
    /// The obligation relied upon, in the IMPORTED module's `proof_obligations`
    /// id space. `None` = names the entity only, no proof claim.
    ///
    /// No `skip_serializing_if`: this struct nests inside `ProofEvidence` and
    /// `FunctionSummary`, both of which are read positionally by the canonical
    /// MessagePack codec, and keeping every field always-emitted is the local
    /// rule that makes appending to it later a one-field decision rather than a
    /// two-field one.
    #[cfg_attr(feature = "serde", serde(default))]
    pub obligation: Option<ProofId>,
}

impl ExternRef {
    /// Name `symbol` inside the imported module `module`, with no proof claim.
    pub fn new(module: ImportId, symbol: impl Into<String>) -> Self {
        Self {
            module,
            symbol: symbol.into(),
            obligation: None,
        }
    }

    /// Rely on `obligation` of the referenced entity. The id is in the
    /// IMPORTED module's id space.
    #[must_use]
    pub fn relying_on(mut self, obligation: ProofId) -> Self {
        self.obligation = Some(obligation);
        self
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ModuleG<X> {
    pub name: String,
    pub functions: Vec<FunctionG<X>>,
    pub structs: Vec<StructDefG<X>>,
    pub enums: Vec<EnumDefG<X>>,
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
    pub globals: Vec<GlobalG<X>>,
    pub func_types: Vec<ty::FuncTyG<X>>,
    pub types: Vec<TyG<X>>,
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
    /// ALWAYS emitted by serde since v41: `global_asm` was appended after it,
    /// and positional MessagePack may only skip a TRAILING field.
    #[cfg_attr(feature = "serde", serde(default))]
    pub predicates: Vec<Pred>,
    /// Module-level `global_asm!` blocks, in source order (v41).
    ///
    /// Opaque text: TrustIr does not parse it and attaches no semantics. A
    /// consumer that cannot emit module-level assembly must REFUSE the module
    /// rather than silently drop these — dropping them removes symbol
    /// definitions the rest of the module may reference. Must-refuse corpus
    /// row `refuse/global_asm_block`. Every projection carries the blocks —
    /// text too since WS4.5, as one `global_asm "<escaped>"` line per block —
    /// so the refusal cannot be laundered through any transport (F-065).
    ///
    /// ALWAYS emitted by serde since the cross-crate identity batch: `imports`
    /// was appended after it, and positional MessagePack may only skip a
    /// TRAILING field. `global_asm` held the sole trailing skip for exactly one
    /// change; flipping it here is the same move `spec_modules` (v30),
    /// `predicates` (v41) and `source` (v34) each made the moment something
    /// landed behind them.
    #[cfg_attr(feature = "serde", serde(default))]
    pub global_asm: Vec<String>,
    /// **Content-interned** cross-crate dependencies (v41), referenced from
    /// [`ExternRef::module`].
    ///
    /// This is the module's DEPENDENCY LIST and the referent table every
    /// cross-module reference resolves against. Interning is load-bearing for
    /// the same reason it is on `predicates`: two references naming one
    /// artifact must be one id, or a consumer walking the dependency graph
    /// counts one crate twice and can reach contradictory conclusions about
    /// which digest it must authenticate.
    ///
    /// Mint entries through [`Module::intern_import`], never `push`; two
    /// equal rows are refused by the validator
    /// (`ValidationError::ImportTableNotInterned`). Table ORDER is identity,
    /// not a hint — an [`ImportId`] is only meaningful against this exact
    /// ordering. One row per `(artifact, producer)` edge: a mixed Rust+Clean
    /// dependency has two rows sharing one digest (see [`ModuleImport`]).
    ///
    /// Always emitted by serde since v42: tuple layouts follow this table.
    #[cfg_attr(feature = "serde", serde(default))]
    pub imports: Vec<ModuleImport>,

    /// Concrete memory layouts for structural tuples, keyed by `types` entries.
    /// Absence supplies no source-layout evidence. Equal tuple spellings may
    /// have only one descriptor, even when the type table contains aliases.
    /// Consumers must validate the complete table before using these offsets.
    /// The table is part of canonical binary identity from wire version 42.
    /// Must-refuse corpus row `refuse/blob_tuple_layout_incoherent`: the
    /// binary reader itself refuses an incoherent table (`InvalidData`), so a
    /// consumer that decodes has validated it; the validator's own
    /// `TupleLayoutInconsistent` is reachable only for a hand-built or
    /// serde-decoded module.
    ///
    /// ALWAYS emitted by serde since WS5.3b: `completeness` was appended after
    /// it, and positional MessagePack may only skip a TRAILING field (the
    /// same flip `global_asm`, `imports`, `predicates` and `spec_modules`
    /// each made the moment something landed behind them).
    #[cfg_attr(feature = "serde", serde(default))]
    pub tuple_layouts: Vec<TupleLayoutDescriptor>,

    /// The producer's completeness claim for this module (WS5.3b, F-090):
    /// whether every source item the producer was asked to lower is in the
    /// module, or which ones are not.
    ///
    /// THREE-VALUED, like [`Function::body_gate`]:
    ///
    /// * `None` — NO CLAIM. Every module decoded from a blob written before
    ///   the carrier existed, and every hand-built module, reads as this.
    ///   It is never `Complete`: a two-state carrier would let a
    ///   re-serialized legacy module silently claim completeness, which is
    ///   exactly the F-090 failure ("a silently incomplete module must not
    ///   read as complete") moved one format inward.
    /// * `Some(Complete)` — the producer affirms its `unlowered` set was
    ///   empty. The format cannot check this against source; it is a
    ///   PRODUCER rule (`docs/SPEC_RATIFICATIONS.md` §15), and the stamp must
    ///   come from the same computation as the producer's own partial-module
    ///   refusal, never a second one.
    /// * `Some(Partial(rows))` — the named symbols were NOT lowered, each
    ///   with the producer's reason. [`trust_ir_build::validate_module`]
    ///   refuses a row naming a bodied function of this module
    ///   (`UnloweredRowNamesDefinition`) and two rows naming one symbol
    ///   (`DuplicateUnloweredRow`); a row may name a bodyless declaration or
    ///   no function at all.
    ///
    /// Text carries it as the module-level `completeness complete` /
    /// `completeness partial` line followed by one `unlowered "<symbol>"
    /// <"<path>" | -> "<reason>"` line per row; JSON and MessagePack carry it
    /// as this field. ALWAYS emitted by serde since amendment D: `drop_glue`
    /// was appended after it, and positional MessagePack may only skip a
    /// TRAILING field (the flip `tuple_layouts`, `imports`, `global_asm`,
    /// `predicates` and `spec_modules` each made the moment something landed
    /// behind them); an older document without it still decodes. The BINARY format has
    /// no carrier yet — its wire part is a member of the next open wire batch
    /// (a reservation first, per `docs/wire-allocation.md`) — so every binary
    /// writer REFUSES a module carrying a claim
    /// (`BinaryProjectionError::CompletenessClaimUnencodable`) rather than
    /// dropping it, and such a module has no wire identity
    /// ([`Module::completeness_claim_unencodable`]).
    #[cfg_attr(feature = "serde", serde(default))]
    pub completeness: Option<ModuleCompleteness>,

    /// The module drop-glue table (amendment D, `docs/SPEC_RATIFICATIONS.md`
    /// §20): one [`DropGlueEntry`] per type whose destructor the module
    /// states. An [`Inst::Drop`] / [`Inst::DropInvoke`] at type `T` RESOLVES
    /// to the glue of the one row whose `ty` equals `T` (derived equality, the
    /// tuple-layout rule) and executes as a call of it; at a type with no row
    /// it is UNRESOLVED: well-formed, but never a no-op — both engines refuse
    /// it and the default codegen gate refuses it
    /// (`refuse/drop_unresolved`).
    ///
    /// ONE canonical order: rows strictly ascending by `glue` (so one glue
    /// names one type), no two rows with equal `ty`. Build it through
    /// [`Module::set_drop_glue`], which inserts at the canonical position.
    /// The binary reader refuses another order (`InvalidData`,
    /// `refuse/blob_drop_glue_not_canonical`) and `validate_module` refuses a
    /// malformed row (`InvalidDropGlue`, `refuse/drop_glue_invalid`).
    ///
    /// Binary: a trailing section from wire v55 (`DROP_GLUE_FORMAT_VERSION`);
    /// an older blob decodes with an empty table, so its drops are
    /// unresolved. It was the sole trailing conditionally-skipped serde field
    /// until wire v58; it is ALWAYS emitted since `closure_layouts` was
    /// APPENDED after it (positional MessagePack may only skip a TRAILING
    /// field — the flip `completeness` made for it), so a module without a
    /// table spells `[]` here; an older document without it still decodes.
    #[cfg_attr(feature = "serde", serde(default))]
    pub drop_glue: Vec<DropGlueEntry>,

    /// Concrete memory layouts for first-class closure types (`Ty::Closure`),
    /// keyed by `closure_types` entries (wire version 58).
    ///
    /// The shape and the rules are exactly [`Module::tuple_layouts`]': a
    /// descriptor per closure type, checked for completeness, natural capture
    /// alignment, containment and non-overlap before any offset is used, with
    /// at most ONE row per closure type. Absence supplies no layout evidence
    /// — a closure type with no row has no byte image, which is the state
    /// every closure type was in before v58.
    ///
    /// Capture offsets follow CAPTURE ORDER, which a producer may lay out in
    /// any physical order (`repr(Rust)` reorders upvars); the offsets are the
    /// producer's declared image, not a recomputation.
    ///
    /// The table is part of canonical binary identity from wire version 58.
    /// Always emitted by serde since v70 appended [`Self::blobs`] after it
    /// (`serde(default)` still decodes an older document without it).
    #[cfg_attr(feature = "serde", serde(default))]
    pub closure_layouts: Vec<ClosureLayoutDescriptor>,

    /// The content-addressed weight blob table (wire v70, PKG-U13e;
    /// `docs/SPEC_RATIFICATIONS.md` §27): the bytes each
    /// [`Constant::TensorBlob`] names by digest, one row per digest, in the
    /// canonical order of strictly ascending digest
    /// ([`blob::blob_table_order_refusal`]). A module table: no function
    /// body's identity reads it ([`Self::function_body_digest`]), while the
    /// module's own identity ([`Self::stable_digest`]) carries every byte.
    /// Build rows through [`Module::intern_blob`], which keeps the order and
    /// stores identical bytes once.
    ///
    /// R3 #5 (the positional-serde rule): appended LAST as the one trailing
    /// skipped field, so `closure_layouts` before it flipped to always-emitted
    /// in the same change, and a legacy shorter array decodes with both empty.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub blobs: Vec<blob::Blob>,
}

/// The level-R module: [`ModuleG`] with no extension.
pub type Module = ModuleG<level::NoExt>;

// The table doors of a plain `Module` never panic on a value their signature
// admits ("A construction door refuses; it never panics on a value its
// signature admits", docs/SPEC_RATIFICATIONS.md): a full table is a typed
// refusal, with the table unchanged. The lint holds this block to it.
#[cfg_attr(
    not(test),
    deny(
        clippy::panic,
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::unreachable,
        clippy::todo,
        clippy::unimplemented,
        clippy::arithmetic_side_effects,
        clippy::cast_possible_truncation
    )
)]
impl<X> ModuleG<X> {
    /// Append `ft` to the signature table and return its positional id.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the table already holds an entry at id
    /// `u32::MAX`; the table is unchanged.
    pub fn add_func_type(&mut self, ft: ty::FuncTyG<X>) -> Result<FuncTyId, IdSpaceExhausted> {
        let id = value::table_id(self.func_types.len())?;
        self.func_types.push(ft);
        Ok(id)
    }

    /// Raw registration: push `sd` and return its declared id, verbatim.
    ///
    /// This legacy constructor performs NO dedup and NO id-collision check —
    /// reconstruction paths (codecs) and callers that manage their own id
    /// space rely on that verbatim behavior. New producer code should prefer
    /// [`Module::add_struct_def`], which dedups structurally-identical defs
    /// and never lets two defs share an id.
    pub fn add_struct(&mut self, sd: StructDefG<X>) -> StructId {
        let id = sd.id;
        self.structs.push(sd);
        id
    }

    /// Raw registration: push `ed` and return its declared id, verbatim.
    ///
    /// Legacy counterpart of [`Module::add_enum_def`] — no dedup, no
    /// id-collision check. See [`Module::add_struct`] for when that is the
    /// right tool.
    pub fn add_enum(&mut self, ed: EnumDefG<X>) -> EnumId {
        let id = ed.id;
        self.enums.push(ed);
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
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the table already holds an entry at id
    /// `u32::MAX`; the table is unchanged.
    pub fn add_closure_type(&mut self, ct: ClosureTy) -> Result<ClosureTyId, IdSpaceExhausted> {
        let id = value::table_id(self.closure_types.len())?;
        self.closure_types.push(ct);
        Ok(id)
    }

    /// Append `ty` to the type table and return its positional id.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the table already holds an entry at id
    /// `u32::MAX`; the table is unchanged.
    pub fn add_type(&mut self, ty: TyG<X>) -> Result<TyId, IdSpaceExhausted> {
        let id = value::table_id(self.types.len())?;
        self.types.push(ty);
        Ok(id)
    }
}

impl<X> ModuleG<X> {
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
            global_asm: Vec::new(),
            imports: Vec::new(),
            tuple_layouts: Vec::new(),
            completeness: None,
            drop_glue: Vec::new(),
            closure_layouts: Vec::new(),
            blobs: Vec::new(),
        }
    }

    /// `true` when this module carries a completeness claim
    /// ([`Module::completeness`] is `Some`), which NO binary version can
    /// encode yet (WS5.3b non-wire half): every binary writer refuses it
    /// (`BinaryProjectionError::CompletenessClaimUnencodable`) and the
    /// digests panic on it, exactly as for
    /// [`first_inlined_scope_chain`](Module::first_inlined_scope_chain).
    /// `trust_ir_build::wire_identity_blocker` probes this and refuses by
    /// name.
    #[must_use]
    pub fn completeness_claim_unencodable(&self) -> bool {
        self.completeness.is_some()
    }

    /// The first signature placement record that exceeds binary encoding
    /// limits, including unused signature rows. This also applies to a
    /// template's generic module. The writer's own `func_types` arm refuses
    /// such a record by the same predicate
    /// (`SignatureAbi::validate_encoding_limits`), so an identity consumer's
    /// pre-check is [`Module::wire_image_refusal`], which also covers every
    /// other construct the writer refuses.
    #[must_use]
    pub fn first_signature_abi_encoding_error(&self) -> Option<(usize, String)> {
        self.func_types
            .iter()
            .enumerate()
            .find_map(|(signature, ty)| {
                ty.abi.as_ref().and_then(|abi| {
                    abi.validate_encoding_limits()
                        .err()
                        .map(|detail| (signature, detail))
                })
            })
    }
}

/// A producer's completeness claim for a [`Module`] (WS5.3b, F-090). See
/// [`Module::completeness`] for the three-valued contract with `None`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ModuleCompleteness {
    /// Every item the producer was asked to lower is in the module.
    Complete,
    /// These items were NOT lowered. Non-empty by convention: an empty row
    /// list is the shape of `Complete` and is refused by the validator
    /// (`EmptyPartialClaim`), so a producer cannot spell "complete" two ways.
    Partial(Vec<UnloweredRow>),
}

impl ModuleCompleteness {
    /// `true` for [`ModuleCompleteness::Complete`].
    #[must_use]
    pub fn is_complete(&self) -> bool {
        matches!(self, Self::Complete)
    }

    /// The unlowered rows of a partial claim (empty for `Complete`).
    #[must_use]
    pub fn unlowered(&self) -> &[UnloweredRow] {
        match self {
            Self::Complete => &[],
            Self::Partial(rows) => rows,
        }
    }
}

/// One item a producer did not lower into a [`ModuleCompleteness::Partial`]
/// module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct UnloweredRow {
    /// The LINK-TIME SYMBOL the item would have had (`Function::name`'s
    /// normative reading). Unique across the claim.
    pub symbol: String,
    /// The human def-path, when the producer has one (`Function::display_path`).
    pub display_path: Option<String>,
    /// The producer's reason, verbatim. Opaque to TrustIr.
    pub reason: String,
}

/// A declared tuple byte image. Offsets follow logical element order, which
/// can differ from physical order. Coherence checking is not a source refinement
/// certificate: the producer must separately bind this descriptor to its source.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TupleLayoutDescriptor {
    pub tuple_type: TyId,
    pub size: u64,
    pub align: u64,
    pub field_offsets: Vec<u64>,
}

/// One row of the module drop-glue table (amendment D,
/// `docs/SPEC_RATIFICATIONS.md` §20 rule 1). Must-refuse rows:
/// `refuse/drop_glue_invalid`, `refuse/blob_drop_glue_not_canonical`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DropGlueEntry {
    /// The function a drop of `ty` runs. Its FuncTy is exactly `(ptr) -> ()`,
    /// not variadic, under any calling convention (the glue's own is used, as
    /// on a direct `Call`); a definition, or a non-weak bodyless declaration
    /// that is not a pinned runtime entry.
    pub glue: FuncId,
    /// The dropped type, inline. A site resolves through the row whose `ty`
    /// equals its own by derived equality (the tuple-layout rule): no type
    /// table is consulted, so `Array(ty.3, 4)` and `Array(ty.7, 4)` are
    /// different keys even when the two table rows are equal.
    pub ty: Ty,
}

/// What a drop at one type resolves to ([`Module::drop_glue_for`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DropResolution {
    /// Exactly one row names the type: the drop calls this glue.
    Resolved(FuncId),
    /// No row names the type: the drop is UNRESOLVED (refused by both engines
    /// and the default codegen gate; never a no-op).
    Unresolved,
    /// Two or more rows name the type. Only an UNVALIDATED module can answer
    /// this (`validate_module` refuses duplicate keys); a consumer treats it
    /// as malformed.
    Ambiguous,
}

/// Why [`Module::set_drop_glue`] refused a row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DropGlueConflict {
    /// The type already has a row, naming this glue.
    TypeHasGlue { existing: FuncId },
    /// The glue already destroys another type (glue is injective).
    GlueHasType { existing: Ty },
}

impl core::fmt::Display for DropGlueConflict {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::TypeHasGlue { existing } => write!(
                f,
                "the type already has drop glue @func.{}",
                existing.index()
            ),
            Self::GlueHasType { existing } => {
                write!(f, "the glue already destroys {existing}")
            }
        }
    }
}

impl std::error::Error for DropGlueConflict {}

/// A prebuilt lookup over a module's drop-glue table: O(1) resolution per
/// drop site and per call of a registered glue. Build it once per consumer
/// pass ([`Module::drop_glue_index`]); it borrows nothing.
#[derive(Debug, Clone, Default)]
pub struct DropGlueIndex {
    by_ty: std::collections::HashMap<Ty, DropResolution>,
    glues: BTreeSet<u32>,
}

impl DropGlueIndex {
    /// Index `entries` (a module's `drop_glue`). Duplicate keys answer
    /// [`DropResolution::Ambiguous`].
    #[must_use]
    pub fn new(entries: &[DropGlueEntry]) -> Self {
        let mut by_ty = std::collections::HashMap::with_capacity(entries.len());
        let mut glues = BTreeSet::new();
        for entry in entries {
            glues.insert(entry.glue.index());
            by_ty
                .entry(entry.ty.clone())
                .and_modify(|resolution| *resolution = DropResolution::Ambiguous)
                .or_insert(DropResolution::Resolved(entry.glue));
        }
        Self { by_ty, glues }
    }

    /// What a drop at `ty` resolves to.
    #[must_use]
    pub fn resolve(&self, ty: &Ty) -> DropResolution {
        self.by_ty
            .get(ty)
            .copied()
            .unwrap_or(DropResolution::Unresolved)
    }

    /// Whether `func` is the glue of some row.
    #[must_use]
    pub fn is_glue(&self, func: FuncId) -> bool {
        self.glues.contains(&func.index())
    }

    /// Whether the table is empty (every drop is unresolved).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.glues.is_empty() && self.by_ty.is_empty()
    }
}

/// A declared closure byte image (wire version 58): the environment frame a
/// `Ty::Closure` value occupies.
///
/// Offsets follow CAPTURE order, which can differ from physical order — that
/// difference is the point, since `repr(Rust)` reorders upvars and a
/// declaration-order C struct is the wrong image. Coherence checking is not a
/// source refinement certificate: the producer must separately bind this
/// descriptor to its source.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClosureLayoutDescriptor {
    pub closure: ClosureTyId,
    pub size: u64,
    pub align: u64,
    pub capture_offsets: Vec<u64>,
    /// Optional nominal source identity of this exact environment type (v66).
    /// This is producer identity data, not a source refinement certificate.
    /// Distinct known origins must not be interned by capture shape alone.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub origin: Option<crate::ty::TypeOrigin>,
}

#[derive(Debug, Clone, Copy)]
enum ModuleFunctionState<'module> {
    Unique(&'module Function),
    Ambiguous,
}

/// Duplicate-aware index over the functions in one exact [`Module`].
///
/// Construction takes `O(F log F)` time and `O(F)` memory for `F` function
/// declarations. A lookup takes `O(log F)` time. Sparse [`FuncId`] values are
/// ordinary keys rather than vector positions, and a duplicated ID resolves to
/// no function, so consumers never authenticate an arbitrary declaration.
///
/// Build one catalog at the boundary of a composite module operation and pass
/// it through that operation's internal helpers. This avoids both repeated
/// linear function-table scans and repeated `O(F log F)` index construction.
#[derive(Debug)]
pub struct ModuleFunctionCatalog<'module> {
    module: &'module Module,
    entries: BTreeMap<u32, ModuleFunctionState<'module>>,
}

impl<'module> ModuleFunctionCatalog<'module> {
    /// Index every function declaration in `module` exactly once.
    pub fn new(module: &'module Module) -> Self {
        let mut entries = BTreeMap::new();
        for function in &module.functions {
            match entries.entry(function.id.index()) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(ModuleFunctionState::Unique(function));
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    entry.insert(ModuleFunctionState::Ambiguous);
                }
            }
        }
        Self { module, entries }
    }

    /// Return the declaration for `function` only when its ID occurs exactly
    /// once in the indexed module.
    pub fn unique(&self, function: FuncId) -> Option<&'module Function> {
        match self.entries.get(&function.index()) {
            Some(ModuleFunctionState::Unique(function)) => Some(*function),
            Some(ModuleFunctionState::Ambiguous) | None => None,
        }
    }

    /// Iterate duplicated function IDs in deterministic numeric order.
    pub fn ambiguous_ids(&self) -> impl Iterator<Item = u32> + '_ {
        self.entries.iter().filter_map(|(&id, state)| {
            matches!(state, ModuleFunctionState::Ambiguous).then_some(id)
        })
    }

    /// Number of distinct function IDs indexed, including ambiguous IDs.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the indexed module has no function IDs.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Description of the first FFI boundary in the indexed module, or `None`.
    ///
    /// After the catalog has been built, this visits at most every function and
    /// instruction once and performs one `O(log F)` lookup for each direct
    /// `Call`/`Invoke`: `O(F + I + C log F)` time, where `I` is the total
    /// instruction count and `C <= I` is the number of direct call edges. It
    /// allocates only the returned description. Missing or ambiguous function
    /// IDs never select a declaration; module validation rejects those edges
    /// independently.
    pub fn first_ffi_boundary(&self) -> Option<String> {
        for function in &self.module.functions {
            if function.blocks.is_empty()
                && matches!(function.linkage, Linkage::External | Linkage::ExternalWeak)
                && function.calling_conv != CallingConv::Rust
            {
                return Some(format!(
                    "bodyless {} declaration `{}`",
                    function.linkage, function.name
                ));
            }
        }
        for function in &self.module.functions {
            for block in &function.blocks {
                for node in &block.body {
                    match &node.inst {
                        crate::inst::Inst::Call { callee, .. }
                        | crate::inst::Inst::CallCannotUnwind { callee, .. } => {
                            if let Some(callee_function) = self.unique(*callee)
                                && callee_function.calling_conv != function.calling_conv
                            {
                                return Some(format!(
                                    "cross-convention call edge `{}` ({}) -> `{}` ({})",
                                    function.name,
                                    function.calling_conv,
                                    callee_function.name,
                                    callee_function.calling_conv
                                ));
                            }
                        }
                        crate::inst::Inst::Invoke { callee, .. } => {
                            if let Some(callee_function) = self.unique(*callee)
                                && callee_function.calling_conv != function.calling_conv
                            {
                                return Some(format!(
                                    "cross-convention invoke edge `{}` ({}) -> `{}` ({})",
                                    function.name,
                                    function.calling_conv,
                                    callee_function.name,
                                    callee_function.calling_conv
                                ));
                            }
                        }
                        // Amendment P: a sited check's failure calls its
                        // entry with the entry's convention.
                        crate::inst::Inst::Assert {
                            site: Some(site), ..
                        }
                        | crate::inst::Inst::AssertInvoke { site, .. } => {
                            if let Some(entry) = self.unique(site.entry)
                                && entry.calling_conv != function.calling_conv
                            {
                                return Some(format!(
                                    "cross-convention panic-site edge `{}` ({}) -> `{}` ({})",
                                    function.name,
                                    function.calling_conv,
                                    entry.name,
                                    entry.calling_conv
                                ));
                            }
                        }
                        crate::inst::Inst::CallIndirect { calling_conv, .. }
                        | crate::inst::Inst::CallIndirectCannotUnwind { calling_conv, .. }
                        | crate::inst::Inst::InvokeIndirect { calling_conv, .. }
                            if *calling_conv != function.calling_conv =>
                        {
                            return Some(format!(
                                "cross-convention indirect call edge in `{}` ({}) declaring {}",
                                function.name, function.calling_conv, calling_conv
                            ));
                        }
                        _ => {}
                    }
                }
            }
        }
        None
    }
}

impl Module {
    /// What a drop at `ty` resolves to through this module's drop-glue table
    /// (amendment D, `docs/SPEC_RATIFICATIONS.md` §20 rule 2). A linear scan;
    /// a pass resolving many sites builds [`Module::drop_glue_index`] once.
    #[must_use]
    pub fn drop_glue_for(&self, ty: &Ty) -> DropResolution {
        let mut rows = self.drop_glue.iter().filter(|entry| entry.ty == *ty);
        match (rows.next(), rows.next()) {
            (None, _) => DropResolution::Unresolved,
            (Some(entry), None) => DropResolution::Resolved(entry.glue),
            (Some(_), Some(_)) => DropResolution::Ambiguous,
        }
    }

    /// Whether `func` is the glue of some drop-glue row (§20 rule 5b: such a
    /// function is reached only by drop resolution or through its address).
    #[must_use]
    pub fn is_registered_drop_glue(&self, func: FuncId) -> bool {
        self.drop_glue.iter().any(|entry| entry.glue == func)
    }

    /// An O(1) lookup over the drop-glue table.
    #[must_use]
    pub fn drop_glue_index(&self) -> DropGlueIndex {
        DropGlueIndex::new(&self.drop_glue)
    }

    /// The sanctioned constructor of a drop-glue row: inserts `(glue, ty)`
    /// at its canonical position (rows strictly ascending by `glue`).
    /// Refuses a second row for `ty` or a second type for `glue`; re-stating
    /// an existing row is a no-op. Whether `glue` names a function of the
    /// right signature is `validate_module`'s question (`InvalidDropGlue`).
    pub fn set_drop_glue(&mut self, ty: Ty, glue: FuncId) -> Result<(), DropGlueConflict> {
        if let Some(entry) = self.drop_glue.iter().find(|entry| entry.ty == ty) {
            return if entry.glue == glue {
                Ok(())
            } else {
                Err(DropGlueConflict::TypeHasGlue {
                    existing: entry.glue,
                })
            };
        }
        if let Some(entry) = self.drop_glue.iter().find(|entry| entry.glue == glue) {
            return Err(DropGlueConflict::GlueHasType {
                existing: entry.ty.clone(),
            });
        }
        let at = self
            .drop_glue
            .partition_point(|entry| entry.glue.index() < glue.index());
        self.drop_glue.insert(at, DropGlueEntry { glue, ty });
        Ok(())
    }
}

// The table doors of a plain `Module`: every one refuses a full table with a
// typed error and the table unchanged, and none panics on a value its
// signature admits ("A construction door refuses; it never panics on a value
// its signature admits", docs/SPEC_RATIFICATIONS.md). The lint holds this
// block to it outside tests.
#[cfg_attr(
    not(test),
    deny(
        clippy::panic,
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::unreachable,
        clippy::todo,
        clippy::unimplemented,
        clippy::arithmetic_side_effects,
        clippy::cast_possible_truncation
    )
)]
impl Module {
    /// Interns `data` in the content-addressed blob table ([`Self::blobs`],
    /// PKG-U13e) and returns its digest, the key a [`Constant::TensorBlob`]
    /// spells. Idempotent: bytes already in the table return their digest and
    /// store nothing, so identical blobs are held once. A new row lands at its
    /// canonical (strictly ascending digest) position.
    pub fn intern_blob(&mut self, data: Vec<u8>) -> blob::BlobDigest {
        let row = blob::Blob::new(data);
        let digest = row.digest;
        if let Err(position) = self
            .blobs
            .binary_search_by(|probe| probe.digest.cmp(&digest))
        {
            self.blobs.insert(position, row);
        }
        digest
    }

    /// The first blob table row keyed by `digest`, if any. Both engines
    /// resolve a [`Constant::TensorBlob`] through it and then check that the
    /// row's bytes hash to the digest; the table's order is the validator's
    /// question, not the lookup's.
    pub fn blob(&self, digest: &blob::BlobDigest) -> Option<&blob::Blob> {
        self.blobs.iter().find(|row| row.digest == *digest)
    }

    /// Interns a debug-info source-file path, returning its index for use in
    /// [`SourceSpan::file`]. Idempotent: a path already in the table returns
    /// its existing index rather than appending a duplicate.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] (space `files`) when the path is new and the table
    /// already holds an entry at index `u32::MAX`; the table is unchanged.
    pub fn intern_file(&mut self, path: impl Into<String>) -> Result<u32, IdSpaceExhausted> {
        let path = path.into();
        // An entry past `u32::MAX` has no index, so nothing can name it: it is
        // not found here (`value::table_index`), never truncated onto an
        // index that names another entry.
        let known = self.files.iter().position(|p| *p == path);
        if let Some(index) = known.and_then(|i| value::table_index(i, "files").ok()) {
            return Ok(index);
        }
        let index = value::table_index(self.files.len(), "files")?;
        self.files.push(path);
        Ok(index)
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
    /// 1. a **bodyless `external` or `external_weak` declaration** — an import
    ///    resolved against a separately compiled object at link time (a
    ///    contract-only declaration with a [`FunctionSummary`] included: the
    ///    summary aids verification, but the symbol still crosses an object
    ///    boundary; a weak import crosses it whether or not it resolves), or
    /// 2. a **call edge whose calling convention differs from the enclosing
    ///    function's** — a direct `Call` to a callee with a different
    ///    `Function::calling_conv`, or a `CallIndirect` declaring a different
    ///    edge convention.
    ///
    /// Either way, two independently produced objects must agree byte-for-byte
    /// on the ABI, which is only well-defined against a pinned target. This is
    /// the predicate behind [`Module::requires_target_info`]; the returned
    /// description feeds the validator's `TargetInfoRequired` diagnostic.
    ///
    /// This convenience entry point constructs one [`ModuleFunctionCatalog`],
    /// so its complete bound is `O(F log F + I + C log F)` time and `O(F)`
    /// temporary memory. A composite operation that already has a catalog
    /// should call [`ModuleFunctionCatalog::first_ffi_boundary`] directly.
    pub fn first_ffi_boundary(&self) -> Option<String> {
        ModuleFunctionCatalog::new(self).first_ffi_boundary()
    }

    /// ABI pinning: true when this module contains an FFI boundary (see
    /// [`Module::first_ffi_boundary`]) and therefore MUST carry a
    /// [`TargetInfo`]. `validate_module` (trust-ir-build) rejects a module for
    /// which this returns `true` while `target_info` is `None`; modules without
    /// FFI boundaries may stay target-independent (`target_info: None`).
    pub fn requires_target_info(&self) -> bool {
        self.first_ffi_boundary().is_some()
    }

    /// Intern a function signature by STRUCTURE, returning its id. Idempotent.
    ///
    /// Returns the id of the first existing [`FuncTy`] equal to `ft` (every
    /// field — params, returns, `is_vararg`, and typed ABI claims — compared
    /// structurally), or
    /// appends `ft` and returns the new id. [`Module::add_func_type`] stays the
    /// raw, always-appending constructor: codecs reconstruct tables verbatim
    /// and a producer that manages its own id space relies on that.
    ///
    /// Interning changes no meaning: two equal rows are the same signature
    /// wherever they are cited. It only stops a producer that mints one row
    /// per call site from growing the table without bound.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when `ft` is new and the table already holds an
    /// entry at id `u32::MAX`; the table is unchanged.
    pub fn intern_func_type(&mut self, ft: FuncTy) -> Result<FuncTyId, IdSpaceExhausted> {
        if let Some(id) = (0..=u32::MAX)
            .zip(&self.func_types)
            .find_map(|(index, existing)| (*existing == ft).then_some(FuncTyId::new(index)))
        {
            return Ok(id);
        }
        self.add_func_type(ft)
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
    ///
    /// The id is one past the HIGHEST id in the struct table, by the one
    /// fresh-id rule ([`FreshIds::after`]).
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the table holds id `u32::MAX` (a DECODED
    /// table can): no id is free, and none is wrapped onto an id in use.
    pub fn allocate_struct_id(&self) -> Result<StructId, IdSpaceExhausted> {
        FreshIds::after(self.structs.iter().map(|sd| sd.id))
            .peek()
            .ok_or(IdSpaceExhausted::of::<StructId>())
    }

    /// Allocate the next free `EnumId` — the enum-table counterpart of
    /// [`Module::allocate_struct_id`], with the same reserve-by-insert
    /// contract ([`FreshIds::after`]).
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the table holds id `u32::MAX`.
    pub fn allocate_enum_id(&self) -> Result<EnumId, IdSpaceExhausted> {
        FreshIds::after(self.enums.iter().map(|ed| ed.id))
            .peek()
            .ok_or(IdSpaceExhausted::of::<EnumId>())
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
    ///
    /// All or nothing.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when step 3 needs a fresh id and the table holds
    /// `u32::MAX` ([`Self::allocate_struct_id`]); the table is unchanged.
    pub fn add_struct_def(&mut self, sd: StructDef) -> Result<StructId, IdSpaceExhausted> {
        if let Some(existing) = self
            .structs
            .iter()
            .find(|other| struct_def_structurally_eq(other, &sd))
        {
            return Ok(existing.id);
        }
        let id = if self.structs.iter().any(|other| other.id == sd.id) {
            self.allocate_struct_id()?
        } else {
            sd.id
        };
        self.structs.push(StructDef { id, ..sd });
        Ok(id)
    }

    /// Register an enum definition with **mandatory dedup** and a collision-
    /// free id guarantee — the enum-table counterpart of
    /// [`Module::add_struct_def`] (same three-step contract; callers must use
    /// the returned id). All or nothing.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when a re-numbering needs a fresh id and the table
    /// holds `u32::MAX` ([`Self::allocate_enum_id`]); the table is unchanged.
    pub fn add_enum_def(&mut self, ed: EnumDef) -> Result<EnumId, IdSpaceExhausted> {
        if let Some(existing) = self
            .enums
            .iter()
            .find(|other| enum_def_structurally_eq(other, &ed))
        {
            return Ok(existing.id);
        }
        let id = if self.enums.iter().any(|other| other.id == ed.id) {
            self.allocate_enum_id()?
        } else {
            ed.id
        };
        self.enums.push(EnumDef { id, ..ed });
        Ok(id)
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
    /// widening. `None` means "not canonicalizable" and nothing else.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the universe is new and the table already
    /// holds an entry at id `u32::MAX`; the table is unchanged.
    pub fn intern_universe(
        &mut self,
        universe: Universe,
    ) -> Result<Option<UnivId>, IdSpaceExhausted> {
        let canonical = match universe {
            Universe::IntRange { lo, hi } => Universe::range(lo, hi),
            Universe::Members(items) => Universe::members(items),
        };
        let Some(canonical) = canonical else {
            return Ok(None);
        };
        if let Some(id) = (0..=u32::MAX)
            .zip(&self.universes)
            .find_map(|(index, known)| (*known == canonical).then_some(UnivId::new(index)))
        {
            return Ok(Some(id));
        }
        let id = value::table_id(self.universes.len())?;
        self.universes.push(canonical);
        Ok(Some(id))
    }

    /// Interns a [`ModuleImport`] by CONTENT, returning its id. Idempotent.
    ///
    /// Identity is the whole row (compared with `==`; today the
    /// `(name, digest, producer)` triple): two calls with an equal row return
    /// the same [`ImportId`], and two imports differing in ANY component —
    /// including a `None` vs `Some` producer — are distinct entries, because
    /// they are distinct claims about what was depended on.
    ///
    /// There is one row per `(artifact, producer)` EDGE: a mixed Rust+Clean
    /// dependency is two rows with the same `name` and `digest` and different
    /// producers (ratified in `docs/SPEC_RATIFICATIONS.md` §6), because the
    /// resolver pairs the row's single producer with the far function's.
    /// Consumers deduplicating ARTIFACTS key on `digest`, never on the id.
    ///
    /// Never `push` into [`Module::imports`] directly. A duplicated ROW gives
    /// one edge two ids — the "one artifact, two ids" hazard, in which a
    /// consumer counting dependency edges sees two where there is one and can
    /// reach contradictory conclusions about what each id authenticated.
    /// `trust_ir_build::validate_module` refuses it as
    /// `ValidationError::ImportTableNotInterned`.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the row is new and the table already holds an
    /// entry at id `u32::MAX`; the table is unchanged.
    pub fn intern_import(&mut self, import: ModuleImport) -> Result<ImportId, IdSpaceExhausted> {
        if let Some(id) = (0..=u32::MAX)
            .zip(&self.imports)
            .find_map(|(index, existing)| (*existing == import).then_some(ImportId::new(index)))
        {
            return Ok(id);
        }
        let id = value::table_id(self.imports.len())?;
        self.imports.push(import);
        Ok(id)
    }

    /// Resolve an [`ImportId`] against this module's import table.
    ///
    /// `None` for a dangling id. Callers must treat that as a REFUSAL — a
    /// cross-module reference whose referent this module does not declare
    /// cannot be authenticated, so nothing may be inherited across it.
    #[must_use]
    pub fn import(&self, id: ImportId) -> Option<&ModuleImport> {
        self.imports.get(id.as_usize())
    }

    /// Interns a [`Pred`] by CONTENT, returning its id. Idempotent.
    ///
    /// Canonicalizes on the way in: finite-set extensions are sorted and
    /// deduped, and `Conj`/`Disj` child lists are sorted and deduped (a
    /// single-child connective collapses to that child, matching the lattice's
    /// one-spelling-per-construct rule). Returns `None` when the predicate
    /// cannot be made canonical, or when it references an id this module does
    /// not have — a dangling `PredId`/`UnivId` is refused at the door rather
    /// than deferred to the validator. `None` means "not canonicalizable" and
    /// nothing else.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the predicate is new and the table already
    /// holds an entry at id `u32::MAX`; the table is unchanged.
    pub fn intern_pred(&mut self, pred: Pred) -> Result<Option<PredId>, IdSpaceExhausted> {
        let Some(canonical) = self.canonical_pred(pred) else {
            return Ok(None);
        };
        self.intern_canonical_pred(canonical).map(Some)
    }

    /// The canonical spelling of `pred` against this module's tables, or
    /// `None` when it has none (see [`Self::intern_pred`]).
    fn canonical_pred(&self, pred: Pred) -> Option<Pred> {
        Some(match pred {
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
        })
    }

    /// Intern an ALREADY-canonical predicate: its existing id, or the next
    /// slot's id by the one table-id rule ([`value::table_id`]).
    fn intern_canonical_pred(&mut self, canonical: Pred) -> Result<PredId, IdSpaceExhausted> {
        if let Some(id) = (0..=u32::MAX)
            .zip(&self.predicates)
            .find_map(|(i, p)| (*p == canonical).then_some(PredId::new(i)))
        {
            return Ok(id);
        }
        let id = value::table_id(self.predicates.len())?;
        self.predicates.push(canonical);
        Ok(id)
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
            1 => children
                .first()
                .and_then(|only| self.predicates.get(only.as_usize()))
                .cloned(),
            n if n <= pred::MAX_CONNECTIVE_ARITY => Some(if conj {
                Pred::Conj(children)
            } else {
                Pred::Disj(children)
            }),
            _ => None,
        }
    }

    /// Convenience: intern `Pred::InUniverse(universe, space)` in one step.
    /// `None` when the universe is not canonicalizable.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when either table must grow and is full. The
    /// universe may already have been interned when the predicate table is the
    /// full one (interning is idempotent, so a retry names the same id).
    pub fn intern_in_universe(
        &mut self,
        universe: Universe,
        space: Space,
    ) -> Result<Option<PredId>, IdSpaceExhausted> {
        let Some(u) = self.intern_universe(universe)? else {
            return Ok(None);
        };
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
    ///
    /// Total on a non-canonical join: a DECODED predicate table can hold a
    /// node with no canonical spelling (an empty interval), and its join with
    /// itself is that node. The merge then weakens to `Top`, join's own
    /// fallback, instead of panicking.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the join is a new node and the predicate
    /// table has no id left for it; the table is unchanged.
    pub fn join_preds(
        &mut self,
        a: Option<PredId>,
        b: Option<PredId>,
    ) -> Result<PredId, IdSpaceExhausted> {
        let joined = match (a, b) {
            (Some(a), Some(b)) => self.pred_table().join_pred(a, b),
            // One side carries no fact: the merge carries no fact.
            _ => Pred::Top,
        };
        // Every fallback is toward `Top`, which is always canonical.
        let canonical = self.canonical_pred(joined).unwrap_or(Pred::Top);
        self.intern_canonical_pred(canonical)
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
    /// All or nothing.
    ///
    /// Synthesis is **unconditional in this constructor** — a module built
    /// through `try_add_function` never carries a claim-bearing function with a
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
    ///
    /// A DECODED module may already hold obligation id `u32::MAX`, and then no
    /// synthesized row has an id: the refusal below, never a panic. There is
    /// no panicking twin; the name `add_function` was deleted (D1b) so every
    /// old call site fails to compile instead of discarding a `Result`:
    ///
    /// ```compile_fail,E0599
    /// use trust_ir::value::{BlockId, FuncId, FuncTyId};
    /// use trust_ir::{Function, Module};
    ///
    /// let mut module = Module::new("deleted");
    /// let function = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    /// module.add_function(function);
    /// ```
    ///
    /// The same setup through this door compiles:
    ///
    /// ```
    /// use trust_ir::value::{BlockId, FuncId, FuncTyId};
    /// use trust_ir::{Function, Module};
    ///
    /// let mut module = Module::new("kept");
    /// let function = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    /// module.try_add_function(function)?;
    /// # Ok::<(), trust_ir::AddFunctionError>(())
    /// ```
    ///
    /// # Errors
    ///
    /// [`AddFunctionError`] when a synthesized obligation needs an id and the
    /// obligation id space is exhausted. Neither the function nor any
    /// obligation is pushed; the function comes back in the error.
    pub fn try_add_function(&mut self, f: Function) -> Result<(), AddFunctionError> {
        match self.synthesize_function_obligations(&f) {
            Ok(()) => {
                self.functions.push(f);
                Ok(())
            }
            Err(exhausted) => Err(AddFunctionError {
                exhausted,
                function: Box::new(f),
            }),
        }
    }

    /// Record the obligation drafts implied by a function's annotations.
    ///
    /// This is the synthesis half of [`Self::try_add_function`]: map claims to
    /// obligation kinds, deduplicate, and append `Pending` entries without
    /// inserting or replacing the function itself. Two-phase body builders
    /// use it when committing into an existing declaration slot.
    ///
    /// This creates claims only, never certificates or checked authority.
    /// The supplied function and final module still require validation.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the rows to synthesize need more obligation
    /// ids than remain (one past the highest in the table, never recycled).
    /// All or nothing: on `Err` the table is unchanged.
    pub fn synthesize_function_obligations(
        &mut self,
        f: &Function,
    ) -> Result<(), IdSpaceExhausted> {
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
        // Against the table: a kind this function already has a row for is
        // not synthesized again.
        kinds.retain(|(kind, _)| {
            !self
                .proof_obligations
                .iter()
                .any(|o| o.kind == *kind && o.function == Some(f.id))
        });
        if kinds.is_empty() {
            return Ok(());
        }
        // Ids after every existing obligation id (never reuse or collide, even
        // when the table carries sparse producer-assigned ids), taken as ONE
        // run before any row is pushed: all or nothing. Refused only when a
        // synthesized row actually needs an id.
        let count = u32::try_from(kinds.len()).map_err(|_| IdSpaceExhausted::of::<ProofId>())?;
        let mut ids = self.fresh_obligation_ids().take_run(count)?;
        for (kind, names) in kinds {
            let Some(id) = ids.take() else {
                // The run holds exactly one id per remaining kind.
                return Err(IdSpaceExhausted::of::<ProofId>());
            };
            let description = format!(
                "synthesized from function-level annotation(s) [{}] on `{}`",
                names.join(", "),
                f.name
            );
            self.proof_obligations.push(
                ProofObligation::new(id, kind, ProofStatus::Pending, description)
                    .with_function(f.id),
            );
        }
        Ok(())
    }

    /// The id a new proof obligation takes: one past the highest id in
    /// [`Self::proof_obligations`], or `0` for an empty table, so it never
    /// reuses or collides with an existing row even when the table carries
    /// sparse, producer-assigned ids.
    ///
    /// `None` when no such id exists — a row already holds `u32::MAX` — so a
    /// caller refuses instead of wrapping onto an existing row. It is
    /// [`Self::fresh_obligation_ids`]'s first id: the one rule
    /// ([`FreshIds::after`]), which [`Self::try_add_function`]'s synthesized
    /// obligations and every table-extending builder allocate through.
    pub fn next_obligation_id(&self) -> Option<ProofId> {
        self.fresh_obligation_ids().peek()
    }

    /// Fresh obligation ids: one past the highest id in
    /// [`Self::proof_obligations`], never a recycled gap (a stale `ProofRef` to
    /// a deleted row must not bind a new one). Exhausted when a row holds
    /// `u32::MAX`.
    pub fn fresh_obligation_ids(&self) -> FreshIds<ProofId> {
        FreshIds::after(self.proof_obligations.iter().map(|o| o.id))
    }
}

impl Module {
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

    /// Whether `ty`, as a `FuncTy` parameter or return, is a BY-VALUE
    /// AGGREGATE SLOT ([`StructPassingPolicy`], `docs/SPEC_RATIFICATIONS.md`
    /// §17): after peeling one `Ty::Refine` to its base through `self.types`,
    /// a `Struct`, `Tuple`, `Array`, `Enum`, `Record`, `Sequence`, `Set`,
    /// `Closure`, `Vector` or `Tensor` (a run-time collection, as a sequence
    /// is).
    ///
    /// ONE predicate, stated once: the validator's `AlwaysMemory` rule and its
    /// `pass = indirect` placement rule read it, and a consumer's
    /// struct-passing gate must use it rather than a set of its own. A
    /// refinement has its base's representation, so a refined aggregate is an
    /// aggregate slot. A dangling or nested `Refine` answers `true` (fail
    /// closed: an unresolvable slot is never exempted as a scalar). Scalars,
    /// thin pointers (`Ptr` / `Ref` / `RefMut` / `PtrConst` / `PtrMut` / `Rc` /
    /// `Func`), `Handle`, `FatPtr` (two scalar lanes), `Unit` and `Never` are
    /// not aggregate slots.
    #[must_use]
    pub fn is_by_value_aggregate_slot(&self, ty: &Ty) -> bool {
        let base = match ty {
            Ty::Refine(base, _) => match self.ty(*base) {
                None | Some(Ty::Refine(..)) => return true,
                Some(base) => base,
            },
            other => other,
        };
        matches!(
            base,
            Ty::Struct(_)
                | Ty::Tuple(_)
                | Ty::Array(_, _)
                | Ty::Enum(_)
                | Ty::Record(_)
                | Ty::Sequence(_)
                | Ty::Set(_, _)
                | Ty::Closure(_)
                | Ty::Vector(_, _)
                | Ty::Tensor(_, _)
        )
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

    /// Compute the whole-module stable structural digest — the module's
    /// identity under [`crate::IdentityScheme::CURRENT`] (V3, the PORTABLE
    /// identity) and the build-determinism (G19) fingerprint of this artifact.
    ///
    /// Equal to `self.stable_digest_under(IdentityScheme::V3)`: the canonical
    /// encoding with every [`Module::files`] string projected to `""` (the
    /// table length kept, so span indices and lines stay identity), hashed
    /// under [`crate::MODULE_IDENTITY_DOMAIN`] (`trust_ir.module.v3`). Moving
    /// the checkout a module was compiled from therefore does not move it.
    /// Before v44 this was the V2 digest (whole encoding, paths included);
    /// that identity is still [`Module::stable_digest_under`]
    /// `(IdentityScheme::V2)`, and a `ModuleImport` recorded under it is
    /// still authenticated under it.
    ///
    /// This is the reusable form of the previously-inline digest computed at the
    /// point of signing (`trust-ir-build`'s `ModuleBuilder::sign`). It serializes
    /// the module via [`crate::binary::serialize_module`] — which walks every
    /// arena/table (functions, blocks, instructions, constants, globals, types,
    /// func-types, structs, enums, records, closure-types, proof obligations and
    /// certificates, target info, files, diagnostics, spec modules) in
    /// **declared / insertion (Vec) order** — and then hashes the bytes with the
    /// domain-separated [`crate::proof::ProofDigest::sha256_domain`] hasher
    /// under the domain [`crate::MODULE_IDENTITY_DOMAIN`] (its single
    /// spelling), after the V3 file-string projection. Module digests cross untrusted
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
    /// The digest streams that encoding directly into SHA-256 after a
    /// count-only pass; it does not allocate a whole-module byte buffer.
    pub fn stable_digest(&self) -> crate::proof::ProofDigest {
        self.stable_digest_under(crate::imports::IdentityScheme::CURRENT)
    }

    /// Traverse this module's actual canonical string collection and count/hash
    /// wire passes under the caller's existing original observation session.
    /// This computes identity only; it never validates source or proof claims.
    ///
    /// Signature ABI descriptors traverse their actual encoding-limit and
    /// canonical text/parser round trip under that same original session.
    /// No prefix or partial identity is returned on an unsupported value,
    /// resource refusal, cancellation or scratch-retirement refusal. Physical
    /// allocator latency and disposal of caller-owned inputs remain separate.
    pub fn stable_digest_observed<O: crate::interpret::ExecutionObserver>(
        &self,
        session: &mut crate::interpret::ObservedSession<'_, O>,
        site: crate::interpret::ExecutionSite,
    ) -> Result<crate::proof::ProofDigest, crate::interpret::ObservedValueError> {
        crate::binary::observed_module_identity(
            self,
            crate::imports::IdentityScheme::CURRENT,
            session,
            site,
        )
    }

    /// Compute the same observed identity only when the actual writer accepts
    /// every construct and format count. This includes the writer's existing
    /// `u32::MAX` count check, which the ordinary total identity API deliberately
    /// does not enforce. No full validator, ABI truth, source authority, proof
    /// or admission capability is established by a successful digest.
    pub fn checked_stable_digest_observed<O: crate::interpret::ExecutionObserver>(
        &self,
        session: &mut crate::interpret::ObservedSession<'_, O>,
        site: crate::interpret::ExecutionSite,
    ) -> Result<crate::proof::ProofDigest, crate::interpret::ObservedValueError> {
        crate::binary::observed_checked_module_identity(
            self,
            crate::imports::IdentityScheme::CURRENT,
            session,
            site,
        )
    }

    /// Compute this module's identity under `scheme` — the digest a
    /// [`ModuleImport`] recorded under that scheme is compared with.
    ///
    /// Both schemes hash the same canonical binary plan
    /// ([`crate::binary::ModuleBinaryPlan`]) under their own domain
    /// ([`crate::IdentityScheme::domain`]):
    ///
    /// * [`crate::IdentityScheme::V2`] (`trust_ir.module.v2`) — the whole
    ///   encoding, debug file paths included; every pre-v44 import row;
    /// * [`crate::IdentityScheme::V3`] (`trust_ir.module.v3`) — each
    ///   `files[i]` string projected to `""`, the table length kept.
    ///
    /// Only the debug path STRINGS leave the V3 image: span file indices,
    /// lines and columns, the module name, and every other string stay
    /// identity. The projection is sound only while nothing load-bearing
    /// reads a `files[i]` string (see [`crate::IdentityScheme`]).
    pub fn stable_digest_under(
        &self,
        scheme: crate::imports::IdentityScheme,
    ) -> crate::proof::ProofDigest {
        // The domains are pinned in `imports` so the digest producer and the
        // import verifier share ONE spelling each.
        crate::binary::ModuleBinaryPlan::identity(self, scheme).sha256_domain(scheme.domain())
    }

    /// Compute the v1 identity of this module's executable/codegen-facing
    /// content without its module-level proof sidecars.
    ///
    /// This digest uses the shared v38 binary projection/writer and streams
    /// its projected image, after an exact-length count pass, through
    /// [`crate::proof::ProofDigest::sha256_domain_stream`] under the versioned
    /// domain `"trust_ir.module.executable_content.v1"`. Function bodies use
    /// the canonical block/SSA/parameter-attribute form, so incidental block
    /// storage order, sparse SSA numbering, and trailing empty parameter
    /// attribute rows do not perturb the result. All other retained tables are
    /// emitted deterministically in their declared order, just as they are by
    /// the canonical binary writer.
    ///
    /// # Retained content
    ///
    /// The projection retains the module name; function-type, type, struct,
    /// enum, record, closure-type, universe, and predicate tables; globals;
    /// target triple/layout/ABI information; and every function declaration
    /// or definition, including its id, name, signature, entry/body, calling
    /// convention, linkage, attributes, summary, producer, debug metadata, and
    /// source provenance. Body-less external/import declarations therefore
    /// remain identity-bearing.
    ///
    /// The v41 ABI/linkage residue is retained explicitly, because a linker or
    /// code generator acts on every part of it: the `AvailableExternally` /
    /// `ExternalWeak` / `WeakOdr` / `LinkOnceOdr` linkages on functions and
    /// globals, `FuncAttrs::naked` and `FuncAttrs::target_features`,
    /// `Global::section` / `Global::visibility` / `Global::retained`,
    /// [`Module::global_asm`], and the [`Module::imports`] table.
    ///
    /// Function- and instruction-level [`ProofAnnotation`]s are also retained
    /// exactly when the binary writer can encode them. This intentionally
    /// includes codegen hints and semantic markers such as `InBounds`,
    /// `NoOverflow`, `Pure`, `Aligned`, `ValueRange`, `KnownBits`,
    /// `BranchWeights`, GPU annotations, `Custom`, and `ProofRef`. Node proof
    /// contexts are retained as part of the body too. The feature-gated
    /// `ProofAnnotation::Goal` is the existing exception: it is a proof-formula
    /// payload that the binary writer has always excluded from its stable wire
    /// image.
    ///
    /// # Excluded proof sidecars
    ///
    /// The complete [`Module::proof_obligations`],
    /// [`Module::proof_certificates`], and
    /// [`Module::obligation_diagnostics`] tables are projected to empty before
    /// string pooling and hashing. Consequently changes to an obligation's
    /// kind, status (including `Pending` to `Certified`), description, formula,
    /// source/site metadata, certificate/prover/evidence payload, or diagnostic
    /// text/location do not change this digest unless an on-IR carrier such as
    /// `ProofRef` is changed too. Debug files/spans, spec modules, function
    /// summaries, source provenance, and all other non-sidecar fields are
    /// conservatively retained.
    ///
    /// # Debug file paths stay in (a decision, not an oversight)
    ///
    /// Unlike [`Module::stable_digest`] (V3, WS4.10), this digest KEEPS the
    /// [`Module::files`] path strings and stays at `v1`. It is not an import
    /// identity — nothing authenticates a dependency by it — and its consumers
    /// are codegen caches, for which serving one module's debug names for
    /// another would be a wrong artifact. A moved checkout therefore changes
    /// this digest while leaving the V3 identity unchanged; a `_v2` that
    /// drops the paths is added only if a consumer asks for one.
    ///
    /// # Excluded codegen license
    ///
    /// [`Function::body_gate`] and [`Function::display_path`] are projected to
    /// `None`/absent before string pooling and hashing, and neither raises the
    /// projected wire version on its own. Stamping a license after
    /// verification, or attaching a human def-path, therefore never moves this
    /// identity: the license is a verdict ABOUT this image, and an identity
    /// that changed when the verdict was recorded could never be the identity
    /// the verdict names. A module whose only v41 feature is the license
    /// projects to the exact pre-v41 bytes of the same module unlicensed.
    /// [`Module::stable_digest`], the exact structural identity, still observes
    /// both fields, as do the faithful `ModuleBinaryOptions` projections.
    ///
    /// # Authority boundary
    ///
    /// This is an **identity comparison only**. Equality says that the retained
    /// executable-content projection is byte-identical; it does not validate
    /// either module, prove semantic equivalence, establish that a retained
    /// `ProofRef` resolves, show that any obligation is discharged, authenticate
    /// a certificate, or grant compilation/execution authority. A consumer
    /// acting on proof-backed annotations must independently validate and
    /// recheck the proof sidecar against the exact module.
    #[must_use]
    pub fn executable_content_digest_v1(&self) -> crate::proof::ProofDigest {
        crate::binary::executable_content_digest_v1(self)
    }

    /// The identity of ONE function's body — what [`GateEvidence::body_digest`]
    /// names (domain [`FUNCTION_BODY_DIGEST_V1_DOMAIN`], roadmap WS1.12(c)).
    ///
    /// The preimage is the [`Self::executable_content_digest_v1`] image of a
    /// module holding ONLY this function (no other function, no module
    /// tables, an empty name), so the function's own record — its id, link
    /// symbol, signature id, attributes, linkage, blocks and instructions —
    /// is what is identified; its codegen license and display path are
    /// excluded exactly as that projection excludes them, so stamping the
    /// license (or its evidence) never moves the digest it cites. Type, struct
    /// and function ids are hashed as the indices the body spells: a module
    /// that renumbers them has rewritten the body, and a license citing the
    /// old digest no longer matches (fail-closed — re-mint the evidence).
    /// SSA values, block order and trailing empty parameter attributes are
    /// NOT: that projection writes every function through its canonical plan,
    /// so canonicalization (`format::canonicalize`) keeps a license's evidence
    /// valid, while a transform that changes the canonical image (mem2reg, a
    /// dialect lowering) moves the digest and must drop the evidence
    /// ([`Function::invalidate_gate_evidence`]).
    ///
    /// The image's drop-glue table is the part of the module's that this
    /// body's drops RESOLVE to (amendment D, "Body digest";
    /// `docs/SPEC_RATIFICATIONS.md` §20): one `(glue, ty)` row per
    /// [`Inst::Drop`] / [`Inst::DropInvoke`] site type that has one, in the
    /// table's canonical order. A drop executes as a call of its glue, so
    /// which glue that is changes what the body runs: re-pointing a resolved
    /// drop at another glue, removing its row (the drop becomes unresolved)
    /// or registering glue for a drop that was unresolved each moves the
    /// digest, and a license citing the old one no longer matches. Rows no
    /// drop of this body resolves to are not bound, so a body without drops
    /// keeps the digest it had before the table existed.
    ///
    /// What it does NOT bind: the DEFINITIONS those ids name — the signature's
    /// parameter and return types, struct / enum / record layouts, globals,
    /// callee and drop-glue bodies — are module tables, outside the preimage. The digest
    /// says "this is the body the license was granted to", not "this body
    /// means what it meant": the meaning is the cited obligation's, whose
    /// kernel re-check (WS1.5, on the codegen lane) re-derives it from the
    /// module as it stands.
    ///
    /// # Errors
    ///
    /// When `function` is missing or duplicated, when the function carries a
    /// construct with no binary carrier yet (an instruction ahead of its wire
    /// tag, an inlined scope chain), when it spells the producer-internal
    /// `Ty::Error` (which the binary writer panics on), or when one of its
    /// drops resolves through a malformed drop-glue table (a site type two
    /// rows name, or one glue named for two of its site types) — none of
    /// which has an identity to state. It never panics on a module the writer
    /// would refuse.
    pub fn function_body_digest(
        &self,
        function: FuncId,
    ) -> Result<crate::proof::ProofDigest, String> {
        let mut candidates = self.functions.iter().filter(|f| f.id == function);
        let (Some(target), None) = (candidates.next(), candidates.next()) else {
            return Err(format!(
                "body digest target function #{} is missing or duplicated",
                function.index()
            ));
        };
        if let Some(construct) = target
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .find_map(|node| node.inst.binary_wire_gap())
        {
            return Err(format!(
                "function #{} carries {construct}, which has no binary carrier yet, so the body \
                 has no identity to state",
                function.index()
            ));
        }
        let mut image = Module::new("");
        image.functions.push(target.clone());
        // Amendment D ("Body digest"): the drop-glue rows this body's drops
        // RESOLVE to are part of what the body executes, so they enter the
        // image as its drop-glue table — one row per resolved site type, in
        // the table's canonical (ascending-glue) order. An unresolved drop
        // contributes no row, so registering glue for it later moves the
        // digest; a row no drop of this body resolves to is never bound.
        image.drop_glue = self.function_body_drop_glue(target)?;
        let mut spells_error = false;
        image.visit_types(|ty| spells_error |= matches!(ty, Ty::Error));
        // The minimal binary preimage also emits ABI Cast-piece types, which
        // the general stored-type visitor does not enumerate. Inline children
        // are part of those lane types; referenced module tables are not.
        for slot in target
            .attrs
            .params
            .iter()
            .chain(std::iter::once(&target.attrs.ret))
        {
            if let Some(PassMode::Cast { pieces }) = &slot.pass {
                for ty in pieces {
                    ty.visit_types(|ty| spells_error |= matches!(ty, Ty::Error));
                }
            }
        }
        if spells_error {
            return Err(format!(
                "function #{} spells the producer-internal Ty::Error, which has no binary \
                 spelling, so the body has no identity to state",
                function.index()
            ));
        }
        if let Some((_, scope)) = image.first_inlined_scope_chain() {
            return Err(format!(
                "function #{} lexical scope #{scope} carries an inlining chain link, which has \
                 no binary carrier yet, so the body has no identity to state",
                function.index()
            ));
        }
        let executable = image.executable_content_digest_v1();
        let mut bytes = Vec::with_capacity(1 + 32);
        bytes.push(match executable.algorithm {
            crate::proof::ProofDigestAlgorithm::Sha256 => 0,
            crate::proof::ProofDigestAlgorithm::TrustIrStableV1 => 1,
        });
        bytes.extend_from_slice(&executable.bytes);
        Ok(crate::proof::ProofDigest::sha256_domain(
            FUNCTION_BODY_DIGEST_V1_DOMAIN,
            &bytes,
        ))
    }

    /// The drop-glue rows `function`'s drops resolve to — the part of the
    /// module drop-glue table [`Self::function_body_digest`] binds (amendment
    /// D, "Body digest"). Each [`Inst::Drop`] / [`Inst::DropInvoke`] at type
    /// `T` contributes the one row whose key equals `T`; an unresolved site
    /// contributes nothing. Rows come back in the table's canonical order
    /// (strictly ascending `glue`), each once.
    ///
    /// # Errors
    ///
    /// When a site's type matches two or more rows, or two resolved rows
    /// share one glue: a malformed table (`validate_module` refuses it as
    /// `InvalidDropGlue`) states no single destructor, so the body has no
    /// identity to state.
    fn function_body_drop_glue(&self, function: &Function) -> Result<Vec<DropGlueEntry>, String> {
        let index = self.drop_glue_index();
        let mut rows: Vec<DropGlueEntry> = Vec::new();
        for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
            let ty = match &node.inst {
                Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => ty,
                _ => continue,
            };
            match index.resolve(ty) {
                DropResolution::Unresolved => {}
                DropResolution::Ambiguous => {
                    return Err(format!(
                        "function #{} drops {ty}, which two or more drop-glue rows name, so the \
                         body has no identity to state",
                        function.id.index()
                    ));
                }
                DropResolution::Resolved(glue) => {
                    if let Some(row) = rows.iter().find(|row| row.glue == glue) {
                        if row.ty != *ty {
                            return Err(format!(
                                "function #{} drops {} and {ty} through the one glue @func.{}, \
                                 so the body has no identity to state",
                                function.id.index(),
                                row.ty,
                                glue.index()
                            ));
                        }
                        continue;
                    }
                    let at = rows.partition_point(|row| row.glue.index() < glue.index());
                    rows.insert(
                        at,
                        DropGlueEntry {
                            glue,
                            ty: ty.clone(),
                        },
                    );
                }
            }
        }
        Ok(rows)
    }

    /// The first `(function index, scope index)` whose lexical scope carries
    /// an inlining chain link ([`ScopeData::inlined_at`], WS4.19), if any.
    ///
    /// A scope past `u32::MAX` has no index, so it is not reported here; the
    /// scope table's count is then itself past the format's limit, which
    /// [`Self::wire_image_refusal`] reports.
    ///
    /// Such a module has NO WIRE IDENTITY yet: the binary format has no
    /// carrier for the link (its wire part is a member of the next open wire
    /// batch), so every binary writer refuses it and
    /// [`stable_digest`](Self::stable_digest) /
    /// [`executable_content_digest_v1`](Self::executable_content_digest_v1)
    /// PANIC on it, exactly as they do on an `Inst::MakeAggregate` ahead of
    /// its wire tag. A digest-keyed entry point probes this first and refuses
    /// by name (`trust_ir_build::wire_identity_blocker`). Available in every
    /// feature configuration, unlike the `binary` module's spelling.
    #[must_use]
    pub fn first_inlined_scope_chain(&self) -> Option<(u32, u32)> {
        crate::binary::first_inlined_scope_chain(self)
    }

    /// Why this module has NO WIRE IMAGE, if it has none: the
    /// highest-precedence construct or count the canonical binary writer
    /// refuses in the module's exact encoding.
    ///
    /// This is THE pre-check of every trust-ir entry point that needs a wire
    /// image or a digest (`ProjectedModuleBinaryPlan::try_new`, the native
    /// bundle's `validate`, `trust_ir_build::wire_identity_blocker`, the
    /// CLI's `convert --to bin` and `digest`). It is not a list of constructs:
    /// it is the writer itself, run once over a counting check sink that
    /// reads no payload, and every construct the writer cannot encode is
    /// refused by the writer's own arm (`docs/SPEC_RATIFICATIONS.md`, "A
    /// construct or count with no wire image is refused by the writer's own
    /// arm, at every trust-ir entry point"). So a pre-check cannot omit a
    /// construct the writer refuses — the drift that left the
    /// producer-internal `Ty::Error` out of all four hand-written pre-checks
    /// this replaced.
    ///
    /// Precedence (first wins): an instruction or variant ahead of its wire
    /// tag, a lexical-scope inlining chain link, a completeness claim, a
    /// certificate binding, a typed signature ABI past its encoding limits,
    /// `Ty::Error`, then a count past the format's `u32`. Within a class, the
    /// first the writer meets.
    ///
    /// Cost: one walk of the writer over the module (plus its string-table
    /// collection); it never hashes and never copies a payload.
    #[must_use]
    pub fn wire_image_refusal(&self) -> Option<BinaryProjectionError> {
        self.wire_image_refusals().into_iter().next()
    }

    /// Every refusal class [`Self::wire_image_refusal`] can report that this
    /// module triggers, the first occurrence of each, in precedence order —
    /// for a consumer (the native bundle's `validate`) that reports every
    /// unencodable carrier rather than the first.
    #[must_use]
    pub fn wire_image_refusals(&self) -> Vec<BinaryProjectionError> {
        crate::binary::wire_image_refusals(self)
    }

    /// Complete actual raw binary-writer refusal inventory, first per class
    /// in original precedence order, under the SAME observation session/site.
    /// This DATA check neither hashes a module nor issues proof authority.
    pub fn wire_image_refusals_observed<O: crate::interpret::ExecutionObserver>(
        &self,
        session: &mut crate::interpret::ObservedSession<'_, O>,
        site: crate::interpret::ExecutionSite,
    ) -> Result<Vec<BinaryProjectionError>, crate::interpret::ObservedValueError> {
        crate::binary::observed_wire_image_refusals(self, session, site)
    }

    /// The first `(certificate table index, obligation ID)` whose CleanCic
    /// kernel-recheck directive carries a [`CertificateBinding`], if any.
    ///
    /// Since v61 (`binary::CERTIFICATE_BINDING_FORMAT_VERSION`) the binary
    /// writer carries a binding, so this is no longer a wire blocker: a bound
    /// module is written at v61 or later, and an explicit v38 projection
    /// refuses it by name (`CertificateBindingRequiresV61`) rather than
    /// narrow the binding to `None`. It remains a locator — the table index
    /// distinguishes even malformed duplicate obligation IDs.
    #[must_use]
    pub fn first_certificate_binding(&self) -> Option<(usize, ProofId)> {
        self.proof_certificates
            .iter()
            .enumerate()
            .find_map(|(index, certificate)| match &certificate.evidence {
                ProofEvidence::CleanCic {
                    kernel_recheck: Some(recheck),
                    ..
                } if recheck.binding.is_some() => Some((index, certificate.obligation)),
                _ => None,
            })
    }

    /// Hash the exact containing module and target function while excluding
    /// every [`Function::source_provenance`] field.
    ///
    /// The target function is retained as the sole function in the digest
    /// image, while module/type/global tables and the module name remain. This
    /// binds a carrier to its function and compilation artifact without making
    /// the digest recursively depend on itself or on a sibling carrier.
    ///
    /// The image is hashed under the PORTABLE [`crate::IdentityScheme::V3`]
    /// module identity and sealed under
    /// `trust_ir.source_provenance.semantic_function.v2` (v1 sealed the V2
    /// identity, debug file paths included).
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
        // EXPLICITLY V3, under a seal domain moved to `v2` in the same change
        // (WS4.10): the preimage changed meaning when the module identity
        // stopped hashing debug file paths, so it must not keep the `v1` name.
        // A `v1`-sealed row fails `validate_source_provenance` closed.
        let module_digest = semantic.stable_digest_under(crate::imports::IdentityScheme::V3);
        let mut bytes = Vec::with_capacity(4 + 1 + 32);
        bytes.extend_from_slice(&function.index().to_be_bytes());
        bytes.push(match module_digest.algorithm {
            crate::proof::ProofDigestAlgorithm::Sha256 => 0,
            crate::proof::ProofDigestAlgorithm::TrustIrStableV1 => 1,
        });
        bytes.extend_from_slice(&module_digest.bytes);
        Ok(crate::proof::ProofDigest::sha256_domain(
            "trust_ir.source_provenance.semantic_function.v2",
            &bytes,
        ))
    }

    /// Content-address a `(module, obligation)` pair (v23): the SHA-256
    /// [`ObligationDigest`] used as the WS4-M2 cert-cache key. Returns `None`
    /// when `id` names no obligation in this module; when the obligation's
    /// function scope and site disagree; or when its function/site does not
    /// resolve to an existing function, block, and instruction. Malformed
    /// proof coordinates have no addressable cache content.
    ///
    /// # Identity contract
    ///
    /// The digest is a pure function of the obligation's *claim* and its
    /// owning function's *content*:
    ///
    /// - obligation kind, description, and full formula (schema, payload,
    ///   smtlib, sort);
    /// - embedded source/public identity and the exact optional IR `site`
    ///   (`function`, `block`, and instruction index);
    /// - when the obligation is function-scoped OR has a `site`: the resolved
    ///   owning function's name, its **canonical text form**
    ///   ([`format::canonical`]'s per-function slice: dense SSA renumbering,
    ///   stable block order), its `entry` block, and its `summary` contract
    ///   (`requires`/`ensures`/`params`). `entry` and `summary` are hashed
    ///   explicitly because the canonical text carries neither, yet both are
    ///   proof-relevant: `entry` decides execution order, and a cached
    ///   certificate may have *assumed* the `requires` clauses — weakening a
    ///   contract MUST invalidate its slot.
    ///
    /// Deliberately EXCLUDED: the obligation's [`ProofStatus`] and the
    /// summary's `proved` flag — verification progress is mutable
    /// bookkeeping, not identity (a cache keyed on it would self-invalidate
    /// on discharge) — and the obligation's own `ProofId`/scope `FuncId` plus
    /// every SSA `ValueId` (densely renumbered by the canonical form). That
    /// includes the id inside a `ClausePlace::Value` binding (of the
    /// obligation's formula or of a summary clause): it is hashed as its
    /// CANONICAL id in the owning function, renumbered with the body (roadmap
    /// WS4.4 review), so a binding keeps naming the same value in the key —
    /// a raw id beside a canonical body would let two functions whose `%9`
    /// names different values share one slot. The raw
    /// ids inside an explicit `site` ARE identity: they name the exact
    /// instruction whose check the obligation states.
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
    /// - raw function/block ids inside an explicit obligation `site` (site
    ///   renumbering shifts the digest because the exact coordinate is bound);
    /// - raw `ProofId` indices inside per-call `; #proof_ctx:` clauses
    ///   (proof-table renumbering shifts the digest; `trust-ir-diff` resolves
    ///   them to claim fingerprints).
    #[cfg(feature = "fmt")]
    pub fn obligation_digest(&self, id: ProofId) -> Option<ObligationDigest> {
        let obligation = self.proof_obligations.iter().find(|o| o.id == id)?;
        let function_id = match (obligation.function, obligation.site) {
            (Some(scope), Some(site)) if scope != site.function => return None,
            (Some(scope), _) => Some(scope),
            (None, Some(site)) => Some(site.function),
            (None, None) => None,
        };
        let function = match function_id {
            None => None,
            Some(fid) => Some(self.functions.iter().find(|f| f.id == fid)?),
        };
        if let Some(site) = obligation.site {
            let function = function?;
            let block = function
                .blocks
                .iter()
                .find(|block| block.id == site.block)?;
            let inst_index = usize::try_from(site.inst_index).ok()?;
            if inst_index >= block.body.len() {
                return None;
            }
        }
        let content = function.map(|f| (f, format::canonical_function(f)));
        Some(ObligationDigest(proof::obligation_content_digest(
            obligation,
            content.as_ref().map(|(func, text)| (*func, text.as_str())),
        )))
    }

    /// Build an exact content-digest index for every proof obligation as one
    /// batch.
    ///
    /// The returned [`ObligationDigestIndex`] is deliberately lookup-only: it
    /// has no iteration-order contract, so proof-table or hash-table order can
    /// never become part of a caller's identity protocol. Every keyed entry is
    /// byte-for-byte identical to [`Module::obligation_digest`] for the same
    /// ID on an unambiguous module. Obligations are grouped by owner, so each
    /// owning function is canonicalized at most once and that temporary text
    /// is dropped before the next function is canonicalized.
    ///
    /// This is a fail-closed identity index, not a whole-module validator. It
    /// returns `None` rather than selecting an arbitrary declaration when any
    /// function ID, block ID within a function, or proof ID is duplicated. It
    /// also returns `None` for a dangling function/block/instruction site or a
    /// disagreement between an obligation's function scope and explicit site.
    /// An empty proof table produces an empty index.
    ///
    /// Construction is expected `O(F + B + P + H)` time and
    /// `O(F + B + P + Cmax)` memory, where `Cmax` is the largest one-function
    /// canonical text and `H` is the total input size unavoidably hashed across
    /// all `P` obligations. The canonical text and its digest input remain
    /// exactly the v23 per-ID identity contract documented on
    /// [`Module::obligation_digest`].
    #[cfg(feature = "fmt")]
    pub fn obligation_digest_index(&self) -> Option<ObligationDigestIndex> {
        let mut functions = HashMap::with_capacity(self.functions.len());
        for function in &self.functions {
            match functions.entry(function.id) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(function);
                }
                std::collections::hash_map::Entry::Occupied(_) => return None,
            }
        }

        // Index blocks independently of vector position. Reject every
        // duplicate key up front, including one not currently named by an
        // obligation: this API promises one unambiguous module-wide index.
        let block_count = self.functions.iter().try_fold(0_usize, |count, function| {
            count.checked_add(function.blocks.len())
        })?;
        let mut blocks = HashMap::with_capacity(block_count);
        for function in &self.functions {
            for block in &function.blocks {
                match blocks.entry((function.id, block.id)) {
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        entry.insert(block);
                    }
                    std::collections::hash_map::Entry::Occupied(_) => return None,
                }
            }
        }

        let mut seen_proofs = HashSet::with_capacity(self.proof_obligations.len());
        let mut obligations_by_function: HashMap<FuncId, Vec<&ProofObligation>> = HashMap::new();
        let mut digests = HashMap::with_capacity(self.proof_obligations.len());
        for obligation in &self.proof_obligations {
            if !seen_proofs.insert(obligation.id) {
                return None;
            }

            let function_id = match (obligation.function, obligation.site) {
                (Some(scope), Some(site)) if scope != site.function => return None,
                (Some(scope), _) => Some(scope),
                (None, Some(site)) => Some(site.function),
                (None, None) => None,
            };
            let function = match function_id {
                None => None,
                Some(fid) => Some(*functions.get(&fid)?),
            };
            if let Some(site) = obligation.site {
                let block = blocks.get(&(site.function, site.block))?;
                let inst_index = usize::try_from(site.inst_index).ok()?;
                if inst_index >= block.body.len() {
                    return None;
                }
            }

            match (function_id, function) {
                (Some(fid), Some(_)) => obligations_by_function
                    .entry(fid)
                    .or_default()
                    .push(obligation),
                (None, None) => {
                    let digest =
                        ObligationDigest(proof::obligation_content_digest(obligation, None));
                    match digests.entry(obligation.id) {
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            entry.insert(digest);
                        }
                        std::collections::hash_map::Entry::Occupied(_) => return None,
                    }
                }
                // Kept explicit so a future change to either resolution path
                // cannot silently turn a malformed pairing into a digest.
                _ => return None,
            }
        }
        for (function_id, obligations) in obligations_by_function {
            let function = *functions.get(&function_id)?;
            let canonical = format::canonical_function(function);
            for obligation in obligations {
                let digest = ObligationDigest(proof::obligation_content_digest(
                    obligation,
                    Some((function, canonical.as_str())),
                ));
                match digests.entry(obligation.id) {
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        entry.insert(digest);
                    }
                    std::collections::hash_map::Entry::Occupied(_) => return None,
                }
            }
        }
        if digests.len() != seen_proofs.len() {
            return None;
        }
        Some(ObligationDigestIndex { entries: digests })
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

/// Complete, duplicate-free proof-ID → content-digest lookup for one module.
///
/// This type intentionally exposes keyed lookup but no iterator. There is no
/// entry-order contract: declaration order and randomized hash-table order are
/// both semantically irrelevant. Only the exact [`ProofId`] correlation is
/// meaningful. Instances are minted by [`Module::obligation_digest_index`]
/// after its fail-closed resolution audit.
#[cfg(feature = "fmt")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObligationDigestIndex {
    entries: HashMap<ProofId, ObligationDigest>,
}

#[cfg(feature = "fmt")]
impl ObligationDigestIndex {
    /// Number of distinct proof IDs in the complete index.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the indexed module contained no proof obligations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Look up one exact proof ID without relying on declaration order.
    #[must_use]
    pub fn get(&self, id: ProofId) -> Option<ObligationDigest> {
        self.entries.get(&id).copied()
    }

    /// Consume one exact proof-ID binding from the index.
    ///
    /// Batch consumers can remove every expected ID and finish by requiring
    /// [`Self::is_empty`], proving both absence of gaps and absence of extras
    /// without a second index or a quadratic table scan.
    #[must_use]
    pub fn remove(&mut self, id: ProofId) -> Option<ObligationDigest> {
        self.entries.remove(&id)
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
        origin,
    } = a;
    *name == b.name
        && *fields == b.fields
        && *size == b.size
        && *align == b.align
        && *repr == b.repr
        // A nominal key SPLITS: two defs that agree in every byte of
        // structure but name different source entities are two types, and
        // deduping them here would merge them behind the validator's back.
        && *origin == b.origin
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
        origin,
    } = a;
    *name == b.name
        && *variants == b.variants
        && *discriminants == b.discriminants
        && *repr == b.repr
        && *layout == b.layout
        && *origin == b.origin
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
pub struct FunctionG<X> {
    pub id: FuncId,
    /// The function's LINK-TIME SYMBOL — normative since v41.
    ///
    /// This is name-keyed identity ACROSS modules: consumers emit it verbatim
    /// as the object symbol, merge/dedup on it (definition upgrades
    /// declaration), and resolve call relocations through it. It is therefore
    /// NOT a display name. A producer whose source identity is not injective
    /// onto symbols must mangle before stamping, and put the readable form in
    /// [`Function::display_path`] instead.
    ///
    /// `validate_module` rejects two functions sharing a name
    /// (`DuplicateFunctionSymbol`): an ambiguous symbol silently conflates two
    /// bodies at link time, which is worse than a refusal.
    pub name: String,
    pub ty: FuncTyId,
    pub entry: BlockId,
    pub blocks: Vec<BlockG<X>>,
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
    /// Must-refuse corpus row `refuse/source_provenance_stale_body_digest`:
    /// a carrier whose semantic-body digest is not the body's is refused by
    /// `validate_module` (`InvalidSourceProvenance`), which rederives it.
    ///
    /// ALWAYS emitted by serde since v41 (no `skip_serializing_if`; `None`
    /// encodes as nil) — the v23/v32/v33/v35 move re-applied per its own
    /// instruction: `display_path` is now the sole trailing conditionally
    /// skipped field, so `source_provenance` must be always-present to keep
    /// its positional index.
    #[cfg_attr(feature = "serde", serde(default))]
    pub source_provenance: Option<SourceProvenance>,
    /// The machine-checkable codegen license for this body (v41). See
    /// [`BodyGate`]: `None` means NO CLAIM (the pre-v41 grandfather state),
    /// which is NOT the same as `Some(BodyGate::Ungated)`.
    ///
    /// This is AUTHORITY metadata, not a debug claim. Unlike `value_names` and
    /// `scopes`, a wrong value here changes whether a backend may emit code,
    /// so ordinary transforms must PRESERVE it — never clear it. Clearing
    /// `Ungated` to `None` would launder a below-tier body into the
    /// grandfathered-permit state. A transform that REWRITES the body (or
    /// drops the obligation a license cites) must drop the license's
    /// [`GateEvidence`], keeping the authority: the evidence names the old
    /// body's digest and would be refused as `GatedEvidenceMismatch`.
    ///
    /// ALWAYS emitted by serde since v41 (no `skip_serializing_if`; `None`
    /// encodes as nil), so `display_path` keeps the sole trailing slot.
    #[cfg_attr(feature = "serde", serde(default))]
    pub body_gate: Option<BodyGate>,
    /// Human-readable definition path for coverage rows and diagnostics (v41)
    /// — e.g. `core::ptr::drop_in_place::<alloc::string::String>`.
    ///
    /// This exists because [`Function::name`] is normatively the LINK-TIME
    /// SYMBOL. A producer that wants to keep a readable def-path puts it HERE;
    /// putting it in `name` makes the symbol unlinkable. Claim-style metadata:
    /// no operational semantics, never proof-bearing, never a linkage identity.
    ///
    /// ALWAYS emitted by serde since v45 (no `skip_serializing_if`; `None`
    /// encodes as nil) — the v23/v32/v33/v35/v41 move re-applied per its own
    /// instruction: `retained` is now the sole trailing conditionally skipped
    /// field, so `display_path` must be always-present to keep its positional
    /// index. `default` still decodes every older, shorter array to `None`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub display_path: Option<String>,
    /// Explicit output section for this function's code, e.g. `.text.startup`
    /// or `__TEXT,__text_cold` (v45, roadmap WS3.10 / F-053). `None` means the
    /// consumer picks the default text section, as before v45.
    ///
    /// Mirrors [`Global::section`]. `trust_ir_build::validate_module` refuses a
    /// blank name or one containing NUL (`InvalidFunctionSection`), and a
    /// section on a pinned handle entry point.
    #[cfg_attr(feature = "serde", serde(default))]
    pub section: Option<String>,
    /// Symbol visibility (v45, roadmap WS3.10 / F-053). Orthogonal to
    /// [`Function::linkage`]; see [`Visibility`]. `(External, Hidden)` is
    /// rustc's default for a non-exported cross-CGU function, which before
    /// v45 had no spelling at all.
    ///
    /// On a bodyless declaration this is the visibility the IMPORT requests.
    /// `Hidden`/`Protected` together with `Internal`/`Private` linkage is
    /// contradictory (a module-local symbol has no cross-image visibility to
    /// restrict) and is refused (`ContradictoryFunctionVisibility`); a pinned
    /// handle entry point must stay `Default`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub visibility: Visibility,
    /// `#[used]`-style retention (v45): keep this function even when nothing
    /// in the module references it. Mirrors [`Global::retained`].
    ///
    /// Declared LAST and conditionally skipped (`false`): the sole trailing
    /// skip, so every pre-v45 positional serde array still decodes (with
    /// `Default` visibility, no section, not retained).
    #[cfg_attr(feature = "serde", serde(default, skip_serializing_if = "is_false"))]
    pub retained: bool,
}

/// The level-R function: [`FunctionG`] with no extension.
pub type Function = FunctionG<level::NoExt>;

impl<X> FunctionG<X> {
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
            body_gate: None,
            display_path: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        }
    }
}

impl<X> FunctionG<X> {
    /// True iff this function uses any v45 symbol attribute: a non-default
    /// visibility, an explicit section, or retention. The binary writer
    /// selects v45 exactly when some function (or another v45 feature) does.
    #[must_use]
    pub fn has_symbol_attributes(&self) -> bool {
        self.visibility != Visibility::Default || self.section.is_some() || self.retained
    }
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
// Field-level `skip_serializing_if` is deliberately NOT used on any field but
// the LAST: the canonical MessagePack codec (`rmp_serde::to_vec`, used by the
// `trust-ir` CLI) encodes structs POSITIONALLY, where a skipped non-trailing
// field shifts every later field out of position on decode. So every field is
// always-present except the single trailing one, `effects` (v59), whose skip
// keeps every pre-v59 JSON / MessagePack summary byte-identical; a struct may
// carry at most ONE trailing skipped field, and this is it.
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
    ///
    /// "Backed" is per clause (WS1.3): for a definition, each clause needs a
    /// Discharged/Certified obligation of the role's kind, scoped to the
    /// function, whose `formula` equals the clause (bindings included); a
    /// body-less declaration is backed only by `backed_by`. `trust-ir-build`'s
    /// validator enforces this — the bit is a derived claim it re-checks.
    #[cfg_attr(feature = "serde", serde(default))]
    pub proved: bool,
    /// Well-founded termination measures, in declaration order (v41).
    ///
    /// The descent conditions — each measure strictly decreases on every back
    /// edge, and is bounded below — are REGENERABLE from these at the root, so
    /// a separately compiled caller does not have to take `proved` on faith for
    /// termination. Before this field the shipping compiler's `decreases`
    /// clause was simply dropped at the IR boundary.
    ///
    /// No `skip_serializing_if`: the struct-level note above makes
    /// always-emitted a local rule for every field here, not a preference.
    #[cfg_attr(feature = "serde", serde(default))]
    pub decreases: Vec<ProofFormula>,
    /// What AUTHENTICATES [`FunctionSummary::proved`] (v41).
    ///
    /// `proved` is a bare `bool` with nothing naming what established it. On a
    /// summary that was verified in THIS module that is merely thin — the
    /// module's own obligations and certificates are right there. On a summary
    /// that arrived from a separately compiled crate it is a bare assertion
    /// with no referent at all: the module carries no crate identity, so a
    /// consumer reading `proved: true` on an imported contract has literally
    /// nothing to check.
    ///
    /// `Some(r)` says the bit is backed by [`ExternRef::obligation`] of
    /// [`ExternRef::symbol`] in the imported module [`ExternRef::module`],
    /// which a consumer authenticates by re-deriving
    /// [`crate::Module::stable_digest`] over the artifact it loaded and
    /// comparing against [`crate::ModuleImport::digest`].
    ///
    /// `None` means NOT RECORDED — never "backed locally" and never "trust the
    /// bit". A fail-closed consumer treats an imported `proved: true` with no
    /// `backed_by` as unauthenticated, exactly as it treats a v34 `site = None`
    /// as unbindable.
    ///
    /// No `skip_serializing_if`, per the struct-level rule above.
    #[cfg_attr(feature = "serde", serde(default))]
    pub backed_by: Option<ExternRef>,
    /// What a call may do to the world: the memory it reads and writes, and
    /// whether it allocates, frees, unwinds or performs I/O (v59, roadmap
    /// WS1.14 / F-013). See [`crate::effects`].
    ///
    /// `None` means UNRECORDED — a caller havocs the world across the call,
    /// exactly as before v59 — never "no effects"; the affirmative pure claim
    /// is `Some(EffectSummary::pure())`. On a DEFINITION the claim is checked
    /// against the body by `trust_ir_build::validate_module`
    /// (`EffectSummaryViolated`). On a body-less DECLARATION it is a claim a
    /// caller's frame check may use only once `validate_linked_module` has
    /// authenticated the declaration's `backed_by` (the far effects restated
    /// exactly); otherwise a caller treats it as `None`.
    ///
    /// It is part of what the contract MEANS, so it enters
    /// `obligation_content_digest` (`trust_ir.obligation.digest.v8`).
    ///
    /// Declared LAST and skipped when `None`: the sole trailing skipped field
    /// (see the struct-level note), so every pre-v59 serde spelling decodes to
    /// `None` and re-encodes byte-identically.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub effects: Option<EffectSummary>,
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

    /// Append a well-founded termination measure
    /// ([`FunctionSummary::decreases`], v41).
    ///
    /// Records the measure only. It asserts nothing about descent and does not
    /// set `proved`: the descent conditions are regenerated from the measure
    /// at the root and discharged there.
    #[must_use]
    pub fn decreasing(mut self, measure: ProofFormula) -> Self {
        self.decreases.push(measure);
        self
    }

    /// Mark the summary's clauses as discharged (assumable by callers).
    #[must_use]
    pub fn proved(mut self) -> Self {
        self.proved = true;
        self
    }

    /// Name the cross-crate obligation that authenticates
    /// [`FunctionSummary::proved`]. Does NOT set `proved` — asserting the bit
    /// and citing what backs it are two separate acts, and a helper that did
    /// both would let a producer mint an authenticated-looking summary by
    /// naming a reference it never checked.
    #[must_use]
    pub fn backed_by(mut self, reference: ExternRef) -> Self {
        self.backed_by = Some(reference);
        self
    }

    /// Record the call's effect summary ([`FunctionSummary::effects`], v59).
    /// Records the claim only; `trust_ir_build` decides whether a body honours
    /// it.
    #[must_use]
    pub fn with_effects(mut self, effects: EffectSummary) -> Self {
        self.effects = Some(effects);
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
    /// Every value id this function DEFINES: block parameters and instruction
    /// results, in block order. The one spelling of "the function's value
    /// ids"; [`Self::max_value_id`] and [`Self::fresh_value_ids`] read it.
    pub fn value_ids(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.blocks.iter().flat_map(|block| {
            block.params.iter().map(|(id, _)| *id).chain(
                block
                    .body
                    .iter()
                    .flat_map(|node| node.results.iter().copied()),
            )
        })
    }

    /// Every block id this function's block list carries, in order.
    pub fn block_ids(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.blocks.iter().map(|block| block.id)
    }

    /// Fresh value ids for new definitions in this function: one past the
    /// highest id [`Self::value_ids`] yields, refused (never wrapped) when a
    /// definition holds `u32::MAX`.
    ///
    /// "Fresh" is relative to the DEFINED ids: on an unvalidated function a
    /// dangling use above them can be captured by a new definition. The
    /// validator's undefined-use refusal is the guard.
    pub fn fresh_value_ids(&self) -> FreshIds<ValueId> {
        FreshIds::after(self.value_ids())
    }

    /// Fresh block ids: one past the highest id in [`Self::block_ids`].
    pub fn fresh_block_ids(&self) -> FreshIds<BlockId> {
        FreshIds::after(self.block_ids())
    }

    /// Returns the maximum `ValueId` currently used in this function
    /// (parameters or instructions), or `0` when it defines none.
    ///
    /// `0` is ambiguous: it means both "no value" and "only `%0`", so
    /// `max_value_id() + 1` is not a fresh id (and overflows at `u32::MAX`).
    /// New code mints ids through [`Self::fresh_value_ids`].
    pub fn max_value_id(&self) -> u32 {
        self.value_ids().map(ValueId::index).max().unwrap_or(0)
    }
}

/// [`Module::try_add_function`] refused: a synthesized obligation needs an
/// id and the obligation id space is exhausted. The function is returned
/// (boxed), untouched and not pushed.
#[derive(Debug, Clone, PartialEq)]
pub struct AddFunctionError {
    /// The exhausted space (`ProofId`).
    pub exhausted: IdSpaceExhausted,
    /// The function that was not added.
    pub function: Box<Function>,
}

impl core::fmt::Display for AddFunctionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "cannot add function `{}`: {}",
            self.function.name, self.exhausted
        )
    }
}

impl std::error::Error for AddFunctionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.exhausted)
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
            body_gate: None,
            display_path: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
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

    /// Stamp the codegen license on this function (v41). See [`BodyGate`] —
    /// note that leaving it unset is `None` ("no claim"), which is distinct
    /// from `BodyGate::Ungated` ("affirmatively not gated").
    #[must_use]
    pub fn with_body_gate(mut self, gate: BodyGate) -> Self {
        self.body_gate = Some(gate);
        self
    }

    /// Attach a human-readable definition path (v41). Never a link symbol —
    /// see [`Function::display_path`].
    #[must_use]
    pub fn with_display_path(mut self, path: impl Into<String>) -> Self {
        self.display_path = Some(path.into());
        self
    }

    /// Place this function in an explicit output section (v45).
    #[must_use]
    pub fn with_section(mut self, section: impl Into<String>) -> Self {
        self.section = Some(section.into());
        self
    }

    /// Set this function's symbol visibility (v45). See [`Visibility`].
    #[must_use]
    pub fn with_visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
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

    /// Drop the [`GateEvidence`] of this function's `Gated` license, keeping
    /// the license and its authority (binary v61, roadmap WS1.12(c)).
    ///
    /// What every transform that REWRITES the body must do — the source
    /// provenance carrier's rule, applied to the license: the evidence names
    /// the digest of the body it was granted to, so after a rewrite it would
    /// name the old body and be refused as a stale license
    /// (`GatedEvidenceMismatch`). Dropping it leaves NO EVIDENCE RECORDED, the
    /// pre-v61 meaning, which a consumer that requires evidence still refuses;
    /// it never re-stamps a digest the transform did not earn. Returns whether
    /// evidence was dropped.
    pub fn invalidate_gate_evidence(&mut self) -> bool {
        match &mut self.body_gate {
            Some(BodyGate::Gated { evidence, .. }) => evidence.take().is_some(),
            _ => false,
        }
    }

    /// True iff this function is a body-less [`Linkage::ExternalWeak`]
    /// declaration: an import whose symbol may resolve to NULL at link time.
    ///
    /// Such a declaration is a valid import (and an FFI boundary), but its
    /// address is nullable, so `trust-ir-build` refuses a direct `Call` /
    /// `Invoke` of it (and a `SeqMap` naming it as `fwd`) and any `Ty::Func` /
    /// `Ty::Closure` spelling of it; the one
    /// admitted address-take is `Const SymbolAddr { symbol, addend: 0 } : Ptr`,
    /// which the producer compares against `NullPtr` before a `CallIndirect`
    /// that must declare this function's exact convention and signature (and
    /// no `Switch` case may name it).
    /// A BODIED `ExternalWeak` function is not a weak declaration.
    #[must_use]
    pub fn is_weak_declaration(&self) -> bool {
        self.blocks.is_empty() && self.linkage == Linkage::ExternalWeak
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
pub struct BlockG<X> {
    pub id: BlockId,
    pub params: Vec<(ValueId, TyG<X>)>,
    pub body: Vec<node::InstrNodeG<X>>,
}

/// The level-R basic block: [`BlockG`] with no extension.
pub type Block = BlockG<level::NoExt>;

impl<X> BlockG<X> {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            params: Vec::new(),
            body: Vec::new(),
        }
    }

    pub fn with_param(mut self, value: ValueId, ty: TyG<X>) -> Self {
        self.params.push((value, ty));
        self
    }
}

impl Block {
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
pub struct GlobalG<X> {
    pub name: String,
    pub ty: TyG<X>,
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
    /// Explicit output section, e.g. `.text.startup` or `__DATA,__mysection`
    /// (v41). `None` means the consumer picks by mutability/initializer, as
    /// before.
    #[cfg_attr(feature = "serde", serde(default))]
    pub section: Option<String>,
    /// Symbol visibility (v41). Orthogonal to `linkage`; see [`Visibility`].
    #[cfg_attr(feature = "serde", serde(default))]
    pub visibility: Visibility,
    /// `#[used]` retention (v41): keep this global even with no in-module
    /// reference.
    ///
    /// Without it a conformant consumer may legally drop an `Internal` global
    /// nothing references — which is exactly the case `#[used]` exists to
    /// prevent, and how a linker-section registration array silently vanishes.
    ///
    /// No `is_false` skip: `Global` carries ZERO `skip_serializing_if` fields
    /// by the local rule in the `tls` docstring above.
    #[cfg_attr(feature = "serde", serde(default))]
    pub retained: bool,
}

/// The level-R global: [`GlobalG`] with no extension.
pub type Global = GlobalG<level::NoExt>;

#[cfg(test)]
mod construction_door_tests;

#[cfg(test)]
mod tests {
    use super::*;

    /// `docs/SPEC_RATIFICATIONS.md` §17: the ONE by-value-aggregate slot
    /// predicate, row by row. Its readers are the validator's `AlwaysMemory`
    /// rule, its `pass = indirect` placement rule, and every consumer's
    /// struct-passing gate.
    #[test]
    fn is_by_value_aggregate_slot_table() {
        let mut module = Module::new("by_value_aggregate_slot");
        let struct_ty = module
            .add_type(Ty::Struct(StructId::new(0)))
            .expect("Module::add_type: test fixture");
        let refined_ty = module
            .add_type(Ty::Refine(struct_ty, PredId::new(0)))
            .expect("Module::add_type: test fixture");
        let scalar_ty = module
            .add_type(Ty::I64)
            .expect("Module::add_type: test fixture");
        let dangling = TyId::new(u32::MAX);
        let rows: Vec<(Ty, bool, &str)> = vec![
            (Ty::Struct(StructId::new(0)), true, "struct"),
            (Ty::Tuple(vec![Ty::I32, Ty::I32]), true, "tuple"),
            (Ty::Array(scalar_ty, 4), true, "array"),
            (Ty::Enum(EnumId::new(0)), true, "enum"),
            (Ty::Record(RecordId::new(0)), true, "record"),
            (Ty::Sequence(scalar_ty), true, "sequence"),
            (Ty::Set(scalar_ty, SetRepr::Boxed), true, "set"),
            (Ty::Closure(ClosureTyId::new(0)), true, "closure"),
            (Ty::Vector(Box::new(Ty::I32), 4), true, "vector"),
            (Ty::Tensor(Box::new(Ty::I32), 2), true, "tensor"),
            (
                Ty::Refine(struct_ty, PredId::new(0)),
                true,
                "refined struct",
            ),
            (
                Ty::Refine(dangling, PredId::new(0)),
                true,
                "dangling refine (fail closed)",
            ),
            (
                Ty::Refine(refined_ty, PredId::new(0)),
                true,
                "nested refine (fail closed)",
            ),
            (
                Ty::Refine(scalar_ty, PredId::new(0)),
                false,
                "refined scalar",
            ),
            (Ty::I64, false, "scalar"),
            (Ty::Ptr, false, "thin pointer"),
            (Ty::Ref(Box::new(Ty::I64)), false, "reference"),
            (Ty::Func(FuncTyId::new(0)), false, "function value"),
            (
                Ty::FatPtr(ty::FatPtrKind::Str),
                false,
                "fat pointer (two scalar lanes)",
            ),
            (
                Ty::Handle(Box::new(ty::HandleTy {
                    name: "Nat".into(),
                    runtime: "trust_bignum::Nat".into(),
                })),
                false,
                "handle",
            ),
            (Ty::Unit, false, "unit"),
            (Ty::Never, false, "never"),
        ];
        for (ty, expected, what) in rows {
            assert_eq!(
                module.is_by_value_aggregate_slot(&ty),
                expected,
                "{what}: {ty}"
            );
        }
    }

    #[test]
    fn function_catalog_scans_many_edges_to_sparse_ids_without_table_rescans() {
        const PADDING_FUNCTIONS: u32 = 1_024;
        const DIRECT_CALLS: usize = 2_048;

        let mut module = Module::new("many-edge-catalog");
        let mut caller = Function::new(FuncId::new(7), "caller", FuncTyId::new(0), BlockId::new(0));
        caller.calling_conv = CallingConv::Rust;
        let mut caller_block = Block::new(BlockId::new(0));
        for _ in 0..DIRECT_CALLS {
            caller_block.body.push(InstrNode::new(Inst::Call {
                callee: FuncId::new(u32::MAX - 1),
                args: vec![],
            }));
        }
        caller_block.body.push(InstrNode::new(Inst::Call {
            callee: FuncId::new(u32::MAX),
            args: vec![],
        }));
        caller_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        caller.blocks.push(caller_block);
        module.functions.push(caller);

        for id in 0..PADDING_FUNCTIONS {
            let mut function = Function::new(
                FuncId::new(10_000 + id),
                format!("padding_{id}"),
                FuncTyId::new(0),
                BlockId::new(0),
            );
            function.calling_conv = CallingConv::Rust;
            let mut block = Block::new(BlockId::new(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            function.blocks.push(block);
            module.functions.push(function);
        }

        for (id, name, convention) in [
            (u32::MAX - 1, "rust_target", CallingConv::Rust),
            (u32::MAX, "foreign_target", CallingConv::C),
        ] {
            let mut function =
                Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
            function.calling_conv = convention;
            let mut block = Block::new(BlockId::new(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            function.blocks.push(block);
            module.functions.push(function);
        }

        let catalog = ModuleFunctionCatalog::new(&module);
        assert_eq!(catalog.len(), PADDING_FUNCTIONS as usize + 3);
        assert_eq!(
            catalog
                .unique(FuncId::new(u32::MAX - 1))
                .map(|f| f.name.as_str()),
            Some("rust_target")
        );
        let expected = "cross-convention call edge `caller` (rustcc) -> `foreign_target` (ccc)";
        assert_eq!(catalog.first_ffi_boundary().as_deref(), Some(expected));
        assert_eq!(module.first_ffi_boundary().as_deref(), Some(expected));
    }

    #[test]
    fn function_catalog_never_selects_an_ambiguous_sparse_target() {
        let sparse = FuncId::new(u32::MAX);
        let mut module = Module::new("ambiguous-catalog");
        let mut caller = Function::new(FuncId::new(1), "caller", FuncTyId::new(0), BlockId::new(0));
        caller.calling_conv = CallingConv::Rust;
        let mut block = Block::new(BlockId::new(0));
        block.body.push(InstrNode::new(Inst::Call {
            callee: sparse,
            args: vec![],
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        caller.blocks.push(block);
        module.functions.push(caller);

        for (name, convention) in [
            ("foreign_candidate", CallingConv::C),
            ("rust_candidate", CallingConv::Rust),
        ] {
            let mut function = Function::new(sparse, name, FuncTyId::new(0), BlockId::new(0));
            function.calling_conv = convention;
            let mut block = Block::new(BlockId::new(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            function.blocks.push(block);
            module.functions.push(function);
        }

        let catalog = ModuleFunctionCatalog::new(&module);
        assert_eq!(catalog.ambiguous_ids().collect::<Vec<_>>(), vec![u32::MAX]);
        assert!(catalog.unique(sparse).is_none());
        assert!(catalog.first_ffi_boundary().is_none());
        assert!(module.first_ffi_boundary().is_none());
    }

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
            "source_provenance",
            "body_gate",
            "display_path",
            "section",
            "visibility",
            // `retained` is NOT here: as of v45 it is the sole trailing
            // skipped field. `display_path` (the v41 trailing skip) and the
            // v45 `section` / `visibility` are now always emitted at their
            // stable positional indices — the v41 note this replaces said the
            // same thing about `source_provenance` and `body_gate`.
        ];
        expected.sort_unstable();
        assert_eq!(keys, expected, "positional-index discipline broken: {json}");
        let back: Function = serde_json::from_str(&json).expect("deserialize");
        assert!(back.summary.is_none());
        assert!(back.producer.is_none());
        assert!(back.value_names.is_none());
        assert!(back.scopes.is_none());
        assert!(back.source_provenance.is_none());
        assert!(
            back.body_gate.is_none(),
            "an absent body gate is `None` (no licensing claim), never `Ungated`"
        );
        assert!(back.display_path.is_none());
        assert!(back.section.is_none());
        assert_eq!(back.visibility, Visibility::Default);
        assert!(!back.retained);

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
                inlined_at: None,
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
        use crate::proof::{ClauseBinding, ClausePlace, ClauseSort};
        let mk = |smtlib: Option<&str>, sort: Option<&str>, bound: bool| crate::ProofFormula {
            schema: "trust-types.Formula@1".into(),
            payload: "p".into(),
            smtlib: smtlib.map(str::to_string),
            sort: sort.map(str::to_string),
            bindings: if bound {
                vec![(
                    "x".to_string(),
                    ClauseBinding {
                        sort: ClauseSort::BitVec(64),
                        place: ClausePlace::Param { index: 0 },
                    },
                )]
            } else {
                Vec::new()
            },
        };
        // The cross product matters: `sort` stopped being the trailing field in
        // v41, so a `sort: None` paired with non-empty `bindings` is exactly the
        // shape that silently shifted fields before the flip.
        for pf in [
            mk(None, Some("Bool"), false),
            mk(Some("(>= x 0)"), None, false),
            mk(None, None, false),
            mk(Some("(>= x 0)"), Some("Bool"), false),
            mk(None, None, true),
            mk(None, Some("Bool"), true),
            mk(Some("(>= x 0)"), None, true),
            mk(Some("(>= x 0)"), Some("Bool"), true),
        ] {
            let bytes = rmp_serde::to_vec(&pf).expect("encode ProofFormula");
            let back: crate::ProofFormula =
                rmp_serde::from_slice(&bytes).expect("decode ProofFormula");
            assert_eq!(
                back, pf,
                "ProofFormula smtlib/sort/bindings must survive positional msgpack"
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
            spec: None,
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
            spec: None,
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
            spec: None,
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
            spec: None,
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
            spec: None,
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
            spec: None,
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
            spec: None,
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
        let t0 = module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        let t1 = module
            .add_type(Ty::I64)
            .expect("Module::add_type: test fixture");
        let t2 = module
            .add_type(Ty::F64)
            .expect("Module::add_type: test fixture");
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
        let ft0 = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let ft1 = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
            origin: None,
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
            origin: None,
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
            origin: None,
        }
    }

    #[test]
    fn add_struct_def_dedups_structurally_identical_defs() {
        let mut module = Module::new("dedup");
        let a = module
            .add_struct_def(point_struct(0, "Point", Ty::I64))
            .expect("Module::add_struct_def: test fixture");
        // Same def again — even under a DIFFERENT declared id — returns the
        // original id and inserts nothing.
        let b = module
            .add_struct_def(point_struct(9, "Point", Ty::I64))
            .expect("Module::add_struct_def: test fixture");
        assert_eq!(a, b);
        assert_eq!(module.structs.len(), 1);
        // A structurally different def (other field type) is a new entry.
        let c = module
            .add_struct_def(point_struct(1, "Point", Ty::F64))
            .expect("Module::add_struct_def: test fixture");
        assert_ne!(a, c);
        assert_eq!(module.structs.len(), 2);
    }

    #[test]
    fn add_struct_def_never_allows_colliding_ids() {
        let mut module = Module::new("collide");
        let a = module
            .add_struct_def(point_struct(0, "A", Ty::I64))
            .expect("Module::add_struct_def: test fixture");
        // Different content under the SAME declared id: gets a fresh id.
        let b = module
            .add_struct_def(point_struct(0, "B", Ty::I64))
            .expect("Module::add_struct_def: test fixture");
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
        assert_eq!(
            module
                .allocate_struct_id()
                .expect("Module::allocate_struct_id: test fixture"),
            StructId::new(0)
        );
        // A sparse producer-assigned id pushes the allocator past it.
        module.add_struct(point_struct(7, "Sparse", Ty::I64));
        let id = module
            .allocate_struct_id()
            .expect("Module::allocate_struct_id: test fixture");
        assert_eq!(id, StructId::new(8));
        // Reserve-by-insert: registering under the allocated id advances it.
        let mut sd = point_struct(0, "Next", Ty::F64);
        sd.id = id;
        assert_eq!(
            module
                .add_struct_def(sd)
                .expect("Module::add_struct_def: test fixture"),
            id
        );
        assert_eq!(
            module
                .allocate_struct_id()
                .expect("Module::allocate_struct_id: test fixture"),
            StructId::new(9)
        );
    }

    #[test]
    fn add_enum_def_dedups_and_never_collides() {
        let mut module = Module::new("enums");
        let a = module
            .add_enum_def(option_enum(0, "Option", Ty::I32))
            .expect("Module::add_enum_def: test fixture");
        // Structural duplicate under another id dedups to the original.
        let b = module
            .add_enum_def(option_enum(5, "Option", Ty::I32))
            .expect("Module::add_enum_def: test fixture");
        assert_eq!(a, b);
        assert_eq!(module.enums.len(), 1);
        // Different payload type = different def; same declared id must not
        // collide.
        let c = module
            .add_enum_def(option_enum(0, "Option", Ty::I64))
            .expect("Module::add_enum_def: test fixture");
        assert_ne!(a, c);
        assert_eq!(module.enums.len(), 2);
        assert_eq!(
            module.enum_def(c).unwrap().variants[1].fields,
            vec![Ty::I64]
        );
        // Allocator sits past both.
        assert_eq!(
            module
                .allocate_enum_id()
                .expect("Module::allocate_enum_id: test fixture"),
            EnumId::new(2)
        );
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

            section: None,
            visibility: Default::default(),
            retained: false,
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

            section: None,
            visibility: Default::default(),
            retained: false,
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

            section: None,
            visibility: Default::default(),
            retained: false,
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let c0 = module
            .add_closure_type(ClosureTy::bare(ft))
            .expect("Module::add_closure_type: test fixture");
        let c1 = module
            .add_closure_type(ClosureTy {
                func: ft,
                captures: vec![Ty::I32, Ty::Bool],
            })
            .expect("Module::add_closure_type: test fixture");
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
        let tid = module
            .add_type(Ty::Record(rid))
            .expect("Module::add_type: test fixture");
        assert_eq!(module.types[tid.as_usize()], Ty::Record(rid));
    }

    #[test]
    fn module_ty_closure_roundtrip() {
        let mut module = Module::new("tc");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let cid = module
            .add_closure_type(ClosureTy::bare(ft))
            .expect("Module::add_closure_type: test fixture");
        let tid = module
            .add_type(Ty::Closure(cid))
            .expect("Module::add_type: test fixture");
        assert_eq!(module.types[tid.as_usize()], Ty::Closure(cid));
    }

    #[test]
    fn module_add_function() {
        let mut module = Module::new("test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let func = Function::new(FuncId::new(0), "noop", ft, BlockId::new(0));
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "noop");
        // A claim-free function synthesizes no obligations.
        assert!(module.proof_obligations.is_empty());
    }

    // --- roadmap §1.1: add_function obligation synthesis ---

    #[test]
    fn next_obligation_id_is_one_past_the_highest_and_refuses_exhaustion() {
        let row = |id: u32| {
            ProofObligation::new(
                ProofId::new(id),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "row",
            )
        };
        let mut module = Module::new("next_id");
        assert_eq!(module.next_obligation_id(), Some(ProofId::new(0)));
        // Sparse, out-of-order producer ids: past the HIGHEST, not the last.
        module.proof_obligations = vec![row(7), row(3)];
        assert_eq!(module.next_obligation_id(), Some(ProofId::new(8)));
        module.proof_obligations.push(row(u32::MAX - 1));
        assert_eq!(module.next_obligation_id(), Some(ProofId::new(u32::MAX)));
        // No id is left: refused, never wrapped onto row 0.
        module.proof_obligations.push(row(u32::MAX));
        assert_eq!(module.next_obligation_id(), None);
    }

    /// r11 item 6 (port of probe P7(a), evidence kind ii): a DECODED table may
    /// hold obligation id `u32::MAX`, and then a claim-bearing function has no
    /// id for its synthesized row. `try_add_function` refuses all or nothing —
    /// the function comes back, no row and no function is pushed, and the
    /// module digest is unchanged — while a claim-free function (which needs
    /// no id) is still added. Mutation check: allocating inside the push loop
    /// (the pre-r11 shape) pushes the first row before refusing the second.
    #[test]
    fn try_add_function_refuses_a_claim_when_the_table_holds_u32_max() {
        let mut module = Module::new("decoded");
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(u32::MAX),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "decoded row",
        ));
        let before = module.stable_digest();
        let mut claiming = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        claiming.proofs = vec![ProofAnnotation::NoPanic, ProofAnnotation::NoOverflow];
        let refusal = module
            .try_add_function(claiming.clone())
            .expect_err("no obligation id is left for the synthesized rows");
        assert_eq!(refusal.exhausted, IdSpaceExhausted { space: "ProofId" });
        assert_eq!(*refusal.function, claiming);
        assert_eq!(module.stable_digest(), before, "nothing was pushed");
        assert!(module.functions.is_empty());
        assert_eq!(module.proof_obligations.len(), 1);

        // All or nothing at the boundary: one id left, two rows needed.
        module.proof_obligations[0].id = ProofId::new(u32::MAX - 1);
        let before = module.stable_digest();
        assert!(module.try_add_function(claiming.clone()).is_err());
        assert_eq!(
            module.stable_digest(),
            before,
            "the first row was not pushed alone"
        );

        // A claim-free function needs no id and is added.
        let plain = Function::new(FuncId::new(1), "g", FuncTyId::new(0), BlockId::new(0));
        module
            .try_add_function(plain)
            .expect("no synthesized row, no id needed");
        assert_eq!(module.functions.len(), 1);
    }

    /// One spelling of "the function's value ids": `max_value_id` and
    /// `fresh_value_ids` read the same walk, and the fresh cursor refuses
    /// (never wraps) when a definition holds `u32::MAX`.
    #[test]
    fn value_ids_are_the_one_walk_behind_max_and_fresh() {
        let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        assert_eq!(func.max_value_id(), 0);
        assert_eq!(func.fresh_value_ids().peek(), Some(ValueId::new(0)));
        assert_eq!(func.fresh_block_ids().peek(), Some(BlockId::new(0)));
        let mut block = Block::new(BlockId::new(4));
        block.params.push((ValueId::new(9), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::I32,
                operand: ValueId::new(9),
            })
            .with_result(ValueId::new(2)),
        );
        func.blocks.push(block);
        assert_eq!(
            func.value_ids().collect::<Vec<_>>(),
            vec![ValueId::new(9), ValueId::new(2)]
        );
        assert_eq!(func.max_value_id(), 9);
        assert_eq!(func.fresh_value_ids().peek(), Some(ValueId::new(10)));
        assert_eq!(func.fresh_block_ids().peek(), Some(BlockId::new(5)));
        func.blocks[0].params[0].0 = ValueId::new(u32::MAX);
        assert_eq!(func.max_value_id(), u32::MAX);
        assert!(func.fresh_value_ids().is_exhausted());
    }

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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(again)
            .expect("Module::try_add_function: test fixture");
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
        module
            .try_add_function(f0)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(f1)
            .expect("Module::try_add_function: test fixture");
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
        let ty = module
            .add_type(Ty::I64)
            .expect("Module::add_type: test fixture");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let cid = module
            .add_closure_type(ClosureTy::bare(ft))
            .expect("Module::add_closure_type: test fixture");
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
            origin: None,
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
            origin: None,
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::F64)
            .expect("Module::add_type: test fixture");
        module.globals.push(Global {
            name: "G".to_string(),
            ty: Ty::Bool,
            mutable: false,
            initializer: Some(Constant::Bool(true)),
            linkage: Linkage::External,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
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

        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
            origin: None,
        });

        module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");

        module.globals.push(Global {
            name: "COUNTER".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::External,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "add does not overflow".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
            spec: None,
        });

        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::Trusted("manual review".to_string()),

            assurance: None,
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

        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        msgpack_round_trip(&module);
    }

    fn vector_instruction_module(name: &str) -> Module {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);

        let mut module = Module::new(name);
        module
            .add_type(v4i32.clone())
            .expect("Module::add_type: test fixture");
        module
            .add_type(v4bool.clone())
            .expect("Module::add_type: test fixture");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, v4i32.clone(), v4i32.clone()],
                returns: vec![v4i32.clone(), v4bool.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
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
            BinOp::RotL,
            BinOp::RotR,
            BinOp::FCopySign,
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
        let ops = [
            UnOp::Neg,
            UnOp::FNeg,
            UnOp::Not,
            UnOp::CtPop,
            UnOp::CtLz,
            UnOp::CtTz,
            UnOp::BSwap,
            UnOp::BitReverse,
        ];
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
                weak: false,
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
            InstrNode::new(Inst::Assert {
                cond: v(0),
                kind: crate::inst::AssertKind::Unspecified,
                site: None,
            }),
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

            assurance: None,
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

    /// The combination the test above does NOT reach: `replay` absent with a
    /// non-empty `depends_on`. `ProofLineageNode` carried `skip_serializing_if`
    /// on BOTH, so in positional MessagePack — a bare array, which is what
    /// `rmp_serde::to_vec` writes and what the module graph is encoded with —
    /// skipping `replay` shifted `depends_on` down into slot 6, and the decoder
    /// read that `Vec<ProofLineageId>` as an `Option<ProofReplayIdentity>`:
    /// `invalid type: integer 0, expected a string`. A struct may carry at most
    /// ONE conditionally-skipped field and it must be the LAST; `replay` gained
    /// a successor and kept its skip.
    ///
    /// All four combinations are exercised, because only one of them was
    /// broken and a fix that traded it for another would look like progress.
    #[test]
    fn serde_proof_lineage_node_round_trips_with_and_without_a_replay_identity() {
        fn node(id: u32) -> ProofLineageNode {
            ProofLineageNode::new(
                ProofLineageId::new(id),
                ProofTransform::new(
                    ProofTransformStage::SolverAdapter,
                    "trust-ir-ay",
                    "TrustIr",
                    "0.1.0",
                ),
                ProofDigest::sha256([1; 32]),
                ProofDigest::sha256([2; 32]),
            )
        }

        for replay in [false, true] {
            for depends in [false, true] {
                let mut tail = node(1);
                if replay {
                    tail.replay = Some(ProofReplayIdentity::new(
                        "stage2-tcargo",
                        "cargo test -p trust-ir-ay",
                    ));
                }
                if depends {
                    tail.depends_on.push(ProofLineageId::new(0));
                }
                let manifest = ProofLineageManifest {
                    schema_version: ProofLineageManifest::SCHEMA_VERSION,
                    nodes: vec![node(0), tail],
                    roots: vec![ProofLineageId::new(0)],
                };
                // Positional MessagePack is the encoding the skip rule is
                // about; JSON is map-based and was never affected.
                let bytes = rmp_serde::to_vec(&manifest).expect("serialize positional");
                let back: ProofLineageManifest =
                    rmp_serde::from_slice(&bytes).unwrap_or_else(|e| {
                        panic!(
                            "replay={replay} depends_on={depends}: positional decode failed: {e}"
                        )
                    });
                assert_eq!(manifest, back, "replay={replay} depends_on={depends}");
                json_round_trip(&manifest);

                // Backward compatibility: `replay` is now always emitted, so
                // no NEW blob omits it — but blobs written before the flip do,
                // and `serde(default)` must still read them. Measured on the
                // real encodings rather than asserted.
                let mut value: serde_json::Value =
                    serde_json::from_str(&serde_json::to_string(&manifest).expect("to json"))
                        .expect("as value");
                for node in value["nodes"].as_array_mut().expect("nodes") {
                    node.as_object_mut().expect("node").remove("replay");
                }
                let legacy: ProofLineageManifest =
                    serde_json::from_value(value).expect("a pre-flip JSON node still decodes");
                for node in &legacy.nodes {
                    assert!(node.replay.is_none());
                }
            }
        }
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
        let ft_add = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let ft_main = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let ft_vararg = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: true,
            })
            .expect("Module::add_func_type: test fixture");

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
            origin: None,
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
            origin: None,
        });

        // Types
        module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Array(TyId::new(0), 10))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Struct(StructId::new(0)))
            .expect("Module::add_type: test fixture");

        // Globals
        module.globals.push(Global {
            name: "GLOBAL_FLAG".to_string(),
            ty: Ty::Bool,
            mutable: true,
            initializer: Some(Constant::Bool(false)),
            linkage: Linkage::External,
            tls: None,
            align: None,

            section: None,
            visibility: Default::default(),
            retained: false,
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

            section: None,
            visibility: Default::default(),
            retained: false,
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
        module
            .try_add_function(f_add)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(f_main)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(f_va)
            .expect("Module::try_add_function: test fixture");

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
            spec: None,
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
            spec: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![0x01, 0x02]),

            assurance: None,
        });

        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    // ---- Control flow with CondBr and Switch ----

    #[test]
    fn serde_module_with_control_flow() {
        let mut module = Module::new("control_flow");

        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn serde_module_with_switch() {
        let mut module = Module::new("switch_demo");

        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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

        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
            spec: None,
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

            section: None,
            visibility: Default::default(),
            retained: false,
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

            section: None,
            visibility: Default::default(),
            retained: false,
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

            section: None,
            visibility: Default::default(),
            retained: false,
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
            origin: None,
        };
        json_round_trip(&sd);
        msgpack_round_trip(&sd);
    }

    #[test]
    fn serde_func_ty_vararg() {
        let ft = FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![],
            abi: None,
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
            origin: None,
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
            origin: None,
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
            origin: None,
        });
        module
            .add_type(Ty::Enum(EnumId::new(0)))
            .expect("Module::add_type: test fixture");
        json_round_trip(&module);
        msgpack_round_trip(&module);
    }

    #[test]
    fn serde_dialect_op_round_trip() {
        use crate::dialect::{AttrValue, DialectInst};
        use crate::inst::Inst;
        use crate::node::InstrNode;

        let mut module = Module::new("serde_dialect");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
