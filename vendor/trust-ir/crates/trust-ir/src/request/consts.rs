// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Version for the native verification bundle schema.
pub const NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION: u32 = 6;

/// Maximum UTF-8 bytes in the public obligation identity bound to one native
/// proof obligation. This matches the public verifier envelope's obligation-id
/// ceiling while keeping the TrustIR handoff independently fail-closed.
pub const NATIVE_PUBLIC_OBLIGATION_ID_MAX_BYTES: usize = 1024;

/// Stable admission-contract version for Trust-produced native TrustMc proof-grade requests.
pub const TRUST_TRUST_MC_NATIVE_ADMISSION_CONTRACT_VERSION: &str =
    "trust-trust_mc-native-admission-contract-v1";

/// Stable schema tag for transport identity handoff records.
pub const NATIVE_TRANSPORT_IDENTITY_SCHEMA: &str = "trust_ir.native.transport_identity.v2";

/// Stable schema version for [`NativeTransportIdentity`].
pub const NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION: u32 = 2;

/// Stable schema tag for typed semantic bridge reports.
pub const NATIVE_SEMANTIC_BRIDGE_SCHEMA: &str = "trust_ir.native.semantic_bridge.v2";

/// Stable schema version for [`NativeSemanticBridge`].
pub const NATIVE_SEMANTIC_BRIDGE_SCHEMA_VERSION: u32 = 2;

/// Stable digest context for semantic bridge proof/evidence identity.
pub const NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA: &str =
    "trust_ir.native.semantic_bridge.proof_identity.v2";

/// Stable schema version for semantic bridge proof/evidence identity.
pub const NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION: u32 = 2;

/// Canonical Petri successor semantic-equivalence formula schema.
pub const PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA: &str =
    "ty.petri.native.successor.plan_cache_equivalence.v1";

/// Stable schema tag for Petri successor TrustMc CHC binding reports.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA: &str =
    "trust_ir.native.petri_successor.trust_mc_chc_binding.v1";

/// Stable schema version for [`PetriSuccessorTrustMcChcBindingReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri successor TrustMc CHC proof handoff reports.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA: &str =
    "trust_ir.native.petri_successor.trust_mc_chc_proof_handoff.v1";

/// Stable schema version for [`PetriSuccessorTrustMcChcProofHandoffReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri successor semantic bridge proof admission.
pub const PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA: &str =
    "trust_ir.native.petri_successor.semantic_bridge_proof_admission.v1";

/// Stable schema version for [`PetriSuccessorSemanticBridgeProofAdmissionReport`].
pub const PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri successor proof/evidence identity rows.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA: &str =
    "trust_ir.native.petri_successor.trust_mc_chc_proof_evidence_identity.v2";

/// Stable schema version for Petri successor proof/evidence identity rows.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION: u32 = 2;

/// Stable digest context for Petri successor proof/evidence identity rows.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT: &str =
    "trust_ir.native.petri_successor.trust_mc_chc_proof_evidence_identity.v2";

/// Stable schema tag for proof/evidence identity replay reports.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA: &str =
    "trust_ir.native.petri_successor.trust_mc_chc_proof_evidence_identity.replay_report.v1";

/// Stable schema version for proof/evidence identity replay reports.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA_VERSION: u32 =
    1;

/// Stable schema tag for Petri successor TrustMc CHC model-validation readiness reports.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA: &str =
    "trust_ir.native.petri_successor.trust_mc_chc_model_validation_readiness.v1";

/// Stable schema version for [`PetriSuccessorTrustMcChcModelValidationReadinessReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for the Petri successor TrustMc CHC downstream contract descriptor.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA: &str =
    "trust_ir.native.petri_successor.trust_mc_chc_contract.v1";

/// Stable schema version for [`PetriSuccessorTrustMcChcContractDescriptor`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for reusable native shared-primitive contract descriptors.
pub const NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA: &str =
    "trust_ir.native.shared_primitive_contract.v1";

/// Stable schema version for [`NativeSharedPrimitiveContractDescriptor`].
pub const NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for key/value shared-primitive contract manifest rows.
pub const NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA: &str =
    "trust_ir.native.shared_primitive_contract.manifest.v1";

/// Stable schema version for [`NativeSharedPrimitiveContractManifestRow`].
pub const NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA_VERSION: u32 = 1;

// ---------------------------------------------------------------------------
// Hardware vector / CHC x86 contract descriptors.
//
// Why these backend-flavored tables live in the IR contract crate (audit #104).
//
// The constants below name x86 instruction-selection facts — native
// instructions (`pmulld`, `paddd`, …), TrustCg LIR opcodes (`V4I32PackLanes`,
// …), and SSE/AVX feature guards (`x86.sse4.1+x86.sse4.2`). LIR opcodes and
// instruction selection are TrustCg's domain, and CLAUDE.md states this repo
// "does NOT contain a compiler, optimizer, or code generator." They are kept
// here deliberately, NOT by accident:
//
//   * They are a *producer-facing contract*, not a code generator. ay emits the
//     CHC batch-JIT sidecar rows by reading these descriptors from `trust-ir`
//     (the deterministic manifest digest/sha256 helpers in `evidence` pin the
//     replay/cache identity). A producer must not depend on TrustCg, so the
//     dependency arrow forbids relocating them *into* TrustCg — that would
//     invert producer → TrustCg into producer → TrustCg → trust-ir.
//   * The placement and ownership split are documented design decisions:
//     `docs/dialects.md` (the CHC x86 contract "is recorded in
//     crates/trust-ir/src/request/ as canonical descriptors") and
//     `designs/2026-05-04-x86-trust_ir-vector-contract-plan.md` (contract
//     boundaries). The descriptor doc-comments mark them "informational;
//     production proof/replay acceptance still belongs to the relevant solver
//     or hardware lane."
//
// Precise cross-repo boundary (what is NOT verifiable in this repo): the opcode
// strings ("V4I32PackLanes", …) and native-instruction strings ("pmulld", …)
// are NOT compile-checked against TrustCg's actual LIR enum or x86 encoder —
// the in-repo tests only assert the strings against themselves. Keeping these
// in lock-step with TrustCg's LIR is a TrustCg-coordinated step; either repo
// must version-bump the `HARDWARE_VECTOR_CONTRACT_SCHEMA` on a real change.
// Relocating them to versioned data fixtures under `trust-ir-conformance` (the
// only in-repo move the audit's verifier found viable) is deferred because it
// would lose compile-time `const` access for producers.
// ---------------------------------------------------------------------------

/// Stable schema tag for TrustIr-owned hardware vector contract descriptors.
pub const HARDWARE_VECTOR_CONTRACT_SCHEMA: &str = "trust_ir.hardware.vector_contract.v1";

/// Stable schema version for [`HardwareVectorContractDescriptor`].
pub const HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for hardware vector contract manifest rows.
pub const HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA: &str =
    "trust_ir.hardware.vector_contract.manifest.v1";

/// Stable schema version for hardware vector contract manifest rows.
pub const HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// TrustIr-owned source package for canonical CHC x86 vector contracts.
pub const CHC_X86_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE: &str = "trust-ir";

/// Stable set name for canonical CHC x86 vector contract descriptors.
pub const CHC_X86_HARDWARE_VECTOR_CONTRACT_SET_NAME: &str = "chc_x86";

/// Stable target family for canonical CHC x86 vector contract descriptors.
pub const CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY: &str = "chc_x86";

/// Stable hardware model named by canonical CHC x86 vector contract descriptors.
pub const CHC_X86_HARDWARE_VECTOR_CONTRACT_HARDWARE_MODEL: &str = "x86_lane_packed_integer_vectors";

/// Stable mask semantics for CHC x86 vector contract descriptors.
pub const CHC_X86_HARDWARE_VECTOR_CONTRACT_MASK_SEMANTICS: &str = "compare_produced_logical_bool_masks;mask_to_bits_compare_masks_only;integer_masks_via_compare_to_zero;arbitrary_bool_constants_require_explicit_trust_cg_support";

/// TrustIr-owned source package for canonical AVX-512 hardware vector contracts.
pub const AVX512_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE: &str = "trust-ir";

/// Stable set name for canonical AVX-512 hardware vector contract descriptors.
pub const AVX512_HARDWARE_VECTOR_CONTRACT_SET_NAME: &str = "avx512";

/// Stable target family for canonical AVX-512 hardware vector contract descriptors.
pub const AVX512_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY: &str = "avx512";

/// Stable hardware model named by canonical AVX-512 hardware vector contract descriptors.
pub const AVX512_HARDWARE_VECTOR_CONTRACT_HARDWARE_MODEL: &str = "x86_avx512_vector_extensions";

/// TrustIr-owned source package for canonical ANE hardware tensor contracts.
pub const ANE_HARDWARE_TENSOR_CONTRACT_SOURCE_PACKAGE: &str = "trust-ir";

/// Stable set name for canonical ANE hardware tensor contract descriptors.
pub const ANE_HARDWARE_TENSOR_CONTRACT_SET_NAME: &str = "ane";

/// Stable target family for canonical ANE hardware tensor contract descriptors.
pub const ANE_HARDWARE_TENSOR_CONTRACT_TARGET_FAMILY: &str = "ane";

/// Stable hardware model named by canonical ANE hardware tensor contract descriptors.
pub const ANE_HARDWARE_TENSOR_CONTRACT_HARDWARE_MODEL: &str = "apple_neural_engine_v1";

/// Consumer policy for operation rows that intentionally reject lowering.
pub const CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY: &str = "fail_closed_reject_lowering";

/// Stable operation names listed by the `<4 x i32>` CHC x86 contract descriptor.
pub const CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_OPERATIONS: &[&str] = &[
    "const.integer_mask.zero",
    "const.integer_mask.all_ones",
    "const.bool_mask",
    "pack_lanes",
    "icmp.ne",
    "binop.add",
    "binop.sub",
    "binop.mul",
    "select",
    "icmp.eq",
    "extract_element",
    "insert_element",
    "icmp.slt",
    "icmp.sle",
    "icmp.sgt",
    "icmp.sge",
    "binop.shl",
    "binop.lshr",
    "binop.ashr",
    "icmp.ult",
    "icmp.ule",
    "icmp.ugt",
    "icmp.uge",
];

/// Stable operation names listed by the `<2 x i64>` CHC x86 contract descriptor.
pub const CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_OPERATIONS: &[&str] = &[
    "const.integer_mask.zero",
    "const.integer_mask.all_ones",
    "const.bool_mask",
    "pack_lanes",
    "icmp.ne",
    "binop.add",
    "binop.sub",
    "select",
    "icmp.eq",
    "insert_element",
    "icmp.slt",
    "icmp.sle",
    "icmp.sgt",
    "icmp.sge",
    "extract_element",
    "icmp.ult",
    "icmp.ule",
    "icmp.ugt",
    "icmp.uge",
];

/// Stable operation names listed by the `<16 x i8>` CHC x86 narrow
/// compare-mask descriptor.
pub const CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_OPERATIONS: &[&str] = &[
    "icmp.eq",
    "icmp.ne",
    "icmp.slt",
    "icmp.sle",
    "icmp.sgt",
    "icmp.sge",
    "vector.mask_to_bits",
    "icmp.ult",
    "icmp.ule",
    "icmp.ugt",
    "icmp.uge",
];

/// Stable operation names listed by the `<8 x i16>` CHC x86 narrow
/// compare-mask descriptor.
pub const CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_OPERATIONS: &[&str] = &[
    "icmp.eq",
    "icmp.ne",
    "icmp.slt",
    "icmp.sle",
    "icmp.sgt",
    "icmp.sge",
    "vector.mask_to_bits",
    "icmp.ult",
    "icmp.ule",
    "icmp.ugt",
    "icmp.uge",
];

/// PMOVMSKB semantics for `<16 x bool>` compare masks produced by
/// `<16 x i8>` SSE2 comparisons.
pub const CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS: &str =
    "pmovmskb_i8_compare_mask_lane0_bit0_laneN_bitN_bits16_31_zero";

/// PMOVMSKB composition for `<16 x bool>` compare masks produced by
/// `<16 x i8>` SSE2 comparisons.
pub const CHC_X86_V16_I8_MASK_TO_BITS_COMPOSITION: &str =
    "pmovmskb(byte_compare_mask);lane0_to_bit0;laneN_to_bitN;bits_16_31_zero";

/// PMOVMSKB semantics for `<8 x bool>` compare masks produced by
/// `<8 x i16>` SSE2 comparisons.
pub const CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS: &str =
    "pmovmskb_i16_compare_mask_compact_word_byte_pairs_lane0_bit0_laneN_bitN_bits8_31_zero";

/// PMOVMSKB composition for `<8 x bool>` compare masks produced by
/// `<8 x i16>` SSE2 comparisons.
pub const CHC_X86_V8_I16_MASK_TO_BITS_COMPOSITION: &str = "compare_mask_words_are_0x0000_or_0xffff;pmovmskb(word_compare_mask);compact_duplicate_byte_bits_2n_or_2n_plus_1_to_bit_n;bits_8_31_zero";

/// Guard attached to the `<4 x i32>` lane-wise multiply contract.
pub const CHC_X86_V4_I32_MUL_FEATURE_GUARD: &str = "x86.sse4.1";

/// Stable native instruction named by the guarded `<4 x i32>` multiply lane.
pub const CHC_X86_V4_I32_MUL_NATIVE_INSTRUCTION: &str = "pmulld";

/// Source semantics for the guarded `<4 x i32>` multiply contract row.
pub const CHC_X86_V4_I32_MUL_SEMANTICS: &str = "lane_wise_i32_wrapping_low_32_bits";

/// Generic TrustIr x86-64 vector baseline for portable packed lane construction.
pub const CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD: &str = "x86.sse2";

/// Current TrustIr x86-64 vector profile used by default/current pipelines.
pub const CHC_X86_TRUST_CG_CURRENT_VECTOR_FEATURE_GUARD: &str = "x86.sse4.1+x86.sse4.2";

/// Host-JIT TrustIr x86-64 vector profile source.
pub const CHC_X86_TRUST_CG_HOST_JIT_VECTOR_FEATURE_GUARD: &str =
    "runtime_detected_optional_x86.sse4.1+x86.sse4.2";

/// TrustIr x86-64 LIR opcode used for `<4 x i32>` scalar lane packing.
pub const CHC_X86_V4_I32_LANE_PACK_LIR_OPCODE: &str = "V4I32PackLanes";

/// TrustIr x86-64 native instruction coverage for `<4 x i32>` lane packing.
pub const CHC_X86_V4_I32_LANE_PACK_NATIVE_INSTRUCTIONS: &str =
    "movd_to_xmm;punpckldq;punpcklqdq;pshufd_same_lane_broadcast";

/// TrustIr x86-64 lane-pack semantics for `<4 x i32>`.
pub const CHC_X86_V4_I32_LANE_PACK_SEMANTICS: &str =
    "scalar_i32_lanes_to_v128_lanes_0_3;single_use_pack_extract_forwards_scalar_lane";

/// TrustIr x86-64 LIR opcode used for `<2 x i64>` scalar lane packing.
pub const CHC_X86_V2_I64_LANE_PACK_LIR_OPCODE: &str = "V2I64PackLanes";

/// TrustIr x86-64 native instruction coverage for `<2 x i64>` lane packing.
pub const CHC_X86_V2_I64_LANE_PACK_NATIVE_INSTRUCTIONS: &str =
    "movq_to_xmm;punpcklqdq;pshufd_same_lane_broadcast";

/// TrustIr x86-64 lane-pack semantics for `<2 x i64>`.
pub const CHC_X86_V2_I64_LANE_PACK_SEMANTICS: &str =
    "scalar_i64_lanes_to_v128_lanes_0_1;single_use_pack_extract_forwards_scalar_lane";

/// Stable TrustIr x86-64 LIR opcode used for `<4 x i32>` constant-lane insertion.
pub const CHC_X86_V4_I32_INSERT_ELEMENT_LIR_OPCODE: &str = "V4I32InsertLane";

/// TrustIr x86-64 native instruction coverage for `<4 x i32>` insert-element.
pub const CHC_X86_V4_I32_INSERT_ELEMENT_NATIVE_INSTRUCTIONS: &str =
    "movd_to_xmm;movd_from_xmm;pshufd;punpckldq;punpcklqdq;pxor_zero_base";

/// TrustIr x86-64 insert-element semantics for `<4 x i32>`.
pub const CHC_X86_V4_I32_INSERT_ELEMENT_SEMANTICS: &str =
    "constant_lane_sse2_rebuild_without_pinsrd_or_stack";

/// Stable TrustIr x86-64 LIR opcode used for `<2 x i64>` constant-lane insertion.
pub const CHC_X86_V2_I64_INSERT_ELEMENT_LIR_OPCODE: &str = "V2I64InsertLane";

/// TrustIr x86-64 native instruction coverage for `<2 x i64>` insert-element.
pub const CHC_X86_V2_I64_INSERT_ELEMENT_NATIVE_INSTRUCTIONS: &str =
    "movq_to_xmm;pshufd;punpcklqdq;pxor_zero_base";

/// TrustIr x86-64 insert-element semantics for `<2 x i64>`.
pub const CHC_X86_V2_I64_INSERT_ELEMENT_SEMANTICS: &str =
    "constant_lane_sse2_rebuild_without_pinsrq_or_stack";

/// TrustIr x86-64 native instruction coverage for scalarized `<4 x i32>` shifts.
pub const CHC_X86_V4_I32_SHIFT_NATIVE_INSTRUCTIONS: &str =
    "movd_from_xmm;pshufd;mov_to_ecx;shl_rr_or_shr_rr_or_sar_rr;movd_to_xmm;punpckldq;punpcklqdq";

/// TrustIr x86-64 proof condition shared by scalarized `<4 x i32>` shifts.
pub const CHC_X86_V4_I32_SHIFT_PROOF_CONDITION: &str =
    "lane_count_4;each_rhs_lane_in_0_31;x86_shift_count_masking_not_source_semantics";

/// TrustIr x86-64 scalarized shift/reassembly semantics for `<4 x i32>`.
pub const CHC_X86_V4_I32_SHIFT_REASSEMBLY_SEMANTICS: &str =
    "lane_wise_i32_shift_with_scalar_gpr_counts_reassembled_by_sse2_dword_qword_unpacks";

/// Stable TrustIr x86-64 LIR opcode used for `<2 x i64>` constant-lane extraction.
pub const CHC_X86_V2_I64_EXTRACT_ELEMENT_LIR_OPCODE: &str = "V2I64ExtractLane";

/// TrustIr x86-64 native instruction coverage for `<2 x i64>` extract-element.
pub const CHC_X86_V2_I64_EXTRACT_ELEMENT_NATIVE_INSTRUCTIONS: &str = "pshufd;movq_from_xmm";

/// TrustIr x86-64 extract-element semantics for `<2 x i64>`.
pub const CHC_X86_V2_I64_EXTRACT_ELEMENT_SEMANTICS: &str =
    "constant_lane_sse2_extract_without_pextrq_or_stack";

/// Stable TrustIr x86-64 LIR opcode used for `<2 x i64>` packed comparisons.
pub const CHC_X86_V2_I64_ICMP_LIR_OPCODE: &str = "V2I64Icmp";

/// Feature guard for `<2 x i64>` equality/inequality comparisons.
pub const CHC_X86_V2_I64_ICMP_EQ_NE_FEATURE_GUARD: &str = "x86.sse4.1";

/// Feature guard for `<2 x i64>` signed ordering comparisons.
pub const CHC_X86_V2_I64_ICMP_SIGNED_ORDER_FEATURE_GUARD: &str = "x86.sse4.2";

/// Stable TrustIr x86-64 LIR opcode used for `<4 x i32>` all-zero vectors.
pub const CHC_X86_V4_I32_ZERO_LIR_OPCODE: &str = "V4I32Zero";

/// Stable TrustIr x86-64 LIR opcode used for `<2 x i64>` all-zero vectors.
pub const CHC_X86_V2_I64_ZERO_LIR_OPCODE: &str = "V2I64Zero";

/// Stable TrustIr x86-64 LIR opcode used for `<4 x i32>` constant-lane extraction.
pub const CHC_X86_V4_I32_EXTRACT_ELEMENT_LIR_OPCODE: &str = "V4I32ExtractLane";

/// TrustIr x86-64 native instruction coverage for `<4 x i32>` extract-element.
pub const CHC_X86_V4_I32_EXTRACT_ELEMENT_NATIVE_INSTRUCTIONS: &str = "movd_from_xmm;pshufd";

/// TrustIr x86-64 extract-element semantics for `<4 x i32>`.
pub const CHC_X86_V4_I32_EXTRACT_ELEMENT_SEMANTICS: &str =
    "constant_lane_sse2_extract_without_pextrd_or_stack";

/// Stable TrustIr x86-64 LIR opcode used for generic `<4 x i32>` comparisons.
pub const CHC_X86_V4_I32_ICMP_LIR_OPCODE: &str = "Icmp";

/// Stable TrustIr x86-64 LIR opcode used for vector-mask selects.
pub const CHC_X86_VECTOR_SELECT_LIR_OPCODE: &str = "Select";

/// Stable status codes for hardware vector descriptors and operation rows.
pub const HARDWARE_VECTOR_CONTRACT_STATUS_CODES: &[&str] =
    &["available", "deferred", "unavailable"];

/// Stable reason codes for hardware vector descriptors and operation rows.
pub const HARDWARE_VECTOR_CONTRACT_REASON_CODES: &[&str] = &[
    "canonical_contract",
    "unsigned_vector_compare_proof_blocked",
    "unsigned_vector_compare_unavailable",
];

/// Stable schema tag for the TY shared-primitive producer manifest.
pub const TY_SHARED_PRIMITIVE_MANIFEST_SCHEMA: &str = "trust_ir.ty.shared_primitive_manifest.v1";

/// Stable schema version for [`TySharedPrimitiveManifest`].
pub const TY_SHARED_PRIMITIVE_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Source package that owns the TY shared-primitive producer manifest.
pub const TY_SHARED_PRIMITIVE_MANIFEST_SOURCE_PACKAGE: &str = "trust-ir";

/// Source package version compiled into the TY shared-primitive manifest.
pub const TY_SHARED_PRIMITIVE_MANIFEST_SOURCE_PACKAGE_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Stable component names emitted by [`TySharedPrimitiveManifest`].
pub const TY_SHARED_PRIMITIVE_MANIFEST_COMPONENT_NAMES: &[&str] = &[
    "native_semantic_bridge_proof_identity",
    "petri_successor_trust_mc_chc_proof_evidence_identity",
    "chc_x86_hardware_vector_contracts",
];

/// Stable status codes for [`TySharedPrimitiveManifest`].
pub const TY_SHARED_PRIMITIVE_MANIFEST_STATUS_CODES: &[&str] = &["available"];

/// Stable reason codes for [`TySharedPrimitiveManifest`].
pub const TY_SHARED_PRIMITIVE_MANIFEST_REASON_CODES: &[&str] = &["producer_owned_rows_available"];

/// Stable schema tag for native evidence artifact byte attachments.
pub const NATIVE_EVIDENCE_ARTIFACT_ATTACHMENT_SCHEMA: &str =
    "trust_ir.native.evidence.artifact_attachment.v1";

/// Stable schema version for [`NativeEvidenceArtifactAttachment`].
pub const NATIVE_EVIDENCE_ARTIFACT_ATTACHMENT_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for native evidence artifact byte resolution reports.
pub const NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA: &str =
    "trust_ir.native.evidence.artifact_resolution.v1";

/// Stable schema version for [`NativeEvidenceArtifactResolutionReport`].
pub const NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for artifact authority evidence rows.
pub const NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA: &str =
    "trust_ir.native.evidence.artifact_authority_row.v1";

/// Stable schema version for [`NativeEvidenceArtifactAuthorityRow`].
pub const NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION: u32 = 1;

/// Ordered row keys emitted by [`NativeEvidenceArtifactResolutionReport`].
pub const NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_REPORT_ROW_KEYS: &[&str] = &[
    "artifact_authority.schema",
    "artifact_authority.schema_version",
    "artifact_resolution.schema",
    "artifact_resolution.schema_version",
    "request.id",
    "owner_suite",
    "artifact.kind",
    "artifact.name",
    "digest.algorithm",
    "digest",
    "byte.source_identity",
    "byte.len",
    "actual_digest",
    "authority",
    "status",
    "reason",
    "report.is_resolved",
    "report.is_authoritative",
    "report.fail_closed",
];

/// Ordered row keys emitted by [`NativeEvidenceArtifactResolution`].
pub const NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_RESOLUTION_ROW_KEYS: &[&str] = &[
    "artifact_authority.schema",
    "artifact_authority.schema_version",
    "artifact_resolution.schema",
    "artifact_resolution.schema_version",
    "request.id",
    "owner_suite",
    "artifact.kind",
    "artifact.name",
    "digest.algorithm",
    "digest",
    "byte.source_identity",
    "byte.len",
    "actual_digest",
    "authority",
    "status",
    "reason",
    "report.is_resolved",
    "report.is_authoritative",
    "report.fail_closed",
    "resolution.bytes_present",
    "resolution.is_resolved",
    "resolution.is_authoritative",
    "resolution.fail_closed",
    "resolution.authoritative_bytes_available",
];

/// TrustIr-owned fields that define the Petri successor TrustMc CHC report surface.
///
/// **Intentional contract manifest — not test scaffolding.** Embedded into the
/// Petri shared-primitive contract descriptor (`provided_fields`) consumed by
/// downstream backends; the owned half of an owned/external split. Drift is
/// guarded by `manifest_field_sets_have_no_drift` (no duplicates, well-formed
/// entries, all module-owned — no `trust_cg.` entries).
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_PROVIDED_FIELDS: &[&str] = &[
    "NativeVerificationBundle::petri_successor_trust_mc_chc_binding_report()",
    "PetriSuccessorTrustMcChcBindingReport::function",
    "PetriSuccessorTrustMcChcBindingReport::semantic_bridge_report",
    "PetriSuccessorTrustMcChcBindingReport::request",
    "PetriSuccessorTrustMcChcBindingReport::request_digest",
    "PetriSuccessorTrustMcChcBindingReport::evidence_digest",
    "PetriSuccessorTrustMcChcBindingReport::expected_evidence_digest",
    "PetriSuccessorTrustMcChcBindingReport::horn_clause_artifact",
    "PetriSuccessorTrustMcChcBindingReport::status",
    "PetriSuccessorTrustMcChcBindingReport::reason",
    "PetriSuccessorTrustMcChcBindingReport::is_bound()",
    "PetriSuccessorTrustMcChcBindingReport::status_code()",
    "PetriSuccessorTrustMcChcBindingReport::reason_code()",
    "PetriSuccessorTrustMcChcBindingReport::fail_closed()",
    "NativeVerificationBundle::petri_successor_trust_mc_chc_proof_handoff_report()",
    "PetriSuccessorTrustMcChcProofHandoffReport::function",
    "PetriSuccessorTrustMcChcProofHandoffReport::binding_report",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_identity_digest",
    "PetriSuccessorTrustMcChcProofHandoffReport::replay",
    "PetriSuccessorTrustMcChcProofHandoffReport::replay_transcript_digest",
    "PetriSuccessorTrustMcChcProofHandoffReport::replay_transcript_artifact",
    "PetriSuccessorTrustMcChcProofHandoffReport::model_artifact",
    "PetriSuccessorTrustMcChcProofHandoffReport::solver_identities",
    "PetriSuccessorTrustMcChcProofHandoffReport::status",
    "PetriSuccessorTrustMcChcProofHandoffReport::reason",
    "PetriSuccessorTrustMcChcProofHandoffReport::is_ready()",
    "PetriSuccessorTrustMcChcProofHandoffReport::status_code()",
    "PetriSuccessorTrustMcChcProofHandoffReport::reason_code()",
    "PetriSuccessorTrustMcChcProofHandoffReport::fail_closed()",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA_VERSION",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_digest()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_rows()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_key_value_lines()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_key_value_text()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_replay_report()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_replay_report_for_key_value_lines()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_replay_report_for_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::is_replayable()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::diagnostic_count()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_rows()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_key_value_lines()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_rows()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_key_value_lines()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_json_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_round_trip_report()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_lines()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::code()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::code()",
    "NativeVerificationBundle::petri_successor_trust_mc_chc_model_validation_readiness_report()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::function",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::proof_handoff_report",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::model_artifact",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::model_artifact_digest",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::solver_identities",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::model_validated",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::status",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::reason",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::status_code()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::reason_code()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::is_ready_for_solver_validation()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::fail_closed()",
    "NativeVerificationBundle::petri_successor_semantic_bridge_proof_admission_report()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::function",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::proof_handoff_report",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::required_artifact_kinds",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::artifact_resolutions",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::blocked_artifact_kind",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::blocked_artifact_reason",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::status",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::reason",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::status_code()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::reason_code()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::blocked_artifact_reason_code()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::artifact_resolution_for_kind()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::authoritative_bytes_for_kind()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::authoritative_byte_count()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::key_value_rows()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::key_value_lines()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::key_value_text()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::is_admitted()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::fail_closed()",
];

/// Stable status codes for [`PetriSuccessorTrustMcChcBindingReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_STATUS_CODES: &[&str] = &["bound", "blocked"];

/// Stable reason codes for [`PetriSuccessorTrustMcChcBindingReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_REASON_CODES: &[&str] = &[
    "bound",
    "bundle_invalid",
    "semantic_bridge_blocked",
    "missing_bridge_proof_obligation",
    "missing_trust_mc_chc_request",
    "missing_trust_mc_chc_evidence",
    "evidence_binding_mismatch",
    "missing_horn_clause_artifact",
];

/// Stable status codes for [`PetriSuccessorTrustMcChcProofHandoffReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_STATUS_CODES: &[&str] = &["ready", "blocked"];

/// Stable reason codes for [`PetriSuccessorTrustMcChcProofHandoffReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_REASON_CODES: &[&str] = &[
    "ready",
    "binding_blocked",
    "missing_trust_mc_chc_evidence",
    "missing_replay_transcript_digest",
    "missing_replay_transcript_artifact",
    "replay_transcript_digest_mismatch",
];

/// Stable status codes for [`PetriSuccessorTrustMcChcModelValidationReadinessReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_STATUS_CODES: &[&str] =
    &["ready_for_solver_validation", "blocked"];

/// Stable reason codes for [`PetriSuccessorTrustMcChcModelValidationReadinessReport`].
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_REASON_CODES: &[&str] = &[
    "solver_validation_required",
    "proof_handoff_blocked",
    "missing_model_artifact",
];

/// Stable status codes for [`PetriSuccessorSemanticBridgeProofAdmissionReport`].
pub const PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_STATUS_CODES: &[&str] =
    &["admitted", "blocked"];

/// Stable reason codes for [`PetriSuccessorSemanticBridgeProofAdmissionReport`].
pub const PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_REASON_CODES: &[&str] = &[
    "admitted",
    "proof_handoff_blocked",
    "artifact_resolution_blocked",
];

/// Verifier suite used by the Petri successor TrustMc CHC contract.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFIER_SUITE: NativeVerifierSuite =
    NativeVerifierSuite::TrustMc;

/// Verification mode used by the Petri successor TrustMc CHC contract.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFICATION_MODE: TrustMcVerificationMode =
    TrustMcVerificationMode::Chc;

/// Artifact kinds required before a Petri successor TrustMc CHC binding can be bound.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_REQUIRED_ARTIFACT_KINDS:
    &[NativeEvidenceArtifactKind] = &[NativeEvidenceArtifactKind::TrustMcHornClauses];

/// Artifact kinds required before a Petri successor TrustMc CHC proof handoff can be ready.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_REQUIRED_ARTIFACT_KINDS:
    &[NativeEvidenceArtifactKind] = &[NativeEvidenceArtifactKind::ReplayTranscript];

/// Artifact kinds surfaced by proof handoff when present, without authorizing acceptance.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_OPTIONAL_ARTIFACT_KINDS:
    &[NativeEvidenceArtifactKind] = &[NativeEvidenceArtifactKind::TrustMcModel];

/// Artifact kinds required before model evidence is ready for solver-owned validation.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRED_ARTIFACT_KINDS:
    &[NativeEvidenceArtifactKind] = &[NativeEvidenceArtifactKind::TrustMcModel];

/// Artifact kinds required before production acceptance can be considered.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS:
    &[NativeEvidenceArtifactKind] = &[
    NativeEvidenceArtifactKind::TrustMcHornClauses,
    NativeEvidenceArtifactKind::ReplayTranscript,
    NativeEvidenceArtifactKind::TrustMcModel,
];

/// Artifact kinds optional at the production acceptance boundary.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OPTIONAL_ARTIFACT_KINDS:
    &[NativeEvidenceArtifactKind] = &[];

/// Solver-owned artifact-byte requirements for Petri/TrustMc production acceptance.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_REQUIREMENTS:
    &[NativeSharedPrimitiveArtifactRequirement] = &[
    NativeSharedPrimitiveArtifactRequirement {
        role: NativeSharedPrimitiveArtifactRole::SolverInput,
        kind: NativeEvidenceArtifactKind::TrustMcHornClauses,
        digest_algorithm: ProofDigestAlgorithm::Sha256,
        owner_suite: NativeVerifierSuite::AY,
        requires_emitted_solver_artifact: true,
    },
    NativeSharedPrimitiveArtifactRequirement {
        role: NativeSharedPrimitiveArtifactRole::ReplayTranscript,
        kind: NativeEvidenceArtifactKind::ReplayTranscript,
        digest_algorithm: ProofDigestAlgorithm::Sha256,
        owner_suite: NativeVerifierSuite::AY,
        requires_emitted_solver_artifact: true,
    },
    NativeSharedPrimitiveArtifactRequirement {
        role: NativeSharedPrimitiveArtifactRole::SolverWitness,
        kind: NativeEvidenceArtifactKind::TrustMcModel,
        digest_algorithm: ProofDigestAlgorithm::Sha256,
        owner_suite: NativeVerifierSuite::AY,
        requires_emitted_solver_artifact: true,
    },
];

/// Production acceptance requires byte-addressable artifacts emitted by the solver lane.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_REQUIRES_EMITTED_SOLVER_ARTIFACTS: bool = true;

/// Model readiness remains fail-closed until a solver-owned validation result is attached.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRES_SOLVER_ACCEPTANCE: bool = true;

/// Downstream API that builds the AY-owned model-acceptance report.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME: &str =
    "ay::chc::trust_mc_petri_successor_chc_model_acceptance_report";

/// Downstream API that owns production acceptance for ready Petri/TrustMc handoffs.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME: &str =
    "ay::chc::TrustMcPetriSuccessorChcModelAcceptanceReport::accept_for_consumer";

/// Verifier suite that owns production acceptance for ready Petri/TrustMc handoffs.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OWNER_SUITE: NativeVerifierSuite =
    NativeVerifierSuite::AY;

/// AY-owned solver capability descriptor schema required by Petri/TrustMc production.
///
/// TrustIr publishes this identity so downstream consumers can find the AY-owned
/// capability report. AY remains the owner of the schema contents and statuses.
pub const AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA: &str = "ay.solver-capability-descriptor.v1";

/// AY-owned solver capability descriptor schema version.
pub const AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION: u32 = 1;

/// AY-owned model-blocking clause schema required by Petri/TrustMc production.
pub const AY_MODEL_BLOCKING_CLAUSE_SCHEMA: &str = "ay.model-blocking-clause.v1";

/// AY-owned model-blocking clause schema version.
pub const AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION: u32 = 1;

/// AY-owned compact model-blocking clause evidence schema.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA: &str = "ay.model-blocking-clause-evidence.v1";

/// AY-owned compact model-blocking clause evidence schema version.
pub const AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION: u32 = 1;

/// AY-owned solve-decision model-consumer schema.
pub const AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA: &str =
    "ay.solve-decision-profile-model-consumer.v1";

/// AY-owned solve-decision model-consumer schema version.
pub const AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for Petri native bundle and solver-evidence handoff descriptors.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA: &str =
    "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.v2";

/// Stable schema version for [`PetriNativeVerificationBundleHandoffDescriptor`].
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA_VERSION: u32 = 2;

/// Source package that owns the Petri native bundle handoff descriptor.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE: &str = "trust-ir";

/// Source package version compiled into the Petri native bundle handoff descriptor.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION: &str =
    env!("CARGO_PKG_VERSION");

/// Downstream responsibilities for consuming Petri native bundle handoff rows.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DOWNSTREAM_CONSUMER_RESPONSIBILITIES: &[&str] =
    &[
        "validate_native_verification_bundle_before_admission",
        "derive_transport_identity_with_NativeVerificationBundle::transport_identity()",
        "resolve_artifact_bytes_with_NativeVerificationBundle::resolve_evidence_artifact_attachment()",
        "resolve_required_artifact_bytes_with_NativeVerificationBundle::resolve_evidence_artifact_attachments_for_kinds()",
        "require_authoritative_NativeEvidenceArtifactResolution_before_using_bytes",
        "use_shared_primitive_solver_evidence_descriptor_for_AY_identities",
        "call_AY_acceptance_API_before_production_selection",
        "do_not_reconstruct_AY_solver_logic_downstream",
        "preserve_fail_closed_status_when_required_rows_are_missing",
    ];

/// Stable schema tag for Petri native handoff manifest identity evidence.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA: &str =
    "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.manifest_identity.v2";

/// Stable schema version for [`PetriNativeVerificationBundleHandoffManifestIdentity`].
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION: u32 = 2;

/// Stable TrustIr digest context for Petri native handoff manifest identity text.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT: &str =
    "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.manifest_identity.v2";

/// Stable schema tag for Petri handoff diagnostic fixture manifests.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA: &str =
    "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.diagnostic_fixture_manifest.v2";

/// Stable schema version for [`PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest`].
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION: u32 =
    2;

/// Stable diagnostic fixture name for the healthy default Petri handoff row set.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME: &str =
    "default_descriptor_healthy";

/// Stable diagnostic fixture name for an intentionally incomplete Petri handoff row set.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME: &str =
    "missing_bundle_identity_schema_and_solver_capability_schema";

/// Required row keys omitted by the incomplete Petri handoff diagnostic fixture.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_MISSING_ROW_KEYS:
    &[&str] = &[
    "bundle_identity.schema",
    "solver_evidence.capability_descriptor.schema",
];

/// Stable schema tag for the aggregate Petri handoff replay contract import surface.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA: &str =
    "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.replay_contract_surface.v2";

/// Stable schema version for [`PetriNativeVerificationBundleHandoffReplayContractSurface`].
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA_VERSION: u32 = 2;

/// Stable schema tag for Petri replay contract surface round-trip report rows.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA: &str = "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.replay_contract_surface.round_trip_report.v2";

/// Stable schema version for [`PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport`].
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA_VERSION:
    u32 = 2;

/// Stable TrustIr digest context for Petri replay contract surface round-trip reports.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT:
    &str =
    "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.replay_contract_surface.round_trip_report.v2";

/// Stable schema tag for binding Petri replay-report JSON to the handoff identity.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA:
    &str = "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.replay_contract_surface.json_manifest_binding.v2";

/// Stable schema version for [`PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport`].
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA_VERSION:
    u32 = 2;

/// Stable TrustIr digest context for compact replay-report JSON text.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT:
    &str = "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.replay_contract_surface.json_manifest_binding.v2";

/// Stable fixture name for a healthy Petri replay JSON manifest binding.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME:
    &str = "default_replay_json_manifest_binding_healthy";

/// Stable fixture name for a stale Petri replay JSON manifest binding.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME:
    &str = "stale_replay_json_manifest_binding_manifest_identity_digest";

/// Public helper names that downstream replay consumers can import as a bundle.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_HELPER_NAMES: &[&str] = &[
    "petri_native_verification_bundle_handoff_descriptor()",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_key_value_lines()",
    "PetriNativeVerificationBundleHandoffDescriptor::normalized_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::normalized_key_value_lines()",
    "PetriNativeVerificationBundleHandoffDescriptor::required_normalized_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::validate_normalized_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_identity()",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_identity_for_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::canonical_manifest_text()",
    "PetriNativeVerificationBundleHandoffDescriptor::canonical_manifest_text_for_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::contract_health_report()",
    "PetriNativeVerificationBundleHandoffDescriptor::contract_health_report_for_rows()",
    "petri_native_verification_bundle_handoff_contract_health_report()",
    "petri_native_verification_bundle_handoff_healthy_diagnostic_fixture()",
    "petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture()",
    "petri_native_verification_bundle_handoff_diagnostic_fixture_manifest()",
    "petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_healthy_fixture()",
    "petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_stale_fixture()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::compact_manifest_json_text()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::compact_manifest_handoff_identity_report()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::key_value_rows()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::key_value_rows()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::key_value_lines()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::key_value_text()",
];

/// Public schema constants covered by the aggregate Petri handoff replay surface.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_NAMES: &[&str] = &[
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA",
];

/// Public schema values covered by the aggregate Petri handoff replay surface.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_VALUES: &[&str] = &[
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA,
];

/// Public fixture names covered by the aggregate Petri handoff replay surface.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_FIXTURE_NAMES: &[&str] = &[
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME,
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME,
];

/// Public validator names that downstream replay consumers can call without reconstructing rows.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_VALIDATOR_NAMES: &[&str] = &[
    "PetriNativeVerificationBundleHandoffDescriptor::validate_normalized_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::contract_health_report_for_rows()",
    "PetriNativeVerificationBundleHandoffManifestIdentity::round_trip_report()",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::round_trip_report()",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::round_trip_report()",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::round_trip_report_for_key_value_lines()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::key_value_round_trip_report()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::key_value_line_round_trip_report()",
];

/// Stable schema tag for downstream native-bundle identity contracts.
pub const NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA: &str =
    "trust_ir.native.bundle_identity_contract.v1";

/// Stable schema version for [`NativeBundleIdentityContractDescriptor`].
pub const NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA_VERSION: u32 = 1;

/// TrustIr-owned fields that define the native-bundle identity surface.
///
/// **Intentional contract manifest — not test scaffolding.** This list is
/// embedded verbatim into [`NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR`]
/// (`provided_fields`) and the Petri handoff descriptor's
/// `expected_bundle_identity_fields`, which ty/ay/TrustCg consume to learn the
/// identity surface this crate guarantees. It is the *owned* half of the
/// owned/external split; the externally-owned half is
/// [`NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS`]. Drift is guarded by
/// `manifest_field_sets_have_no_drift` in the request test module (no
/// duplicates, well-formed entries, and the owned/external namespace split).
pub static NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS: &[&str] = &[
    "NativeVerificationBundle::SCHEMA_VERSION",
    "NativeVerificationBundle::schema_version",
    "NativeVerificationBundle::source_digest()",
    "NativeVerificationBundle::trust_ir_module_digest",
    "NativeVerificationBundle::stable_digest()",
    "NativeVerificationBundle::transport_identity()",
    "NativeVerificationBundle::native_semantic_bridge_report()",
    "NativeTransportIdentity::schema",
    "NativeTransportIdentity::schema_version",
    "NativeTransportIdentity::bundle_schema_version",
    "NativeTransportIdentity::source_digest",
    "NativeTransportIdentity::trust_ir_module_digest",
    "NativeTransportIdentity::compiler_facts_digest",
    "NativeTransportIdentity::lineage_digest",
    "NativeTransportIdentity::bundle_digest",
    "NativeTransportIdentity::target_abi",
    "NativeTransportIdentity::request_digests",
    "NativeTransportIdentity::evidence_digests",
    "NativeTransportIdentity::stable_digest()",
    "NativeTransportIdentity::identity_rows()",
    "NativeTransportIdentity::identity_key_value_lines()",
    "NativeTransportIdentity::identity_key_value_text()",
    "NativeTransportIdentity::identity_replay_report()",
    "NativeTransportIdentity::identity_replay_report_for_key_value_lines()",
    "NativeTransportIdentity::identity_replay_report_for_key_value_text()",
    "NativeTransportIdentityReplayReport::is_replayable()",
    "NativeTransportIdentityReplayReport::diagnostic_count()",
    "NativeTransportIdentityReplayReport::compact_health_summary_rows()",
    "NativeTransportIdentityReplayReport::compact_health_summary_key_value_lines()",
    "NativeTransportIdentityReplayReport::compact_health_summary_key_value_text()",
    "NativeTransportIdentityReplayReport::compact_health_summary_json_text()",
    "NativeTransportIdentityReplayReport::compact_health_summary_round_trip_report()",
    "NativeTransportIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_lines()",
    "NativeTransportIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_text()",
    "NativeTransportIdentityReplayStatus::code()",
    "NativeTransportIdentityReplayHealthSummaryRoundTripStatus::code()",
    "NativeTargetAbiIdentity::triple",
    "NativeTargetAbiIdentity::pointer_size",
    "NativeTargetAbiIdentity::endianness",
    "NativeTargetAbiIdentity::digest",
    "NativeEvidenceBundle::from_request()",
    "NativeVerificationBundle::evidence_bundle_for_request()",
    "NativeVerificationBundle::resolve_evidence_artifact_attachment()",
    "NativeVerificationBundle::resolve_evidence_artifact_attachment_for_kind()",
    "NativeVerificationBundle::resolve_evidence_artifact_attachments_for_kinds()",
    "Module::functions[].id",
    "Module::functions[].name",
    "Module::functions[].ty",
    "Module::functions[].calling_conv",
    "Module::functions[].linkage",
    "Module::func_types[].params",
    "Module::func_types[].returns",
    "Module::func_types[].is_vararg",
    "NativeCompilerFacts::stable_digest()",
    "NativeCompilerFacts::monomorphizations[].source_item",
    "NativeCompilerFacts::monomorphizations[].symbol",
    "NativeCompilerFacts::monomorphizations[].generic_args",
    "NativeCompilerFacts::monomorphizations[].function",
    "NativeCompilerFacts::monomorphizations[].stable_digest",
    "NativeCompilerFacts::trait_object_metadata[].ty",
    "NativeCompilerFacts::trait_object_metadata[].source_ty",
    "NativeCompilerFacts::trait_object_metadata[].trait_id",
    "NativeCompilerFacts::trait_object_metadata[].source_trait_id",
    "NativeCompilerFacts::trait_object_metadata[].upcast_path",
    "NativeCompilerFacts::trait_object_metadata[].vtable_symbol",
    "NativeCompilerFacts::trait_object_metadata[].stable_digest",
    "NativeCompilerFacts::trait_object_metadata[].function",
    "NativeCompilerFacts::trait_object_metadata[].obligations",
    "NativeCompilerFacts::pointer_offsets[].base_ty",
    "NativeCompilerFacts::pointer_offsets[].pointee_ty",
    "NativeCompilerFacts::pointer_offsets[].element_layout",
    "NativeCompilerFacts::pointer_offsets[].stride_bits",
    "NativeCompilerFacts::pointer_offsets[].offset_ty",
    "NativeCompilerFacts::pointer_offsets[].provenance",
    "NativeSemanticBridge::schema",
    "NativeSemanticBridge::schema_version",
    "NativeSemanticBridge::relation",
    "NativeSemanticBridge::function",
    "NativeSemanticBridge::formula_schema",
    "NativeSemanticBridge::stable_digest()",
    "NativeSemanticBridge::petri_successor_plan_cache_equivalence()",
    "NativeSemanticBridge::is_petri_successor_plan_cache_equivalence()",
    "NativeSemanticBridgeReport::proof_obligation",
    "NativeSemanticBridgeReport::proof_digest",
    "NativeSemanticBridgeReport::proof_status",
    "NativeSemanticBridgeReport::evidence_digest",
    "NativeSemanticBridgeReport::evidence_status",
    "NativeSemanticBridgeReport::status",
    "NativeSemanticBridgeReport::reason",
    "NativeSemanticBridgeReport::status_code()",
    "NativeSemanticBridgeReport::reason_code()",
    "NativeSemanticBridgeReport::evidence_status_code()",
    "NativeSemanticBridgeReport::fail_closed()",
    "NativeSemanticBridgeReport::proof_identity_schema()",
    "NativeSemanticBridgeReport::proof_identity_schema_version()",
    "NativeSemanticBridgeReport::proof_identity_digest()",
    "NativeSemanticBridgeReport::proof_identity_rows()",
    "NativeSemanticBridgeReport::proof_identity_key_value_lines()",
    "NativeSemanticBridgeReport::proof_identity_key_value_text()",
    "NativeSemanticBridgeReport::proof_identity_replay_report()",
    "NativeSemanticBridgeReport::proof_identity_replay_report_for_key_value_lines()",
    "NativeSemanticBridgeReport::proof_identity_replay_report_for_key_value_text()",
    "NativeSemanticBridgeReport::represents_petri_successor_plan_cache_equivalence()",
    "NativeSemanticBridgeProofIdentityReplayReport::is_replayable()",
    "NativeSemanticBridgeProofIdentityReplayReport::diagnostic_count()",
    "NativeSemanticBridgeProofIdentityReplayReport::component_health_summary_rows()",
    "NativeSemanticBridgeProofIdentityReplayReport::component_health_summary_key_value_lines()",
    "NativeSemanticBridgeProofIdentityReplayReport::component_health_summary_key_value_text()",
    "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_rows()",
    "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_key_value_lines()",
    "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_key_value_text()",
    "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_json_text()",
    "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_round_trip_report()",
    "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_lines()",
    "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_text()",
    "NativeSemanticBridgeProofIdentityReplayStatus::code()",
    "NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::code()",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA_VERSION",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_digest()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_rows()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_key_value_lines()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_key_value_text()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_replay_report()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_replay_report_for_key_value_lines()",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_replay_report_for_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::is_replayable()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::diagnostic_count()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_rows()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_key_value_lines()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_rows()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_key_value_lines()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_json_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_round_trip_report()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_lines()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_round_trip_report_for_key_value_text()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::code()",
    "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::code()",
    "NativeVerificationBundle::petri_successor_semantic_bridge_report()",
    "petri_successor_trust_mc_chc_contract_descriptor()",
    "PetriSuccessorTrustMcChcContractDescriptor::schema",
    "PetriSuccessorTrustMcChcContractDescriptor::schema_version",
    "PetriSuccessorTrustMcChcContractDescriptor::formula_schema",
    "PetriSuccessorTrustMcChcContractDescriptor::binding_report_schema",
    "PetriSuccessorTrustMcChcContractDescriptor::binding_report_schema_version",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_handoff_report_schema",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_handoff_report_schema_version",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_evidence_identity_schema",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_evidence_identity_schema_version",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_evidence_identity_digest_context",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_evidence_identity_replay_report_schema",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_evidence_identity_replay_report_schema_version",
    "PetriSuccessorTrustMcChcContractDescriptor::model_validation_readiness_report_schema",
    "PetriSuccessorTrustMcChcContractDescriptor::model_validation_readiness_report_schema_version",
    "PetriSuccessorTrustMcChcContractDescriptor::verifier_suite",
    "PetriSuccessorTrustMcChcContractDescriptor::verification_mode",
    "PetriSuccessorTrustMcChcContractDescriptor::binding_required_artifact_kinds",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_handoff_required_artifact_kinds",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_handoff_optional_artifact_kinds",
    "PetriSuccessorTrustMcChcContractDescriptor::model_validation_required_artifact_kinds",
    "PetriSuccessorTrustMcChcContractDescriptor::production_acceptance_required_artifact_kinds",
    "PetriSuccessorTrustMcChcContractDescriptor::model_validation_requires_solver_acceptance",
    "PetriSuccessorTrustMcChcContractDescriptor::model_acceptance_report_api_name",
    "PetriSuccessorTrustMcChcContractDescriptor::consumer_acceptance_api_name",
    "PetriSuccessorTrustMcChcContractDescriptor::production_acceptance_owner_suite",
    "PetriSuccessorTrustMcChcContractDescriptor::shared_primitive_contract",
    "petri_successor_trust_mc_chc_shared_primitive_contract_descriptor()",
    "NativeSharedPrimitiveContractDescriptor::schema",
    "NativeSharedPrimitiveContractDescriptor::schema_version",
    "NativeSharedPrimitiveContractDescriptor::contract_schema",
    "NativeSharedPrimitiveContractDescriptor::contract_schema_version",
    "NativeSharedPrimitiveContractDescriptor::formula_schema",
    "NativeSharedPrimitiveContractDescriptor::readiness_report_schema",
    "NativeSharedPrimitiveContractDescriptor::readiness_report_schema_version",
    "NativeSharedPrimitiveContractDescriptor::verifier_suite",
    "NativeSharedPrimitiveContractDescriptor::verification_mode",
    "NativeSharedPrimitiveContractDescriptor::required_artifact_kinds",
    "NativeSharedPrimitiveContractDescriptor::optional_artifact_kinds",
    "NativeSharedPrimitiveContractDescriptor::required_artifact_requirements",
    "NativeSharedPrimitiveContractDescriptor::production_requires_emitted_solver_artifacts",
    "NativeSharedPrimitiveContractDescriptor::requires_solver_acceptance",
    "NativeSharedPrimitiveContractDescriptor::model_acceptance_report_api_name",
    "NativeSharedPrimitiveContractDescriptor::consumer_acceptance_api_name",
    "NativeSharedPrimitiveContractDescriptor::production_acceptance_owner_suite",
    "NativeSharedPrimitiveContractDescriptor::solver_evidence_descriptor",
    "NativeSharedPrimitiveContractDescriptor::production_required_artifact_requirements()",
    "NativeSharedPrimitiveContractDescriptor::production_requires_emitted_solver_artifacts()",
    "NativeSharedPrimitiveContractDescriptor::production_acceptance_report_api_name()",
    "NativeSharedPrimitiveContractDescriptor::production_consumer_acceptance_api_name()",
    "NativeSharedPrimitiveContractDescriptor::production_acceptance_requires_solver()",
    "NativeSharedPrimitiveContractDescriptor::production_acceptance_owner_suite()",
    "NativeSharedPrimitiveContractDescriptor::production_solver_evidence_descriptor()",
    "NativeSharedPrimitiveContractDescriptor::production_solver_capability_descriptor_schema()",
    "NativeSharedPrimitiveContractDescriptor::production_model_blocking_clause_schema()",
    "NativeSharedPrimitiveContractDescriptor::production_model_blocking_clause_evidence_schema()",
    "NativeSharedPrimitiveContractDescriptor::production_solve_decision_profile_model_consumer_schema()",
    "NativeSharedPrimitiveContractDescriptor::production_required_artifact_roles()",
    "NativeSharedPrimitiveContractDescriptor::production_artifact_owner_suites()",
    "NativeSharedPrimitiveContractDescriptor::production_required_artifact_requirement_for_role()",
    "NativeSharedPrimitiveContractDescriptor::production_required_artifact_requirement_for_kind()",
    "NativeSharedPrimitiveContractDescriptor::production_artifact_requirements_for_owner_suite()",
    "NativeSharedPrimitiveContractDescriptor::production_artifact_digest_algorithm()",
    "NativeSharedPrimitiveContractDescriptor::production_artifact_owner_suite()",
    "NativeSharedPrimitiveContractDescriptor::manifest_rows()",
    "NativeSharedPrimitiveContractDescriptor::manifest_key_value_lines()",
    "NativeSharedPrimitiveContractManifestRow::key",
    "NativeSharedPrimitiveContractManifestRow::value",
    "NativeSharedPrimitiveContractManifestRow::escaped_key()",
    "NativeSharedPrimitiveContractManifestRow::escaped_value()",
    "NativeSharedPrimitiveContractManifestRow::to_key_value_line()",
    "NativeSharedPrimitiveArtifactRequirement::role",
    "NativeSharedPrimitiveArtifactRequirement::kind",
    "NativeSharedPrimitiveArtifactRequirement::digest_algorithm",
    "NativeSharedPrimitiveArtifactRequirement::owner_suite",
    "NativeSharedPrimitiveArtifactRequirement::requires_emitted_solver_artifact",
    "NativeSharedPrimitiveArtifactRequirement::role_code()",
    "NativeSharedPrimitiveArtifactRequirement::accepts_artifact_identity()",
    "NativeSharedPrimitiveArtifactRole::code()",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::owner_suite",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::solver_capability_descriptor_schema",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::solver_capability_descriptor_schema_version",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::model_blocking_clause_schema",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::model_blocking_clause_schema_version",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::model_blocking_clause_evidence_schema",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::model_blocking_clause_evidence_schema_version",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::solve_decision_profile_model_consumer_schema",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::solve_decision_profile_model_consumer_schema_version",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::acceptance_report_api_name",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::consumer_acceptance_api_name",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::capability_descriptor_schema()",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::model_blocking_clause_schema()",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::model_blocking_clause_evidence_schema()",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::solve_decision_profile_model_consumer_schema()",
    "NativeSharedPrimitiveSolverEvidenceDescriptor::acceptance_api_names()",
    "PETRI_SUCCESSOR_TRUST_MC_CHC_SOLVER_EVIDENCE_DESCRIPTOR",
    "petri_native_verification_bundle_handoff_descriptor()",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA_VERSION",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DOWNSTREAM_CONSUMER_RESPONSIBILITIES",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_MISSING_ROW_KEYS",
    "petri_native_verification_bundle_handoff_replay_contract_surface()",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA_VERSION",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA_VERSION",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA_VERSION",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_HELPER_NAMES",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_NAMES",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_VALUES",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_FIXTURE_NAMES",
    "PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_VALIDATOR_NAMES",
    "PetriNativeVerificationBundleHandoffDescriptor::schema",
    "PetriNativeVerificationBundleHandoffDescriptor::schema_version",
    "PetriNativeVerificationBundleHandoffDescriptor::source_package",
    "PetriNativeVerificationBundleHandoffDescriptor::source_package_version",
    "PetriNativeVerificationBundleHandoffDescriptor::bundle_identity_contract",
    "PetriNativeVerificationBundleHandoffDescriptor::artifact_authority_row_descriptor",
    "PetriNativeVerificationBundleHandoffDescriptor::shared_primitive_contract",
    "PetriNativeVerificationBundleHandoffDescriptor::solver_evidence_descriptor",
    "PetriNativeVerificationBundleHandoffDescriptor::expected_bundle_identity_fields",
    "PetriNativeVerificationBundleHandoffDescriptor::downstream_consumer_responsibilities",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_key_value_lines()",
    "PetriNativeVerificationBundleHandoffDescriptor::required_normalized_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::validate_normalized_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::normalized_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::normalized_key_value_lines()",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_identity()",
    "PetriNativeVerificationBundleHandoffDescriptor::manifest_identity_for_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::canonical_manifest_text()",
    "PetriNativeVerificationBundleHandoffDescriptor::canonical_manifest_text_for_rows()",
    "PetriNativeVerificationBundleHandoffDescriptor::contract_health_report()",
    "PetriNativeVerificationBundleHandoffDescriptor::contract_health_report_for_rows()",
    "petri_native_verification_bundle_handoff_contract_health_report()",
    "petri_native_verification_bundle_handoff_diagnostic_fixture_manifest()",
    "petri_native_verification_bundle_handoff_healthy_diagnostic_fixture()",
    "petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture()",
    "petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_healthy_fixture()",
    "petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_stale_fixture()",
    "PetriNativeVerificationBundleHandoffManifestIdentity::schema",
    "PetriNativeVerificationBundleHandoffManifestIdentity::schema_version",
    "PetriNativeVerificationBundleHandoffManifestIdentity::descriptor_schema",
    "PetriNativeVerificationBundleHandoffManifestIdentity::descriptor_schema_version",
    "PetriNativeVerificationBundleHandoffManifestIdentity::source_package",
    "PetriNativeVerificationBundleHandoffManifestIdentity::source_package_version",
    "PetriNativeVerificationBundleHandoffManifestIdentity::digest_context",
    "PetriNativeVerificationBundleHandoffManifestIdentity::digest_algorithm",
    "PetriNativeVerificationBundleHandoffManifestIdentity::digest",
    "PetriNativeVerificationBundleHandoffManifestIdentity::canonical_text",
    "PetriNativeVerificationBundleHandoffManifestIdentity::completeness_status",
    "PetriNativeVerificationBundleHandoffManifestIdentity::completeness_status_code",
    "PetriNativeVerificationBundleHandoffManifestIdentity::observed_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentity::required_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentity::present_required_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentity::missing_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentity::missing_rows",
    "PetriNativeVerificationBundleHandoffManifestIdentity::missing_row_kinds",
    "PetriNativeVerificationBundleHandoffManifestIdentity::extra_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentity::is_complete()",
    "PetriNativeVerificationBundleHandoffManifestIdentity::fail_closed()",
    "PetriNativeVerificationBundleHandoffManifestIdentity::key_value_rows()",
    "PetriNativeVerificationBundleHandoffManifestIdentity::key_value_lines()",
    "PetriNativeVerificationBundleHandoffManifestIdentity::key_value_text()",
    "PetriNativeVerificationBundleHandoffManifestIdentity::round_trip_report()",
    "PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic::row_kind_code",
    "PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic::key",
    "PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic::ordinal",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::status",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::status_code",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::fail_closed",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::expected_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::observed_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::unique_key_count",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::duplicate_keys",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::missing_keys",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::unexpected_keys",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::mismatched_value_keys",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::invalid_bool_keys",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::invalid_usize_keys",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_schema",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_schema_version",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_digest_context",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_digest",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_completeness_status_code",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_fail_closed",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_missing_row_count",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_missing_row_kind_count",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_missing_row_kinds",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport::reconstructed_missing_rows",
    "PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::code()",
    "PetriNativeVerificationBundleHandoffContractHealthReport::status",
    "PetriNativeVerificationBundleHandoffContractHealthReport::status_code",
    "PetriNativeVerificationBundleHandoffContractHealthReport::descriptor_schema",
    "PetriNativeVerificationBundleHandoffContractHealthReport::descriptor_schema_version",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_schema",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_schema_version",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::normalized_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::required_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::completeness_required_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::completeness_present_required_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::completeness_missing_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_observed_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_required_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_present_required_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_missing_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_extra_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_key_value_row_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_key_value_line_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_key_value_text_line_count",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_digest",
    "PetriNativeVerificationBundleHandoffContractHealthReport::schema_version_rows_agree",
    "PetriNativeVerificationBundleHandoffContractHealthReport::row_counts_agree",
    "PetriNativeVerificationBundleHandoffContractHealthReport::completeness_agrees",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_digest_agrees",
    "PetriNativeVerificationBundleHandoffContractHealthReport::manifest_identity_key_values_agree",
    "PetriNativeVerificationBundleHandoffContractHealthReport::is_healthy()",
    "PetriNativeVerificationBundleHandoffContractHealthReport::fail_closed()",
    "PetriNativeVerificationBundleHandoffContractHealthReport::key_value_rows()",
    "PetriNativeVerificationBundleHandoffContractHealthReport::key_value_lines()",
    "PetriNativeVerificationBundleHandoffContractHealthReport::key_value_text()",
    "PetriNativeVerificationBundleHandoffContractHealthStatus::code()",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::schema",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::schema_version",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::source_package",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::source_package_version",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::fixtures",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::key_value_rows()",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::key_value_lines()",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::key_value_text()",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest::round_trip_report()",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::fixture_name",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::expected_completeness_status_code",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::expected_manifest_identity_status_code",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::expected_contract_health_status_code",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::expected_accepted",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::expected_fail_closed",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::handoff_schema",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::handoff_schema_version",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::manifest_identity_schema",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry::manifest_identity_schema_version",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::status",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::status_code",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::fail_closed",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::expected_row_count",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::observed_row_count",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::unique_key_count",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::duplicate_keys",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::missing_keys",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::unexpected_keys",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::mismatched_value_keys",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::invalid_bool_keys",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::reconstructed_fixture_names",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::reconstructed_completeness_status_codes",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::reconstructed_manifest_identity_status_codes",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::reconstructed_contract_health_status_codes",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::reconstructed_accepted_values",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport::reconstructed_fail_closed_values",
    "PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::code()",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::fixture_name",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::normalized_rows",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::completeness_report",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::manifest_identity",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::manifest_identity_rows",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::contract_health_report",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::contract_health_rows",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::is_healthy()",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::accepted()",
    "PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture::fail_closed()",
    "PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture::fixture_name",
    "PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture::missing_row_keys",
    "PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture::normalized_rows",
    "PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture::completeness_report",
    "PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture::manifest_identity",
    "PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture::contract_health_report",
    "PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture::fail_closed()",
    "PetriNativeVerificationBundleHandoffRow::row_kind",
    "PetriNativeVerificationBundleHandoffRow::row_kind_code",
    "PetriNativeVerificationBundleHandoffRow::key",
    "PetriNativeVerificationBundleHandoffRow::value",
    "PetriNativeVerificationBundleHandoffRow::new()",
    "PetriNativeVerificationBundleHandoffRow::escaped_key()",
    "PetriNativeVerificationBundleHandoffRow::escaped_value()",
    "PetriNativeVerificationBundleHandoffRow::to_normalized_line()",
    "PetriNativeVerificationBundleHandoffRowKind::code()",
    "PetriNativeVerificationBundleHandoffRequiredRow::row_kind",
    "PetriNativeVerificationBundleHandoffRequiredRow::row_kind_code",
    "PetriNativeVerificationBundleHandoffRequiredRow::key",
    "PetriNativeVerificationBundleHandoffRequiredRow::ordinal",
    "PetriNativeVerificationBundleHandoffCompletenessReport::status",
    "PetriNativeVerificationBundleHandoffCompletenessReport::status_code",
    "PetriNativeVerificationBundleHandoffCompletenessReport::required_rows",
    "PetriNativeVerificationBundleHandoffCompletenessReport::missing_rows",
    "PetriNativeVerificationBundleHandoffCompletenessReport::missing_row_kinds",
    "PetriNativeVerificationBundleHandoffCompletenessReport::required_row_count",
    "PetriNativeVerificationBundleHandoffCompletenessReport::present_required_row_count",
    "PetriNativeVerificationBundleHandoffCompletenessReport::is_complete()",
    "PetriNativeVerificationBundleHandoffCompletenessReport::fail_closed()",
    "PetriNativeVerificationBundleHandoffCompletenessStatus::code()",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::schema",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::schema_version",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::source_package",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::source_package_version",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::helper_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::schema_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::schema_values",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::fixture_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::validator_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::key_value_rows()",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::key_value_lines()",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::key_value_text()",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::round_trip_report()",
    "PetriNativeVerificationBundleHandoffReplayContractSurface::round_trip_report_for_key_value_lines()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::status",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::status_code",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::fail_closed",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::expected_row_count",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::observed_row_count",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::unique_key_count",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::duplicate_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::missing_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::unexpected_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::mismatched_value_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::invalid_usize_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::invalid_lines",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_schema",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_schema_version",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_helper_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_schema_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_schema_values",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_fixture_count",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_fixture_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::reconstructed_validator_names",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::schema_header_matches",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::schema_name_value_rows_agree",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::helper_names_match",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::fixture_count_matches",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::fixture_names_match",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::validator_names_match",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::diagnostic_count()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::canonical_identity_text()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::identity_digest()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::compact_manifest_json_text()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::compact_manifest_handoff_identity_report()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::key_value_rows()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::key_value_lines()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::key_value_text()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::key_value_round_trip_report()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::key_value_line_round_trip_report()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::status",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::status_code",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::fail_closed",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::expected_row_count",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::observed_row_count",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::unique_key_count",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::duplicate_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::missing_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::unexpected_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::mismatched_value_keys",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport::invalid_lines",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::schema",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::schema_version",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::status",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::status_code",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::fail_closed",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::json_manifest_text_digest",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::round_trip_report_identity_digest",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::manifest_identity_digest",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::key_value_rows()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::key_value_lines()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::key_value_text()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport::is_bound()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::fixture_name",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::compact_json_text",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::round_trip_report",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::manifest_identity",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::binding_report",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::binding_rows",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::accepted()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::fail_closed()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::key_value_rows()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::key_value_lines()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::key_value_text()",
    "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::code()",
    "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::code()",
    "AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA",
    "AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION",
    "AY_MODEL_BLOCKING_CLAUSE_SCHEMA",
    "AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION",
    "AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA",
    "AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION",
    "AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA",
    "AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION",
    "NativeSharedPrimitiveVerificationMode::verifier_suite()",
    "NativeSharedPrimitiveVerificationMode::code()",
    "NativeVerifierSuite::code()",
    "NativeEvidenceArtifactKind::code()",
    "NativeEvidenceArtifactAuthority::code()",
    "NativeEvidenceArtifactAttachmentKey::request",
    "NativeEvidenceArtifactAttachmentKey::kind",
    "NativeEvidenceArtifactAttachmentKey::digest_algorithm",
    "NativeEvidenceArtifactAttachmentKey::digest",
    "NativeEvidenceArtifactAttachmentKey::new()",
    "NativeEvidenceArtifactAttachmentKey::for_artifact()",
    "NativeEvidenceArtifactAttachment::key",
    "NativeEvidenceArtifactAttachment::owner_suite",
    "NativeEvidenceArtifactAttachment::source_identity",
    "NativeEvidenceArtifactAttachment::bytes",
    "NativeEvidenceArtifactAttachment::new()",
    "NativeEvidenceArtifactAttachment::for_artifact()",
    "NativeEvidenceArtifactAttachment::digest_for_bytes()",
    "NativeEvidenceArtifactResolution::report",
    "NativeEvidenceArtifactResolution::bytes",
    "NativeEvidenceArtifactResolution::is_resolved()",
    "NativeEvidenceArtifactResolution::is_authoritative()",
    "NativeEvidenceArtifactResolution::authoritative_bytes()",
    "NativeEvidenceArtifactResolution::authority_evidence_rows()",
    "NativeEvidenceArtifactResolution::authority_evidence_key_value_lines()",
    "NativeEvidenceArtifactAttachmentResolution::request",
    "NativeEvidenceArtifactAttachmentResolution::owner_suite",
    "NativeEvidenceArtifactAttachmentResolution::required_kind",
    "NativeEvidenceArtifactAttachmentResolution::artifact",
    "NativeEvidenceArtifactAttachmentResolution::resolution",
    "NativeEvidenceArtifactAttachmentResolution::status",
    "NativeEvidenceArtifactAttachmentResolution::reason",
    "NativeEvidenceArtifactAttachmentResolution::is_resolved()",
    "NativeEvidenceArtifactAttachmentResolution::is_authoritative()",
    "NativeEvidenceArtifactAttachmentResolution::fail_closed()",
    "NativeEvidenceArtifactAttachmentResolution::artifact_digest()",
    "NativeEvidenceArtifactAttachmentResolution::actual_digest()",
    "NativeEvidenceArtifactAttachmentResolution::byte_source_identity()",
    "NativeEvidenceArtifactAttachmentResolution::byte_len()",
    "NativeEvidenceArtifactAttachmentResolution::bytes()",
    "NativeEvidenceArtifactAttachmentResolution::authoritative_bytes()",
    "NativeEvidenceArtifactAttachmentResolution::status_code()",
    "NativeEvidenceArtifactAttachmentResolution::reason_code()",
    "NativeEvidenceArtifactAttachmentResolution::authority_evidence_rows()",
    "NativeEvidenceArtifactAttachmentResolution::authority_evidence_key_value_lines()",
    "NativeEvidenceArtifactResolutionReport::schema",
    "NativeEvidenceArtifactResolutionReport::schema_version",
    "NativeEvidenceArtifactResolutionReport::request",
    "NativeEvidenceArtifactResolutionReport::owner_suite",
    "NativeEvidenceArtifactResolutionReport::required_kind",
    "NativeEvidenceArtifactResolutionReport::digest_algorithm",
    "NativeEvidenceArtifactResolutionReport::digest",
    "NativeEvidenceArtifactResolutionReport::artifact_name",
    "NativeEvidenceArtifactResolutionReport::byte_source_identity",
    "NativeEvidenceArtifactResolutionReport::byte_len",
    "NativeEvidenceArtifactResolutionReport::actual_digest",
    "NativeEvidenceArtifactResolutionReport::authority",
    "NativeEvidenceArtifactResolutionReport::status",
    "NativeEvidenceArtifactResolutionReport::reason",
    "NativeEvidenceArtifactResolutionReport::authority_code()",
    "NativeEvidenceArtifactResolutionReport::status_code()",
    "NativeEvidenceArtifactResolutionReport::reason_code()",
    "NativeEvidenceArtifactResolutionReport::is_resolved()",
    "NativeEvidenceArtifactResolutionReport::is_authoritative()",
    "NativeEvidenceArtifactResolutionReport::fail_closed()",
    "NativeEvidenceArtifactResolutionReport::authority_evidence_rows()",
    "NativeEvidenceArtifactResolutionReport::authority_evidence_key_value_lines()",
    "NativeEvidenceArtifactResolutionStatus::code()",
    "NativeEvidenceArtifactResolutionReason::code()",
    "NativeEvidenceArtifactAuthorityRow::key",
    "NativeEvidenceArtifactAuthorityRow::value",
    "NativeEvidenceArtifactAuthorityRow::escaped_key()",
    "NativeEvidenceArtifactAuthorityRow::escaped_value()",
    "NativeEvidenceArtifactAuthorityRow::to_key_value_line()",
    "NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_REPORT_ROW_KEYS",
    "NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_RESOLUTION_ROW_KEYS",
    "NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_DESCRIPTOR",
    "native_evidence_artifact_authority_row_descriptor()",
    "NativeEvidenceArtifactAuthorityRowDescriptor::schema",
    "NativeEvidenceArtifactAuthorityRowDescriptor::schema_version",
    "NativeEvidenceArtifactAuthorityRowDescriptor::report_row_keys",
    "NativeEvidenceArtifactAuthorityRowDescriptor::resolution_row_keys",
    "NativeEvidenceArtifactAuthorityRowDescriptor::report_row_keys_match()",
    "NativeEvidenceArtifactAuthorityRowDescriptor::resolution_row_keys_match()",
    "NativeEvidenceArtifactAuthorityRowDescriptor::manifest_rows()",
    "NativeEvidenceArtifactAuthorityRowDescriptor::manifest_key_value_lines()",
    "NativeEvidenceArtifactAuthorityRowsKind::code()",
    "NativeEvidenceArtifactAuthorityRowsValidationReport::rows_kind",
    "NativeEvidenceArtifactAuthorityRowsValidationReport::valid",
    "NativeEvidenceArtifactAuthorityRowsValidationReport::diagnostics",
    "NativeEvidenceArtifactAuthorityRowsValidationReport::is_valid()",
    "NativeEvidenceArtifactAuthorityRowsValidationReport::fail_closed()",
    "NativeEvidenceArtifactAuthorityRowsValidationReport::diagnostic_count()",
    "validate_native_evidence_artifact_authority_rows()",
    "validate_native_evidence_artifact_authority_key_value_lines()",
    "PetriSuccessorTrustMcChcContractDescriptor::provided_fields",
    "PetriSuccessorTrustMcChcContractDescriptor::binding_status_codes",
    "PetriSuccessorTrustMcChcContractDescriptor::binding_reason_codes",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_handoff_status_codes",
    "PetriSuccessorTrustMcChcContractDescriptor::proof_handoff_reason_codes",
    "PetriSuccessorTrustMcChcContractDescriptor::model_validation_readiness_status_codes",
    "PetriSuccessorTrustMcChcContractDescriptor::model_validation_readiness_reason_codes",
    "NativeVerificationBundle::petri_successor_trust_mc_chc_binding_report()",
    "PetriSuccessorTrustMcChcBindingReport::function",
    "PetriSuccessorTrustMcChcBindingReport::semantic_bridge_report",
    "PetriSuccessorTrustMcChcBindingReport::request",
    "PetriSuccessorTrustMcChcBindingReport::request_digest",
    "PetriSuccessorTrustMcChcBindingReport::evidence_digest",
    "PetriSuccessorTrustMcChcBindingReport::expected_evidence_digest",
    "PetriSuccessorTrustMcChcBindingReport::horn_clause_artifact",
    "PetriSuccessorTrustMcChcBindingReport::status",
    "PetriSuccessorTrustMcChcBindingReport::reason",
    "PetriSuccessorTrustMcChcBindingReport::is_bound()",
    "PetriSuccessorTrustMcChcBindingReport::status_code()",
    "PetriSuccessorTrustMcChcBindingReport::reason_code()",
    "PetriSuccessorTrustMcChcBindingReport::fail_closed()",
    "NativeVerificationBundle::petri_successor_trust_mc_chc_proof_handoff_report()",
    "PetriSuccessorTrustMcChcProofHandoffReport::function",
    "PetriSuccessorTrustMcChcProofHandoffReport::binding_report",
    "PetriSuccessorTrustMcChcProofHandoffReport::proof_identity_digest",
    "PetriSuccessorTrustMcChcProofHandoffReport::replay",
    "PetriSuccessorTrustMcChcProofHandoffReport::replay_transcript_digest",
    "PetriSuccessorTrustMcChcProofHandoffReport::replay_transcript_artifact",
    "PetriSuccessorTrustMcChcProofHandoffReport::model_artifact",
    "PetriSuccessorTrustMcChcProofHandoffReport::solver_identities",
    "PetriSuccessorTrustMcChcProofHandoffReport::status",
    "PetriSuccessorTrustMcChcProofHandoffReport::reason",
    "PetriSuccessorTrustMcChcProofHandoffReport::is_ready()",
    "PetriSuccessorTrustMcChcProofHandoffReport::status_code()",
    "PetriSuccessorTrustMcChcProofHandoffReport::reason_code()",
    "PetriSuccessorTrustMcChcProofHandoffReport::fail_closed()",
    "NativeVerificationBundle::petri_successor_trust_mc_chc_model_validation_readiness_report()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::function",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::proof_handoff_report",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::model_artifact",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::model_artifact_digest",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::solver_identities",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::model_validated",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::status",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::reason",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::status_code()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::reason_code()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::is_ready_for_solver_validation()",
    "PetriSuccessorTrustMcChcModelValidationReadinessReport::fail_closed()",
    "NativeVerificationBundle::petri_successor_semantic_bridge_proof_admission_report()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::function",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::proof_handoff_report",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::required_artifact_kinds",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::artifact_resolutions",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::blocked_artifact_kind",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::blocked_artifact_reason",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::status",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::reason",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::status_code()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::reason_code()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::blocked_artifact_reason_code()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::artifact_resolution_for_kind()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::authoritative_bytes_for_kind()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::authoritative_byte_count()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::key_value_rows()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::key_value_lines()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::key_value_text()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::is_admitted()",
    "PetriSuccessorSemanticBridgeProofAdmissionReport::fail_closed()",
];

/// Stable digest contexts used by the native-bundle identity contract.
pub const NATIVE_BUNDLE_IDENTITY_CONTRACT_DIGEST_CONTEXTS: &[&str] = &[
    "trust_ir.module.v2",
    "trust_ir.proof.evidence.v2",
    "trust_ir.proof.certificate.v2",
    "trust_ir.proof.lineage.node.v2",
    "trust_ir.proof.lineage.manifest.v2",
    "trust_ir.native.verification.bundle.v6",
    "trust_ir.native.verification.request.v2",
    "trust_ir.native.evidence.bundle.v2",
    "trust_ir.native.transport_identity.v2",
    "trust_ir.native.target_abi_identity.v2",
    "trust_ir.native.compiler.facts.v4",
    "trust_ir.native.replay.atom.payload.v2",
    "trust_ir.native.semantic_bridge.v2",
    "trust_ir.native.semantic_bridge.proof_obligation.v3",
    "trust_ir.native.semantic_bridge.proof_identity.v2",
];

/// Native-call identities intentionally owned by downstream compiled artifacts.
///
/// **Intentional contract manifest — not test scaffolding.** The *external*
/// half of the owned/external split (see
/// [`NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS`]); embedded into
/// [`NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR`] (`external_fields`). Every
/// entry names a TrustCg-owned identity, so each must carry the `trust_cg.`
/// namespace prefix — that prefix is the structural invariant
/// `manifest_field_sets_have_no_drift` enforces for this list.
pub static NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS: &[&str] = &[
    "trust_cg.NativeInstallGatePayloadIdentity::native_payload_sha256",
    "trust_cg.PetriNativeSuccessorTrampolineContract::entry_symbol",
    "trust_cg.PetriNativeSuccessorTrampolineContract::trampoline_abi",
    "trust_cg.PetriNativeSuccessorTrampolineContract::trampoline_sha256",
];
