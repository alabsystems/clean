// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof annotations, obligations, evidence, and lineage.
//!
//! Proof annotations are the mechanism by which TrustIr carries verification
//! evidence from frontends to the backend. This module is split into four
//! cohesive submodules — every public item is re-exported here, so external
//! paths such as `crate::proof::ProofAnnotation` resolve unchanged:
//!
//! * [`annotations`] — [`ProofAnnotation`], [`Divergence`], and the annotation
//!   classifier methods.
//! * [`obligations`] — [`ProofObligation`], [`ObligationKind`], [`ProofStatus`],
//!   [`ProofFormula`], [`ProofSummary`], and [`ProofContext`].
//! * [`evidence`] — [`ProofEvidence`], [`ProofCertificate`],
//!   [`ProofCertificateRef`], the [`ProofDigest`] family, and the CleanCic
//!   lineage helpers.
//! * [`lineage`] — the [`ProofLineageManifest`] and its building blocks.

mod annotations;
pub mod bvgoal;
#[cfg(feature = "clean-expr")]
mod clean_expr_codec;
mod evidence;
mod lineage;
mod obligations;
pub mod satprov;
pub mod satres;

#[cfg(test)]
mod tests;

pub use annotations::{Divergence, ProofAnnotation, ProofAnnotationFilters};
// The bit-vector goal kernel: what a sited panic-class obligation STATES,
// re-derived from the IR by validator-owned code. Lives in the zero-dep core so
// the producer and the validator cannot disagree about it.
pub use bvgoal::{
    BVBLAST_GOAL_SCHEMA, BVGOAL_MAX_NODES, BVGOAL_MAX_WIDTH, BvGoal, BvTerm, BvTermError,
    GoalDeriveError, bvblast_goal_formula, bvblast_goal_formula_parts, bvgoal_canonical_bytes,
    bvgoal_digest, bvgoal_digest_hex, bvgoal_leaf_name, derive_site_goal, is_diverging_arm,
    lowered_assert_condition,
};
// FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the on-node
// `Expr`-valued obligation carrier, re-exported so `crate::proof::ExprObligation`
// (and the crate-root `trust_ir::ExprObligation`) resolve unchanged after the
// proof.rs -> proof/ split. Gated so the default zero-dep build never sees it.
#[cfg(feature = "clean-expr")]
pub use annotations::ExprObligation;
#[cfg(feature = "clean-expr")]
pub use clean_expr_codec::{
    CLEAN_EXPR_V1_MAX_BYTES, CLEAN_EXPR_V1_MAX_DEPTH, CLEAN_EXPR_V1_MAX_NODES,
    decode_clean_expr_v1, encode_clean_expr_v1,
};
pub use evidence::{
    CleanCicKernelRecheck, CleanCicProofAuthorityRechecker, CleanCicRechecker,
    KERNEL_ANCHOR_CLEAN_BACKEND_TV, KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE,
    KERNEL_ANCHOR_GIVEBACK_AGGREGATE, KERNEL_ANCHOR_GIVEBACK_CLOSURE, KERNEL_ANCHOR_GIVEBACK_COND,
    KERNEL_ANCHOR_GIVEBACK_ENUM, KERNEL_ANCHOR_GIVEBACK_GENERICS, KERNEL_ANCHOR_GIVEBACK_HASHMAP,
    KERNEL_ANCHOR_GIVEBACK_LIST, KERNEL_ANCHOR_GIVEBACK_LOOP, KERNEL_ANCHOR_GIVEBACK_NESTED,
    KERNEL_ANCHOR_GIVEBACK_REFINEMENT, KERNEL_ANCHOR_GIVEBACK_SPLIT, KERNEL_ANCHOR_GIVEBACK_STEP,
    KERNEL_ANCHOR_GIVEBACK_TRAIT, KERNEL_ANCHOR_GIVEBACK_U32, KERNEL_ANCHOR_GIVEBACK_VEC,
    KERNEL_ANCHOR_SLACKCERTZ, KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION, ModuleProofAuthority,
    ProofAuthorityRechecker, ProofCertificate, ProofCertificateRef, ProofDigest,
    ProofDigestAlgorithm, ProofEvidence, RejectingCleanCicRechecker, RejectingModuleProofAuthority,
    RejectingProofAuthorityRechecker, clean_cic_lineage_digest,
    obligation_has_kernel_rechecked_clean_cic, obligation_has_matching_clean_cic,
    obligation_has_replayed_authority,
};
// Crate-internal: the byte-layout core of `Module::obligation_digest` (v23).
// `evidence` is a private module, so lib.rs reaches it through this re-export.
#[cfg(feature = "fmt")]
pub(crate) use evidence::obligation_content_digest;
pub(crate) use evidence::write_proof_obligation_source_identity_stable;
pub use lineage::{
    LINEAGE_TRANSFORM_BINDING_SCHEMA, LineageGap, ProofLineageError, ProofLineageId,
    ProofLineageManifest, ProofLineageNode, ProofReplayIdentity, ProofTransform,
    ProofTransformStage, lineage_closed, lineage_closed_with_authority,
    lineage_transform_binding_digest, lineage_transform_binding_formula,
};
pub use obligations::{
    DiagnosticSeverity, ObligationDiagnostic, ObligationKind, ObligationSite,
    PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES, ProofContext, ProofFormula, ProofObligation,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus, ProofSummary,
    PublicObligationIdentity, is_canonical_public_obligation_id,
    is_valid_proof_obligation_source_text_id,
};
