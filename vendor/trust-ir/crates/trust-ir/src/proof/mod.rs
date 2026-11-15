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
pub mod clause_typing;
#[cfg(feature = "clean-expr-codec")]
mod clean_expr_codec;
#[cfg(feature = "clean-expr-codec")]
mod clean_expr_dag;
mod digest_observed;
mod evidence;
pub mod formula_schema;
mod lineage;
mod obligations;
mod observed_equality;
mod observed_sort_debug;
pub mod satprov;
pub mod satres;
pub mod smtlib_source;
mod transform;

#[cfg(test)]
mod tests;

pub use annotations::{Divergence, ProofAnnotation, ProofAnnotationFilters};
// The bit-vector goal kernel: what a sited panic-class obligation STATES,
// re-derived from the IR by validator-owned code. Lives in the zero-dep core so
// the producer and the validator cannot disagree about it.
pub use bvgoal::{
    ASSERT_CLASS_OBLIGATION_KINDS, BVBLAST_GOAL_SCHEMA, BVGOAL_MAX_NODES, BVGOAL_MAX_WIDTH, BvGoal,
    BvTerm, BvTermError, GoalDeriveError, PRODUCER_FORMULA_DISAGREES, assert_class_kind_refusal,
    bvblast_goal_formula, bvblast_goal_formula_parts, bvgoal_canonical_bytes, bvgoal_digest,
    bvgoal_digest_hex, bvgoal_formula, bvgoal_leaf_name, bvgoal_smtlib, derive_site_goal,
    formula_binds_site_goal, formula_matches_goal, is_assert_class_kind, is_assert_site_inst,
    is_bvgoal_digest_hex, is_diverging_arm, lowered_assert_condition,
};
// FUSION (design 2026-06-20-fusion-obligation-as-clean-expr): the on-node
// `Expr`-valued obligation carrier, re-exported so `crate::proof::ExprObligation`
// (and the crate-root `trust_ir::ExprObligation`) resolve unchanged after the
// proof.rs -> proof/ split. Gated so the default zero-dep build never sees it.
#[cfg(feature = "clean-expr")]
pub use annotations::ExprObligation;
#[cfg(feature = "clean-expr-codec")]
pub use clean_expr_codec::{
    CLEAN_CIC_STATEMENT_DIGEST_V1_DOMAIN, CLEAN_EXPR_V1_MAX_BYTES, CLEAN_EXPR_V1_MAX_DEPTH,
    CLEAN_EXPR_V1_MAX_NODES, ISLAND_DECLARATIONS_V1_MAX_BYTES,
    ISLAND_DECLARATIONS_V1_MAX_DECLARATIONS, ISLAND_DECLARATIONS_V1_MAX_DEPTH,
    ISLAND_DECLARATIONS_V1_MAX_NODES, KERNEL_ENVIRONMENT_DIGEST_V1_DOMAIN,
    clean_cic_statement_digest, decode_clean_expr_v1, decode_island_declarations_v1,
    encode_clean_expr_v1, encode_island_declarations_v1, kernel_environment_digest,
};
#[cfg(feature = "clean-expr-codec")]
pub use clean_expr_dag::{
    CLEAN_EXPR_DAG_V2_MAX_BYTES, CLEAN_EXPR_DAG_V2_MAX_CONSTRUCTOR_WORK,
    CLEAN_EXPR_DAG_V2_MAX_DEPTH, CLEAN_EXPR_DAG_V2_MAX_ENCODE_WORK_BYTES,
    CLEAN_EXPR_DAG_V2_MAX_NODES, CLEAN_EXPR_DAG_V2_MAX_SCRATCH_BYTES, decode_clean_expr_dag_v2,
    encode_clean_expr_dag_v2,
};
pub use evidence::{
    CertificateBinding, CleanCicKernelRecheck, CleanCicModuleProofAuthority,
    CleanCicProofAuthorityRechecker, CleanCicRechecker, CoverageAssurance, CoverageBound,
    ISLAND_DECLARATIONS_DIGEST_V1_DOMAIN, IslandEnvironment,
    KERNEL_ANCHOR_CLEAN_BACKEND_READONLY_CALLS_V1, KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1,
    KERNEL_ANCHOR_CLEAN_BACKEND_TV, KERNEL_ANCHOR_CLEAN_ISLAND, KERNEL_ANCHOR_CLEAN_ISLAND_MODULE,
    KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE, KERNEL_ANCHOR_GIVEBACK_AGGREGATE,
    KERNEL_ANCHOR_GIVEBACK_CLOSURE, KERNEL_ANCHOR_GIVEBACK_COND, KERNEL_ANCHOR_GIVEBACK_ENUM,
    KERNEL_ANCHOR_GIVEBACK_GENERICS, KERNEL_ANCHOR_GIVEBACK_HASHMAP, KERNEL_ANCHOR_GIVEBACK_LIST,
    KERNEL_ANCHOR_GIVEBACK_LOOP, KERNEL_ANCHOR_GIVEBACK_NESTED, KERNEL_ANCHOR_GIVEBACK_REFINEMENT,
    KERNEL_ANCHOR_GIVEBACK_SPLIT, KERNEL_ANCHOR_GIVEBACK_STEP, KERNEL_ANCHOR_GIVEBACK_TRAIT,
    KERNEL_ANCHOR_GIVEBACK_U32, KERNEL_ANCHOR_GIVEBACK_VEC, KERNEL_ANCHOR_SLACKCERTZ,
    KERNEL_ANCHOR_TRUST_IR_CONTRACT, KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE,
    KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION, KernelClaimFamily,
    LEAN_THEOREM_OBLIGATION_NAMESPACE, ModuleCleanCicRechecker, ModuleProofAuthority,
    ProofAuthorityRechecker, ProofCertificate, ProofCertificateRef, ProofDigest,
    ProofDigestAlgorithm, ProofDigestSha256DomainStream, ProofDigestStreamError, ProofEvidence,
    ProofEvidenceShape, RejectingCleanCicRechecker, RejectingModuleProofAuthority,
    RejectingProofAuthorityRechecker, SourceDefinitionRef, clean_cic_lineage_binds,
    clean_cic_lineage_content_v8, clean_cic_lineage_digest, clean_cic_lineage_digest_v8,
    clean_cic_lineage_is_v8, is_clean_source_call_anchor, is_lean_theorem_kind,
    island_declarations_digest, module_symbol_resolver, obligation_has_kernel_rechecked_clean_cic,
    obligation_has_kernel_rechecked_clean_cic_in, obligation_has_matching_clean_cic,
    obligation_has_replayed_authority, obligation_has_replayed_module_authority,
};
// Crate-internal: the byte-layout core of `Module::obligation_digest` (v23).
// `evidence` is a private module, so lib.rs reaches it through this re-export.
#[cfg(feature = "fmt")]
pub(crate) use evidence::obligation_content_digest;
pub(crate) use evidence::write_proof_obligation_source_identity_stable;
// The formula schemas trust-ir owns and the one text each states.
pub use formula_schema::{OwnedFormulaSchema, OwnedFormulaText};
pub use lineage::{
    LINEAGE_TRANSFORM_BINDING_SCHEMA, LineageAppendError, LineageGap, ProofLineageError,
    ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofReplayIdentity, ProofTransform,
    ProofTransformStage, lineage_closed, lineage_closed_with_authority,
    lineage_transform_binding_digest, lineage_transform_binding_formula,
};
pub use obligations::{
    ClauseBinding, ClausePlace, ClauseSort, DiagnosticSeverity, FormulaSite, FormulaSiteRef,
    ObligationDiagnostic, ObligationKind, ObligationKindShape, ObligationSite,
    PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES, ProofContext, ProofFormula, ProofObligation,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus, ProofSummary,
    PublicObligationIdentity, SMTLIB2_FORMULA_SCHEMA, SpecObligationRef,
    is_canonical_public_obligation_id, is_valid_proof_obligation_source_text_id,
};
// The ONE reader of SMT-LIB2 formula text: every trust-ir reader of an
// `smtlib2` formula (the contract grounder, the clause free-name reader, the
// Linked spec surface) reads through it, and so does a consumer that must
// know what a replay grounded.
pub use smtlib_source::{
    MAX_SMTLIB_TERM_DEPTH, SmtSexp, SmtSourceDefect, is_smtlib_token, read_smtlib_term,
};
pub use transform::{
    IntroducedProofObligation, PROOF_TABLE_TRANSFORM_SCHEMA_VERSION,
    PROOF_TRANSFORM_TEXT_MAX_BYTES, ProofObligationDisposition, ProofObligationTransform,
    ProofTableTransformError, ProofTableTransformTransaction, ProofTableTransformValidation,
};
