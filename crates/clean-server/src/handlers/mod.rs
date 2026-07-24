// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Request handlers for clean JSON-RPC server
//!
//! Each method handler takes parsed parameters and produces a result or error.
//! Handlers are organized into submodules:
//! - `types`: Shared request/response type definitions
//! - `core`: Theorem-proving handlers (check, prove, getType, batchCheck)
//! - `admin`: Server management handlers (info, config, metrics, environment)
//! - `verify`: Verification handlers (verifyC, verifyProof, verifyProofBatch, verifyFile, fillSorries, composeProof)

// Allow manual modulo check since is_multiple_of is nightly-only
#![allow(clippy::manual_is_multiple_of)]

mod admin;
mod cert;
mod check_decl_validation;
mod core;
mod external_cert;
mod external_cert_alethe;
mod helpers;
mod premise;
pub(crate) mod prove_response;
mod search_proof;
mod state;
mod swarm;
mod tactic;
mod tla_handler;
pub(crate) mod types;
mod verify;
mod widget;

pub use check_decl_validation::validate_decl_read_only;
#[cfg(test)]
pub(crate) use prove_response::build_verified_prove_result;
pub(crate) use prove_response::prove_result_from_automation_outcome;
pub(crate) use prove_response::prove_result_from_smt_verification;
pub use state::{CacheMetrics, ServerMetrics, ServerState};

// Re-export shared types
pub use types::*;

// Re-export core handlers
pub use core::{handle_batch_check, handle_check, handle_get_type, handle_prove};

// Re-export admin handlers
pub use admin::{
    handle_get_cache_metrics, handle_get_config, handle_get_environment, handle_get_metrics,
    handle_import_module, handle_load_environment, handle_save_environment, handle_server_info,
};

// Re-export verify handlers and types
pub(crate) use verify::trust_summary_from_ledger;
pub(crate) use verify::trust_summary_from_proof_state;
pub use verify::{
    handle_compose_proof, handle_fill_sorries, handle_verify_c, handle_verify_file,
    handle_verify_proof, handle_verify_proof_batch, ComposeProofParams, ComposeProofResult,
    ExtractedTheorem, FillSorriesParams, FillSorriesResult, SorryLocation, SorryProvenance,
    SorryReplacement, TimingBreakdown, TrustSummary, VerifyCFunctionResult, VerifyCParams,
    VerifyCResult, VerifyCVCDetail, VerifyFileParams, VerifyFileResult, VerifyProofBatchItem,
    VerifyProofBatchItemResult, VerifyProofBatchParams, VerifyProofBatchResult,
    VerifyProofBatchStats, VerifyProofContext, VerifyProofError, VerifyProofParams,
    VerifyProofPosition, VerifyProofResult,
};

// Re-export certificate module types and handlers
pub use cert::{
    handle_archive_cert, handle_archive_cert_with_dict, handle_batch_verify_cert,
    handle_batch_verify_cert_archive, handle_compress_cert, handle_decompress_cert,
    handle_train_dict, handle_unarchive_cert, handle_unarchive_cert_with_dict, handle_verify_cert,
    handle_verify_cert_archive, ArchiveCertParams, ArchiveCertResult, ArchiveCertWithDictParams,
    ArchiveCertWithDictResult, BatchVerifyCertArchiveItem, BatchVerifyCertArchiveParams,
    BatchVerifyCertItem, BatchVerifyCertItemResult, BatchVerifyCertParams, BatchVerifyCertResult,
    BatchVerifyCertStats, CompressCertParams, CompressCertResult, CompressCertStats,
    DecompressCertParams, DecompressCertResult, TrainDictParams, TrainDictResult,
    UnarchiveCertParams, UnarchiveCertResult, UnarchiveCertWithDictParams,
    UnarchiveCertWithDictResult, VerifyCertArchiveParams, VerifyCertParams, VerifyCertResult,
};

// Re-export external certificate handlers and types
pub use external_cert::{
    handle_verify_certificates_batch, handle_verify_entailment_certificate,
    handle_verify_farkas_certificate, BatchExternalCertItem, BatchExternalCertItemResult,
    BatchExternalCertStats, BatchVerifyExternalCertParams, BatchVerifyExternalCertResult,
    VerifyEntailmentCertResult, VerifyExternalCertParams, VerifyFarkasCertResult,
};
pub use external_cert_alethe::{handle_verify_alethe_certificate, VerifyAletheCertResult};

// Re-export tactic module types and handlers
pub use tactic::{
    handle_apply_tactic, handle_batch_apply_tactic, handle_close_proof_state,
    handle_explain_failure, handle_extract_proof, handle_get_proof_state, handle_init_proof_state,
    handle_open_obligation, handle_retain_proof_state, handle_search_tactics,
    handle_search_theorems, ApplyTacticParams, BatchApplyTacticParams, BatchApplyTacticResult,
    BatchTacticItem, BatchTacticItemResult, BatchTacticStats, CloseProofStateParams,
    CloseProofStateResult, ExplainFailureParams, ExplainFailureResult, ExtractProofParams,
    ExtractProofResult, FailureBlocker, GetProofStateParams, InitProofStateParams,
    InitProofStateResult, OpenObligationParams, ProofStateGoalSearchParams, ProofVerification,
    RetainProofStateParams, RetainProofStateResult, SearchTacticsResult, SearchTheoremsResult,
};

// Re-export TLA+ handler types and functions
pub use tla_handler::{
    handle_batch_prove_tla, handle_prove_tla, BatchProveTlaItem, BatchProveTlaItemResult,
    BatchProveTlaParams, BatchProveTlaResult, BatchProveTlaStats, ProveTlaParams, ProveTlaResult,
};

// Re-export premise selection types and handlers
pub use premise::{
    handle_batch_get_premises, handle_get_premises, BatchGetPremisesItem,
    BatchGetPremisesItemResult, BatchGetPremisesParams, BatchGetPremisesResult,
    BatchGetPremisesStats, GetPremisesParams, GetPremisesResult, PremiseInfo,
    PremiseSelectionStats,
};

// Re-export search proof types and handler (Part of #3177)
pub use search_proof::{
    handle_search_proof, SearchProofParams, SearchProofResult, SearchStats, SearchStrategy,
    StrategyTiming,
};

// Re-export swarm worker addDecl handler and types (C1 Task C)
pub use swarm::{handle_add_decl, AddDeclParams, AddDeclResult, AddDeclVerdict};

// Re-export widget types and handlers (Part of #1193)
pub use widget::{
    handle_get_widget_source, handle_get_widgets, handle_widget_event, GetWidgetSourceParams,
    GetWidgetSourceResult, GetWidgetsParams, GetWidgetsResult, WidgetEventParams,
    WidgetEventResult, WidgetInstance,
};

// Re-export dependencies used by tests (were in scope when handlers was a single file)
#[cfg(test)]
pub(crate) use crate::progress::ProgressSender;
#[cfg(test)]
pub(crate) use crate::rpc::RequestId;
#[cfg(test)]
pub(crate) use std::time::Duration;

// Re-export parse_lean_file for tests
#[cfg(test)]
pub(crate) use verify::parse_lean_file;

#[cfg(test)]
mod tests;
