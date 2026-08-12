// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Centralized JSON-RPC method dispatch.
//!
//! Both TCP ([`crate::serve`]) and WebSocket ([`crate::websocket::serve_websocket`])
//! transports delegate to [`dispatch_request`], eliminating the duplicated match
//! arms that previously existed in `lib.rs` and `websocket.rs` (Part of #1742).

use crate::handlers::{
    handle_add_decl, handle_apply_tactic, handle_archive_cert, handle_archive_cert_with_dict,
    handle_batch_apply_tactic, handle_batch_check, handle_batch_get_premises,
    handle_batch_prove_tla, handle_batch_verify_cert, handle_batch_verify_cert_archive,
    handle_check, handle_close_proof_state, handle_compose_proof, handle_compress_cert,
    handle_decompress_cert, handle_explain_failure, handle_extract_proof, handle_fill_sorries,
    handle_get_cache_metrics, handle_get_config, handle_get_environment, handle_get_metrics,
    handle_get_premises, handle_get_proof_state, handle_get_type, handle_get_widget_source,
    handle_get_widgets, handle_import_module, handle_init_proof_state, handle_load_environment,
    handle_open_obligation, handle_prove, handle_prove_tla, handle_retain_proof_state,
    handle_save_environment, handle_search_proof, handle_search_tactics, handle_search_theorems,
    handle_server_info, handle_train_dict, handle_unarchive_cert, handle_unarchive_cert_with_dict,
    handle_verify_alethe_certificate, handle_verify_c, handle_verify_cert,
    handle_verify_cert_archive, handle_verify_certificates_batch,
    handle_verify_entailment_certificate, handle_verify_farkas_certificate, handle_verify_file,
    handle_verify_proof, handle_verify_proof_batch, handle_widget_event, ServerState,
};
use crate::progress::ProgressSender;
use crate::rpc::{RequestId, Response, RpcError};
use crate::rpc_goals::{
    handle_get_interactive_diagnostics, handle_get_interactive_goals, handle_get_plain_goal,
    GetInteractiveDiagnosticsParams, PlainGoalParams,
};
use serde_json::Map;

/// Dispatch a JSON-RPC request to the appropriate handler.
///
/// This is the single dispatch function used by both TCP and WebSocket
/// transports. The `progress` parameter is `None` for TCP (no streaming)
/// and `Some(sender)` for WebSocket requests that support progress.
pub(crate) async fn dispatch_request(
    method: &str,
    params: Option<serde_json::Value>,
    id: RequestId,
    state: &ServerState,
    progress: Option<ProgressSender>,
) -> Response {
    match method {
        "check" => match parse_params::<crate::handlers::CheckParams>(params) {
            Ok(p) => handle_check(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "prove" => match parse_params::<crate::handlers::ProveParams>(params) {
            Ok(p) => handle_prove(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "proveTLA" => match parse_params::<crate::handlers::ProveTlaParams>(params) {
            Ok(p) => handle_prove_tla(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "batchProveTLA" => match parse_params::<crate::handlers::BatchProveTlaParams>(params) {
            Ok(p) => handle_batch_prove_tla(state, id, p, progress).await,
            Err(e) => Response::error(id, e),
        },
        "getType" => match parse_params::<crate::handlers::GetTypeParams>(params) {
            Ok(p) => handle_get_type(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "getPremises" => match parse_params::<crate::handlers::GetPremisesParams>(params) {
            Ok(p) => handle_get_premises(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "batchGetPremises" => {
            match parse_params::<crate::handlers::BatchGetPremisesParams>(params) {
                Ok(p) => handle_batch_get_premises(state, id, p, progress).await,
                Err(e) => Response::error(id, e),
            }
        }
        "batchCheck" => match parse_params::<crate::handlers::BatchCheckParams>(params) {
            Ok(p) => handle_batch_check(state, id, p, progress).await,
            Err(e) => Response::error(id, e),
        },
        "verifyCert" => match parse_params::<crate::handlers::VerifyCertParams>(params) {
            Ok(p) => handle_verify_cert(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        // Canonical snake_case methods for external certificate verification.
        // These are the names advertised in serverInfo.
        "verify_farkas_certificate" => {
            match parse_params::<crate::handlers::VerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_farkas_certificate(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "verify_entailment_certificate" => {
            match parse_params::<crate::handlers::VerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_entailment_certificate(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "verify_alethe_certificate" => {
            match parse_params::<crate::handlers::VerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_alethe_certificate(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "verify_certificates_batch" => {
            match parse_params::<crate::handlers::BatchVerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_certificates_batch(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        // camelCase alias methods for external certificate verification (Part of #894)
        "verifyAletheCertificate" => {
            match parse_params::<crate::handlers::VerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_alethe_certificate(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "verifyFarkasCertificate" => {
            match parse_params::<crate::handlers::VerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_farkas_certificate(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "verifyEntailmentCertificate" => {
            match parse_params::<crate::handlers::VerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_entailment_certificate(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "verifyCertificatesBatch" | "batchVerifyExternalCert" => {
            match parse_params::<crate::handlers::BatchVerifyExternalCertParams>(params) {
                Ok(p) => handle_verify_certificates_batch(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "batchVerifyCert" => match parse_params::<crate::handlers::BatchVerifyCertParams>(params) {
            Ok(p) => handle_batch_verify_cert(state, id, p, progress).await,
            Err(e) => Response::error(id, e),
        },
        "verifyCertArchive" => {
            match parse_params::<crate::handlers::VerifyCertArchiveParams>(params) {
                Ok(p) => handle_verify_cert_archive(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "batchVerifyCertArchive" => {
            match parse_params::<crate::handlers::BatchVerifyCertArchiveParams>(params) {
                Ok(p) => handle_batch_verify_cert_archive(state, id, p, progress).await,
                Err(e) => Response::error(id, e),
            }
        }
        "compressCert" => match parse_params::<crate::handlers::CompressCertParams>(params) {
            Ok(p) => handle_compress_cert(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "decompressCert" => match parse_params::<crate::handlers::DecompressCertParams>(params) {
            Ok(p) => handle_decompress_cert(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "archiveCert" => match parse_params::<crate::handlers::ArchiveCertParams>(params) {
            Ok(p) => handle_archive_cert(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "unarchiveCert" => match parse_params::<crate::handlers::UnarchiveCertParams>(params) {
            Ok(p) => handle_unarchive_cert(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "trainDict" => match parse_params::<crate::handlers::TrainDictParams>(params) {
            Ok(p) => handle_train_dict(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "archiveCertWithDict" => {
            match parse_params::<crate::handlers::ArchiveCertWithDictParams>(params) {
                Ok(p) => handle_archive_cert_with_dict(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "unarchiveCertWithDict" => {
            match parse_params::<crate::handlers::UnarchiveCertWithDictParams>(params) {
                Ok(p) => handle_unarchive_cert_with_dict(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "serverInfo" => handle_server_info(state, id).await,
        "saveEnvironment" => match parse_params::<crate::handlers::SaveEnvironmentParams>(params) {
            Ok(p) => handle_save_environment(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "loadEnvironment" => match parse_params::<crate::handlers::LoadEnvironmentParams>(params) {
            Ok(p) => handle_load_environment(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "importModule" => match parse_params::<crate::handlers::ImportModuleParams>(params) {
            Ok(p) => handle_import_module(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        // Swarm worker declaration submission (C1 Task C). Session-scoped:
        // routes through the kernel-recheck verdict and lands an accepted decl
        // in the session overlay.
        "addDecl" => match parse_params::<crate::handlers::AddDeclParams>(params) {
            Ok(p) => handle_add_decl(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "getEnvironment" => match parse_params::<crate::handlers::GetEnvironmentParams>(params) {
            Ok(p) => handle_get_environment(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "verifyC" => match parse_params::<crate::handlers::VerifyCParams>(params) {
            Ok(p) => handle_verify_c(state, id, p, progress).await,
            Err(e) => Response::error(id, e),
        },
        "getConfig" => handle_get_config(state, id).await,
        "getMetrics" => handle_get_metrics(state, id).await,
        "getCacheMetrics" => handle_get_cache_metrics(state, id).await,
        // LLM Integration API (Proof State Management)
        "initProofState" => match parse_params::<crate::handlers::InitProofStateParams>(params) {
            Ok(p) => handle_init_proof_state(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "proofState.openObligation" => {
            match parse_params::<crate::handlers::OpenObligationParams>(params) {
                Ok(p) => handle_open_obligation(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "applyTactic" => match parse_params::<crate::handlers::ApplyTacticParams>(params) {
            Ok(p) => handle_apply_tactic(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "getProofState" => match parse_params::<crate::handlers::GetProofStateParams>(params) {
            Ok(p) => handle_get_proof_state(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "proofState.searchTheorems" => {
            match parse_params::<crate::handlers::ProofStateGoalSearchParams>(params) {
                Ok(p) => handle_search_theorems(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "proofState.searchTactics" => {
            match parse_params::<crate::handlers::ProofStateGoalSearchParams>(params) {
                Ok(p) => handle_search_tactics(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "proofState.close" => {
            match parse_params::<crate::handlers::CloseProofStateParams>(params) {
                Ok(p) => handle_close_proof_state(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "proofState.retain" => {
            match parse_params::<crate::handlers::RetainProofStateParams>(params) {
                Ok(p) => handle_retain_proof_state(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "proofState.explainFailure" => {
            match parse_params::<crate::handlers::ExplainFailureParams>(params) {
                Ok(p) => handle_explain_failure(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "extractProof" => match parse_params::<crate::handlers::ExtractProofParams>(params) {
            Ok(p) => handle_extract_proof(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "batchApplyTactic" => {
            match parse_params::<crate::handlers::BatchApplyTacticParams>(params) {
                Ok(p) => handle_batch_apply_tactic(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        // LLM Integration API - Complete Proof Verification (#79)
        "verifyProof" => match parse_params::<crate::handlers::VerifyProofParams>(params) {
            Ok(p) => handle_verify_proof(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        // LLM Integration API - Batch Proof Verification (#89)
        "verifyProofBatch" => {
            match parse_params::<crate::handlers::VerifyProofBatchParams>(params) {
                Ok(p) => handle_verify_proof_batch(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        // LLM Integration API - Full File Verification (#91)
        "verifyFile" => match parse_params::<crate::handlers::VerifyFileParams>(params) {
            Ok(p) => handle_verify_file(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "fillSorries" => match parse_params::<crate::handlers::FillSorriesParams>(params) {
            Ok(p) => handle_fill_sorries(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "composeProof" => match parse_params::<crate::handlers::ComposeProofParams>(params) {
            Ok(p) => handle_compose_proof(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        // Lean 4 editor infoview compatibility endpoints (Part of #1245)
        "Lean.Widget.getInteractiveDiagnostics" => {
            match parse_params::<GetInteractiveDiagnosticsParams>(params) {
                Ok(p) => handle_get_interactive_diagnostics(state, id, p).await,
                Err(e) => Response::error(id, e),
            }
        }
        "Lean.Widget.getInteractiveGoals" => match parse_params::<PlainGoalParams>(params) {
            Ok(p) => handle_get_interactive_goals(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "getPlainGoal" => match parse_params::<PlainGoalParams>(params) {
            Ok(p) => handle_get_plain_goal(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        // LLM Integration API - Full Proof Search (#3177)
        "searchProof" => match parse_params::<crate::handlers::SearchProofParams>(params) {
            Ok(p) => handle_search_proof(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        // Widget RPC endpoints for infoview parity (Part of #1193)
        "getWidgets" => match parse_params::<crate::handlers::GetWidgetsParams>(params) {
            Ok(p) => handle_get_widgets(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "getWidgetSource" => match parse_params::<crate::handlers::GetWidgetSourceParams>(params) {
            Ok(p) => handle_get_widget_source(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        "Widget_event" => match parse_params::<crate::handlers::WidgetEventParams>(params) {
            Ok(p) => handle_widget_event(state, id, p).await,
            Err(e) => Response::error(id, e),
        },
        _ => Response::error(id, RpcError::method_not_found(method)),
    }
}

/// Parse JSON-RPC request parameters into a typed struct.
pub(crate) fn parse_params<T: serde::de::DeserializeOwned>(
    params: Option<serde_json::Value>,
) -> Result<T, RpcError> {
    match params {
        Some(v) => serde_json::from_value(v)
            .map_err(|e| RpcError::invalid_params(format!("Invalid parameters: {e}"))),
        None => serde_json::from_value(serde_json::Value::Object(Map::default()))
            .map_err(|e| RpcError::invalid_params(format!("Missing required parameters: {e}"))),
    }
}
