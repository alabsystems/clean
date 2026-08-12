// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Server administration handlers: info, config, metrics, environment management.

use super::state::ServerState;
use super::types::*;
use crate::rpc::{RequestId, Response, RpcError};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::name::NameInterner;
use clean_kernel::Environment;
use std::sync::atomic::Ordering;
use tracing::instrument;

/// Handle the "serverInfo" method
pub async fn handle_server_info(state: &ServerState, id: RequestId) -> Response {
    // Build per-method contract metadata from the registry (Part of #2515)
    let method_contracts: Vec<MethodContractInfo> = crate::registry::all_method_contracts()
        .into_iter()
        .map(|(name, oc)| {
            let has_outcome = oc.top_level_field.is_some() || oc.item_field.is_some();
            MethodContractInfo {
                name: name.to_string(),
                outcome_field: oc.top_level_field.map(|s| s.to_string()),
                item_outcome_field: oc.item_field.map(|s| s.to_string()),
                preferred_outcome_field: if has_outcome {
                    Some("verified".to_string())
                } else {
                    None
                },
            }
        })
        .collect();

    let info = ServerInfo {
        name: "clean-server".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        lean_toolchain_version: state.lean_toolchain_version().map(ToOwned::to_owned),
        // Use centralized registry as single source of truth for method names
        methods: crate::registry::all_method_names(),
        gpu_available: state.gpu_enabled,
        method_contracts,
    };

    Response::success_typed(id.clone(), &info)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle the "getConfig" method
///
/// Returns current server configuration including thread settings.
#[instrument(skip(state))]
pub async fn handle_get_config(state: &ServerState, id: RequestId) -> Response {
    // Determine effective thread count
    let effective_threads = if state.worker_threads > 0 {
        state.worker_threads
    } else {
        rayon::current_num_threads()
    };

    let result = GetConfigResult {
        gpu_enabled: state.gpu_enabled,
        default_timeout_ms: state.default_timeout_ms,
        worker_threads: state.worker_threads,
        effective_threads,
        lean_toolchain_version: state.lean_toolchain_version().map(ToOwned::to_owned),
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle the "getMetrics" method
///
/// Returns server-wide runtime metrics for monitoring and optimization.
/// Useful for AI agents to track server health and performance.
#[instrument(skip(state))]
pub async fn handle_get_metrics(state: &ServerState, id: RequestId) -> Response {
    let metrics = &state.metrics;

    let avg_us = metrics.avg_latency_us();
    let handler_us = metrics.cumulative_time_us.load(Ordering::Relaxed);
    let tc_us = metrics.type_check_time_us.load(Ordering::Relaxed);
    let cv_us = metrics.cert_verify_time_us.load(Ordering::Relaxed);

    let result = GetMetricsResult {
        uptime_secs: metrics.uptime_secs(),
        total_requests: metrics.total_requests.load(Ordering::Relaxed),
        successful_requests: metrics.successful_requests.load(Ordering::Relaxed),
        failed_requests: metrics.failed_requests.load(Ordering::Relaxed),
        success_rate: metrics.success_rate(),
        avg_latency_us: avg_us,
        avg_latency_ns: Some(ns_from_us(avg_us)),
        requests_per_second: metrics.requests_per_second(),
        method_counts: MethodCounts {
            check: metrics.check_requests.load(Ordering::Relaxed),
            prove: metrics.prove_requests.load(Ordering::Relaxed),
            get_type: metrics.get_type_requests.load(Ordering::Relaxed),
            batch_check: metrics.batch_check_requests.load(Ordering::Relaxed),
            verify_cert: metrics.verify_cert_requests.load(Ordering::Relaxed),
            batch_verify_cert: metrics.batch_verify_cert_requests.load(Ordering::Relaxed),
            verify_cert_archive: metrics.verify_cert_archive_requests.load(Ordering::Relaxed),
            batch_verify_cert_archive: metrics
                .batch_verify_cert_archive_requests
                .load(Ordering::Relaxed),
            verify_c: metrics.verify_c_requests.load(Ordering::Relaxed),
        },
        batch_stats: BatchStats {
            items_processed: metrics.batch_items_processed.load(Ordering::Relaxed),
            certificates_verified: metrics.certificates_verified.load(Ordering::Relaxed),
        },
        timing: TimingStats {
            cumulative_handler_time_us: handler_us,
            cumulative_handler_time_ns: Some(ns_from_us(handler_us)),
            type_check_time_us: tc_us,
            type_check_time_ns: Some(ns_from_us(tc_us)),
            cert_verify_time_us: cv_us,
            cert_verify_time_ns: Some(ns_from_us(cv_us)),
        },
        name_interner_entries: NameInterner::global().len() as u64,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle the "getCacheMetrics" method
///
/// Returns cache statistics for type checking and proof state caches.
#[instrument(skip(state))]
pub async fn handle_get_cache_metrics(state: &ServerState, id: RequestId) -> Response {
    let cache_metrics = &state.cache_metrics;
    state.proof_cache.evict_expired();

    let type_cache_enabled = cache_metrics.type_cache_enabled.load(Ordering::Relaxed) != 0;
    let type_cache = if type_cache_enabled {
        let hits = cache_metrics.type_cache_hits.load(Ordering::Relaxed);
        let misses = cache_metrics.type_cache_misses.load(Ordering::Relaxed);
        let entries = cache_metrics.type_cache_entries.load(Ordering::Relaxed);
        let total = hits + misses;
        let hit_rate = if total == 0 {
            0.0
        } else {
            (hits as f64 / total as f64) * 100.0
        };
        Some(TypeCacheMetrics {
            hits,
            misses,
            entries,
            hit_rate,
        })
    } else {
        None
    };

    let result = GetCacheMetricsResult {
        type_cache,
        def_eq_cache_enabled: true,
        whnf_cache_entries: cache_metrics.whnf_cache_entries.load(Ordering::Relaxed),
        def_eq_cache_entries: cache_metrics.def_eq_cache_entries.load(Ordering::Relaxed),
        proof_state_cache_entries: state.proof_cache.len() as u64,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle the "saveEnvironment" method
#[instrument(skip(state))]
pub async fn handle_save_environment(
    state: &ServerState,
    id: RequestId,
    params: SaveEnvironmentParams,
) -> Response {
    let env = state.env.read().await;
    let path = std::path::Path::new(&params.path);
    let format = params.format.as_deref().unwrap_or("bincode");

    let result = match format {
        "json" => {
            let json = env.to_json_pretty().map_err(|e| e.to_string());
            match json {
                Ok(data) => std::fs::write(path, data.as_bytes()).map_err(|e| e.to_string()),
                Err(e) => Err(e),
            }
        }
        _ => env.save_to_file(path).map_err(|e| e.to_string()),
    };

    match result {
        Ok(_) => {
            let file_size = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
            let save_result = SaveEnvironmentResult {
                success: true,
                num_constants: env.num_constants(),
                num_inductives: env.num_inductives(),
                file_size,
            };
            Response::success_typed(id.clone(), &save_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(id, RpcError::internal_error(format!("Failed to save: {e}"))),
    }
}

/// Handle the "loadEnvironment" method
#[instrument(skip(state))]
pub async fn handle_load_environment(
    state: &ServerState,
    id: RequestId,
    params: LoadEnvironmentParams,
) -> Response {
    let path = std::path::Path::new(&params.path);
    let format = params.format.as_deref().unwrap_or("bincode");

    let loaded_env = match format {
        "json" => {
            let data = std::fs::read_to_string(path).map_err(|e| e.to_string());
            match data {
                Ok(json) => Environment::from_json(&json).map_err(|e| e.to_string()),
                Err(e) => Err(e),
            }
        }
        _ => Environment::load_from_file(path).map_err(|e| e.to_string()),
    };

    match loaded_env {
        Ok(new_env) => {
            let num_constants = new_env.num_constants();
            let num_inductives = new_env.num_inductives();

            // Update the shared environment
            let mut env = state.env.write().await;
            if params.replace {
                *env = new_env;
            } else {
                // Merge: register inductives/constructors/recursors first (they
                // create their own constants entries), then add remaining constants.
                // For .olean-based merging with dependency resolution, use importModule.
                for ind in new_env.inductives() {
                    if env.get_const(&ind.name).is_none() {
                        env.register_inductive(ind.clone());
                    }
                }
                for ctor in new_env.constructors() {
                    if env.get_const(&ctor.name).is_none() {
                        env.register_constructor(ctor.clone());
                    }
                }
                for rec in new_env.recursors() {
                    if env.get_const(&rec.name).is_none() {
                        env.register_recursor(rec.clone());
                    }
                }
                // Add remaining constants (definitions, axioms, theorems, opaques)
                // that weren't already added as part of inductive registration.
                // Use ConstantKind to correctly reconstruct the Declaration variant.
                for ci in new_env.constants() {
                    if env.get_const(&ci.name).is_none() {
                        let decl = match ci.kind {
                            clean_kernel::ConstantKind::Theorem => {
                                clean_kernel::Declaration::Theorem {
                                    name: ci.name.clone(),
                                    level_params: ci.level_params.clone(),
                                    type_: ci.type_.clone(),
                                    value: ci.value.clone().unwrap_or_else(|| ci.type_.clone()),
                                }
                            }
                            clean_kernel::ConstantKind::Opaque => {
                                clean_kernel::Declaration::Opaque {
                                    name: ci.name.clone(),
                                    level_params: ci.level_params.clone(),
                                    type_: ci.type_.clone(),
                                    value: ci.value.clone().unwrap_or_else(|| ci.type_.clone()),
                                }
                            }
                            clean_kernel::ConstantKind::Axiom => clean_kernel::Declaration::Axiom {
                                name: ci.name.clone(),
                                level_params: ci.level_params.clone(),
                                type_: ci.type_.clone(),
                            },
                            clean_kernel::ConstantKind::Definition => {
                                let Some(value) = ci.value.clone() else {
                                    return Response::error(
                                        id,
                                        RpcError::internal_error(format!(
                                            "Cannot load value-less definition {}",
                                            ci.name
                                        )),
                                    );
                                };
                                clean_kernel::Declaration::Definition {
                                    name: ci.name.clone(),
                                    level_params: ci.level_params.clone(),
                                    type_: ci.type_.clone(),
                                    value,
                                    is_reducible: ci.is_reducible,
                                }
                            }
                        };
                        // Re-check imported constants before making them visible in
                        // the server environment.  Uncheckable serialized constants
                        // fail closed instead of entering via a trusted insertion path.
                        if let Err(e) = env.add_decl(decl) {
                            return Response::error(
                                id,
                                RpcError::internal_error(format!(
                                    "Kernel validation failed for {}: {e}",
                                    ci.name
                                )),
                            );
                        }
                    }
                }
            }

            let load_result = LoadEnvironmentResult {
                success: true,
                num_constants,
                num_inductives,
            };
            Response::success_typed(id.clone(), &load_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(id, RpcError::internal_error(format!("Failed to load: {e}"))),
    }
}

/// Handle the "importModule" method — loads .olean files by module name
#[instrument(skip(state))]
pub async fn handle_import_module(
    state: &ServerState,
    id: RequestId,
    params: ImportModuleParams,
) -> Response {
    let module_name = params.module.clone();
    let extra_paths: Vec<std::path::PathBuf> = params
        .search_paths
        .iter()
        .map(std::path::PathBuf::from)
        .collect();

    // Clone the current environment so we can load .olean data into it,
    // preserving any existing declarations while adding new ones
    let current_env = {
        let env = state.env.read().await;
        env.clone()
    };

    // Use server-level cache so repeated imports of overlapping module hierarchies
    // don't re-parse the same .olean files.
    let cache = state.olean_cache.clone();

    // Run the blocking .olean load in a spawn_blocking to avoid blocking the async runtime
    let result = tokio::task::spawn_blocking(move || {
        let mut search_paths = clean_olean::default_search_paths();
        search_paths.extend(extra_paths);

        let mut env = current_env;
        clean_olean::load_module_with_deps_cached(&mut env, &module_name, &search_paths, &cache)
            .map(|summaries| (env, summaries))
    })
    .await;

    match result {
        Ok(Ok((new_env, summaries))) => {
            let modules_loaded: Vec<String> = summaries
                .iter()
                .filter_map(|s| s.module_name.clone())
                .collect();
            let constants_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let constants_skipped: usize = summaries.iter().map(|s| s.duplicate_constants).sum();

            // Swap in the updated environment
            let mut env = state.env.write().await;
            *env = new_env;

            tracing::info!(
                "importModule: loaded {} modules, {} constants added, {} skipped",
                modules_loaded.len(),
                constants_added,
                constants_skipped,
            );

            let import_result = ImportModuleResult {
                success: true,
                modules_loaded,
                constants_added,
                constants_skipped,
            };
            Response::success_typed(id.clone(), &import_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Ok(Err(e)) => Response::error(
            id,
            RpcError::internal_error(format!("Failed to import module: {e}")),
        ),
        Err(e) => Response::error(
            id,
            RpcError::internal_error(format!("Import task failed: {e}")),
        ),
    }
}

/// Handle the "getEnvironment" method
#[instrument(skip(state))]
pub async fn handle_get_environment(
    state: &ServerState,
    id: RequestId,
    params: GetEnvironmentParams,
) -> Response {
    let env = state.env.read().await;

    let constant_names: Vec<String> = env
        .constants()
        .take(100)
        .map(|c| c.name.to_string())
        .collect();

    let json = if params.include_json {
        env.to_json_pretty().ok()
    } else {
        None
    };

    let result = GetEnvironmentResult {
        num_constants: env.num_constants(),
        num_inductives: env.num_inductives(),
        constant_names,
        json,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}
