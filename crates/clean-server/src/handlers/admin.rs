// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Server administration handlers: info, config, metrics, environment management.

use super::core::answer_with_env;
use super::off_runtime::OffRuntime;
use super::save_file::{save_file, Commit};
use super::state::ServerState;
use super::types::*;
use super::work::{within, WorkError, WorkPool};
use crate::rpc::{RequestId, Response, RpcError};
use crate::trust_boundary::{
    check_import_token, check_module_name, check_replace_token, confine, ModuleSearch,
};
use clean_kernel::name::NameInterner;
use clean_kernel::Environment;
use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::OwnedRwLockReadGuard;
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
        destructive_methods: crate::registry::destructive_methods()
            .into_iter()
            .map(str::to_string)
            .collect(),
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
        work_in_use: state.work.in_use() as u64,
        work_limit: state.work.limit() as u64,
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
///
/// Encoding and writing the environment grows with the environment, so it is
/// work on the pool under the request's deadline. The encoding holds the
/// environment for reading; the file is written after the hold is let go
/// ([`save_environment_answer`]), whole or not at all (`save_file.rs`). The
/// encoding reads no deadline, but the save reads it before it writes and
/// before it commits, and commits only if its request has not stopped waiting
/// ([`save_until`]): a save whose request answered the timeout error leaves a
/// regular file as it was (or, at a path where nothing was, through symbolic
/// links or not, creates nothing), and one that answered success replaced or
/// created it (a named pipe it was writing is written to its end). Like
/// `loadEnvironment`, it gets ten times the server's default timeout.
#[instrument(skip(state, params))]
pub async fn handle_save_environment(
    state: &ServerState,
    id: RequestId,
    params: SaveEnvironmentParams,
) -> Response {
    let timeout = Duration::from_millis(
        params
            .timeout_ms
            .unwrap_or(state.default_timeout_ms.saturating_mul(10)),
    );
    save_until(state, id, params, timeout, tokio::time::sleep(timeout)).await
}

/// `saveEnvironment` inside `timeout`, whose end is `timer` (the request's
/// own timer; a test's, to order it against the save).
///
/// The save and the request decide once whether the save commits
/// (`save_file::Commit`). When the timer fires first, a save that has not
/// begun replacing its file never will, and the request answers the timeout
/// error; one that has is waited for, and the request answers what became of
/// the file. A `within` timeout dropped the save's answer instead, so a save
/// that renamed just before its request's timer fired was answered with the
/// timeout error (review of 2026-10-18). A request cancelled before the save
/// commits (its future dropped) abandons it too.
pub(crate) async fn save_until(
    state: &ServerState,
    id: RequestId,
    params: SaveEnvironmentParams,
    timeout: Duration,
    timer: impl std::future::Future<Output = ()>,
) -> Response {
    /// Abandons the save when the request lets go of it, answered or not: a
    /// save that has committed or ended is not changed by it.
    struct AbandonOnDrop(Arc<Commit>);
    impl Drop for AbandonOnDrop {
        fn drop(&mut self) {
            let _ = self.0.abandon();
        }
    }

    let start = Instant::now();
    let deadline = start.checked_add(timeout);
    let answering = id.clone();
    let commit = Arc::new(Commit::default());
    let deciding = Arc::clone(&commit);
    let _cancelled = AbandonOnDrop(Arc::clone(&commit));
    let root = state.workspace_root().map(Path::to_path_buf);
    let work = async {
        // The pool's lock order (`work.rs`): a slot, then the environment.
        let slot = state.work.slot().await?;
        let held = state.env.read_owned().await;
        WorkPool::run_in(slot, deadline, move || {
            save_environment_answer(answering, held, &params, root.as_deref(), &deciding)
        })
        .await
    };
    tokio::pin!(work);
    tokio::pin!(timer);
    let saved = tokio::select! {
        biased;
        saved = &mut work => saved,
        () = &mut timer => {
            if commit.abandon() {
                Err(WorkError::Interrupted)
            } else {
                // The save has begun replacing the file: its answer says how
                // that ended (a rename and a directory flush; never a pipe,
                // which is written in place and takes no commit).
                work.await
            }
        }
    };
    match saved {
        Ok(response) => response,
        Err(error) => Response::error(id, error.into_rpc_error(timeout)),
    }
}

/// `saveEnvironment`'s work, on the pool: refuse a path outside `root`
/// (`trust_boundary::confine`) before anything is encoded or written, encode
/// `held`, let the hold go, then write the file.
///
/// The encoding is all the save reads. A write can block for as long as its
/// path makes it (a pipe nobody reads, a stalled disk), past the request's
/// timeout; holding the environment meanwhile kept a writer queued behind the
/// hold waiting, and, the lock being write-preferring, every reader queued
/// behind that writer (review of 2026-10-16: a save to a pipe past its timeout
/// made `check` and `getEnvironment` answer their timeout errors).
fn save_environment_answer(
    id: RequestId,
    held: OwnedRwLockReadGuard<Environment>,
    params: &SaveEnvironmentParams,
    root: Option<&Path>,
    commit: &Commit,
) -> Response {
    let confined = match confine("saveEnvironment", "path", &params.path, root) {
        Ok(confined) => confined,
        Err(error) => return Response::error(id, error),
    };
    let path = confined.as_path();
    let format = params.format.as_deref().unwrap_or("bincode");

    let encoded = match format {
        "json" => held
            .to_json_pretty()
            .map(String::into_bytes)
            .map_err(|e| e.to_string()),
        _ => held.to_bincode().map_err(|e| e.to_string()),
    };
    let (num_constants, num_inductives) = (held.num_constants(), held.num_inductives());
    drop(held);
    // A save interrupted at its deadline latched it: the work's `run_until`
    // drops this answer, and the request answers its timeout error. One its
    // request abandoned is answered by nobody: the request has answered.
    let result = encoded.and_then(|data| save_file(path, &data, commit).map_err(|e| e.to_string()));

    match result {
        Ok(()) => {
            let file_size = std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
            let save_result = SaveEnvironmentResult {
                success: true,
                num_constants,
                num_inductives,
                file_size,
            };
            Response::success_typed(id.clone(), &save_result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        Err(e) => Response::error(id, RpcError::internal_error(format!("Failed to save: {e}"))),
    }
}

/// Handle the "loadEnvironment" method
#[instrument(skip(state, params))]
pub async fn handle_load_environment(
    state: &ServerState,
    id: RequestId,
    params: LoadEnvironmentParams,
) -> Response {
    // Pure request validation, before any file I/O: the acknowledgement flag
    // is meaningless outside replace mode, and silently ignoring it would let
    // a caller believe the merge path can skip re-checking (it never does).
    if params.replace_unchecked && !params.replace {
        return Response::error(
            id,
            RpcError::invalid_params(
                "replace_unchecked only applies to replace mode (replace: true); \
                 the merge path always re-checks every loaded declaration",
            ),
        );
    }
    // A request whose effect later verdicts rest on without a kernel check
    // carries the launch token itself (`trust_boundary.rs`); `importModule`
    // is the other.
    if params.replace_unchecked {
        if let Err(error) = check_replace_token(state.launch_token(), params.token.as_deref()) {
            return Response::error(id, error);
        }
    }

    let start = Instant::now();
    // A merge re-checks every declaration it loads, so it gets a batch's
    // default: ten times the server's.
    let timeout = Duration::from_millis(
        params
            .timeout_ms
            .unwrap_or(state.default_timeout_ms.saturating_mul(10)),
    );
    let deadline = start.checked_add(timeout);
    let path = params.path.clone();
    let format = params
        .format
        .clone()
        .unwrap_or_else(|| "bincode".to_string());
    let (replace, replace_unchecked) = (params.replace, params.replace_unchecked);
    let root = state.workspace_root().map(Path::to_path_buf);

    let outcome = within(timeout, async {
        // Confining the path and reading and decoding the file are work on
        // the pool, holding nothing. What it read is freed off the runtime
        // wherever it is let go: after the merge, or when the request is
        // cancelled (`off_runtime.rs`).
        let loaded = state
            .work
            .run(deadline, move || {
                let confined = confine("loadEnvironment", "path", &path, root.as_deref())?;
                read_environment(&confined, &format)
                    .map(OffRuntime::new)
                    .map_err(|e| RpcError::internal_error(format!("Failed to load: {e}")))
            })
            .await?;
        let new_env = match loaded {
            Ok(new_env) => new_env,
            Err(error) => return Ok(Err(error)),
        };
        let load_result = LoadEnvironmentResult {
            success: true,
            num_constants: new_env.num_constants(),
            num_inductives: new_env.num_inductives(),
        };

        if replace {
            // Wholesale install of a deserialized environment: the loaded
            // declarations carry NO provenance stamps
            // (`declaration_verification` is `#[serde(skip)]`) and are NOT
            // re-checked here. That door stays open only behind an explicit
            // opt-in whose name says what it skips; it is ledgered as a
            // structural door in data/env_bypass_census.json (row
            // `env-serde-load`, disposition R1-SRV) with this flag as its
            // guard.
            if !replace_unchecked {
                return Ok(Err(RpcError::internal_error(
                    "loadEnvironment replace mode installs a deserialized \
                     environment wholesale, without kernel re-checking of the \
                     loaded declarations. Pass replace_unchecked: true to accept \
                     that explicitly, or use replace: false for the checked \
                     merge path.",
                )));
            }
            // In the writers' turn: no merge or import is computing on a copy
            // this would make stale.
            state.env.replace(new_env.into_inner()).await;
        } else {
            // Merge mode: every loaded declaration is re-earned through the
            // kernel's checked admission paths — inductive families through
            // the full `add_inductive` replay, plain constants through
            // `add_decl` (see `env_merge`). That is kernel work on the pool
            // under the request's deadline, on a copy of the live environment
            // made under a read hold that is let go before the work runs, so
            // requests that read the environment are served while it merges.
            // The write lock is taken only to publish the merged copy, and
            // the copy is published only over the environment it was made
            // from: one that changed meanwhile is merged into again from a
            // fresh copy (`shared_env.rs`). A refused or interrupted merge
            // publishes nothing. For .olean-based merging with dependency
            // resolution, use importModule.
            let loaded = Arc::new(new_env);
            let merged = state
                .env
                .update(&state.work, deadline, move |target| {
                    super::env_merge::checked_merge_loaded_env(target, &loaded)
                        .map(|merged| (merged, ()))
                })
                .await?;
            if let Err(message) = merged {
                return Ok(Err(RpcError::internal_error(message)));
            }
        }
        Ok(Ok(load_result))
    })
    .await;

    match outcome {
        Ok(Ok(load_result)) => Response::success_typed(id.clone(), &load_result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string()))),
        Ok(Err(error)) => Response::error(id, error),
        Err(error) => Response::error(id, error.into_rpc_error(timeout)),
    }
}

/// Read and decode a saved environment. Runs on the work pool.
fn read_environment(path: &Path, format: &str) -> Result<Environment, String> {
    match format {
        "json" => {
            let json = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
            Environment::from_json(&json).map_err(|e| e.to_string())
        }
        _ => Environment::load_from_file(path).map_err(|e| e.to_string()),
    }
}

/// Handle the "importModule" method — loads .olean files by module name
///
/// What it loads is installed with structural checks only, and no verdict the
/// server gives re-checks it, so the request carries the launch token in its
/// own `params.token`, as `replace_unchecked` does (`trust_boundary.rs`).
///
/// The load is work on the pool under the request's deadline, into a copy of
/// the environment that is published only over the environment it was made
/// from (`shared_env.rs`). A change that lands while the modules load (a
/// merge, the verify family's set-up) is never overwritten: the load runs
/// again on a copy of the current environment. An interrupted load publishes
/// nothing.
#[instrument(skip(state, params))]
pub async fn handle_import_module(
    state: &ServerState,
    id: RequestId,
    params: ImportModuleParams,
) -> Response {
    let start = Instant::now();
    // A module closure is a batch of declarations: a batch's default, ten
    // times the server's.
    let timeout = Duration::from_millis(
        params
            .timeout_ms
            .unwrap_or(state.default_timeout_ms.saturating_mul(10)),
    );
    let deadline = start.checked_add(timeout);
    if let Err(error) = check_import_token(state.launch_token(), params.token.as_deref()) {
        return Response::error(id, error);
    }
    let module_name = params.module;
    // A component that holds a separator is a path: an absolute one replaced
    // the search path and read the file it spelled (`trust_boundary.rs`).
    if let Err(error) = check_module_name(&module_name) {
        return Response::error(id, error);
    }
    let requested_paths = params.search_paths;
    let root = state.workspace_root().map(Path::to_path_buf);
    // Use server-level cache so repeated imports of overlapping module hierarchies
    // don't re-parse the same .olean files.
    let cache = Arc::clone(&state.olean_cache);

    let outcome = within(timeout, async {
        // The client's search paths must resolve under the root; resolving
        // them is work on the pool (as many as the request names), and a
        // request that names none needs no slot for it. They are searched
        // after the operator's (the defaults). The search keeps the root's
        // real path: the walk runs later, and each file it reads from them is
        // judged against that root, not against what a search path has become.
        let searched = if requested_paths.is_empty() {
            Ok(None)
        } else {
            let module = module_name.clone();
            state
                .work
                .run(
                    deadline,
                    move || -> Result<Option<ModuleSearch>, RpcError> {
                        let confined = requested_paths
                            .iter()
                            .map(|p| confine("importModule", "search path", p, root.as_deref()))
                            .collect::<Result<Vec<PathBuf>, RpcError>>()?;
                        Ok(Some(ModuleSearch::new(
                            &module,
                            clean_olean::default_search_paths(),
                            confined,
                            root.as_deref(),
                        )))
                    },
                )
                .await?
        };
        let searched = match searched {
            Ok(search) => search,
            Err(error) => return Ok(Err(error)),
        };
        // Each module file the load reads from a client's search path, the
        // requested module's and every one its `.olean` headers import, must
        // resolve under that search path and under the root: a symbolic link
        // below it (`oleans/Ext -> /elsewhere`) took the file outside it, and
        // so did the search path swapped for a link out while this request
        // waited for the writer's turn (`trust_boundary.rs`). The load asks
        // before it reads each file.
        let loaded = state
            .env
            .update(&state.work, deadline, move |mut env| {
                let search = searched.clone().unwrap_or_else(|| {
                    ModuleSearch::new(
                        &module_name,
                        clean_olean::default_search_paths(),
                        Vec::new(),
                        None,
                    )
                });
                search
                    .load(&mut env, &cache)
                    .map(|summaries| (env, summaries))
            })
            .await?;
        Ok(loaded)
    })
    .await;

    match outcome {
        Ok(Ok(summaries)) => {
            let modules_loaded: Vec<String> = summaries
                .iter()
                .filter_map(|s| s.module_name.clone())
                .collect();
            let constants_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let constants_skipped: usize = summaries.iter().map(|s| s.duplicate_constants).sum();

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
        Ok(Err(error)) => Response::error(id, error),
        Err(error) => Response::error(id, error.into_rpc_error(timeout)),
    }
}

/// Handle the "getEnvironment" method
///
/// The summary (the counts and the first 100 names) is bounded, so it is
/// answered here, its wait for the environment inside the request's timeout.
/// The JSON rendering grows with the environment, so with `include_json` the
/// whole answer is work on the pool under the request's deadline
/// (`core::answer_with_env`).
#[instrument(skip(state, params))]
pub async fn handle_get_environment(
    state: &ServerState,
    id: RequestId,
    params: GetEnvironmentParams,
) -> Response {
    let start = Instant::now();
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let include_json = params.include_json;
    if include_json {
        return answer_with_env(state, id, start, timeout, move |id, env| {
            environment_answer(id, env, include_json)
        })
        .await;
    }
    match tokio::time::timeout(timeout, state.env.read()).await {
        Ok(env) => environment_answer(id, &env, include_json),
        Err(_) => Response::error(id, WorkError::Interrupted.into_rpc_error(timeout)),
    }
}

/// `getEnvironment`'s answer from the held environment.
fn environment_answer(id: RequestId, env: &Environment, include_json: bool) -> Response {
    let constant_names: Vec<String> = env
        .constants()
        .take(100)
        .map(|c| c.name.to_string())
        .collect();

    let json = if include_json {
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
