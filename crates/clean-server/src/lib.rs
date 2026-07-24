// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean JSON-RPC Server
//!
//! Provides an AI-native API for theorem proving:
//!
//! # Methods
//!
//! ## Core Type Checking
//! - `check`: Type check an expression or declaration
//! - `getType`: Get the type of an expression
//! - `batchCheck`: GPU-accelerated batch checking
//!
//! ## Proof & SMT
//! - `prove`: Attempt automatic proof via SMT
//! - `proveTLA`: Prove TLAPS obligations (TLA+ temporal logic)
//! - `batchProveTLA`: Batch TLA+ proof verification
//!
//! ## Premise Selection
//! - `getPremises`: Select relevant premises for a goal (MePo/MaSh/Hybrid)
//! - `batchGetPremises`: Batch premise selection for multiple goals
//!
//! ## Certificate Operations
//! - `verifyCert`: Verify a proof certificate
//! - `batchVerifyCert`: Parallel batch certificate verification (high-throughput)
//! - `verifyCertArchive`: Verify a compressed certificate archive
//! - `batchVerifyCertArchive`: Batch verification for compressed certificate archives
//! - `compressCert`: Structure-sharing compression for certificates (in-memory)
//! - `decompressCert`: Restore certificate from structure-sharing compression
//! - `archiveCert`: Byte-level compression (LZ4/Zstd) for storage/transmission
//! - `unarchiveCert`: Restore certificate from byte-level archive
//! - `trainDict`: Train a compression dictionary from sample certificates
//! - `archiveCertWithDict`: Dictionary-based Zstd compression for improved ratios
//! - `unarchiveCertWithDict`: Restore certificate from dictionary-compressed archive
//!
//! ## External Certificate Verification
//! These methods bridge external provers (Ay SMT, gamma-crown) with Lean verification:
//! - `verify_alethe_certificate` / `verifyAletheCertificate`: Verify external Alethe proof certificates
//! - `verify_farkas_certificate` / `verifyFarkasCertificate`: Verify linear arithmetic Farkas certificates
//! - `verify_entailment_certificate` / `verifyEntailmentCertificate`: Verify entailment certificates
//! - `verify_certificates_batch` / `verifyCertificatesBatch` / `batchVerifyExternalCert`: Batch external certificate verification
//!
//! Note: snake_case names are canonical (advertised in `serverInfo`). camelCase
//! aliases (`verifyFarkasCertificate`, etc.) are supported for external-cert
//! callers but are not part of the discovery contract.
//!
//! ## LLM Integration (Proof State Management)
//! - `initProofState`: Initialize a new proof state for interactive proving
//! - `applyTactic`: Apply a tactic to a proof state
//! - `getProofState`: Get current proof state (goals, context)
//! - `extractProof`: Extract completed proof term from proof state
//! - `batchApplyTactic`: Apply tactics to multiple proof states
//! - `verifyProof`: Verify a complete proof term
//! - `verifyProofBatch`: Batch verification of multiple proofs
//! - `verifyFile`: Full file verification with sorry detection
//! - `fillSorries`: Try a SorryHammer-style tactic sequence for each `sorry`
//! - `composeProof`: Splice per-sorry tactics back into a full file and verify it
//! - `searchProof`: Full proof search combining automation cascade and sorry filling
//!
//! ## Environment Management
//! - `saveEnvironment`: Serialize environment to file
//! - `loadEnvironment`: Load environment from file
//! - `importModule`: Load .olean module by name (e.g. "Init", "Std", "Mathlib")
//! - `getEnvironment`: Get environment information
//!
//! ## C Verification
//! - `verifyC`: Verify C code with ACSL specifications
//!
//! ## Server Management
//! - `serverInfo`: Get server capabilities
//! - `getConfig`: Get server configuration
//! - `getMetrics`: Get performance metrics
//! - `getCacheMetrics`: Get cache metrics for type checking and proof state
//!
//! # Transports
//!
//! - **TCP**: JSON-RPC 2.0 over line-delimited TCP (`serve`)
//! - **WebSocket**: JSON-RPC 2.0 over WebSocket with streaming progress (`websocket::serve_websocket`)
//!
//! # Streaming Progress
//!
//! WebSocket clients receive progress notifications during long-running operations:
//!
//! ```json
//! {"jsonrpc": "2.0", "method": "progress", "params": {"requestId": 1, "message": "Checking..."}}
//! ```
//!
//! # Design
//!
//! - JSON-RPC 2.0 protocol
//! - Connection pooling for warm starts
//! - Async/await with tokio runtime
//!
//! # Example
//!
//! ```text
//! use clean_server::{ServerConfig, serve};
//!
//! #[tokio::main]
//! async fn main() {
//!     let config = ServerConfig::default();
//!     serve(config).await.unwrap();
//! }
//! ```
//!
//! # Import Styles
//!
//! Primary embedding types are re-exported at the crate root:
//!
//! ```text
//! use clean_server::{Request, RequestId, Response, RpcError};
//! use clean_server::{ServerConfig, StateId, WebSocketConfig};
//! ```
//!
//! Module-path imports remain available when you want a grouped namespace:
//!
//! ```text
//! use clean_server::proof_state::pp_expr;
//! use clean_server::registry::{all_method_names, supports_progress};
//! use clean_server::rpc::{parse_message, Request};
//! ```

pub mod cli;
pub(crate) mod dispatch;
pub mod handlers;
pub mod mathverse_provider;
pub mod progress;
pub mod proof_state;
pub mod registry;
pub mod rpc;
pub mod rpc_goals;
pub mod rpc_widgets;
pub mod session_env;
pub(crate) mod startup;
pub mod websocket;

use crate::handlers::{ServerMetrics as HandlerServerMetrics, ServerState};
use crate::rpc::{parse_message, BatchItem, BatchResponse, ParsedMessage};
pub use rpc::{Request, RequestId, Response, RpcError};
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::Semaphore;
use tracing::{debug, error, info, instrument, warn};

/// Default per-connection request limit (0 = unlimited).
pub const DEFAULT_MAX_REQUESTS_PER_CONNECTION: u64 = 10_000;

/// Default graceful shutdown drain timeout in seconds.
pub const DEFAULT_DRAIN_TIMEOUT_SECS: u64 = 30;

/// Clean server configuration
#[derive(Clone)]
#[non_exhaustive]
pub struct ServerConfig {
    /// Address to bind to
    pub addr: SocketAddr,
    /// Enable GPU acceleration
    pub gpu_enabled: bool,
    /// Maximum concurrent requests
    pub max_concurrent: usize,
    /// Default timeout for operations (milliseconds)
    pub default_timeout_ms: u64,
    /// Number of worker threads for batch operations (0 = auto/Rayon default)
    pub worker_threads: usize,
    /// Optional pre-loaded environment (e.g. from --init or --stdlib flags)
    pub initial_env: Option<clean_kernel::Environment>,
    /// Optional precomputed math-project theorem-index provider.
    pub project_theorem_index: Option<proof_state::ProjectTheoremIndexProvider>,
    /// Maximum requests allowed per connection (0 = unlimited).
    pub max_requests_per_connection: u64,
    /// Graceful shutdown drain timeout in seconds.
    pub drain_timeout_secs: u64,
}

impl std::fmt::Debug for ServerConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ServerConfig")
            .field("addr", &self.addr)
            .field("gpu_enabled", &self.gpu_enabled)
            .field("max_concurrent", &self.max_concurrent)
            .field("default_timeout_ms", &self.default_timeout_ms)
            .field("worker_threads", &self.worker_threads)
            .field(
                "max_requests_per_connection",
                &self.max_requests_per_connection,
            )
            .field("drain_timeout_secs", &self.drain_timeout_secs)
            .field(
                "initial_env",
                &self.initial_env.as_ref().map(|e| {
                    format!(
                        "{} constants, {} inductives",
                        e.num_constants(),
                        e.num_inductives()
                    )
                }),
            )
            .field(
                "project_theorem_index",
                &self
                    .project_theorem_index
                    .as_ref()
                    .map(|provider| !provider.is_empty()),
            )
            .finish()
    }
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            addr: "127.0.0.1:8080".parse().expect("valid default address"),
            gpu_enabled: false,
            max_concurrent: 100,
            default_timeout_ms: 5000,
            worker_threads: 0, // Auto (Rayon default = num_cpus)
            initial_env: None,
            project_theorem_index: None,
            max_requests_per_connection: DEFAULT_MAX_REQUESTS_PER_CONNECTION,
            drain_timeout_secs: DEFAULT_DRAIN_TIMEOUT_SECS,
        }
    }
}

impl ServerConfig {
    /// Create a new server config with defaults
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new server config with the specified address
    #[must_use]
    pub fn with_addr(mut self, addr: SocketAddr) -> Self {
        self.addr = addr;
        self
    }

    /// Enable or disable GPU acceleration
    #[must_use]
    pub fn with_gpu(mut self, enabled: bool) -> Self {
        self.gpu_enabled = enabled;
        self
    }

    /// Set maximum concurrent requests
    #[must_use]
    pub fn with_max_concurrent(mut self, max: usize) -> Self {
        self.max_concurrent = max;
        self
    }

    /// Set number of worker threads for batch operations
    ///
    /// 0 = auto (Rayon default, typically num_cpus)
    #[must_use]
    pub fn with_worker_threads(mut self, threads: usize) -> Self {
        self.worker_threads = threads;
        self
    }

    /// Set default timeout for operations in milliseconds
    #[must_use]
    pub fn with_default_timeout_ms(mut self, timeout_ms: u64) -> Self {
        self.default_timeout_ms = timeout_ms;
        self
    }

    /// Set a pre-loaded environment for the server to start with
    #[must_use]
    pub fn with_environment(mut self, env: clean_kernel::Environment) -> Self {
        self.initial_env = Some(env);
        self
    }

    /// Set the maximum number of requests allowed per connection (0 = unlimited).
    #[must_use]
    pub fn with_max_requests_per_connection(mut self, limit: u64) -> Self {
        self.max_requests_per_connection = limit;
        self
    }

    /// Set the graceful shutdown drain timeout in seconds.
    #[must_use]
    pub fn with_drain_timeout_secs(mut self, secs: u64) -> Self {
        self.drain_timeout_secs = secs;
        self
    }
}

/// Server handle for managing a running server
pub struct ServerHandle {
    /// Local address the server is bound to
    local_addr: SocketAddr,
    /// Shutdown signal sender
    shutdown_tx: Option<tokio::sync::oneshot::Sender<()>>,
}

impl ServerHandle {
    /// Get the local address
    #[must_use]
    pub fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }

    /// Shutdown the server
    pub fn shutdown(mut self) {
        if let Some(tx) = self.shutdown_tx.take() {
            let _ = tx.send(());
        }
    }
}

/// Wait for all in-flight connections to complete, with a timeout.
///
/// Used by both TCP and WebSocket server loops after the accept loop exits.
pub(crate) async fn drain_inflight(
    count: &std::sync::atomic::AtomicU64,
    notify: &tokio::sync::Notify,
    timeout: std::time::Duration,
    label: &str,
) {
    let active = count.load(std::sync::atomic::Ordering::Acquire);
    if active == 0 {
        return;
    }
    info!(
        "Waiting for {} in-flight {label} connection(s) to drain (timeout {}s)",
        active,
        timeout.as_secs()
    );
    let drain_result = tokio::time::timeout(timeout, async {
        loop {
            if count.load(std::sync::atomic::Ordering::Acquire) == 0 {
                break;
            }
            notify.notified().await;
        }
    })
    .await;
    match drain_result {
        Ok(()) => info!("All {label} connections drained successfully"),
        Err(_) => {
            let remaining = count.load(std::sync::atomic::Ordering::Acquire);
            warn!("{label} drain timeout reached with {remaining} connection(s) still active");
        }
    }
}

/// Start the clean server
#[instrument(skip(config))]
pub async fn serve(config: ServerConfig) -> Result<ServerHandle, ServerError> {
    let listener = TcpListener::bind(config.addr)
        .await
        .map_err(|e| ServerError::Bind(e.to_string()))?;

    let local_addr = listener.local_addr()?;
    info!("Clean server listening on {}", local_addr);

    let initial_env = config.initial_env.unwrap_or_default();
    let mut state = ServerState::new();
    state.env = Arc::new(tokio::sync::RwLock::new(initial_env));
    state.default_timeout_ms = config.default_timeout_ms;
    state.gpu_enabled = config.gpu_enabled;
    state.worker_threads = config.worker_threads;
    state.metrics = HandlerServerMetrics::new();
    state.proof_cache = proof_state::ProofStateCache::default_config();
    if let Some(project_theorem_index) = config.project_theorem_index {
        state.theorem_index = project_theorem_index;
    }
    state.cache_metrics = handlers::CacheMetrics::default();
    state.olean_cache = Arc::new(clean_olean::ModuleCache::new());
    state.tactic_patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let state = Arc::new(state);

    let semaphore = Arc::new(Semaphore::new(config.max_concurrent));
    let (shutdown_tx, mut shutdown_rx) = tokio::sync::oneshot::channel::<()>();
    let max_requests = config.max_requests_per_connection;
    let drain_timeout = std::time::Duration::from_secs(config.drain_timeout_secs);

    let inflight_notify = Arc::new(tokio::sync::Notify::new());
    let inflight_count = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let notify_loop = Arc::clone(&inflight_notify);
    let count_loop = Arc::clone(&inflight_count);

    tokio::spawn(async move {
        loop {
            tokio::select! {
                accept_result = listener.accept() => {
                    match accept_result {
                        Ok((stream, peer_addr)) => {
                            debug!("New connection from {}", peer_addr);
                            let state = Arc::clone(&state);
                            let permit = semaphore.clone().acquire_owned().await;
                            let n = Arc::clone(&notify_loop);
                            let c = Arc::clone(&count_loop);
                            c.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            tokio::spawn(async move {
                                let _permit = permit;
                                if let Err(e) = handle_connection(stream, state, max_requests).await {
                                    warn!("Connection error from {}: {}", peer_addr, e);
                                }
                                debug!("Connection closed: {}", peer_addr);
                                if c.fetch_sub(1, std::sync::atomic::Ordering::AcqRel) == 1 {
                                    n.notify_waiters();
                                }
                            });
                        }
                        Err(e) => error!("Accept error: {}", e),
                    }
                }
                _ = &mut shutdown_rx => {
                    info!("Server shutting down — draining in-flight connections");
                    break;
                }
            }
        }
        drain_inflight(&count_loop, &notify_loop, drain_timeout, "TCP").await;
    });

    Ok(ServerHandle {
        local_addr,
        shutdown_tx: Some(shutdown_tx),
    })
}

/// Maximum line length for TCP transport (10 MB).
const MAX_TCP_LINE_LENGTH: usize = 10 * 1024 * 1024;

/// Handle a single connection
#[instrument(skip(stream, state))]
async fn handle_connection(
    stream: TcpStream,
    state: Arc<ServerState>,
    max_requests: u64,
) -> Result<(), ServerError> {
    let (reader, mut writer) = stream.into_split();
    let mut reader = BufReader::new(reader);
    let mut line = String::new();
    let mut request_count: u64 = 0;

    loop {
        line.clear();
        let bytes_read = reader.read_line(&mut line).await?;

        if bytes_read == 0 {
            // Connection closed
            break;
        }

        if line.len() > MAX_TCP_LINE_LENGTH {
            warn!(
                "TCP line exceeds {} byte limit, dropping",
                MAX_TCP_LINE_LENGTH
            );
            let err_response = Response::error(
                RequestId::Null,
                RpcError::invalid_request(format!(
                    "Line too long: {} bytes exceeds {} limit",
                    line.len(),
                    MAX_TCP_LINE_LENGTH
                )),
            );
            if let Ok(json) = serde_json::to_string(&err_response) {
                writer.write_all(json.as_bytes()).await?;
                writer.write_all(b"\n").await?;
                writer.flush().await?;
            }
            continue;
        }

        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        // Enforce per-connection request limit (0 = unlimited)
        request_count = request_count.saturating_add(1);
        if max_requests > 0 && request_count > max_requests {
            warn!("Per-connection request limit ({}) exceeded", max_requests);
            let err_response = Response::error(
                RequestId::Null,
                RpcError::request_limit_exceeded(max_requests),
            );
            if let Ok(json) = serde_json::to_string(&err_response) {
                writer.write_all(json.as_bytes()).await?;
                writer.write_all(b"\n").await?;
                writer.flush().await?;
            }
            break;
        }

        debug!("Received: {}", line);

        let response = process_message(line, &state).await;

        // Serialize and send response
        let response_json = match &response {
            MessageResponse::Single(r) => serde_json::to_string(r),
            MessageResponse::Batch(b) => serde_json::to_string(b),
            MessageResponse::None => continue, // Notification, no response
        };

        match response_json {
            Ok(json) => {
                debug!("Sending: {}", json);
                writer.write_all(json.as_bytes()).await?;
                writer.write_all(b"\n").await?;
                writer.flush().await?;
            }
            Err(e) => {
                error!("Failed to serialize response: {}", e);
                let err_response = Response::error(
                    RequestId::Null,
                    RpcError::internal_error(format!("Response serialization failed: {e}")),
                );
                if let Ok(json) = serde_json::to_string(&err_response) {
                    writer.write_all(json.as_bytes()).await?;
                    writer.write_all(b"\n").await?;
                    writer.flush().await?;
                }
            }
        }
    }

    Ok(())
}

/// Response type (single, batch, or none for notifications)
enum MessageResponse {
    Single(Response),
    Batch(BatchResponse),
    None,
}

/// Process a JSON-RPC message
async fn process_message(json: &str, state: &ServerState) -> MessageResponse {
    match parse_message(json) {
        Ok(ParsedMessage::Single(request)) => {
            if request.is_notification() {
                // Process notification but don't respond
                let _ = dispatch::dispatch_request(
                    &request.method,
                    request.params.clone(),
                    RequestId::Null,
                    state,
                    None,
                )
                .await;
                MessageResponse::None
            } else {
                let id = request.id.clone().unwrap_or(RequestId::Null);
                let response =
                    dispatch::dispatch_request(&request.method, request.params, id, state, None)
                        .await;
                MessageResponse::Single(response)
            }
        }
        Ok(ParsedMessage::Batch(items)) => {
            let mut responses = Vec::with_capacity(items.len());
            for item in items {
                match item {
                    BatchItem::Request(request) => {
                        if !request.is_notification() {
                            let id = request.id.clone().unwrap_or(RequestId::Null);
                            let response = dispatch::dispatch_request(
                                &request.method,
                                request.params,
                                id,
                                state,
                                None,
                            )
                            .await;
                            responses.push(response);
                        }
                    }
                    BatchItem::Error(err) => {
                        responses.push(Response::error(RequestId::Null, err));
                    }
                }
            }
            if responses.is_empty() {
                MessageResponse::None
            } else {
                MessageResponse::Batch(BatchResponse(responses))
            }
        }
        Err(e) => MessageResponse::Single(Response::error(RequestId::Null, e)),
    }
}

/// Errors that can occur during server initialization and operation.
///
/// These errors indicate problems with server lifecycle (binding, I/O)
/// rather than individual request handling (which uses RpcError).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ServerError {
    /// Failed to bind the server to the specified network address.
    #[error("Failed to bind to address: {0}")]
    Bind(String),
    /// An I/O error occurred during server operation.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

// Re-export key types for external consumers
pub use handlers::{
    ArchiveCertParams, ArchiveCertResult, ArchiveCertWithDictParams, ArchiveCertWithDictResult,
    BatchCheckItemResult, BatchCheckParams, BatchCheckResult, BatchGetPremisesItem,
    BatchGetPremisesItemResult, BatchGetPremisesParams, BatchGetPremisesResult,
    BatchGetPremisesStats, BatchProveTlaItem, BatchProveTlaItemResult, BatchProveTlaParams,
    BatchProveTlaResult, BatchProveTlaStats, BatchStats, BatchVerifyCertItem,
    BatchVerifyCertItemResult, BatchVerifyCertParams, BatchVerifyCertResult, BatchVerifyCertStats,
    CheckError, CheckParams, CheckResult, CompressCertParams, CompressCertResult,
    CompressCertStats, DecompressCertParams, DecompressCertResult, ExtractedTheorem,
    GetCacheMetricsResult, GetConfigParams, GetConfigResult, GetEnvironmentParams,
    GetEnvironmentResult, GetMetricsResult, GetPremisesParams, GetPremisesResult, GetTypeParams,
    GetTypeResult, ImportModuleParams, ImportModuleResult, LoadEnvironmentParams,
    LoadEnvironmentResult, MethodCounts, PremiseInfo, PremiseSelectionStats, ProveParams,
    ProveResult, ProveStatus, ProveTlaParams, ProveTlaResult, SaveEnvironmentParams,
    SaveEnvironmentResult, SearchProofParams, SearchProofResult, SearchStats, SearchStrategy,
    ServerInfo, ServerMetrics, SorryLocation, StrategyTiming, TimingStats, TrainDictParams,
    TrainDictResult, TypeCacheMetrics, UnarchiveCertParams, UnarchiveCertResult,
    UnarchiveCertWithDictParams, UnarchiveCertWithDictResult, VerifyCFunctionResult, VerifyCParams,
    VerifyCResult, VerifyCVCDetail, VerifyCertParams, VerifyCertResult, VerifyFileParams,
    VerifyFileResult, VerifyProofContext, VerifyProofError, VerifyProofParams, VerifyProofPosition,
    VerifyProofResult,
};
pub use proof_state::StateId;
pub use websocket::{
    serve_websocket, ProgressNotification, ProgressParams, WebSocketConfig, WebSocketError,
    WebSocketHandle,
};

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
    use tokio::net::TcpStream;

    async fn send_request(addr: SocketAddr, request: &str) -> String {
        let mut stream = TcpStream::connect(addr).await.unwrap();
        stream.write_all(request.as_bytes()).await.unwrap();
        stream.write_all(b"\n").await.unwrap();

        let mut reader = BufReader::new(stream);
        let mut response = String::new();
        reader.read_line(&mut response).await.unwrap();
        response
    }

    #[cfg(feature = "carcara-verify")]
    fn load_holey_alethe_fixture() -> clean_elab::cert::external::ExternalAletheCert {
        let workspace_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("crate directory should have workspace parent")
            .parent()
            .expect("workspace root should exist");
        let fixture_path = workspace_root
            .join("tests/fixtures/external_certificates")
            .join("ay_alethe_envelope.json");
        let json = std::fs::read_to_string(&fixture_path)
            .expect("Alethe fixture should be readable for TCP smoke tests");
        let cert: clean_elab::cert::external::ExternalCertificate =
            serde_json::from_str(&json).expect("Alethe fixture should deserialize");
        let mut cert = match cert {
            clean_elab::cert::external::ExternalCertificate::Alethe(cert) => cert,
            other => panic!("expected Alethe fixture, got {other:?}"),
        };

        let marker = ":rule ";
        let start = cert
            .proof
            .find(marker)
            .map(|i| i + marker.len())
            .expect("Alethe fixture proof should contain a rule marker");
        let end = cert.proof[start..]
            .find(|c: char| c.is_whitespace() || c == ')')
            .map(|i| start + i)
            .expect("Alethe fixture rule should terminate");
        assert_ne!(
            &cert.proof[start..end],
            "hole",
            "fixture mutation must change the rule name"
        );
        cert.proof = format!("{}hole{}", &cert.proof[..start], &cert.proof[end..]);
        cert
    }

    #[tokio::test]
    async fn test_server_check() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Use fully-typed expression
        let request = r#"{"jsonrpc": "2.0", "method": "check", "params": {"code": "fun (A : Type) (x : A) => x"}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(response.contains("\"valid\":true"), "Response: {response}");

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_info() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(response.contains("clean-server"));
        assert!(response.contains("\"methods\""));

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_method_not_found() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "unknownMethod", "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(response.contains("\"error\""));
        assert!(response.contains("-32601")); // METHOD_NOT_FOUND

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_request() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"[{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}, {"jsonrpc": "2.0", "method": "serverInfo", "id": 2}]"#;
        let response = send_request(addr, request).await;

        // Should be an array response
        assert!(response.starts_with('['));
        assert!(response.ends_with("]\n"));

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_request_with_invalid_item() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Batch with one valid and one invalid request
        let request =
            r#"[{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}, {"not_valid": true}]"#;
        let response = send_request(addr, request).await;

        // Should be an array response
        assert!(response.starts_with('['), "Expected array: {response}");
        let arr: Vec<serde_json::Value> =
            serde_json::from_str(&response).expect("Failed to parse response");
        assert_eq!(arr.len(), 2, "Expected 2 responses: {response}");

        // First should be success
        assert!(
            arr[0].get("result").is_some(),
            "Expected result in first: {response}"
        );
        assert_eq!(
            arr[0].get("id"),
            Some(&serde_json::json!(1)),
            "Expected id=1 in first"
        );

        // Second should be error with null id
        assert!(
            arr[1].get("error").is_some(),
            "Expected error in second: {response}"
        );
        assert_eq!(
            arr[1].get("id"),
            Some(&serde_json::Value::Null),
            "Expected null id for invalid item"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_request_with_invalid_jsonrpc_version() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Batch with one valid and one with invalid jsonrpc version
        let request = r#"[{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}, {"jsonrpc": "1.0", "method": "serverInfo", "id": 2}]"#;
        let response = send_request(addr, request).await;

        let arr: Vec<serde_json::Value> =
            serde_json::from_str(&response).expect("Failed to parse response");
        assert_eq!(arr.len(), 2, "Expected 2 responses: {response}");

        // First should be success
        assert!(arr[0].get("result").is_some(), "Expected result in first");

        // Second should be error
        let error = arr[1].get("error").expect("Expected error in second");
        assert!(
            error.get("message").is_some(),
            "Expected error message: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_request_with_primitive_items() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Batch with valid request mixed with primitive types (not objects)
        // Per JSON-RPC 2.0, batch items must be Request objects
        let request =
            r#"[{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}, 42, "string", true, null]"#;
        let response = send_request(addr, request).await;

        // Should be an array response with 5 items
        assert!(response.starts_with('['), "Expected array: {response}");
        let arr: Vec<serde_json::Value> =
            serde_json::from_str(&response).expect("Failed to parse response");
        assert_eq!(arr.len(), 5, "Expected 5 responses: {response}");

        // First should be success (valid request)
        assert!(
            arr[0].get("result").is_some(),
            "Expected result in first: {response}"
        );

        // Remaining 4 should be errors (primitives are not valid request objects)
        for (i, item) in arr.iter().enumerate().skip(1) {
            assert!(
                item.get("error").is_some(),
                "Expected error for item {i}: {response}"
            );
            assert_eq!(
                item.get("id"),
                Some(&serde_json::Value::Null),
                "Expected null id for primitive item {i}"
            );
        }

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_invalid_json() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r"{invalid json";
        let response = send_request(addr, request).await;

        assert!(response.contains("\"error\""));
        assert!(response.contains("-32700")); // PARSE_ERROR

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_verify_c() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "verifyC", "params": {"code": "//@ requires n >= 0;\n//@ ensures \\result >= 0;\nint id(int n) { return n; }"}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"num_functions\":1"),
            "Response: {response}"
        );
        assert!(response.contains("\"id\""), "Response: {response}");

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_verify_cert() {
        use clean_kernel::cert::ProofCert;
        use clean_kernel::{Expr, Level};

        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Construct a valid certificate for Sort(0) : Sort(1)
        let level = Level::zero();
        let expr = Expr::sort(level.clone());
        let cert = ProofCert::Sort {
            level: level.clone(),
        };

        let item = BatchVerifyCertItem {
            id: "test1".to_string(),
            cert,
            expr,
        };

        // Serialize the request params
        let params = BatchVerifyCertParams {
            items: vec![item],
            threads: 0,
            timeout_ms: None,
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchVerifyCert", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"success\":true"),
            "Response: {response}"
        );
        assert!(response.contains("\"total\":1"), "Response: {response}");

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_prove_tla_always_true() {
        use clean_tla::{TlaFormula, TlaObligation};

        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Create a simple TLA+ obligation: prove □TRUE
        let obligation = TlaObligation {
            module: "TestModule".to_string(),
            line: Some(1),
            declares: vec![],
            hypotheses: vec![],
            goal: TlaFormula::Always(Box::new(TlaFormula::True)),
            tactic_hint: None,
        };

        let params = ProveTlaParams {
            obligation,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "proveTLA", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"proved\":true"),
            "Expected proved:true in response: {response}"
        );
        assert!(
            response.contains("\"tactics_tried\""),
            "Response: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_prove_tla_eventually_true() {
        use clean_tla::{TlaFormula, TlaObligation};

        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Create a simple TLA+ obligation: prove ◇TRUE
        let obligation = TlaObligation {
            module: "TestModule".to_string(),
            line: Some(2),
            declares: vec![],
            hypotheses: vec![],
            goal: TlaFormula::Eventually(Box::new(TlaFormula::True)),
            tactic_hint: None,
        };

        let params = ProveTlaParams {
            obligation,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "proveTLA", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"proved\":true"),
            "Expected proved:true in response: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_info_includes_prove_tla() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(
            response.contains("\"proveTLA\""),
            "serverInfo should include proveTLA method: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_prove_tla_with_hypotheses() {
        use clean_tla::{TlaFormula, TlaHypothesis, TlaObligation};

        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Create an obligation with hypotheses: h1: P → prove P (trivially via hypothesis)
        // Actually: h1: TRUE → □TRUE (hypotheses should help but goal is independently provable)
        let obligation = TlaObligation {
            module: "TestModule".to_string(),
            line: Some(10),
            declares: vec![],
            hypotheses: vec![TlaHypothesis {
                name: "h1".to_string(),
                formula: TlaFormula::True,
            }],
            goal: TlaFormula::Always(Box::new(TlaFormula::True)),
            tactic_hint: None,
        };

        let params = ProveTlaParams {
            obligation,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "proveTLA", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"proved\":true"),
            "Expected proved:true with hypotheses: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_prove_tla_with_declarations() {
        use clean_tla::{TlaDeclare, TlaFormula, TlaObligation};

        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Create an obligation with CONSTANT declarations
        let obligation = TlaObligation {
            module: "TestModule".to_string(),
            line: Some(20),
            declares: vec![
                TlaDeclare::Constant {
                    name: "N".to_string(),
                    arity: 0,
                },
                TlaDeclare::Variable {
                    name: "x".to_string(),
                },
            ],
            hypotheses: vec![],
            goal: TlaFormula::Eventually(Box::new(TlaFormula::True)),
            tactic_hint: None,
        };

        let params = ProveTlaParams {
            obligation,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "proveTLA", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"proved\":true"),
            "Expected proved:true with declarations: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_prove_tla_complex_sequent() {
        use clean_tla::{TlaDeclare, TlaFormula, TlaHypothesis, TlaObligation};

        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Full sequent with temporal goal: CONSTANT N; VARIABLE x; h1: □TRUE ├── □TRUE
        // This tests complex obligations with declarations and hypotheses where goal is provable
        let obligation = TlaObligation {
            module: "ComplexModule".to_string(),
            line: Some(42),
            declares: vec![
                TlaDeclare::Constant {
                    name: "N".to_string(),
                    arity: 0,
                },
                TlaDeclare::Variable {
                    name: "x".to_string(),
                },
            ],
            hypotheses: vec![TlaHypothesis {
                name: "h1".to_string(),
                formula: TlaFormula::Always(Box::new(TlaFormula::True)),
            }],
            goal: TlaFormula::Always(Box::new(TlaFormula::True)),
            tactic_hint: None,
        };

        let params = ProveTlaParams {
            obligation,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "proveTLA", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        // □TRUE is provable by the temporal tactic engine
        assert!(
            response.contains("\"proved\":true"),
            "Expected proved:true for complex sequent: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_prove_tla() {
        use clean_tla::{TlaFormula, TlaObligation};

        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Create batch of 3 obligations
        let items = vec![
            BatchProveTlaItem {
                id: "ob1".to_string(),
                obligation: TlaObligation {
                    module: "Batch1".to_string(),
                    line: Some(1),
                    declares: vec![],
                    hypotheses: vec![],
                    goal: TlaFormula::Always(Box::new(TlaFormula::True)),
                    tactic_hint: None,
                },
            },
            BatchProveTlaItem {
                id: "ob2".to_string(),
                obligation: TlaObligation {
                    module: "Batch2".to_string(),
                    line: Some(2),
                    declares: vec![],
                    hypotheses: vec![],
                    goal: TlaFormula::Eventually(Box::new(TlaFormula::True)),
                    tactic_hint: None,
                },
            },
            BatchProveTlaItem {
                id: "ob3".to_string(),
                obligation: TlaObligation {
                    module: "Batch3".to_string(),
                    line: Some(3),
                    declares: vec![],
                    hypotheses: vec![],
                    // Another temporal goal that's provable: □TRUE
                    goal: TlaFormula::Always(Box::new(TlaFormula::True)),
                    tactic_hint: None,
                },
            },
        ];

        let params = BatchProveTlaParams {
            items,
            threads: 0,
            timeout_ms: Some(10000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchProveTLA", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(response.contains("\"total\":3"), "Response: {response}");
        // All three obligations should be proved
        assert!(
            response.contains("\"all_proved\":true"),
            "Expected all_proved:true: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_info_includes_batch_prove_tla() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(
            response.contains("\"batchProveTLA\""),
            "serverInfo should include batchProveTLA method: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_info_includes_get_premises() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(
            response.contains("\"getPremises\""),
            "serverInfo should include getPremises method: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_get_premises_basic() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test getPremises with a simple goal using Sort (always available)
        let params = GetPremisesParams {
            goal: "Sort 0".to_string(),
            method: "hybrid".to_string(),
            max_premises: 10,
            threshold: 0.0,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "getPremises", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"premises\""),
            "Response should contain premises: {response}"
        );
        assert!(
            response.contains("\"stats\""),
            "Response should contain stats: {response}"
        );
        assert!(
            response.contains("\"method_used\""),
            "Response should contain method_used: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_get_premises_mepo() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test with mepo method - use Prop (Sort 0, always available)
        let params = GetPremisesParams {
            goal: "Prop".to_string(),
            method: "mepo".to_string(),
            max_premises: 5,
            threshold: 0.0,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "getPremises", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"method_used\":\"mepo\""),
            "Response should use mepo method: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_get_premises_mash() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test with mash method - use Type (Sort 1, always available)
        let params = GetPremisesParams {
            goal: "Type".to_string(),
            method: "mash".to_string(),
            max_premises: 5,
            threshold: 0.0,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "getPremises", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"method_used\":\"mash\""),
            "Response should use mash method: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_get_premises_with_defaults() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test with minimal params (should use defaults) - Prop is always available
        let request =
            r#"{"jsonrpc": "2.0", "method": "getPremises", "params": {"goal": "Prop"}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        // Default method is hybrid
        assert!(
            response.contains("\"method_used\":\"hybrid\""),
            "Default method should be hybrid: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_get_premises_basic() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test batchGetPremises with multiple goals
        let params = BatchGetPremisesParams {
            items: vec![
                BatchGetPremisesItem {
                    id: "goal1".to_string(),
                    goal: "Prop".to_string(),
                },
                BatchGetPremisesItem {
                    id: "goal2".to_string(),
                    goal: "Type".to_string(),
                },
            ],
            method: "hybrid".to_string(),
            max_premises: 10,
            threshold: 0.0,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchGetPremises", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"results\""),
            "Response should contain results: {response}"
        );
        assert!(
            response.contains("\"stats\""),
            "Response should contain stats: {response}"
        );
        assert!(
            response.contains("\"goal1\""),
            "Response should contain goal1 id: {response}"
        );
        assert!(
            response.contains("\"goal2\""),
            "Response should contain goal2 id: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_get_premises_mepo() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test with mepo method
        let params = BatchGetPremisesParams {
            items: vec![BatchGetPremisesItem {
                id: "mepo1".to_string(),
                goal: "Sort 0".to_string(),
            }],
            method: "mepo".to_string(),
            max_premises: 5,
            threshold: 0.0,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchGetPremises", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"method_used\":\"mepo\""),
            "Response should use mepo method: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_get_premises_mash() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test with mash method
        let params = BatchGetPremisesParams {
            items: vec![BatchGetPremisesItem {
                id: "mash1".to_string(),
                goal: "Type".to_string(),
            }],
            method: "mash".to_string(),
            max_premises: 5,
            threshold: 0.0,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchGetPremises", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(
            response.contains("\"method_used\":\"mash\""),
            "Response should use mash method: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_get_premises_with_invalid_goal() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test with mix of valid and invalid goals
        let params = BatchGetPremisesParams {
            items: vec![
                BatchGetPremisesItem {
                    id: "valid".to_string(),
                    goal: "Prop".to_string(),
                },
                BatchGetPremisesItem {
                    id: "invalid".to_string(),
                    goal: "NonexistentIdentifier".to_string(),
                },
            ],
            method: "hybrid".to_string(),
            max_premises: 10,
            threshold: 0.0,
            timeout_ms: Some(5000),
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchGetPremises", "params": {params_json}, "id": 1}}"#
        );

        let response = send_request(addr, &request).await;

        // Batch should still succeed with partial results
        assert!(response.contains("\"result\""), "Response: {response}");
        // Check stats show 1 success, 1 failure
        assert!(
            response.contains("\"succeeded\":1"),
            "Should have 1 success: {response}"
        );
        assert!(
            response.contains("\"failed\":1"),
            "Should have 1 failure: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_batch_get_premises_with_defaults() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Test with minimal params (should use defaults)
        let request = r#"{"jsonrpc": "2.0", "method": "batchGetPremises", "params": {"items": [{"id": "test", "goal": "Prop"}]}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(response.contains("\"result\""), "Response: {response}");
        // Default method is hybrid
        assert!(
            response.contains("\"method_used\":\"hybrid\""),
            "Default method should be hybrid: {response}"
        );

        handle.shutdown();
    }

    // ============================================================================
    // Alias Registry Contract Tests (Part of #1380)
    // ============================================================================

    /// Regression test: all registry-defined aliases are accepted by dispatch.
    ///
    /// Calls dispatch::dispatch_request with each alias from the registry and verifies it
    /// doesn't return METHOD_NOT_FOUND. This catches regressions where a dispatch
    /// match arm is removed but the alias definition remains in the registry.
    #[tokio::test]
    async fn test_http_dispatch_supports_all_registry_aliases() {
        let state = ServerState::new();

        for (alias, canonical) in registry::all_aliases() {
            let response =
                dispatch::dispatch_request(alias, None, RequestId::Number(1), &state, None).await;

            if let Some(error) = response.error {
                assert_ne!(
                    error.code,
                    rpc::error_codes::METHOD_NOT_FOUND,
                    "Registry alias '{}' (canonical: '{}') not handled by dispatch",
                    alias,
                    canonical
                );
            }
        }
    }

    // ============================================================================
    // camelCase Alias Tests (Part of #894 / #901)
    // ============================================================================

    #[tokio::test]
    async fn test_verify_farkas_certificate_camelcase_alias() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Valid Farkas certificate: x <= 5, -x <= -6 → contradiction (5 - 6 = -1 < 0)
        // ExternalCertificate uses serde(tag = "type") with rename = "farkas_certificate"
        let request = r#"{"jsonrpc": "2.0", "method": "verifyFarkasCertificate", "params": {"certificate": {"type": "farkas_certificate", "version": "1.0", "constraints": [{"kind": "le", "coefficients": {"x": {"num": "1", "den": "1"}}, "constant": {"num": "5", "den": "1"}}, {"kind": "le", "coefficients": {"x": {"num": "-1", "den": "1"}}, "constant": {"num": "-6", "den": "1"}}], "multipliers": [{"num": "1", "den": "1"}, {"num": "1", "den": "1"}], "conclusion": "contradiction"}}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(
            response.contains("\"result\""),
            "Expected result in response: {response}"
        );
        assert!(
            response.contains("\"valid\":true"),
            "Expected valid=true: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_verify_entailment_certificate_camelcase_alias() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Valid entailment: x <= 5 implies x <= 6 (multiplier 1)
        // ExternalCertificate uses serde(tag = "type") with rename = "entailment_certificate"
        let request = r#"{"jsonrpc": "2.0", "method": "verifyEntailmentCertificate", "params": {"certificate": {"type": "entailment_certificate", "version": "1.0", "premises": [{"kind": "le", "coefficients": {"x": {"num": "1", "den": "1"}}, "constant": {"num": "5", "den": "1"}}], "multipliers": [{"num": "1", "den": "1"}], "conclusion": {"kind": "le", "coefficients": {"x": {"num": "1", "den": "1"}}, "constant": {"num": "6", "den": "1"}}}}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(
            response.contains("\"result\""),
            "Expected result in response: {response}"
        );
        assert!(
            response.contains("\"valid\":true"),
            "Expected valid=true: {response}"
        );

        handle.shutdown();
    }

    #[cfg(feature = "carcara-verify")]
    #[tokio::test]
    async fn test_verify_alethe_certificate_holey_proof_over_tcp() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let cert =
            clean_elab::cert::external::ExternalCertificate::Alethe(load_holey_alethe_fixture());
        let request = serde_json::json!({
            "jsonrpc": "2.0",
            "method": "verify_alethe_certificate",
            "params": {
                "certificate": cert,
            },
            "id": 1,
        })
        .to_string();
        let response = send_request(addr, &request).await;
        let parsed: serde_json::Value =
            serde_json::from_str(&response).expect("server response should be valid JSON");

        assert!(
            parsed.get("error").is_none() || parsed["error"].is_null(),
            "holey proofs should not surface as transport-level RPC errors: {parsed}"
        );
        assert_eq!(
            parsed["result"]["valid"],
            serde_json::Value::Bool(false),
            "holey proofs must stay invalid over the top-level TCP RPC path"
        );
        assert!(
            parsed["result"]["error"].is_null(),
            "single-certificate RPC should not reclassify holey proofs as handler errors: {parsed}"
        );
        assert!(
            parsed["result"]["detail"].is_null(),
            "single-certificate RPC should not synthesize extra detail for holey proofs: {parsed}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_verify_certificates_batch_camelcase_alias() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Batch with one valid certificate
        // ExternalCertificate uses serde(tag = "type") with rename = "farkas_certificate"
        let request = r#"{"jsonrpc": "2.0", "method": "verifyCertificatesBatch", "params": {"certificates": [{"id": "test1", "certificate": {"type": "farkas_certificate", "version": "1.0", "constraints": [{"kind": "le", "coefficients": {"x": {"num": "1", "den": "1"}}, "constant": {"num": "5", "den": "1"}}, {"kind": "le", "coefficients": {"x": {"num": "-1", "den": "1"}}, "constant": {"num": "-6", "den": "1"}}], "multipliers": [{"num": "1", "den": "1"}, {"num": "1", "den": "1"}], "conclusion": "contradiction"}}], "threads": 0}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(
            response.contains("\"result\""),
            "Expected result in response: {response}"
        );
        assert!(
            response.contains("\"total\":1"),
            "Expected total=1: {response}"
        );
        assert!(
            response.contains("\"valid\":1"),
            "Expected valid=1 in stats: {response}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_batch_verify_external_cert_alias() {
        let config = ServerConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // batchVerifyExternalCert is alternative alias for verify_certificates_batch
        // ExternalCertificate uses serde(tag = "type") with rename = "farkas_certificate"
        let request = r#"{"jsonrpc": "2.0", "method": "batchVerifyExternalCert", "params": {"certificates": [{"id": "test1", "certificate": {"type": "farkas_certificate", "version": "1.0", "constraints": [{"kind": "le", "coefficients": {"x": {"num": "1", "den": "1"}}, "constant": {"num": "5", "den": "1"}}, {"kind": "le", "coefficients": {"x": {"num": "-1", "den": "1"}}, "constant": {"num": "-6", "den": "1"}}], "multipliers": [{"num": "1", "den": "1"}, {"num": "1", "den": "1"}], "conclusion": "contradiction"}}], "threads": 0}, "id": 1}"#;
        let response = send_request(addr, request).await;

        assert!(
            response.contains("\"result\""),
            "Expected result in response: {response}"
        );
        assert!(
            response.contains("\"total\":1"),
            "Expected total=1: {response}"
        );

        handle.shutdown();
    }

    /// End-to-end TCP test: server starts with prelude env (Nat, Bool, Eq, List),
    /// client sends check requests over JSON-RPC and verifies type checking works.
    /// This exercises the same code path as `clean server --init`.
    #[tokio::test]
    async fn test_server_preloaded_env_check_nat() {
        let env =
            clean_kernel::Environment::try_with_prelude().expect("try_with_prelude should succeed");
        let config = ServerConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_environment(env);
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Check that Nat is well-typed in the pre-loaded environment
        let request =
            r#"{"jsonrpc": "2.0", "method": "check", "params": {"code": "Nat"}, "id": 1}"#;
        let response = send_request(addr, request).await;
        assert!(
            response.contains("\"valid\":true"),
            "Nat should be valid in preloaded env: {response}"
        );

        // Check that @Eq Nat is well-typed
        let request =
            r#"{"jsonrpc": "2.0", "method": "check", "params": {"code": "@Eq Nat"}, "id": 2}"#;
        let response = send_request(addr, request).await;
        assert!(
            response.contains("\"valid\":true"),
            "@Eq Nat should be valid in preloaded env: {response}"
        );

        // Check that @List Nat is well-typed
        let request =
            r#"{"jsonrpc": "2.0", "method": "check", "params": {"code": "@List Nat"}, "id": 3}"#;
        let response = send_request(addr, request).await;
        assert!(
            response.contains("\"valid\":true"),
            "@List Nat should be valid in preloaded env: {response}"
        );

        // Verify getEnvironment shows many constants
        let request = r#"{"jsonrpc": "2.0", "method": "getEnvironment", "params": {}, "id": 4}"#;
        let response = send_request(addr, request).await;
        assert!(
            response.contains("\"num_constants\""),
            "getEnvironment should return num_constants: {response}"
        );
        // Parse and verify the constant count is substantial
        let parsed: serde_json::Value = serde_json::from_str(&response).unwrap();
        let num_constants = parsed["result"]["num_constants"].as_u64().unwrap_or(0);
        assert!(
            num_constants > 10,
            "preloaded env should have >10 constants, got {num_constants}"
        );

        handle.shutdown();
    }

    /// Negative test: non-existent identifier should fail even in preloaded env.
    #[tokio::test]
    async fn test_server_preloaded_env_unknown_name_fails() {
        let env =
            clean_kernel::Environment::try_with_prelude().expect("try_with_prelude should succeed");
        let config = ServerConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_environment(env);
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // An identifier that doesn't exist in the prelude should not type-check
        let request = r#"{"jsonrpc": "2.0", "method": "check", "params": {"code": "NonExistentType42"}, "id": 1}"#;
        let response = send_request(addr, request).await;
        assert!(
            !response.contains("\"valid\":true"),
            "NonExistentType42 should NOT be valid: {response}"
        );

        handle.shutdown();
    }

    // ════════════════════════════════════════════════════════════════════════
    // Shutdown drain and per-connection request limit tests
    // ════════════════════════════════════════════════════════════════════════

    #[tokio::test]
    async fn test_tcp_per_connection_request_limit_enforced() {
        // Set a low limit so the test is fast
        let config = ServerConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_max_requests_per_connection(3);
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let mut stream = TcpStream::connect(addr).await.unwrap();
        let (reader, mut writer) = stream.split();
        let mut reader = BufReader::new(reader);

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;

        let mut responses = Vec::new();
        // Send 4 requests (limit is 3), expect the 4th to be rejected
        for _ in 0..4 {
            writer.write_all(request.as_bytes()).await.unwrap();
            writer.write_all(b"\n").await.unwrap();
        }

        // Read all responses until the connection closes
        loop {
            let mut line = String::new();
            let n = reader.read_line(&mut line).await.unwrap();
            if n == 0 {
                break;
            }
            responses.push(line);
        }

        // First 3 should succeed
        assert!(
            responses.len() >= 3,
            "Expected at least 3 responses, got {}",
            responses.len()
        );
        for resp in &responses[..3] {
            assert!(
                resp.contains("\"result\""),
                "First 3 should succeed: {resp}"
            );
        }

        // The 4th should be an error with REQUEST_LIMIT_EXCEEDED code
        assert!(
            responses.len() == 4,
            "Expected exactly 4 responses (3 ok + 1 error), got {}",
            responses.len()
        );
        let err_resp = &responses[3];
        assert!(
            err_resp.contains("-32005"),
            "4th response should contain REQUEST_LIMIT_EXCEEDED code: {err_resp}"
        );
        assert!(
            err_resp.contains("request limit"),
            "4th response should mention request limit: {err_resp}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_tcp_unlimited_requests_when_limit_zero() {
        // 0 = unlimited
        let config = ServerConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_max_requests_per_connection(0);
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;

        // Send 5 requests, all should succeed
        for _ in 0..5 {
            let response = send_request(addr, request).await;
            assert!(
                response.contains("\"result\""),
                "All requests should succeed with limit 0: {response}"
            );
        }

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_server_config_defaults() {
        let config = ServerConfig::default();
        assert_eq!(
            config.max_requests_per_connection,
            DEFAULT_MAX_REQUESTS_PER_CONNECTION
        );
        assert_eq!(config.drain_timeout_secs, DEFAULT_DRAIN_TIMEOUT_SECS);
    }

    #[tokio::test]
    async fn test_server_config_builder() {
        let config = ServerConfig::default()
            .with_max_requests_per_connection(500)
            .with_drain_timeout_secs(60);
        assert_eq!(config.max_requests_per_connection, 500);
        assert_eq!(config.drain_timeout_secs, 60);
    }

    #[tokio::test]
    async fn test_server_config_debug() {
        let config = ServerConfig::default();
        let debug = format!("{config:?}");
        assert!(
            debug.contains("max_requests_per_connection"),
            "Debug should show max_requests_per_connection: {debug}"
        );
        assert!(
            debug.contains("drain_timeout_secs"),
            "Debug should show drain_timeout_secs: {debug}"
        );
    }

    #[tokio::test]
    async fn test_shutdown_drains_inflight_connections() {
        let config = ServerConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_drain_timeout_secs(5);
        let handle = serve(config).await.unwrap();
        let addr = handle.local_addr();

        // Start a request that will be in-flight
        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;
        let response = send_request(addr, request).await;
        assert!(
            response.contains("\"result\""),
            "Pre-shutdown request should succeed: {response}"
        );

        // Shutdown should complete cleanly (drain has nothing to wait for since
        // the request above already completed)
        handle.shutdown();
    }
}
