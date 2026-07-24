// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WebSocket transport for clean JSON-RPC server
//!
//! Provides WebSocket connectivity with streaming support for progress notifications.
//!
//! # Protocol
//!
//! Messages are JSON-RPC 2.0 over WebSocket text frames.
//!
//! # Streaming Notifications
//!
//! For long-running operations, the server sends progress notifications:
//!
//! ```json
//! {"jsonrpc": "2.0", "method": "progress", "params": {"requestId": 1, "message": "Checking..."}}
//! ```
//!
//! The final result is sent as a normal JSON-RPC response.
//!
//! # Methods with Progress Support
//!
//! Methods supporting progress are defined in [`crate::registry::METHOD_REGISTRY`].
//! Use [`crate::registry::progress_methods()`] to get the current list.
//!
//! Currently: `prove`, `batchCheck`, `batchVerifyCert`, `batchVerifyCertArchive`,
//! `verifyC`, `batchProveTLA`, `batchGetPremises`
//!
//! # JSON-RPC Batch Mode and Progress Streaming
//!
//! JSON-RPC batch framing (`[{request1}, {request2}, ...]`) streams progress
//! notifications for each request that supports them, followed by a single batch
//! response array once all requests complete. Progress notifications include the
//! `requestId`, so clients can attribute updates when multiple long-running
//! requests are batched together.
//!
//! Methods are marked as "batch-safe" in [`crate::registry::METHOD_REGISTRY`] if
//! they work correctly in batch mode. When batch requests include non-batch-safe
//! methods that expect responses, the server emits a warning listing them. Use
//! [`crate::registry::is_batch_safe()`] to check programmatically.

use crate::handlers::ServerState;
use crate::progress::{ProgressSender, ProgressUpdate};
use crate::rpc::{
    parse_message, BatchItem, BatchResponse, ParsedMessage, RequestId, Response, RpcError,
};
use futures_util::{SinkExt, StreamExt};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{mpsc, Semaphore};
use tokio_tungstenite::{accept_async, tungstenite::Message};
use tracing::{debug, error, info, instrument, warn};

/// Progress notification sent during long-running operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProgressNotification {
    /// JSON-RPC version
    pub jsonrpc: String,
    /// Method name (always "progress")
    pub method: String,
    /// Progress parameters
    pub params: ProgressParams,
}

/// Progress notification parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProgressParams {
    /// ID of the request this progress relates to
    #[serde(rename = "requestId")]
    pub request_id: RequestId,
    /// Progress message
    pub message: String,
    /// Progress percentage (0-100, if applicable)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub percentage: Option<u8>,
    /// Additional details
    #[serde(skip_serializing_if = "Option::is_none")]
    pub details: Option<serde_json::Value>,
}

impl ProgressNotification {
    /// Create a new progress notification
    pub fn new(request_id: RequestId, message: impl Into<String>) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            method: "progress".to_string(),
            params: ProgressParams {
                request_id,
                message: message.into(),
                percentage: None,
                details: None,
            },
        }
    }

    /// Create a progress notification with percentage
    pub fn with_percentage(
        request_id: RequestId,
        message: impl Into<String>,
        percentage: u8,
    ) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            method: "progress".to_string(),
            params: ProgressParams {
                request_id,
                message: message.into(),
                percentage: Some(percentage.min(100)),
                details: None,
            },
        }
    }
}

impl From<ProgressUpdate> for ProgressNotification {
    fn from(update: ProgressUpdate) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            method: "progress".to_string(),
            params: ProgressParams {
                request_id: update.request_id,
                message: update.message,
                percentage: update.percentage,
                details: update.details,
            },
        }
    }
}

/// WebSocket server configuration
#[derive(Clone)]
pub struct WebSocketConfig {
    /// Address to bind to
    pub addr: SocketAddr,
    /// Enable GPU acceleration
    pub gpu_enabled: bool,
    /// Maximum concurrent connections
    pub max_concurrent: usize,
    /// Default timeout for operations (milliseconds)
    pub default_timeout_ms: u64,
    /// Number of worker threads for batch operations (0 = auto/Rayon default)
    pub worker_threads: usize,
    /// Optional pre-loaded environment
    pub initial_env: Option<clean_kernel::Environment>,
    /// Optional precomputed math-project theorem-index provider.
    pub project_theorem_index: Option<crate::proof_state::ProjectTheoremIndexProvider>,
    /// Maximum requests allowed per connection (0 = unlimited).
    pub max_requests_per_connection: u64,
    /// Graceful shutdown drain timeout in seconds.
    pub drain_timeout_secs: u64,
}

impl std::fmt::Debug for WebSocketConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WebSocketConfig")
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

impl Default for WebSocketConfig {
    fn default() -> Self {
        Self {
            addr: "127.0.0.1:8081".parse().expect("valid default address"),
            gpu_enabled: false,
            max_concurrent: 100,
            default_timeout_ms: 5000,
            worker_threads: 0,
            initial_env: None,
            project_theorem_index: None,
            max_requests_per_connection: crate::DEFAULT_MAX_REQUESTS_PER_CONNECTION,
            drain_timeout_secs: crate::DEFAULT_DRAIN_TIMEOUT_SECS,
        }
    }
}

impl WebSocketConfig {
    /// Create a new WebSocket config with the specified address
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

    /// Set maximum concurrent connections
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

/// WebSocket server handle
pub struct WebSocketHandle {
    /// Local address the server is bound to
    local_addr: SocketAddr,
    /// Shutdown signal sender
    shutdown_tx: Option<tokio::sync::oneshot::Sender<()>>,
}

impl WebSocketHandle {
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

/// Start the WebSocket server
#[instrument(skip(config))]
pub async fn serve_websocket(config: WebSocketConfig) -> Result<WebSocketHandle, WebSocketError> {
    let listener = TcpListener::bind(config.addr)
        .await
        .map_err(|e| WebSocketError::Bind(e.to_string()))?;

    let local_addr = listener.local_addr()?;
    info!("clean WebSocket server listening on {}", local_addr);

    let initial_env = config.initial_env.unwrap_or_default();
    let mut state = ServerState::new();
    state.env = Arc::new(tokio::sync::RwLock::new(initial_env));
    state.default_timeout_ms = config.default_timeout_ms;
    state.gpu_enabled = config.gpu_enabled;
    state.worker_threads = config.worker_threads;
    state.metrics = crate::handlers::ServerMetrics::new();
    state.proof_cache = crate::proof_state::ProofStateCache::default_config();
    if let Some(project_theorem_index) = config.project_theorem_index {
        state.theorem_index = project_theorem_index;
    }
    state.cache_metrics = crate::handlers::CacheMetrics::default();
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
                            debug!("New WebSocket connection from {}", peer_addr);
                            let state = Arc::clone(&state);
                            let permit = semaphore.clone().acquire_owned().await;
                            let n = Arc::clone(&notify_loop);
                            let c = Arc::clone(&count_loop);
                            c.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            tokio::spawn(async move {
                                let _permit = permit;
                                if let Err(e) = handle_websocket_connection(stream, state, max_requests).await {
                                    warn!("WebSocket error from {}: {}", peer_addr, e);
                                }
                                debug!("WebSocket connection closed: {}", peer_addr);
                                if c.fetch_sub(1, std::sync::atomic::Ordering::AcqRel) == 1 {
                                    n.notify_waiters();
                                }
                            });
                        }
                        Err(e) => error!("Accept error: {}", e),
                    }
                }
                _ = &mut shutdown_rx => {
                    info!("WebSocket server shutting down — draining in-flight connections");
                    break;
                }
            }
        }
        crate::drain_inflight(&count_loop, &notify_loop, drain_timeout, "WebSocket").await;
    });

    Ok(WebSocketHandle {
        local_addr,
        shutdown_tx: Some(shutdown_tx),
    })
}

/// Handle a single WebSocket connection
#[instrument(skip(stream, state))]
async fn handle_websocket_connection(
    stream: TcpStream,
    state: Arc<ServerState>,
    max_requests: u64,
) -> Result<(), WebSocketError> {
    let ws_stream = accept_async(stream)
        .await
        .map_err(|e| WebSocketError::Handshake(e.to_string()))?;

    let (mut ws_sender, mut ws_receiver) = ws_stream.split();

    // Channel for sending responses back to the WebSocket
    let (tx, mut rx) = mpsc::channel::<String>(32);

    // Spawn a task to send responses
    let sender_task = tokio::spawn(async move {
        while let Some(msg) = rx.recv().await {
            if ws_sender.send(Message::Text(msg.into())).await.is_err() {
                break;
            }
        }
        ws_sender
    });

    let mut request_count: u64 = 0;

    // Process incoming messages
    while let Some(msg) = ws_receiver.next().await {
        match msg {
            Ok(Message::Text(text)) => {
                // Enforce per-connection request limit (0 = unlimited)
                request_count = request_count.saturating_add(1);
                if max_requests > 0 && request_count > max_requests {
                    warn!(
                        "WebSocket per-connection request limit ({}) exceeded",
                        max_requests
                    );
                    let err_response = Response::error(
                        RequestId::Null,
                        RpcError::request_limit_exceeded(max_requests),
                    );
                    send_serialized(&err_response, RequestId::Null, &tx).await;
                    break;
                }

                let tx = tx.clone();
                let state = Arc::clone(&state);

                // Process message and send response(s)
                process_websocket_message(&text, &state, tx).await;
            }
            Ok(Message::Close(_)) => {
                debug!("Client requested close");
                break;
            }
            Ok(Message::Ping(data)) => {
                // Pong is handled automatically by tungstenite
                debug!("Received ping: {:?}", data);
            }
            Ok(Message::Pong(_)) => {
                debug!("Received pong");
            }
            Ok(Message::Binary(_)) => {
                warn!("Received binary message, ignoring");
            }
            Ok(Message::Frame(_)) => {
                // Internal frame, ignore
            }
            Err(e) => {
                error!("WebSocket error: {}", e);
                break;
            }
        }
    }

    // clean up sender task
    drop(tx);
    let _ = sender_task.await;

    Ok(())
}

/// Serialize a value and send it over the WebSocket channel. On serialization
/// failure, sends a JSON-RPC internal error response so the client is not left
/// hanging.
async fn send_serialized(
    value: &impl Serialize,
    fallback_id: RequestId,
    tx: &mpsc::Sender<String>,
) {
    match serde_json::to_string(value) {
        Ok(json) => {
            let _ = tx.send(json).await;
        }
        Err(e) => {
            error!("Failed to serialize response: {}", e);
            let err = Response::error(
                fallback_id,
                RpcError::internal_error(format!("Response serialization failed: {e}")),
            );
            if let Ok(json) = serde_json::to_string(&err) {
                let _ = tx.send(json).await;
            }
        }
    }
}

/// Process a WebSocket message and send response(s)
async fn process_websocket_message(json: &str, state: &ServerState, tx: mpsc::Sender<String>) {
    match parse_message(json) {
        Ok(ParsedMessage::Single(request)) => {
            if request.is_notification() {
                let _ = crate::dispatch::dispatch_request(
                    &request.method,
                    request.params,
                    RequestId::Null,
                    state,
                    None,
                )
                .await;
            } else {
                let id = request.id.clone().unwrap_or(RequestId::Null);
                dispatch_request_ws(&request.method, request.params, id, state, tx).await;
            }
        }
        Ok(ParsedMessage::Batch(items)) => {
            let mut responses = Vec::with_capacity(items.len());
            let mut non_batch_safe = BTreeMap::<String, usize>::new();
            for item in items {
                match item {
                    BatchItem::Request(request) => {
                        let is_notification = request.is_notification();
                        let method = request.method;
                        let params = request.params;
                        let id = request.id.unwrap_or(RequestId::Null);

                        if is_notification {
                            let _ = crate::dispatch::dispatch_request(
                                &method,
                                params,
                                RequestId::Null,
                                state,
                                None,
                            )
                            .await;
                            continue;
                        }

                        let response =
                            dispatch_request_ws_batch(&method, params, id, state, tx.clone()).await;
                        responses.push(response);

                        if !crate::registry::is_batch_safe(&method) {
                            *non_batch_safe.entry(method).or_insert(0) += 1;
                        }
                    }
                    BatchItem::Error(err) => {
                        responses.push(Response::error(RequestId::Null, err));
                    }
                }
            }
            if !non_batch_safe.is_empty() {
                let summary = non_batch_safe
                    .iter()
                    .map(|(method, count)| format!("{method}x{count}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                warn!(
                    "Batch request contains non-batch-safe methods ({summary}). Responses will \
                     be returned, but semantics may be degraded; consider single-request \
                     framing for these methods."
                );
            }
            if !responses.is_empty() {
                send_serialized(&BatchResponse(responses), RequestId::Null, &tx).await;
            }
        }
        Err(e) => {
            let response = Response::error(RequestId::Null, e);
            send_serialized(&response, RequestId::Null, &tx).await;
        }
    }
}

/// Shared progress-channel setup/execute/teardown for WebSocket dispatch.
///
/// Spawns a forwarder that streams `ProgressNotification`s to `tx`, runs the
/// handler, then joins the forwarder before returning the response. Both the
/// fire-and-forget (`dispatch_request_ws`) and batch (`dispatch_request_ws_batch`)
/// entry points share this body so their progress lifecycles cannot drift.
async fn run_ws_with_progress(
    method: &str,
    params: Option<serde_json::Value>,
    id: RequestId,
    state: &ServerState,
    tx: &mpsc::Sender<String>,
) -> Response {
    // Use centralized registry as single source of truth for progress support
    let wants_progress = crate::registry::supports_progress(method);
    let can_stream_progress = wants_progress && !matches!(id, RequestId::Null);

    let (progress_sender, mut progress_task) = if can_stream_progress {
        let (progress_tx, mut progress_rx) = mpsc::channel::<ProgressUpdate>(32);
        let forward_tx = tx.clone();
        let handle = tokio::spawn(async move {
            while let Some(update) = progress_rx.recv().await {
                let notification: ProgressNotification = update.into();
                if let Ok(json) = serde_json::to_string(&notification) {
                    if forward_tx.send(json).await.is_err() {
                        break;
                    }
                }
            }
        });
        (
            Some(ProgressSender::new(id.clone(), progress_tx)),
            Some(handle),
        )
    } else {
        (None, None)
    };

    if can_stream_progress {
        if let Some(progress) = progress_sender.as_ref() {
            progress.notify("Starting...", Some(0), None).await;
        }
    }

    // Execute the actual handler
    let response =
        crate::dispatch::dispatch_request(method, params, id, state, progress_sender.clone()).await;

    drop(progress_sender);
    if let Some(task) = progress_task.take() {
        let _ = task.await;
    }
    response
}

/// Dispatch a request with progress notifications
async fn dispatch_request_ws(
    method: &str,
    params: Option<serde_json::Value>,
    id: RequestId,
    state: &ServerState,
    tx: mpsc::Sender<String>,
) {
    let response = run_ws_with_progress(method, params, id, state, &tx).await;
    // Send the response after all progress messages have been forwarded
    let fallback_id = response.id.clone();
    send_serialized(&response, fallback_id, &tx).await;
}

/// Dispatch a request within a JSON-RPC batch, streaming progress but returning the response.
async fn dispatch_request_ws_batch(
    method: &str,
    params: Option<serde_json::Value>,
    id: RequestId,
    state: &ServerState,
    tx: mpsc::Sender<String>,
) -> Response {
    run_ws_with_progress(method, params, id, state, &tx).await
}

/// Errors that can occur during WebSocket server operation.
///
/// These errors are specific to the WebSocket transport layer, including
/// connection establishment and upgrade handshake failures.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum WebSocketError {
    /// Failed to bind the WebSocket server to the specified address.
    #[error("Failed to bind to address: {0}")]
    Bind(String),
    /// WebSocket protocol upgrade handshake failed.
    #[error("WebSocket handshake failed: {0}")]
    Handshake(String),
    /// An I/O error occurred during WebSocket communication.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures_util::{SinkExt, StreamExt};
    use std::sync::atomic::Ordering;
    use tokio_tungstenite::connect_async;

    // ════════════════════════════════════════════════════════════════════════════
    // Unit tests for ProgressNotification
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_progress_notification_new() {
        let notif = ProgressNotification::new(RequestId::Number(42), "Testing...");

        assert_eq!(notif.jsonrpc, "2.0");
        assert_eq!(notif.method, "progress");
        assert_eq!(notif.params.request_id, RequestId::Number(42));
        assert_eq!(notif.params.message, "Testing...");
        assert_eq!(
            notif.params.percentage, None,
            "basic notification should have no percentage"
        );
        assert_eq!(
            notif.params.details, None,
            "basic notification should have no details"
        );
    }

    #[test]
    fn test_progress_notification_with_percentage() {
        let notif = ProgressNotification::with_percentage(
            RequestId::String("req1".to_string()),
            "Loading",
            75,
        );

        assert_eq!(
            notif.params.request_id,
            RequestId::String("req1".to_string())
        );
        assert_eq!(notif.params.message, "Loading");
        assert_eq!(notif.params.percentage, Some(75));
    }

    #[test]
    fn test_progress_notification_percentage_clamped_to_100() {
        let notif = ProgressNotification::with_percentage(RequestId::Number(1), "Over", 150);

        // Should be clamped to 100
        assert_eq!(notif.params.percentage, Some(100));
    }

    #[test]
    fn test_progress_notification_serializes_correctly() {
        let notif = ProgressNotification::new(RequestId::Number(1), "Working");
        let json = serde_json::to_string(&notif).unwrap();

        assert!(json.contains("\"jsonrpc\":\"2.0\""));
        assert!(json.contains("\"method\":\"progress\""));
        assert!(json.contains("\"requestId\":1"));
        assert!(json.contains("\"message\":\"Working\""));
        // percentage should be absent (skip_serializing_if = None)
        assert!(!json.contains("percentage"));
    }

    #[test]
    fn test_progress_notification_with_percentage_serializes() {
        let notif = ProgressNotification::with_percentage(RequestId::Number(2), "Progress", 50);
        let json = serde_json::to_string(&notif).unwrap();

        assert!(json.contains("\"percentage\":50"));
    }

    #[test]
    fn test_progress_notification_from_progress_update() {
        let update = ProgressUpdate {
            request_id: RequestId::Number(99),
            message: "Converting".to_string(),
            percentage: Some(33),
            details: Some(serde_json::json!({"step": 1})),
        };
        let notif: ProgressNotification = update.into();

        assert_eq!(notif.params.request_id, RequestId::Number(99));
        assert_eq!(notif.params.message, "Converting");
        assert_eq!(notif.params.percentage, Some(33));
        assert!(
            notif.params.details.is_some(),
            "update with details should preserve them"
        );
    }

    #[test]
    fn test_websocket_config_defaults() {
        let config = WebSocketConfig::default();

        assert_eq!(config.max_concurrent, 100);
        assert!(!config.gpu_enabled);
        assert_eq!(
            config.max_requests_per_connection,
            crate::DEFAULT_MAX_REQUESTS_PER_CONNECTION
        );
        assert_eq!(config.drain_timeout_secs, crate::DEFAULT_DRAIN_TIMEOUT_SECS);
    }

    #[test]
    fn test_websocket_config_builder_pattern() {
        let config = WebSocketConfig::default()
            .with_addr("127.0.0.1:9999".parse().unwrap())
            .with_max_concurrent(50)
            .with_gpu(true)
            .with_max_requests_per_connection(500)
            .with_drain_timeout_secs(60);

        assert_eq!(config.addr.port(), 9999);
        assert_eq!(config.max_concurrent, 50);
        assert!(config.gpu_enabled);
        assert_eq!(config.max_requests_per_connection, 500);
        assert_eq!(config.drain_timeout_secs, 60);
    }

    #[test]
    fn test_websocket_config_debug() {
        let config = WebSocketConfig::default();
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

    // ════════════════════════════════════════════════════════════════════════════
    // Integration tests (async)
    // ════════════════════════════════════════════════════════════════════════════

    async fn connect_and_send(addr: SocketAddr, request: &str) -> Vec<String> {
        let url = format!("ws://{addr}");
        let (mut ws_stream, _) = connect_async(&url).await.unwrap();

        ws_stream
            .send(Message::Text(request.to_string().into()))
            .await
            .unwrap();

        let mut responses = Vec::new();
        // Give server time to respond
        let timeout = tokio::time::timeout(std::time::Duration::from_secs(2), async {
            while let Some(msg) = ws_stream.next().await {
                match msg {
                    Ok(Message::Text(text)) => {
                        responses.push(text.to_string());
                        // For simple requests, one response is enough
                        if !responses.is_empty() {
                            break;
                        }
                    }
                    Ok(Message::Close(_)) => break,
                    _ => {}
                }
            }
        });
        let _ = timeout.await;

        ws_stream.close(None).await.ok();
        responses
    }

    #[tokio::test]
    async fn test_websocket_server_check() {
        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        // Use fully-typed expression
        let request = r#"{"jsonrpc": "2.0", "method": "check", "params": {"code": "fun (A : Type) (x : A) => x"}, "id": 1}"#;
        let responses = connect_and_send(addr, request).await;

        assert!(
            !responses.is_empty(),
            "Should receive at least one response"
        );
        let response = &responses[0];
        assert!(response.contains("\"result\""), "Response: {response}");
        assert!(response.contains("\"valid\":true"), "Response: {response}");

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_server_info() {
        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;
        let responses = connect_and_send(addr, request).await;

        assert!(!responses.is_empty());
        assert!(responses[0].contains("clean-server"));
        assert!(responses[0].contains("\"methods\""));

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_dispatch_supports_server_info_methods() {
        let state = ServerState::new();
        let response = crate::handlers::handle_server_info(&state, RequestId::Number(1)).await;

        let info: crate::handlers::ServerInfo =
            serde_json::from_value(response.result.unwrap()).unwrap();

        for (idx, method) in info.methods.iter().enumerate() {
            let response = crate::dispatch::dispatch_request(
                method,
                None,
                RequestId::Number(idx as i64 + 1),
                &state,
                None,
            )
            .await;

            if let Some(error) = response.error {
                assert_ne!(
                    error.code,
                    crate::rpc::error_codes::METHOD_NOT_FOUND,
                    "serverInfo advertises {method}, but dispatch is missing it"
                );
            }
        }
    }

    /// Regression test: all registry-defined aliases are accepted by dispatch.
    ///
    /// This complements `test_websocket_dispatch_supports_server_info_methods` which
    /// only checks canonical names. Aliases can silently regress without this test
    /// because they're not advertised in serverInfo (Part of #1380).
    #[tokio::test]
    async fn test_websocket_dispatch_supports_alias_methods() {
        let state = ServerState::new();

        for (alias, canonical) in crate::registry::all_aliases() {
            let response =
                crate::dispatch::dispatch_request(alias, None, RequestId::Number(1), &state, None)
                    .await;

            if let Some(error) = response.error {
                assert_ne!(
                    error.code,
                    crate::rpc::error_codes::METHOD_NOT_FOUND,
                    "Registry alias '{}' (canonical: '{}') not handled by dispatch",
                    alias,
                    canonical
                );
            }
        }
    }

    #[tokio::test]
    async fn test_websocket_method_not_found() {
        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "unknownMethod", "id": 1}"#;
        let responses = connect_and_send(addr, request).await;

        assert!(!responses.is_empty());
        assert!(responses[0].contains("\"error\""));
        assert!(responses[0].contains("-32601")); // METHOD_NOT_FOUND

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_batch_progress_streaming() {
        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let url = format!("ws://{addr}");
        let (mut ws_stream, _) = connect_async(&url).await.unwrap();

        let request = r#"{"jsonrpc": "2.0", "method": "batchCheck", "params": {"items": [{"id": "1", "code": "fun (A : Type) (x : A) => x"}, {"id": "2", "code": "Type"}]}, "id": 42}"#;
        ws_stream
            .send(Message::Text(request.to_string().into()))
            .await
            .unwrap();

        let mut saw_progress = false;
        let mut saw_result = false;
        let mut seen = Vec::new();

        let timeout = tokio::time::timeout(std::time::Duration::from_secs(3), async {
            while let Some(msg) = ws_stream.next().await {
                match msg {
                    Ok(Message::Text(text)) => {
                        if text.contains("\"method\":\"progress\"") {
                            saw_progress = true;
                        }
                        if text.contains("\"result\"") && text.contains("\"results\"") {
                            saw_result = true;
                            seen.push(text);
                            break;
                        }
                        seen.push(text);
                    }
                    Ok(Message::Close(_)) => break,
                    _ => {}
                }
            }
        });
        let _ = timeout.await;

        ws_stream.close(None).await.ok();

        assert!(saw_progress, "Expected progress notification, got {seen:?}");
        assert!(saw_result, "Expected final response, got {seen:?}");

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_batch_notification_dispatches() {
        let state = ServerState::new();
        let (tx, mut rx) = mpsc::channel(4);

        let request = r#"[{"jsonrpc": "2.0", "method": "check", "params": {"code": "fun (A : Type) (x : A) => x"}},{"jsonrpc": "2.0", "method": "check", "params": {"code": "fun (A : Type) (x : A) => x"}, "id": 1}]"#;

        process_websocket_message(request, &state, tx).await;

        let _ = rx.recv().await;

        let check_count = state.metrics.check_requests.load(Ordering::Relaxed);
        assert!(
            check_count >= 2,
            "Expected notification + request to dispatch, saw {check_count}"
        );
    }

    #[tokio::test]
    async fn test_websocket_batch_null_id_is_notification() {
        let state = ServerState::new();
        let (tx, mut rx) = mpsc::channel(4);

        let request = r#"[{"jsonrpc": "2.0", "method": "getType", "params": {"code": "Type"}, "id": null},{"jsonrpc": "2.0", "method": "getType", "params": {"code": "Type"}, "id": 7}]"#;

        process_websocket_message(request, &state, tx).await;

        let response = rx.recv().await.expect("expected batch response");
        let value: serde_json::Value = serde_json::from_str(&response).unwrap();
        let arr = value.as_array().expect("batch response should be array");
        assert_eq!(arr.len(), 1, "Expected only one response, got {arr:?}");
        assert_eq!(arr[0].get("id"), Some(&serde_json::Value::Number(7.into())));
        assert!(rx.try_recv().is_err(), "Expected only one batch response");
    }

    #[tokio::test]
    async fn test_websocket_batch_with_invalid_item() {
        let state = ServerState::new();
        let (tx, mut rx) = mpsc::channel(4);

        // Batch with one valid and one invalid request
        let request =
            r#"[{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}, {"not_valid": true}]"#;

        process_websocket_message(request, &state, tx).await;

        let response = rx.recv().await.expect("expected batch response");
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

        assert!(rx.try_recv().is_err(), "Expected only one batch response");
    }

    #[tokio::test]
    async fn test_websocket_batch_with_invalid_jsonrpc_version() {
        let state = ServerState::new();
        let (tx, mut rx) = mpsc::channel(4);

        // Batch with one valid and one with invalid jsonrpc version
        let request = r#"[{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}, {"jsonrpc": "1.0", "method": "serverInfo", "id": 2}]"#;

        process_websocket_message(request, &state, tx).await;

        let response = rx.recv().await.expect("expected batch response");
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
        // Error should contain reference to invalid jsonrpc version
        let msg = error.get("message").unwrap().as_str().unwrap();
        assert!(
            msg.contains("jsonrpc") || msg.contains("version"),
            "Expected jsonrpc version error: {msg}"
        );

        assert!(rx.try_recv().is_err(), "Expected only one batch response");
    }

    #[tokio::test]
    async fn test_websocket_batch_with_primitive_items() {
        let state = ServerState::new();
        let (tx, mut rx) = mpsc::channel(8);

        // Batch with valid request mixed with primitive types (not objects)
        // Per JSON-RPC 2.0, batch items must be Request objects
        let request =
            r#"[{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}, 42, "string", true, null]"#;

        process_websocket_message(request, &state, tx).await;

        let response = rx.recv().await.expect("expected batch response");
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

        assert!(rx.try_recv().is_err(), "Expected only one batch response");
    }

    #[tokio::test]
    async fn test_websocket_jsonrpc_batch_streams_progress() {
        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let url = format!("ws://{addr}");
        let (mut ws_stream, _) = connect_async(&url).await.unwrap();

        let request = r#"[{"jsonrpc": "2.0", "method": "batchCheck", "params": {"items": [{"id": "1", "code": "fun (A : Type) (x : A) => x"}, {"id": "2", "code": "Type"}]}, "id": 1}, {"jsonrpc": "2.0", "method": "getType", "params": {"code": "Type"}, "id": 2}]"#;
        ws_stream
            .send(Message::Text(request.to_string().into()))
            .await
            .unwrap();

        let mut saw_progress = false;
        let mut saw_batch = false;
        let mut seen = Vec::new();

        let timeout = tokio::time::timeout(std::time::Duration::from_secs(3), async {
            while let Some(msg) = ws_stream.next().await {
                match msg {
                    Ok(Message::Text(text)) => {
                        if text.contains("\"method\":\"progress\"") {
                            saw_progress = true;
                        }
                        if text.trim_start().starts_with('[') {
                            saw_batch = true;
                            seen.push(text);
                            break;
                        }
                        seen.push(text);
                    }
                    Ok(Message::Close(_)) => break,
                    _ => {}
                }
            }
        });
        let _ = timeout.await;

        ws_stream.close(None).await.ok();

        assert!(saw_progress, "Expected progress notification, got {seen:?}");
        assert!(saw_batch, "Expected batch response, got {seen:?}");

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_invalid_json() {
        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r"{invalid json";
        let responses = connect_and_send(addr, request).await;

        assert!(!responses.is_empty());
        assert!(responses[0].contains("\"error\""));
        assert!(responses[0].contains("-32700")); // PARSE_ERROR

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_progress_notification_struct() {
        let progress = ProgressNotification::new(RequestId::Number(42), "Testing...");
        let json = serde_json::to_string(&progress).unwrap();

        assert!(json.contains("\"jsonrpc\":\"2.0\""));
        assert!(json.contains("\"method\":\"progress\""));
        assert!(json.contains("\"requestId\":42"));
        assert!(json.contains("\"message\":\"Testing...\""));
    }

    #[tokio::test]
    async fn test_progress_with_percentage() {
        let progress = ProgressNotification::with_percentage(
            RequestId::String("req-1".into()),
            "Processing",
            50,
        );
        let json = serde_json::to_string(&progress).unwrap();

        assert!(json.contains("\"percentage\":50"));
        assert!(json.contains("\"requestId\":\"req-1\""));
    }

    #[tokio::test]
    async fn test_websocket_batch_verify_cert_progress_streaming() {
        use clean_kernel::cert::ProofCert;
        use clean_kernel::{Expr, ExprKind, Level};

        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let url = format!("ws://{addr}");
        let (mut ws_stream, _) = connect_async(&url).await.unwrap();

        // Construct valid certificates for Sort(0) : Sort(1)
        let level = Level::zero();
        let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
        let cert = ProofCert::Sort {
            level: level.clone(),
        };

        let item1 = crate::handlers::BatchVerifyCertItem {
            id: "cert1".to_string(),
            cert: cert.clone(),
            expr: expr.clone(),
        };
        let item2 = crate::handlers::BatchVerifyCertItem {
            id: "cert2".to_string(),
            cert,
            expr,
        };

        let params = crate::handlers::BatchVerifyCertParams {
            items: vec![item1, item2],
            threads: 0,
            timeout_ms: None,
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchVerifyCert", "params": {params_json}, "id": 42}}"#
        );

        ws_stream.send(Message::Text(request.into())).await.unwrap();

        let mut saw_progress = false;
        let mut saw_result = false;
        let mut seen = Vec::new();

        let timeout = tokio::time::timeout(std::time::Duration::from_secs(3), async {
            while let Some(msg) = ws_stream.next().await {
                match msg {
                    Ok(Message::Text(text)) => {
                        if text.contains("\"method\":\"progress\"") {
                            saw_progress = true;
                        }
                        if text.contains("\"result\"") && text.contains("\"results\"") {
                            saw_result = true;
                            seen.push(text);
                            break;
                        }
                        seen.push(text);
                    }
                    Ok(Message::Close(_)) => break,
                    _ => {}
                }
            }
        });
        let _ = timeout.await;

        ws_stream.close(None).await.ok();

        assert!(
            saw_progress,
            "Expected progress notification for batchVerifyCert, got {seen:?}"
        );
        assert!(
            saw_result,
            "Expected final response for batchVerifyCert, got {seen:?}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_batch_get_premises_progress_streaming() {
        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let url = format!("ws://{addr}");
        let (mut ws_stream, _) = connect_async(&url).await.unwrap();

        let params = crate::handlers::BatchGetPremisesParams {
            items: vec![
                crate::handlers::BatchGetPremisesItem {
                    id: "goal1".to_string(),
                    goal: "Prop".to_string(),
                },
                crate::handlers::BatchGetPremisesItem {
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
            r#"{{"jsonrpc": "2.0", "method": "batchGetPremises", "params": {params_json}, "id": 42}}"#
        );

        ws_stream.send(Message::Text(request.into())).await.unwrap();

        let mut saw_progress = false;
        let mut saw_result = false;
        let mut seen = Vec::new();

        let timeout = tokio::time::timeout(std::time::Duration::from_secs(3), async {
            while let Some(msg) = ws_stream.next().await {
                match msg {
                    Ok(Message::Text(text)) => {
                        if text.contains("\"method\":\"progress\"") {
                            saw_progress = true;
                        }
                        if text.contains("\"result\"") && text.contains("\"results\"") {
                            saw_result = true;
                            seen.push(text);
                            break;
                        }
                        seen.push(text);
                    }
                    Ok(Message::Close(_)) => break,
                    _ => {}
                }
            }
        });
        let _ = timeout.await;

        ws_stream.close(None).await.ok();

        assert!(
            saw_progress,
            "Expected progress notification for batchGetPremises, got {seen:?}"
        );
        assert!(
            saw_result,
            "Expected final response for batchGetPremises, got {seen:?}"
        );

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_batch_prove_tla_progress_streaming() {
        use clean_tla::encoding::TlaFormula;
        use clean_tla::obligation::TlaObligation;

        let config = WebSocketConfig::default().with_addr("127.0.0.1:0".parse().unwrap());
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let url = format!("ws://{addr}");
        let (mut ws_stream, _) = connect_async(&url).await.unwrap();

        // Create batch prove TLA request with multiple obligations
        let item1 = crate::handlers::BatchProveTlaItem {
            id: "ob1".to_string(),
            obligation: TlaObligation::new(TlaFormula::Always(Box::new(TlaFormula::True))),
        };
        let item2 = crate::handlers::BatchProveTlaItem {
            id: "ob2".to_string(),
            obligation: TlaObligation::new(TlaFormula::Eventually(Box::new(TlaFormula::True))),
        };
        let item3 = crate::handlers::BatchProveTlaItem {
            id: "ob3".to_string(),
            obligation: TlaObligation::new(TlaFormula::LeadsTo(
                Box::new(TlaFormula::True),
                Box::new(TlaFormula::True),
            )),
        };

        let params = crate::handlers::BatchProveTlaParams {
            items: vec![item1, item2, item3],
            threads: 0,
            timeout_ms: None,
        };
        let params_json = serde_json::to_string(&params).unwrap();
        let request = format!(
            r#"{{"jsonrpc": "2.0", "method": "batchProveTLA", "params": {params_json}, "id": 99}}"#
        );

        ws_stream.send(Message::Text(request.into())).await.unwrap();

        let mut saw_progress = false;
        let mut saw_per_item_progress = false;
        let mut saw_result = false;
        let mut seen = Vec::new();

        let timeout = tokio::time::timeout(std::time::Duration::from_secs(5), async {
            while let Some(msg) = ws_stream.next().await {
                match msg {
                    Ok(Message::Text(text)) => {
                        if text.contains("\"method\":\"progress\"") {
                            saw_progress = true;
                            // Check for per-item progress (contains item_id in details)
                            if text.contains("\"item_id\"") {
                                saw_per_item_progress = true;
                            }
                        }
                        if text.contains("\"result\"") && text.contains("\"results\"") {
                            saw_result = true;
                            seen.push(text);
                            break;
                        }
                        seen.push(text);
                    }
                    Ok(Message::Close(_)) => break,
                    _ => {}
                }
            }
        });
        let _ = timeout.await;

        ws_stream.close(None).await.ok();

        assert!(
            saw_progress,
            "Expected progress notification for batchProveTLA, got {seen:?}"
        );
        assert!(
            saw_per_item_progress,
            "Expected per-item progress notifications with item_id details, got {seen:?}"
        );
        assert!(
            saw_result,
            "Expected final response for batchProveTLA, got {seen:?}"
        );

        // Verify all obligations proved
        let final_response = &seen.last().unwrap();
        assert!(
            final_response.contains("\"all_proved\":true"),
            "Expected all_proved:true in response, got {final_response}"
        );

        handle.shutdown();
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Per-connection request limit and shutdown drain tests (WebSocket)
    // ════════════════════════════════════════════════════════════════════════════

    #[tokio::test]
    async fn test_websocket_per_connection_request_limit_enforced() {
        let config = WebSocketConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_max_requests_per_connection(3);
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let url = format!("ws://{addr}");
        let (mut ws_stream, _) = connect_async(&url).await.unwrap();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;

        let mut responses = Vec::new();

        // Send 4 requests (limit is 3)
        for i in 0..4 {
            if ws_stream
                .send(Message::Text(request.to_string().into()))
                .await
                .is_err()
            {
                // Connection may be closed after the limit error
                break;
            }
            // Read response
            let timeout_result = tokio::time::timeout(std::time::Duration::from_secs(2), async {
                while let Some(msg) = ws_stream.next().await {
                    match msg {
                        Ok(Message::Text(text)) => {
                            responses.push(text);
                            break;
                        }
                        Ok(Message::Close(_)) => break,
                        Err(_) => break,
                        _ => {}
                    }
                }
            })
            .await;
            if timeout_result.is_err() {
                break;
            }
            // If the last response was an error with limit exceeded, stop
            if i == 3 {
                break;
            }
        }

        // First 3 should succeed
        assert!(
            responses.len() >= 3,
            "Expected at least 3 responses, got {}: {:?}",
            responses.len(),
            responses
        );
        for resp in &responses[..3] {
            assert!(
                resp.contains("\"result\""),
                "First 3 should succeed: {resp}"
            );
        }

        // The 4th should be the limit error
        assert!(
            responses.len() == 4,
            "Expected exactly 4 responses (3 ok + 1 error), got {}: {:?}",
            responses.len(),
            responses
        );
        let err_resp = &responses[3];
        assert!(
            err_resp.contains("-32005"),
            "4th response should contain REQUEST_LIMIT_EXCEEDED code: {err_resp}"
        );

        ws_stream.close(None).await.ok();
        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_unlimited_requests_when_limit_zero() {
        let config = WebSocketConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_max_requests_per_connection(0);
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;

        // Send 5 requests, all should succeed
        for _ in 0..5 {
            let responses = connect_and_send(addr, request).await;
            assert!(
                !responses.is_empty(),
                "Should receive at least one response"
            );
            assert!(
                responses[0].contains("\"result\""),
                "All requests should succeed with limit 0: {}",
                responses[0]
            );
        }

        handle.shutdown();
    }

    #[tokio::test]
    async fn test_websocket_shutdown_drains_connections() {
        let config = WebSocketConfig::default()
            .with_addr("127.0.0.1:0".parse().unwrap())
            .with_drain_timeout_secs(5);
        let handle = serve_websocket(config).await.unwrap();
        let addr = handle.local_addr();

        // Start a request that will complete before shutdown
        let request = r#"{"jsonrpc": "2.0", "method": "serverInfo", "id": 1}"#;
        let responses = connect_and_send(addr, request).await;
        assert!(!responses.is_empty(), "Pre-shutdown request should succeed");

        // Shutdown should complete cleanly
        handle.shutdown();
    }
}
