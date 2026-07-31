// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean4-compatible RPC session endpoints for infoview
//!
//! Implements the `$/lean/rpc/*` protocol endpoints:
//! - `$/lean/rpc/connect` - Start RPC session for a document
//! - `$/lean/rpc/call` - Invoke registered RPC procedure
//! - `$/lean/rpc/release` - Release RPC object references
//! - `$/lean/rpc/keepAlive` - Keep session alive
//!
//! Protocol spec: designs/2026-02-01-lean-infoview-rpc-protocol.md
//!
//! Sources: Lean team, "Lean.Data.Lsp.Extra"
//! <https://lean-lang.org/doc/api/Lean/Data/Lsp/Extra.html>

use dashmap::DashMap;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};
use tower_lsp::lsp_types::{Position, Url};

/// RPC connect request params
/// Source: Lean.Data.Lsp.Extra, RpcConnectParams
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RpcConnectParams {
    /// Document URI to connect to
    pub uri: Url,
}

/// RPC connect response
/// Source: Lean.Data.Lsp.Extra, RpcConnected
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RpcConnected {
    /// Session identifier (UInt64 in Lean4)
    pub session_id: u64,
}

/// RPC call request params
/// Source: Lean.Data.Lsp.Extra, RpcCallParams
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RpcCallParams {
    /// Document being operated on
    pub text_document: TextDocumentIdentifier,
    /// Position in document
    pub position: Position,
    /// Session ID from connect
    pub session_id: u64,
    /// Fully-qualified method name (e.g., "Lean.Widget.getWidgets")
    pub method: String,
    /// Method-specific parameters
    #[serde(default)]
    pub params: Value,
}

/// Simplified text document identifier for RPC
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentIdentifier {
    /// Document URI
    pub uri: Url,
}

/// RPC release notification params
/// Source: Lean.Data.Lsp.Extra, RpcReleaseParams
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RpcReleaseParams {
    /// Document URI
    pub uri: Url,
    /// Session ID
    pub session_id: u64,
    /// References to release
    pub refs: Vec<RpcRef>,
}

/// RPC object reference
/// Source: Lean.Server.Rpc.Basic, RpcRef
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RpcRef {
    /// Reference pointer (opaque to client)
    pub p: u64,
}

/// RPC keepAlive notification params
/// Source: Lean.Data.Lsp.Extra, RpcKeepAliveParams
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RpcKeepAliveParams {
    /// Document URI
    pub uri: Url,
    /// Session ID
    pub session_id: u64,
}

// Note: RpcNeedsReconnect is not a separate struct in Lean4.
// The error is signaled via RpcError with code -32000 and message "RpcNeedsReconnect".
// See RpcError::needs_reconnect() for the implementation.

/// Widget source request params
/// Source: Lean.Widget.UserWidget, GetWidgetSourceParams
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetWidgetSourceParams {
    /// Hash of JS module
    pub hash: u64,
    /// Position in document
    pub pos: Position,
}

/// Widget source response
/// Source: Lean.Widget.UserWidget, WidgetSource
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WidgetSource {
    /// JavaScript source text
    pub sourcetext: String,
}

/// Get widgets response
/// Source: Lean.Widget.UserWidget, GetWidgetsResponse
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetWidgetsResponse {
    /// Panel widgets at position
    pub widgets: Vec<PanelWidgetInstance>,
}

/// Panel widget instance
/// Source: Lean.Widget.UserWidget, PanelWidgetInstance
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PanelWidgetInstance {
    /// Widget module name
    pub id: String,
    /// Hash of JS source
    pub javascript_hash: u64,
    /// Widget props (may contain RPC refs)
    pub props: Value,
    /// Optional range where widget is displayed
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<Range>,
    /// Deprecated: wraps widget in details/summary
    #[deprecated(since = "0.2.0", note = "Widget name field is no longer used")]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
}

/// LSP Range (simplified)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

// ============================================================================
// $/lean/plainGoal and $/lean/plainTermGoal endpoints
// ============================================================================

/// Request params for $/lean/plainGoal
/// Source: Lean.Data.Lsp.Extra, PlainGoalParams
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PlainGoalParams {
    /// Text document to query
    pub text_document: TextDocumentIdentifier,
    /// Position to query goals at
    pub position: Position,
}

/// Response for $/lean/plainGoal
/// Source: Lean.Data.Lsp.Extra, PlainGoal
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlainGoalResponse {
    /// List of tactic goals rendered as plain text
    /// None if there are no goals at this position
    #[serde(skip_serializing_if = "Option::is_none")]
    pub goals: Option<Vec<String>>,
}

/// Request params for $/lean/plainTermGoal
/// Source: Lean.Data.Lsp.Extra, PlainTermGoalParams
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PlainTermGoalParams {
    /// Text document to query
    pub text_document: TextDocumentIdentifier,
    /// Position to query expected type at
    pub position: Position,
}

/// Response for $/lean/plainTermGoal
/// Source: Lean.Data.Lsp.Extra, PlainTermGoal
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlainTermGoalResponse {
    /// Expected type rendered as plain text
    /// None if there is no expected type at this position
    #[serde(skip_serializing_if = "Option::is_none")]
    pub goal: Option<String>,
}

/// RPC session state
#[derive(Debug)]
struct RpcSession {
    /// Document URI this session is bound to
    uri: Url,
    /// Last activity timestamp
    last_activity: Instant,
    /// Object store for this session
    object_store: RpcObjectStore,
}

/// RPC object store - holds server-side values behind opaque `u64` references.
///
/// Lean4 widget RPC hands the client opaque reference ids (`RpcRef.p`) that
/// stand in for server-held values (e.g. interactive goal/expression trees).
/// The client later releases them via `$/lean/rpc/release`. This store maps
/// those ids to the held [`Value`]s.
///
/// References are allocated with a monotonically-increasing counter, so an id
/// is never reused even after the value it pointed to is released. That keeps
/// a stale client reference from silently resolving to a different object.
///
/// Backed by a [`DashMap`] for interior-mutable, thread-safe access, matching
/// the threading model of the surrounding [`RpcSessionManager`].
#[derive(Debug)]
pub(crate) struct RpcObjectStore {
    /// Next reference id to hand out. Starts at 1; `0` is reserved as a
    /// never-allocated sentinel for callers that need one.
    next_ref: AtomicU64,
    /// Live references keyed by their opaque id.
    objects: DashMap<u64, Value>,
}

impl Default for RpcObjectStore {
    fn default() -> Self {
        Self::new()
    }
}

impl RpcObjectStore {
    fn new() -> Self {
        Self {
            next_ref: AtomicU64::new(1),
            objects: DashMap::new(),
        }
    }

    /// Allocate a fresh reference for `value`, returning its opaque id.
    ///
    /// Ids are monotonically increasing and never reused.
    fn alloc(&self, value: Value) -> u64 {
        let id = self.next_ref.fetch_add(1, Ordering::SeqCst);
        self.objects.insert(id, value);
        id
    }

    /// Look up the value held behind `id`, cloning it for the caller.
    ///
    /// Returns `None` if `id` was never allocated or has already been released.
    fn get(&self, id: u64) -> Option<Value> {
        self.objects.get(&id).map(|entry| entry.value().clone())
    }

    /// Release the given references, dropping any values they held.
    ///
    /// Unknown or already-released ids are ignored, so repeated release
    /// notifications are idempotent.
    fn release(&self, refs: &[RpcRef]) {
        for r in refs {
            self.objects.remove(&r.p);
        }
    }
}

/// Session timeout (30 seconds = 3 missed keepAlives at 10s interval)
const SESSION_TIMEOUT: Duration = Duration::from_secs(30);

/// RPC session manager
/// Manages RPC sessions for all documents
pub struct RpcSessionManager {
    /// Next session ID
    next_session: AtomicU64,
    /// Active sessions by session ID
    sessions: DashMap<u64, RpcSession>,
    /// Registered widget instances and JavaScript sources
    widget_registry: WidgetRegistry,
    /// RPC procedure registry
    procedures: HashMap<String, RpcProcedure>,
}

/// RPC procedure type - function that handles an RPC call
type RpcProcedure =
    Box<dyn Fn(&RpcCallContext<'_>, Value) -> Result<Value, RpcError> + Send + Sync>;

/// Context passed to RPC procedures
///
/// Fields are populated for every call but not yet read by stub procedures.
/// When real widget procedures are implemented, they will use these fields.
pub(crate) struct RpcCallContext<'a> {
    /// Session ID
    pub session_id: u64,
    /// Document URI
    pub uri: &'a Url,
    /// Position in document
    pub position: Position,
    /// Object store for allocating references
    pub object_store: &'a RpcObjectStore,
    /// Widget instances and JS modules visible to infoview calls
    pub widget_registry: &'a WidgetRegistry,
}

/// In-memory widget registry used by infoview RPC procedures.
///
/// This records the Lean4-compatible data shape for panel widgets and widget
/// source lookup. The entries are explicit until elaboration can populate them.
#[derive(Debug, Default)]
pub(crate) struct WidgetRegistry {
    widgets_by_uri: DashMap<Url, Vec<PanelWidgetInstance>>,
    sources_by_hash: DashMap<u64, WidgetSource>,
}

impl WidgetRegistry {
    fn register_widget(&self, uri: Url, widget: PanelWidgetInstance) {
        self.widgets_by_uri.entry(uri).or_default().push(widget);
    }

    fn replace_widgets(&self, uri: Url, widgets: Vec<PanelWidgetInstance>) {
        if widgets.is_empty() {
            self.widgets_by_uri.remove(&uri);
        } else {
            self.widgets_by_uri.insert(uri, widgets);
        }
    }

    fn register_source(&self, hash: u64, source: WidgetSource) {
        self.sources_by_hash.insert(hash, source);
    }

    fn widgets_at(&self, uri: &Url, position: Position) -> Vec<PanelWidgetInstance> {
        self.widgets_by_uri
            .get(uri)
            .map(|widgets| {
                widgets
                    .iter()
                    .filter(|widget| {
                        widget
                            .range
                            .as_ref()
                            .is_none_or(|range| position_in_range(position, range))
                    })
                    .cloned()
                    .collect()
            })
            .unwrap_or_default()
    }

    fn source(&self, hash: u64) -> Option<WidgetSource> {
        self.sources_by_hash
            .get(&hash)
            .map(|source| source.value().clone())
    }
}

fn position_in_range(position: Position, range: &Range) -> bool {
    position_after_or_equal(position, range.start) && position_before(position, range.end)
}

fn position_after_or_equal(position: Position, boundary: Position) -> bool {
    position.line > boundary.line
        || (position.line == boundary.line && position.character >= boundary.character)
}

fn position_before(position: Position, boundary: Position) -> bool {
    position.line < boundary.line
        || (position.line == boundary.line && position.character < boundary.character)
}

/// RPC error
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RpcError {
    pub code: i32,
    pub message: String,
}

impl RpcError {
    pub fn needs_reconnect() -> Self {
        Self {
            code: -32000,
            message: "RpcNeedsReconnect".to_string(),
        }
    }

    pub fn method_not_found(method: &str) -> Self {
        Self {
            code: -32601,
            message: format!("Method not found: {method}"),
        }
    }

    pub fn invalid_params(msg: &str) -> Self {
        Self {
            code: -32602,
            message: msg.to_string(),
        }
    }

    /// Widget source not found (widget JS not registered)
    pub fn widget_source_not_found(hash: u64) -> Self {
        Self {
            code: -32001,
            message: format!("Widget source not found for hash {hash}"),
        }
    }
}

impl Default for RpcSessionManager {
    fn default() -> Self {
        Self::new()
    }
}

impl RpcSessionManager {
    /// Create a new session manager with default procedures
    pub fn new() -> Self {
        let mut manager = Self {
            next_session: AtomicU64::new(1),
            sessions: DashMap::new(),
            widget_registry: WidgetRegistry::default(),
            procedures: HashMap::new(),
        };
        manager.register_default_procedures();
        manager
    }

    /// Register a panel widget for a document.
    ///
    /// This is an explicit registry hook. It does not yet imply that widgets are
    /// populated from live elaboration state.
    pub(crate) fn register_panel_widget(&self, uri: Url, widget: PanelWidgetInstance) {
        self.widget_registry.register_widget(uri, widget);
    }

    /// Replace all panel widgets for a document.
    ///
    /// The LSP backend uses this to refresh document-backed widgets after
    /// elaboration. Direct test registration can still append individual
    /// widgets with `register_panel_widget`.
    pub(crate) fn replace_panel_widgets(&self, uri: Url, widgets: Vec<PanelWidgetInstance>) {
        self.widget_registry.replace_widgets(uri, widgets);
    }

    /// Register JavaScript source for a widget module hash.
    pub(crate) fn register_widget_source(&self, hash: u64, source: WidgetSource) {
        self.widget_registry.register_source(hash, source);
    }

    /// Register default RPC procedures
    fn register_default_procedures(&mut self) {
        // Lean.Widget.getWidgets - returns widgets at a position
        self.procedures.insert(
            "Lean.Widget.getWidgets".to_string(),
            Box::new(|ctx, _params| {
                let widgets = ctx.widget_registry.widgets_at(ctx.uri, ctx.position);
                serde_json::to_value(GetWidgetsResponse { widgets })
                    .map_err(|e| RpcError::invalid_params(&e.to_string()))
            }),
        );

        // Lean.Widget.getWidgetSource - returns JS source for a widget
        self.procedures.insert(
            "Lean.Widget.getWidgetSource".to_string(),
            Box::new(|ctx, params| {
                let params: GetWidgetSourceParams = serde_json::from_value(params)
                    .map_err(|e| RpcError::invalid_params(&e.to_string()))?;
                ctx.widget_registry
                    .source(params.hash)
                    .map(serde_json::to_value)
                    .transpose()
                    .map_err(|e| RpcError::invalid_params(&e.to_string()))?
                    .ok_or_else(|| RpcError::widget_source_not_found(params.hash))
            }),
        );
    }

    /// Handle $/lean/rpc/connect
    ///
    /// Opportunistically cleans up expired sessions on each connect to prevent
    /// unbounded session accumulation from clients that disconnect without
    /// sending `release` (#2054).
    pub fn connect(&self, params: RpcConnectParams) -> Result<RpcConnected, RpcError> {
        self.cleanup_expired();
        let session_id = self.next_session.fetch_add(1, Ordering::SeqCst);
        self.sessions.insert(
            session_id,
            RpcSession {
                uri: params.uri,
                last_activity: Instant::now(),
                object_store: RpcObjectStore::new(),
            },
        );
        Ok(RpcConnected { session_id })
    }

    /// Handle $/lean/rpc/call
    pub fn call(&self, params: RpcCallParams) -> Result<Value, RpcError> {
        // Validate session
        let mut session = self
            .sessions
            .get_mut(&params.session_id)
            .ok_or_else(RpcError::needs_reconnect)?;

        // Check session matches document
        if session.uri != params.text_document.uri {
            return Err(RpcError::needs_reconnect());
        }

        // Check session hasn't timed out
        if session.last_activity.elapsed() > SESSION_TIMEOUT {
            drop(session);
            self.sessions.remove(&params.session_id);
            return Err(RpcError::needs_reconnect());
        }

        // Update last activity
        session.last_activity = Instant::now();

        // Look up procedure
        let procedure = self
            .procedures
            .get(&params.method)
            .ok_or_else(|| RpcError::method_not_found(&params.method))?;

        // Create context
        let ctx = RpcCallContext {
            session_id: params.session_id,
            uri: &session.uri,
            position: params.position,
            object_store: &session.object_store,
            widget_registry: &self.widget_registry,
        };

        // Call procedure
        procedure(&ctx, params.params)
    }

    /// Handle $/lean/rpc/release (notification - no response)
    pub fn release(&self, params: RpcReleaseParams) {
        if let Some(session) = self.sessions.get(&params.session_id) {
            if session.uri == params.uri {
                session.object_store.release(&params.refs);
            }
        }
    }

    /// Handle $/lean/rpc/keepAlive (notification - no response)
    pub fn keep_alive(&self, params: RpcKeepAliveParams) {
        if let Some(mut session) = self.sessions.get_mut(&params.session_id) {
            if session.uri == params.uri {
                session.last_activity = Instant::now();
            }
        }
    }

    /// clean up expired sessions (call periodically)
    pub fn cleanup_expired(&self) {
        let expired: Vec<u64> = self
            .sessions
            .iter()
            .filter(|s| s.last_activity.elapsed() > SESSION_TIMEOUT)
            .map(|s| *s.key())
            .collect();

        for session_id in expired {
            self.sessions.remove(&session_id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rpc_connect() {
        let manager = RpcSessionManager::new();
        let params = RpcConnectParams {
            uri: Url::parse("file:///test.lean").unwrap(),
        };

        let result = manager.connect(params).unwrap();
        assert!(result.session_id > 0);
    }

    #[test]
    fn test_rpc_connect_cleans_expired_sessions_without_dropping_active_ones() {
        let manager = RpcSessionManager::new();
        let active = manager
            .connect(RpcConnectParams {
                uri: Url::parse("file:///active.lean").unwrap(),
            })
            .unwrap();
        let expired = manager
            .connect(RpcConnectParams {
                uri: Url::parse("file:///expired.lean").unwrap(),
            })
            .unwrap();

        manager
            .sessions
            .get_mut(&expired.session_id)
            .unwrap()
            .last_activity = Instant::now() - SESSION_TIMEOUT - Duration::from_secs(1);

        let next = manager
            .connect(RpcConnectParams {
                uri: Url::parse("file:///next.lean").unwrap(),
            })
            .unwrap();

        assert!(
            manager.sessions.contains_key(&active.session_id),
            "connect cleanup should not drop active RPC sessions"
        );
        assert!(
            !manager.sessions.contains_key(&expired.session_id),
            "connect cleanup should remove timed-out RPC sessions"
        );
        assert!(
            manager.sessions.contains_key(&next.session_id),
            "connect should register the newly opened RPC session"
        );
    }

    #[test]
    fn test_rpc_call_invalid_session() {
        let manager = RpcSessionManager::new();
        let params = RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///test.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: 999, // Invalid
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        };

        let result = manager.call(params);
        let err = result.unwrap_err();
        assert!(
            err.message.contains("Reconnect"),
            "expected Reconnect error, got: {}",
            err.message
        );
        assert!(
            manager.sessions.is_empty(),
            "invalid-session calls should not allocate or recover RPC session state"
        );
    }

    #[test]
    fn test_rpc_call_valid_session() {
        let manager = RpcSessionManager::new();

        // Connect first
        let connect_params = RpcConnectParams {
            uri: Url::parse("file:///test.lean").unwrap(),
        };
        let connected = manager.connect(connect_params).unwrap();

        // Call getWidgets
        let call_params = RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///test.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        };

        let result = manager.call(call_params).unwrap();
        // Should return empty widgets array
        let response: GetWidgetsResponse = serde_json::from_value(result).unwrap();
        assert!(response.widgets.is_empty());
    }

    #[test]
    fn test_rpc_call_unknown_method() {
        let manager = RpcSessionManager::new();

        let connect_params = RpcConnectParams {
            uri: Url::parse("file:///test.lean").unwrap(),
        };
        let connected = manager.connect(connect_params).unwrap();

        let call_params = RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///test.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: connected.session_id,
            method: "Unknown.Method".to_string(),
            params: Value::Null,
        };

        let result = manager.call(call_params);
        let err = result.unwrap_err();
        assert!(
            err.message.contains("Method not found"),
            "expected 'Method not found' error, got: {}",
            err.message
        );

        let follow_up = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///test.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        assert!(
            follow_up.is_ok(),
            "unsupported RPC methods should not invalidate the active infoview session"
        );
    }

    #[test]
    fn test_rpc_release() {
        let manager = RpcSessionManager::new();

        let connect_params = RpcConnectParams {
            uri: Url::parse("file:///test.lean").unwrap(),
        };
        let connected = manager.connect(connect_params).unwrap();

        let release_params = RpcReleaseParams {
            uri: Url::parse("file:///test.lean").unwrap(),
            session_id: connected.session_id,
            refs: vec![RpcRef { p: 1 }, RpcRef { p: 2 }],
        };

        // Should not panic
        manager.release(release_params);
    }

    #[test]
    fn test_rpc_release_is_idempotent_for_missing_session_and_wrong_uri() {
        let manager = RpcSessionManager::new();
        let uri = Url::parse("file:///test.lean").unwrap();
        let connected = manager
            .connect(RpcConnectParams { uri: uri.clone() })
            .unwrap();

        manager.release(RpcReleaseParams {
            uri: Url::parse("file:///missing.lean").unwrap(),
            session_id: connected.session_id + 1,
            refs: vec![RpcRef { p: 1 }],
        });
        manager.release(RpcReleaseParams {
            uri: Url::parse("file:///other.lean").unwrap(),
            session_id: connected.session_id,
            refs: vec![RpcRef { p: 2 }],
        });
        manager.release(RpcReleaseParams {
            uri: uri.clone(),
            session_id: connected.session_id,
            refs: vec![RpcRef { p: 3 }],
        });
        manager.release(RpcReleaseParams {
            uri: uri.clone(),
            session_id: connected.session_id,
            refs: vec![RpcRef { p: 3 }],
        });

        assert!(
            manager.sessions.contains_key(&connected.session_id),
            "release is an object-ref notification and must not drop the RPC session"
        );

        let call = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier { uri },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        assert!(
            call.is_ok(),
            "repeated release notifications should leave the RPC session callable"
        );
    }

    #[test]
    fn test_rpc_keep_alive() {
        let manager = RpcSessionManager::new();

        let connect_params = RpcConnectParams {
            uri: Url::parse("file:///test.lean").unwrap(),
        };
        let connected = manager.connect(connect_params).unwrap();

        // Record the session's last_activity before keep_alive
        let before = manager
            .sessions
            .get(&connected.session_id)
            .unwrap()
            .last_activity;

        // Small sleep to ensure Instant::now() advances
        std::thread::sleep(Duration::from_millis(1));

        let keep_alive_params = RpcKeepAliveParams {
            uri: Url::parse("file:///test.lean").unwrap(),
            session_id: connected.session_id,
        };

        manager.keep_alive(keep_alive_params);

        // Verify last_activity was updated
        let after = manager
            .sessions
            .get(&connected.session_id)
            .unwrap()
            .last_activity;
        assert!(
            after > before,
            "keep_alive should update last_activity timestamp"
        );

        // Session should still be live after keep_alive
        assert!(manager.sessions.contains_key(&connected.session_id));
    }

    #[test]
    fn test_rpc_keep_alive_wrong_uri_does_not_refresh_session() {
        let manager = RpcSessionManager::new();
        let uri = Url::parse("file:///test.lean").unwrap();
        let connected = manager
            .connect(RpcConnectParams { uri: uri.clone() })
            .unwrap();

        let before = manager
            .sessions
            .get(&connected.session_id)
            .unwrap()
            .last_activity;

        std::thread::sleep(Duration::from_millis(1));

        manager.keep_alive(RpcKeepAliveParams {
            uri: Url::parse("file:///other.lean").unwrap(),
            session_id: connected.session_id,
        });

        let after = manager
            .sessions
            .get(&connected.session_id)
            .unwrap()
            .last_activity;
        assert_eq!(
            after, before,
            "keepAlive with the wrong document URI must not refresh the RPC session"
        );

        let call = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier { uri },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        assert!(
            call.is_ok(),
            "wrong-URI keepAlive should be ignored without dropping the session"
        );
    }

    #[test]
    fn test_object_store_alloc_returns_distinct_ids() {
        let store = RpcObjectStore::new();

        let a = store.alloc(serde_json::json!("a"));
        let b = store.alloc(serde_json::json!("b"));
        let c = store.alloc(serde_json::json!("c"));

        assert_ne!(
            a, b,
            "each allocation must hand out a distinct reference id"
        );
        assert_ne!(
            b, c,
            "each allocation must hand out a distinct reference id"
        );
        assert_ne!(
            a, c,
            "each allocation must hand out a distinct reference id"
        );

        assert_eq!(store.get(a), Some(serde_json::json!("a")));
        assert_eq!(store.get(b), Some(serde_json::json!("b")));
        assert_eq!(store.get(c), Some(serde_json::json!("c")));
    }

    #[test]
    fn test_object_store_release_middle_keeps_other_refs() {
        let store = RpcObjectStore::new();

        let first = store.alloc(serde_json::json!({"i": 0}));
        let middle = store.alloc(serde_json::json!({"i": 1}));
        let last = store.alloc(serde_json::json!({"i": 2}));

        store.release(&[RpcRef { p: middle }]);

        assert_eq!(
            store.get(middle),
            None,
            "released reference must no longer resolve"
        );
        assert_eq!(
            store.get(first),
            Some(serde_json::json!({"i": 0})),
            "releasing one reference must not affect the others"
        );
        assert_eq!(
            store.get(last),
            Some(serde_json::json!({"i": 2})),
            "releasing one reference must not affect the others"
        );
    }

    #[test]
    fn test_object_store_get_unknown_id_returns_none() {
        let store = RpcObjectStore::new();
        assert_eq!(
            store.get(12_345),
            None,
            "looking up a never-allocated id must return None"
        );

        let id = store.alloc(serde_json::json!("held"));
        // An id adjacent to a live one is still unknown.
        assert_eq!(store.get(id + 1), None);
    }

    #[test]
    fn test_object_store_release_is_idempotent_and_ids_are_not_reused() {
        let store = RpcObjectStore::new();
        let id = store.alloc(serde_json::json!("v"));

        store.release(&[RpcRef { p: id }]);
        // Releasing the same (now-unknown) id again must be a harmless no-op.
        store.release(&[RpcRef { p: id }]);
        store.release(&[RpcRef { p: 999 }]);
        assert_eq!(store.get(id), None);

        // A subsequent allocation must not reuse the released id, so a stale
        // client reference can never silently resolve to a different value.
        let next = store.alloc(serde_json::json!("w"));
        assert_ne!(next, id, "released reference ids must not be reused");
        assert_eq!(store.get(id), None);
        assert_eq!(store.get(next), Some(serde_json::json!("w")));
    }

    #[test]
    fn test_rpc_connect_params_serde() {
        let json = r#"{"uri":"file:///path/to/Foo.lean"}"#;
        let params: RpcConnectParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.uri.path(), "/path/to/Foo.lean");
    }

    #[test]
    fn test_rpc_connected_serde() {
        let connected = RpcConnected { session_id: 42 };
        let json = serde_json::to_string(&connected).unwrap();
        assert!(json.contains("sessionId"));
        assert!(json.contains("42"));
    }

    #[test]
    fn test_rpc_call_params_serde() {
        let json = r#"{
            "textDocument": {"uri": "file:///test.lean"},
            "position": {"line": 10, "character": 5},
            "sessionId": 42,
            "method": "Lean.Widget.getWidgets",
            "params": {}
        }"#;
        let params: RpcCallParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.session_id, 42);
        assert_eq!(params.method, "Lean.Widget.getWidgets");
        assert_eq!(params.position.line, 10);
    }

    #[test]
    fn test_rpc_release_params_serde() {
        let json = r#"{
            "uri": "file:///test.lean",
            "sessionId": 42,
            "refs": [{"p": 1}, {"p": 2}]
        }"#;
        let params: RpcReleaseParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.session_id, 42);
        assert_eq!(params.refs.len(), 2);
        assert_eq!(params.refs[0].p, 1);
    }

    #[test]
    fn test_rpc_call_wrong_document() {
        let manager = RpcSessionManager::new();

        // Connect to one document
        let connect_params = RpcConnectParams {
            uri: Url::parse("file:///doc1.lean").unwrap(),
        };
        let connected = manager.connect(connect_params).unwrap();

        // Try to call with different document
        let call_params = RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///doc2.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        };

        let result = manager.call(call_params);
        let err = result.unwrap_err();
        assert!(
            err.message.contains("Reconnect"),
            "expected Reconnect error, got: {}",
            err.message
        );

        let follow_up = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///doc1.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        assert!(
            follow_up.is_ok(),
            "wrong-document calls should not invalidate the original RPC session"
        );
    }

    #[test]
    fn test_rpc_call_get_widget_source_not_found() {
        let manager = RpcSessionManager::new();

        // Connect first
        let connect_params = RpcConnectParams {
            uri: Url::parse("file:///test.lean").unwrap(),
        };
        let connected = manager.connect(connect_params).unwrap();

        // Call getWidgetSource - should return explicit error since
        // clean doesn't have widget registration yet
        let call_params = RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///test.lean").unwrap(),
            },
            position: Position {
                line: 5,
                character: 10,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgetSource".to_string(),
            params: serde_json::json!({"hash": 12345, "pos": {"line": 5, "character": 10}}),
        };

        let result = manager.call(call_params);
        // Should return widget_source_not_found error (code -32001)
        let err = result.unwrap_err();
        assert_eq!(err.code, -32001);
        assert!(err.message.contains("12345"));
        assert!(err.message.contains("not found"));

        let follow_up = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///test.lean").unwrap(),
            },
            position: Position {
                line: 5,
                character: 10,
            },
            session_id: connected.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        assert!(
            follow_up.is_ok(),
            "missing widget source lookup should not invalidate the active infoview session"
        );
    }

    #[test]
    #[allow(deprecated)] // Test constructs the full Lean4-compatible widget shape.
    fn test_widget_registry_shape_returns_registered_widget_and_source() {
        let manager = RpcSessionManager::new();
        let uri = Url::parse("file:///widgets.lean").unwrap();
        let javascript_hash = 987_654;

        manager.register_panel_widget(
            uri.clone(),
            PanelWidgetInstance {
                id: "clean.TestWidget".to_string(),
                javascript_hash,
                props: serde_json::json!({"kind": "test", "value": 5}),
                range: Some(Range {
                    start: Position {
                        line: 1,
                        character: 0,
                    },
                    end: Position {
                        line: 1,
                        character: 20,
                    },
                }),
                name: None,
            },
        );
        manager.register_widget_source(
            javascript_hash,
            WidgetSource {
                sourcetext: "export default function TestWidget() { return null; }".to_string(),
            },
        );

        let connected = manager
            .connect(RpcConnectParams { uri: uri.clone() })
            .unwrap();

        let widgets_result = manager
            .call(RpcCallParams {
                text_document: TextDocumentIdentifier { uri: uri.clone() },
                position: Position {
                    line: 1,
                    character: 5,
                },
                session_id: connected.session_id,
                method: "Lean.Widget.getWidgets".to_string(),
                params: Value::Null,
            })
            .unwrap();
        let widgets: GetWidgetsResponse = serde_json::from_value(widgets_result).unwrap();
        assert_eq!(widgets.widgets.len(), 1);
        assert_eq!(widgets.widgets[0].id, "clean.TestWidget");
        assert_eq!(widgets.widgets[0].javascript_hash, javascript_hash);
        assert_eq!(
            widgets.widgets[0].props,
            serde_json::json!({"kind": "test", "value": 5})
        );

        let source_result = manager
            .call(RpcCallParams {
                text_document: TextDocumentIdentifier { uri },
                position: Position {
                    line: 1,
                    character: 5,
                },
                session_id: connected.session_id,
                method: "Lean.Widget.getWidgetSource".to_string(),
                params: serde_json::json!({
                    "hash": javascript_hash,
                    "pos": {"line": 1, "character": 5}
                }),
            })
            .unwrap();
        let source: WidgetSource = serde_json::from_value(source_result).unwrap();
        assert!(source.sourcetext.contains("TestWidget"));
    }

    #[test]
    #[allow(deprecated)] // Test constructs the full Lean4-compatible widget shape.
    fn test_widget_registry_filters_widgets_by_range() {
        let manager = RpcSessionManager::new();
        let uri = Url::parse("file:///widgets.lean").unwrap();
        manager.register_panel_widget(
            uri.clone(),
            PanelWidgetInstance {
                id: "clean.RangeWidget".to_string(),
                javascript_hash: 1,
                props: Value::Null,
                range: Some(Range {
                    start: Position {
                        line: 4,
                        character: 0,
                    },
                    end: Position {
                        line: 4,
                        character: 10,
                    },
                }),
                name: None,
            },
        );

        let connected = manager
            .connect(RpcConnectParams { uri: uri.clone() })
            .unwrap();

        let result = manager
            .call(RpcCallParams {
                text_document: TextDocumentIdentifier { uri },
                position: Position {
                    line: 5,
                    character: 0,
                },
                session_id: connected.session_id,
                method: "Lean.Widget.getWidgets".to_string(),
                params: Value::Null,
            })
            .unwrap();
        let widgets: GetWidgetsResponse = serde_json::from_value(result).unwrap();
        assert!(
            widgets.widgets.is_empty(),
            "registered widgets should only appear at positions within their range"
        );
    }

    #[test]
    fn test_get_widget_source_params_serde() {
        let json = r#"{"hash": 123456789, "pos": {"line": 10, "character": 5}}"#;
        let params: GetWidgetSourceParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.hash, 123_456_789);
        assert_eq!(params.pos.line, 10);
    }

    #[test]
    #[allow(deprecated)] // Testing deprecated name field
    fn test_panel_widget_instance_serde() {
        let widget = PanelWidgetInstance {
            id: "MyWidget".to_string(),
            javascript_hash: 12345,
            props: serde_json::json!({"key": "value"}),
            range: Some(Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 0,
                    character: 10,
                },
            }),
            name: None,
        };

        let json = serde_json::to_string(&widget).unwrap();
        assert!(json.contains("javascriptHash"));
        assert!(json.contains("12345"));
        assert!(!json.contains("name")); // None should be skipped
    }

    #[test]
    fn test_cleanup_expired_sessions() {
        let manager = RpcSessionManager::new();

        // Create a session
        let connect_params = RpcConnectParams {
            uri: Url::parse("file:///test.lean").unwrap(),
        };
        let connected = manager.connect(connect_params).unwrap();

        // Session should exist
        assert!(manager.sessions.contains_key(&connected.session_id));

        // cleanup shouldn't remove active session (not expired yet)
        manager.cleanup_expired();
        assert!(manager.sessions.contains_key(&connected.session_id));

        // Note: We can't easily test actual timeout expiry without sleeping 30s,
        // but we verify the cleanup mechanism works on active sessions.
    }

    #[test]
    fn test_multiple_concurrent_sessions() {
        let manager = RpcSessionManager::new();

        // Create 3 sessions for different documents
        let session1 = manager
            .connect(RpcConnectParams {
                uri: Url::parse("file:///doc1.lean").unwrap(),
            })
            .unwrap();
        let session2 = manager
            .connect(RpcConnectParams {
                uri: Url::parse("file:///doc2.lean").unwrap(),
            })
            .unwrap();
        let session3 = manager
            .connect(RpcConnectParams {
                uri: Url::parse("file:///doc3.lean").unwrap(),
            })
            .unwrap();

        // All session IDs should be unique
        assert_ne!(session1.session_id, session2.session_id);
        assert_ne!(session2.session_id, session3.session_id);
        assert_ne!(session1.session_id, session3.session_id);

        // Each session should work independently
        let call1 = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///doc1.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: session1.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        call1.expect("RPC call to doc1 with session1 should succeed");

        let call2 = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///doc2.lean").unwrap(),
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: session2.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        call2.expect("RPC call to doc2 with session2 should succeed");

        // Session for wrong document should fail
        let cross_call = manager.call(RpcCallParams {
            text_document: TextDocumentIdentifier {
                uri: Url::parse("file:///doc2.lean").unwrap(), // Wrong doc for session1
            },
            position: Position {
                line: 0,
                character: 0,
            },
            session_id: session1.session_id,
            method: "Lean.Widget.getWidgets".to_string(),
            params: Value::Null,
        });
        let err = cross_call.unwrap_err();
        assert!(
            err.message.contains("Reconnect"),
            "expected Reconnect error for cross-doc call, got: {}",
            err.message
        );
    }
}
