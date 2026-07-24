// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Widget RPC handlers for Lean4 infoview parity.
//!
//! Implements `getWidgets`, `getWidgetSource`, and `Widget_event` endpoints so
//! that Lean4-compatible infoview clients can query widget state through the
//! JSON-RPC server. These handlers delegate the protocol logic to
//! [`crate::rpc_widgets`] against the [`crate::handlers::ServerState`] widget
//! store.
//!
//! clean has no elaboration-time `@[widget_module]` registration yet, so the
//! store is populated explicitly (via [`ServerState::register_widget_source`]
//! / [`ServerState::register_document_widgets`]); until elaboration wires that
//! up, queries for unregistered documents/hashes degrade gracefully (empty
//! widget list, `null` source).
//!
//! Protocol reference: Lean.Widget.UserWidget
//! <https://lean-lang.org/doc/api/Lean/Widget/UserWidget.html>
//!
//! Part of #1193

use crate::rpc::{RequestId, Response, RpcError};
use crate::rpc_widgets;
use serde::{Deserialize, Serialize};

/// Parameters for the `getWidgets` method.
///
/// Mirrors `Lean.Widget.getWidgets` RPC call params.
#[derive(Debug, Clone, Deserialize)]
pub struct GetWidgetsParams {
    /// Document URI (file path or virtual URI)
    #[serde(default)]
    pub uri: Option<String>,
    /// Line number (0-indexed)
    #[serde(default)]
    pub line: Option<u32>,
    /// Column number (0-indexed)
    #[serde(default)]
    pub column: Option<u32>,
}

/// A single panel widget instance returned by `getWidgets`.
///
/// Mirrors `Lean.Widget.UserWidget.PanelWidgetInstance`.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WidgetInstance {
    /// Widget module identifier
    pub id: String,
    /// Content-addressable hash of the JavaScript source module
    pub javascript_hash: String,
    /// Widget props (opaque JSON, may contain RPC refs)
    pub props: serde_json::Value,
}

/// Response for the `getWidgets` method.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetWidgetsResult {
    /// Panel widgets registered for the document and in scope at the
    /// requested position. Empty when the document has no registered widgets.
    pub widgets: Vec<WidgetInstance>,
}

/// Parameters for the `getWidgetSource` method.
///
/// Mirrors `Lean.Widget.UserWidget.GetWidgetSourceParams`.
#[derive(Debug, Clone, Deserialize)]
pub struct GetWidgetSourceParams {
    /// Content-addressable hash of the JavaScript module to retrieve
    pub hash: String,
}

/// Response for the `getWidgetSource` method.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetWidgetSourceResult {
    /// JavaScript source text for the widget module.
    pub sourcetext: String,
}

/// Handle the `getWidgets` method.
///
/// Returns the widget instances registered for the requested document that are
/// in scope at the requested position. Delegates the protocol logic to
/// [`rpc_widgets::handle_get_widgets`] against the document metadata held in
/// [`super::ServerState`]. Returns an empty list when the document has no
/// registered widgets (graceful degradation).
pub async fn handle_get_widgets(
    state: &super::ServerState,
    id: RequestId,
    params: GetWidgetsParams,
) -> Response {
    let uri = params.uri.unwrap_or_default();
    let rpc_params = rpc_widgets::GetWidgetsParams {
        text_document: rpc_widgets::TextDocumentIdentifier { uri: uri.clone() },
        position: rpc_widgets::Position {
            line: params.line.unwrap_or(0),
            character: params.column.unwrap_or(0),
        },
    };

    let guard = state.widgets.read().await;
    let rpc_result = rpc_widgets::handle_get_widgets(&rpc_params, guard.document_metadata(&uri));
    drop(guard);

    let result = GetWidgetsResult {
        widgets: rpc_result
            .widgets
            .into_iter()
            .map(|w| WidgetInstance {
                id: w.id,
                javascript_hash: w.hash,
                props: w.props,
            })
            .collect(),
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

/// Handle the `getWidgetSource` method.
///
/// Returns the JavaScript source for a widget module identified by its content
/// hash. Delegates the lookup to [`rpc_widgets::handle_get_widget_source`]
/// against the [`super::ServerState`] source store. Returns an `INVALID_PARAMS`
/// error when the hash is unknown so clients can distinguish a missing source
/// from an empty one.
pub async fn handle_get_widget_source(
    state: &super::ServerState,
    id: RequestId,
    params: GetWidgetSourceParams,
) -> Response {
    let rpc_params = rpc_widgets::GetWidgetSourceParams {
        hash: params.hash.clone(),
        position: rpc_widgets::Position::default(),
    };

    let guard = state.widgets.read().await;
    let rpc_result = rpc_widgets::handle_get_widget_source(&rpc_params, guard.sources());
    drop(guard);

    match rpc_result.source {
        Some(sourcetext) => {
            let result = GetWidgetSourceResult { sourcetext };
            Response::success_typed(id.clone(), &result)
                .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
        }
        None => Response::error(
            id,
            RpcError::invalid_params(format!("Widget source not found for hash {}", params.hash)),
        ),
    }
}

/// Parameters for the `Widget_event` method.
///
/// Mirrors `Lean.Widget.RpcHandlers.WidgetEventParams`.
/// Clients send this to notify the server of a widget interaction (click,
/// value change, etc.).
#[derive(Debug, Clone, Deserialize)]
pub struct WidgetEventParams {
    /// Widget instance identifier
    pub id: String,
    /// Document URI that owns this widget instance.
    #[serde(default)]
    pub uri: Option<String>,
    /// Content hash of the JavaScript source module that owns this widget.
    #[serde(default)]
    pub hash: Option<String>,
    /// Event kind (e.g. `"onClick"`, `"onChange"`)
    pub kind: String,
    /// Opaque event payload (widget-specific)
    #[serde(default)]
    pub payload: serde_json::Value,
}

/// Response for the `Widget_event` method.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WidgetEventResult {
    /// Whether the event was handled.
    ///
    /// Currently always `false` because clean does not yet process
    /// widget interactions.
    pub handled: bool,
    /// Optional response data from the widget handler.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
}

/// Handle the `Widget_event` method.
///
/// Routes a widget interaction event (click, value change, etc.) to the
/// targeted widget. The event is considered `handled` when the referenced
/// widget instance is registered for its document, or — absent a document URI
/// — when its source hash is registered. clean has no client-side event
/// effect engine yet, so a routed event has no side effects beyond the
/// acknowledgement; unknown widgets report `handled: false` rather than
/// erroring.
pub async fn handle_widget_event(
    state: &super::ServerState,
    id: RequestId,
    params: WidgetEventParams,
) -> Response {
    let guard = state.widgets.read().await;
    let handled = match (&params.uri, &params.hash) {
        (Some(uri), _) => guard.has_widget(uri, &params.id),
        (None, Some(hash)) => guard.sources().get(hash).is_some(),
        (None, None) => false,
    };
    drop(guard);

    let result = WidgetEventResult {
        handled,
        data: None,
    };

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}
