// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the widget RPC handlers (`getWidgets`,
//! `getWidgetSource`, `Widget_event`).
//!
//! These exercise the handler/state layer: `ServerState` constructs with the
//! widget store, registered widgets/sources are returned by the handlers, and
//! unknown lookups degrade or error cleanly. Part of #1193.

use crate::handlers::{
    handle_get_widget_source, handle_get_widgets, handle_widget_event, GetWidgetSourceParams,
    GetWidgetSourceResult, GetWidgetsParams, GetWidgetsResult, ServerState, WidgetEventParams,
    WidgetEventResult,
};
use crate::rpc::{error_codes, RequestId};

const URI: &str = "file:///tmp/Widget.lean";

/// Goal-state metadata containing a single widget registered at line 0.
fn one_widget_metadata() -> serde_json::Value {
    serde_json::json!({
        "widgets": [{
            "id": "GoalWidget",
            "name": "Goal Display",
            "hash": "abc123",
            "line": 0,
            "character": 0
        }]
    })
}

#[tokio::test]
async fn test_server_state_constructs_with_widget_store() {
    // The new widget field must be default-initialized so existing
    // construction paths keep compiling and the store starts empty.
    let state = ServerState::new();
    let guard = state.widgets.read().await;
    assert!(
        guard.sources().is_empty(),
        "fresh ServerState should have no registered widget sources"
    );
    assert!(
        guard.document_metadata(URI).is_none(),
        "fresh ServerState should have no document widget metadata"
    );
}

#[tokio::test]
async fn test_get_widgets_unregistered_document_returns_empty() {
    let state = ServerState::new();
    let params = GetWidgetsParams {
        uri: Some(URI.to_string()),
        line: Some(10),
        column: Some(0),
    };

    let response = handle_get_widgets(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "getWidgets should not error: {:?}",
        response.error
    );
    let result: GetWidgetsResult = serde_json::from_value(
        response
            .result
            .expect("getWidgets response should have a result"),
    )
    .expect("getWidgets result should deserialize");
    assert!(
        result.widgets.is_empty(),
        "unregistered document should yield no widgets"
    );
}

#[tokio::test]
async fn test_get_widgets_returns_registered_widget() {
    let state = ServerState::new();
    state
        .register_document_widgets(URI.to_string(), one_widget_metadata())
        .await;

    let params = GetWidgetsParams {
        uri: Some(URI.to_string()),
        line: Some(10),
        column: Some(0),
    };
    let response = handle_get_widgets(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "getWidgets should not error: {:?}",
        response.error
    );

    let result: GetWidgetsResult =
        serde_json::from_value(response.result.expect("result expected"))
            .expect("getWidgets result should deserialize");
    assert_eq!(result.widgets.len(), 1, "one registered widget expected");
    assert_eq!(result.widgets[0].id, "GoalWidget");
    assert_eq!(result.widgets[0].javascript_hash, "abc123");
}

#[tokio::test]
async fn test_get_widgets_filters_widget_above_cursor() {
    let state = ServerState::new();
    // Widget registered at line 100 is not in scope at line 5.
    let meta = serde_json::json!({
        "widgets": [{
            "id": "Late", "name": "L", "hash": "h", "line": 100, "character": 0
        }]
    });
    state.register_document_widgets(URI.to_string(), meta).await;

    let params = GetWidgetsParams {
        uri: Some(URI.to_string()),
        line: Some(5),
        column: Some(0),
    };
    let response = handle_get_widgets(&state, RequestId::Number(1), params).await;
    let result: GetWidgetsResult =
        serde_json::from_value(response.result.expect("result expected"))
            .expect("getWidgets result should deserialize");
    assert!(
        result.widgets.is_empty(),
        "widget below the cursor should be filtered out"
    );
}

#[tokio::test]
async fn test_get_widget_source_returns_registered_source() {
    let state = ServerState::new();
    state
        .register_widget_source("abc123".to_string(), "<div>hello</div>".to_string())
        .await;

    let params = GetWidgetSourceParams {
        hash: "abc123".to_string(),
    };
    let response = handle_get_widget_source(&state, RequestId::Number(2), params).await;
    assert!(
        response.error.is_none(),
        "getWidgetSource should not error for a known hash: {:?}",
        response.error
    );
    let result: GetWidgetSourceResult =
        serde_json::from_value(response.result.expect("result expected"))
            .expect("getWidgetSource result should deserialize");
    assert_eq!(result.sourcetext, "<div>hello</div>");
}

#[tokio::test]
async fn test_get_widget_source_unknown_hash_errors_cleanly() {
    let state = ServerState::new();
    let params = GetWidgetSourceParams {
        hash: "missing".to_string(),
    };
    let response = handle_get_widget_source(&state, RequestId::Number(3), params).await;
    assert!(
        response.result.is_none(),
        "unknown hash should not produce a result"
    );
    let error = response
        .error
        .expect("unknown hash should produce an error");
    assert_eq!(
        error.code,
        error_codes::INVALID_PARAMS,
        "unknown hash should be an invalid-params error"
    );
    assert!(
        error.message.contains("missing"),
        "error message should reference the missing hash: {}",
        error.message
    );
}

#[tokio::test]
async fn test_widget_event_routes_to_registered_widget() {
    let state = ServerState::new();
    state
        .register_document_widgets(URI.to_string(), one_widget_metadata())
        .await;

    let params = WidgetEventParams {
        id: "GoalWidget".to_string(),
        uri: Some(URI.to_string()),
        hash: None,
        kind: "onClick".to_string(),
        payload: serde_json::Value::Null,
    };
    let response = handle_widget_event(&state, RequestId::Number(4), params).await;
    assert!(
        response.error.is_none(),
        "Widget_event should not error: {:?}",
        response.error
    );
    let result: WidgetEventResult =
        serde_json::from_value(response.result.expect("result expected"))
            .expect("Widget_event result should deserialize");
    assert!(
        result.handled,
        "event for a registered widget should be handled"
    );
}

#[tokio::test]
async fn test_widget_event_routes_by_source_hash_when_no_uri() {
    let state = ServerState::new();
    state
        .register_widget_source("srchash".to_string(), "<div/>".to_string())
        .await;

    let params = WidgetEventParams {
        id: "AnyId".to_string(),
        uri: None,
        hash: Some("srchash".to_string()),
        kind: "onChange".to_string(),
        payload: serde_json::json!({"value": 1}),
    };
    let response = handle_widget_event(&state, RequestId::Number(5), params).await;
    let result: WidgetEventResult =
        serde_json::from_value(response.result.expect("result expected"))
            .expect("Widget_event result should deserialize");
    assert!(
        result.handled,
        "event for a registered source hash should be handled"
    );
}

#[tokio::test]
async fn test_widget_event_unknown_widget_not_handled() {
    let state = ServerState::new();
    let params = WidgetEventParams {
        id: "Nope".to_string(),
        uri: Some(URI.to_string()),
        hash: None,
        kind: "onClick".to_string(),
        payload: serde_json::Value::Null,
    };
    let response = handle_widget_event(&state, RequestId::Number(6), params).await;
    assert!(
        response.error.is_none(),
        "Widget_event should not error for unknown widgets: {:?}",
        response.error
    );
    let result: WidgetEventResult =
        serde_json::from_value(response.result.expect("result expected"))
            .expect("Widget_event result should deserialize");
    assert!(
        !result.handled,
        "event for an unregistered widget should report handled: false"
    );
}
