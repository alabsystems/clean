// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_parse_single_request() {
    let json =
        r#"{"jsonrpc": "2.0", "method": "check", "params": {"code": "def x := 1"}, "id": 1}"#;
    let msg = parse_message(json).unwrap();
    match msg {
        ParsedMessage::Single(req) => {
            assert_eq!(req.jsonrpc, "2.0");
            assert_eq!(req.method, "check");
            assert_eq!(req.id, Some(RequestId::Number(1)));
        }
        _ => panic!("Expected single request"),
    }
}

#[test]
fn test_parse_notification() {
    let json = r#"{"jsonrpc": "2.0", "method": "cancel"}"#;
    let msg = parse_message(json).unwrap();
    match msg {
        ParsedMessage::Single(req) => {
            assert!(req.is_notification());
            assert_eq!(req.method, "cancel");
        }
        _ => panic!("Expected single request"),
    }
}

#[test]
fn test_parse_batch_request() {
    let json = r#"[
        {"jsonrpc": "2.0", "method": "check", "params": {"code": "1"}, "id": 1},
        {"jsonrpc": "2.0", "method": "check", "params": {"code": "2"}, "id": 2}
    ]"#;
    let msg = parse_message(json).unwrap();
    match msg {
        ParsedMessage::Batch(items) => {
            assert_eq!(items.len(), 2);
            assert!(matches!(items[0], BatchItem::Request(_)));
            assert!(matches!(items[1], BatchItem::Request(_)));
        }
        _ => panic!("Expected batch request"),
    }
}

#[test]
fn test_parse_empty_batch_error() {
    let json = "[]";
    let err = parse_message(json).unwrap_err();
    assert_eq!(err.code, error_codes::INVALID_REQUEST);
}

#[test]
fn test_parse_invalid_json() {
    let json = "{invalid}";
    let err = parse_message(json).unwrap_err();
    assert_eq!(err.code, error_codes::PARSE_ERROR);
}

#[test]
fn test_serialize_response() {
    let resp = Response::success(RequestId::Number(1), serde_json::json!({"valid": true}));
    let json = serde_json::to_string(&resp).unwrap();
    assert!(json.contains("\"jsonrpc\":\"2.0\""));
    assert!(json.contains("\"result\""));
    assert!(!json.contains("\"error\""));
}

#[test]
fn test_serialize_error_response() {
    let resp = Response::error(
        RequestId::String("abc".into()),
        RpcError::method_not_found("unknown"),
    );
    let json = serde_json::to_string(&resp).unwrap();
    assert!(json.contains("\"error\""));
    assert!(json.contains("-32601"));
}

#[test]
fn test_request_id_types() {
    // Number ID
    let json = r#"{"jsonrpc": "2.0", "method": "test", "id": 42}"#;
    let req: Request = serde_json::from_str(json).unwrap();
    assert_eq!(req.id, Some(RequestId::Number(42)));

    // String ID
    let json = r#"{"jsonrpc": "2.0", "method": "test", "id": "abc-123"}"#;
    let req: Request = serde_json::from_str(json).unwrap();
    assert_eq!(req.id, Some(RequestId::String("abc-123".into())));

    // Null ID - in JSON-RPC, null id is treated as a missing notification id.
    let json = r#"{"jsonrpc": "2.0", "method": "test", "id": null}"#;
    let req: Request = serde_json::from_str(json).unwrap();
    assert_eq!(
        req.id, None,
        "JSON null id should deserialize to a missing request id"
    );
}

#[test]
fn test_request_new_constructor() {
    let req = Request::new(
        "testMethod",
        Some(serde_json::json!({"key": "value"})),
        RequestId::Number(42),
    );
    assert_eq!(req.jsonrpc, JSONRPC_VERSION);
    assert_eq!(req.method, "testMethod");
    assert_eq!(req.id, Some(RequestId::Number(42)));
    assert!(
        req.params.is_some(),
        "request created with params should have params"
    );
}

#[test]
fn test_request_notification_constructor() {
    let req = Request::notification("cancel", None);
    assert_eq!(req.jsonrpc, JSONRPC_VERSION);
    assert_eq!(req.method, "cancel");
    assert!(req.is_notification());
    assert_eq!(req.id, None, "notification should have no id");
}

#[test]
fn test_request_is_notification_false() {
    let req = Request::new("check", None, RequestId::Number(1));
    assert!(!req.is_notification());
}

#[test]
fn test_request_is_notification_null_id() {
    let json = r#"{"jsonrpc": "2.0", "method": "check", "id": null}"#;
    let req: Request = serde_json::from_str(json).unwrap();
    assert!(req.is_notification());
}

#[test]
fn test_response_success_typed() {
    #[derive(serde::Serialize)]
    struct TestResult {
        valid: bool,
        count: i32,
    }
    let result = TestResult {
        valid: true,
        count: 42,
    };
    let resp = Response::success_typed(RequestId::Number(1), &result).unwrap();

    assert!(
        resp.error.is_none(),
        "success response should have no error: {:?}",
        resp.error
    );
    let result_value = resp.result.expect("success response should have a result");
    assert_eq!(result_value["valid"], true);
    assert_eq!(result_value["count"], 42);
}

#[test]
fn test_rpc_error_new() {
    let err = RpcError::new(-32000, "Custom error");
    assert_eq!(err.code, -32000);
    assert_eq!(err.message, "Custom error");
    assert_eq!(err.data, None, "error without data should have None");
}

#[test]
fn test_rpc_error_with_data() {
    let data = serde_json::json!({"line": 10, "column": 5});
    let err = RpcError::with_data(-32001, "Parse error", data.clone());
    assert_eq!(err.code, -32001);
    assert_eq!(err.message, "Parse error");
    assert_eq!(err.data, Some(data));
}

#[test]
fn test_rpc_error_constructors() {
    // Test all error constructor methods
    let err = RpcError::parse_error("invalid syntax");
    assert_eq!(err.code, error_codes::PARSE_ERROR);

    let err = RpcError::invalid_request("missing field");
    assert_eq!(err.code, error_codes::INVALID_REQUEST);

    let err = RpcError::method_not_found("unknown");
    assert_eq!(err.code, error_codes::METHOD_NOT_FOUND);
    assert!(err.message.contains("unknown"));

    let err = RpcError::invalid_params("wrong type");
    assert_eq!(err.code, error_codes::INVALID_PARAMS);

    let err = RpcError::internal_error("server crash");
    assert_eq!(err.code, error_codes::INTERNAL_ERROR);

    let err = RpcError::type_error("type mismatch");
    assert_eq!(err.code, error_codes::TYPE_ERROR);

    let err = RpcError::lean_parse_error("syntax error");
    assert_eq!(err.code, error_codes::LEAN_PARSE_ERROR);

    let err = RpcError::elaboration_error("unification failed");
    assert_eq!(err.code, error_codes::ELABORATION_ERROR);

    let err = RpcError::proof_not_found();
    assert_eq!(err.code, error_codes::PROOF_NOT_FOUND);

    let err = RpcError::timeout(5000);
    assert_eq!(err.code, error_codes::TIMEOUT);
    assert!(err.message.contains("5000"));

    let err = RpcError::request_limit_exceeded(10_000);
    assert_eq!(err.code, error_codes::REQUEST_LIMIT_EXCEEDED);
    assert!(err.message.contains("10000"));
}

#[test]
fn test_batch_request_serde() {
    let batch = BatchRequest(vec![
        Request::new("check", None, RequestId::Number(1)),
        Request::new("check", None, RequestId::Number(2)),
    ]);

    let json = serde_json::to_string(&batch).unwrap();
    assert!(json.starts_with('['));

    let parsed: BatchRequest = serde_json::from_str(&json).unwrap();
    assert_eq!(parsed.0.len(), 2);
}

#[test]
fn test_batch_response_serde() {
    let batch = BatchResponse(vec![
        Response::success(RequestId::Number(1), serde_json::json!({"ok": true})),
        Response::error(RequestId::Number(2), RpcError::internal_error("test")),
    ]);

    let json = serde_json::to_string(&batch).unwrap();
    assert!(json.starts_with('['));

    let parsed: BatchResponse = serde_json::from_str(&json).unwrap();
    assert_eq!(parsed.0.len(), 2);
}

#[test]
fn test_parse_message_primitive_types() {
    // Primitive values should be rejected
    let err = parse_message("42").unwrap_err();
    assert_eq!(err.code, error_codes::INVALID_REQUEST);

    let err = parse_message("\"string\"").unwrap_err();
    assert_eq!(err.code, error_codes::INVALID_REQUEST);

    let err = parse_message("true").unwrap_err();
    assert_eq!(err.code, error_codes::INVALID_REQUEST);

    let err = parse_message("null").unwrap_err();
    assert_eq!(err.code, error_codes::INVALID_REQUEST);
}

#[test]
fn test_parse_message_invalid_request_in_batch() {
    // Batch with an invalid request object
    let json = r#"[{"jsonrpc": "2.0", "method": "test", "id": 1}, {"not_valid": true}]"#;
    let msg = parse_message(json).unwrap();
    match msg {
        ParsedMessage::Batch(items) => {
            assert_eq!(items.len(), 2);
            assert!(matches!(items[0], BatchItem::Request(_)));
            assert!(matches!(items[1], BatchItem::Error(_)));
        }
        _ => panic!("Expected batch request"),
    }
}

#[test]
fn test_parse_message_invalid_jsonrpc_version() {
    let json = r#"{"jsonrpc": "1.0", "method": "check", "id": 1}"#;
    let err = parse_message(json).unwrap_err();
    assert_eq!(err.code, error_codes::INVALID_REQUEST);
}

#[test]
fn test_request_id_default() {
    let id = RequestId::default();
    assert_eq!(id, RequestId::Null);
}

#[test]
fn test_request_id_hash() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(RequestId::Number(1));
    set.insert(RequestId::String("abc".into()));
    set.insert(RequestId::Null);
    assert_eq!(set.len(), 3);
}

#[test]
fn test_response_clone() {
    let resp = Response::success(RequestId::Number(1), serde_json::json!({"test": true}));
    let cloned = resp.clone();
    assert_eq!(cloned.id, resp.id);
    assert_eq!(cloned.result, resp.result);
}

#[test]
fn test_rpc_error_clone() {
    let err = RpcError::with_data(-32000, "test", serde_json::json!({"extra": "data"}));
    let cloned = err.clone();
    assert_eq!(cloned.code, err.code);
    assert_eq!(cloned.message, err.message);
    assert_eq!(cloned.data, err.data);
}

#[test]
fn test_request_debug() {
    let req = Request::new("test", None, RequestId::Number(1));
    let debug_str = format!("{req:?}");
    assert!(debug_str.contains("Request"));
    assert!(debug_str.contains("test"));
}

#[test]
fn test_response_debug() {
    let resp = Response::success(RequestId::Number(1), serde_json::json!(null));
    let debug_str = format!("{resp:?}");
    assert!(debug_str.contains("Response"));
}

#[test]
fn test_rpc_error_debug() {
    let err = RpcError::internal_error("debug test");
    let debug_str = format!("{err:?}");
    assert!(debug_str.contains("RpcError"));
}

#[test]
fn test_parsed_message_debug() {
    let json = r#"{"jsonrpc": "2.0", "method": "test", "id": 1}"#;
    let msg = parse_message(json).unwrap();
    let debug_str = format!("{msg:?}");
    assert!(debug_str.contains("Single"));
}

#[test]
fn test_is_null_id_helper() {
    // Test the internal helper function through serialization behavior
    let req = Request {
        jsonrpc: "2.0".to_string(),
        method: "test".to_string(),
        params: None,
        id: None,
    };
    let json = serde_json::to_string(&req).unwrap();
    // id should be skipped when None
    assert!(!json.contains("\"id\""));

    let req = Request {
        jsonrpc: "2.0".to_string(),
        method: "test".to_string(),
        params: None,
        id: Some(RequestId::Null),
    };
    let json = serde_json::to_string(&req).unwrap();
    // id should be skipped when Null
    assert!(!json.contains("\"id\""));

    let req = Request {
        jsonrpc: "2.0".to_string(),
        method: "test".to_string(),
        params: None,
        id: Some(RequestId::Number(1)),
    };
    let json = serde_json::to_string(&req).unwrap();
    // id should be present when it has a value
    assert!(json.contains("\"id\""));
}

#[test]
fn test_negative_request_id() {
    let json = r#"{"jsonrpc": "2.0", "method": "test", "id": -42}"#;
    let req: Request = serde_json::from_str(json).unwrap();
    assert_eq!(req.id, Some(RequestId::Number(-42)));
}

#[test]
fn test_empty_string_request_id() {
    let json = r#"{"jsonrpc": "2.0", "method": "test", "id": ""}"#;
    let req: Request = serde_json::from_str(json).unwrap();
    assert_eq!(req.id, Some(RequestId::String("".into())));
}

#[test]
fn test_batch_with_mixed_notifications_and_requests() {
    // JSON-RPC 2.0: Batch can contain mix of requests and notifications
    let json = r#"[
        {"jsonrpc": "2.0", "method": "notify", "params": {}},
        {"jsonrpc": "2.0", "method": "call", "id": 1}
    ]"#;
    let msg = parse_message(json).unwrap();
    match msg {
        ParsedMessage::Batch(items) => {
            assert_eq!(items.len(), 2);
            // First is notification
            if let BatchItem::Request(ref req) = items[0] {
                assert!(req.is_notification());
            } else {
                panic!("Expected request");
            }
            // Second is request
            if let BatchItem::Request(ref req) = items[1] {
                assert!(!req.is_notification());
            } else {
                panic!("Expected request");
            }
        }
        _ => panic!("Expected batch"),
    }
}

#[test]
fn test_batch_with_non_object_item() {
    // JSON-RPC 2.0 spec: Non-object items in batch should error individually
    let json = r#"[{"jsonrpc": "2.0", "method": "test", "id": 1}, 42, "string"]"#;
    let msg = parse_message(json).unwrap();
    match msg {
        ParsedMessage::Batch(items) => {
            assert_eq!(items.len(), 3);
            assert!(matches!(items[0], BatchItem::Request(_)));
            // Number 42 should be an error
            if let BatchItem::Error(ref err) = items[1] {
                assert_eq!(err.code, error_codes::INVALID_REQUEST);
            } else {
                panic!("Expected error for number");
            }
            // String should be an error
            if let BatchItem::Error(ref err) = items[2] {
                assert_eq!(err.code, error_codes::INVALID_REQUEST);
            } else {
                panic!("Expected error for string");
            }
        }
        _ => panic!("Expected batch"),
    }
}

#[test]
fn test_batch_with_invalid_jsonrpc_version() {
    // Invalid jsonrpc version in batch item should error that item only
    let json = r#"[
        {"jsonrpc": "2.0", "method": "valid", "id": 1},
        {"jsonrpc": "1.0", "method": "invalid", "id": 2}
    ]"#;
    let msg = parse_message(json).unwrap();
    match msg {
        ParsedMessage::Batch(items) => {
            assert_eq!(items.len(), 2);
            assert!(matches!(items[0], BatchItem::Request(_)));
            if let BatchItem::Error(ref err) = items[1] {
                assert_eq!(err.code, error_codes::INVALID_REQUEST);
                assert!(err.message.contains("jsonrpc"));
            } else {
                panic!("Expected error for invalid version");
            }
        }
        _ => panic!("Expected batch"),
    }
}
