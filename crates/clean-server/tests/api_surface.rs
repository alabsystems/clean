// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Environment, Expr};
use clean_server::handlers::ServerState;
use clean_server::proof_state::{pp_expr, ProofStateCache, ProofStateCacheConfig};
use clean_server::registry::{all_method_names, supports_progress};
use clean_server::rpc::{parse_message, BatchItem, BatchRequest, BatchResponse, ParsedMessage};
use clean_server::{Request, RequestId, Response, RpcError, StateId, WebSocketConfig};

#[test]
fn test_root_reexports_focus_on_primary_rpc_entry_points() {
    let request = Request::new("check", None, RequestId::Number(1));
    assert!(!request.is_notification());

    let response = Response::error(
        RequestId::Number(1),
        RpcError::method_not_found("missingMethod"),
    );
    assert_eq!(response.id, RequestId::Number(1));

    let _batch_item = BatchItem::Request(request.clone());
    let _batch_request = BatchRequest(vec![request]);
    let _batch_response = BatchResponse(vec![response]);

    let parsed = parse_message(r#"{"jsonrpc":"2.0","method":"check","id":1}"#)
        .expect("single request should parse");
    assert!(matches!(parsed, ParsedMessage::Single(_)));
    assert!(supports_progress("batchCheck"));
    assert!(all_method_names().iter().any(|name| name == "check"));

    let state_id = StateId::new();
    assert!(state_id.to_string().starts_with("ps_"));

    let cache = ProofStateCache::new(ProofStateCacheConfig::default());
    assert!(cache.is_empty());

    let _state = ServerState::new()
        .with_gpu(true)
        .with_worker_threads(2)
        .with_env(Environment::new());

    let ws_config = WebSocketConfig::default()
        .with_gpu(true)
        .with_max_concurrent(8)
        .with_worker_threads(2);
    assert!(ws_config.gpu_enabled);
    assert_eq!(ws_config.max_concurrent, 8);
    assert_eq!(ws_config.worker_threads, 2);

    let env = Environment::new();
    assert_eq!(pp_expr(&Expr::prop(), &env), "Prop");
}
