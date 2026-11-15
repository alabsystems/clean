// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise the real build_service dispatcher, rather than manager calls only.

use super::*;
use serde_json::json;
use tower_lsp::jsonrpc::{Request, Response};
use tower_service::Service;

async fn dispatch(
    service: &mut tower_lsp::LspService<crate::CleanBackend>,
    request: Request,
) -> Option<Response> {
    std::future::poll_fn(|cx| service.poll_ready(cx))
        .await
        .expect("service ready");
    service.call(request).await.expect("service call")
}

async fn initialized() -> (
    tower_lsp::LspService<crate::CleanBackend>,
    tower_lsp::ClientSocket,
) {
    let (mut service, socket) = crate::build_service();
    let reply = dispatch(
        &mut service,
        Request::build("initialize")
            .id(1)
            .params(json!({"capabilities":{}}))
            .finish(),
    )
    .await
    .expect("initialize response");
    assert!(reply.is_ok());
    (service, socket)
}

#[tokio::test]
async fn built_service_keep_alive_notification_updates_activity_without_response() {
    let (mut service, _socket) = initialized().await;
    let manager = std::sync::Arc::clone(&service.inner().rpc_sessions);
    let uri = Url::parse("file:///keep-alive-wire.lean").unwrap();
    let id = manager
        .connect(RpcConnectParams { uri: uri.clone() })
        .unwrap()
        .session_id;
    let before = Instant::now() - Duration::from_secs(30);
    manager.sessions.get_mut(&id).unwrap().last_activity = before;
    assert!(dispatch(
        &mut service,
        Request::build("$/lean/rpc/keepAlive")
            .params(json!({"uri":uri,"sessionId":id.to_string()}))
            .finish()
    )
    .await
    .is_none());
    assert!(manager.sessions.get(&id).unwrap().last_activity > before);
}

#[tokio::test]
async fn built_service_release_notification_releases_only_its_document_without_response() {
    let (mut service, _socket) = initialized().await;
    let manager = std::sync::Arc::clone(&service.inner().rpc_sessions);
    let uri = Url::parse("file:///release-wire.lean").unwrap();
    let id = manager
        .connect(RpcConnectParams { uri: uri.clone() })
        .unwrap()
        .session_id;
    let reference = manager
        .sessions
        .get(&id)
        .unwrap()
        .object_store
        .alloc(json!("held value"));
    let wrong_uri = Url::parse("file:///another-wire.lean").unwrap();
    assert!(dispatch(
        &mut service,
        Request::build("$/lean/rpc/release")
            .params(json!({"uri":wrong_uri,"sessionId":id.to_string(),"refs":[{"p":reference.to_string()}]}))
            .finish()
    )
    .await
    .is_none());
    assert!(manager
        .sessions
        .get(&id)
        .unwrap()
        .object_store
        .get(reference)
        .is_some());
    assert!(dispatch(
        &mut service,
        Request::build("$/lean/rpc/release")
            .params(
                json!({"uri":uri,"sessionId":id.to_string(),"refs":[{"p":reference.to_string()}]})
            )
            .finish()
    )
    .await
    .is_none());
    assert!(manager
        .sessions
        .get(&id)
        .unwrap()
        .object_store
        .get(reference)
        .is_none());
}

#[tokio::test]
async fn built_service_keep_alive_request_is_refused_without_mutating_activity() {
    let (mut service, _socket) = initialized().await;
    let manager = std::sync::Arc::clone(&service.inner().rpc_sessions);
    let uri = Url::parse("file:///keep-alive-request.lean").unwrap();
    let id = manager
        .connect(RpcConnectParams { uri: uri.clone() })
        .unwrap()
        .session_id;
    let before = Instant::now() - Duration::from_secs(30);
    manager.sessions.get_mut(&id).unwrap().last_activity = before;
    let reply = dispatch(
        &mut service,
        Request::build("$/lean/rpc/keepAlive")
            .id(2)
            .params(json!({"uri":uri,"sessionId":id.to_string()}))
            .finish(),
    )
    .await
    .expect("wrong-kind request response");
    assert_eq!(reply.id(), &tower_lsp::jsonrpc::Id::Number(2));
    assert!(reply.error().is_some());
    assert_eq!(manager.sessions.get(&id).unwrap().last_activity, before);
}

#[tokio::test]
async fn built_service_release_request_is_refused_without_releasing_an_object() {
    let (mut service, _socket) = initialized().await;
    let manager = std::sync::Arc::clone(&service.inner().rpc_sessions);
    let uri = Url::parse("file:///release-request.lean").unwrap();
    let id = manager
        .connect(RpcConnectParams { uri: uri.clone() })
        .unwrap()
        .session_id;
    let reference = manager
        .sessions
        .get(&id)
        .unwrap()
        .object_store
        .alloc(json!("held value"));
    let reply = dispatch(
        &mut service,
        Request::build("$/lean/rpc/release")
            .id(2)
            .params(
                json!({"uri":uri,"sessionId":id.to_string(),"refs":[{"p":reference.to_string()}]}),
            )
            .finish(),
    )
    .await
    .expect("wrong-kind request response");
    assert!(reply.error().is_some());
    assert!(manager
        .sessions
        .get(&id)
        .unwrap()
        .object_store
        .get(reference)
        .is_some());
}
