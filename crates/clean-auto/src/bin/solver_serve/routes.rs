// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Request routing for `solver_serve`.
//!
//! A thin adapter: it forwards the parsed [`Request`] to the library's
//! transport-agnostic dispatcher
//! ([`clean_auto::solver_cache_service::dispatch`]) and renders the resulting
//! [`ApiResponse`] as an HTTP JSON [`Response`]. ALL endpoint logic, ingest
//! validation, and the honest trust-note live in the library so they are unit-
//! and integration-tested without the HTTP transport.
//!
//! Endpoint surface (design §10.2):
//! - `GET  /healthz`                      Cloud Run health probe
//! - `GET  /stats`                        aggregate report + trust note
//! - `GET  /weak?by=&top=&budget_ms=`     worst-class regression worklist
//! - `GET  /vbs-gap?budget_ms=`           VBS−SBS gap (Phase-3 gate)
//! - `GET  /lookup/{obligation_digest}`   per-obligation provenance + re-check note
//! - `GET  /export-dataset?engine=&theory=&limit=`  bounded NN dataset
//! - `POST /ingest`                       append a record (+ optional proof blob)

use clean_auto::solver_cache_service::{self as svc, ServeState};

use super::config::ServeConfig;
use super::http::{Request, Response};

/// Shared application state: the serving state + the resolved config.
pub(crate) struct AppState {
    pub(crate) state: ServeState,
    #[allow(dead_code)]
    pub(crate) config: ServeConfig,
}

/// Forward a parsed request to the library dispatcher and render JSON.
pub(crate) fn dispatch(app: &AppState, req: &Request) -> Response {
    let api = svc::dispatch(&app.state, &req.method, &req.path, &req.query, &req.body);
    Response::json_with_status(api.status, &api.body)
}
