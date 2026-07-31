//! `clean-mathverse-server` — the Mathverse hosting service (Phase 1 MVP).
//!
//! A net-new `axum` HTTP service that serves an honest public browse/search
//! surface over a directory of `.mathverse` shards (the "Core"): a JSON API
//! under `/v1/*` plus a minimal server-rendered web UI at `/`.
//!
//! It is **read-only** and does not re-verify proofs — it serves the stored
//! trust labels faithfully (see [`trust`]). Minting/re-verification (the
//! publisher + daily re-auditor) is Phase 2 and intentionally not in this crate.
//!
//! Build note: this crate depends on `clean-mathverse` with
//! `default-features = false`, dropping `clean-auto`, the AY solver graph, and
//! the `../trust-ir` sibling path dependency — so it builds in a bare Docker
//! context.

pub mod api;
pub mod corpus;
pub mod error;
pub mod stats;
pub mod trust;
pub mod web;

use std::sync::Arc;
use std::time::Instant;

use axum::Router;
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;

use crate::corpus::Corpus;

/// Crate version, surfaced in `/v1/health`.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Shared application state.
pub struct App {
    pub corpus: Corpus,
    pub started: Instant,
}

impl App {
    pub fn new(corpus: Corpus) -> Self {
        App {
            corpus,
            started: Instant::now(),
        }
    }
}

/// Handle threaded through axum handlers.
pub type AppState = Arc<App>;

/// Build the full router (JSON API + SSR web + middleware).
pub fn router(state: AppState) -> Router {
    Router::new()
        .merge(api::routes())
        .merge(web::routes())
        .layer(TraceLayer::new_for_http())
        .layer(CorsLayer::permissive())
        .with_state(state)
}
