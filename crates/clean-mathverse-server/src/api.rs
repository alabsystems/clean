//! JSON API handlers (`/v1/*`) and liveness (`/healthz`).

use axum::extract::{Path, Query, State};
use axum::http::StatusCode;
use axum::response::IntoResponse;
use axum::routing::get;
use axum::{Json, Router};
use serde::{Deserialize, Serialize};

use crate::corpus::{DeclDetail, SearchHit};
use crate::stats::CorpusStats;
use crate::trust::{TrustStatement, FOUNDATIONAL_AXIOM_DISCLOSURE};
use crate::{AppState, VERSION};

/// Mount the JSON + liveness routes.
pub fn routes() -> Router<AppState> {
    Router::new()
        .route("/healthz", get(healthz))
        .route("/v1/health", get(health))
        .route("/v1/stats", get(stats))
        .route("/v1/search", get(search))
        .route("/v1/decl/{name}", get(decl))
        .route("/v1/decl/{name}/deps", get(decl_deps))
        .route("/v1/trust", get(trust))
        .route("/v1/foundational-axioms", get(foundational_axioms))
}

async fn healthz() -> &'static str {
    "ok\n"
}

#[derive(Serialize)]
struct Health {
    status: &'static str,
    version: &'static str,
    generation: String,
    declarations: usize,
    shards_loaded: usize,
    shards_skipped: usize,
    uptime_seconds: u64,
}

async fn health(State(app): State<AppState>) -> Json<Health> {
    Json(Health {
        status: "ok",
        version: VERSION,
        generation: app.corpus.generation().to_string(),
        declarations: app.corpus.declaration_count(),
        shards_loaded: app.corpus.shards_loaded().len(),
        shards_skipped: app.corpus.shards_skipped().len(),
        uptime_seconds: app.started.elapsed().as_secs(),
    })
}

#[derive(Serialize)]
struct SkippedShard {
    shard: String,
    reason: String,
}

#[derive(Serialize)]
struct StatsResponse {
    generation: String,
    corpus_dir: String,
    #[serde(flatten)]
    stats: CorpusStats,
    shards: Vec<String>,
    skipped: Vec<SkippedShard>,
}

async fn stats(State(app): State<AppState>) -> Json<StatsResponse> {
    let corpus = &app.corpus;
    Json(StatsResponse {
        generation: corpus.generation().to_string(),
        corpus_dir: corpus.dir().display().to_string(),
        stats: corpus.stats().clone(),
        shards: corpus.shards_loaded().to_vec(),
        skipped: corpus
            .shards_skipped()
            .iter()
            .map(|(shard, reason)| SkippedShard {
                shard: shard.clone(),
                reason: reason.clone(),
            })
            .collect(),
    })
}

#[derive(Deserialize)]
struct SearchParams {
    #[serde(default)]
    q: String,
    limit: Option<usize>,
}

#[derive(Serialize)]
struct SearchResponse {
    query: String,
    count: usize,
    results: Vec<SearchHit>,
}

async fn search(
    State(app): State<AppState>,
    Query(p): Query<SearchParams>,
) -> Json<SearchResponse> {
    let limit = p.limit.unwrap_or(25).clamp(1, 200);
    let results = app.corpus.search(&p.q, limit);
    Json(SearchResponse {
        query: p.q,
        count: results.len(),
        results,
    })
}

#[derive(Serialize)]
struct ApiError {
    error: String,
}

async fn decl(
    State(app): State<AppState>,
    Path(name): Path<String>,
) -> Result<Json<DeclDetail>, (StatusCode, Json<ApiError>)> {
    app.corpus.decl(&name).map(Json).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ApiError {
                error: format!("declaration not found: {name}"),
            }),
        )
    })
}

#[derive(Serialize)]
struct DepsResponse {
    name: String,
    dependency_count: usize,
    dependencies: Vec<String>,
    truncated: bool,
}

async fn decl_deps(
    State(app): State<AppState>,
    Path(name): Path<String>,
) -> Result<Json<DepsResponse>, (StatusCode, Json<ApiError>)> {
    match app.corpus.decl(&name) {
        Some(d) => Ok(Json(DepsResponse {
            name: d.name,
            dependency_count: d.dependency_count,
            dependencies: d.dependencies,
            truncated: d.dependencies_truncated,
        })),
        None => Err((
            StatusCode::NOT_FOUND,
            Json(ApiError {
                error: format!("declaration not found: {name}"),
            }),
        )),
    }
}

async fn trust() -> Json<TrustStatement> {
    Json(TrustStatement::current())
}

#[derive(Serialize)]
struct FoundationalAxioms {
    foundational_axioms: &'static [&'static str],
    note: &'static str,
}

async fn foundational_axioms() -> impl IntoResponse {
    Json(FoundationalAxioms {
        foundational_axioms: FOUNDATIONAL_AXIOM_DISCLOSURE,
        note: "A declaration may be called KernelVerified only if its transitive axiom \
               closure is a subset of this set.",
    })
}
