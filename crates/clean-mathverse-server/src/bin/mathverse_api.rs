//! `mathverse-api` — the Mathverse hosting service binary.
//!
//! Serves the JSON API (`/v1/*`) and SSR web (`/`) over a directory of
//! `.mathverse` shards. Designed for GCP Cloud Run: it honours the injected
//! `PORT` env var and binds `0.0.0.0`.

use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Context;
use clap::Parser;
use clean_mathverse_server::corpus::Corpus;
use clean_mathverse_server::{router, App, VERSION};

#[derive(Parser, Debug)]
#[command(name = "mathverse-api", version = VERSION, about = "Mathverse hosting service — browse/search API + web")]
struct Args {
    /// Directory of `.mathverse` shards to serve (the Core).
    #[arg(long, env = "MATHVERSE_CORPUS_DIR", default_value = "./corpus")]
    corpus_dir: PathBuf,

    /// Cap the number of shards merged into memory (useful for demos / small
    /// instances). Unset = load all.
    #[arg(long, env = "MATHVERSE_MAX_SHARDS")]
    max_shards: Option<usize>,

    /// Port to listen on. Cloud Run injects `PORT`.
    #[arg(long, env = "PORT", default_value_t = 8080)]
    port: u16,

    /// Bind address.
    #[arg(long, env = "MATHVERSE_BIND", default_value = "0.0.0.0")]
    bind: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    let args = Args::parse();

    tracing::info!(dir = %args.corpus_dir.display(), "loading corpus");
    let corpus = Corpus::load(&args.corpus_dir, args.max_shards)
        .with_context(|| format!("loading corpus from {}", args.corpus_dir.display()))?;

    if corpus.declaration_count() == 0 {
        tracing::warn!(
            dir = %args.corpus_dir.display(),
            "no declarations loaded — serving an empty corpus (set MATHVERSE_CORPUS_DIR \
             to a directory of .mathverse shards)"
        );
    }

    let state = Arc::new(App::new(corpus));
    let app = router(state);

    let addr: SocketAddr = format!("{}:{}", args.bind, args.port)
        .parse()
        .with_context(|| format!("invalid bind address {}:{}", args.bind, args.port))?;

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .with_context(|| format!("binding {addr}"))?;

    tracing::info!(%addr, version = VERSION, "mathverse-api listening");
    axum::serve(listener, app).await.context("server error")?;

    Ok(())
}
