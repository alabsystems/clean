// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Server state and metrics types.
//!
//! This module contains the foundational types used by all request handlers:
//! - `ServerMetrics`: Runtime metrics for monitoring and optimization
//! - `ServerState`: Shared state including environment, metrics, and configuration

use super::core::run_with_env;
use super::off_runtime::Shared;
use super::shared_env::SharedEnv;
use crate::rpc::RpcError;
use crate::session_env::{SessionEnv, SessionId};
use crate::startup;
use clean_kernel::{Environment, TypeChecker};
use clean_parser::TacticPatterns;
use std::collections::HashMap;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::sync::{Mutex, RwLock};

/// Server-wide runtime metrics for monitoring and optimization
///
/// All counters use relaxed ordering for maximum throughput - exact counts
/// aren't critical, but trends are useful for AI agents.
#[derive(Debug, Default)]
pub struct ServerMetrics {
    /// Server start time (Unix timestamp in seconds)
    pub(crate) start_time_secs: AtomicU64,
    /// Total requests processed
    pub(crate) total_requests: AtomicU64,
    /// Total successful requests
    pub(crate) successful_requests: AtomicU64,
    /// Total failed requests (errors)
    pub(crate) failed_requests: AtomicU64,
    /// Total check requests
    pub(crate) check_requests: AtomicU64,
    /// Total prove requests
    pub(crate) prove_requests: AtomicU64,
    /// Total getType requests
    pub(crate) get_type_requests: AtomicU64,
    /// Total batchCheck requests
    pub(crate) batch_check_requests: AtomicU64,
    /// Total verifyCert requests
    pub(crate) verify_cert_requests: AtomicU64,
    /// Total batchVerifyCert requests
    pub(crate) batch_verify_cert_requests: AtomicU64,
    /// Total verifyCertArchive requests
    pub(crate) verify_cert_archive_requests: AtomicU64,
    /// Total batchVerifyCertArchive requests
    pub(crate) batch_verify_cert_archive_requests: AtomicU64,
    /// Total verifyC requests
    pub(crate) verify_c_requests: AtomicU64,
    /// Total items processed in batch operations
    pub(crate) batch_items_processed: AtomicU64,
    /// Total certificates verified
    pub(crate) certificates_verified: AtomicU64,
    /// Cumulative time spent in handlers (microseconds)
    pub(crate) cumulative_time_us: AtomicU64,
    /// Cumulative time spent in type checking (microseconds)
    pub(crate) type_check_time_us: AtomicU64,
    /// Cumulative time spent in certificate verification (microseconds)
    pub(crate) cert_verify_time_us: AtomicU64,
}

impl ServerMetrics {
    /// Create new metrics with current timestamp
    #[must_use]
    pub fn new() -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        let metrics = Self::default();
        metrics.start_time_secs.store(now, Ordering::Relaxed);
        metrics
    }

    /// Record a request
    pub(crate) fn record_request(&self, method: &str, success: bool, duration_us: u64) {
        self.total_requests.fetch_add(1, Ordering::Relaxed);
        if success {
            self.successful_requests.fetch_add(1, Ordering::Relaxed);
        } else {
            self.failed_requests.fetch_add(1, Ordering::Relaxed);
        }
        self.cumulative_time_us
            .fetch_add(duration_us, Ordering::Relaxed);

        // Track by method type
        match method {
            "check" => {
                self.check_requests.fetch_add(1, Ordering::Relaxed);
            }
            "prove" => {
                self.prove_requests.fetch_add(1, Ordering::Relaxed);
            }
            "getType" => {
                self.get_type_requests.fetch_add(1, Ordering::Relaxed);
            }
            "batchCheck" => {
                self.batch_check_requests.fetch_add(1, Ordering::Relaxed);
            }
            "verifyCert" => {
                self.verify_cert_requests.fetch_add(1, Ordering::Relaxed);
            }
            "batchVerifyCert" => {
                self.batch_verify_cert_requests
                    .fetch_add(1, Ordering::Relaxed);
            }
            "verifyCertArchive" => {
                self.verify_cert_archive_requests
                    .fetch_add(1, Ordering::Relaxed);
            }
            "batchVerifyCertArchive" => {
                self.batch_verify_cert_archive_requests
                    .fetch_add(1, Ordering::Relaxed);
            }
            "verifyC" => {
                self.verify_c_requests.fetch_add(1, Ordering::Relaxed);
            }
            _ => {}
        }
    }

    /// Record batch items processed
    pub(crate) fn record_batch_items(&self, count: u64) {
        self.batch_items_processed
            .fetch_add(count, Ordering::Relaxed);
    }

    /// Record certificates verified
    pub fn record_certs_verified(&self, count: u64) {
        self.certificates_verified
            .fetch_add(count, Ordering::Relaxed);
    }

    /// Record type checking time
    pub fn record_type_check_time(&self, duration_us: u64) {
        self.type_check_time_us
            .fetch_add(duration_us, Ordering::Relaxed);
    }

    /// Record certificate verification time
    pub fn record_cert_verify_time(&self, duration_us: u64) {
        self.cert_verify_time_us
            .fetch_add(duration_us, Ordering::Relaxed);
    }

    /// Get uptime in seconds
    pub fn uptime_secs(&self) -> u64 {
        let start = self.start_time_secs.load(Ordering::Relaxed);
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        now.saturating_sub(start)
    }

    /// Get average request latency in microseconds
    pub(crate) fn avg_latency_us(&self) -> u64 {
        let total = self.total_requests.load(Ordering::Relaxed);
        if total == 0 {
            return 0;
        }
        self.cumulative_time_us.load(Ordering::Relaxed) / total
    }

    /// Get requests per second (based on uptime)
    pub fn requests_per_second(&self) -> f64 {
        let uptime = self.uptime_secs();
        if uptime == 0 {
            return 0.0;
        }
        self.total_requests.load(Ordering::Relaxed) as f64 / uptime as f64
    }

    /// Get success rate (0.0 - 1.0)
    pub fn success_rate(&self) -> f64 {
        let total = self.total_requests.load(Ordering::Relaxed);
        if total == 0 {
            return 1.0;
        }
        self.successful_requests.load(Ordering::Relaxed) as f64 / total as f64
    }
}

/// Cache metrics sampled from recent type checker usage.
#[derive(Debug, Default)]
pub struct CacheMetrics {
    /// Cumulative type cache hits across requests
    pub(crate) type_cache_hits: AtomicU64,
    /// Cumulative type cache misses across requests
    pub(crate) type_cache_misses: AtomicU64,
    /// Last observed type cache entries
    pub(crate) type_cache_entries: AtomicU64,
    /// Whether type cache was enabled in the last sample (0/1)
    pub(crate) type_cache_enabled: AtomicU64,
    /// Last observed WHNF cache entries
    pub(crate) whnf_cache_entries: AtomicU64,
    /// Last observed def_eq cache entries
    pub(crate) def_eq_cache_entries: AtomicU64,
}

/// The cache counters of one type checker, taken where the checker ran (a
/// work-pool thread) and recorded where the request answers.
#[derive(Debug, Clone, Default)]
pub(crate) struct TypeCheckerSample {
    type_cache: Option<clean_kernel::TypeCheckCacheStats>,
    whnf_cache_entries: usize,
    def_eq_cache_entries: usize,
}

impl TypeCheckerSample {
    /// Sample `tc`'s caches.
    pub(crate) fn of(tc: &TypeChecker<'_>) -> Self {
        Self {
            type_cache: tc.type_cache_stats(),
            whnf_cache_entries: tc.whnf_cache_entries(),
            def_eq_cache_entries: tc.def_eq_cache_entries(),
        }
    }
}

impl CacheMetrics {
    /// Record cache metrics from a type checker instance.
    pub fn record_type_checker(&self, tc: &TypeChecker<'_>) {
        self.record_sample(&TypeCheckerSample::of(tc));
    }

    /// Record cache metrics sampled from a type checker.
    pub(crate) fn record_sample(&self, sample: &TypeCheckerSample) {
        if let Some(stats) = &sample.type_cache {
            self.type_cache_hits
                .fetch_add(stats.hits, Ordering::Relaxed);
            self.type_cache_misses
                .fetch_add(stats.misses, Ordering::Relaxed);
            self.type_cache_entries
                .store(stats.entries as u64, Ordering::Relaxed);
            self.type_cache_enabled.store(1, Ordering::Relaxed);
        } else {
            self.type_cache_entries.store(0, Ordering::Relaxed);
            self.type_cache_enabled.store(0, Ordering::Relaxed);
        }

        self.whnf_cache_entries
            .store(sample.whnf_cache_entries as u64, Ordering::Relaxed);
        self.def_eq_cache_entries
            .store(sample.def_eq_cache_entries as u64, Ordering::Relaxed);
    }
}

/// A swarm worker's session, behind a lock of its own: `addDecl`s to one
/// session are checked one at a time, in the order they reach the lock
/// (tokio's `Mutex` is fair), and never wait for another session's.
///
/// The session itself is a [`Shared`] value: an `addDecl` copies it on the
/// work pool from a share it hands its work, never on the runtime, and
/// replaces the share when its declaration is accepted. Whoever lets the last
/// share of a session go (the map closing it, an `addDecl` holding it when it
/// was closed, a replaced one) frees it off the runtime (`off_runtime.rs`).
pub(crate) type SessionHandle = Arc<Mutex<Shared<SessionEnv>>>;

/// Shared server state
pub struct ServerState {
    /// The kernel environment (shared, read-mostly; `shared_env.rs` says how
    /// a writer changes it).
    pub(crate) env: SharedEnv,
    /// Per-session isolated environments for swarm workers.
    ///
    /// Each entry is a worker's private overlay over a shared base snapshot of
    /// `env`. A worker's in-progress or rejected declarations live only in its
    /// [`SessionEnv`] overlay and are dropped on session close, so they can
    /// never pollute the shared corpus environment. See
    /// [`crate::session_env`]. The map is held only to look a session up, open
    /// one or close one; a session's own lock guards its overlay.
    pub(crate) sessions: RwLock<HashMap<SessionId, SessionHandle>>,
    /// Default timeout for operations (ms)
    pub(crate) default_timeout_ms: u64,
    /// GPU acceleration enabled
    pub(crate) gpu_enabled: bool,
    /// Number of worker threads for batch operations (0 = auto/Rayon default)
    pub(crate) worker_threads: usize,
    /// Server-wide metrics
    pub(crate) metrics: ServerMetrics,
    /// Proof state cache for LLM API
    pub(crate) proof_cache: crate::proof_state::ProofStateCache,
    /// Precomputed project theorem-index provider used by proof-state theorem search.
    pub(crate) theorem_index: crate::proof_state::ProjectTheoremIndexProvider,
    /// Cache metrics sampled from type checker usage
    pub(crate) cache_metrics: CacheMetrics,
    /// Shared .olean module cache for cross-request caching.
    /// Avoids re-parsing the same .olean files across repeated importModule calls.
    pub(crate) olean_cache: Arc<clean_olean::ModuleCache>,
    /// Cached tactic argument patterns for the parser.
    /// Computed once at startup from the built-in tactic registry; shared, so
    /// work handed to [`Self::work`] can parse with them.
    pub(crate) tactic_patterns: Arc<TacticPatterns>,
    /// The threads requests' synchronous work runs on, under each request's
    /// deadline (`handlers/work.rs`).
    pub(crate) work: super::work::WorkPool,
    /// Repo-root lean-toolchain identifier, if present.
    pub(crate) lean_toolchain: Option<String>,
    /// Resolved Lean version requested by `lean-toolchain`, if available.
    pub(crate) lean_toolchain_version: Option<String>,
    /// Widget state (infoview sources + per-document registrations) for the
    /// Lean 4 widget RPC endpoints. Interior-mutable so widget handlers can
    /// register and query sources through a shared `&ServerState`.
    pub(crate) widgets: RwLock<crate::rpc_widgets::WidgetState>,
    /// In-process Mathverse corpus handle for proof-state premise selection.
    ///
    /// Lazily loaded from the discovered library path at startup; empty (and
    /// thus a no-op yielding zero candidates) when no corpus is present, so the
    /// server still runs corpus-less. Cheaply cloneable; a clone is also
    /// registered as the process-global so the proof-state choke point can reach
    /// it without threading a handle through every signature.
    pub(crate) mathverse: crate::mathverse_provider::MathverseProvider,
    /// The directory `saveEnvironment`, `loadEnvironment` and `importModule`
    /// are confined to, as its real path (`trust_boundary::confine`): the
    /// directory the state was made in, or the root it was made for. `None`
    /// when that does not resolve, and then every path is refused.
    pub(crate) workspace_root: Option<std::path::PathBuf>,
    /// The token a connection presents first, and `replace_unchecked` and
    /// `importModule` in their own params. `None` when the system's random
    /// source could not be read, and then every check of it refuses (a
    /// transport will not start).
    pub(crate) launch_token: Option<crate::LaunchToken>,
}

impl ServerState {
    /// Create a new server state
    #[must_use]
    pub fn new() -> Self {
        let cwd = std::env::current_dir().ok();
        let toolchain = startup::read_workspace_toolchain(cwd.as_deref());
        let workspace_root = cwd.as_deref().and_then(real_root);

        Self {
            env: SharedEnv::new(Environment::new()),
            sessions: RwLock::new(HashMap::new()),
            default_timeout_ms: 5000,
            gpu_enabled: false,
            worker_threads: 0,
            metrics: ServerMetrics::new(),
            proof_cache: crate::proof_state::ProofStateCache::default_config(),
            theorem_index: crate::proof_state::ProjectTheoremIndexProvider::default(),
            cache_metrics: CacheMetrics::default(),
            olean_cache: Arc::new(clean_olean::ModuleCache::new()),
            tactic_patterns: Arc::new(clean_elab::tactic::builtins::builtin_tactic_patterns()),
            work: super::work::WorkPool::with_default_limit(),
            lean_toolchain: toolchain.identifier,
            lean_toolchain_version: toolchain.resolved_version,
            widgets: RwLock::new(crate::rpc_widgets::WidgetState::new()),
            mathverse: Self::init_mathverse_provider(),
            workspace_root,
            launch_token: new_launch_token(),
        }
    }

    /// Discover the Mathverse corpus and register it as the process-global
    /// provider used by the proof-state premise-selection choke point.
    ///
    /// Discovery is corpus-optional: if no shards are found, an empty provider
    /// is returned and installed, so a corpus-less server still runs. The global
    /// install is idempotent (first writer wins), so constructing multiple
    /// `ServerState`s (e.g. in tests) is safe.
    fn init_mathverse_provider() -> crate::mathverse_provider::MathverseProvider {
        let provider = crate::mathverse_provider::MathverseProvider::discover();
        crate::mathverse_provider::install_global(provider.clone());
        provider
    }

    /// Create a server state rooted at a specific workspace directory.
    #[must_use]
    pub fn from_root(root: &Path) -> Self {
        let toolchain = startup::read_workspace_toolchain(Some(root));
        let workspace_root = real_root(root);

        Self {
            env: SharedEnv::new(Environment::new()),
            sessions: RwLock::new(HashMap::new()),
            default_timeout_ms: 5000,
            gpu_enabled: false,
            worker_threads: 0,
            metrics: ServerMetrics::new(),
            proof_cache: crate::proof_state::ProofStateCache::default_config(),
            theorem_index: crate::proof_state::ProjectTheoremIndexProvider::default(),
            cache_metrics: CacheMetrics::default(),
            olean_cache: Arc::new(clean_olean::ModuleCache::new()),
            tactic_patterns: Arc::new(clean_elab::tactic::builtins::builtin_tactic_patterns()),
            work: super::work::WorkPool::with_default_limit(),
            lean_toolchain: toolchain.identifier,
            lean_toolchain_version: toolchain.resolved_version,
            widgets: RwLock::new(crate::rpc_widgets::WidgetState::new()),
            mathverse: Self::init_mathverse_provider(),
            workspace_root,
            launch_token: new_launch_token(),
        }
    }

    /// Confine the file methods to `root` instead (a test's scratch
    /// directory); a root that does not resolve refuses every path.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn with_workspace_root(mut self, root: &Path) -> Self {
        self.workspace_root = real_root(root);
        self
    }

    /// The workspace root the file methods are confined to, as a real path.
    pub(crate) fn workspace_root(&self) -> Option<&Path> {
        self.workspace_root.as_deref()
    }

    /// The token connections, `replace_unchecked` and `importModule` must
    /// present.
    pub(crate) fn launch_token(&self) -> Option<&crate::LaunchToken> {
        self.launch_token.as_ref()
    }

    /// Create with GPU enabled
    #[must_use]
    pub fn with_gpu(mut self, enabled: bool) -> Self {
        self.gpu_enabled = enabled;
        self
    }

    /// Create with worker thread count
    #[must_use]
    pub fn with_worker_threads(mut self, threads: usize) -> Self {
        self.worker_threads = threads;
        self
    }

    /// Create with a pre-populated environment (e.g. from --init/--stdlib pre-loading)
    #[must_use]
    pub fn with_env(mut self, env: Environment) -> Self {
        self.env = SharedEnv::new(env);
        self
    }

    /// Create with a precomputed math-project theorem index.
    #[must_use]
    pub fn with_project_theorem_index(
        mut self,
        report: clean_math_project::theorem_index::MathTheoremIndexReport,
    ) -> Self {
        self.theorem_index = crate::proof_state::ProjectTheoremIndexProvider::from_report(report);
        self
    }

    /// Create with a precomputed math-project theorem index loaded from JSON text.
    pub fn try_with_project_theorem_index_json(
        mut self,
        text: &str,
    ) -> Result<Self, serde_json::Error> {
        self.theorem_index = crate::proof_state::ProjectTheoremIndexProvider::from_json_str(text)?;
        Ok(self)
    }

    /// The in-process Mathverse corpus provider for premise selection.
    #[must_use]
    pub fn mathverse(&self) -> &crate::mathverse_provider::MathverseProvider {
        &self.mathverse
    }

    /// Get the repo-root `lean-toolchain` identifier, if present.
    #[must_use]
    pub fn lean_toolchain(&self) -> Option<&str> {
        self.lean_toolchain.as_deref()
    }

    /// Get the resolved toolchain version from `lean-toolchain`, if present.
    #[must_use]
    pub(crate) fn lean_toolchain_version(&self) -> Option<&str> {
        self.lean_toolchain_version.as_deref()
    }

    /// Register a widget JavaScript/HTML source under its content hash.
    ///
    /// Used by the widget RPC endpoints (and by tests / future
    /// elaboration-time registration) to make a source retrievable via
    /// `getWidgetSource`.
    #[cfg(test)]
    pub(crate) async fn register_widget_source(&self, hash: String, source: String) {
        self.widgets.write().await.register_source(hash, source);
    }

    /// Register goal-state widget metadata for a document URI.
    ///
    /// The metadata is the JSON shape consumed by
    /// [`crate::rpc_widgets::parse_widget_registrations`] (a `"widgets"`
    /// array). Replaces any prior registration for the same URI.
    #[cfg(test)]
    pub(crate) async fn register_document_widgets(&self, uri: String, metadata: serde_json::Value) {
        self.widgets
            .write()
            .await
            .register_document_widgets(uri, metadata);
    }

    /// Open a new isolated session for a swarm worker.
    ///
    /// Snapshots the current shared environment into an immutable base and
    /// gives the session a private overlay on top of it. The worker's
    /// declarations live only in that overlay until the session is closed
    /// (dropped), so an in-progress or rejected proof cannot pollute the
    /// shared corpus. Returns the new [`SessionId`].
    ///
    /// Snapshotting copies the environment (the base, then the overlay from
    /// it): work that grows with the environment, so it runs on the work pool,
    /// in its lock order (a slot, then a read hold on the environment), never
    /// on the runtime (R87, 2026-10-17). It has no deadline: no
    /// request asks for it, and a copy reads none. So it waits, with no bound
    /// of its own, for a free work slot and then for the environment: behind
    /// the requests holding every slot (each until its timeout, its work up to
    /// its next deadline read) and behind a writer. A caller that needs a
    /// bound awaits it inside a timeout of its own.
    ///
    /// # Errors
    ///
    /// The internal error when the work pool could not run the copy (no work
    /// thread could be started).
    pub async fn create_session(&self) -> Result<SessionId, RpcError> {
        let session = run_with_env(self, None, |held| {
            SessionEnv::new(Arc::new(Environment::clone(&held.env)))
        })
        .await
        .map_err(|error| error.into_rpc_error(std::time::Duration::ZERO))?;
        let id = SessionId::new();
        self.sessions
            .write()
            .await
            .insert(id, Arc::new(Mutex::new(Shared::new(session))));
        Ok(id)
    }

    /// The open session `id`, if any. The session map is held only for the
    /// look-up.
    pub(crate) async fn session(&self, id: &SessionId) -> Option<SessionHandle> {
        self.sessions.read().await.get(id).cloned()
    }

    /// Close (roll back) a session, dropping its overlay.
    ///
    /// Returns `true` if a session with this ID was present. Dropping the
    /// [`SessionEnv`] discards every session-local declaration; the shared
    /// base environment is never mutated, so the corpus stays pristine. An
    /// `addDecl` that has already looked the session up (holding its lock, or
    /// queued on it) finishes on the closed session, as if it ran before the
    /// close, and what it adds is dropped with it.
    ///
    /// A session holds a whole environment (its overlay), so the closed one is
    /// freed off the runtime (`off_runtime.rs`), after the session map's lock
    /// is let go: by the map's share here when it is the last, or by the
    /// `addDecl` that still holds the session, when that lets it go.
    pub async fn drop_session(&self, id: &SessionId) -> bool {
        let removed = self.sessions.write().await.remove(id);
        removed.is_some()
    }

    /// Number of currently open worker sessions.
    pub async fn session_count(&self) -> usize {
        self.sessions.read().await.len()
    }
}

/// `root`'s real path, the form confinement compares against.
fn real_root(root: &Path) -> Option<std::path::PathBuf> {
    match std::fs::canonicalize(root) {
        Ok(real) => Some(real),
        Err(error) => {
            tracing::error!(
                root = %root.display(),
                %error,
                "the workspace root does not resolve; every file method's path is refused"
            );
            None
        }
    }
}

/// A launch token for a new state; `None` (every check of it refusing) when
/// the system's random source cannot be read.
fn new_launch_token() -> Option<crate::LaunchToken> {
    match crate::LaunchToken::generate() {
        Ok(token) => Some(token),
        Err(error) => {
            tracing::error!(%error, "no launch token; every connection will be refused");
            None
        }
    }
}

impl Default for ServerState {
    fn default() -> Self {
        Self::new()
    }
}
