// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof State Management for LLM Integration API
//!
//! Provides state management, caching, and serialization for verification-guided
//! proof search. Enables LLM provers to interact with clean incrementally.
//!
//! # Design
//!
//! - **StateId**: UUID v7 identifiers for proof states (time-ordered)
//! - **ProofStateCache**: LRU cache with TTL for state storage
//! - **ApiProofState**: Serializable proof state for API responses
//! - **TacticApiError**: Structured errors for LLM feedback
//!
//! # Reference
//!
//! - Primary contract: docs/reference/proof-state-serialization.md
//! - Design deltas: designs/2026-03-14-2716-interactive-trust-summary-surface.md,
//!   designs/2026-03-15-2285-pantograph-resume-token-contract.md
//! - Historical origin: #73

use clean_elab::tactic::{Goal, LocalDecl, ProofState as InternalProofState, TacticError};
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Name};
use lru::LruCache;
use serde::{Deserialize, Serialize};
use std::num::NonZeroUsize;
use std::str::FromStr;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use uuid::Uuid;

// ============================================================================
// State ID
// ============================================================================

/// Unique identifier for a proof state (UUID v7, time-ordered)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StateId(Uuid);

impl StateId {
    /// Generate a new state ID
    #[must_use]
    pub fn new() -> Self {
        Self(Uuid::now_v7())
    }

    /// Get the underlying UUID
    #[must_use]
    pub fn uuid(&self) -> Uuid {
        self.0
    }
}

impl Default for StateId {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for StateId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ps_{}", self.0.simple())
    }
}

impl FromStr for StateId {
    type Err = uuid::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Handle "ps_" prefix if present
        let s = s.strip_prefix("ps_").unwrap_or(s);
        Ok(Self(Uuid::parse_str(s)?))
    }
}

/// Unique identifier for a failed tactic attempt (UUID v7, time-ordered).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AttemptId(Uuid);

impl AttemptId {
    /// Generate a new failed-attempt ID.
    #[must_use]
    pub fn new() -> Self {
        Self(Uuid::now_v7())
    }
}

impl Default for AttemptId {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for AttemptId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "pa_{}", self.0.simple())
    }
}

impl FromStr for AttemptId {
    type Err = uuid::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.strip_prefix("pa_").unwrap_or(s);
        Ok(Self(Uuid::parse_str(s)?))
    }
}

// ============================================================================
// Cached State
// ============================================================================

/// Cached proof state with expiration and metadata
struct CachedState {
    /// The internal proof state
    state: InternalProofState,
    /// When this state was created (reserved for metrics/debugging)
    _created_at: Instant,
    /// When this state expires
    expires_at: Instant,
    /// Problem identifier (for tracking)
    problem_id: Option<String>,
    /// Step number in the proof
    step_number: u32,
    /// Parent state ID (for tree navigation)
    parent_id: Option<StateId>,
    /// Tactic that was applied to reach this state (None for initial state)
    tactic_applied: Option<String>,
    /// Trust policy inherited from `proofState.openObligation`, when present.
    trust_policy: Option<ObligationTrustPolicy>,
    /// Domain profile inherited from `proofState.openObligation`, or `General`.
    domain_profile: ObligationDomainProfile,
    /// Structured metadata inherited from `proofState.openObligation`, when present.
    metadata: Option<ProofStateMetadata>,
    /// Root state for lifecycle accounting.
    lifecycle_root_id: StateId,
    /// Maximum live states for this lifecycle group.
    max_states: usize,
    /// TTL applied to retained child states in this lifecycle group.
    ttl: Duration,
}

/// Persisted failed tactic attempt.
struct CachedFailure {
    failure: FailedTacticAttempt,
    expires_at: Instant,
}

// ============================================================================
// Cache Configuration
// ============================================================================

/// Configuration for proof state cache
#[derive(Debug, Clone)]
pub struct ProofStateCacheConfig {
    /// Maximum number of states to cache
    pub max_states: usize,
    /// Default TTL for states
    pub default_ttl: Duration,
}

impl Default for ProofStateCacheConfig {
    fn default() -> Self {
        Self {
            max_states: 10_000,
            default_ttl: Duration::from_secs(30 * 60), // 30 minutes
        }
    }
}

// ============================================================================
// Proof State Cache
// ============================================================================

/// LRU cache for proof states with TTL expiration
pub struct ProofStateCache {
    /// The underlying cache
    cache: RwLock<LruCache<StateId, CachedState>>,
    /// Failed tactic attempts available to `proofState.explainFailure`.
    failures: RwLock<LruCache<AttemptId, CachedFailure>>,
    /// Cache configuration
    config: ProofStateCacheConfig,
}

impl ProofStateCache {
    /// Create a new cache with the given configuration
    #[must_use]
    pub fn new(config: ProofStateCacheConfig) -> Self {
        const ONE: NonZeroUsize = NonZeroUsize::new(1).expect("invariant: 1 is non-zero");
        let cap = NonZeroUsize::new(config.max_states).unwrap_or(ONE);
        Self {
            cache: RwLock::new(LruCache::new(cap)),
            failures: RwLock::new(LruCache::new(cap)),
            config,
        }
    }

    /// Create a new cache with default configuration
    #[must_use]
    pub fn default_config() -> Self {
        Self::new(ProofStateCacheConfig::default())
    }

    /// Insert a new state, returning its ID
    pub fn insert(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            None,
            None,
            ObligationDomainProfile::General,
            None,
            self.config.default_ttl,
        )
    }

    /// Insert a new state with tactic tracking, returning its ID
    pub fn insert_with_tactic(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        tactic_applied: Option<String>,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            tactic_applied,
            None,
            ObligationDomainProfile::General,
            None,
            self.config.default_ttl,
        )
    }

    /// Insert a new state with tactic tracking and a trust policy, returning its ID.
    pub fn insert_with_tactic_and_trust_policy(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        tactic_applied: Option<String>,
        trust_policy: Option<ObligationTrustPolicy>,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            tactic_applied,
            trust_policy,
            ObligationDomainProfile::General,
            None,
            self.config.default_ttl,
        )
    }

    /// Insert a new state with tactic tracking, trust policy, and domain profile.
    pub fn insert_with_tactic_policy_and_domain(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        tactic_applied: Option<String>,
        trust_policy: Option<ObligationTrustPolicy>,
        domain_profile: ObligationDomainProfile,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            tactic_applied,
            trust_policy,
            domain_profile,
            None,
            self.config.default_ttl,
        )
    }

    /// Insert a new state with tactic tracking, trust policy, domain profile, and metadata.
    pub fn insert_with_tactic_policy_domain_and_metadata(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        tactic_applied: Option<String>,
        trust_policy: Option<ObligationTrustPolicy>,
        domain_profile: ObligationDomainProfile,
        metadata: Option<ProofStateMetadata>,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            tactic_applied,
            trust_policy,
            domain_profile,
            metadata,
            self.config.default_ttl,
        )
    }

    /// Insert a new state with an explicit TTL, returning its ID.
    pub fn insert_with_ttl(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        ttl: Duration,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            None,
            None,
            ObligationDomainProfile::General,
            None,
            ttl,
        )
    }

    /// Insert a new state with an explicit TTL and trust policy, returning its ID.
    pub fn insert_with_ttl_and_trust_policy(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        ttl: Duration,
        trust_policy: Option<ObligationTrustPolicy>,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            None,
            trust_policy,
            ObligationDomainProfile::General,
            None,
            ttl,
        )
    }

    /// Insert a new state with an explicit TTL, trust policy, and domain profile.
    pub fn insert_with_ttl_policy_and_domain(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        ttl: Duration,
        trust_policy: Option<ObligationTrustPolicy>,
        domain_profile: ObligationDomainProfile,
    ) -> StateId {
        self.insert_with_tactic_and_ttl(
            state,
            problem_id,
            parent_id,
            step_number,
            None,
            trust_policy,
            domain_profile,
            None,
            ttl,
        )
    }

    /// Insert the root of an open-obligation lifecycle group.
    pub fn insert_open_obligation(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        ttl: Duration,
        max_states: usize,
        trust_policy: Option<ObligationTrustPolicy>,
        domain_profile: ObligationDomainProfile,
        metadata: Option<ProofStateMetadata>,
    ) -> StateId {
        let id = StateId::new();
        let now = Instant::now();
        let cached = CachedState {
            state,
            _created_at: now,
            expires_at: saturating_expires_at(now, ttl),
            problem_id,
            step_number: 0,
            parent_id: None,
            tactic_applied: None,
            trust_policy,
            domain_profile,
            metadata,
            lifecycle_root_id: id,
            max_states: max_states.max(1),
            ttl,
        };

        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());
        cache.put(id, cached);
        id
    }

    /// Insert a child state, inheriting lifecycle metadata from its parent.
    pub fn insert_child(
        &self,
        state: InternalProofState,
        parent: &ProofStateRef,
        tactic_applied: Option<String>,
    ) -> Result<StateId, ProofStateLifecycleError> {
        let id = StateId::new();
        let now = Instant::now();
        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());
        evict_expired_from_cache(&mut cache, now);

        let live_in_group = cache
            .iter()
            .filter(|(_, cached)| cached.lifecycle_root_id == parent.lifecycle_root_id)
            .count();
        if live_in_group >= parent.max_states {
            return Err(ProofStateLifecycleError::MaxStatesExceeded {
                max_states: parent.max_states,
                live_states: live_in_group,
            });
        }

        let cached = CachedState {
            state,
            _created_at: now,
            expires_at: saturating_expires_at(now, parent.ttl),
            problem_id: parent.problem_id.clone(),
            step_number: parent.step_number + 1,
            parent_id: Some(parent.id),
            tactic_applied,
            trust_policy: parent.trust_policy,
            domain_profile: parent.domain_profile,
            metadata: parent.metadata.clone(),
            lifecycle_root_id: parent.lifecycle_root_id,
            max_states: parent.max_states,
            ttl: parent.ttl,
        };
        cache.put(id, cached);
        Ok(id)
    }

    fn insert_with_tactic_and_ttl(
        &self,
        state: InternalProofState,
        problem_id: Option<String>,
        parent_id: Option<StateId>,
        step_number: u32,
        tactic_applied: Option<String>,
        trust_policy: Option<ObligationTrustPolicy>,
        domain_profile: ObligationDomainProfile,
        metadata: Option<ProofStateMetadata>,
        ttl: Duration,
    ) -> StateId {
        let id = StateId::new();
        let now = Instant::now();
        let cached = CachedState {
            state,
            _created_at: now,
            expires_at: saturating_expires_at(now, ttl),
            problem_id,
            step_number,
            parent_id,
            tactic_applied,
            trust_policy,
            domain_profile,
            metadata,
            lifecycle_root_id: id,
            max_states: self.config.max_states,
            ttl,
        };

        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());
        cache.put(id, cached);
        id
    }

    /// Get a state by ID (None if expired or missing)
    #[must_use]
    pub fn get(&self, id: &StateId) -> Option<ProofStateRef> {
        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());

        let snapshot = if let Some(cached) = cache.get(id) {
            if Instant::now() < cached.expires_at {
                Some((
                    cached.state.clone(),
                    cached.problem_id.clone(),
                    cached.step_number,
                    cached.parent_id,
                    cached.tactic_applied.clone(),
                    cached.trust_policy,
                    cached.domain_profile,
                    cached.metadata.clone(),
                    cached.lifecycle_root_id,
                    cached.max_states,
                    cached.ttl,
                    cached.expires_at.saturating_duration_since(Instant::now()),
                ))
            } else {
                cache.pop(id);
                None
            }
        } else {
            None
        }?;

        let (
            state,
            problem_id,
            step_number,
            parent_id,
            tactic_applied,
            trust_policy,
            domain_profile,
            metadata,
            lifecycle_root_id,
            max_states,
            ttl,
            ttl_remaining,
        ) = snapshot;
        let tactic_script_prefix = reconstruct_tactic_script_from_cache(&cache, id);
        let live_states = live_states_in_group(&cache, lifecycle_root_id);
        Some(ProofStateRef {
            state,
            id: *id,
            problem_id,
            step_number,
            parent_id,
            tactic_applied,
            trust_policy,
            domain_profile,
            metadata,
            lifecycle_root_id,
            max_states,
            ttl,
            ttl_remaining,
            live_states,
            tactic_script_prefix,
        })
    }

    /// Reconstruct the tactic script by walking back through parent states
    pub fn reconstruct_tactic_script(&self, id: &StateId) -> Vec<String> {
        let cache = self.cache.read().unwrap_or_else(|e| e.into_inner());
        reconstruct_tactic_script_from_cache(&cache, id)
    }

    /// Remove a state from the cache
    pub fn remove(&self, id: &StateId) {
        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());
        cache.pop(id);
    }

    /// Remove a state and all descendants currently in cache.
    pub fn remove_subtree(&self, id: &StateId) -> bool {
        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());
        let keys: Vec<StateId> = cache.iter().map(|(state_id, _)| *state_id).collect();
        let mut removed = false;
        for candidate in keys {
            if candidate == *id || cached_state_has_ancestor(&cache, &candidate, id) {
                removed |= cache.pop(&candidate).is_some();
            }
        }
        removed
    }

    /// Retain a state by extending its TTL. Returns the effective lifecycle if found.
    pub fn retain(
        &self,
        id: &StateId,
        ttl: Option<Duration>,
    ) -> Option<ProofStateLifecycleMetadata> {
        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());
        let now = Instant::now();
        let (ttl_sec, ttl_remaining_sec, max_states, lifecycle_root_id) = {
            let cached = cache.get_mut(id)?;
            if now >= cached.expires_at {
                cache.pop(id);
                return None;
            }
            if let Some(ttl) = ttl {
                cached.ttl = ttl;
                cached.expires_at = saturating_expires_at(now, ttl);
            } else {
                cached.expires_at = saturating_expires_at(now, cached.ttl);
            }
            (
                cached.ttl.as_secs(),
                cached.expires_at.saturating_duration_since(now).as_secs(),
                cached.max_states,
                cached.lifecycle_root_id,
            )
        };
        Some(ProofStateLifecycleMetadata {
            ttl_sec,
            ttl_remaining_sec,
            max_states,
            live_states: live_states_in_group(&cache, lifecycle_root_id),
        })
    }

    /// Persist a failed tactic attempt.
    pub fn insert_failure(&self, failure: FailedTacticAttempt, ttl: Duration) -> AttemptId {
        let id = AttemptId::new();
        let cached = CachedFailure {
            failure,
            expires_at: saturating_expires_at(Instant::now(), ttl),
        };
        let mut failures = self.failures.write().unwrap_or_else(|e| e.into_inner());
        failures.put(id, cached);
        id
    }

    /// Get a persisted failed tactic attempt.
    pub fn get_failure(&self, id: &AttemptId) -> Option<FailedTacticAttempt> {
        let mut failures = self.failures.write().unwrap_or_else(|e| e.into_inner());
        let cached = failures.get(id)?;
        if Instant::now() < cached.expires_at {
            Some(cached.failure.clone())
        } else {
            failures.pop(id);
            None
        }
    }

    /// Evict expired states (call periodically for cleanup)
    pub fn evict_expired(&self) {
        let mut cache = self.cache.write().unwrap_or_else(|e| e.into_inner());
        evict_expired_from_cache(&mut cache, Instant::now());
    }

    /// Get the number of cached states
    #[must_use]
    pub fn len(&self) -> usize {
        self.cache.read().unwrap_or_else(|e| e.into_inner()).len()
    }

    /// Check if the cache is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.cache
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .is_empty()
    }
}

/// Compute an expiry `Instant` for a cache entry, saturating instead of
/// panicking when `now + ttl` would overflow the platform clock.
///
/// `std::time::Instant`'s `Add<Duration>` impl calls `.expect("overflow when
/// adding duration to instant")`, so an attacker-controlled `ttl` (e.g. a wire
/// `ttl_sec` near `u64::MAX` in `proofState.openObligation`) would abort the
/// server process. For realistic TTLs `checked_add` returns exactly the same
/// value as `+`, so correct-path behavior is unchanged; only the overflow path
/// is diverted to a far-future-but-valid capped expiry.
fn saturating_expires_at(now: Instant, ttl: Duration) -> Instant {
    // ~100 years — comfortably beyond any legitimate proof-state lifetime, yet
    // representable on all supported platforms.
    const EXPIRY_CAP: Duration = Duration::from_secs(100 * 365 * 24 * 60 * 60);
    now.checked_add(ttl)
        .or_else(|| now.checked_add(EXPIRY_CAP))
        // If even the cap overflows the clock, fall back to `now`: the entry is
        // treated as already-expired, which is the safe degenerate behavior.
        .unwrap_or(now)
}

fn evict_expired_from_cache(cache: &mut LruCache<StateId, CachedState>, now: Instant) {
    let expired: Vec<StateId> = cache
        .iter()
        .filter(|(_, v)| now >= v.expires_at)
        .map(|(k, _)| *k)
        .collect();

    for id in expired {
        cache.pop(&id);
    }
}

fn cached_state_has_ancestor(
    cache: &LruCache<StateId, CachedState>,
    state_id: &StateId,
    ancestor_id: &StateId,
) -> bool {
    let mut current_id = cache.peek(state_id).and_then(|cached| cached.parent_id);
    while let Some(id) = current_id {
        if id == *ancestor_id {
            return true;
        }
        current_id = cache.peek(&id).and_then(|cached| cached.parent_id);
    }
    false
}

fn live_states_in_group(
    cache: &LruCache<StateId, CachedState>,
    lifecycle_root_id: StateId,
) -> usize {
    cache
        .iter()
        .filter(|(_, cached)| cached.lifecycle_root_id == lifecycle_root_id)
        .count()
}

fn reconstruct_tactic_script_from_cache(
    cache: &LruCache<StateId, CachedState>,
    id: &StateId,
) -> Vec<String> {
    let mut script = Vec::new();
    let mut current_id = Some(*id);

    while let Some(state_id) = current_id {
        if let Some(cached) = cache.peek(&state_id) {
            if let Some(tactic) = &cached.tactic_applied {
                script.push(tactic.clone());
            }
            current_id = cached.parent_id;
        } else {
            break;
        }
    }

    script.reverse();
    script
}

// ============================================================================
// Proof State Reference
// ============================================================================

/// Reference to a cached proof state with metadata
#[derive(Debug, Clone)]
pub struct ProofStateRef {
    /// The internal proof state
    pub state: InternalProofState,
    /// State identifier
    pub id: StateId,
    /// Problem identifier
    pub problem_id: Option<String>,
    /// Step number
    pub step_number: u32,
    /// Parent state ID
    pub parent_id: Option<StateId>,
    /// Tactic that was applied to reach this state
    pub tactic_applied: Option<String>,
    /// Trust policy inherited from `proofState.openObligation`, when present.
    pub trust_policy: Option<ObligationTrustPolicy>,
    /// Domain profile inherited from `proofState.openObligation`, or `General`.
    pub domain_profile: ObligationDomainProfile,
    /// Structured metadata inherited from `proofState.openObligation`, when present.
    pub metadata: Option<ProofStateMetadata>,
    /// Root state for lifecycle accounting.
    pub lifecycle_root_id: StateId,
    /// Maximum live states for this lifecycle group.
    pub max_states: usize,
    /// TTL applied to child states in this lifecycle group.
    pub ttl: Duration,
    /// Remaining TTL for this state at read time.
    pub ttl_remaining: Duration,
    /// Current live states in this lifecycle group.
    pub live_states: usize,
    /// Tactics from the root state to this state, in application order.
    pub tactic_script_prefix: Vec<String>,
}

/// Lifecycle metadata returned by retain/close style handlers.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProofStateLifecycleMetadata {
    /// Effective TTL in seconds.
    pub ttl_sec: u64,
    /// Remaining TTL in seconds.
    pub ttl_remaining_sec: u64,
    /// Effective maximum live branch states.
    pub max_states: usize,
    /// Current live states in this lifecycle group.
    pub live_states: usize,
}

/// Cache lifecycle insertion failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStateLifecycleError {
    /// Inserting another state would exceed the lifecycle max.
    MaxStatesExceeded {
        /// Effective max state count.
        max_states: usize,
        /// Current live state count.
        live_states: usize,
    },
}

/// Persisted failed tactic attempt.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailedTacticAttempt {
    /// State used by the failed attempt.
    pub state_id: String,
    /// Focused goal requested by the caller.
    pub goal_id: String,
    /// Tactic text that failed.
    pub tactic: String,
    /// Structured tactic error returned by apply.
    pub error: TacticApiError,
    /// Step number of the source proof state.
    pub step_number: u32,
    /// Lifecycle metadata at failure time.
    pub lifecycle: ProofStateLifecycleMetadata,
}

// ============================================================================
// API Response Types
// ============================================================================

/// Serializable goal for API responses
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiGoal {
    /// Unique identifier for this goal
    pub goal_id: String,
    /// Target type (full expression, JSON serialized)
    pub target: Expr,
    /// Pretty-printed target (for LLM format)
    pub target_pp: String,
    /// Stable summary of the target and local context.
    #[serde(default)]
    pub summary: ApiGoalSummary,
    /// Head symbol of the target, when structurally available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_head: Option<String>,
    /// Constant symbols mentioned by the target.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub target_symbols: Vec<String>,
    /// Available hypotheses
    pub hypotheses: Vec<ApiHypothesis>,
    /// Stable summaries of local hypotheses and let-bindings.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub local_context_summary: Vec<ApiLocalContextSummary>,
    /// Context summary (for LLM format)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context_summary: Option<String>,
}

/// Stable goal summary for proof-factory agents.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ApiGoalSummary {
    /// Number of local declarations in scope.
    pub local_count: usize,
    /// Number of local let-bindings in scope.
    pub let_count: usize,
    /// Head symbol of the target, when structurally available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_head: Option<String>,
    /// Constant symbols mentioned by the target.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub target_symbols: Vec<String>,
}

/// Stable summary of one local declaration.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ApiLocalContextSummary {
    /// Hypothesis or local variable name.
    pub name: String,
    /// Head symbol of the declaration type, when structurally available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_head: Option<String>,
    /// Constant symbols mentioned by the declaration type.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub type_symbols: Vec<String>,
    /// Whether this local declaration has a value.
    pub is_let: bool,
}

/// Serializable hypothesis for API responses
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiHypothesis {
    /// Hypothesis name
    pub name: String,
    /// Type expression (full)
    pub type_expr: Expr,
    /// Pretty-printed type
    pub type_pp: String,
    /// Optional value (for let-bindings)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<Expr>,
    /// Pretty-printed value
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value_pp: Option<String>,
    /// Binder info string
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binder_info: Option<String>,
}

/// API proof state response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiProofState {
    /// State identifier
    pub state_id: String,
    /// Current goals
    pub goals: Vec<ApiGoal>,
    /// Whether the proof is complete
    pub is_solved: bool,
    /// Step number in the proof
    pub step_number: u32,
    /// Problem identifier
    #[serde(skip_serializing_if = "Option::is_none")]
    pub problem_id: Option<String>,
    /// Structured proof-state metadata for project/obligation-backed states.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<ProofStateMetadata>,
    /// Parent state identifier
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent_state_id: Option<String>,
    /// Tactic applied to the parent state to produce this state.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tactic_applied: Option<String>,
    /// Tactics from the root state to this state, in application order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub tactic_script_prefix: Vec<String>,
    /// Relevant lemmas (for LLM format)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relevant_lemmas: Option<Vec<RelevantLemma>>,
    /// Search hints (for LLM format)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub search_hints: Option<Vec<String>>,
    /// Trust-filtered Mathverse Library candidates for the current proof state.
    #[serde(default)]
    pub mathverse_candidates: Vec<MathverseCandidate>,
    /// Live trust summary for the current proof state (#2716).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<crate::handlers::TrustSummary>,
    /// Cache lifecycle metadata for this state.
    #[serde(default)]
    pub lifecycle: ProofStateLifecycleMetadata,
}

/// Relevant lemma suggestion
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelevantLemma {
    /// Lemma name
    pub name: String,
    /// Pretty-printed type
    pub type_pp: String,
    /// Relevance score (0.0 - 1.0)
    pub relevance: f64,
    /// Optional source/index provenance for non-environment candidates.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub provenance: Option<RelevantLemmaProvenance>,
    /// Optional trust decision surfaced by the theorem-index provider.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust: Option<RelevantLemmaTrust>,
}

/// Source metadata for a theorem-search candidate.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct RelevantLemmaProvenance {
    /// Provider label, e.g. `math-project-theorem-index`.
    pub source: String,
    /// Math project name, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub project: Option<String>,
    /// Source theorem-pack path, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_path: Option<String>,
    /// Source module, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub module: Option<String>,
    /// Stable theorem-index candidate fingerprint.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidate_fingerprint: Option<String>,
}

/// Trust decision attached to a theorem-search candidate.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RelevantLemmaTrust {
    /// Trust policy used by the precomputed index.
    pub policy: String,
    /// Candidate conformance under that policy.
    pub conformance: String,
    /// Kernel proof status claimed by the index.
    pub kernel_proof_status: String,
    /// Trust debt labels carried by the indexed declaration.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub trust_debt: Vec<String>,
    /// Whether the index considered this candidate promotable.
    pub promotion_allowed: bool,
    /// Reasons this candidate was blocked or downranked.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reasons: Vec<String>,
}

/// Trust-filtered Mathverse Library candidate suggestion.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct MathverseCandidate {
    /// Declaration name.
    pub name: String,
    /// Pretty-printed theorem/definition type.
    pub type_pp: String,
    /// Relevance score assigned by the Mathverse retrieval provider.
    pub relevance: f64,
    /// Trust level after filtering, e.g. KernelVerified or CertificateReplayed.
    pub trust_level: String,
    /// Optional source system label, e.g. Lean4, Coq, Metamath.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_system: Option<String>,
    /// Optional content-domain label used by Mathverse shards.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub domain: Option<String>,
}

/// LLM-oriented guidance derived from a proof state's focused goal.
#[derive(Debug, Clone, Default)]
pub(crate) struct LlmStateGuidance {
    /// Relevant lemmas from premise selection.
    pub relevant_lemmas: Vec<RelevantLemma>,
    /// Human-readable search hints for the focused goal.
    pub search_hints: Vec<String>,
    /// Machine-friendly tactic suggestions for the focused goal.
    pub suggested_tactics: Vec<String>,
    /// Trust-filtered Mathverse Library candidates for the focused goal.
    pub mathverse_candidates: Vec<MathverseCandidate>,
}

/// In-memory provider for precomputed math-project theorem-index candidates.
#[derive(Debug, Clone, Default)]
pub struct ProjectTheoremIndexProvider {
    reports: Arc<RwLock<Vec<clean_math_project::theorem_index::MathTheoremIndexReport>>>,
}

impl ProjectTheoremIndexProvider {
    #[must_use]
    pub fn from_report(report: clean_math_project::theorem_index::MathTheoremIndexReport) -> Self {
        Self::from_reports(vec![report])
    }

    #[must_use]
    pub fn from_reports(
        reports: Vec<clean_math_project::theorem_index::MathTheoremIndexReport>,
    ) -> Self {
        Self {
            reports: Arc::new(RwLock::new(reports)),
        }
    }

    pub fn from_json_str(text: &str) -> Result<Self, serde_json::Error> {
        clean_math_project::theorem_index::parse_theorem_index_json_str(text).map(Self::from_report)
    }

    pub fn from_path(path: &std::path::Path) -> Result<Self, clean_math_project::MathProjectError> {
        clean_math_project::theorem_index::load_theorem_index(path).map(Self::from_report)
    }

    pub fn replace_reports(
        &self,
        reports: Vec<clean_math_project::theorem_index::MathTheoremIndexReport>,
    ) {
        *self.reports.write().unwrap_or_else(|e| e.into_inner()) = reports;
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.reports
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .is_empty()
    }

    #[must_use]
    pub fn search(
        &self,
        state: &InternalProofState,
        env: &Environment,
        domain_profile: ObligationDomainProfile,
        trust_policy: Option<ObligationTrustPolicy>,
        max_lemmas: usize,
    ) -> Vec<RelevantLemma> {
        self.search_goal(
            state.goals().front(),
            env,
            domain_profile,
            trust_policy,
            max_lemmas,
        )
    }

    #[must_use]
    pub fn search_goal(
        &self,
        goal: Option<&Goal>,
        env: &Environment,
        domain_profile: ObligationDomainProfile,
        trust_policy: Option<ObligationTrustPolicy>,
        max_lemmas: usize,
    ) -> Vec<RelevantLemma> {
        if max_lemmas == 0 {
            return Vec::new();
        }

        let mut target_symbols = Vec::new();
        if let Some(goal) = goal {
            collect_expr_symbols(&goal.target, &mut target_symbols);
        }
        let target_terms = normalized_goal_terms(goal, env, &target_symbols);
        let domain = domain_profile.as_wire_str();
        let reports = self.reports.read().unwrap_or_else(|e| e.into_inner());
        let mut scored = Vec::new();
        let mut seen = std::collections::BTreeSet::new();

        for report in reports.iter().filter(|report| report.is_supported_schema()) {
            for candidate in &report.candidates {
                if !project_candidate_allowed_by_policy(candidate, trust_policy) {
                    continue;
                }
                if !seen.insert(candidate.name.clone()) {
                    continue;
                }
                let relevance =
                    project_candidate_relevance(candidate, report, domain, &target_terms);
                scored.push((
                    relevance,
                    candidate.name.clone(),
                    project_candidate_relevant_lemma(candidate, report, env, relevance),
                ));
            }
        }

        scored.sort_by(|left, right| {
            right
                .0
                .partial_cmp(&left.0)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| left.1.cmp(&right.1))
        });
        scored
            .into_iter()
            .take(max_lemmas)
            .map(|(_, _, lemma)| lemma)
            .collect()
    }
}

fn project_candidate_allowed_by_policy(
    candidate: &clean_math_project::theorem_index::ProjectTheoremCandidate,
    trust_policy: Option<ObligationTrustPolicy>,
) -> bool {
    if !candidate.trust_decision.promotion_allowed
        || candidate.trust_decision.conformance != "conforming"
    {
        return false;
    }

    match trust_policy {
        Some(ObligationTrustPolicy::ConstructiveOnly) => candidate
            .trust_decision
            .trust_debt
            .iter()
            .all(|debt| !constructive_project_debt_rejected(debt)),
        Some(ObligationTrustPolicy::AllowTrustedArith) => candidate
            .trust_decision
            .trust_debt
            .iter()
            .all(|debt| !trusted_arith_policy_project_debt_rejected(debt)),
        Some(ObligationTrustPolicy::KernelCheckedImports) | None => candidate
            .trust_decision
            .trust_debt
            .iter()
            .all(|debt| !kernel_import_project_debt_rejected(debt)),
    }
}

fn constructive_project_debt_rejected(debt: &str) -> bool {
    matches!(
        debt,
        "explicit_sorry" | "synthetic_sorry" | "unsafe" | "axiom"
    ) || debt.starts_with("trusted_arith:")
        || debt.starts_with("trusted_ay:")
}

fn kernel_import_project_debt_rejected(debt: &str) -> bool {
    matches!(debt, "explicit_sorry" | "synthetic_sorry" | "unsafe")
        || debt.starts_with("trusted_arith:")
        || debt.starts_with("trusted_ay:")
}

fn trusted_arith_policy_project_debt_rejected(debt: &str) -> bool {
    matches!(debt, "explicit_sorry" | "synthetic_sorry" | "unsafe")
        || debt.starts_with("trusted_ay:")
}

fn normalized_goal_terms(
    goal: Option<&Goal>,
    env: &Environment,
    target_symbols: &[String],
) -> Vec<String> {
    let mut terms = Vec::new();
    if let Some(goal) = goal {
        terms.push(normalized_project_search_term(&pp_expr(&goal.target, env)));
    }
    for symbol in target_symbols {
        terms.push(normalized_project_search_term(symbol));
        if let Some(short) = symbol.rsplit('.').next() {
            terms.push(normalized_project_search_term(short));
        }
    }
    terms.retain(|term| term.len() >= 3);
    terms.sort();
    terms.dedup();
    terms
}

fn normalized_project_search_term(value: &str) -> String {
    value
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric())
        .flat_map(char::to_lowercase)
        .collect()
}

fn project_candidate_relevance(
    candidate: &clean_math_project::theorem_index::ProjectTheoremCandidate,
    report: &clean_math_project::theorem_index::MathTheoremIndexReport,
    domain_profile: &str,
    target_terms: &[String],
) -> f64 {
    let domain_match = report.project.domain_profile == domain_profile
        || candidate.domain_signals.profile == domain_profile;
    let mut relevance: f64 = if domain_match { 0.91 } else { 0.78 };

    if candidate.classification.local {
        relevance += 0.03;
    }
    if candidate.classification.project {
        relevance += 0.02;
    }
    if candidate.classification.domain || candidate.domain_signals.module_match {
        relevance += 0.02;
    }
    if !candidate.domain_signals.semantic_head_matches.is_empty() {
        relevance += 0.02;
    }
    if !candidate.domain_signals.ranking_signal_matches.is_empty() {
        relevance += 0.01;
    }

    let candidate_haystack = normalized_project_search_term(&format!(
        "{} {} {}",
        candidate.name, candidate.module, candidate.source_path
    ));
    if target_terms
        .iter()
        .any(|term| !term.is_empty() && candidate_haystack.contains(term))
    {
        relevance += 0.02;
    }

    relevance.min(0.995)
}

fn project_candidate_relevant_lemma(
    candidate: &clean_math_project::theorem_index::ProjectTheoremCandidate,
    report: &clean_math_project::theorem_index::MathTheoremIndexReport,
    env: &Environment,
    relevance: f64,
) -> RelevantLemma {
    RelevantLemma {
        name: candidate.name.clone(),
        type_pp: project_candidate_type_pp(candidate, env),
        relevance,
        provenance: Some(RelevantLemmaProvenance {
            source: "math-project-theorem-index".to_owned(),
            project: Some(report.project.name.clone()),
            source_path: Some(candidate.source_path.clone()),
            module: Some(candidate.module.clone()),
            candidate_fingerprint: Some(candidate.candidate_fingerprint.clone()),
        }),
        trust: Some(RelevantLemmaTrust {
            policy: candidate.trust_decision.policy.clone(),
            conformance: candidate.trust_decision.conformance.clone(),
            kernel_proof_status: candidate.trust_decision.kernel_proof_status.clone(),
            trust_debt: candidate.trust_decision.trust_debt.clone(),
            promotion_allowed: candidate.trust_decision.promotion_allowed,
            reasons: candidate.trust_decision.reasons.clone(),
        }),
    }
}

fn project_candidate_type_pp(
    candidate: &clean_math_project::theorem_index::ProjectTheoremCandidate,
    env: &Environment,
) -> String {
    env.get_const(&Name::from_string(&candidate.name))
        .map(|info| pp_expr(&info.type_, env))
        .unwrap_or_else(|| {
            let fingerprint = candidate
                .candidate_fingerprint
                .get(..12)
                .unwrap_or(&candidate.candidate_fingerprint);
            format!(
                "indexed theorem candidate from {} (fingerprint {fingerprint})",
                candidate.source_path
            )
        })
}

/// Output format for proof state
#[derive(Debug, Clone, Copy, Deserialize, Default, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum OutputFormat {
    /// LLM-optimized: pretty-printed, with lemmas and hints
    #[default]
    Llm,
    /// Full debugging info: complete Expr AST
    Full,
    /// Compact: minimal IDs for storage
    Compact,
}

// ============================================================================
// proofState.openObligation API Types
// ============================================================================

/// Current request schema for dynamic proof obligations.
pub const OPEN_OBLIGATION_SCHEMA_VERSION: &str = "clean-open-obligation-v1";

/// Current proof-state response schema selected by `proofState.openObligation`.
pub const PROOF_STATE_SCHEMA_VERSION: &str = "clean-proof-state-v2";

/// Dynamic obligation request for `proofState.openObligation`.
///
/// This is a product-facing schema foundation only. It describes a dynamic goal,
/// artifacts, trust policy, and lifecycle preferences; handler-side elaboration
/// and state insertion are intentionally separate.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct OpenObligationRequest {
    /// Request payload schema, currently [`OPEN_OBLIGATION_SCHEMA_VERSION`].
    pub schema_version: String,
    /// Environment identifier chosen by the caller or server.
    pub environment_id: String,
    /// Domain-specific normalizer/search profile.
    pub domain_profile: ObligationDomainProfile,
    /// Goal payload supplied by the caller.
    pub goal: ObligationGoalPayload,
    /// Local hypotheses available to the obligation.
    #[serde(default)]
    pub local_context: Vec<ObligationLocalHypothesis>,
    /// External artifacts referenced by content hash/path.
    #[serde(default)]
    pub artifact_refs: Vec<ObligationArtifactRef>,
    /// Optional structured metadata to persist with the proof state.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<ProofStateMetadata>,
    /// Trust policy requested for proof construction.
    pub trust_policy: ObligationTrustPolicy,
    /// Requested state TTL in seconds.
    pub ttl_sec: u64,
    /// Requested maximum live branch states for this obligation.
    pub max_states: usize,
    /// Minimum proof-state response schema accepted by the caller.
    pub min_schema_version: String,
    /// Maximum proof-state response schema accepted by the caller.
    pub max_schema_version: String,
}

impl OpenObligationRequest {
    /// Validate request metadata and select the proof-state response schema.
    pub fn validate(&self) -> Result<OpenObligationValidation, OpenObligationValidationError> {
        if self.schema_version != OPEN_OBLIGATION_SCHEMA_VERSION {
            return Err(OpenObligationValidationError::UnsupportedRequestSchema {
                requested: self.schema_version.clone(),
                supported: OPEN_OBLIGATION_SCHEMA_VERSION.to_string(),
            });
        }
        if self.environment_id.trim().is_empty() {
            return Err(OpenObligationValidationError::MissingField {
                field: "environment_id",
            });
        }
        if self.goal.pretty.trim().is_empty() && self.goal.expr.is_none() {
            return Err(OpenObligationValidationError::MissingGoalPayload);
        }
        if self.ttl_sec == 0 {
            return Err(OpenObligationValidationError::InvalidLifecycle {
                field: "ttl_sec",
                message: "ttl_sec must be greater than zero".to_string(),
            });
        }
        if self.max_states == 0 {
            return Err(OpenObligationValidationError::InvalidLifecycle {
                field: "max_states",
                message: "max_states must be greater than zero".to_string(),
            });
        }

        let selected_schema = negotiate_schema_version(
            &self.min_schema_version,
            &self.max_schema_version,
            PROOF_STATE_SCHEMA_VERSION,
        )?;

        Ok(OpenObligationValidation { selected_schema })
    }
}

/// Successful validation metadata for an open-obligation request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenObligationValidation {
    /// Selected proof-state response schema.
    pub selected_schema: String,
}

/// Validation errors for `proofState.openObligation` request metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpenObligationValidationError {
    /// The request payload schema is not supported.
    UnsupportedRequestSchema {
        requested: String,
        supported: String,
    },
    /// Required string field is empty.
    MissingField { field: &'static str },
    /// Goal lacks both a pretty payload and an expression payload.
    MissingGoalPayload,
    /// Lifecycle field is outside accepted bounds.
    InvalidLifecycle {
        field: &'static str,
        message: String,
    },
    /// Schema version string does not use a supported `...-vN` suffix.
    InvalidSchemaVersion { field: &'static str, value: String },
    /// Caller supplied `min_schema_version` greater than `max_schema_version`.
    ImpossibleSchemaRange { min: String, max: String },
    /// Server cannot provide any schema in the requested range.
    UnsupportedSchemaRange {
        min: String,
        max: String,
        supported: String,
    },
}

impl std::fmt::Display for OpenObligationValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedRequestSchema {
                requested,
                supported,
            } => write!(
                f,
                "unsupported open-obligation schema `{requested}`; supported `{supported}`"
            ),
            Self::MissingField { field } => write!(f, "missing required field `{field}`"),
            Self::MissingGoalPayload => {
                write!(f, "goal must include `pretty` text or an `expr` payload")
            }
            Self::InvalidLifecycle { field, message } => {
                write!(f, "invalid lifecycle field `{field}`: {message}")
            }
            Self::InvalidSchemaVersion { field, value } => {
                write!(f, "invalid schema version in `{field}`: `{value}`")
            }
            Self::ImpossibleSchemaRange { min, max } => {
                write!(
                    f,
                    "impossible schema range: min `{min}` is greater than max `{max}`"
                )
            }
            Self::UnsupportedSchemaRange {
                min,
                max,
                supported,
            } => write!(
                f,
                "unsupported schema range `{min}`..`{max}`; supported `{supported}`"
            ),
        }
    }
}

impl std::error::Error for OpenObligationValidationError {}

/// Domain profile used to choose obligation-specific normalizers and search.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum ObligationDomainProfile {
    /// ay SAT/PB certificate and checker obligations.
    SatPb,
    /// SMT-style proof obligations.
    Smt,
    /// Linear/nonlinear arithmetic obligations.
    Arithmetic,
    /// Neural-network verifier proof obligations.
    NnVerify,
    /// Generic Lean proof-state work.
    General,
}

impl ObligationDomainProfile {
    /// Stable wire spelling used by serde for this enum.
    #[must_use]
    pub fn as_wire_str(self) -> &'static str {
        match self {
            Self::SatPb => "sat-pb",
            Self::Smt => "smt",
            Self::Arithmetic => "arithmetic",
            Self::NnVerify => "nn-verify",
            Self::General => "general",
        }
    }
}

/// Trust policy requested by an open-obligation caller.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum ObligationTrustPolicy {
    /// Kernel/proof-producing paths only; no trusted arithmetic/oracle fallback.
    ConstructiveOnly,
    /// Kernel-checked imported artifacts may be used.
    KernelCheckedImports,
    /// Explicitly allow trusted arithmetic debt in returned trust summaries.
    AllowTrustedArith,
}

impl ObligationTrustPolicy {
    /// Stable wire spelling used by serde for this enum.
    #[must_use]
    pub fn as_wire_str(self) -> &'static str {
        match self {
            Self::ConstructiveOnly => "constructive-only",
            Self::KernelCheckedImports => "kernel-checked-imports",
            Self::AllowTrustedArith => "allow-trusted-arith",
        }
    }
}

/// Return whether a tactic application is allowed under an obligation trust policy.
///
/// Missing policy means a legacy/default proof state, which remains permissive.
#[must_use]
pub fn trust_policy_allows_tactic(
    trust_policy: Option<ObligationTrustPolicy>,
    tactic: &str,
) -> bool {
    !matches!(
        trust_policy,
        Some(ObligationTrustPolicy::ConstructiveOnly)
            if constructive_only_rejected_tactic(tactic).is_some()
    )
}

/// The tactic name rejected by `ConstructiveOnly`, if this tactic is disallowed.
#[must_use]
pub fn constructive_only_rejected_tactic(tactic: &str) -> Option<&str> {
    let tactic_name = tactic.split_whitespace().next()?;
    match tactic_name {
        "sorry" | "admit" | "omega" | "linarith" | "nlinarith" | "ay_smt" | "native_decide" => {
            Some(tactic_name)
        }
        _ => None,
    }
}

/// Backward-compatible structured metadata carried by cached proof states.
#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProofStateMetadata {
    /// Math project name, when the state originated from a math project.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub project: Option<String>,
    /// Path to the project manifest supplied by the caller.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub project_path: Option<String>,
    /// Project root directory supplied by the caller.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub project_root: Option<String>,
    /// Stable obligation fingerprint for project-backed states.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_fingerprint: Option<String>,
    /// Path to the obligation source JSON supplied by the caller.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_source_path: Option<String>,
    /// Origin label for the obligation source, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_origin: Option<String>,
    /// Producer metadata copied from the obligation, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub producer: Option<ProofStateProducerMetadata>,
    /// Artifact references associated with the obligation.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub artifact_refs: Vec<ObligationArtifactRef>,
}

/// Producer metadata copied into [`ProofStateMetadata`].
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProofStateProducerMetadata {
    /// Producer system label.
    pub system: String,
    /// Producer commit or version.
    pub commit: String,
    /// Producer command line, when supplied by the obligation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command: Option<String>,
}

/// Goal payload for a dynamic obligation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ObligationGoalPayload {
    /// Optional serialized Lean expression for the goal target.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expr: Option<Expr>,
    /// Pretty-printed goal target for agents and logs.
    pub pretty: String,
    /// Optional type expression for the goal payload, when the caller has it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub type_expr: Option<Expr>,
    /// Pretty-printed type payload for logs and language bindings.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub type_pp: Option<String>,
}

/// Local hypothesis payload for a dynamic obligation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ObligationLocalHypothesis {
    /// User-facing hypothesis name.
    pub name: String,
    /// Optional serialized type expression.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub type_expr: Option<Expr>,
    /// Pretty-printed hypothesis type.
    pub type_pp: String,
    /// Optional let-bound value expression.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value_expr: Option<Expr>,
    /// Pretty-printed let-bound value.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value_pp: Option<String>,
}

/// External artifact reference for large checker/certificate inputs.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ObligationArtifactRef {
    /// Artifact kind.
    pub kind: ObligationArtifactKind,
    /// Content hash when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    /// Local path or URI when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    /// Optional media type or schema label.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub media_type: Option<String>,
}

/// Known dynamic-obligation artifact kinds.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum ObligationArtifactKind {
    /// OPB input.
    Opb,
    /// VeriPB proof/checker artifact.
    #[serde(rename = "veripb")]
    VeriPb,
    /// DIMACS CNF input.
    Dimacs,
    /// LRAT proof.
    Lrat,
    /// DRAT proof.
    Drat,
    /// Lean-side artifact.
    Lean,
    /// Other caller-defined artifact.
    Other,
}

/// Response shape for a future `proofState.openObligation` handler.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpenObligationResponse {
    /// Selected proof-state response schema.
    pub schema_version: String,
    /// Server-side state identifier, when a handler has opened one.
    pub state_id: String,
    /// Environment identifier backing the state.
    pub environment_id: String,
    /// Domain profile accepted for this obligation.
    pub domain_profile: ObligationDomainProfile,
    /// Initial proof-state snapshot under `schema_version`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub initial_snapshot: Option<ApiProofState>,
    /// Lifecycle limits applied by the server.
    pub lifecycle: OpenObligationLifecycle,
    /// Artifact references accepted into the state metadata.
    #[serde(default)]
    pub artifact_refs: Vec<ObligationArtifactRef>,
    /// Non-fatal validation or policy warnings.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

/// Lifecycle metadata returned by `proofState.openObligation`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct OpenObligationLifecycle {
    /// Effective TTL in seconds.
    pub ttl_sec: u64,
    /// Effective maximum live branch states.
    pub max_states: usize,
}

fn negotiate_schema_version(
    min_schema: &str,
    max_schema: &str,
    supported_schema: &str,
) -> Result<String, OpenObligationValidationError> {
    let min_version = schema_version_number("min_schema_version", min_schema)?;
    let max_version = schema_version_number("max_schema_version", max_schema)?;
    let supported_version = schema_version_number("supported_schema_version", supported_schema)?;

    if min_version > max_version {
        return Err(OpenObligationValidationError::ImpossibleSchemaRange {
            min: min_schema.to_string(),
            max: max_schema.to_string(),
        });
    }
    if supported_version < min_version || supported_version > max_version {
        return Err(OpenObligationValidationError::UnsupportedSchemaRange {
            min: min_schema.to_string(),
            max: max_schema.to_string(),
            supported: supported_schema.to_string(),
        });
    }

    Ok(supported_schema.to_string())
}

fn schema_version_number(
    field: &'static str,
    schema: &str,
) -> Result<u32, OpenObligationValidationError> {
    let Some((_, version)) = schema.rsplit_once("-v") else {
        return Err(OpenObligationValidationError::InvalidSchemaVersion {
            field,
            value: schema.to_string(),
        });
    };
    version
        .parse::<u32>()
        .map_err(|_| OpenObligationValidationError::InvalidSchemaVersion {
            field,
            value: schema.to_string(),
        })
}

// ============================================================================
// Structured Error Types
// ============================================================================

/// Structured tactic error for API responses
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticApiError {
    /// Error code
    pub code: TacticErrorCode,
    /// Human-readable error message
    pub message: String,
    /// Detailed error information
    #[serde(skip_serializing_if = "Option::is_none")]
    pub details: Option<TacticErrorDetails>,
    /// Suggestions for fixing the error
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub suggestions: Vec<String>,
}

/// Error codes for tactic failures
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
#[non_exhaustive]
pub enum TacticErrorCode {
    /// Failed to parse tactic
    ParseError,
    /// Unknown tactic name
    UnknownTactic,
    /// Invalid tactic syntax
    InvalidSyntax,
    /// Type mismatch
    TypeMismatch,
    /// Unification failed
    UnificationFailed,
    /// Tactic failed to apply
    TacticFailed,
    /// No matching goal found
    NoMatchingGoal,
    /// Goal not closed by tactic
    GoalNotClosed,
    /// Operation timed out
    Timeout,
    /// Memory limit exceeded
    MemoryExceeded,
    /// Invalid state ID
    InvalidStateId,
    /// State expired from cache
    StateExpired,
    /// No goals remaining
    NoGoals,
    /// Tactic is not allowed by the proof state's trust policy
    TrustPolicyViolation,
    /// Proof-state lifecycle limits rejected the transition.
    LifecycleLimitExceeded,
}

/// Detailed error information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticErrorDetails {
    /// Expected type (for type errors)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected_type: Option<String>,
    /// Actual type found
    #[serde(skip_serializing_if = "Option::is_none")]
    pub actual_type: Option<String>,
    /// Type difference
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diff: Option<TypeDiff>,
    /// Failed constraints
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub failed_constraints: Vec<String>,
    /// Execution trace
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub trace: Vec<String>,
}

/// Type difference for error messages
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDiff {
    /// Expected type
    pub expected: String,
    /// Actual type
    pub actual: String,
}

impl TacticApiError {
    /// Create an error for an invalid state ID
    #[must_use]
    pub fn invalid_state_id(state_id: &str) -> Self {
        Self {
            code: TacticErrorCode::InvalidStateId,
            message: format!("state {} not found or expired", state_id),
            details: None,
            suggestions: vec![
                "State may have expired. Use initProofState to create a new state.".to_string(),
            ],
        }
    }

    /// Create a parse error
    #[must_use]
    pub fn parse_error(msg: impl Into<String>) -> Self {
        Self {
            code: TacticErrorCode::ParseError,
            message: format!("failed to parse tactic: {}", msg.into()),
            details: None,
            suggestions: vec![],
        }
    }

    /// Create an unknown tactic error
    #[must_use]
    pub fn unknown_tactic(name: impl Into<String>) -> Self {
        let name = name.into();
        Self {
            code: TacticErrorCode::UnknownTactic,
            message: format!("unknown tactic: {}", name),
            details: None,
            suggestions: vec![format!(
                "Available tactics: intro, exact, apply, rfl, simp, ring, omega, aesop"
            )],
        }
    }

    fn with_code(code: TacticErrorCode, message: String) -> Self {
        Self {
            code,
            message,
            details: None,
            suggestions: vec![],
        }
    }

    /// Create an error for a tactic rejected by a proof state's trust policy.
    #[must_use]
    pub fn trust_policy_violation(
        policy: ObligationTrustPolicy,
        tactic_name: impl Into<String>,
    ) -> Self {
        let tactic_name = tactic_name.into();
        Self {
            code: TacticErrorCode::TrustPolicyViolation,
            message: format!(
                "tactic `{tactic_name}` is rejected by trust policy `{}`",
                policy.as_wire_str()
            ),
            details: None,
            suggestions: vec![
                "Use a kernel-constructive tactic, or reopen the obligation with a permissive trust policy."
                    .to_string(),
            ],
        }
    }

    /// Create an error when a proof-state lifecycle limit rejects a transition.
    #[must_use]
    pub fn with_lifecycle_limit(max_states: usize, live_states: usize) -> Self {
        Self {
            code: TacticErrorCode::LifecycleLimitExceeded,
            message: format!(
                "proof-state lifecycle max_states exceeded: max_states={max_states}, live_states={live_states}"
            ),
            details: Some(TacticErrorDetails {
                expected_type: None,
                actual_type: None,
                diff: None,
                failed_constraints: vec![format!(
                    "live_states ({live_states}) must be less than max_states ({max_states})"
                )],
                trace: vec![],
            }),
            suggestions: vec![
                "Close unused proof states with proofState.close or reopen with a higher max_states."
                    .to_string(),
            ],
        }
    }
}

impl From<TacticError> for TacticApiError {
    fn from(err: TacticError) -> Self {
        match err {
            TacticError::NoGoals => Self::with_code(TacticErrorCode::NoGoals, "no goals".into()),
            TacticError::TypeMismatch { expected, actual } => TacticApiError {
                code: TacticErrorCode::TypeMismatch,
                message: format!("type mismatch: expected {expected}, got {actual}"),
                details: Some(TacticErrorDetails {
                    expected_type: Some(expected.clone()),
                    actual_type: Some(actual.clone()),
                    diff: Some(TypeDiff { expected, actual }),
                    failed_constraints: vec![],
                    trace: vec![],
                }),
                suggestions: vec![],
            },
            TacticError::GoalMismatch(msg) => Self::with_code(
                TacticErrorCode::TacticFailed,
                format!("goal mismatch: {msg}"),
            ),
            TacticError::UnknownIdent(name) => Self::with_code(
                TacticErrorCode::UnknownTactic,
                format!("unknown identifier: {name}"),
            ),
            TacticError::TypeCheckFailed(msg) => TacticApiError {
                code: TacticErrorCode::TypeMismatch,
                message: format!("type check failed: {msg}"),
                details: Some(TacticErrorDetails {
                    expected_type: None,
                    actual_type: None,
                    diff: None,
                    failed_constraints: vec![],
                    trace: vec![msg],
                }),
                suggestions: vec![],
            },
            TacticError::UnificationFailed(msg) => Self::with_code(
                TacticErrorCode::UnificationFailed,
                format!("unification failed: {msg}"),
            ),
            TacticError::HypothesisNotFound(name) => TacticApiError {
                code: TacticErrorCode::TacticFailed,
                message: format!("hypothesis not found: {name}"),
                details: None,
                suggestions: vec!["Check available hypotheses with getProofState".into()],
            },
            _ => Self::with_code(TacticErrorCode::TacticFailed, err.to_string()),
        }
    }
}

// ============================================================================
// Apply Tactic Result
// ============================================================================

/// Result of applying a tactic
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApplyTacticResult {
    /// Whether the tactic succeeded
    pub success: bool,
    /// New state ID (same as input if failed)
    pub new_state_id: String,
    /// New goals after tactic application
    pub new_goals: Vec<ApiGoal>,
    /// Whether the proof is now complete
    pub is_solved: bool,
    /// Error information (if failed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<TacticApiError>,
    /// Persisted failure attempt ID, present only when the tactic failed on a valid state.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub attempt_id: Option<String>,
    /// Suggestions for next steps
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub suggestions: Vec<String>,
    /// Time taken in microseconds
    pub time_us: u64,
    /// Time taken in nanoseconds (normalized alias, Part of #2515)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time_ns: Option<u64>,
    /// Trust-filtered Mathverse Library candidates for the current proof state.
    #[serde(default)]
    pub mathverse_candidates: Vec<MathverseCandidate>,
    /// Live trust summary for the current proof state (#2716).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_summary: Option<crate::handlers::TrustSummary>,
}

// ============================================================================
// Pretty Printer
// ============================================================================

/// Pretty-print an expression (Lean-like syntax)
pub fn pp_expr(expr: &Expr, _env: &Environment) -> String {
    pp_expr_prec(expr, 0)
}

fn pp_expr_prec(expr: &Expr, prec: u8) -> String {
    use clean_kernel::Level;

    match expr.kind() {
        ExprKind::BVar(idx) => format!("#{}", idx),
        ExprKind::FVar(fvar) => format!("?f{}", fvar.as_u64()),
        ExprKind::Sort(level) => {
            if level.is_zero() {
                "Prop".to_string()
            } else if matches!(level, Level::Succ(inner) if inner.is_zero()) {
                "Type".to_string()
            } else {
                format!("Sort {}", level)
            }
        }
        ExprKind::Const(name, levels) => {
            if levels.is_empty() {
                format!("{}", name)
            } else {
                let lvls: Vec<String> = levels.iter().map(|l| format!("{}", l)).collect();
                format!("{}.{{{}}}", name, lvls.join(", "))
            }
        }
        ExprKind::App(f, arg) => {
            let f_str = pp_expr_prec(f, 10);
            let arg_str = pp_expr_prec(arg, 11);
            let s = format!("{} {}", f_str, arg_str);
            if prec > 10 {
                format!("({})", s)
            } else {
                s
            }
        }
        ExprKind::Lam(bi, domain, body) => {
            let bi_str = pp_binder_info(bi.info);
            let dom_str = pp_expr_prec(domain, 0);
            let body_str = pp_expr_prec(body, 0);
            let s = format!("fun {} : {} => {}", bi_str, dom_str, body_str);
            if prec > 0 {
                format!("({})", s)
            } else {
                s
            }
        }
        ExprKind::Pi(_bi, domain, body) => {
            let dom_str = pp_expr_prec(domain, 0);
            let body_str = pp_expr_prec(body, 0);
            let s = if body.has_loose_bvar(0) {
                format!("∀ _ : {}, {}", dom_str, body_str)
            } else {
                format!("{} → {}", dom_str, body_str)
            };
            if prec > 1 {
                format!("({})", s)
            } else {
                s
            }
        }
        ExprKind::Let(name, ty, val, body, _) => {
            let ty_str = pp_expr_prec(ty, 0);
            let val_str = pp_expr_prec(val, 0);
            let body_str = pp_expr_prec(body, 0);
            format!("let {} : {} := {} in {}", name, ty_str, val_str, body_str)
        }
        ExprKind::Lit(lit) => match lit {
            clean_kernel::Literal::Nat(n) => n.to_string(),
            clean_kernel::Literal::String(s) => format!("\"{}\"", s),
        },
        ExprKind::Proj(name, idx, base) => {
            let base_str = pp_expr_prec(base, 11);
            format!("{}.{}.{}", base_str, name, idx)
        }
        ExprKind::MData(_, inner) | ExprKind::Squash(inner) => pp_expr_prec(inner, prec),
        // Extended variants (Cubical, SProp, etc.) - display as placeholder
        _ => "<extended>".to_string(),
    }
}

fn pp_binder_info(bi: BinderInfo) -> &'static str {
    match bi {
        BinderInfo::Default => "_",
        BinderInfo::Implicit => "{_}",
        BinderInfo::StrictImplicit => "{{_}}",
        BinderInfo::InstImplicit => "[_]",
    }
}

// ============================================================================
// Conversion Functions
// ============================================================================

/// Convert internal goals to API goals
pub fn convert_goals(state: &InternalProofState, env: &Environment) -> Vec<ApiGoal> {
    state
        .goals()
        .iter()
        .enumerate()
        .map(|(i, g)| convert_goal(g, i, env))
        .collect()
}

/// Convert a single goal to API format
fn convert_goal(goal: &Goal, index: usize, env: &Environment) -> ApiGoal {
    let target_head = expr_head_symbol(&goal.target);
    let target_symbols = expr_symbols(&goal.target);
    let local_context_summary: Vec<ApiLocalContextSummary> =
        goal.local_ctx.iter().map(summarize_local_decl).collect();
    let let_count = local_context_summary
        .iter()
        .filter(|summary| summary.is_let)
        .count();
    let summary = ApiGoalSummary {
        local_count: goal.local_ctx.len(),
        let_count,
        target_head: target_head.clone(),
        target_symbols: target_symbols.clone(),
    };
    let context_summary = context_summary_for_goal(&summary, &local_context_summary);

    ApiGoal {
        goal_id: format!("g{}", index),
        target: goal.target.clone(),
        target_pp: pp_expr(&goal.target, env),
        summary,
        target_head,
        target_symbols,
        hypotheses: goal
            .local_ctx
            .iter()
            .map(|h| convert_hypothesis(h, env))
            .collect(),
        local_context_summary,
        context_summary,
    }
}

/// Convert a hypothesis to API format
fn convert_hypothesis(hyp: &LocalDecl, env: &Environment) -> ApiHypothesis {
    ApiHypothesis {
        name: hyp.name.clone(),
        type_expr: hyp.ty.clone(),
        type_pp: pp_expr(&hyp.ty, env),
        value: hyp.value.clone(),
        value_pp: hyp.value.as_ref().map(|v| pp_expr(v, env)),
        binder_info: None, // NOTE: Binder info needs elab LocalDecl change (#83) - add bi field to clean_elab::tactic::LocalDecl
    }
}

fn summarize_local_decl(hyp: &LocalDecl) -> ApiLocalContextSummary {
    ApiLocalContextSummary {
        name: hyp.name.clone(),
        type_head: expr_head_symbol(&hyp.ty),
        type_symbols: expr_symbols(&hyp.ty),
        is_let: hyp.value.is_some(),
    }
}

fn context_summary_for_goal(
    summary: &ApiGoalSummary,
    locals: &[ApiLocalContextSummary],
) -> Option<String> {
    let mut parts = Vec::new();

    if let Some(head) = &summary.target_head {
        parts.push(format!("target_head={head}"));
    }
    if !summary.target_symbols.is_empty() {
        parts.push(format!(
            "target_symbols={}",
            summary.target_symbols.join(",")
        ));
    }
    if summary.local_count > 0 {
        let names: Vec<&str> = locals.iter().map(|local| local.name.as_str()).collect();
        parts.push(format!(
            "locals={}:{}",
            summary.local_count,
            names.join(",")
        ));
    }
    if summary.let_count > 0 {
        parts.push(format!("lets={}", summary.let_count));
    }

    if parts.is_empty() {
        None
    } else {
        Some(parts.join("; "))
    }
}

fn expr_head_symbol(expr: &Expr) -> Option<String> {
    match expr.strip_mdata().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        ExprKind::App(_, _) => match expr.strip_mdata().get_app_fn().strip_mdata().kind() {
            ExprKind::Const(name, _) => Some(name.to_string()),
            ExprKind::FVar(fvar) => Some(format!("fvar:{}", fvar.as_u64())),
            ExprKind::BVar(idx) => Some(format!("bvar:{idx}")),
            _ => None,
        },
        ExprKind::Pi(_, _, body) => expr_head_symbol(body),
        ExprKind::Lam(_, _, body) => expr_head_symbol(body),
        ExprKind::Let(_, _, _, body, _) => expr_head_symbol(body),
        ExprKind::Proj(name, _, _) => Some(name.to_string()),
        ExprKind::FVar(fvar) => Some(format!("fvar:{}", fvar.as_u64())),
        ExprKind::BVar(idx) => Some(format!("bvar:{idx}")),
        ExprKind::Sort(level) if level.is_zero() => Some("Prop".to_string()),
        ExprKind::Sort(_) => Some("Sort".to_string()),
        ExprKind::Lit(_) => Some("literal".to_string()),
        ExprKind::Squash(inner) => expr_head_symbol(inner),
        ExprKind::SProp => Some("SProp".to_string()),
        _ => None,
    }
}

fn expr_symbols(expr: &Expr) -> Vec<String> {
    let mut symbols = Vec::new();
    collect_expr_symbols(expr, &mut symbols);
    symbols.sort();
    symbols.dedup();
    symbols
}

fn collect_expr_symbols(expr: &Expr, symbols: &mut Vec<String>) {
    match expr.strip_mdata().kind() {
        ExprKind::Const(name, _) => symbols.push(name.to_string()),
        ExprKind::App(f, arg) => {
            collect_expr_symbols(f, symbols);
            collect_expr_symbols(arg, symbols);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_expr_symbols(ty, symbols);
            collect_expr_symbols(body, symbols);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_expr_symbols(ty, symbols);
            collect_expr_symbols(val, symbols);
            collect_expr_symbols(body, symbols);
        }
        ExprKind::Proj(name, _, base) => {
            symbols.push(name.to_string());
            collect_expr_symbols(base, symbols);
        }
        ExprKind::MData(_, inner) | ExprKind::Squash(inner) => collect_expr_symbols(inner, symbols),
        ExprKind::CubicalPath { ty, left, right } => {
            collect_expr_symbols(ty, symbols);
            collect_expr_symbols(left, symbols);
            collect_expr_symbols(right, symbols);
        }
        ExprKind::CubicalPathLam { body } => collect_expr_symbols(body, symbols),
        ExprKind::CubicalPathApp { path, arg } => {
            collect_expr_symbols(path, symbols);
            collect_expr_symbols(arg, symbols);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            collect_expr_symbols(ty, symbols);
            collect_expr_symbols(phi, symbols);
            collect_expr_symbols(u, symbols);
            collect_expr_symbols(base, symbols);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            collect_expr_symbols(ty, symbols);
            collect_expr_symbols(phi, symbols);
            collect_expr_symbols(base, symbols);
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            collect_expr_symbols(ty, symbols);
            collect_expr_symbols(r, symbols);
            collect_expr_symbols(s, symbols);
            collect_expr_symbols(base, symbols);
        }
        ExprKind::ZFCMem { element, set } => {
            collect_expr_symbols(element, symbols);
            collect_expr_symbols(set, symbols);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            collect_expr_symbols(domain, symbols);
            collect_expr_symbols(pred, symbols);
        }
        ExprKind::ZFCSet(_)
        | ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => {}
    }
}

/// Convert ProofStateRef to ApiProofState
///
/// The `trust_summary` parameter is a precomputed trust summary from the
/// handler layer. This keeps kernel-checking in handler space and avoids
/// teaching proof_state.rs how to verify proofs (#2716).
pub fn to_api_state(
    state_ref: &ProofStateRef,
    env: &Environment,
    format: OutputFormat,
    trust_summary: Option<crate::handlers::TrustSummary>,
) -> ApiProofState {
    let goals = convert_goals(&state_ref.state, env);
    let is_solved = state_ref.state.is_complete();

    // For LLM format, add relevant lemmas and search hints
    let (relevant_lemmas, search_hints) = if format == OutputFormat::Llm && !is_solved {
        let lemmas =
            select_relevant_lemmas_for_profile(&state_ref.state, env, state_ref.domain_profile, 16);
        let hints = generate_search_hints(&state_ref.state, env);
        (
            if lemmas.is_empty() {
                None
            } else {
                Some(lemmas)
            },
            if hints.is_empty() { None } else { Some(hints) },
        )
    } else {
        (None, None)
    };

    ApiProofState {
        state_id: state_ref.id.to_string(),
        goals,
        is_solved,
        step_number: state_ref.step_number,
        problem_id: state_ref.problem_id.clone(),
        metadata: state_ref.metadata.clone(),
        parent_state_id: state_ref.parent_id.map(|id| id.to_string()),
        tactic_applied: state_ref.tactic_applied.clone(),
        tactic_script_prefix: state_ref.tactic_script_prefix.clone(),
        relevant_lemmas,
        search_hints,
        mathverse_candidates: mathverse_candidates_for_state(&state_ref.state, env),
        trust_summary,
        lifecycle: ProofStateLifecycleMetadata {
            ttl_sec: state_ref.ttl.as_secs(),
            ttl_remaining_sec: state_ref.ttl_remaining.as_secs(),
            max_states: state_ref.max_states,
            live_states: state_ref.live_states,
        },
    }
}

/// Return Mathverse Library candidates that have already passed the trust filter.
///
/// Runs the corpus-backed premise selector
/// ([`clean_mathverse::premise_select::search_for_kernel_goal`]) over the
/// focused goal of `state`, using the process-global Mathverse provider
/// installed at server startup. The provider already applies a kernel-verified
/// trust policy, so every returned [`MathverseCandidate`] has passed the trust
/// gate. When no corpus is loaded (corpus-less deployment) this returns an empty
/// list. Both Task C's freshly-added session declarations (once the session env
/// is folded into the corpus) and the on-disk corpus become visible here.
pub fn mathverse_candidates_for_state(
    state: &InternalProofState,
    env: &Environment,
) -> Vec<MathverseCandidate> {
    mathverse_candidates_for_goal(state.goals().front(), env)
}

/// Candidate retrieval for a single focused goal (the shared core of
/// [`mathverse_candidates_for_state`] and the LLM-guidance path).
fn mathverse_candidates_for_goal(
    goal: Option<&Goal>,
    _env: &Environment,
) -> Vec<MathverseCandidate> {
    let goal = match goal {
        Some(goal) => goal,
        None => return Vec::new(),
    };

    // Local hypothesis names already in scope feed the dependency-neighbor
    // channel of the premise selector.
    let context_names: Vec<&str> = goal
        .local_ctx
        .iter()
        .map(|decl| decl.name.as_str())
        .collect();

    crate::mathverse_provider::global().candidates_for_goal(&goal.target, &context_names)
}

/// Build LLM-facing guidance for the current proof state.
pub(crate) fn llm_guidance_for_state(
    state: &InternalProofState,
    env: &Environment,
) -> LlmStateGuidance {
    llm_guidance_for_state_and_profile(state, env, ObligationDomainProfile::General)
}

/// Build LLM-facing guidance for the current proof state under a domain profile.
pub(crate) fn llm_guidance_for_state_and_profile(
    state: &InternalProofState,
    env: &Environment,
    domain_profile: ObligationDomainProfile,
) -> LlmStateGuidance {
    llm_guidance_for_goal_and_profile(state, state.goals().front(), env, domain_profile)
}

/// Build LLM-facing guidance for a specific live goal under a domain profile.
pub(crate) fn llm_guidance_for_goal_and_profile(
    _state: &InternalProofState,
    goal: Option<&Goal>,
    env: &Environment,
    domain_profile: ObligationDomainProfile,
) -> LlmStateGuidance {
    LlmStateGuidance {
        relevant_lemmas: select_relevant_lemmas_for_goal_and_profile(goal, env, domain_profile, 16),
        search_hints: generate_search_hints_for_goal(goal, env),
        suggested_tactics: suggest_tactics_for_goal_and_profile(goal, env, domain_profile),
        mathverse_candidates: mathverse_candidates_for_goal(goal, env),
    }
}

fn select_relevant_lemmas_for_profile(
    state: &InternalProofState,
    env: &Environment,
    domain_profile: ObligationDomainProfile,
    max_lemmas: usize,
) -> Vec<RelevantLemma> {
    select_relevant_lemmas_for_goal_and_profile(
        state.goals().front(),
        env,
        domain_profile,
        max_lemmas,
    )
}

fn select_relevant_lemmas_for_goal_and_profile(
    goal: Option<&Goal>,
    env: &Environment,
    domain_profile: ObligationDomainProfile,
    max_lemmas: usize,
) -> Vec<RelevantLemma> {
    let generic = select_relevant_lemmas_for_goal(goal, env, max_lemmas);
    if domain_profile == ObligationDomainProfile::General {
        return generic;
    }

    let mut candidates = select_profile_lemmas(env, domain_profile, max_lemmas);
    for lemma in generic {
        if candidates.len() >= max_lemmas {
            break;
        }
        if !candidates
            .iter()
            .any(|existing| existing.name == lemma.name)
        {
            candidates.push(lemma);
        }
    }
    candidates
}

fn select_profile_lemmas(
    env: &Environment,
    domain_profile: ObligationDomainProfile,
    max_lemmas: usize,
) -> Vec<RelevantLemma> {
    let keywords = profile_keywords(domain_profile);
    if keywords.is_empty() {
        return Vec::new();
    }

    let mut scored = Vec::new();
    for info in env.constants() {
        if !is_prop_type(&info.type_) {
            continue;
        }
        let name = info.name.to_string();
        let type_pp = pp_expr(&info.type_, env);
        let haystack = format!("{name} {type_pp}").to_ascii_lowercase();
        let score = keywords
            .iter()
            .filter(|keyword| haystack.contains(**keyword))
            .count();
        if score > 0 {
            scored.push((score, name, type_pp));
        }
    }

    scored.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    scored
        .into_iter()
        .take(max_lemmas)
        .map(|(score, name, type_pp)| RelevantLemma {
            name,
            type_pp,
            relevance: (0.80 + (score as f64 * 0.05)).min(0.99),
            provenance: None,
            trust: None,
        })
        .collect()
}

fn profile_keywords(domain_profile: ObligationDomainProfile) -> &'static [&'static str] {
    match domain_profile {
        ObligationDomainProfile::SatPb => &[
            "sat", "pb", "pseudo", "boolean", "cert", "veripb", "opb", "lrat", "drat",
        ],
        ObligationDomainProfile::NnVerify => &[
            "nn", "neural", "network", "verify", "crown", "zonotope", "relu", "bound",
        ],
        ObligationDomainProfile::Smt => &["smt", "z3", "ay", "sat", "unsat"],
        ObligationDomainProfile::Arithmetic => {
            &["arith", "mathverse", "linear", "nat", "int", "rat"]
        }
        ObligationDomainProfile::General => &[],
    }
}

/// Select relevant lemmas for the current proof state using MePo
fn select_relevant_lemmas(
    state: &InternalProofState,
    env: &Environment,
    max_lemmas: usize,
) -> Vec<RelevantLemma> {
    select_relevant_lemmas_for_goal(state.goals().front(), env, max_lemmas)
}

fn select_relevant_lemmas_for_goal(
    goal: Option<&Goal>,
    env: &Environment,
    max_lemmas: usize,
) -> Vec<RelevantLemma> {
    use clean_auto::premise::{MePoSelector, PremiseDatabase};

    // Build premise database from environment
    let mut premise_db = PremiseDatabase::new();
    for info in env.constants() {
        // Only include theorems/lemmas (things with Prop types)
        if is_prop_type(&info.type_) {
            premise_db.add(info.name.clone(), info.type_.clone());
        }
    }

    if premise_db.is_empty() {
        return Vec::new();
    }

    let selector = MePoSelector::new(&premise_db)
        .with_threshold(0.05)
        .with_max_premises(max_lemmas);

    let Some(goal) = goal else {
        return Vec::new();
    };

    selector
        .select_with_scores(&goal.target)
        .into_iter()
        .map(|(premise, score)| RelevantLemma {
            name: premise.name.to_string(),
            type_pp: pp_expr(&premise.statement, env),
            relevance: score,
            provenance: None,
            trust: None,
        })
        .collect()
}

/// Check if an expression is a Prop type (theorem/lemma)
fn is_prop_type(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Sort(level) => level.is_zero(),
        ExprKind::Pi(_, _, body) => is_prop_type(body),
        _ => false,
    }
}

fn looks_like_equality_target(target_pp: &str) -> bool {
    target_pp.contains(" = ") || target_pp.starts_with("Eq")
}

/// Generate search hints based on goal patterns
fn generate_search_hints(state: &InternalProofState, env: &Environment) -> Vec<String> {
    generate_search_hints_for_goal(state.goals().front(), env)
}

fn generate_search_hints_for_goal(goal: Option<&Goal>, env: &Environment) -> Vec<String> {
    let mut hints = Vec::new();

    let Some(goal) = goal else {
        return hints;
    };

    let target = &goal.target;
    let target_pp = pp_expr(target, env);
    let hyps = &goal.local_ctx;
    let has_nat_context = target_pp.contains("Nat")
        || target_pp.contains("ℕ")
        || hyps.iter().any(|hyp| {
            let hyp_pp = pp_expr(&hyp.ty, env);
            hyp_pp.contains("Nat") || hyp_pp.contains("ℕ")
        });

    // Pattern-based hints
    if looks_like_equality_target(&target_pp) {
        hints.push("Goal is an equality - try: rfl, simp, ring, linarith".to_string());
    }
    if target_pp.contains(" → ") || target_pp.contains("->") {
        hints.push("Goal has implication - try: intro, intros".to_string());
    }
    if target_pp.contains("∀") || target_pp.contains("forall") {
        hints.push("Goal has universal quantifier - try: intro, intros".to_string());
    }
    if target_pp.contains("∃") || target_pp.contains("Exists") {
        hints.push("Goal has existential quantifier - try: use, exists".to_string());
    }
    if target_pp.contains("∧") || target_pp.contains("And") {
        hints.push("Goal is a conjunction - try: constructor, and_iff_right".to_string());
    }
    if target_pp.contains("∨") || target_pp.contains("Or") {
        hints.push("Goal is a disjunction - try: left, right".to_string());
    }
    if has_nat_context {
        hints.push("Goal involves natural numbers - try: omega, linarith, induction".to_string());
    }

    // Check hypotheses for tactics
    for hyp in hyps {
        let hyp_pp = pp_expr(&hyp.ty, env);
        if looks_like_equality_target(&hyp_pp) {
            hints.push(format!(
                "Hypothesis {} is an equality - try: rw [{}]",
                hyp.name, hyp.name
            ));
            break; // Only suggest first
        }
    }

    hints
}

/// Suggest tactic names for the focused goal in machine-friendly form.
fn suggest_tactics_for_state(state: &InternalProofState, env: &Environment) -> Vec<String> {
    suggest_tactics_for_state_and_profile(state, env, ObligationDomainProfile::General)
}

/// Suggest tactic names for the focused goal using a domain profile as the first signal.
fn suggest_tactics_for_state_and_profile(
    state: &InternalProofState,
    env: &Environment,
    domain_profile: ObligationDomainProfile,
) -> Vec<String> {
    suggest_tactics_for_goal_and_profile(state.goals().front(), env, domain_profile)
}

fn suggest_tactics_for_goal_and_profile(
    goal: Option<&Goal>,
    env: &Environment,
    domain_profile: ObligationDomainProfile,
) -> Vec<String> {
    let Some(goal) = goal else {
        return Vec::new();
    };

    let mut suggestions = Vec::new();
    let target_pp = pp_expr(&goal.target, env);
    let has_nat_context = target_pp.contains("Nat")
        || target_pp.contains("ℕ")
        || goal.local_ctx.iter().any(|hyp| {
            let hyp_pp = pp_expr(&hyp.ty, env);
            hyp_pp.contains("Nat") || hyp_pp.contains("ℕ")
        });

    let mut push_unique = |tactic: &str| {
        if !suggestions.iter().any(|existing| existing == tactic) {
            suggestions.push(tactic.to_string());
        }
    };

    for tactic in profile_tactic_prefix(domain_profile) {
        push_unique(tactic);
    }

    if looks_like_equality_target(&target_pp) {
        for tactic in ["rfl", "simp", "ring", "linarith"] {
            push_unique(tactic);
        }
    }
    if target_pp.contains(" → ") || target_pp.contains("->") {
        for tactic in ["intro", "intros"] {
            push_unique(tactic);
        }
    }
    if target_pp.contains("∀") || target_pp.contains("forall") {
        for tactic in ["intro", "intros"] {
            push_unique(tactic);
        }
    }
    if target_pp.contains("∃") || target_pp.contains("Exists") {
        for tactic in ["use", "exists"] {
            push_unique(tactic);
        }
    }
    if target_pp.contains("∧") || target_pp.contains("And") {
        for tactic in ["constructor", "and_iff_right"] {
            push_unique(tactic);
        }
    }
    if target_pp.contains("∨") || target_pp.contains("Or") {
        for tactic in ["left", "right"] {
            push_unique(tactic);
        }
    }
    if has_nat_context {
        for tactic in ["omega", "linarith", "induction"] {
            push_unique(tactic);
        }
    }

    for hyp in &goal.local_ctx {
        let hyp_pp = pp_expr(&hyp.ty, env);
        if looks_like_equality_target(&hyp_pp) {
            push_unique(&format!("rw [{}]", hyp.name));
            break;
        }
    }

    suggestions
}

fn profile_tactic_prefix(domain_profile: ObligationDomainProfile) -> &'static [&'static str] {
    match domain_profile {
        ObligationDomainProfile::SatPb => &["cert_simp", "cert_mathverse", "sat_pb"],
        ObligationDomainProfile::NnVerify => &["cert_simp", "nn_norm", "nn_verify"],
        ObligationDomainProfile::Smt => &["cert_simp", "ay_smt"],
        ObligationDomainProfile::Arithmetic => &["cert_simp", "omega", "linarith"],
        ObligationDomainProfile::General => &[],
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{FVarId, Level, Name};

    #[test]
    fn test_state_id_generation() {
        let id1 = StateId::new();
        let id2 = StateId::new();
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_state_id_display() {
        let id = StateId::new();
        let s = id.to_string();
        assert!(s.starts_with("ps_"));
        assert_eq!(s.len(), 3 + 32); // "ps_" + 32 hex chars
    }

    #[test]
    fn test_state_id_roundtrip() {
        let id = StateId::new();
        let s = id.to_string();
        let id2: StateId = s.parse().unwrap();
        assert_eq!(id, id2);
    }

    #[test]
    fn test_cache_insert_get() {
        let config = ProofStateCacheConfig::default();
        let cache = ProofStateCache::new(config);

        let env = Environment::new();
        let state = InternalProofState::new(env, Expr::sort(Level::zero()));

        let id = cache.insert(state, Some("test".to_string()), None, 0);
        let retrieved = cache.get(&id);

        let retrieved = retrieved.expect("inserted state should be retrievable from cache");
        assert_eq!(retrieved.problem_id, Some("test".to_string()));
        assert_eq!(retrieved.step_number, 0);
        assert!(retrieved.tactic_script_prefix.is_empty());
    }

    // Regression: a wire-controlled `ttl_sec` near `u64::MAX` (the only bound
    // enforced by `OpenObligationRequest::validate` is `ttl_sec != 0`) reaches
    // `insert_open_obligation`, which used to compute `now + ttl`. `Instant`'s
    // `Add<Duration>` panics on overflow ("overflow when adding duration to
    // instant"), so a single unauthenticated `proofState.openObligation`
    // request could abort the server. The fix saturates the expiry instead.
    #[test]
    fn test_insert_open_obligation_extreme_ttl_does_not_panic() {
        let config = ProofStateCacheConfig::default();
        let cache = ProofStateCache::new(config);

        let env = Environment::new();
        let state = InternalProofState::new(env, Expr::sort(Level::zero()));

        // Duration::from_secs(u64::MAX) is fine to construct; `now + ttl` is
        // what overflows. Before the fix this line panics.
        let id = cache.insert_open_obligation(
            state,
            Some("dos".to_string()),
            Duration::from_secs(u64::MAX),
            1,
            None,
            ObligationDomainProfile::General,
            None,
        );

        // The saturated expiry is ~100 years out, so the entry must still be
        // live and retrievable — no panic, no premature expiry.
        let retrieved = cache
            .get(&id)
            .expect("state inserted with extreme ttl should be retrievable");
        assert_eq!(retrieved.problem_id, Some("dos".to_string()));
    }

    #[test]
    fn test_saturating_expires_at_is_exact_for_realistic_ttl() {
        // Correct-path invariant: for any ttl that does not overflow the clock,
        // `saturating_expires_at` returns exactly `now + ttl`.
        let now = Instant::now();
        let ttl = Duration::from_secs(3600);
        assert_eq!(saturating_expires_at(now, ttl), now + ttl);
    }

    #[test]
    fn test_cache_get_includes_tactic_script_prefix() {
        let cache = ProofStateCache::default_config();
        let env = Environment::new();
        let target = Expr::sort(Level::zero());
        let initial = InternalProofState::new(env.clone(), target.clone());
        let child = InternalProofState::new(env.clone(), target.clone());
        let grandchild = InternalProofState::new(env, target);

        let root_id = cache.insert(initial, None, None, 0);
        let child_id =
            cache.insert_with_tactic(child, None, Some(root_id), 1, Some("intro h".to_string()));
        let grandchild_id = cache.insert_with_tactic(
            grandchild,
            None,
            Some(child_id),
            2,
            Some("exact h".to_string()),
        );

        let retrieved = cache
            .get(&grandchild_id)
            .expect("grandchild proof state should be cached");
        assert_eq!(
            retrieved.tactic_script_prefix,
            vec!["intro h".to_string(), "exact h".to_string()]
        );
    }

    #[test]
    fn test_cache_remove() {
        let config = ProofStateCacheConfig::default();
        let cache = ProofStateCache::new(config);

        let env = Environment::new();
        let state = InternalProofState::new(env, Expr::sort(Level::zero()));

        let id = cache.insert(state, None, None, 0);
        assert!(
            cache.get(&id).is_some(),
            "state should be in cache before remove"
        );

        cache.remove(&id);
        assert!(
            cache.get(&id).is_none(),
            "state should be absent after remove"
        );
    }

    /// Regression: `proofState.retain` with an adversarially large `ttl_sec`
    /// (e.g. `u64::MAX` from the JSON-RPC wire) must not panic. `retain` reads
    /// the wire `ttl_sec` with no upper bound, maps it via
    /// `Duration::from_secs`, and previously stored `now + ttl` — hitting
    /// `Instant`'s `Add` overflow `expect`, which under `panic = "abort"`
    /// aborts the whole server process. The state is opened with a normal TTL
    /// first so the liveness guard (`now >= expires_at`) is not tripped,
    /// exercising the overflow path directly rather than the early return.
    #[test]
    fn test_retain_saturates_absurd_ttl_without_panic() {
        let config = ProofStateCacheConfig::default();
        let cache = ProofStateCache::new(config);

        let env = Environment::new();
        let state = InternalProofState::new(env, Expr::sort(Level::zero()));

        // Step 1: open a live state with an ordinary TTL.
        let id = cache.insert_open_obligation(
            state,
            Some("overflow-probe".to_string()),
            Duration::from_secs(600),
            4,
            None,
            ObligationDomainProfile::General,
            None,
        );

        // Step 2: retain with the maximum possible TTL. Pre-fix this panics
        // (`Instant + Duration::from_secs(u64::MAX)`); post-fix it saturates.
        let ttl = Duration::from_secs(u64::MAX);
        let lifecycle = cache
            .retain(&id, Some(ttl))
            .expect("retaining a live state with a huge TTL should still succeed");

        // ttl_sec echoes the requested (absurd) TTL; the stored instant is
        // saturated far into the future rather than overflowing.
        assert_eq!(lifecycle.ttl_sec, u64::MAX);
        assert!(
            lifecycle.ttl_remaining_sec > 0,
            "saturated expiry should be in the far future"
        );

        // The state must remain retrievable (not popped) afterwards.
        assert!(
            cache.get(&id).is_some(),
            "state should still be live after a saturating retain"
        );
    }

    #[test]
    fn test_pp_expr_sort() {
        let env = Environment::new();
        assert_eq!(pp_expr(&Expr::sort(Level::zero()), &env), "Prop");
        assert_eq!(
            pp_expr(&Expr::sort(Level::succ(Level::zero())), &env),
            "Type"
        );
    }

    #[test]
    fn test_pp_expr_literal() {
        let env = Environment::new();
        assert_eq!(
            pp_expr(
                &Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
                    clean_kernel::BigNat::Small(42)
                ))),
                &env
            ),
            "42"
        );
    }

    #[test]
    fn test_convert_goals_adds_stable_summaries_and_symbols() {
        let env = Environment::new();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let target = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![]),
            [nat.clone(), zero.clone(), zero],
        );
        let mut state = InternalProofState::new(env.clone(), target);
        state
            .current_goal_mut()
            .expect("new proof state should have one goal")
            .local_ctx
            .push(LocalDecl {
                fvar: FVarId::new(0),
                name: "n".to_string(),
                ty: nat,
                value: None,
            });

        let goals = convert_goals(&state, &env);
        let goal = goals.first().expect("converted state should have one goal");

        assert_eq!(goal.summary.local_count, 1);
        assert_eq!(goal.summary.let_count, 0);
        assert_eq!(goal.target_head.as_deref(), Some("Eq"));
        assert_eq!(goal.summary.target_head.as_deref(), Some("Eq"));
        assert_eq!(goal.target_symbols, vec!["Eq", "Nat", "Nat.zero"]);
        assert_eq!(goal.local_context_summary.len(), 1);
        assert_eq!(goal.local_context_summary[0].name, "n");
        assert_eq!(
            goal.local_context_summary[0].type_symbols,
            vec!["Nat".to_string()]
        );
        assert!(goal
            .context_summary
            .as_deref()
            .is_some_and(|summary| summary.contains("locals=1:n")));
    }

    #[test]
    fn test_tactic_api_error_from_tactic_error() {
        let err = TacticError::NoGoals;
        let api_err: TacticApiError = err.into();
        assert_eq!(api_err.code, TacticErrorCode::NoGoals);
        assert_eq!(api_err.message, "no goals");
    }

    #[test]
    fn test_tactic_api_error_type_mismatch() {
        let err = TacticError::TypeMismatch {
            expected: "Nat".to_string(),
            actual: "Bool".to_string(),
        };
        let api_err: TacticApiError = err.into();
        assert_eq!(api_err.code, TacticErrorCode::TypeMismatch);
        let details = api_err
            .details
            .expect("TypeMismatch should include details");
        assert_eq!(details.expected_type, Some("Nat".to_string()));
        assert_eq!(details.actual_type, Some("Bool".to_string()));
    }

    #[test]
    fn test_pp_expr_pi_non_dependent() {
        let env = Environment::new();
        let nat = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
        // Nat → Nat (body does not reference binder)
        let arrow = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
        assert_eq!(pp_expr(&arrow, &env), "Nat → Nat");
    }

    #[test]
    fn test_pp_expr_pi_dependent() {
        let env = Environment::new();
        let nat = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
        let p = Expr::const_(clean_kernel::Name::from_string("P"), vec![]);
        // ∀ (_ : Nat), P #0  (body references binder via BVar(0))
        let dep_pi = Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(p, Expr::bvar(0)),
        );
        assert_eq!(pp_expr(&dep_pi, &env), "∀ _ : Nat, P #0");
    }

    #[test]
    fn test_pp_expr_let_preserves_name() {
        let env = Environment::new();
        let nat = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
        let one = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
            clean_kernel::BigNat::Small(1),
        )));
        let let_expr = Expr::let_named(
            clean_kernel::Name::from_string("x"),
            nat,
            one,
            Expr::bvar(0),
            false,
        );
        assert_eq!(pp_expr(&let_expr, &env), "let x : Nat := 1 in #0");
    }

    #[test]
    fn test_open_obligation_rejects_impossible_schema_range() {
        let request = OpenObligationRequest {
            schema_version: OPEN_OBLIGATION_SCHEMA_VERSION.to_string(),
            environment_id: "env_blake3_test".to_string(),
            domain_profile: ObligationDomainProfile::SatPb,
            goal: ObligationGoalPayload {
                expr: Some(Expr::const_(
                    clean_kernel::Name::from_string("Cert.PB.Accepted"),
                    vec![],
                )),
                pretty: "Cert.PB.Accepted formula proof".to_string(),
                type_expr: None,
                type_pp: Some("Prop".to_string()),
            },
            local_context: vec![],
            artifact_refs: vec![],
            metadata: None,
            trust_policy: ObligationTrustPolicy::ConstructiveOnly,
            ttl_sec: 600,
            max_states: 4096,
            min_schema_version: "clean-proof-state-v3".to_string(),
            max_schema_version: "clean-proof-state-v2".to_string(),
        };

        let err = request
            .validate()
            .expect_err("min schema greater than max schema should fail");
        assert!(matches!(
            err,
            OpenObligationValidationError::ImpossibleSchemaRange { .. }
        ));
    }

    #[test]
    fn test_open_obligation_accepts_ay_sat_pb_request() {
        let request = OpenObligationRequest {
            schema_version: OPEN_OBLIGATION_SCHEMA_VERSION.to_string(),
            environment_id: "env_blake3_ay_sat_pb".to_string(),
            domain_profile: ObligationDomainProfile::SatPb,
            goal: ObligationGoalPayload {
                expr: Some(Expr::const_(
                    clean_kernel::Name::from_string("Cert.PB.Accepted"),
                    vec![],
                )),
                pretty: "Cert.PB.Accepted formula proof".to_string(),
                type_expr: None,
                type_pp: Some("Prop".to_string()),
            },
            local_context: vec![ObligationLocalHypothesis {
                name: "h_checked".to_string(),
                type_expr: None,
                type_pp: "Cert.PB.check proof = true".to_string(),
                value_expr: None,
                value_pp: None,
            }],
            artifact_refs: vec![
                ObligationArtifactRef {
                    kind: ObligationArtifactKind::Opb,
                    sha256: Some("0".repeat(64)),
                    path: None,
                    media_type: Some("application/opb".to_string()),
                },
                ObligationArtifactRef {
                    kind: ObligationArtifactKind::VeriPb,
                    sha256: Some("1".repeat(64)),
                    path: None,
                    media_type: Some("text/x-veripb".to_string()),
                },
            ],
            metadata: None,
            trust_policy: ObligationTrustPolicy::ConstructiveOnly,
            ttl_sec: 600,
            max_states: 4096,
            min_schema_version: PROOF_STATE_SCHEMA_VERSION.to_string(),
            max_schema_version: PROOF_STATE_SCHEMA_VERSION.to_string(),
        };

        let validation = request
            .validate()
            .expect("ay SAT/PB obligation should validate");
        assert_eq!(validation.selected_schema, PROOF_STATE_SCHEMA_VERSION);

        let json = serde_json::to_value(&request).expect("request should serialize");
        assert_eq!(json["domain_profile"], "sat-pb");
        assert_eq!(json["trust_policy"], "constructive-only");
        assert_eq!(json["artifact_refs"][0]["kind"], "opb");
        assert_eq!(json["artifact_refs"][1]["kind"], "veripb");

        let decoded: OpenObligationRequest =
            serde_json::from_value(json).expect("request should deserialize");
        assert_eq!(decoded.domain_profile, ObligationDomainProfile::SatPb);
        assert_eq!(decoded.artifact_refs.len(), 2);
    }

    #[test]
    fn test_obligation_domain_profile_preserves_nn_verify_wire_value() {
        let json =
            serde_json::to_value(ObligationDomainProfile::NnVerify).expect("serialize profile");
        assert_eq!(json, serde_json::json!("nn-verify"));

        let decoded: ObligationDomainProfile =
            serde_json::from_value(json).expect("deserialize profile");
        assert_eq!(decoded, ObligationDomainProfile::NnVerify);
    }
}
