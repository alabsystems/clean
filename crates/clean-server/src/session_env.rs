// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-session environment isolation for swarm workers.
//!
//! A swarm of proof workers shares a single corpus [`Environment`]. Without
//! isolation, a worker that adds an in-progress (or ultimately rejected)
//! declaration mutates the shared environment, so a later worker — or a
//! retry of the same worker — can see a constant that was never accepted.
//! That pollutes premise selection and, worse, lets a rejected proof's
//! by-products leak into the corpus that downstream proofs check against.
//!
//! [`SessionEnv`] gives each worker a private overlay on top of a shared,
//! immutable base snapshot:
//!
//! - **base** ([`Arc<Environment>`]): the shared corpus snapshot. It is
//!   reference-counted and never mutated through a session — a worker only
//!   ever holds a read view of it, so concurrent sessions can share it
//!   cheaply and safely.
//! - **overlay** ([`Environment`]): the session's private working copy. A
//!   session-scoped `add_decl` type-checks against `base ∪ overlay` (the
//!   kernel runs against the overlay, which is materialized from the base)
//!   and writes only into the overlay.
//!
//! Lifecycle:
//!
//! - **lookup** consults the overlay, which contains the base plus any
//!   session-local declarations.
//! - **rollback** is dropping the [`SessionEnv`]: the `Arc<Environment>`
//!   base is untouched, so the shared corpus stays pristine.
//! - **drain** returns the names the session added on top of the base, for
//!   callers that want to graduate an accepted session's work into the
//!   shared corpus deliberately (a separate, audited step — never automatic).
//!
//! # Trust note
//!
//! This module reuses the kernel's [`Environment::add_decl`], which runs the
//! full kernel type checker. It does not touch kernel trust logic and adds no
//! new trusted path: a session decl that the kernel rejects is simply not
//! registered into the overlay, exactly as if it had been checked against the
//! shared environment — only without the shared-state pollution.

use clean_kernel::{ConstantInfo, Declaration, EnvError, Environment, Name};
use std::collections::HashSet;
use std::str::FromStr;
use std::sync::Arc;
use uuid::Uuid;

/// Unique identifier for a swarm worker session (UUID v7, time-ordered).
///
/// Mirrors the `StateId` / `AttemptId` pattern in
/// [`crate::proof_state`]: a thin newtype over [`Uuid`] with a stable,
/// prefixed wire spelling (`sess_…`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SessionId(Uuid);

impl SessionId {
    /// Generate a new session ID.
    #[must_use]
    pub fn new() -> Self {
        Self(Uuid::now_v7())
    }

    /// Get the underlying UUID.
    #[must_use]
    pub fn uuid(&self) -> Uuid {
        self.0
    }
}

impl Default for SessionId {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for SessionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "sess_{}", self.0.simple())
    }
}

impl FromStr for SessionId {
    type Err = uuid::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.strip_prefix("sess_").unwrap_or(s);
        Ok(Self(Uuid::parse_str(s)?))
    }
}

/// Errors raised while operating on a per-session environment.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SessionEnvError {
    /// A session-scoped declaration failed the kernel type check (against
    /// `base ∪ overlay`) and was not registered into the overlay.
    #[error("session declaration rejected by kernel: {0}")]
    Rejected(#[from] EnvError),
}

/// A swarm worker's isolated view of the corpus environment.
///
/// Holds a shared, immutable `base` snapshot and a private `overlay`. The
/// overlay is materialized from the base, so all base declarations remain
/// visible while session-local additions stay confined to the overlay.
///
/// Dropping a `SessionEnv` is the rollback: the shared `base` is never
/// mutated, so a worker's in-progress or rejected work cannot pollute the
/// corpus.
pub struct SessionEnv {
    /// Shared corpus snapshot. Reference-counted and never mutated here.
    base: Arc<Environment>,
    /// Private working overlay (materialized from `base`).
    overlay: Environment,
}

/// A point-in-time snapshot of a [`SessionEnv`] overlay.
///
/// Produced by [`SessionEnv::checkpoint`] and consumed by
/// [`SessionEnv::restore`] to undo speculative additions while preserving the
/// session's earlier accepted work. Opaque on purpose — callers treat it as a
/// rollback token, not a readable environment.
#[must_use]
pub struct OverlayCheckpoint {
    overlay: Environment,
}

impl SessionEnv {
    /// Create a session environment over a shared base snapshot.
    ///
    /// The overlay is initialized as a private copy of the base so that
    /// kernel type checks for session decls see every base constant. The
    /// base `Arc` is retained so [`Self::drain`] can diff against the
    /// pristine snapshot and so rollback (drop) leaves the shared base
    /// untouched.
    #[must_use]
    pub fn new(base: Arc<Environment>) -> Self {
        let overlay = (*base).clone();
        Self { base, overlay }
    }

    /// Read-only access to the effective environment (`base ∪ overlay`).
    ///
    /// This is the environment that lookups, premise selection, and kernel
    /// checks should run against for this session.
    #[must_use]
    pub fn env(&self) -> &Environment {
        &self.overlay
    }

    /// The shared base snapshot this session was derived from.
    #[must_use]
    pub fn base(&self) -> &Arc<Environment> {
        &self.base
    }

    /// Look up a constant in the effective environment (overlay first, then
    /// base — both are folded into the overlay copy).
    #[must_use]
    pub fn get_const(&self, name: &Name) -> Option<&ConstantInfo> {
        self.overlay.get_const(name)
    }

    /// Whether the effective environment defines `name`.
    #[must_use]
    pub fn contains(&self, name: &Name) -> bool {
        self.overlay.get_const(name).is_some()
    }

    /// Whether `name` is part of the shared base snapshot (i.e. it was not
    /// introduced by this session).
    #[must_use]
    pub fn base_contains(&self, name: &Name) -> bool {
        self.base.get_const(name).is_some()
    }

    /// Type-check `decl` against `base ∪ overlay` and, on success, register
    /// it into the session overlay only.
    ///
    /// The shared base is never written to: a rejected declaration leaves
    /// the overlay (and therefore the base) unchanged, and an accepted one
    /// is visible only inside this session until explicitly drained and
    /// graduated by a caller.
    ///
    /// # Errors
    /// Returns [`SessionEnvError::Rejected`] if the kernel rejects the
    /// declaration (duplicate name, type-check failure, free variables, ...).
    pub fn add_decl(&mut self, decl: Declaration) -> Result<(), SessionEnvError> {
        self.overlay.add_decl(decl)?;
        Ok(())
    }

    /// Type-check and register `decl` into the overlay under a per-call kernel
    /// heartbeat (fuel) budget.
    ///
    /// `heartbeat_limit` reuses the kernel's existing deterministic
    /// `maxHeartbeats` mechanism: `Environment::add_decl` reads the
    /// `maxHeartbeats` option and stamps it onto the per-check `TypeChecker`,
    /// so a pathological proof term that would otherwise spin the kernel is
    /// stopped at a bounded number of major operations (whnf / def_eq / …)
    /// instead of wedging the worker. A limit of `0` means "kernel default"
    /// (unbounded heartbeat) and is treated as no budget.
    ///
    /// The option is scoped to this single call: it is set on the overlay
    /// before the check and removed afterwards, whether or not the check
    /// succeeded, so it never leaks into a sibling call's budget. Setting the
    /// option does not touch kernel trust logic — it only bounds work, and a
    /// budget exhaustion is reported by the kernel as a (deterministic)
    /// type-check failure, i.e. fail-closed.
    ///
    /// # Errors
    /// Returns [`SessionEnvError::Rejected`] if the kernel rejects the
    /// declaration, including the deterministic heartbeat-limit-exceeded error.
    pub fn add_decl_with_heartbeat(
        &mut self,
        decl: Declaration,
        heartbeat_limit: u32,
    ) -> Result<(), SessionEnvError> {
        if heartbeat_limit == 0 {
            return self.add_decl(decl);
        }
        self.overlay.set_option(
            "maxHeartbeats".to_string(),
            Some(heartbeat_limit.to_string()),
        );
        let result = self.overlay.add_decl(decl);
        // Always restore the option, success or failure, so the next call's
        // budget is independent of this one.
        self.overlay.remove_option("maxHeartbeats");
        result?;
        Ok(())
    }

    /// Classify the transitive proof quality of a session-local constant.
    ///
    /// Thin read-only passthrough to [`Environment::proof_quality`] on the
    /// effective environment so callers can classify a just-added theorem
    /// without raw access to the overlay.
    #[must_use]
    pub fn proof_quality(&self, name: &Name) -> Option<clean_kernel::ProofQuality> {
        self.overlay.proof_quality(name)
    }

    /// The transitive non-foundational axiom closure of a session-local
    /// constant, as an owned `Vec` (unspecified order).
    ///
    /// Thin read-only passthrough to [`Environment::axiom_deps`] on the
    /// effective environment. Returns `None` only if the constant is absent.
    /// Collected into a `Vec` so callers do not depend on the kernel's
    /// concrete set type.
    #[must_use]
    pub fn axiom_deps(&self, name: &Name) -> Option<Vec<Name>> {
        self.overlay
            .axiom_deps(name)
            .map(|deps| deps.into_iter().collect())
    }

    /// Names this session added on top of the base snapshot.
    ///
    /// Computed as the set difference between the overlay's constants and the
    /// base's constants. Used to graduate an accepted session's work into the
    /// shared corpus as a deliberate, audited step.
    #[must_use]
    pub fn drain_names(&self) -> Vec<Name> {
        let base_names: HashSet<&Name> = self.base.constants().map(|info| &info.name).collect();
        self.overlay
            .constants()
            .map(|info| &info.name)
            .filter(|name| !base_names.contains(*name))
            .cloned()
            .collect()
    }

    /// The [`ConstantInfo`] for each declaration this session added on top of
    /// the base snapshot, in unspecified order.
    #[must_use]
    pub fn drain(&self) -> Vec<&ConstantInfo> {
        let base_names: HashSet<&Name> = self.base.constants().map(|info| &info.name).collect();
        self.overlay
            .constants()
            .filter(|info| !base_names.contains(&info.name))
            .collect()
    }

    /// Number of declarations this session added on top of the base snapshot.
    #[must_use]
    pub fn session_decl_count(&self) -> usize {
        self.overlay
            .num_constants()
            .saturating_sub(self.base.num_constants())
    }

    /// Take a checkpoint of the current overlay.
    ///
    /// The returned [`OverlayCheckpoint`] captures every session-local decl
    /// accepted so far. Pass it to [`Self::restore`] to undo any decls added
    /// after the checkpoint — used to roll back exactly one speculative
    /// `add_decl` (a kernel-valid decl rejected by a downstream policy) without
    /// discarding the session's earlier accepted work. The shared base is never
    /// touched.
    pub fn checkpoint(&self) -> OverlayCheckpoint {
        OverlayCheckpoint {
            overlay: self.overlay.clone(),
        }
    }

    /// Restore the overlay to a previously-taken [`OverlayCheckpoint`],
    /// discarding any decls added since.
    pub fn restore(&mut self, checkpoint: OverlayCheckpoint) {
        self.overlay = checkpoint.overlay;
    }

    /// Discard every session-local addition, restoring the overlay to the
    /// pristine base snapshot.
    ///
    /// Equivalent to dropping and re-creating the session, but in place so the
    /// caller keeps the same [`SessionId`] entry. The shared base is never
    /// touched.
    pub fn rollback_to_base(&mut self) {
        self.overlay = (*self.base).clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Expr, Name};

    /// A `Prop`-valued axiom over `Prop` always type-checks, giving us a base
    /// constant other declarations can depend on without prelude bootstrap.
    fn prop_axiom(name: &str) -> Declaration {
        Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        }
    }

    /// Build a base environment containing a single `Prop` axiom named `base`.
    fn base_with_const() -> Arc<Environment> {
        let mut env = Environment::new();
        env.add_decl(prop_axiom("base"))
            .expect("axiom over Prop type-checks");
        Arc::new(env)
    }

    #[test]
    fn test_session_id_roundtrip_parses_prefixed_form() {
        let id = SessionId::new();
        let text = id.to_string();
        assert!(text.starts_with("sess_"), "wire form is prefixed: {text}");
        let parsed = SessionId::from_str(&text).expect("prefixed form parses");
        assert_eq!(id, parsed);
    }

    #[test]
    fn test_session_sees_base_constants() {
        let base = base_with_const();
        let session = SessionEnv::new(base);
        assert!(
            session.contains(&Name::from_string("base")),
            "session must see base constants"
        );
        assert!(session.base_contains(&Name::from_string("base")));
    }

    #[test]
    fn test_session_decl_depending_on_base_checks_in_session() {
        let base = base_with_const();
        let mut session = SessionEnv::new(base);

        // `dependent : base` — a theorem whose *type* is the base constant.
        // It type-checks only if the base constant is visible in the session.
        let base_const = Expr::const_(Name::from_string("base"), vec![]);
        let decl = Declaration::Axiom {
            name: Name::from_string("dependent"),
            level_params: vec![],
            type_: base_const,
        };

        session
            .add_decl(decl)
            .expect("decl depending on a base constant checks in the session");
        assert!(session.contains(&Name::from_string("dependent")));
    }

    #[test]
    fn test_dropped_session_leaves_base_pristine() {
        let base = base_with_const();
        let base_count_before = base.num_constants();

        {
            let mut session = SessionEnv::new(Arc::clone(&base));
            session
                .add_decl(prop_axiom("worker_local"))
                .expect("worker-local axiom type-checks");
            assert!(session.contains(&Name::from_string("worker_local")));
            // Session goes out of scope here — this is the rollback.
        }

        // The shared base must NOT have grown: the worker's decl was confined
        // to the (now-dropped) overlay.
        assert_eq!(
            base.num_constants(),
            base_count_before,
            "dropped session must leave base pristine"
        );
        assert!(
            base.get_const(&Name::from_string("worker_local")).is_none(),
            "worker-local decl must not leak into the shared base"
        );
    }

    #[test]
    fn test_rejected_decl_does_not_pollute_session_or_base() {
        let base = base_with_const();
        let base_count_before = base.num_constants();
        let mut session = SessionEnv::new(Arc::clone(&base));

        // Duplicate of an existing base name: the kernel rejects it.
        let dup = prop_axiom("base");
        let err = session
            .add_decl(dup)
            .expect_err("duplicate name is rejected");
        assert!(matches!(err, SessionEnvError::Rejected(_)));

        // Neither the session nor the base gained anything.
        assert_eq!(session.session_decl_count(), 0);
        assert_eq!(base.num_constants(), base_count_before);
    }

    #[test]
    fn test_drain_reports_only_session_local_names() {
        let base = base_with_const();
        let mut session = SessionEnv::new(base);
        session
            .add_decl(prop_axiom("added_a"))
            .expect("axiom type-checks");
        session
            .add_decl(prop_axiom("added_b"))
            .expect("axiom type-checks");

        let mut drained = session.drain_names();
        drained.sort();
        assert_eq!(
            drained,
            vec![Name::from_string("added_a"), Name::from_string("added_b")],
            "drain reports only session-local additions, not base constants"
        );
        assert_eq!(session.session_decl_count(), 2);
    }

    #[test]
    fn test_concurrent_sessions_do_not_see_each_others_decls() {
        let base = base_with_const();
        let mut session_a = SessionEnv::new(Arc::clone(&base));
        let mut session_b = SessionEnv::new(Arc::clone(&base));

        session_a
            .add_decl(prop_axiom("only_in_a"))
            .expect("axiom type-checks");

        assert!(session_a.contains(&Name::from_string("only_in_a")));
        assert!(
            !session_b.contains(&Name::from_string("only_in_a")),
            "a worker's overlay must be invisible to a sibling session"
        );
        // And `session_b` can independently add the *same* name without a clash.
        session_b
            .add_decl(prop_axiom("only_in_a"))
            .expect("sibling session has its own namespace");
    }
}
