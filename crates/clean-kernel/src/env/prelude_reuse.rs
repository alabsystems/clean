// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Process-local reuse of the ordinary prelude, never of a proof verdict.

use std::cell::Cell;
use std::sync::{Mutex, OnceLock};

use super::{EnvError, Environment};

thread_local! {
    // A future initializer calling the shared boundary must fail instead of
    // waiting on the mutex held by the parent of this construction worker.
    static BUILDING_PRELUDE: Cell<bool> = const { Cell::new(false) };
}

fn unavailable(detail: impl Into<String>) -> EnvError {
    EnvError::PreludeInitialization {
        detail: detail.into(),
    }
}

struct ConstructionGuard;

impl ConstructionGuard {
    fn enter() -> Self {
        BUILDING_PRELUDE.with(|building| building.set(true));
        Self
    }
}

impl Drop for ConstructionGuard {
    fn drop(&mut self) {
        BUILDING_PRELUDE.with(|building| building.set(false));
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConstructionPolicy {
    Shared,
    Fresh,
}

impl ConstructionPolicy {
    fn from_controls(
        strict_quality: bool,
        deny_sorry: bool,
        declaration_budget: u64,
        mm_axiom_only: bool,
        mm_two_pass: bool,
    ) -> Result<Self, EnvError> {
        if mm_axiom_only || mm_two_pass {
            return Err(unavailable(
                "reusable ordinary prelude refuses Metamath two-pass construction context",
            ));
        }
        if strict_quality || deny_sorry || declaration_budget != 0 {
            return Ok(Self::Fresh);
        }
        Ok(Self::Shared)
    }

    fn for_worker_support(self, worker_supported: bool) -> Self {
        if worker_supported {
            self
        } else {
            Self::Fresh
        }
    }

    fn current() -> Result<Self, EnvError> {
        let policy = Self::from_controls(
            super::proof_quality::strict_mode_enabled(),
            // Respect both the request spelling and the kernel's process-wide
            // already-latched guard. Even DENY_SORRY=0 declines reuse: an
            // explicit construction diagnostic must not disappear on a hit.
            std::env::var_os("DENY_SORRY").is_some() || crate::sorry::deny_sorry_already_enabled(),
            crate::tc::declaration_budget_limit(),
            super::mm_axiom_only(),
            super::mm_two_pass_active(),
        )?;
        // Admission precedes platform selection: a no-thread target does not
        // rescue an MM refusal. Conservatively keep every WASM target fresh,
        // including threaded variants until their worker path is qualified.
        Ok(policy.for_worker_support(!cfg!(target_family = "wasm")))
    }
}

/// Is the ORDINARY prelude shareable in this process right now?
///
/// The single source of truth for that question is `ReusePolicy::current`, and
/// it has two consumers: this module's reusable-reference cache, and the
/// per-thread template `Environment::try_with_prelude` clones from. They must
/// agree — a second copy of these conditions would drift, and the failure would
/// be a stale prelude served after a control latched, which is exactly the
/// thing the policy exists to prevent. An MM construction context (`Err`) is
/// not shareable either.
pub(in crate::env) fn ordinary_prelude_is_shareable() -> bool {
    matches!(
        ConstructionPolicy::current(),
        Ok(ConstructionPolicy::Shared)
    )
}

struct PreludeCell {
    value: OnceLock<Environment>,
    initializing: Mutex<()>,
}

impl PreludeCell {
    const fn new() -> Self {
        Self {
            value: OnceLock::new(),
            initializing: Mutex::new(()),
        }
    }

    fn with<R>(
        &self,
        policy: ConstructionPolicy,
        build: impl FnOnce() -> Result<Environment, EnvError> + Send + 'static,
        use_environment: impl FnOnce(&Environment) -> R,
    ) -> Result<R, EnvError> {
        if BUILDING_PRELUDE.with(Cell::get) {
            return Err(unavailable("recursive ordinary-prelude initialization"));
        }
        if policy == ConstructionPolicy::Fresh {
            // In particular do not move a caller's declaration budget to a
            // fresh thread, suspend it, reset it, or serve a warmed value.
            let environment = {
                let _constructing = ConstructionGuard::enter();
                build()?
            };
            return Ok(use_environment(&environment));
        }
        let environment = self.get_or_try_init(build)?;
        // The initialization mutex is gone before arbitrary caller code runs.
        // A callback may make another ordinary request without deadlocking.
        Ok(use_environment(environment))
    }

    fn get_or_try_init(
        &self,
        build: impl FnOnce() -> Result<Environment, EnvError> + Send + 'static,
    ) -> Result<&Environment, EnvError> {
        if let Some(environment) = self.value.get() {
            return Ok(environment);
        }
        let _initializing = self
            .initializing
            .lock()
            .map_err(|_| unavailable("ordinary-prelude initialization lock poisoned"))?;
        if let Some(environment) = self.value.get() {
            return Ok(environment);
        }
        let environment = build_on_worker(build)?;
        // Errors and worker panics leave the cell empty, not permanently red
        // and never initialized with a partial environment.
        Ok(self.value.get_or_init(|| environment))
    }
}

fn build_on_worker(
    build: impl FnOnce() -> Result<Environment, EnvError> + Send + 'static,
) -> Result<Environment, EnvError> {
    // Same construction stack as Clean's existing EvalIR vocabulary worker.
    // This selects no checker heartbeat, cache capacity, or proof authority.
    const PRELUDE_STACK_BYTES: usize = 64 * 1024 * 1024;
    std::thread::Builder::new()
        .name("clean-ordinary-prelude".into())
        .stack_size(PRELUDE_STACK_BYTES)
        .spawn(move || {
            // A new thread cannot inherit an importer's axiom-only flag or
            // ambient declaration budget. Public admission checked those on
            // the caller first; override requests take the fresh path instead.
            let _constructing = ConstructionGuard::enter();
            build()
        })
        .map_err(|error| unavailable(format!("cannot spawn ordinary-prelude worker: {error}")))?
        .join()
        .map_err(|_| unavailable("ordinary-prelude construction worker panicked"))?
}

static ORDINARY_PRELUDE: PreludeCell = PreludeCell::new();

impl Environment {
    /// Borrow the ordinary prelude for one operation, reusing its successful
    /// process-local construction when the caller's policy permits it.
    ///
    /// The sole builder is the unchanged [`Self::try_with_prelude`], with its
    /// exact declarations, options and registration checks. No EvalIR vocabulary,
    /// external source, serialized environment, or caller-supplied declaration
    /// is added. Raw prelude constructors remain fresh and uncached.
    ///
    /// The normal native path constructs at most one immutable environment, on
    /// a named worker with fresh thread-local state, retained until process exit.
    /// Concurrent first requests share initialization; construction errors and
    /// worker panics are not cached. The callback runs on the calling thread,
    /// outside the initialization lock. It receives no mutable access. A caller
    /// needing declarations may clone the environment into its own session;
    /// this copies owned maps and shares immutable expression DAGs, not verdicts.
    ///
    /// Every request checks live construction policy, including warm hits.
    /// `CLEAN_STRICT_PROOF_QUALITY=1`, a requested or latched `DENY_SORRY`, or an
    /// active declaration budget takes the original fresh caller-thread path.
    /// In particular the ambient budget is neither bypassed nor refilled.
    /// Metamath two-pass contexts are refused, never retained. Process-global
    /// configuration must stay stable during a request, as for raw construction.
    ///
    /// WASM targets conservatively use fresh caller-thread construction after
    /// the same policy checks, installing no cached environment. This preserves
    /// the raw-constructor path on single-threaded targets; threaded WASM also
    /// remains fresh until a worker-reuse path is separately qualified. Native
    /// worker errors still fail closed instead of silently selecting a fallback.
    ///
    /// A global per-checker cache cap is still read by each newly constructed
    /// checker. Trace/counter hooks describe work actually performed; a cache hit
    /// performs no prelude construction. `CLEAN_SPEC_DECL_BUDGET` belongs to
    /// specification elaboration and is not read by the raw kernel constructor.
    ///
    /// This supplies no new proof authority. Create a fresh `TypeChecker` and
    /// local context for every independent check, retaining its existing limits
    /// and admission/audit policy. The callback must still check the actual term.
    ///
    /// # Errors
    /// Returns the raw construction error, a worker/initialization failure, or
    /// an explicit refusal of Metamath/reentrant construction context.
    pub fn with_reusable_prelude<R>(
        use_environment: impl FnOnce(&Environment) -> R,
    ) -> Result<R, EnvError> {
        ORDINARY_PRELUDE.with(
            ConstructionPolicy::current()?,
            Self::try_with_prelude,
            use_environment,
        )
    }
}

#[cfg(test)]
#[path = "prelude_reuse_tests.rs"]
mod tests;
