// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hard per-goal wall-clock timeout for the swarm worker.
//!
//! # Why the prover's own timeout is not enough
//!
//! [`clean_auto::AutomationEngine::auto_prove_with_premises`] takes a
//! `Duration`, but the superposition saturation loop only checks that deadline
//! BETWEEN iterations. A single hard goal — a large clause set, a false goal
//! that never closes — can grind deep inside one iteration and run far past the
//! wall. Over a 50k-constant corpus run that turns one pathological goal into a
//! hang of the whole batch.
//!
//! # The mechanism
//!
//! [`run_with_hard_timeout`] runs the prover closure on a dedicated worker
//! thread and the caller blocks on [`std::sync::mpsc::Receiver::recv_timeout`].
//! Whichever happens first wins:
//!
//! * the prover finishes ⇒ its `Option<ProofResult>` arrives on the channel and
//!   is returned;
//! * the wall-clock `timeout` elapses first ⇒ [`run_with_hard_timeout`] returns
//!   `None` (the goal is a MISS) and the loop moves on. The still-running prover
//!   thread is DETACHED — never joined — so the caller is guaranteed to make
//!   progress regardless of how stuck that one goal is. The abandoned thread
//!   runs to its own (between-iteration) deadline and then exits on its own; a
//!   bounded, transient leak that is far better than a hang for a batch run.
//!
//! All proof inputs are shared into the thread as `'static + Send` handles
//! (`Arc<Environment>`, `Arc<PremiseDatabase>`, owned hypotheses + local
//! context), so spawning costs an `Arc` refcount bump, not a deep clone of the
//! (large) corpus environment.
//!
//! # Soundness is untouched
//!
//! This module only decides WHEN to stop searching for a proof; it never
//! decides whether a goal is proved. A returned `ProofResult` still flows
//! through `closeover_premise_fvars` and the C1 kernel-recheck gate exactly as
//! before. A timeout can only ever turn a would-be proof into a MISS — it can
//! never manufacture one.

use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use clean_auto::prelude::{AutomationEngine, PremiseDatabase, ProofResult, QuantifierOrigin};
use clean_kernel::{Environment, Expr, LocalContext};

/// The owned, `'static + Send` bundle of everything one premise-guided proof
/// attempt needs, ready to move onto a worker thread.
///
/// Shared, immutable corpus data (`env`, `premise_db`) is carried behind `Arc`
/// so a spawn is a refcount bump rather than a clone of the whole environment;
/// the per-goal pieces (`goal`, `hypotheses`, `local_ctx`) are owned outright.
pub(crate) struct ProofJob {
    /// The search environment, shared immutably across goals.
    pub(crate) env: Arc<Environment>,
    /// The goal proposition to discharge (the opened body, for tier-2).
    pub(crate) goal: Expr,
    /// The MePo-selected premise hypotheses, already chosen on the main thread.
    pub(crate) hypotheses: Vec<(Expr, Option<QuantifierOrigin>)>,
    /// The premise database for E-matching relevance, shared across goals.
    pub(crate) premise_db: Arc<PremiseDatabase>,
    /// Tier-2's peeled-binder local context, if any.
    pub(crate) local_ctx: Option<LocalContext>,
}

/// Run `job` on a fresh engine under a HARD wall-clock `timeout`, guaranteeing
/// the caller regains control after at most `timeout` regardless of how stuck
/// the prover gets on this one goal.
///
/// Returns `Some(result)` if the prover finishes within the wall, `None` on
/// timeout (a MISS) — and `None`, too, if the worker thread vanished without
/// sending (e.g. a panic in the prover, or the thread could not be spawned): a
/// fail-closed miss, never a hang.
///
/// The engine is built fresh on the worker thread with [`AutomationEngine::new`]
/// — the exact construction [`crate::swarm_worker::SwarmWorker::new`] uses — so
/// the timeout path is behaviourally identical to the direct call it replaces,
/// and no engine reference outlives the detached thread.
pub(crate) fn run_with_hard_timeout(job: ProofJob, timeout: Duration) -> Option<ProofResult> {
    // Build the engine fresh on the worker thread — the exact construction
    // `SwarmWorker::new` uses — and run the prover with the SAME `timeout` as a
    // soft, graceful self-stop. The hard backstop is the `recv_timeout` below.
    spawn_with_hard_timeout(
        move || {
            let engine = AutomationEngine::new();
            engine.auto_prove_with_premises(
                job.env.as_ref(),
                &job.goal,
                job.hypotheses,
                job.premise_db.as_ref(),
                timeout,
                job.local_ctx.as_ref(),
            )
        },
        timeout,
    )
    .flatten()
}

/// Run `work` on a dedicated worker thread under a HARD wall-clock `timeout`.
///
/// Returns `Some(value)` if `work` finished within the wall, `None` on timeout
/// — or if the thread could not be spawned or vanished without sending (e.g. a
/// panic in `work`). The worker thread is NEVER joined: on timeout it is
/// detached and the caller regains control immediately, so the surrounding loop
/// is guaranteed to make progress no matter how stuck a single `work` call is.
/// This is the lone reason the swarm batch cannot hang on one hard goal.
///
/// `'static + Send` on the value and closure is what lets the thread outlive
/// this call: nothing it touches may borrow from the caller's frame.
fn spawn_with_hard_timeout<T, F>(work: F, timeout: Duration) -> Option<T>
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    let (tx, rx) = mpsc::channel::<T>();

    // The worker runs detached: we never join the handle. On timeout the caller
    // returns and this thread keeps running to its own internal deadline, then
    // exits. `send` on a dropped receiver is a benign error we ignore — by then
    // the caller has already recorded the miss and moved on.
    thread::Builder::new()
        .name("swarm-prove".to_string())
        .spawn(move || {
            let value = work();
            let _ = tx.send(value);
        })
        .ok()?;

    // `Ok` ⇒ `work` finished inside the wall. `Err` ⇒ the wall elapsed first
    // (`RecvTimeoutError::Timeout`) or the worker thread vanished without
    // sending (`Disconnected`, e.g. a panic in `work`). Both error cases map to
    // `None`: the caller moves on and the still-running thread (if any) is left
    // detached.
    rx.recv_timeout(timeout).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, Ordering};

    /// The mechanism's core guarantee: a `work` closure that runs LONGER than
    /// the wall is abandoned, and the caller regains control at the wall with a
    /// `None`. This is the property that stops one hard goal from hanging the
    /// batch — exercised directly, without depending on prover internals.
    #[test]
    fn test_spawn_with_hard_timeout_abandons_overrunning_work() {
        let start = std::time::Instant::now();
        // The closure sleeps far past the wall; the hard timeout must fire first.
        let out: Option<u32> = spawn_with_hard_timeout(
            || {
                thread::sleep(Duration::from_secs(30));
                42
            },
            Duration::from_millis(150),
        );
        let elapsed = start.elapsed();

        assert_eq!(out, None, "an overrunning closure must time out to None");
        assert!(
            elapsed < Duration::from_secs(5),
            "the caller must regain control at the wall, not wait for the work: {elapsed:?}"
        );
    }

    /// The complement: `work` that finishes inside the wall returns its value —
    /// the timeout never penalises a fast closure.
    #[test]
    fn test_spawn_with_hard_timeout_returns_fast_work() {
        let out: Option<u32> = spawn_with_hard_timeout(|| 7, Duration::from_secs(5));
        assert_eq!(out, Some(7), "fast work must return its value");
    }

    /// Progress guarantee: after a goal times out, the NEXT call still runs and
    /// succeeds — the abandoned thread does not block the following work.
    #[test]
    fn test_spawn_with_hard_timeout_loop_makes_progress_after_a_timeout() {
        // First call: overruns, times out.
        let first: Option<u32> = spawn_with_hard_timeout(
            || {
                thread::sleep(Duration::from_secs(30));
                1
            },
            Duration::from_millis(100),
        );
        assert_eq!(first, None, "the hard goal must time out");

        // Second call: completes promptly. The loop made progress despite the
        // first goal's still-running detached thread.
        static RAN: AtomicBool = AtomicBool::new(false);
        let second: Option<u32> = spawn_with_hard_timeout(
            || {
                RAN.store(true, Ordering::SeqCst);
                2
            },
            Duration::from_secs(5),
        );
        assert_eq!(second, Some(2), "the next goal must still complete");
        assert!(
            RAN.load(Ordering::SeqCst),
            "the next goal's work must have actually run"
        );
    }
}
