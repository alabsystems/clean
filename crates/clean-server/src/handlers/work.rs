// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A request's synchronous work, run off the async runtime under the request's
//! deadline.
//!
//! # Why
//!
//! Handlers used to await `tokio::time::timeout` around synchronous work
//! (elaboration, type checking, certificate checking, proof search). A timeout
//! is a future, and a future is only polled when the task yields; synchronous
//! work never yields, so the timeout could not fire while it ran. The request
//! answered when the work returned, whatever its `timeout_ms`, and the runtime
//! worker running it served nothing else meanwhile: measured on the release
//! server (2026-10-15), a `check` with `timeout_ms: 300` answered a valid
//! result after 2.87 s, and an unrelated `check` sent 0.3 s later waited
//! 2.57 s for it.
//!
//! # What the pool does
//!
//! * The work runs on a pool thread, so the runtime worker stays free and the
//!   request's `tokio::time::timeout` fires at the deadline.
//! * The work runs under the request's deadline
//!   (`clean_kernel::tc::run_until`). The kernel's tick sites, the certificate
//!   verifier and the automation's work-budget charges poll it and stop once
//!   it has passed, and work the deadline interrupted is never reported: the
//!   pool answers [`WorkError::Interrupted`] and the handler answers the
//!   timeout error.
//! * At most [`WorkPool::limit`] pieces of work run at once, abandoned ones
//!   included. A request waits for a slot inside its own timeout, and a slot is
//!   freed only when its work has actually ended, so work that polls no tick
//!   site (parsing, one big-number operation, a decision procedure bounded only
//!   by its own counts) can run on after its request answered, but cannot pile
//!   up past the limit.
//! * A thread whose work the deadline interrupted, or that panicked, exits
//!   instead of taking the next request: whatever its thread-local caches
//!   (the simp-set cache, memo tables) picked up past the deadline leaves with
//!   it. A thread whose work finished keeps its caches for the next request, as
//!   the runtime workers did.
//!
//! Every kernel check a request makes (inferring, checking or reducing a term)
//! runs here, under the request's deadline: `getType`, the proof-state reads
//! that re-check a closed proof, `addDecl` and `loadEnvironment`'s merge
//! included (R32 in `docs/DECISIONS.md`), and so does `importModule`'s load
//! (R34), which reads the deadline before each module it reads, decodes or
//! registers (R36). So does all other work that grows with the request's
//! input or the environment and has no bound of its own (R36): the
//! certificate codec methods ([`answer_on_pool`]), `saveEnvironment`,
//! `getEnvironment`'s JSON and the proof-state searches
//! (`core::answer_with_env`). So, since R87 (2026-10-17), do the
//! parse of the file `verifyFile`, `fillSorries` and `composeProof` are sent
//! (`verify::parse_on_pool`, read under the deadline: `parse_lean.rs`), the
//! scan of an installed Mathverse corpus for the state a tactic's new state
//! was refused under at the lifecycle limit (`tactic.rs`), and the copies of
//! the environment a session is opened with and an `addDecl` checks on
//! (`ServerState::create_session`, `swarm.rs`); since 2026-10-19 so do the
//! verify family's set-up of the shared environment (`SharedEnv::seed`: the
//! kernel copies the whole environment for each inductive it adds) and
//! `verifyFile`'s answers that list a file's holes. Most of what stays on the
//! runtime is bounded by tables the server keeps (the proof-state cache, the
//! widget registry, the status counters) or by a constant
//! (`getEnvironment`'s summary of 100 names), or renders an unsolved proof
//! state's `full` or `compact` snapshot with no corpus installed (its `llm`
//! snapshot selects premises from the whole environment, so it is pool
//! work). The exception grows with a request's input, which the transport
//! bounds (at most 10 MiB a TCP line or WebSocket message): the transport
//! parses each request and writes each answer there (R87 measures
//! why it stays; an answer can be several times its request). A cached proof state, which holds a whole
//! environment, is shared with the cache, never copied there: a tactic copies
//! the state it changes on the pool, and the copy is freed off the runtime
//! whatever becomes of it (failed, refused at the lifecycle limit, or its
//! request cancelled).
//!
//! Shared server state is never written from the pool: a handler reads what
//! the work needs (an environment read guard, cloned parameters) on the async
//! side, and acts on the work's result there, after the pool has answered. A
//! writer hands the pool a copy of what it changes and commits the copy on
//! the async side only when the work finished: `addDecl` a copy of its
//! session, holding the session's lock; `loadEnvironment`'s merge and
//! `importModule` a copy of the environment, made under a read hold they let
//! go before the work runs, published under the write lock only over the
//! environment the copy was made from (`shared_env.rs`). The one exception is
//! `ServerState::olean_cache`, which `importModule`'s load fills from the pool:
//! it holds decoded modules keyed by path and content identity, never a
//! declaration or a verdict, and a module enters it only from a decode that
//! finished with the deadline not passed (`clean-olean`'s
//! `import/deadline.rs`), so a load cut anywhere leaves it holding whole
//! modules, each as good as a fresh decode.
//!
//! An environment the async side lets go (the one a publish replaces, a copy
//! never installed, one a cancelled request held, the copy a failed tactic
//! ran on) is freed off the runtime, on Tokio's blocking pool
//! (`off_runtime.rs`, which says why not here). So is an answer whose request
//! was cancelled after its work sent it but before the request took it (a
//! `within` timeout firing between the two, an aborted task): the answer may
//! hold a whole environment (a writer's copy, a proof state), and it would
//! otherwise be freed where the request's future is dropped, on the runtime
//! ([`Answer`]). A value requests share with a table the server keeps (a
//! cached proof state, a session) is freed by its last holder off the runtime
//! (`off_runtime::Shared`): a request that still held one when the cache or
//! the session map let it go no longer frees it where it lets it go.
//!
//! # Lock order: a writer's lock, then a slot, then the environment
//!
//! A request takes a work slot first and the environment's read guard second
//! (`core::run_with_env`), and never waits for a slot while it holds the
//! environment. The environment's lock is write-preferring, so a request that
//! held the guard while it waited for a slot would close a cycle with a queued
//! writer and the slots' holders waiting behind that writer (review of
//! 2026-10-15: `applyTactic` did, and stalled every pool request for its own
//! `timeout_ms`). A writer's own lock comes before its slot: `addDecl` takes
//! its session's lock, and `loadEnvironment` and `importModule` their turn
//! among the environment's writers (`shared_env::SharedEnv::writer_turn`),
//! then a slot, then the environment. Waiting for a slot holding one of those
//! closes no cycle, because no slot holder ever waits for a session or a
//! writer's turn; it keeps a writer queued behind another from holding a slot
//! while it waits (review of 2026-10-16: two `addDecl`s queued on the session
//! map held both slots of a two-slot pool, and a `check` timed out). The
//! session map itself is held only to look a session up (R34 in
//! `docs/DECISIONS.md`).
//!
//! A request that answers from the environment after its work has run renders
//! from the read hold its work ran under (`core::slot_then_env`), never from a
//! second read: a writer queued during the work is granted between two reads,
//! so the second waited outside the request's timeout and rendered against
//! another environment than the work checked in (review of 2026-10-15:
//! `proofState.openObligation` did). A request whose work is bounded (the
//! list above) takes no slot, and waits for the environment inside its
//! timeout.
//!
//! # Panics
//!
//! The release profile aborts on a panic, so no answer here may depend on
//! catching one. Work whose deadline fired must not panic at all: fixed
//! seeding that the deadline could refuse (a fresh `Environment`, the TLA
//! engine's theories) runs with the deadline suspended, and the tests sweep the
//! handlers at short deadlines and require [`WorkPool::panics`] to stay zero.
//! In a build that unwinds, a panic is answered, never resumed on the request's
//! task: past its deadline as [`WorkError::Interrupted`], before it as
//! [`WorkError::Unavailable`] (the internal error the blocking pool's join
//! error used to be).

use std::any::Any;
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex, PoisonError};
use std::time::{Duration, Instant};

use super::off_runtime::free_off_runtime;
use crate::rpc::{RequestId, Response, RpcError};
use clean_kernel::tc::run_until;
use tokio::sync::{oneshot, OwnedSemaphorePermit, Semaphore};

/// Stack of a work thread.
///
/// The kernel's recursions grow their own stack (`stack_safe`), but parsing
/// and elaboration recurse on the thread's; the runtime workers that ran this
/// work before had 2 MiB. 64 MiB is the stack the kernel builds its prelude on,
/// reserved, not committed: a thread only pays for the depth it reaches.
const WORK_THREAD_STACK_BYTES: usize = 64 * 1024 * 1024;

/// Why work handed to the pool produced no value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WorkError {
    /// The deadline passed while the work ran. Whatever the work returned was
    /// dropped: the request answers its timeout error.
    Interrupted,
    /// The work produced no value: no thread could be started, its thread
    /// ended without an answer, or it panicked before its deadline.
    Unavailable(String),
}

impl WorkError {
    /// The error a request whose work produced no value answers: the timeout
    /// error for its `timeout` when the deadline interrupted the work (or the
    /// request's timeout fired first), an internal error otherwise.
    pub(crate) fn into_rpc_error(self, timeout: Duration) -> RpcError {
        match self {
            Self::Interrupted => RpcError::timeout(timeout.as_millis() as u64),
            Self::Unavailable(detail) => RpcError::internal_error(detail),
        }
    }
}

/// Await a request's waits and work inside its `timeout`. A timeout that fires
/// first is an interrupted request: whatever the work goes on to compute is
/// dropped with the future.
pub(crate) async fn within<T>(
    timeout: Duration,
    work: impl Future<Output = Result<T, WorkError>>,
) -> Result<T, WorkError> {
    tokio::time::timeout(timeout, work)
        .await
        .unwrap_or(Err(WorkError::Interrupted))
}

/// Answer a request whose whole work is synchronous and reads no shared state
/// (decoding, encoding): `answer` builds the response on a pool thread under
/// the request's deadline, inside its `timeout`, which `start` began. A
/// request whose timeout fires first answers the timeout error, and what its
/// work goes on to build is dropped.
pub(crate) async fn answer_on_pool(
    pool: &WorkPool,
    id: RequestId,
    start: Instant,
    timeout: Duration,
    answer: impl FnOnce(RequestId) -> Response + Send + 'static,
) -> Response {
    let deadline = start.checked_add(timeout);
    let answering = id.clone();
    match within(timeout, pool.run(deadline, move || answer(answering))).await {
        Ok(response) => response,
        Err(error) => Response::error(id, error.into_rpc_error(timeout)),
    }
}

/// What a pool thread reports back.
enum Outcome<T> {
    /// The work finished before its deadline fired.
    Finished(T),
    /// The deadline fired while the work ran; what it returned was dropped.
    Interrupted,
    /// The work panicked before its deadline: the panic's message.
    Panicked(String),
}

/// The request's end of its work's answer channel.
///
/// A request cancelled after its work sent the answer, but before the request
/// took it, drops the answer with this. The answer may hold a whole
/// environment (a writer's copy, a proof state, a batch's children), so what
/// is left in the channel then is freed off the runtime
/// ([`free_off_runtime`]): dropped with the channel, it would be freed on the
/// runtime worker that dropped the request's future. The channel is closed
/// first, so the check races nothing: work that answers after the close finds
/// the request gone, and its answer is dropped on its pool thread.
struct Answer<T: Send + 'static>(oneshot::Receiver<Outcome<T>>);

impl<T: Send + 'static> Drop for Answer<T> {
    fn drop(&mut self) {
        self.0.close();
        if let Ok(untaken) = self.0.try_recv() {
            free_off_runtime(untaken);
        }
    }
}

/// One piece of work, boxed for a pool thread; returns whether the thread may
/// take another.
type Job = Box<dyn FnOnce() -> bool + Send>;

struct Shared {
    limit: usize,
    slots: Arc<Semaphore>,
    /// Panics caught in this pool's work, before or past a deadline.
    panics: AtomicUsize,
    /// Threads waiting for work, by the sender that reaches each.
    idle: Mutex<Vec<mpsc::Sender<Dispatch>>>,
}

/// A slot in the pool, held from before the work starts until it has ended.
pub(crate) struct WorkSlot {
    _permit: OwnedSemaphorePermit,
    shared: Arc<Shared>,
}

struct Dispatch {
    job: Job,
    slot: WorkSlot,
    /// The sender that reached this thread, put back in the idle list when the
    /// thread may take more work.
    me: mpsc::Sender<Dispatch>,
}

/// The server's pool of work threads. Cloning shares the pool.
#[derive(Clone)]
pub(crate) struct WorkPool {
    shared: Arc<Shared>,
}

impl WorkPool {
    /// A pool running at most `limit` (at least one) pieces of work at once.
    pub(crate) fn new(limit: usize) -> Self {
        let limit = limit.max(1);
        Self {
            shared: Arc::new(Shared {
                limit,
                slots: Arc::new(Semaphore::new(limit)),
                panics: AtomicUsize::new(0),
                idle: Mutex::new(Vec::new()),
            }),
        }
    }

    /// A pool with one slot per available core.
    pub(crate) fn with_default_limit() -> Self {
        Self::new(std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get))
    }

    /// The most pieces of work that run at once.
    pub(crate) fn limit(&self) -> usize {
        self.shared.limit
    }

    /// Pieces of work holding a slot now: running, abandoned-but-running, or
    /// about to start.
    pub(crate) fn in_use(&self) -> usize {
        self.shared.limit - self.shared.slots.available_permits()
    }

    /// Panics caught in this pool's work so far. Each would have aborted a
    /// release server (`panic = "abort"`), so the tests require none.
    #[cfg(test)]
    pub(crate) fn panics(&self) -> usize {
        self.shared.panics.load(Ordering::Relaxed)
    }

    /// Wait for a free slot. Await it inside the request's timeout: a request
    /// that times out waiting leaves the queue having run nothing. Never wait
    /// for one while holding the environment (the lock order above).
    pub(crate) async fn slot(&self) -> Result<WorkSlot, WorkError> {
        let permit = Arc::clone(&self.shared.slots)
            .acquire_owned()
            .await
            .map_err(|e| WorkError::Unavailable(format!("the work pool is closed: {e}")))?;
        Ok(WorkSlot {
            _permit: permit,
            shared: Arc::clone(&self.shared),
        })
    }

    /// Run `work` on a pool thread under `deadline` (`None`: no deadline),
    /// waiting for a slot first.
    pub(crate) async fn run<T: Send + 'static>(
        &self,
        deadline: Option<Instant>,
        work: impl FnOnce() -> T + Send + 'static,
    ) -> Result<T, WorkError> {
        let slot = self.slot().await?;
        Self::run_in(slot, deadline, work).await
    }

    /// Run `work` on a pool thread under `deadline` in a slot already held.
    ///
    /// A panic is counted ([`WorkPool::panics`]) and answered: as `Interrupted`
    /// when the deadline has passed by the time it is caught (the clock
    /// decides: a batch item's latch is its own thread's), else as
    /// `Unavailable`. Only a build that unwinds gets here; see "Panics" above.
    pub(crate) async fn run_in<T: Send + 'static>(
        slot: WorkSlot,
        deadline: Option<Instant>,
        work: impl FnOnce() -> T + Send + 'static,
    ) -> Result<T, WorkError> {
        let (answer, answered) = oneshot::channel::<Outcome<T>>();
        let mut answered = Answer(answered);
        let shared = Arc::clone(&slot.shared);
        let job: Job = Box::new(move || {
            let mut panicked = None;
            let finished = run_until(deadline, || match catch_unwind(AssertUnwindSafe(work)) {
                Ok(value) => Some(value),
                Err(panic) => {
                    panicked = Some(panic_message(panic.as_ref()));
                    None
                }
            });
            let outcome = match (finished, panicked) {
                (Some(Some(value)), _) => Outcome::Finished(value),
                (_, Some(message)) => {
                    shared.panics.fetch_add(1, Ordering::Relaxed);
                    tracing::error!(%message, "a request's work panicked");
                    if past(deadline) {
                        Outcome::Interrupted
                    } else {
                        Outcome::Panicked(message)
                    }
                }
                _ => Outcome::Interrupted,
            };
            let reusable = matches!(outcome, Outcome::Finished(_));
            // The request may have stopped waiting; the answer is then dropped.
            let _ = answer.send(outcome);
            reusable
        });
        dispatch(job, slot)?;
        match (&mut answered.0).await {
            Ok(Outcome::Finished(value)) => Ok(value),
            Ok(Outcome::Interrupted) => Err(WorkError::Interrupted),
            Ok(Outcome::Panicked(message)) => Err(WorkError::Unavailable(format!(
                "the request's work panicked: {message}"
            ))),
            Err(_) => Err(WorkError::Unavailable(
                "the work thread ended without an answer".to_string(),
            )),
        }
    }
}

/// Run one item of a batch under `deadline` on the current thread (a rayon
/// worker: the deadline is thread-local, so a batch installs it per item).
/// `None` when the deadline interrupted the item: what it returned is dropped.
/// A panic propagates to the batch's pool thread, which counts and answers it
/// (`WorkPool::run_in`).
pub(crate) fn run_item_until<T>(deadline: Option<Instant>, item: impl FnOnce() -> T) -> Option<T> {
    run_until(deadline, item)
}

/// Has `deadline` passed? Reads the clock.
///
/// Work that was running when its deadline passed may have been cut short (the
/// kernel's latch fires only once the clock has passed the deadline), so a
/// batch reads this after each item, before it reports the item or starts the
/// next one: an item it reads `true` after is no verdict.
pub(crate) fn past(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

/// Has this thread's deadline (the one `run_until` installed for the work)
/// passed? Reads the clock now, and latches the deadline when it has, so the
/// work's `run_until` answers `None` and the request its timeout error.
///
/// The kernel's poll reads the clock once every 1,024 polls. A `run_until`
/// with no deadline of its own keeps the caller's and restores it with the
/// poll's countdown at zero, so the poll after it reads the clock
/// (`clean-olean`'s `import/deadline.rs` reads it the same way). For work
/// whose steps are few and long (a step that searches a whole file, a commit
/// that must not happen past the deadline).
pub(crate) fn deadline_passed_now() -> bool {
    let _ = run_until(None, || ());
    clean_kernel::tc::poll_deadline()
}

/// A rayon pool of a batch's own, for batches whose items run tactics or
/// replays: an item the deadline interrupts may leave thread-local caches (the
/// simp-set cache) filled past it, and this pool's threads end with the batch.
/// `threads` is capped at the items (at least one). When no pool can be built
/// the batch fails closed: it never falls back to rayon's global pool.
pub(crate) fn batch_pool(threads: usize, items: usize) -> Result<rayon::ThreadPool, WorkError> {
    rayon::ThreadPoolBuilder::new()
        .num_threads(threads.min(items).max(1))
        .build()
        .map_err(|e| WorkError::Unavailable(format!("cannot start the batch's threads: {e}")))
}

/// The message of a caught panic.
fn panic_message(panic: &(dyn Any + Send)) -> String {
    panic
        .downcast_ref::<&str>()
        .map(|message| (*message).to_string())
        .or_else(|| panic.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "a panic without a message".to_string())
}

/// Hand `job` to an idle thread, or to a new one.
fn dispatch(job: Job, slot: WorkSlot) -> Result<(), WorkError> {
    let mut pending = (job, slot);
    // An idle thread only leaves the list to take work, so a send to one
    // succeeds; a failed send falls through to a new thread, once.
    for _ in 0..2 {
        let idle = pending
            .1
            .shared
            .idle
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .pop();
        let me = match idle {
            Some(sender) => sender,
            None => spawn_work_thread()?,
        };
        let (job, slot) = pending;
        match me.send(Dispatch {
            job,
            slot,
            me: me.clone(),
        }) {
            Ok(()) => return Ok(()),
            Err(mpsc::SendError(back)) => pending = (back.job, back.slot),
        }
    }
    Err(WorkError::Unavailable(
        "no work thread took the work".to_string(),
    ))
}

fn spawn_work_thread() -> Result<mpsc::Sender<Dispatch>, WorkError> {
    let (sender, jobs) = mpsc::channel::<Dispatch>();
    std::thread::Builder::new()
        .name("clean-server-work".to_string())
        .stack_size(WORK_THREAD_STACK_BYTES)
        .spawn(move || work_thread(&jobs))
        .map_err(|e| WorkError::Unavailable(format!("cannot start a work thread: {e}")))?;
    Ok(sender)
}

/// A pool thread: takes work until its work is interrupted or panics, or the
/// pool is gone (its idle sender dropped with the pool).
fn work_thread(jobs: &mpsc::Receiver<Dispatch>) {
    while let Ok(Dispatch { job, slot, me }) = jobs.recv() {
        if !job() {
            // Leaving: the slot is freed as the thread ends, and its
            // thread-local state goes with it.
            return;
        }
        // Idle again BEFORE the slot is freed, so the request that takes the
        // slot finds this thread rather than starting another.
        slot.shared
            .idle
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(me);
        drop(slot);
    }
}

#[cfg(test)]
#[path = "work_tests.rs"]
mod tests;
