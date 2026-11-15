// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::mpsc;
use std::time::Duration;

/// A wait for something that must happen: a one-minute hang detector.
const HANG: Duration = Duration::from_secs(60);

fn past() -> Option<Instant> {
    Some(Instant::now())
}

/// Work that polls the deadline the way the kernel's tick sites do, until it
/// fires (or the hang detector does).
fn spin_until_interrupted() -> &'static str {
    let give_up = Instant::now() + HANG;
    while Instant::now() < give_up {
        if clean_kernel::tc::poll_deadline() {
            return "a degraded answer nobody may see";
        }
    }
    "the deadline never fired"
}

#[tokio::test]
async fn work_runs_on_a_pool_thread_and_the_thread_is_reused() {
    let pool = WorkPool::new(2);
    let caller = std::thread::current().id();
    let first = pool
        .run(None, || std::thread::current().id())
        .await
        .expect("work runs");
    assert_ne!(first, caller, "the work left the async task's thread");
    let second = pool
        .run(None, || std::thread::current().id())
        .await
        .expect("work runs");
    assert_eq!(first, second, "a thread whose work finished takes the next");
    assert_eq!(pool.in_use(), 0);
}

#[tokio::test]
async fn interrupted_work_answers_interrupted_and_its_thread_leaves() {
    let pool = WorkPool::new(1);
    let before = pool
        .run(None, || std::thread::current().id())
        .await
        .expect("work runs");
    let interrupted = pool
        .run(past(), || {
            (spin_until_interrupted(), std::thread::current().id())
        })
        .await;
    assert_eq!(interrupted, Err(WorkError::Interrupted));
    let after = pool
        .run(None, || std::thread::current().id())
        .await
        .expect("work runs");
    assert_ne!(
        before, after,
        "the thread that ran past its deadline did not take more work"
    );
}

#[tokio::test]
async fn a_distant_deadline_changes_nothing() {
    let pool = WorkPool::new(1);
    let distant = Instant::now().checked_add(Duration::from_secs(3600));
    let answer = pool
        .run(distant, || {
            (0..10_000).all(|_| !clean_kernel::tc::poll_deadline())
        })
        .await;
    assert_eq!(answer, Ok(true));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_slots_bound_running_work_abandoned_work_included() {
    let pool = WorkPool::new(1);
    let (release, released) = mpsc::channel::<()>();
    let (started, has_started) = mpsc::channel::<()>();
    // The first piece of work holds the only slot until it is released.
    let held = pool.clone();
    let first = tokio::spawn(async move {
        held.run(None, move || {
            let _ = started.send(());
            released.recv_timeout(HANG).is_ok()
        })
        .await
    });
    has_started
        .recv_timeout(HANG)
        .expect("the first work started");
    assert_eq!(pool.in_use(), 1);
    // A request that gives up waiting for a slot ran nothing.
    let waited = tokio::time::timeout(Duration::from_millis(50), pool.slot()).await;
    assert!(waited.is_err(), "no slot is free while the work runs");
    // Abandoning the request does not free the slot: the work still runs.
    first.abort();
    let _ = first.await;
    assert_eq!(pool.in_use(), 1, "the abandoned work still holds its slot");
    release.send(()).expect("the work is waiting");
    let slot = tokio::time::timeout(HANG, pool.slot())
        .await
        .expect("the slot is freed when the work ends")
        .expect("pool open");
    drop(slot);
    assert_eq!(pool.in_use(), 0);
}

#[tokio::test]
async fn a_panic_before_the_deadline_is_answered_and_counted_and_its_thread_leaves() {
    let pool = WorkPool::new(1);
    let before = pool
        .run(None, || std::thread::current().id())
        .await
        .expect("work runs");
    let answer = pool
        .run(None, || -> () { panic!("the work panicked") })
        .await;
    match answer {
        Err(WorkError::Unavailable(detail)) => assert!(
            detail.contains("the work panicked"),
            "the answer names the panic: {detail}"
        ),
        other => panic!("a panic before any deadline is an internal error, got {other:?}"),
    }
    assert_eq!(pool.panics(), 1);
    let after = pool
        .run(None, || std::thread::current().id())
        .await
        .expect("work runs");
    assert_ne!(
        before, after,
        "the thread that panicked did not take more work"
    );
}

#[tokio::test]
async fn a_panic_after_the_deadline_fired_is_interrupted_work_and_counted() {
    let pool = WorkPool::new(1);
    let answer = pool
        .run(past(), || {
            assert!(clean_kernel::tc::poll_deadline());
            panic!("a degraded step panicked past the deadline");
        })
        .await;
    assert_eq!(answer, Err::<(), _>(WorkError::Interrupted));
    assert_eq!(pool.panics(), 1, "the panic is counted, not hidden");
}

#[tokio::test]
async fn a_batch_item_that_panics_after_its_deadline_is_interrupted_and_counted() {
    let pool = WorkPool::new(1);
    let deadline = past();
    let answer = pool
        .run(deadline, move || {
            let items = batch_pool(2, 2).expect("a pool");
            items.install(|| {
                use rayon::prelude::*;
                (0..2)
                    .into_par_iter()
                    .map(|_| {
                        run_item_until(deadline, || {
                            assert!(clean_kernel::tc::poll_deadline());
                            panic!("a degraded step panicked past the deadline");
                        })
                    })
                    .collect::<Vec<Option<()>>>()
            })
        })
        .await;
    assert_eq!(answer, Err(WorkError::Interrupted));
    assert_eq!(pool.panics(), 1);
    let finished = std::thread::spawn(|| run_item_until(None, || 4))
        .join()
        .expect("no panic");
    assert_eq!(finished, Some(4));
}

#[test]
fn a_batch_pool_has_no_more_threads_than_items() {
    assert_eq!(batch_pool(8, 1).expect("a pool").current_num_threads(), 1);
    assert_eq!(batch_pool(8, 0).expect("a pool").current_num_threads(), 1);
    assert_eq!(batch_pool(2, 5).expect("a pool").current_num_threads(), 2);
}

#[test]
fn past_reads_the_clock() {
    assert!(!super::past(None));
    assert!(super::past(past()));
    assert!(!super::past(
        Instant::now().checked_add(Duration::from_secs(3600))
    ));
}

/// An answer its request never took (the request was cancelled after its
/// work sent the answer, before the request received it) was dropped with
/// the answer channel where the request's future was dropped: on the runtime.
/// An answer may hold a whole environment (a writer's copy, a proof state a
/// tactic ran on). Here the answer holds the only reference to a gated source
/// (`tests/free_gate.rs`), whose free lasts until the test releases it: on
/// this one-thread runtime a free on the runtime's thread can never be
/// released (the test waits on that thread), and it ends at the hang
/// detector, unreleased.
#[tokio::test]
async fn an_answer_its_request_never_took_is_freed_off_the_runtime() {
    let pool = WorkPool::new(1);
    let (source, gate) = crate::handlers::tests::free_gate::gated_source();
    let (started_tx, started) = mpsc::channel::<()>();
    let (go, gone) = mpsc::channel::<()>();
    let request = {
        let pool = pool.clone();
        tokio::spawn(async move {
            pool.run(None, move || {
                let _ = started_tx.send(());
                let _ = gone.recv_timeout(HANG);
                source
            })
            .await
            .map(drop)
        })
    };
    // Yield until the work runs: the request then waits for its answer.
    let give_up = Instant::now() + HANG;
    while started.try_recv().is_err() {
        assert!(Instant::now() < give_up, "the work never started");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    // From here the runtime's one thread is the test's, and nothing is polled
    // until the test awaits: let the work answer, and wait (blocking) until
    // its slot is back, by which time its answer is in the channel.
    let _ = go.send(());
    while pool.in_use() != 0 {
        assert!(Instant::now() < give_up, "the work never answered");
        std::thread::sleep(Duration::from_millis(1));
    }
    request.abort();
    let runtime = std::thread::current().id();
    let ended = tokio::time::timeout(HANG * 2, request).await;
    assert!(
        matches!(ended, Ok(Err(ref e)) if e.is_cancelled()),
        "the request was cancelled"
    );
    let freed = gate.release().await;
    assert!(
        freed.released,
        "the untaken answer was freed on the runtime's thread: {freed:?}"
    );
    assert_ne!(
        freed.on, runtime,
        "the answer was freed on the runtime's thread"
    );
}
