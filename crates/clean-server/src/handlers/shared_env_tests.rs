// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::handlers::tests::free_gate::{gated_source, FreeGate};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{Declaration, Expr, Level, Name};
use std::sync::atomic::AtomicUsize;
use std::sync::mpsc;
use std::time::Duration;

/// A wait for something that must happen: a one-minute hang detector.
const HANG: Duration = Duration::from_secs(60);

fn axiom(name: &str) -> Declaration {
    Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    }
}

/// Work for [`SharedEnv::update`] that adds `name` to its copy. Its first run
/// says its copy is made (`copied`) and waits for `go` before it goes on; a
/// later run goes straight through. Returns the run's number.
fn adding(
    name: &'static str,
    copied: mpsc::Sender<()>,
    go: mpsc::Receiver<()>,
) -> impl Fn(Environment) -> Result<(Environment, usize), String> + Send + Sync + 'static {
    let runs = AtomicUsize::new(0);
    let gate = std::sync::Mutex::new(Some((copied, go)));
    move |mut env: Environment| {
        let run = runs.fetch_add(1, Ordering::Relaxed) + 1;
        let first = gate.lock().ok().and_then(|mut gate| gate.take());
        if let Some((copied, go)) = first {
            let _ = copied.send(());
            if go.recv_timeout(HANG).is_err() {
                return Err("the test never let the work go on".to_string());
            }
        }
        env.add_decl_unchecked(axiom(name));
        Ok((env, run))
    }
}

/// Wait on a pool-side signal without blocking the runtime.
async fn signalled(what: &str, signal: &mpsc::Receiver<()>) {
    let give_up = Instant::now() + HANG;
    while signal.try_recv().is_err() {
        assert!(Instant::now() < give_up, "{what} never happened");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

/// `importModule` installed a copy of the environment made before its load,
/// overwriting a change that landed meanwhile. A copy is published only over
/// the environment it was made from now; over a changed one the work runs
/// again on a fresh copy, and both changes are kept.
#[tokio::test]
async fn a_change_made_while_a_writer_works_is_kept() {
    let shared = SharedEnv::new(Environment::new());
    let pool = WorkPool::new(2);
    let (copied, copy_made) = mpsc::channel();
    let (go, gone) = mpsc::channel();
    let writer = {
        let shared = shared.clone();
        let pool = pool.clone();
        tokio::spawn(async move {
            shared
                .update(&pool, None, adding("from_the_writer", copied, gone))
                .await
        })
    };
    signalled("the writer's copy", &copy_made).await;
    shared
        .write()
        .await
        .add_decl_unchecked(axiom("made_meanwhile"));
    let _ = go.send(());

    let runs = tokio::time::timeout(HANG, writer)
        .await
        .expect("the writer answers")
        .expect("the writer's task")
        .expect("the writer's work ran")
        .expect("the writer's work refused nothing");
    assert_eq!(runs, 2, "the stale copy was worked on again");
    let env = shared.read().await;
    assert!(
        env.get_const(&Name::from_string("made_meanwhile"))
            .is_some(),
        "the change made while the writer worked was overwritten"
    );
    assert!(env
        .get_const(&Name::from_string("from_the_writer"))
        .is_some());
}

/// `loadEnvironment`'s merge held the write lock while it worked, so a reader
/// waited for the whole merge. A writer works on its copy holding nothing.
#[tokio::test]
async fn a_reader_is_served_while_a_writer_works() {
    let shared = SharedEnv::new(Environment::new());
    let pool = WorkPool::new(1);
    let (copied, copy_made) = mpsc::channel();
    let (go, gone) = mpsc::channel();
    let writer = {
        let shared = shared.clone();
        let pool = pool.clone();
        tokio::spawn(async move {
            shared
                .update(&pool, None, adding("merged", copied, gone))
                .await
        })
    };
    signalled("the writer's copy", &copy_made).await;
    assert!(
        shared.try_read().is_ok(),
        "the environment is held while the writer works on its copy"
    );
    assert_eq!(pool.in_use(), 1, "the writer's work holds its slot");
    let _ = go.send(());
    let runs = tokio::time::timeout(HANG, writer)
        .await
        .expect("the writer answers")
        .expect("the writer's task")
        .expect("the writer's work ran")
        .expect("the writer's work refused nothing");
    assert_eq!(runs, 1, "nothing changed meanwhile: one run");
    assert!(shared
        .read()
        .await
        .get_const(&Name::from_string("merged"))
        .is_some());
}

/// A refusal publishes nothing.
#[tokio::test]
async fn a_refused_update_publishes_nothing() {
    let shared = SharedEnv::new(Environment::new());
    let before = shared.revision().await;
    let refused = shared
        .update(&WorkPool::new(1), None, |_env| {
            Err::<(Environment, ()), _>("refused")
        })
        .await
        .expect("the work ran");
    assert_eq!(refused, Err("refused"));
    assert_eq!(shared.revision().await, before);
}

/// The verify family seeds the prelude on every call; counting each call as a
/// change would make every writer working meanwhile work again. Seeding counts
/// a change only when it added something; handing the environment out mutably
/// always counts one.
#[tokio::test]
async fn seeding_what_is_there_counts_no_change() {
    let shared = SharedEnv::new(Environment::new());
    let pool = WorkPool::new(1);
    let start = shared.revision().await;
    let seeded = shared
        .seed(&pool, Environment::init_true_false)
        .await
        .expect("the work ran");
    assert!(seeded.is_ok(), "{seeded:?}");
    let after_seed = shared.revision().await;
    assert_ne!(
        after_seed, start,
        "a seed that added declarations is a change"
    );

    let again = shared
        .seed(&pool, Environment::init_true_false)
        .await
        .expect("the work ran");
    assert!(again.is_ok(), "{again:?}");
    assert_eq!(
        shared.revision().await,
        after_seed,
        "a seed that added nothing is no change"
    );

    drop(shared.write().await);
    assert_eq!(
        shared.revision().await,
        after_seed,
        "a write hold never used is no change"
    );

    shared.write().await.add_decl_unchecked(axiom("handed_out"));
    assert_ne!(shared.revision().await, after_seed);
}

// ---------------------------------------------------------------------------
// Frees off the runtime. Each environment here holds the only reference to a
// gated constant source (`tests/free_gate.rs`), so freeing it lasts until the
// test releases it. These tests run on a one-thread runtime: a free on the
// runtime's thread blocks the test itself, which then can never release it,
// and the free ends only at the hang detector, unreleased.
// ---------------------------------------------------------------------------

/// An environment holding the only reference to a gated source.
fn gated_env() -> (Environment, FreeGate) {
    let (source, gate) = gated_source();
    let mut env = Environment::new();
    env.set_constant_source(source);
    (env, gate)
}

/// The gated free started, the runtime served a read of the environment while
/// it ran, and it ran off the runtime's thread.
async fn freed_off_the_runtime(gate: FreeGate, shared: &SharedEnv) {
    let runtime = std::thread::current().id();
    gate.freeing().await;
    drop(
        tokio::time::timeout(HANG, shared.read())
            .await
            .expect("a read is served while an environment is freed"),
    );
    let freed = gate.release().await;
    assert!(
        freed.released,
        "the free ran on the runtime's thread: the test, waiting on that thread, could not release it"
    );
    assert_ne!(freed.on, runtime, "the free ran on the runtime's thread");
}

/// `replace` freed the environment it replaced on the runtime.
#[tokio::test]
async fn replace_frees_the_old_environment_off_the_runtime() {
    let (env, gate) = gated_env();
    let shared = SharedEnv::new(env);
    shared.replace(Environment::new()).await;
    freed_off_the_runtime(gate, &shared).await;
}

/// A publish freed the environment it replaced on the runtime.
#[tokio::test]
async fn a_publish_frees_the_environment_it_replaces_off_the_runtime() {
    let (env, gate) = gated_env();
    let shared = SharedEnv::new(env);
    // The work lets its copy (and the copy's share of the gated source) go on
    // the pool: the environment the publish replaces holds the only one left.
    let published = shared
        .update(&WorkPool::new(1), None, |_copy| {
            Ok::<_, String>((Environment::new(), ()))
        })
        .await
        .expect("the work ran");
    assert_eq!(published, Ok(()));
    freed_off_the_runtime(gate, &shared).await;
}

/// A copy a publish refused as stale was freed on the runtime.
#[tokio::test]
async fn a_stale_copy_is_freed_off_the_runtime() {
    let shared = SharedEnv::new(Environment::new());
    let pool = WorkPool::new(2);
    let (source, gate) = gated_source();
    let (copied, copy_made) = mpsc::channel();
    let (go, gone) = mpsc::channel::<()>();
    // The first run holds the gated source in its copy, says so, and waits
    // for the test to change the environment; later runs go straight through.
    let first = std::sync::Mutex::new(Some((source, copied, gone)));
    let work = move |mut env: Environment| {
        let gated = first.lock().ok().and_then(|mut first| first.take());
        if let Some((source, copied, gone)) = gated {
            env.set_constant_source(source);
            let _ = copied.send(());
            if gone.recv_timeout(HANG).is_err() {
                return Err("the test never let the work go on".to_string());
            }
        }
        env.add_decl_unchecked(axiom("from_the_writer"));
        Ok((env, ()))
    };
    let writer = {
        let shared = shared.clone();
        tokio::spawn(async move { shared.update(&pool, None, work).await })
    };
    signalled("the writer's copy", &copy_made).await;
    shared
        .write()
        .await
        .add_decl_unchecked(axiom("made_meanwhile"));
    let _ = go.send(());

    freed_off_the_runtime(gate, &shared).await;
    let published = tokio::time::timeout(HANG, writer)
        .await
        .expect("the writer answers")
        .expect("the writer's task")
        .expect("the writer's work ran");
    assert_eq!(published, Ok(()));
}

/// A copy whose request was cancelled while it waited to publish was freed on
/// the runtime, by the cancellation.
#[tokio::test]
async fn a_copy_cancelled_while_it_waits_to_publish_is_freed_off_the_runtime() {
    let shared = SharedEnv::new(Environment::new());
    let pool = WorkPool::new(1);
    let (source, gate) = gated_source();
    let gated = std::sync::Mutex::new(Some(source));
    let work = move |mut env: Environment| {
        if let Some(source) = gated.lock().ok().and_then(|mut gated| gated.take()) {
            env.set_constant_source(source);
        }
        Ok::<_, String>((env, ()))
    };
    let before = shared.revision().await;
    let reading = shared.read().await;
    let writer = {
        let (shared, pool) = (shared.clone(), pool.clone());
        tokio::spawn(async move { shared.update(&pool, None, work).await })
    };
    // The environment is write-preferring: a queued publish keeps new reads
    // out. The work is done when the slot is back.
    let give_up = Instant::now() + HANG;
    while !(shared.try_read().is_err() && pool.in_use() == 0) {
        assert!(
            Instant::now() < give_up,
            "the writer never waited to publish"
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    writer.abort();
    assert!(writer.await.is_err(), "the writer was cancelled");
    drop(reading);
    freed_off_the_runtime(gate, &shared).await;
    assert_eq!(
        shared.revision().await,
        before,
        "a cancelled writer published"
    );
}

/// A copy whose request was cancelled after its work sent the copy, but
/// before the request took it from the answer channel, was dropped with the
/// channel on the runtime (review of 2026-10-16: a `within` timeout firing
/// between its inner poll and its drop). The channel frees an answer nobody
/// took off the runtime now (`work.rs`, `Answer`). Here the runtime's one
/// thread is the test's while the work answers: it waits, without yielding,
/// until the work's slot is back (the answer is then in the channel), and
/// cancels the writer before it is polled again.
#[tokio::test]
async fn a_copy_cancelled_after_its_work_answered_is_freed_off_the_runtime() {
    let shared = SharedEnv::new(Environment::new());
    let pool = WorkPool::new(1);
    let (source, gate) = gated_source();
    let (copied_tx, copied) = mpsc::channel::<()>();
    let (go, gone) = mpsc::channel::<()>();
    let first = std::sync::Mutex::new(Some((source, copied_tx, gone)));
    let work = move |mut env: Environment| {
        if let Some((source, copied, gone)) = first.lock().ok().and_then(|mut f| f.take()) {
            env.set_constant_source(source);
            let _ = copied.send(());
            let _ = gone.recv_timeout(HANG);
        }
        Ok::<_, String>((env, ()))
    };
    let before = shared.revision().await;
    let writer = {
        let (shared, pool) = (shared.clone(), pool.clone());
        tokio::spawn(async move { shared.update(&pool, None, work).await })
    };
    signalled("the writer's copy", &copied).await;
    let _ = go.send(());
    let give_up = Instant::now() + HANG;
    while pool.in_use() != 0 {
        assert!(Instant::now() < give_up, "the work never answered");
        std::thread::sleep(Duration::from_millis(1));
    }
    writer.abort();
    let runtime = std::thread::current().id();
    let ended = tokio::time::timeout(HANG * 2, writer).await;
    assert!(
        matches!(ended, Ok(Err(ref e)) if e.is_cancelled()),
        "the writer was cancelled"
    );
    let freed = gate.release().await;
    assert_eq!(
        shared.revision().await,
        before,
        "a cancelled writer published"
    );
    assert!(
        freed.released,
        "the cancelled writer's copy was freed on the runtime's thread: {freed:?}"
    );
    assert_ne!(
        freed.on, runtime,
        "the copy was freed on the runtime's thread"
    );
}
