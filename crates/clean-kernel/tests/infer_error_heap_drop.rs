// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression witness: an error that OWNS HEAP, returned through `infer_type`'s
//! `?`, is dropped exactly once.
//!
//! The release `infer_type` is `self.tick_heartbeat()?; self.infer_type_fast(e)`.
//! Its `?` moves the residual `Result<Infallible, TypeError>` into the return
//! place. A miscompile that drops that residual AGAIN after the move frees the
//! error's heap twice. The Trust flip's retired `TRUST_DROP_CITE` stack did
//! exactly that to `infer_type` (measured 2026-09-23 as gained drop glue in the
//! object, and 2026-09-24 as the computed gate's C1 refusal
//! `use of moved/uninitialized place ((_7 as Break).0: …)`).
//!
//! Why this needs its own test: on this path only
//! `TypeError::HeartbeatExceeded { profile: Some(_) }` owns heap, and only when
//! the heartbeat profiler is enabled. Without the profiler the variant is plain
//! data, a double drop of it does nothing observable, and the kernel's
//! integration suite passed 242 of 242 against a build carrying the double drop.
//! The one test that did build a heap-owning heartbeat error
//! (`tc/tests/heartbeat.rs::test_profiler_included_in_error`) is a lib unit test,
//! so a battery running the integration suite never saw it.
//!
//! Detection does not depend on the allocator's own double-free checks. After
//! each error is dropped the test allocates a batch of buffers across the small
//! size classes, stamps each with a unique pattern, and re-reads every stamp. A
//! block freed twice is handed out twice, two live buffers alias, and one of the
//! stamps is overwritten. If the allocator traps the double free first, the
//! test process aborts, which is also a failure.

use clean_kernel::{Environment, Expr, Level, TypeChecker, TypeError};

/// Allocate `per_class` buffers in every size class from 16 to 512 bytes, stamp
/// each with a pattern unique to it, and panic if any stamp does not read back.
fn assert_allocations_are_distinct(round: usize, per_class: usize) {
    let mut live: Vec<(u64, Vec<u64>)> = Vec::new();
    let mut id: u64 = (round as u64) << 32;
    for words in (2..=64).step_by(2) {
        for _ in 0..per_class {
            id += 1;
            let buf: Vec<u64> = (0..words as u64).map(|w| id ^ (w << 48)).collect();
            live.push((id, buf));
        }
    }
    for (id, buf) in &live {
        for (w, word) in buf.iter().enumerate() {
            assert_eq!(
                *word,
                *id ^ ((w as u64) << 48),
                "round {round}: buffer {id:#x} word {w} was overwritten: two live allocations \
                 alias, so a block was freed twice"
            );
        }
    }
}

#[test]
fn heartbeat_error_with_profile_is_dropped_once() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(1);
    tc.enable_heartbeat_profiler();
    let prop = Expr::sort(Level::zero());

    // The first call spends the only heartbeat; every later call fails at the
    // tick, which is the `?` in `infer_type` itself.
    let _ = tc.infer_type(&prop);

    let mut with_profile = 0usize;
    for round in 0..256 {
        match tc.infer_type(&prop) {
            Err(TypeError::HeartbeatExceeded { limit, profile }) => {
                assert_eq!(limit, 1);
                let profile = profile.expect(
                    "the profiler is enabled, so the error must own a profile; without it this \
                     test would exercise no heap at all",
                );
                assert!(profile.total() > 0, "the profile must have recorded ticks");
                with_profile += 1;
                drop(profile);
            }
            other => panic!("round {round}: expected HeartbeatExceeded, got {other:?}"),
        }
        assert_allocations_are_distinct(round, 8);
    }
    assert_eq!(with_profile, 256);
}

#[test]
fn heartbeat_error_dropped_unread_keeps_heap_consistent() {
    // The same path, but the error is discarded without being matched, so the
    // only drop of its profile is the one the callee's return hands us.
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(1);
    tc.enable_heartbeat_profiler();
    let prop = Expr::sort(Level::zero());
    let _ = tc.infer_type(&prop);
    for round in 0..256 {
        let result = tc.infer_type(&prop);
        assert!(
            matches!(
                &result,
                Err(TypeError::HeartbeatExceeded {
                    profile: Some(_),
                    ..
                })
            ),
            "round {round}: expected a profiled HeartbeatExceeded, got {result:?}"
        );
        drop(result);
        assert_allocations_are_distinct(round, 8);
    }
}
