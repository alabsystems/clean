// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::time::Duration;

/// Each test runs on its own thread, so the thread-local state cannot leak
/// between tests that share a harness thread.
fn on_fresh_thread<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::spawn(f)
        .join()
        .expect("deadline test thread must not panic");
}

fn passed() -> Option<Instant> {
    Some(Instant::now())
}

fn distant() -> Option<Instant> {
    Instant::now().checked_add(Duration::from_secs(3600))
}

#[test]
fn no_deadline_never_fires() {
    on_fresh_thread(|| {
        for _ in 0..(4 * CLOCK_EVERY) {
            assert!(!poll_deadline());
        }
        assert!(!deadline_fired());
        assert_eq!(run_until(None, || 7), Some(7));
    });
}

#[test]
fn a_passed_deadline_fires_at_the_first_poll_and_latches() {
    on_fresh_thread(|| {
        let result = run_until(passed(), || {
            assert!(poll_deadline(), "the first poll reads the clock");
            assert!(deadline_fired());
            assert!(poll_deadline(), "the latch holds without a clock read");
            "what the work returned"
        });
        assert_eq!(result, None);
        assert!(!deadline_fired(), "the latch ends with the call");
        assert!(!poll_deadline(), "no deadline is left installed");
    });
}

#[test]
fn work_that_never_polls_returns_its_value_even_past_its_deadline() {
    on_fresh_thread(|| {
        // A deadline nobody polled interrupted nothing: the value is the
        // value the work computes without one.
        assert_eq!(run_until(passed(), || 3), Some(3));
    });
}

#[test]
fn a_distant_deadline_changes_nothing() {
    on_fresh_thread(|| {
        let result = run_until(distant(), || {
            for _ in 0..(4 * CLOCK_EVERY) {
                assert!(!poll_deadline());
            }
            11
        });
        assert_eq!(result, Some(11));
    });
}

#[test]
fn a_deadline_passing_during_the_work_fires_within_one_clock_period() {
    on_fresh_thread(|| {
        let deadline = Instant::now() + Duration::from_millis(20);
        let mut polls_after = None;
        let result = run_until(Some(deadline), || {
            let mut polls: u64 = 0;
            // A one-minute hang detector, not a latency budget.
            let give_up = Instant::now() + Duration::from_secs(60);
            while !poll_deadline() {
                polls += 1;
                assert!(Instant::now() < give_up, "the deadline never fired");
                if Instant::now() >= deadline && polls_after.is_none() {
                    polls_after = Some(polls);
                }
            }
            if let Some(start) = polls_after {
                assert!(
                    polls - start <= u64::from(CLOCK_EVERY),
                    "fired {} polls after the deadline passed",
                    polls - start
                );
            }
        });
        assert_eq!(result, None);
    });
}

#[test]
fn a_nested_call_keeps_the_earlier_deadline_and_restores_the_outer_one() {
    on_fresh_thread(|| {
        let outer = run_until(distant(), || {
            // The inner call's own deadline is the earlier one.
            assert_eq!(run_until(passed(), poll_deadline), None);
            // The outer deadline is distant: the outer call goes on.
            assert!(!poll_deadline());
            // An inner call cannot extend the outer deadline either.
            assert_eq!(run_until(None, poll_deadline), Some(false));
            5
        });
        assert_eq!(outer, Some(5));
    });
}

#[test]
fn a_call_made_after_the_enclosing_deadline_fired_is_interrupted_at_once() {
    on_fresh_thread(|| {
        let mut inner = None;
        let outer = run_until(passed(), || {
            assert!(poll_deadline());
            inner = Some(run_until(distant(), || 1));
        });
        assert_eq!(inner, Some(None));
        assert_eq!(outer, None);
    });
}

#[test]
fn a_suspended_region_runs_unbounded_and_the_deadline_returns_after_it() {
    on_fresh_thread(|| {
        let result = run_until(passed(), || {
            assert!(poll_deadline());
            let inside = with_deadline_suspended(|| {
                (0..(4 * CLOCK_EVERY)).all(|_| !poll_deadline()) && !deadline_fired()
            });
            assert!(inside, "nothing fires inside the suspended region");
            assert!(deadline_fired(), "the latch is back after the region");
        });
        assert_eq!(result, None);
    });
}

#[test]
fn the_state_is_restored_when_the_work_unwinds() {
    on_fresh_thread(|| {
        let unwound = std::panic::catch_unwind(|| {
            let _ = run_until(passed(), || {
                assert!(poll_deadline());
                panic!("the work unwinds");
            });
        });
        assert!(unwound.is_err());
        assert!(!deadline_fired());
        assert!(!poll_deadline());
        assert_eq!(run_until(distant(), || 2), Some(2));
    });
}

#[test]
fn the_deadline_is_thread_local() {
    on_fresh_thread(|| {
        let mut seen = None;
        let result = run_until(passed(), || {
            assert!(poll_deadline());
            seen = Some(
                std::thread::spawn(|| (poll_deadline(), deadline_fired()))
                    .join()
                    .expect("inner thread must not panic"),
            );
        });
        assert_eq!(result, None);
        assert_eq!(seen, Some((false, false)), "another thread has no deadline");
    });
}

// ── The kernel's tick sites ───────────────────────────────────────────────

use crate::cert::{CertError, CertVerifier, ProofCert};
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::tc::{TypeChecker, TypeError};
use std::sync::Arc;

/// A wait for something that must happen: a one-minute hang detector.
const HANG: Duration = Duration::from_secs(60);

/// Run `f` on its own thread; panic if it has not answered within [`HANG`].
fn within_hang_detector<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    let (answer, answered) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = answer.send(f());
    });
    answered
        .recv_timeout(HANG)
        .expect("the work must stop within the hang detector")
}

/// `(fun x : Prop => x x) (fun x : Prop => x x)`: reduces to itself forever.
fn omega() -> Expr {
    let self_app = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::app(Expr::bvar(0), Expr::bvar(0)),
    );
    Expr::app(self_app.clone(), self_app)
}

/// A certificate for `Prop` whose `DefEq` step asks the verifier to reduce
/// `omega`. The verifier's reduction has no fuel: unbounded, it never ends.
fn endless_cert() -> ProofCert {
    ProofCert::DefEq {
        inner: Arc::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(omega()),
        actual_type: Box::new(Expr::sort(Level::succ(Level::zero()))),
        eq_steps: vec![],
    }
}

#[test]
fn the_type_checker_refuses_past_its_deadline_and_is_unchanged_before_it() {
    on_fresh_thread(|| {
        let env = Environment::new();
        let term = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        );
        let unbounded = TypeChecker::new(&env).infer_type(&term);
        assert!(unbounded.is_ok());
        let bounded = run_until(distant(), || TypeChecker::new(&env).infer_type(&term));
        assert_eq!(
            bounded.map(|r| r.ok()),
            Some(unbounded.ok()),
            "a deadline that never fires changes nothing"
        );
        // Past the deadline the first tick refuses, and the call is discarded.
        let mut refused = None;
        let interrupted = run_until(passed(), || {
            refused = Some(TypeChecker::new(&env).infer_type(&term));
        });
        assert_eq!(interrupted, None);
        assert!(matches!(refused, Some(Err(TypeError::Interrupted))));
    });
}

#[test]
fn the_cert_verifier_stops_at_its_deadline() {
    // The deadline bounds a check that has no other bound.
    let answer = within_hang_detector(|| {
        let env = Environment::new();
        let deadline = Instant::now() + Duration::from_millis(200);
        let mut verdict = None;
        let outcome = run_until(Some(deadline), || {
            verdict =
                Some(CertVerifier::new(&env).verify(&endless_cert(), &Expr::sort(Level::zero())));
        });
        (outcome, verdict)
    });
    assert_eq!(answer.0, None);
    assert!(
        matches!(answer.1, Some(Err(CertError::Interrupted))),
        "the verifier names the deadline, not a type error: {:?}",
        answer.1
    );
}

#[test]
fn the_cert_verifier_is_unchanged_before_its_deadline() {
    on_fresh_thread(|| {
        let env = Environment::new();
        let cert = ProofCert::Sort {
            level: Level::zero(),
        };
        let prop = Expr::sort(Level::zero());
        let unbounded = CertVerifier::new(&env).verify(&cert, &prop);
        assert!(unbounded.is_ok());
        let bounded = run_until(distant(), || CertVerifier::new(&env).verify(&cert, &prop));
        assert_eq!(
            bounded.map(|r| r.ok()),
            Some(unbounded.ok()),
            "a deadline that never fires changes nothing"
        );
    });
}

/// Review of 2026-10-15: `Environment::new()` `expect`s its three seed
/// declarations, and a deadline that had passed refused the first of them, so
/// building a fresh environment under one panicked (a release server aborted
/// on a `proveTLA` with `timeout_ms: 0`). The seeding runs with the deadline
/// suspended; the latch is back after it, and the call is still interrupted.
#[test]
fn a_fresh_environment_is_seeded_whole_under_a_passed_deadline() {
    on_fresh_thread(|| {
        let mut seeded = None;
        let interrupted = run_until(passed(), || {
            assert!(poll_deadline());
            let env = Environment::new();
            seeded = Some(
                ["sorry", "trustedArith", "trustedAy"]
                    .iter()
                    .all(|name| env.get_const(&crate::Name::from_string(name)).is_some()),
            );
            assert!(deadline_fired(), "the latch is back after the seeding");
        });
        assert_eq!(
            interrupted, None,
            "the call the deadline fired in is discarded"
        );
        assert_eq!(seeded, Some(true));
    });
}
