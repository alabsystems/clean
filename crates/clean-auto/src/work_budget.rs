// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration-scoped, deterministic work budget for proof AUTOMATION — the
//! shape of Lean's `maxHeartbeats`.
//!
//! # Why this exists
//!
//! Measured 2026-09-26 on the pinned source-elaboration slice (the dated
//! report `reports/source-elab/srcelab-2026-09-26-g07774b87b.json`, per-
//! declaration timing): `Function.Injective.dite` in
//! `Mathlib/Logic/Function/Basic.lean` spent **1,421 s of the file's 1,498 s**
//! of elaboration inside one `grind` → `decide` → superposition-fallback path
//! (`crates/clean-elab/src/tactic/smt/decide/recovery.rs`), and then FAILED
//! with `grind: no progress`. The performance audit's `sample` snapshots
//! (`reports/lean4-replacement-audit-2026-09-24/performance.json`, 8 of 8
//! between 400 s and 1,800 s) put all of it in
//! `SuperpositionProver::prove_until(10_000, None)`. Nothing bounded it: the
//! kernel's ambient `--decl-budget` counts kernel operations only (the run's
//! `peak_decl_ticks` was 11.95M against a 2e9 budget), and the superposition
//! loop never ticks it: it makes no kernel call. (`simp` and `grind` tick it
//! only through the kernel checks they make, never for their own steps.)
//!
//! # The Lean shape it ports
//!
//! Lean bounds all elaboration work of ONE command by `maxHeartbeats`:
//! `Lean.Core.checkMaxHeartbeatsCore` (`src/lean/Lean/CoreM.lean`) compares
//! the heartbeats spent since the command's `initHeartbeats` against the
//! limit and throws `throwMaxHeartbeat` — "(deterministic) timeout …,
//! maximum number of heartbeats … has been reached" — from `checkSystem`,
//! which `whnf`, `isDefEq`, `simp` (`Simp.simpLoop`, `Lean/Meta/Tactic/Simp/
//! Main.lean`) and `grind` call as they work. The exception is a RUNTIME
//! exception (`Exception.isRuntime`), which `Core.tryCatch` re-throws rather
//! than handing to `first`/`try`/`<|>`, so exhausting the budget fails the
//! declaration with that named error.
//!
//! Here the unit is a *work unit* counted at the automation's own loop heads
//! (see [`charge`]'s callers: the superposition given-clause loop, every simp
//! lemma attempt and traversal frame, every `grind` core step and closer), not
//! an allocation or a clock, and the bound is only as tight as those sites are
//! dense. What a declaration spends is not load-independent everywhere,
//! though: a search that also carries its own wall-clock deadline (`grind`'s
//! automation-engine fallback runs superposition under one, and
//! `prove_until` tests that deadline after each step's charge) can stop sooner
//! on a slower or busier machine and spend fewer units.
//!
//! # Scope: one LEAF declaration
//!
//! Lean's heartbeat window is one command, and in Lean a `namespace` or
//! `section` is not a command that contains its members — each member is its
//! own command. Clean's elaborator refills this budget at the same place it
//! starts a per-declaration timing record (`clean_elab`'s
//! `elaborate_decl_and_register_inner_with_aux`, outermost non-container call
//! only). That is deliberately NOT the kernel's ambient `--decl-budget`,
//! whose unit is the TOP-LEVEL surface declaration: exhausting that one rolls
//! a whole `namespace Function … end Function` block back to `diverged`,
//! which would take every passing member of the block with it.
//!
//! # Disabled by default, everywhere
//!
//! A limit of `0` means unlimited and is the initial value on every thread;
//! disabled, every entry point is one thread-local load and a compare, and
//! nothing is counted. `clean check` is the only production caller that
//! turns it on (`--automation-budget`).
//!
//! # Exhaustion can only take a proof away
//!
//! A charge that finds the budget spent returns `false`, and every caller
//! answers that by giving up exactly as it gives up on its own limits — the
//! prover reports `ResourceLimit`, `simp` trips its traversal budget and
//! leaves the goal unchanged, `grind` fails. No caller builds a term from an
//! exhausted search, so soundness is untouched: the kernel still re-checks
//! whatever a surviving path produces. The budget LATCHES for the rest of
//! the declaration, like Lean's, so a later automation call in the same
//! declaration fails at once instead of re-spending.

use std::cell::Cell;

/// Thread-local state. One `thread_local!` entry so a charge pays for one TLS
/// lookup.
struct WorkBudget {
    /// Units granted per declaration. `0` disables the mechanism.
    limit: Cell<u64>,
    /// Units still available in the current declaration.
    remaining: Cell<u64>,
    /// The site whose charge found the budget spent, once it has been; `None`
    /// until then. This is the latch.
    exhausted_at: Cell<Option<&'static str>>,
}

thread_local! {
    static BUDGET: WorkBudget = const {
        WorkBudget {
            limit: Cell::new(0),
            remaining: Cell::new(0),
            exhausted_at: Cell::new(None),
        }
    };
}

/// Set the per-declaration limit on this thread and start a fresh
/// declaration. `0` disables the mechanism.
pub(crate) fn set_limit(limit: u64) {
    BUDGET.with(|b| {
        b.limit.set(limit);
        b.remaining.set(limit);
        b.exhausted_at.set(None);
    });
}

/// Refill the budget for the next declaration; a no-op while disabled.
pub(crate) fn begin_declaration() {
    BUDGET.with(|b| {
        b.remaining.set(b.limit.get());
        b.exhausted_at.set(None);
    });
}

/// The configured limit; `0` when disabled.
pub(crate) fn limit() -> u64 {
    BUDGET.with(|b| b.limit.get())
}

/// Units spent in the current declaration; `0` when disabled.
pub(crate) fn used() -> u64 {
    BUDGET.with(|b| b.limit.get().saturating_sub(b.remaining.get()))
}

/// The site that exhausted the current declaration's budget, if one has.
/// Always `None` while disabled.
pub(crate) fn exhausted_at() -> Option<&'static str> {
    BUDGET.with(|b| b.exhausted_at.get())
}

/// Charge `units` of work done at `site`.
///
/// Returns `true` while the budget holds (always, when disabled). Returns
/// `false` when this charge does not fit in what is left, or when the budget
/// was already spent: the budget then stays spent until [`begin_declaration`]
/// and the caller must stop searching. The charge that does not fit spends
/// the remainder, so [`used`] reads the full limit afterwards.
///
/// Also returns `false`, budget or not, once a deadline the caller installed
/// with `clean_kernel::tc::run_until` has passed (`clean-server` installs the
/// request's). The superposition loop makes no kernel call, so without this it
/// would never see the deadline. The deadline keeps its own latch in the
/// kernel, and `run_until` discards whatever the search returns after it, so
/// nothing here is counted or latched for it.
#[inline]
pub(crate) fn charge(site: &'static str, units: u64) -> bool {
    if clean_kernel::tc::poll_deadline() {
        return false;
    }
    BUDGET.with(|b| {
        if b.limit.get() == 0 {
            return true;
        }
        if b.exhausted_at.get().is_some() {
            return false;
        }
        let remaining = b.remaining.get();
        if units > remaining {
            b.remaining.set(0);
            b.exhausted_at.set(Some(site));
            return false;
        }
        b.remaining.set(remaining - units);
        true
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each test runs on its own thread so the thread-local state cannot leak
    /// between tests that share a harness thread.
    fn on_fresh_thread<F: FnOnce() + Send + 'static>(f: F) {
        std::thread::spawn(f)
            .join()
            .expect("work-budget test thread must not panic");
    }

    #[test]
    fn test_work_budget_disabled_by_default_counts_nothing() {
        on_fresh_thread(|| {
            assert_eq!(limit(), 0);
            for _ in 0..1_000 {
                assert!(charge("test", 1_000_000));
            }
            assert_eq!(used(), 0);
            assert_eq!(exhausted_at(), None);
        });
    }

    #[test]
    fn test_work_budget_charge_that_does_not_fit_exhausts_and_latches() {
        on_fresh_thread(|| {
            set_limit(10);
            assert!(charge("a", 4));
            assert!(charge("a", 6), "a charge that exactly fits succeeds");
            assert_eq!(used(), 10);
            assert_eq!(exhausted_at(), None, "exactly spent is not yet exhausted");
            assert!(!charge("b", 1), "the next unit does not fit");
            assert_eq!(exhausted_at(), Some("b"));
            assert!(!charge("c", 0), "the latch refuses even a free charge");
            assert_eq!(exhausted_at(), Some("b"), "the first site is kept");
            set_limit(0);
        });
    }

    #[test]
    fn test_work_budget_oversized_charge_spends_the_remainder() {
        on_fresh_thread(|| {
            set_limit(10);
            assert!(charge("a", 3));
            assert!(!charge("big", 50));
            assert_eq!(used(), 10, "a refused charge spends what was left");
            assert_eq!(exhausted_at(), Some("big"));
            set_limit(0);
        });
    }

    #[test]
    fn test_work_budget_begin_declaration_refills_and_clears_the_latch() {
        on_fresh_thread(|| {
            set_limit(2);
            assert!(!charge("a", 3));
            begin_declaration();
            assert_eq!(exhausted_at(), None);
            assert_eq!(used(), 0);
            assert!(charge("a", 2));
            set_limit(0);
        });
    }

    #[test]
    fn test_work_budget_charge_refuses_past_a_callers_deadline() {
        on_fresh_thread(|| {
            // Disabled budget: every charge is free until the deadline passes.
            let past = Some(std::time::Instant::now());
            let refused = clean_kernel::tc::run_until(past, || charge("superposition", 1));
            assert_eq!(
                refused, None,
                "the charge refused, and the search was interrupted"
            );
            assert_eq!(
                exhausted_at(),
                None,
                "the deadline latches in the kernel only"
            );
            assert_eq!(used(), 0);
            // A distant deadline changes nothing.
            let distant =
                std::time::Instant::now().checked_add(std::time::Duration::from_secs(3600));
            assert_eq!(
                clean_kernel::tc::run_until(distant, || charge("superposition", 1)),
                Some(true)
            );
            assert!(charge("superposition", 1), "no deadline is left installed");
        });
    }

    #[test]
    fn test_work_budget_is_thread_local() {
        on_fresh_thread(|| {
            set_limit(1);
            assert!(!charge("a", 2));
            std::thread::spawn(|| {
                assert_eq!(limit(), 0);
                assert_eq!(exhausted_at(), None);
            })
            .join()
            .expect("inner thread must not panic");
            assert_eq!(exhausted_at(), Some("a"));
            set_limit(0);
        });
    }
}
