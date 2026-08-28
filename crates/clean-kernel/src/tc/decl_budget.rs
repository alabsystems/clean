// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ambient, declaration-scoped cooperative budget.
//!
//! # Why this exists and why it is not the per-`TypeChecker` heartbeat
//!
//! [`TypeChecker::set_heartbeat_limit`](super::TypeChecker::set_heartbeat_limit)
//! bounds ONE type checker. A caller that elaborates a declaration builds many
//! type checkers — the tactic engine, instance resolution, `simp` matching and
//! the final `add_decl` each construct their own — and every one of them starts
//! at a fresh [`DEFAULT_HEARTBEAT_LIMIT`](super::DEFAULT_HEARTBEAT_LIMIT). The
//! per-checker budget therefore bounds each *step* and bounds the *declaration*
//! not at all: a declaration that keeps minting new checkers runs forever while
//! no individual heartbeat is ever exceeded. That is exactly how one `by grind`
//! declaration in `Mathlib/Logic/Basic.lean` held a whole-file `clean check`
//! measurement hostage for 40+ minutes with no output and no verdict.
//!
//! This module adds a second, *ambient* counter with declaration scope. It
//! lives in thread-local storage rather than on a `TypeChecker`, so every
//! checker constructed on the thread — including ones this crate's callers
//! never see — draws from the same pot. The owner of the declaration loop
//! (`clean check`) refills it once per declaration with
//! [`reset_declaration_budget`] and asks [`declaration_budget_exhausted`]
//! afterwards.
//!
//! # It is a budget, not a timer
//!
//! Nothing here interrupts, signals or kills anything: a synchronous Rust call
//! cannot be safely stopped from outside. The counter is decremented at the
//! same cooperative tick sites the heartbeat already uses (`infer_type`,
//! `whnf_impl`, `is_def_eq_impl`) **plus one the heartbeat never reached**:
//! `cert::infer_core::infer_type_with_cert_inner`, the retained-certificate
//! inference the tactic engine runs on every proof term. That omission is a
//! known heartbeat parity gap; leaving it open here would have been worse than
//! cosmetic, because a spent budget makes `whnf` return unreduced terms, the
//! tactic layers retry, and the cert recursion — having nothing to check —
//! spins. Measured: `--decl-budget 1` on a one-line `def` ran at 98% CPU
//! instead of reporting `diverged`. So exhaustion is observed only where the
//! code agreed to look, and the cert path now agrees. Consequently the bound is *deterministic* —
//! the same input spends the same ticks on any machine at any load — and it is
//! only as tight as the tick sites are dense. A pathology that spends its time
//! between ticks (for example, one whose cost is per-tick allocation SIZE
//! rather than tick COUNT — see
//! `docs/issues/2026-08-21-cert-clone-exponential-tree-mirror.md`) is NOT
//! bounded by this mechanism, and this module does not claim otherwise.
//!
//! # Disabled by default, everywhere
//!
//! A limit of `0` means unlimited, and `0` is the initial value on every
//! thread. Until a caller sets a limit, every entry point here is a single
//! thread-local load and a compare — and, crucially, no verdict anywhere can
//! move. `clean check` is the only production caller that turns it on.
//!
//! # Exhaustion is information, not a verdict
//!
//! When the budget runs out, the honest reading is "this declaration did not
//! finish" — neither "it was proved" nor "it failed to prove". The kernel
//! surfaces that as its own [`TypeError::DeclarationBudgetExhausted`]
//! variant, distinct from `HeartbeatExceeded`, so a caller can never round it
//! up into a pass or down into a refutation.
//!
//! [`TypeError::DeclarationBudgetExhausted`]: super::TypeError::DeclarationBudgetExhausted

use std::cell::Cell;

/// Thread-local ambient budget state.
///
/// Both fields live in one `thread_local!` entry so a tick pays for a single
/// TLS lookup rather than two.
struct DeclBudget {
    /// Ticks granted per declaration. `0` disables the mechanism entirely.
    limit: Cell<u64>,
    /// Ticks still available in the current declaration.
    remaining: Cell<u64>,
}

thread_local! {
    static BUDGET: DeclBudget = const {
        DeclBudget {
            limit: Cell::new(0),
            remaining: Cell::new(0),
        }
    };
}

/// Set the ambient per-declaration budget for the current thread and start a
/// fresh declaration.
///
/// `limit == 0` disables the mechanism (unlimited), which is the default state
/// of every thread. The budget is thread-local: setting it on one thread has
/// no effect on any other, so a caller that hands work to a worker thread must
/// set it *inside* that thread.
///
/// # Contract
///
/// ENSURES: `declaration_budget_limit() == limit`
/// ENSURES: `declaration_budget_remaining() == limit`
/// ENSURES: `declaration_budget_exhausted() == false` when `limit != 0`
pub fn set_declaration_budget(limit: u64) {
    BUDGET.with(|b| {
        b.limit.set(limit);
        b.remaining.set(limit);
    });
}

/// Refill the ambient budget to its configured limit.
///
/// Call this immediately before each declaration. No-op when the mechanism is
/// disabled.
pub fn reset_declaration_budget() {
    BUDGET.with(|b| b.remaining.set(b.limit.get()));
}

/// Disable the ambient budget on this thread (equivalent to
/// `set_declaration_budget(0)`).
pub fn clear_declaration_budget() {
    set_declaration_budget(0);
}

/// The configured per-declaration limit; `0` when disabled.
#[must_use]
pub fn declaration_budget_limit() -> u64 {
    BUDGET.with(|b| b.limit.get())
}

/// Ticks still available in the current declaration; `0` when disabled.
#[must_use]
pub fn declaration_budget_remaining() -> u64 {
    BUDGET.with(|b| b.remaining.get())
}

/// Ticks spent since the last reset; `0` when disabled.
///
/// This is the measurement entry point: run a corpus with a deliberately
/// enormous limit and read this after each declaration to learn what a real
/// budget would have to be.
#[must_use]
pub fn declaration_budget_used() -> u64 {
    BUDGET.with(|b| b.limit.get().saturating_sub(b.remaining.get()))
}

/// Has the current declaration spent its whole ambient budget?
///
/// Always `false` when the mechanism is disabled. Once true, it stays true
/// until [`reset_declaration_budget`] or [`set_declaration_budget`] is called
/// — the latch is the point: a caller that checks only after the declaration
/// finishes still learns that the work was cut short, even if some
/// intermediate layer swallowed the error.
#[must_use]
pub fn declaration_budget_exhausted() -> bool {
    BUDGET.with(|b| b.limit.get() != 0 && b.remaining.get() == 0)
}

/// Run `f` with the ambient budget SUSPENDED, then restore it exactly.
///
/// For work that is not the declaration's own: environment seeding, prelude
/// registration, and anything else whose cost is fixed setup rather than the
/// proof search under measurement. `clean check` already excludes
/// `Environment::with_prelude()` by arming the budget after it; some seeding is
/// LAZY, though, and first runs inside the first declaration
/// (`clean_elab`'s homogeneous→heterogeneous operator bridges are seeded once
/// per declaration and register three kernel-checked definitions the first
/// time). Charging that to whichever declaration happened to be first is both
/// unfair and confusing: a tight budget made the seed's own `add_decl` fail
/// with `DeclarationBudgetExhausted`, which reads as "the prelude is broken".
///
/// The suspended region is UNBOUNDED, so it is only appropriate where the work
/// is bounded by construction — a fixed, repo-authored set of declarations —
/// never around anything user input can grow.
///
/// Restores both the limit and the remaining count, so a suspension cannot be
/// used to refill a declaration that has already spent its fuel.
pub fn with_declaration_budget_suspended<T>(f: impl FnOnce() -> T) -> T {
    let saved = BUDGET.with(|b| (b.limit.get(), b.remaining.get()));
    BUDGET.with(|b| b.limit.set(0));
    let out = f();
    BUDGET.with(|b| {
        b.limit.set(saved.0);
        b.remaining.set(saved.1);
    });
    out
}

/// Spend one ambient tick.
///
/// Returns `false` if the budget is exhausted (now or already), `true`
/// otherwise — including when the mechanism is disabled, in which case this is
/// one thread-local load and a compare.
#[inline]
pub(super) fn consume_declaration_budget() -> bool {
    BUDGET.with(|b| {
        if b.limit.get() == 0 {
            return true;
        }
        let remaining = b.remaining.get();
        if remaining == 0 {
            return false;
        }
        b.remaining.set(remaining - 1);
        true
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each test runs on its own thread so the thread-local state cannot leak
    /// between them (cargo's test harness reuses threads within a test only).
    fn on_fresh_thread<F: FnOnce() + Send + 'static>(f: F) {
        std::thread::spawn(f)
            .join()
            .expect("budget test thread must not panic");
    }

    #[test]
    fn test_declaration_budget_disabled_by_default() {
        on_fresh_thread(|| {
            assert_eq!(declaration_budget_limit(), 0);
            assert!(!declaration_budget_exhausted());
            // Ticking a disabled budget never exhausts and never counts.
            for _ in 0..10_000 {
                assert!(consume_declaration_budget());
            }
            assert!(!declaration_budget_exhausted());
            assert_eq!(declaration_budget_used(), 0);
        });
    }

    #[test]
    fn test_declaration_budget_exhausts_after_limit_ticks() {
        on_fresh_thread(|| {
            set_declaration_budget(3);
            assert!(consume_declaration_budget());
            assert!(consume_declaration_budget());
            assert!(consume_declaration_budget());
            // Exactly `limit` ticks are granted; the latch trips on the next.
            assert!(declaration_budget_exhausted());
            assert!(!consume_declaration_budget());
            assert!(declaration_budget_exhausted());
            assert_eq!(declaration_budget_used(), 3);
        });
    }

    #[test]
    fn test_declaration_budget_reset_refills() {
        on_fresh_thread(|| {
            set_declaration_budget(2);
            assert!(consume_declaration_budget());
            assert!(consume_declaration_budget());
            assert!(declaration_budget_exhausted());
            reset_declaration_budget();
            assert!(!declaration_budget_exhausted());
            assert_eq!(declaration_budget_remaining(), 2);
            assert_eq!(declaration_budget_used(), 0);
        });
    }

    #[test]
    fn test_declaration_budget_is_thread_local() {
        on_fresh_thread(|| {
            set_declaration_budget(1);
            assert!(consume_declaration_budget());
            assert!(declaration_budget_exhausted());
            // A different thread must see the untouched default.
            std::thread::spawn(|| {
                assert_eq!(declaration_budget_limit(), 0);
                assert!(!declaration_budget_exhausted());
            })
            .join()
            .expect("inner thread must not panic");
            // …and this thread's latch must survive the other thread's run.
            assert!(declaration_budget_exhausted());
        });
    }

    #[test]
    fn test_declaration_budget_suspension_restores_exactly() {
        on_fresh_thread(|| {
            set_declaration_budget(10);
            assert!(consume_declaration_budget());
            assert!(consume_declaration_budget());
            assert_eq!(declaration_budget_remaining(), 8);

            let out = with_declaration_budget_suspended(|| {
                // Unbounded inside: a thousand ticks cost nothing…
                for _ in 0..1_000 {
                    assert!(consume_declaration_budget());
                }
                assert!(!declaration_budget_exhausted());
                42
            });
            assert_eq!(out, 42);
            // …and the declaration's own fuel is exactly where it was.
            assert_eq!(declaration_budget_limit(), 10);
            assert_eq!(declaration_budget_remaining(), 8);
            clear_declaration_budget();
        });
    }

    /// A suspension must not be a back door for refilling a spent budget.
    #[test]
    fn test_declaration_budget_suspension_does_not_refill_a_spent_budget() {
        on_fresh_thread(|| {
            set_declaration_budget(1);
            assert!(consume_declaration_budget());
            assert!(declaration_budget_exhausted());
            with_declaration_budget_suspended(|| {
                assert!(consume_declaration_budget());
            });
            assert!(
                declaration_budget_exhausted(),
                "the declaration was already out of fuel before the suspension \
                 and must still be out of fuel after it"
            );
            clear_declaration_budget();
        });
    }

    #[test]
    fn test_declaration_budget_clear_disables() {
        on_fresh_thread(|| {
            set_declaration_budget(1);
            assert!(consume_declaration_budget());
            assert!(declaration_budget_exhausted());
            clear_declaration_budget();
            assert!(!declaration_budget_exhausted());
            assert!(consume_declaration_budget());
        });
    }
}
