// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trusted arithmetic proof tracking and generation.
//!
//! Tracks proofs that rely on arithmetic decision procedures (Fourier-Motzkin,
//! Omega test). Unlike sorry terms which indicate incomplete proofs, trustedArith
//! proofs indicate that a decision procedure verified the goal.

#[cfg(test)]
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(test)]
use std::sync::Mutex;

#[cfg(test)]
use clean_kernel::{Expr, ExprKind, Level, Name};

#[cfg(test)]
use super::super::{create_sorry_term, Goal, ProofState, TacticResult};

/// Global counter for trusted arithmetic proof generation.
/// Tracks how many trusted arithmetic proof terms were emitted successfully.
pub(crate) static ARITH_PROOF_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Lifetime counter for trusted arithmetic proof generation — monotonically increases,
/// never reset. Used by trusted_ratchet to get true cumulative count regardless of
/// test resets.
#[cfg(test)]
pub(crate) static ARITH_LIFETIME_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Tracks trustedArith provenance keys for runtime ratchet reporting.
#[cfg(test)]
static ARITH_LOCATIONS: Mutex<Option<HashMap<String, u64>>> = Mutex::new(None);

#[cfg(test)]
#[derive(Clone, Copy)]
enum TrustedArithSource<'a> {
    DirectCaller { file: &'a str, line: u32 },
    GoalCloseHelper { tactic: &'a str },
    TargetRewriteHelper { tactic: &'a str },
}

#[cfg(test)]
impl TrustedArithSource<'_> {
    fn location_key(&self) -> String {
        match self {
            Self::DirectCaller { file, line } => format!("{file}:{line}"),
            Self::GoalCloseHelper { tactic } => {
                format!("helper:close_with_trusted_arith:{tactic}")
            }
            Self::TargetRewriteHelper { tactic } => {
                format!("helper:replace_target_with_trusted_fallback:{tactic}")
            }
        }
    }

    fn record_proof_state_debt(self, state: &mut ProofState, count: u32) {
        match self {
            Self::DirectCaller { .. } => state.record_trusted_arith_direct(count),
            Self::GoalCloseHelper { .. } => state.record_trusted_arith_goal_close_helper(count),
            Self::TargetRewriteHelper { .. } => {
                state.record_trusted_arith_target_rewrite_helper(count)
            }
        }
    }
}

/// Reset the arithmetic proof counter to zero.
/// Call this at the start of tests to isolate arithmetic proof tracking.
///
/// REQUIRES: Called only during test setup
/// ENSURES: `arith_proof_count() == 0` after return
/// ENSURES: `arith_lifetime_count()` is unchanged (lifetime counter never resets)
pub fn reset_arith_counter() {
    ARITH_PROOF_COUNTER.store(0, Ordering::SeqCst);
}

/// Get the current arithmetic proof count.
///
/// ENSURES: Result >= 0 and reflects calls to `create_trusted_arith_term` since last reset
pub fn arith_proof_count() -> u64 {
    ARITH_PROOF_COUNTER.load(Ordering::SeqCst)
}

/// Get the lifetime arithmetic proof count (never reset).
///
/// Returns the total number of trusted arithmetic proofs generated since program start.
/// Unlike `arith_proof_count()`, this is not affected by `reset_arith_counter()`.
///
/// ENSURES: Result is monotonically non-decreasing across calls
/// ENSURES: Result >= `arith_proof_count()` (lifetime includes all resets)
#[cfg(test)]
pub fn arith_lifetime_count() -> u64 {
    ARITH_LIFETIME_COUNTER.load(Ordering::SeqCst)
}

/// Initialize trustedArith location tracking.
#[cfg(test)]
pub(crate) fn enable_arith_location_tracking() {
    if let Ok(mut guard) = ARITH_LOCATIONS.lock() {
        if guard.is_none() {
            *guard = Some(HashMap::new());
        }
    }
}

/// Record a trustedArith term at a specific provenance source.
#[cfg(test)]
fn record_trusted_arith_location(source: TrustedArithSource<'_>) {
    let location = source.location_key();

    if let Ok(mut guard) = ARITH_LOCATIONS.lock() {
        let map = guard.get_or_insert_with(HashMap::new);
        *map.entry(location).or_insert(0) += 1;
    }
}

#[track_caller]
#[cfg(test)]
fn record_direct_trusted_arith_location() {
    let caller = std::panic::Location::caller();
    record_trusted_arith_location(TrustedArithSource::DirectCaller {
        file: caller.file(),
        line: caller.line(),
    });
}

/// Get trustedArith caller locations and counts.
#[cfg(test)]
pub(crate) fn arith_locations() -> Option<HashMap<String, u64>> {
    ARITH_LOCATIONS.lock().ok().and_then(|guard| guard.clone())
}

#[cfg(test)]
const _: fn() = enable_arith_location_tracking;

#[cfg(test)]
const _: fn() -> Option<HashMap<String, u64>> = arith_locations;

#[cfg(test)]
fn increment_trusted_arith_counters() {
    ARITH_PROOF_COUNTER.fetch_add(1, Ordering::SeqCst);
    ARITH_LIFETIME_COUNTER.fetch_add(1, Ordering::SeqCst);
}

#[cfg(test)]
fn record_trusted_arith_success_for_source(source: TrustedArithSource<'_>) {
    record_trusted_arith_location(source);
    increment_trusted_arith_counters();
}

#[cfg(test)]
#[track_caller]
pub(crate) fn record_trusted_arith_success() {
    record_direct_trusted_arith_location();
    increment_trusted_arith_counters();
}

#[cfg(test)]
fn record_proof_state_trusted_arith_fallback(
    state: &mut ProofState,
    source: TrustedArithSource<'_>,
) {
    record_trusted_arith_success_for_source(source);
    source.record_proof_state_debt(state, 1);
}

#[cfg(test)]
pub(crate) fn record_target_rewrite_trusted_arith_fallback(state: &mut ProofState, tactic: &str) {
    record_proof_state_trusted_arith_fallback(
        state,
        TrustedArithSource::TargetRewriteHelper { tactic },
    );
}

#[cfg(test)]
pub(crate) fn make_trusted_arith_term_untracked(
    env: &clean_kernel::env::Environment,
    goal_ty: &Expr,
) -> Expr {
    let trusted_arith_name = Name::from_string("trustedArith");
    if env.get_const(&trusted_arith_name).is_some() {
        // Compute correct universe level: trustedArith.{u} : {α : Sort u} → α
        // If goal_ty is Sort(n), then goal_ty : Sort(n+1), so u = n+1
        // Otherwise goal_ty is a proposition (: Prop = Sort 0), so u = 0
        let level = match goal_ty.kind() {
            ExprKind::Sort(l) => Level::succ(l.clone()),
            _ => Level::zero(),
        };
        let trusted_arith_const = Expr::const_(trusted_arith_name, vec![level]);
        return Expr::app(trusted_arith_const, goal_ty.clone());
    }

    // If trustedArith doesn't exist, fall back to sorry.
    // This path should only be reached with bare Environment::default() (no init).
    create_sorry_term(env, goal_ty)
}

/// Create a trusted arithmetic proof term for the given goal type.
///
/// When the `trustedArith` axiom is present in the environment, constructs
/// `@trustedArith.{0} goal_ty` and increments the tracking counter. This
/// distinguishes arithmetic-verified proofs from incomplete (sorry) proofs.
///
/// If the `trustedArith` axiom is not present (e.g., in a bare Environment
/// without prelude), falls back to `create_sorry_term` for compatibility.
///
/// REQUIRES: `env` is a valid `Environment`
/// REQUIRES: `goal_ty` is a well-typed Lean expression representing the goal type
/// ENSURES: Returned expression has type `goal_ty` (assuming axiom soundness)
/// ENSURES: When `trustedArith` exists in `env`, `arith_proof_count()` and
///   `arith_lifetime_count()` each increase by 1
/// ENSURES: When `trustedArith` is absent, falls back to `create_sorry_term`
#[track_caller]
#[cfg(test)]
pub(crate) fn create_trusted_arith_term(
    env: &clean_kernel::env::Environment,
    goal_ty: &Expr,
) -> Expr {
    if env.get_const(&Name::from_string("trustedArith")).is_some() {
        record_trusted_arith_success();
    }
    make_trusted_arith_term_untracked(env, goal_ty)
}

/// Close goal with trustedArith fallback: logs a warning and tracks in ProofState.
/// Part of #2411.
///
/// REQUIRES: `state` has at least one open goal
/// REQUIRES: `goal` is a valid goal from `state`
/// REQUIRES: `tactic` is a non-empty string identifying the calling tactic
/// ENSURES: On `Ok(())`, `goal` is closed with a `trustedArith` (or sorry) proof term
/// ENSURES: `state.trusted_axiom_count` is incremented by 1
/// ENSURES: A `tracing::warn` diagnostic is emitted with `tactic` and `detail`
#[cfg(test)]
pub(crate) fn close_with_trusted_arith(
    state: &mut ProofState,
    goal: &Goal,
    tactic: &str,
    detail: &str,
) -> TacticResult {
    let target = state.metas.instantiate(&goal.target);
    let has_trusted_arith = state
        .env()
        .get_const(&Name::from_string("trustedArith"))
        .is_some();
    // Phase E.1 (#2422): structured diagnostic for trustedArith elimination audit
    let goal_head = goal.target.get_app_fn();
    tracing::warn!(
        tactic,
        detail,
        goal_head = %goal_head,
        "trustedArith fallback — proof reconstruction gap"
    );
    if has_trusted_arith {
        record_trusted_arith_success_for_source(TrustedArithSource::GoalCloseHelper { tactic });
    }
    let proof = make_trusted_arith_term_untracked(state.env(), &target);
    state.close_goal(goal, proof)?;
    if has_trusted_arith {
        TrustedArithSource::GoalCloseHelper { tactic }.record_proof_state_debt(state, 1);
    } else {
        state.record_sorry();
    }
    Ok(())
}
