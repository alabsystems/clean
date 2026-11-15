// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel checks of a checked axiom-stub upgrade batch, run concurrently.
//!
//! [`Environment::upgrade_axiom_stubs_checked`] kernel-checks every
//! `.olean.private` value over its stub. On a Mathlib import header that is
//! nearly the whole import: measured 2026-09-30 (release, `clean check` of
//! Mathlib `Order/Basic`'s import header, macOS `sample`), 74% of the import's
//! time was these checks, 59,121 of them theorem proofs (58 s of 62 s).
//!
//! Each check reads the environment and nothing else, so the checks of one
//! batch can run on many threads against the environment as it stands before
//! the batch. [`speculative_checks`] returns the checked verdict per record.
//! The caller installs the records in batch
//! order exactly as before. A speculative accept still needs a value-free
//! stub; a completed refusal additionally needs the entire environment unchanged.
//!
//! # Why a speculative accept is the same check
//!
//! Between the speculative check of record `k` and its installation, the only
//! changes to the environment are earlier records of this batch replacing
//! THEIR stubs: each replacement keeps the constant's type (step 3 refuses a
//! record whose type is not the stub's) and adds a value. So record `k` was
//! checked against a δ-sub-environment of the one it is installed into —
//! every constant it could see is there with the same type, some now with a
//! value too — and a typing derivation in the smaller environment is one in
//! the larger. Record `k`'s own stub cannot have changed: an earlier record of
//! the same name leaves a value behind, and the pre-check then skips `k`, as
//! the sequential loop did.
//!
//! A completed speculative REFUSAL is reused only before the first installation,
//! while the entire environment is unchanged. Once any sibling gains a value,
//! every refusal is checked again in order: hidden/transitive dependencies need
//! no approximation. Resource-limited checks are never reused as refusals.
//!
//! # The ambient declaration budget
//!
//! The ambient budget (`tc::decl_budget`) is thread-local. Each worker check
//! runs with the calling thread's limit and the calling thread's remaining
//! ticks, and reports what it spent. When the budget is armed and the checks
//! together spent at least what remained, every speculative verdict is
//! discarded and the batch runs sequentially from the untouched budget — so a
//! budget-limited verdict is only ever the sequential one. Otherwise the
//! calling thread is charged the total, as if it had run the checks itself.

use super::types::{ConstantInfo, EnvError};
use super::Environment;

#[path = "stub_upgrade_pool.rs"]
mod worker_pool;
use worker_pool::pool;

/// Below this many records a batch is checked in order on the calling thread.
pub(super) const MIN_PARALLEL_BATCH: usize = 4;

/// The outcome of one record of a checked stub-upgrade batch.
pub(crate) enum StubVerdict {
    /// The silent no-op lane: a value-bearing resident, or a record without a
    /// value.
    Skip,
    /// Refused fail-closed; the stub stays.
    Refuse(EnvError),
    /// Passed steps 1-4; install the record.
    Install,
}

#[derive(Default)]
pub(super) struct SpeculativeBatch {
    /// A completed refusal is reusable only in the exact unchanged environment.
    pub verdicts: Vec<SpeculativeVerdict>,
    pub checks: usize,
}

/// Keep successful batches compact; only reusable refusals allocate a diagnostic.
pub(super) enum SpeculativeVerdict {
    Recheck,
    Install,
    Refuse(Box<EnvError>),
}

#[derive(Debug, Default)]
#[cfg_attr(not(test), allow(dead_code))]
pub(super) struct StubUpgradeWork {
    pub speculative_checks: usize,
    pub sequential_checks: usize,
    pub reused_refusals: usize,
}

/// A resource refusal from a nested checker need not exhaust the caller's
/// heartbeat. Reuse only explicit semantic errors, and only if this checker
/// also finished with fuel remaining. New error variants default to rechecking.
pub(super) fn completed_type_refusal(
    tc: &crate::tc::TypeChecker<'_>,
    error: &crate::tc::TypeError,
) -> bool {
    use crate::tc::TypeError;
    matches!(
        error,
        TypeError::UnboundVariable(_)
            | TypeError::UnknownFVar(_)
            | TypeError::UnknownConst(_)
            | TypeError::NotAFunction { .. }
            | TypeError::TypeMismatch { .. }
            | TypeError::ExpectedSort { .. }
            | TypeError::InvalidProjNotStruct(_)
            | TypeError::InvalidProjNotUniqueConstructor(_)
            | TypeError::InvalidProjIndexOutOfBounds(_, _)
            | TypeError::InvalidProjWrongArgCount { .. }
            | TypeError::UnknownInductive(_)
            | TypeError::InvalidProjFromProp { .. }
            | TypeError::ModeRequired { .. }
            | TypeError::LevelCountMismatch { .. }
            | TypeError::UndefinedLevelParam { .. }
            | TypeError::UnsafeDeclaration { .. }
            | TypeError::PartialDeclaration { .. }
            | TypeError::LevelSharingDependent { .. }
    ) && !tc.heartbeat_spent()
}

/// Per-record checked outcomes against the initial environment. A refusal is
/// marked reusable only for a completed check without ambient bounds or a
/// lazy source. An empty result leaves every decision to the original loop.
pub(super) fn speculative_checks(
    env: &Environment,
    constants: &[ConstantInfo],
    reuse_refusals: bool,
) -> SpeculativeBatch {
    use rayon::prelude::*;
    if constants.len() < MIN_PARALLEL_BATCH {
        return SpeculativeBatch::default();
    }
    let Some(pool) = pool() else {
        return SpeculativeBatch::default();
    };
    let (limit, remaining) = crate::tc::declaration_budget_state();
    let reuse_refusals = reuse_refusals
        && limit == 0
        && !crate::tc::deadline_is_armed()
        && !env.has_constant_source();
    let checked: Vec<(SpeculativeVerdict, u64)> = pool.install(|| {
        constants
            .par_iter()
            .map(|ci| {
                crate::tc::restore_declaration_budget_state(limit, remaining);
                let verdict = env.stub_upgrade_check(ci, reuse_refusals);
                // Keep the old small result when a refusal cannot be reused;
                // its diagnostic will be produced by the sequential check.
                let verdict = match verdict {
                    (StubVerdict::Install, _) => SpeculativeVerdict::Install,
                    (StubVerdict::Refuse(error), true) => {
                        SpeculativeVerdict::Refuse(Box::new(error))
                    }
                    _ => SpeculativeVerdict::Recheck,
                };
                let spent = remaining.saturating_sub(crate::tc::declaration_budget_remaining());
                crate::tc::restore_declaration_budget_state(0, 0);
                (verdict, spent)
            })
            .collect()
    });
    if limit != 0 {
        let spent = checked
            .iter()
            .fold(0u64, |total, (_, spent)| total.saturating_add(*spent));
        if spent >= remaining {
            // The sequential run might have exhausted the budget part-way:
            // discard everything and let it decide, from the untouched budget.
            return SpeculativeBatch {
                verdicts: Vec::new(),
                checks: constants.len(),
            };
        }
        crate::tc::restore_declaration_budget_state(limit, remaining - spent);
    }
    SpeculativeBatch {
        verdicts: checked.into_iter().map(|(verdict, _)| verdict).collect(),
        checks: constants.len(),
    }
}
