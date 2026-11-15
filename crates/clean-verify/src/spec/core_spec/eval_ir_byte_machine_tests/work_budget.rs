// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel work meter on trust-ir's real gate-9 judgment.
//!
//! The judgment is trust-ir's gate-9 hang. trust-ir 2ce4067d presented a step
//! proof at the run-one type, `run 1 c = R` for the actual configuration `c`
//! of a fetched U64 `LShr` by 3, which leaves `run 1 c = step c` to kernel
//! conversion. Lazy delta then evaluates the step's REFERENCE semantics, where
//! `w >>> 3` is `ir_nat_div w 8` by repeated subtraction: one `Nat.sub` link
//! per iteration, and whnf-cache probes that compare equal but separately
//! built chains, as long as the chain. Before the kernel work meter those
//! comparisons spent no heartbeats, and trust-ir's 5,000,000-heartbeat
//! rechecker ran 3.5 hours at the full 64-bit word without stopping (trust-ir
//! 67b91383, which removed the presentation). The meter now bills walking past
//! each step's allowance, and that rechecker stops the full-width judgment with
//! `HeartbeatExceeded` (`docs/DECISIONS.md` `DR-KERNEL-WORK-METER-20261014`);
//! the refusal of the mechanism itself is pinned by
//! `growing_chain_probes_are_refused_by_a_budget_their_steps_fit` and its mutant
//! in `clean-kernel`.
//!
//! This file pins it on the real judgment at the 20-bit word `2^20 - 1`:
//! measured 2026-10-15 (debug, the rechecker's strict checker with 100,000
//! cache entries, no limit), 919,535 heartbeats of steps without the equality
//! charge and 1,095,099 with the walks past the steps' allowance billed. So a
//! budget of 1,000,000 heartbeats, which the steps fit, refuses it with the
//! meter and admits it under the mutant that drops the equality charge, and
//! the kernel's default 2,000,000 still admits it. The fixtures are the
//! judgment exactly as the rechecker replays it: the proof term and the
//! reconstructed claim, produced by trust-ir 409a9ed6 with 67b91383's
//! `one_step` change reverted (`Claim { shift: Logical, word: 2^20 - 1, answer:
//! word >> 3 }`) and written with `clean_kernel::flat::FlatBuilder`, one file
//! each, the root last. Tested, not proved.

use crate::spec::Specification;
use clean_kernel::flat::{reconstruct_expr, FlatDb};
use clean_kernel::{tc::DEFAULT_HEARTBEAT_LIMIT, work_meter, Expr, TypeChecker, TypeError};

const TERM: &[u8] = include_bytes!("../../../../tests/fixtures/work_meter/gate9_lshr_20.term.flat");
const CLAIM: &[u8] =
    include_bytes!("../../../../tests/fixtures/work_meter/gate9_lshr_20.claim.flat");

/// The root of a one-expression fixture: its last expression.
fn root(bytes: &[u8]) -> Expr {
    let db = FlatDb::from_bytes(bytes).expect("flat fixture");
    let last = u32::try_from(db.expr_count() - 1).expect("fixture index");
    reconstruct_expr(&db, last).expect("fixture root")
}

/// The environment trust-ir's shift rechecker replays against.
fn shift_spec() -> Specification {
    crate::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack()
        .expect("checked full64 shift vocabulary")
}

/// Check `term : claim` on a strict checker with the rechecker's cache limit
/// and `heartbeats` (the kernel's default when `None`).
fn check(
    spec: &Specification,
    term: &Expr,
    claim: &Expr,
    heartbeats: Option<u32>,
) -> Result<(), TypeError> {
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker.set_max_cache_entries(100_000);
    match heartbeats {
        Some(limit) => checker.set_heartbeat_limit(limit),
        None => assert_eq!(checker.heartbeat_limit(), DEFAULT_HEARTBEAT_LIMIT),
    }
    checker.check_type(term, claim)
}

/// Fits the judgment's steps (919,535) and not its billed walks (1,095,099).
const BUDGET: u32 = 1_000_000;

#[test]
fn gate9_judgment_is_refused_by_a_budget_its_steps_fit_and_not_under_the_mutant() {
    crate::test_utils::run_with_stack(|| {
        let spec = shift_spec();
        let (term, claim) = (root(TERM), root(CLAIM));
        let verdict = check(&spec, &term, &claim, Some(BUDGET));
        assert!(
            matches!(
                verdict,
                Err(TypeError::HeartbeatExceeded { limit: BUDGET, .. })
            ),
            "the walks past the steps' allowance must spend the budget, and say so: {verdict:?}"
        );

        // MUTANT: drop the equality charge (the kernel before the meter, where
        // a cache probe's key comparison spent nothing). The same judgment
        // under the same budget is admitted: the refusal above is the charge's
        // doing, and the claim itself is true.
        let mutant = work_meter::mutant::with_equality_charge_dropped(|| {
            check(&spec, &term, &claim, Some(BUDGET))
        });
        assert!(mutant.is_ok(), "MUTANT survives the guard: {mutant:?}");

        // The kernel's default budget still admits it: the meter moved this
        // judgment's heartbeats, not its verdict.
        let default = check(&spec, &term, &claim, None);
        assert!(default.is_ok(), "{default:?}");
    });
}
