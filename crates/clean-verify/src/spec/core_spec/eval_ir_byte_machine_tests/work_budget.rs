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
//! charge and 1,095,099 with the walks past the steps' allowance billed, about
//! 175,000 apart. Wider cached hashes for closed expressions then removed the
//! long colliding probes: measured 2026-11-08 the two costs were 919,539 and
//! 919,535, and on 2026-11-17 (the merge of fix/implicit-positional-arguments
//! with main) a bisection put the smallest admitting budgets at 919,421 with
//! the meter and 919,418 under the mutant. A fixed budget between two costs
//! three heartbeats apart flipped with any unrelated change to the checker's
//! step count, so the guard now finds its budget on the judgment itself
//! (2026-11-18): it bisects the smallest budget that admits the judgment under
//! the mutant that drops the equality charge, and requires the meter to refuse
//! that same budget by `HeartbeatExceeded`. That still fails the day the
//! charge stops billing this judgment, and no longer fails when the steps
//! alone grow or shrink. What it cannot show is a WIDE margin: under the
//! current hashing this judgment's billed walking is a few heartbeats. The
//! mechanism at scale is pinned by the kernel's own
//! `growing_chain_probes_are_refused_by_a_budget_their_steps_fit` and its
//! mutant (`clean-kernel`, `tc/tests/work_billing.rs`); a real judgment with a
//! wide margin under the current hashing needs a new fixture. The fixtures are the
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

/// The smallest budget that admits the judgment under `admits`, by bisection
/// over `(0, DEFAULT_HEARTBEAT_LIMIT]` (a check's cost does not depend on its
/// limit, so admission is monotone in the budget). Budget 0 is never tried: it
/// disables the limit.
fn smallest_admitting_budget(admits: impl Fn(u32) -> bool) -> u32 {
    let (mut refused, mut admitted) = (0_u32, DEFAULT_HEARTBEAT_LIMIT);
    assert!(
        admits(admitted),
        "the kernel's default budget must admit the judgment"
    );
    while admitted - refused > 1 {
        let mid = refused + (admitted - refused) / 2;
        if admits(mid) {
            admitted = mid;
        } else {
            refused = mid;
        }
    }
    admitted
}

#[test]
fn gate9_judgment_is_refused_by_a_budget_its_steps_fit_and_not_under_the_mutant() {
    crate::test_utils::run_with_stack(|| {
        let spec = shift_spec();
        let (term, claim) = (root(TERM), root(CLAIM));

        // MUTANT: drop the equality charge (the kernel before the meter, where
        // a cache probe's key comparison spent nothing). The smallest budget
        // it admits the judgment at is what the judgment's steps cost.
        let steps = work_meter::mutant::with_equality_charge_dropped(|| {
            smallest_admitting_budget(|budget| match check(&spec, &term, &claim, Some(budget)) {
                Ok(()) => true,
                Err(TypeError::HeartbeatExceeded { .. }) => false,
                Err(other) => panic!("the claim is true; only the budget may refuse: {other:?}"),
            })
        });

        // With the meter, the walks past the steps' allowance spend that
        // budget, and the refusal says so: the refusal is the charge's doing.
        let verdict = check(&spec, &term, &claim, Some(steps));
        assert!(
            matches!(
                verdict,
                Err(TypeError::HeartbeatExceeded { limit, .. }) if limit == steps
            ),
            "the walks past the steps' allowance must spend the {steps}-heartbeat budget \
             the steps fit, and say so: {verdict:?}"
        );

        // The kernel's default budget still admits it: the meter moved this
        // judgment's heartbeats, not its verdict.
        let default = check(&spec, &term, &claim, None);
        assert!(default.is_ok(), "{default:?}");

        // The original guard's million-heartbeat budget is now a positive
        // control: wider closed keys avoid its formerly expensive collisions.
        let original_budget = check(&spec, &term, &claim, Some(1_000_000));
        assert!(original_budget.is_ok(), "{original_budget:?}");
    });
}
