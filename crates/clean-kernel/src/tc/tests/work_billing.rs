// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A checker bills itself, in heartbeats, for the structural walks its own
//! operations run (`crate::work_meter`, `tc/work_account.rs`).
//!
//! The defect these pin (found by trust-ir's gate 9, trust-ir 67b91383): a
//! whnf-cache HIT returned without a tick, so the key comparison behind it was
//! free however long the key was. Before the meter, the second `whnf` below
//! cost zero heartbeats. Each tick now pays for `UNITS_PER_HEARTBEAT` units of
//! walking; only walking past that is billed.

use super::*;
use crate::env::Declaration;
use crate::work_meter::{self, UNITS_PER_HEARTBEAT};

/// `T : Type`, `f : T → T`, `x : T`: every `f (f (... x))` is stuck.
fn stuck_env() -> Environment {
    let mut env = Environment::new();
    for (name, type_) in [
        ("T", Expr::type_()),
        ("f", Expr::arrow(constant("T"), constant("T"))),
        ("x", constant("T")),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .expect("axiom fixture");
    }
    env
}

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `f` applied `links` times to `x`, every node a fresh allocation.
fn chain(links: usize) -> Expr {
    let mut term = constant("x");
    for _ in 0..links {
        term = Expr::app(constant("f"), term);
    }
    term
}

const LINKS: usize = 20_000;
const LIMIT: u32 = 1_000_000;

/// Heartbeats one `whnf` of a fresh, equal, already-cached chain costs.
fn cache_hit_cost(tc: &TypeChecker<'_>) -> u32 {
    let first = chain(LINKS);
    assert_eq!(tc.whnf(&first), first, "a stuck chain is its own whnf");
    let before = tc.heartbeat_remaining();
    let second = chain(LINKS);
    assert_eq!(tc.whnf(&second), second);
    before - tc.heartbeat_remaining()
}

#[test]
fn whnf_cache_hit_bills_its_key_comparison() {
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(LIMIT);
    let cost = cache_hit_cost(&tc);
    // The hit's walk enters 2 * LINKS + 1 node pairs (each link's App and `f`,
    // then `x`); the probe is one more unit. The hit takes no tick, so only
    // the allowance the cold whnf's ticks left over (at most two heartbeats'
    // worth) covers any of it.
    let walked = (2 * LINKS as u64 + 1) / UNITS_PER_HEARTBEAT;
    assert!(
        u64::from(cost) + 2 >= walked,
        "a cache hit that walked {} pairs cost {cost} heartbeats",
        2 * LINKS + 1
    );
    assert!(u64::from(cost) <= walked + 2, "cost {cost} over {walked}");
}

#[test]
fn whnf_cache_hit_mutant_without_the_equality_charge_is_free() {
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(LIMIT);
    let cost = work_meter::mutant::with_equality_charge_dropped(|| cache_hit_cost(&tc));
    // MUTANT: the pre-meter kernel. The billing test above refuses it.
    assert_eq!(cost, 0, "without the equality charge the hit is free");
}

#[test]
fn a_spent_budget_stops_cache_hits_at_the_next_heartbeat_check() {
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    let walked = u32::try_from((2 * LINKS as u64 + 1) / UNITS_PER_HEARTBEAT).unwrap();
    // Enough for the first (cold) whnf, not for the hit's walk on top.
    tc.set_heartbeat_limit(walked / 2);
    let first = chain(LINKS);
    let _ = tc.whnf(&first);
    let _ = tc.whnf(&chain(LINKS));
    assert!(tc.heartbeat_spent(), "the hit's walk spent the budget");
    let refused = tc.infer_type(&chain(3));
    assert!(
        matches!(refused, Err(TypeError::HeartbeatExceeded { .. })),
        "a spent budget is refused, never accepted: {refused:?}"
    );
}

#[test]
fn work_on_the_thread_between_operations_is_not_billed() {
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(LIMIT);
    let _ = tc.whnf(&chain(10));
    let before = tc.heartbeat_remaining();
    // Not this checker's work: a long comparison outside its operations, and
    // another checker's whole operation.
    assert!(chain(LINKS) == chain(LINKS));
    let other = TypeChecker::new(&env);
    let _ = other.whnf(&chain(LINKS));
    let _ = other.whnf(&chain(LINKS));
    let _ = tc.whnf(&chain(10));
    assert!(
        before - tc.heartbeat_remaining() <= 2,
        "foreign work was billed: {} heartbeats",
        before - tc.heartbeat_remaining()
    );
}

#[test]
fn unlimited_checker_still_answers_identically() {
    // The meter moves budget counters only: the same questions get the same
    // answers with no limit, with a large limit, and under the mutant.
    let env = stuck_env();
    let answers = |limit: u32| {
        let mut tc = TypeChecker::new(&env);
        tc.set_heartbeat_limit(limit);
        let a = chain(LINKS);
        let b = chain(LINKS);
        (
            tc.whnf(&a) == a,
            tc.is_def_eq(&a, &b),
            tc.is_def_eq(&a, &chain(LINKS - 1)),
            // `TypeError` has no `PartialEq`: compare the verdict's shape.
            tc.infer_type(&b)
                .map(|ty| ty == constant("T"))
                .map_err(|error| format!("{error:?}")),
        )
    };
    let unlimited = answers(0);
    assert_eq!(unlimited, (true, true, false, Ok(true)));
    assert_eq!(answers(LIMIT), unlimited);
    assert_eq!(
        work_meter::mutant::with_equality_charge_dropped(|| answers(LIMIT)),
        unlimited
    );
}

#[test]
fn every_public_operation_ticks_inside_a_metered_scope() {
    use crate::tc::work_account::UNSCOPED_TICKS;
    let env = stuck_env();
    let tc = TypeChecker::new(&env);
    UNSCOPED_TICKS.with(|count| count.set(0));
    let a = chain(50);
    let b = chain(50);
    let _ = tc.whnf(&a);
    let _ = tc.whnf_with_transparency(&a, TransparencyMode::All);
    let _ = tc.is_def_eq(&a, &b);
    let _ = tc.is_le(&a, &b);
    let _ = tc.infer_type(&a);
    let _ = tc.infer_type_full(&a);
    let _ = tc.infer_sort(&constant("T"));
    let _ = tc.check_type(&a, &constant("T"));
    let _ = tc.check_type(&a, &Expr::prop());
    let _ = tc.infer_type_with_cert(&a);
    let _ = tc.infer_type_with_cert_full(&a);
    let _ = tc.try_reduce_native(&a);
    assert_eq!(
        UNSCOPED_TICKS.with(Cell::get),
        0,
        "a heartbeat site was reached outside every metered scope"
    );
}

#[test]
fn nested_checker_work_is_billed_to_the_inner_checker_once() {
    // Ticks already work this way: an inner checker's steps draw the inner
    // counter and the ambient pot, never the enclosing checker's counter. A
    // walk the inner checker ran is billed the same way, once.
    let env = stuck_env();
    let mut outer = TypeChecker::new(&env);
    outer.set_heartbeat_limit(LIMIT);
    let mut inner = TypeChecker::new(&env);
    inner.set_heartbeat_limit(LIMIT);
    let first = chain(LINKS);
    let second = chain(LINKS);
    let _ = inner.whnf(&first);
    let (outer_before, inner_before) = (outer.heartbeat_remaining(), inner.heartbeat_remaining());
    set_declaration_budget(u64::from(LIMIT));
    let reduced = {
        // An operation of `outer` that runs `inner`'s cache hit, and nothing
        // else (the answer is compared after the scope closes, since that
        // comparison is a walk of its own).
        let _scope = outer.metered_scope();
        let reduced = inner.whnf(&second);
        outer.settle_kernel_work();
        reduced
    };
    assert!(reduced == second, "a stuck chain is its own whnf");
    let used = declaration_budget_used();
    clear_declaration_budget();
    let inner_cost = u64::from(inner_before - inner.heartbeat_remaining());
    let outer_cost = u64::from(outer_before - outer.heartbeat_remaining());
    let walked = (2 * LINKS as u64 + 1) / UNITS_PER_HEARTBEAT;
    assert!(
        inner_cost + 2 >= walked,
        "inner billed {inner_cost} of {walked}"
    );
    assert!(
        outer_cost <= 1,
        "the enclosing checker paid {outer_cost} for nested work"
    );
    // The ambient pot was drawn by exactly what the two counters drew: the
    // walk once, not once per enclosing checker.
    assert_eq!(used, inner_cost + outer_cost);
}

#[test]
fn an_operations_own_walk_is_billed_to_it_inside_the_same_window() {
    // CONTROL for the test above: the deduction removes only what a nested
    // checker billed. A walk the enclosing operation runs itself (here a bare
    // comparison inside its scope) is its own work, and it pays, so the
    // outer counter staying whole above is the deduction, not a window that
    // never bills.
    let env = stuck_env();
    let mut outer = TypeChecker::new(&env);
    outer.set_heartbeat_limit(LIMIT);
    let walked = (2 * LINKS as u64 + 1) / UNITS_PER_HEARTBEAT;
    let (left, right) = (chain(LINKS), chain(LINKS));
    let before = outer.heartbeat_remaining();
    {
        let _scope = outer.metered_scope();
        assert!(left == right);
        outer.settle_kernel_work();
    }
    let cost = u64::from(before - outer.heartbeat_remaining());
    assert!(cost >= walked, "own walk billed {cost} of {walked}");
}

#[test]
fn walks_inside_the_steps_allowance_cost_only_the_steps() {
    // Inferring `f (f x)` ticks per node and walks a handful of units (folds,
    // cache probes), inside its ticks' allowance. Such a check spends exactly
    // the heartbeats it spent before the meter: one per step.
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(LIMIT);
    let _ = work_meter::stats::take();
    let before = tc.heartbeat_remaining();
    for _ in 0..1_000 {
        assert!(tc.infer_type(&chain(2)).is_ok());
    }
    let stats = work_meter::stats::take();
    let units = stats.equality_visits + stats.fold_nodes + stats.equiv_nodes + stats.probes;
    assert!(units >= 1_000, "the walks ran: {stats:?}");
    assert_eq!(stats.work_heartbeats, 0, "nothing past the allowance");
    assert_eq!(
        u64::from(before - tc.heartbeat_remaining()),
        stats.step_ticks,
        "every heartbeat spent was a step"
    );
}

#[test]
fn every_heartbeat_spent_is_a_step_or_billed_walking() {
    // The accounting identity, on comparisons whose walks DO exceed their
    // steps' allowance (each compares two separately built 2,000-link chains).
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(LIMIT);
    let _ = work_meter::stats::take();
    let before = tc.heartbeat_remaining();
    for _ in 0..200 {
        assert!(tc.is_def_eq(&chain(2_000), &chain(2_000)));
    }
    let stats = work_meter::stats::take();
    assert!(
        stats.work_heartbeats > 0,
        "these walks exceed the allowance: {stats:?}"
    );
    assert_eq!(
        u64::from(before - tc.heartbeat_remaining()),
        stats.step_ticks + stats.work_heartbeats
    );
}

#[test]
fn a_budget_bounds_the_walking_it_admits() {
    // A budget of B heartbeats admits at most B * UNITS_PER_HEARTBEAT units:
    // every unit is covered by a tick's allowance or billed as a heartbeat.
    // Repeated cache hits of a long chain take no tick at all, so before the
    // meter this loop never ended.
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    let budget: u32 = 10_000;
    tc.set_heartbeat_limit(budget);
    let _ = tc.whnf(&chain(LINKS));
    let _ = work_meter::stats::take();
    let mut hits = 0u64;
    while !tc.heartbeat_spent() {
        let _ = tc.whnf(&chain(LINKS));
        hits += 1;
        assert!(hits <= 1_000, "the budget never stopped the walks");
    }
    let units = work_meter::stats::take().equality_visits;
    // The walk that spent the budget ran to its end before it was billed.
    let one_walk = 2 * LINKS as u64 + 1;
    assert!(
        units <= u64::from(budget) * UNITS_PER_HEARTBEAT + one_walk,
        "{units} units walked under {budget} heartbeats"
    );
}

#[test]
fn a_reset_budget_starts_without_banked_allowance() {
    // Steps bank allowance; a long walk right after them is paid from the
    // bank. `reset_heartbeat` (and `set_heartbeat_limit`) clear the bank, so
    // allowance earned under one budget never pays for walks under the next.
    let env = stuck_env();
    let walked = (2 * LINKS as u64 + 1) / UNITS_PER_HEARTBEAT;
    let hit_cost = |reset: bool| {
        let mut tc = TypeChecker::new(&env);
        tc.set_heartbeat_limit(LIMIT);
        let _ = tc.whnf(&chain(LINKS));
        for _ in 0..2_000 {
            let _ = tc.infer_type(&chain(1));
        }
        if reset {
            tc.reset_heartbeat();
        }
        let before = tc.heartbeat_remaining();
        let _ = tc.whnf(&chain(LINKS));
        u64::from(before - tc.heartbeat_remaining())
    };
    // CONTROL: without the reset, the 2,000 steps' allowance pays the walk.
    assert!(
        hit_cost(false) < walked / 2,
        "the steps banked no allowance"
    );
    let after_reset = hit_cost(true);
    assert!(
        after_reset + 1 >= walked,
        "banked allowance paid across a reset: {after_reset}"
    );
}

#[test]
fn the_banked_allowance_is_capped() {
    // Five thousand steps would bank five thousand heartbeats' worth of
    // walking uncapped, enough for forty 40,001-unit walks. The bank holds at
    // most CREDIT_CAP (1,024 steps' worth), so the walks past it are billed.
    use crate::tc::work_account::CREDIT_CAP;
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(LIMIT);
    let _ = tc.whnf(&chain(LINKS));
    for _ in 0..5_000 {
        let _ = tc.infer_type(&constant("x"));
    }
    let probe = chain(LINKS);
    let before = tc.heartbeat_remaining();
    for _ in 0..40 {
        let _ = tc.whnf(&probe);
    }
    let cost = u64::from(before - tc.heartbeat_remaining());
    let walked = 40 * (2 * LINKS as u64 + 1);
    assert!(walked > CREDIT_CAP, "the walks must outgrow the cap");
    assert!(
        cost * UNITS_PER_HEARTBEAT + CREDIT_CAP + UNITS_PER_HEARTBEAT >= walked,
        "{cost} heartbeats for {walked} units: more than the cap was banked"
    );
    assert!(cost > 0, "the cap left nothing to bill");
}

/// The gate-9 mechanism (trust-ir 67b91383, measured there inside
/// `ExprEqWalk` under whnf-cache lookups): every iteration of a loop adds one
/// link to a chain, and the cache is probed with equal but separately built
/// chains, so each probe walks the whole chain. Steps grow linearly, the walks
/// quadratically. Here every iteration takes one cold `whnf` (a step) and four
/// cache hits (no step, a full walk each).
fn growing_chain_probes(tc: &TypeChecker<'_>, links: usize) -> usize {
    for n in 1..=links {
        let _ = tc.whnf(&chain(n));
        let probe = chain(n);
        for _ in 0..4 {
            let _ = tc.whnf(&probe);
        }
        if tc.heartbeat_spent() {
            return n;
        }
    }
    links
}

const GROWING_LINKS: usize = 2_000;
const GROWING_BUDGET: u32 = 8_000;

#[test]
fn growing_chain_probes_are_refused_by_a_budget_their_steps_fit() {
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(GROWING_BUDGET);
    let reached = growing_chain_probes(&tc, GROWING_LINKS);
    assert!(reached < GROWING_LINKS, "the walks never spent the budget");
    let refused = tc.infer_type(&constant("x"));
    assert!(
        matches!(
            refused,
            Err(TypeError::HeartbeatExceeded {
                limit: GROWING_BUDGET,
                ..
            })
        ),
        "a budget the walks spent is refused, never accepted: {refused:?}"
    );
}

#[test]
fn growing_chain_probes_mutant_without_the_equality_charge_fits_the_budget() {
    // MUTANT: the kernel before the meter, where a probe's key comparison spent
    // nothing. The same loop under the same budget runs to its end with the
    // budget unspent: its steps fit, and only the walks spend it above.
    let env = stuck_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(GROWING_BUDGET);
    let reached = work_meter::mutant::with_equality_charge_dropped(|| {
        growing_chain_probes(&tc, GROWING_LINKS)
    });
    assert_eq!(
        reached, GROWING_LINKS,
        "MUTANT: the steps alone spent the budget"
    );
    assert!(!tc.heartbeat_spent());
    assert!(tc.infer_type(&constant("x")).is_ok());
}

/// A calibration row for `UNITS_PER_HEARTBEAT` (`docs/DECISIONS.md`
/// `DR-KERNEL-WORK-METER-20261014`): the kernel prelude, an ordinary
/// environment of checked declarations, built uncached. The printed row is the
/// measurement (`--nocapture`); the assertion is the billing bound.
#[test]
fn prelude_build_row_bills_no_more_than_it_walks() {
    let _ = work_meter::stats::take();
    let env = Environment::try_with_prelude_uncached().expect("prelude");
    let stats = work_meter::stats::take();
    let units = stats.equality_visits + stats.fold_nodes + stats.equiv_nodes + stats.probes;
    println!(
        "ROW prelude constants={} steps={} work_heartbeats={} units={units} eq_walks={} \
         eq_visits={} collided_visits={} fold={} equiv={} probes={}",
        env.num_constants(),
        stats.step_ticks,
        stats.work_heartbeats,
        stats.equality_walks,
        stats.equality_visits,
        stats.collided_visits,
        stats.fold_nodes,
        stats.equiv_nodes,
        stats.probes,
    );
    assert!(
        stats.step_ticks > 0,
        "the prelude build reached no heartbeat site"
    );
    // Billing never exceeds the walking charged: a billed heartbeat is
    // UNITS_PER_HEARTBEAT units past the steps' allowance.
    assert!(
        stats.work_heartbeats * UNITS_PER_HEARTBEAT <= units,
        "billed {} heartbeats for {units} units",
        stats.work_heartbeats
    );
}
