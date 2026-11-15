// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The SMT solver's CDCL core stops at `SMT_CONFLICT_LIMIT`, a constant of the
//! language, and the bridge says so.
//!
//! The fixture is the pigeonhole principle over opaque `Prop` atoms: `holes + 1`
//! pigeons, each in some hole, no two in one hole. It is unsatisfiable, and a
//! resolution refutation of it (so any CDCL run) needs exponentially many
//! conflicts in `holes`. Measured 2026-10-14 with no limit: six holes take 440
//! conflicts, nine 15,720, ten 78,688. So ten holes is far past the limit and
//! six far inside it.

use super::super::*;
use crate::smt::{SmtResult, SMT_CONFLICT_LIMIT_REASON};
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

fn atom(pigeon: usize, hole: usize) -> Expr {
    Expr::const_(Name::from_string(&format!("php_{pigeon}_{hole}")), vec![])
}

/// `True`/`False`/`Not`, `Or`, and one `Prop` atom per (pigeon, hole).
fn pigeonhole_env(holes: usize) -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("True/False/Not");
    env.init_or().expect("Or");
    for pigeon in 0..=holes {
        for hole in 0..holes {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(&format!("php_{pigeon}_{hole}")),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("pigeonhole atom");
        }
    }
    env
}

fn or(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [a, b])
}

fn not(a: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a)
}

/// The pigeonhole clauses, one hypothesis each.
fn pigeonhole_clauses(holes: usize) -> Vec<Expr> {
    let mut clauses = Vec::new();
    for pigeon in 0..=holes {
        let somewhere = (1..holes).fold(atom(pigeon, 0), |acc, hole| or(acc, atom(pigeon, hole)));
        clauses.push(somewhere);
    }
    for hole in 0..holes {
        for first in 0..=holes {
            for second in first + 1..=holes {
                clauses.push(or(not(atom(first, hole)), not(atom(second, hole))));
            }
        }
    }
    clauses
}

/// Prove `False` from the pigeonhole clauses; the bridge and its answer.
fn refute_pigeonhole(env: &Environment, holes: usize) -> (SmtBridge<'_>, SmtVerificationResult) {
    let mut bridge = SmtBridge::new(env);
    for clause in pigeonhole_clauses(holes) {
        bridge
            .add_hypothesis(&clause)
            .expect("a clause over Prop atoms translates");
    }
    let goal = Expr::const_(Name::from_string("False"), vec![]);
    let result = bridge.prove(&goal).expect("the bridge runs the solve");
    (bridge, result)
}

#[test]
fn a_pigeonhole_core_stops_at_the_conflict_limit_and_says_so() {
    let env = pigeonhole_env(10);
    let (mut bridge, result) = refute_pigeonhole(&env, 10);
    match &result {
        SmtVerificationResult::Unknown(reason) => assert_eq!(
            reason, SMT_CONFLICT_LIMIT_REASON,
            "the answer names the count that stopped the solve"
        ),
        other => panic!("ten holes must stop at the conflict limit, got {other:?}"),
    }
    assert!(bridge.conflict_limit_reached());
    // The count, not a clock: the solve spent exactly the limit.
    assert_eq!(
        bridge.stats().sat_conflicts,
        crate::smt::SMT_CONFLICT_LIMIT,
        "the CDCL core stops at its limit, not before or after"
    );
    // The stop leaves the core at its root, as the DPLL(T) loop's restart and
    // theory-clause exits do. The stopped search's decisions are not facts: a
    // later `add_clause` (E-matching's instance clauses) or `solve()` that read
    // them as level-0 assignments would answer a level-0 UNSAT, and a core,
    // that depend on guesses.
    assert_eq!(
        bridge.smt.sat_trail_max_level(),
        0,
        "a solve stopped at the limit backtracks to the root"
    );
    // A re-solve on the spent solver, which is what E-matching does after an
    // `Unknown`, stops at the limit again: level-0 propagation cannot refute
    // ten holes, and the first conflict above the root is past the limit.
    match bridge.smt.solve() {
        SmtResult::Unknown => {}
        other => panic!("a spent solver must stop at the limit again, got {other:?}"),
    }
    assert_eq!(bridge.smt.sat_trail_max_level(), 0);
}

#[test]
fn a_small_pigeonhole_core_is_decided_inside_the_limit() {
    // Paired control: the same encoding, six holes, is refuted by the solver
    // itself, so the limit is not what answers the small case.
    let env = pigeonhole_env(6);
    let (bridge, result) = refute_pigeonhole(&env, 6);
    assert!(
        !bridge.conflict_limit_reached(),
        "six holes stay inside the limit"
    );
    assert!(
        bridge.stats().sat_conflicts < crate::smt::SMT_CONFLICT_LIMIT,
        "conflicts {}",
        bridge.stats().sat_conflicts
    );
    assert!(
        !matches!(&result, SmtVerificationResult::Unknown(reason) if reason == SMT_CONFLICT_LIMIT_REASON),
        "a decided solve does not report the limit: {result:?}"
    );
}

#[test]
fn a_search_decided_inside_the_limit_spends_the_same_conflicts_every_run() {
    // "Decided by counts alone, the same on every host" needs more than a limit
    // that stops: a search the limit lets finish must take the same path every
    // time, or a goal near the limit is decided on one run and stopped on the
    // next. Each run builds a fresh bridge, so its hash maps iterate in a fresh
    // order; the six-hole core spends hundreds of conflicts, so a choice that
    // followed that order would show here.
    let env = pigeonhole_env(6);
    let spend = || {
        let (bridge, result) = refute_pigeonhole(&env, 6);
        (bridge.stats().sat_conflicts, format!("{result:?}"))
    };
    let first = spend();
    assert!(first.0 > 0, "the control does real CDCL work: {first:?}");
    for run in 1..10 {
        assert_eq!(spend(), first, "run {run} differs from run 0");
    }
}
