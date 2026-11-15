// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The structural-induction search is decided by counts; its clock is a
//! backstop.
//!
//! The corpus is the goals of clean's own induction tests
//! (`crates/clean-cli/tests/auto_induction*.rs`) plus two the lane must refuse.
//! For each goal the answer, the proof term and the search's work (its backstop
//! polls, one per step that reached a poll site, superposition's given-clause
//! steps included) are compared:
//!
//! * with no clock at all, with an ample backstop, and under the slow-host seam
//!   (`search_stop::slowdown`), which makes every step slower;
//! * across ten runs.
//!
//! A backstop that fires answers `BackstopFired`, never `NotProved`; a count of
//! the language that stops an SMT solve answers `CountLimit` with its message.

use std::time::{Duration, Instant};

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, Level, LocalContext};

use crate::engine::AutomationEngine;
use crate::engine_induction::{InductionSearch, INDUCTION_FUEL, MAX_GOAL_DEPTH};
use crate::search_stop::slowdown::{PassAfterPoll, Slowdown};
use crate::search_stop::SearchStop;
use crate::smt::SMT_CONFLICT_LIMIT_REASON;

fn lvl0() -> Level {
    Level::zero()
}
fn lvl1() -> Level {
    Level::succ(Level::zero())
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn zero() -> Expr {
    Expr::const_str("Nat.zero")
}
fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}
fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.mul"), [a, b])
}
fn nat_succ(a: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), a)
}
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![lvl1()]),
        [nat(), lhs, rhs],
    )
}
fn list_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List", vec![lvl0()]), [nat()])
}
fn nil_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List.nil", vec![lvl0()]), [nat()])
}
fn cons_nat(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("List.cons", vec![lvl0()]),
        [nat(), h, t],
    )
}
fn eq_list(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![lvl1()]),
        [list_nat(), l, r],
    )
}
fn append(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("List.append"), [a, b])
}
/// `∀ (x₀ … x_{n-1} : dom), body`, outermost binder = highest index.
fn forall_n(dom: Expr, n: usize, body: Expr) -> Expr {
    (0..n).fold(body, |acc, _| {
        Expr::pi(BinderInfo::Default, dom.clone(), acc)
    })
}

/// `Nat`, `Eq`, `List`, the classical bootstrap, and a reducible
/// `List.append` recursing on its first argument (as in clean-cli's tests).
fn induction_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_list().expect("init_list");
    env.init_classical().expect("init_classical");
    let ty = Expr::pi(
        BinderInfo::Default,
        list_nat(),
        Expr::pi(BinderInfo::Default, list_nat(), list_nat()),
    );
    let motive = Expr::lam(BinderInfo::Default, list_nat(), list_nat());
    let cons_case = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            list_nat(),
            Expr::lam(
                BinderInfo::Default,
                list_nat(),
                cons_nat(Expr::bvar(2), Expr::bvar(0)),
            ),
        ),
    );
    let body = Expr::apps(
        Expr::const_str_levels("List.rec", vec![lvl1(), lvl0()]),
        [nat(), motive, Expr::bvar(0), cons_case, Expr::bvar(1)],
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("List.append"),
        level_params: vec![],
        type_: ty,
        value: Expr::lam(
            BinderInfo::Default,
            list_nat(),
            Expr::lam(BinderInfo::Default, list_nat(), body),
        ),
        is_reducible: true,
    })
    .expect("register List.append");
    env
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expect {
    Proved,
    NotProved,
}

/// The corpus: `(name, goal, expected answer)`.
fn corpus() -> Vec<(&'static str, Expr, Expect)> {
    let b = Expr::bvar;
    vec![
        (
            "zero_add",
            forall_n(nat(), 1, nat_eq(nat_add(zero(), b(0)), b(0))),
            Expect::Proved,
        ),
        (
            "add_zero",
            forall_n(nat(), 1, nat_eq(nat_add(b(0), zero()), b(0))),
            Expect::Proved,
        ),
        (
            "add_assoc",
            forall_n(
                nat(),
                3,
                nat_eq(
                    nat_add(nat_add(b(2), b(1)), b(0)),
                    nat_add(b(2), nat_add(b(1), b(0))),
                ),
            ),
            Expect::Proved,
        ),
        (
            "add_comm",
            forall_n(nat(), 2, nat_eq(nat_add(b(1), b(0)), nat_add(b(0), b(1)))),
            Expect::Proved,
        ),
        (
            "mul_comm",
            forall_n(nat(), 2, nat_eq(nat_mul(b(1), b(0)), nat_mul(b(0), b(1)))),
            Expect::Proved,
        ),
        (
            "append_nil",
            forall_n(list_nat(), 1, eq_list(append(b(0), nil_nat()), b(0))),
            Expect::Proved,
        ),
        (
            "append_assoc",
            forall_n(
                list_nat(),
                3,
                eq_list(
                    append(append(b(2), b(1)), b(0)),
                    append(b(2), append(b(1), b(0))),
                ),
            ),
            Expect::Proved,
        ),
        // Refusals: not the lane's shape, and a false equation.
        (
            "not_a_forall",
            eq_list(nil_nat(), nil_nat()),
            Expect::NotProved,
        ),
        (
            "succ_ne_self",
            forall_n(nat(), 1, nat_eq(nat_succ(b(0)), b(0))),
            Expect::NotProved,
        ),
    ]
}

/// What a search answered and what it spent.
#[derive(Debug, PartialEq)]
struct Observed {
    answer: &'static str,
    proof: Option<Expr>,
    polls: u64,
}

fn search(env: &Environment, goal: &Expr, stop: &SearchStop) -> Observed {
    let answer =
        AutomationEngine::new().search_by_induction_with(env, goal, &LocalContext::new(), stop);
    let (answer, proof) = match answer {
        InductionSearch::Proved(result) => ("proved", Some(result.proof_term().clone())),
        InductionSearch::NotProved => ("not-proved", None),
        InductionSearch::CountLimit(limit) => (limit, None),
        InductionSearch::BackstopFired => ("backstop-fired", None),
    };
    Observed {
        answer,
        proof,
        polls: stop.polls(),
    }
}

/// A backstop no run here should reach.
fn ample() -> Option<Instant> {
    Instant::now().checked_add(Duration::from_secs(600))
}

#[test]
fn the_corpus_answers_on_counts_idle_and_under_a_slow_host() {
    let env = induction_env();
    for (name, goal, expect) in corpus() {
        let counts_only = search(&env, &goal, &SearchStop::new(None));
        let expected = match expect {
            Expect::Proved => "proved",
            Expect::NotProved => "not-proved",
        };
        assert_eq!(counts_only.answer, expected, "{name}: {counts_only:?}");
        assert!(
            counts_only.polls > 0,
            "{name}: the search reaches a poll site, so the seam below slows it"
        );

        let idle = search(&env, &goal, &SearchStop::new(ample()));
        assert_eq!(
            idle, counts_only,
            "{name}: an unfired backstop changes nothing"
        );

        let slow = {
            let _seam = Slowdown::new(Duration::from_micros(200));
            search(&env, &goal, &SearchStop::new(ample()))
        };
        assert_eq!(
            slow, counts_only,
            "{name}: a slower host gets the same answer and work"
        );
    }
}

#[test]
fn the_corpus_spends_the_same_work_in_ten_runs() {
    let env = induction_env();
    for (name, goal, _) in corpus() {
        let first = search(&env, &goal, &SearchStop::new(None));
        for run in 1..10 {
            let again = search(&env, &goal, &SearchStop::new(None));
            assert_eq!(again, first, "{name}: run {run} differs from run 0");
        }
    }
}

#[test]
fn a_backstop_that_fires_is_could_not_run_never_not_proved() {
    let env = induction_env();
    // Every poll first sleeps 2 ms, and the backstop passes 1 ms after the
    // search starts, so the first poll sees it fired. Whatever the counts would
    // answer — a proof (`add_comm`, `mul_comm`) or a refusal (`succ_ne_self`,
    // `not_a_forall`) — the search reports the fired backstop.
    for (name, goal, _) in corpus().into_iter().filter(|(name, _, _)| {
        matches!(
            *name,
            "add_comm" | "mul_comm" | "succ_ne_self" | "not_a_forall"
        )
    }) {
        let _seam = Slowdown::new(Duration::from_millis(2));
        let stop = SearchStop::new(Instant::now().checked_add(Duration::from_millis(1)));
        let observed = search(&env, &goal, &stop);
        assert_eq!(observed.answer, "backstop-fired", "{name}: {observed:?}");
        assert!(stop.has_fired(), "{name}");
    }
    // Mid-search: `mul_comm` spends thousands of polls on its counts (5,559 on
    // 2026-10-14). At 1 ms a poll, a 50 ms backstop fires partway through, and
    // the answer is still the backstop's, not a missing proof.
    let (_, mul_comm, _) = corpus()
        .into_iter()
        .find(|(name, _, _)| *name == "mul_comm")
        .expect("corpus has mul_comm");
    let full = search(&env, &mul_comm, &SearchStop::new(None)).polls;
    let _seam = Slowdown::new(Duration::from_millis(1));
    let stop = SearchStop::new(Instant::now().checked_add(Duration::from_millis(50)));
    let observed = search(&env, &mul_comm, &stop);
    assert_eq!(observed.answer, "backstop-fired", "{observed:?}");
    assert!(
        observed.polls < full,
        "the backstop cut a {full}-poll search short: {observed:?}"
    );
}

#[test]
fn a_decision_the_counts_reached_stands_when_the_backstop_passes_after_the_last_poll() {
    // Let the backstop pass right after the lane's last poll has read the
    // clock. No poll sees it, so it cut no work short, and the counts' answer
    // must stand although it arrives after the backstop. An entry that read the
    // clock on its way out instead of the latch would answer `BackstopFired`
    // here. The poll to pass after is counted on the lane itself
    // (`try_induction_lane`), so a read on the way out is one poll past it.
    let env = induction_env();
    let engine = AutomationEngine::new();
    for (name, goal, expect) in corpus() {
        let lane = SearchStop::new(None);
        let _ = engine.try_induction_lane(&env, &goal, &LocalContext::new(), &lane, INDUCTION_FUEL);
        let _seam = PassAfterPoll::new(lane.polls());
        let stop = SearchStop::new(ample());
        let late = search(&env, &goal, &stop);
        let expected = match expect {
            Expect::Proved => "proved",
            Expect::NotProved => "not-proved",
        };
        assert_eq!(late.answer, expected, "{name}: {late:?}");
        assert_eq!(
            (late.polls, stop.has_fired()),
            (lane.polls(), false),
            "{name}: the entry polls nothing past the lane"
        );
    }
}

#[test]
fn the_lanes_count_checks_come_before_its_poll() {
    // Fuel and the goal-depth rail decide before the lane polls, so a backstop
    // that passed before the search started does not pre-empt them: the lane
    // declines without polling, and the search answers `NotProved`.
    let env = induction_env();
    let passed = || SearchStop::new(Some(Instant::now()));
    let (_, add_comm, _) = corpus()
        .into_iter()
        .find(|(name, _, _)| *name == "add_comm")
        .expect("corpus has add_comm");
    let stop = passed();
    let out_of_fuel =
        AutomationEngine::new().try_induction_lane(&env, &add_comm, &LocalContext::new(), &stop, 0);
    assert!(out_of_fuel.is_none());
    assert_eq!((stop.polls(), stop.has_fired()), (0, false), "no fuel");

    let too_deep = (0..=MAX_GOAL_DEPTH).fold(Expr::bvar(0), |e, _| nat_succ(e));
    let goal = forall_n(nat(), 1, nat_eq(too_deep, Expr::bvar(0)));
    let stop = passed();
    let observed = search(&env, &goal, &stop);
    assert_eq!(observed.answer, "not-proved", "{observed:?}");
    assert_eq!((stop.polls(), stop.has_fired()), (0, false), "too deep");
}

#[test]
fn the_old_entry_keeps_its_answers_and_treats_its_timeout_as_a_backstop() {
    let env = induction_env();
    let engine = AutomationEngine::new();
    for (name, goal, expect) in corpus() {
        let found = engine.prove_by_induction(&env, &goal, Duration::from_secs(600));
        assert_eq!(found.is_some(), expect == Expect::Proved, "{name}");
    }
    // A timeout that has already passed is a fired backstop: no answer, even for
    // a goal the counts prove.
    let (_, add_comm, _) = corpus()
        .into_iter()
        .find(|(name, _, _)| *name == "add_comm")
        .expect("corpus has add_comm");
    assert!(engine
        .prove_by_induction(&env, &add_comm, Duration::ZERO)
        .is_none());
    assert!(matches!(
        engine.prove_by_induction_counted(&env, &add_comm, Instant::now()),
        InductionSearch::BackstopFired
    ));
}

#[test]
fn the_backstop_latches_only_when_polled() {
    let stop = SearchStop::new(Instant::now().checked_sub(Duration::from_millis(1)));
    assert!(
        !stop.has_fired(),
        "a passed backstop no poll has seen cuts nothing"
    );
    assert!(stop.backstop_fired());
    assert!(stop.has_fired(), "a poll that saw it fire latches");
    let unbounded = SearchStop::new(None);
    assert!(!unbounded.backstop_fired() && !unbounded.has_fired());
}

/// `True`/`False`/`Not`, `Or`, `And`, `Nat` and one `Prop` atom per
/// (pigeon, hole).
fn pigeonhole_env(holes: usize) -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("True/False/Not");
    env.init_or().expect("Or");
    env.init_and().expect("And");
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

/// `¬ pigeonhole` for `holes + 1` pigeons, as one disjunction with no
/// hypotheses: some pigeon is in no hole, or two pigeons share a hole. It is
/// true, and refuting its negation (the pigeonhole clauses) needs exponentially
/// many CDCL conflicts (`bridge::tests::tests_conflict_limit`). As a single
/// disjunction rather than local clauses, no proof-reconstruction case split
/// runs over hundreds of hypotheses; as balanced trees, it stays inside the
/// lane's `MAX_GOAL_DEPTH`.
fn not_pigeonhole(holes: usize) -> Expr {
    fn balanced(mut items: Vec<Expr>, join: &dyn Fn(Expr, Expr) -> Expr) -> Expr {
        while items.len() > 1 {
            let mut next = Vec::with_capacity(items.len().div_ceil(2));
            let mut pairs = items.into_iter();
            while let Some(left) = pairs.next() {
                next.push(match pairs.next() {
                    Some(right) => join(left, right),
                    None => left,
                });
            }
            items = next;
        }
        items.pop().expect("at least one item")
    }
    let atom =
        |p: usize, h: usize| Expr::const_(Name::from_string(&format!("php_{p}_{h}")), vec![]);
    let or = |a: Expr, b: Expr| Expr::apps(Expr::const_str("Or"), [a, b]);
    let and = |a: Expr, b: Expr| Expr::apps(Expr::const_str("And"), [a, b]);
    let not = |a: Expr| Expr::app(Expr::const_str("Not"), a);
    let mut disjuncts = Vec::new();
    for p in 0..=holes {
        disjuncts.push(balanced(
            (0..holes).map(|h| not(atom(p, h))).collect(),
            &and,
        ));
    }
    for h in 0..holes {
        for first in 0..=holes {
            for second in first + 1..=holes {
                disjuncts.push(and(atom(first, h), atom(second, h)));
            }
        }
    }
    balanced(disjuncts, &or)
}

#[test]
fn an_smt_solve_stopped_by_the_conflict_limit_is_the_searchs_count_limit() {
    // `∀ n : Nat, ¬ pigeonhole(10)`: the zero minor is the disjunction itself,
    // which only an SMT refutation of the pigeonhole clauses could prove, and
    // that solve stops at `SMT_CONFLICT_LIMIT`. The search ends on its counts
    // and says which count stopped it, with no clock involved.
    let env = pigeonhole_env(10);
    let goal = Expr::pi(BinderInfo::Default, nat(), not_pigeonhole(10));
    let stop = SearchStop::new(None);
    let answer =
        AutomationEngine::new().search_by_induction_with(&env, &goal, &LocalContext::new(), &stop);
    match answer {
        InductionSearch::CountLimit(limit) => assert_eq!(limit, SMT_CONFLICT_LIMIT_REASON),
        other => panic!("expected the conflict limit's stop, got {other:?}"),
    }
    assert!(!stop.has_fired());
}
