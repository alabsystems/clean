// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit pins for the replay schedule (`replay_order.rs`), on name graphs.
//!
//! Every expected verdict is the one `Lean.Environment.replay` gives for the
//! same dependency shape, measured 2026-09-24 with the pinned v4.30.0-rc2
//! binary on `.olean`s minted by `GenReplayForged.lean` (the `forged_replay`
//! fixture family) and replayed one constant at a time:
//! `forged3_self: (kernel) unknown constant 'forged3_self'`;
//! `forged3_cycA: while replaying declaration 'forged3_cycB': (kernel) unknown
//! constant 'forged3_cycA'`; `honest_chain: ok`.

use super::*;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn graph(edges: &[(&str, &[&str])]) -> ReplayGraph {
    let mut g = ReplayGraph::new();
    for (name, refs) in edges {
        g.insert(n(name), refs.iter().map(|r| n(r)));
    }
    g
}

fn all_pass(_: &Name) -> Result<(), String> {
    Ok(())
}

#[test]
fn test_schedule_self_reference_is_refused_before_the_kernel() {
    let g = graph(&[("self", &["self", "False"])]);
    let schedule = g.schedule();
    assert!(matches!(
        schedule.structural_refusal(&n("self")),
        Some(ReplayRefusal::SelfReference { .. })
    ));
    let mut kernel_calls = 0;
    let verdicts = schedule.resolve(|_| {
        kernel_calls += 1;
        Ok(())
    });
    assert_eq!(
        kernel_calls, 0,
        "a self-referential value never reaches the kernel"
    );
    let err = verdicts[&n("self")].clone().expect_err("refused");
    assert!(err.to_string().contains("refers to itself"), "{err}");
}

#[test]
fn test_schedule_two_cycle_refuses_both_members() {
    let g = graph(&[("cycA", &["cycB"]), ("cycB", &["cycA"])]);
    let schedule = g.schedule();
    let verdicts = schedule.resolve(all_pass);
    // Lean's order of discovery: replaying cycA first replays cycB, whose
    // check meets the pending cycA.
    let b = verdicts[&n("cycB")].clone().expect_err("cycB refused");
    assert!(
        matches!(&b, ReplayRefusal::DependencyCycle { pending, .. } if *pending == n("cycA")),
        "{b}"
    );
    assert!(b.to_string().contains("cycA -> cycB -> cycA"), "{b}");
    let a = verdicts[&n("cycA")].clone().expect_err("cycA refused");
    assert!(
        matches!(&a, ReplayRefusal::DependsOnRefused { dependency, .. } if *dependency == n("cycB")),
        "{a}"
    );
}

#[test]
fn test_schedule_orders_dependencies_before_dependents() {
    // chain -> t, eq -> one, and a non-local reference that is ignored.
    let g = graph(&[
        ("t", &["True.intro"]),
        ("chain", &["t", "True"]),
        ("one", &["Nat.succ"]),
        ("eq", &["one", "Eq"]),
    ]);
    let schedule = g.schedule();
    let pos = |s: &str| {
        schedule
            .order()
            .iter()
            .position(|x| *x == n(s))
            .unwrap_or_else(|| panic!("{s} scheduled"))
    };
    assert!(pos("t") < pos("chain"));
    assert!(pos("one") < pos("eq"));
    let verdicts = schedule.resolve(all_pass);
    assert!(verdicts.values().all(Result::is_ok), "{verdicts:?}");
}

#[test]
fn test_kernel_rejection_propagates_to_dependents_only() {
    let g = graph(&[("bad", &[]), ("uses_bad", &["bad"]), ("independent", &[])]);
    let verdicts = g.schedule().resolve(|name| {
        if *name == n("bad") {
            Err("check_type: TypeMismatch".to_owned())
        } else {
            Ok(())
        }
    });
    assert!(matches!(
        verdicts[&n("bad")],
        Err(ReplayRefusal::KernelRejected { .. })
    ));
    let dep = verdicts[&n("uses_bad")]
        .clone()
        .expect_err("dependent refused");
    assert!(
        dep.to_string().contains("check_type: TypeMismatch"),
        "{dep}"
    );
    assert!(verdicts[&n("independent")].is_ok());
}

#[test]
fn test_structurally_doomed_covers_transitive_dependents_of_a_cycle() {
    let g = graph(&[
        ("cycA", &["cycB"]),
        ("cycB", &["cycA"]),
        ("above", &["cycA"]),
        ("clean", &[]),
    ]);
    let doomed = g.schedule().structurally_doomed();
    assert!(doomed.contains(&n("cycA")) && doomed.contains(&n("cycB")));
    assert!(doomed.contains(&n("above")));
    assert!(!doomed.contains(&n("clean")));
}

#[test]
fn test_caller_refusal_is_structural_and_propagates() {
    let mut g = graph(&[("a", &["unsafeCast"]), ("b", &["a"])]);
    g.refuse(
        n("a"),
        ReplayRefusal::NotReplayable {
            name: n("a"),
            safety: "unsafe",
        },
    );
    let verdicts = g.schedule().resolve(all_pass);
    assert!(matches!(
        verdicts[&n("a")],
        Err(ReplayRefusal::NotReplayable { .. })
    ));
    let b = verdicts[&n("b")]
        .clone()
        .expect_err("dependent of an unsafe refused");
    assert!(b.to_string().contains("is unsafe"), "{b}");
}

/// A declaration of the replayed module that this replay does not admit is
/// not in Lean's replay environment: a node that mentions it is refused, while
/// a reference to anything else outside the graph is a trusted import.
#[test]
fn test_reference_to_unreplayed_local_is_refused_imports_are_not() {
    let mut g = graph(&[
        ("uses_mate", &["mate", "Nat"]),
        ("uses_import", &["Nat.succ"]),
    ]);
    g.mark_unreplayed(n("mate"));
    let mut kernel_calls = Vec::new();
    let verdicts = g.schedule().resolve(|name| {
        kernel_calls.push(name.clone());
        Ok(())
    });
    let err = verdicts[&n("uses_mate")].clone().expect_err("refused");
    assert!(
        matches!(&err, ReplayRefusal::DependsOnUnreplayed { dependency, .. } if *dependency == n("mate")),
        "{err}"
    );
    assert!(verdicts[&n("uses_import")].is_ok());
    assert_eq!(kernel_calls, vec![n("uses_import")]);
}

/// The unreplayed set is compared by NAME: a numeric component and a string
/// component that DISPLAY alike (`x.0`) are different names, and the one that
/// was not marked is a trusted import.
#[test]
fn test_unreplayed_is_compared_by_name_not_display_spelling() {
    let num = Name::from_string("x").num(0);
    let str_ = Name::from_string("x").str("0");
    assert_eq!(
        num.to_string(),
        str_.to_string(),
        "the two names display alike"
    );
    let mut g = ReplayGraph::new();
    g.insert(n("uses_num"), [num.clone()]);
    g.insert(n("uses_str"), [str_.clone()]);
    g.mark_unreplayed(num.clone());
    let verdicts = g.schedule().resolve(|_| Ok(()));
    assert!(
        matches!(&verdicts[&n("uses_num")], Err(ReplayRefusal::DependsOnUnreplayed { dependency, .. }) if *dependency == num),
        "{:?}",
        verdicts[&n("uses_num")]
    );
    assert!(
        verdicts[&n("uses_str")].is_ok(),
        "a different name is not refused"
    );
}

/// Only the local declarations a target reaches need a verdict.
#[test]
fn test_local_closure_is_what_the_targets_reach() {
    let g = graph(&[
        ("target", &["mid"]),
        ("mid", &["leaf", "Nat"]),
        ("leaf", &[]),
        ("unrelated", &["leaf"]),
    ]);
    let closure = g.schedule().local_closure([&n("target")]);
    let got: Vec<String> = closure.iter().map(ToString::to_string).collect();
    assert_eq!(got, ["leaf", "mid", "target"]);
}

/// A constructor mentioning its own inductive is no cycle (Lean replays the
/// block as one `inductDecl`), and every block member carries the block's
/// external references.
#[test]
fn test_resident_refs_treats_an_inductive_block_as_one_unit() {
    let env = Environment::with_prelude();
    let succ = resident_refs(&env, &n("Nat.succ"));
    for member in ["Nat", "Nat.zero", "Nat.succ", "Nat.rec"] {
        assert!(
            !succ.contains(&n(member)),
            "`{member}` is in Nat's own block: {succ:?}"
        );
    }
    let nat = resident_refs(&env, &n("Nat"));
    assert_eq!(
        succ, nat,
        "every block member carries the block's references"
    );
}

/// `Proj` nodes name their structure, which the kernel must consult.
#[test]
fn test_expr_refs_reports_projection_structures() {
    let e = Expr::proj(n("Prod"), 0, Expr::const_(n("p"), vec![]));
    let refs = expr_refs(&Expr::const_(n("Nat"), vec![]), Some(&e));
    assert_eq!(
        refs.iter().map(ToString::to_string).collect::<Vec<_>>(),
        ["Nat", "Prod", "p"]
    );
}

#[test]
fn test_admission_gate_is_fail_closed_on_a_missing_dependency_verdict() {
    let g = graph(&[("a", &[]), ("b", &["a"])]);
    let schedule = g.schedule();
    let err = schedule
        .admission_gate(&n("b"), &ReplayVerdicts::new())
        .expect_err("no verdict for `a` yet");
    assert!(matches!(err, ReplayRefusal::DependsOnRefused { .. }));
}

/// A dependent is refused on a FINDING whenever one of its refused
/// dependencies was: it is undecided (the heartbeat budget's doing) only when
/// every refused dependency is, so a budget refusal never hides a finding,
/// whichever dependency comes first.
#[test]
fn test_admission_gate_names_a_finding_dependency_before_an_undecided_one() {
    let starved = |name: &str| ReplayRefusal::BudgetExhausted {
        name: n(name),
        limit: 1,
        message: "infer_sort: constant registry: TypeMismatch".to_owned(),
    };
    let rejected = |name: &str| ReplayRefusal::KernelRejected {
        name: n(name),
        message: "check_type: TypeMismatch".to_owned(),
    };
    for refs in [&["u", "f"][..], &["f", "u"][..]] {
        let g = graph(&[("u", &[]), ("f", &[]), ("d", refs)]);
        let schedule = g.schedule();
        let verdicts =
            ReplayVerdicts::from([(n("u"), Err(starved("u"))), (n("f"), Err(rejected("f")))]);
        let err = schedule
            .admission_gate(&n("d"), &verdicts)
            .expect_err("`d` uses two refused declarations");
        assert!(
            matches!(&err, ReplayRefusal::DependsOnRefused { dependency, undecided: false, .. }
                if *dependency == n("f")),
            "{refs:?}: {err:?}"
        );
        assert!(!err.undecided(), "{err:?}");
    }

    // Every refused dependency undecided: undecided, and so is a dependent of
    // that dependent; one refused through a finding stays a finding.
    let g = graph(&[
        ("u", &[]),
        ("v", &[]),
        ("f", &[]),
        ("d", &["u", "v"]),
        ("e", &["d"]),
        ("g", &["f"]),
        ("h", &["g", "d"]),
    ]);
    let schedule = g.schedule();
    let mut verdicts = ReplayVerdicts::from([
        (n("u"), Err(starved("u"))),
        (n("v"), Err(starved("v"))),
        (n("f"), Err(rejected("f"))),
    ]);
    for name in ["d", "e", "g", "h"] {
        let verdict = schedule.admission_gate(&n(name), &verdicts);
        verdicts.insert(n(name), verdict);
    }
    let undecided = |name: &str| {
        verdicts[&n(name)]
            .as_ref()
            .expect_err("refused through a refused dependency")
            .undecided()
    };
    assert!(undecided("d"), "{:?}", verdicts[&n("d")]);
    assert!(
        matches!(&verdicts[&n("d")], Err(ReplayRefusal::DependsOnRefused { dependency, .. })
            if *dependency == n("u")),
        "{:?}",
        verdicts[&n("d")]
    );
    assert!(undecided("e"), "{:?}", verdicts[&n("e")]);
    assert!(!undecided("g"), "{:?}", verdicts[&n("g")]);
    assert!(!undecided("h"), "{:?}", verdicts[&n("h")]);
    assert!(starved("u").undecided() && !rejected("f").undecided());
}

#[test]
fn test_schedule_survives_a_chain_deeper_than_a_thread_stack() {
    const DEPTH: usize = 200_000;
    let mut g = ReplayGraph::new();
    for i in 0..DEPTH {
        let refs = if i == 0 {
            vec![]
        } else {
            vec![n(&format!("c{}", i - 1))]
        };
        g.insert(n(&format!("c{i}")), refs);
    }
    let schedule = g.schedule();
    assert_eq!(schedule.order().len(), DEPTH);
    assert!(schedule.structurally_doomed().is_empty());
}
