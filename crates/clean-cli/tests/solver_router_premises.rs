// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the per-goal engine ROUTER (`clean_auto::engine_router`)
//! and the improved premise selection / injection lane (`MePoSelector` +
//! `AutomationEngine::try_premise_injection`, exercised through
//! `auto_prove_with_premises`).
//!
//! These tests live in `clean-cli/tests` (not `clean-auto/tests`) on purpose:
//! `clean-auto`'s dev-dependency graph pulls the sibling trust-cg / trust-ir
//! path-deps, whose hardcoded `clean-kernel` path collides during lockfile
//! resolution from a worktree. `clean-cli` depends only on `clean-auto`'s lib
//! (no trust-cg), so it drives the public API without that dep.
//!
//! SOUNDNESS (load-bearing): the router and premise lane are on the *search*
//! side, not the TCB. The router only decides engine *order* — it has zero
//! soundness weight. The premise-injection test re-checks the emitted proof term
//! through the kernel (`TypeChecker::infer_type` + `is_def_eq` against the goal),
//! so the test passes only when the closed proof *kernel-checks*, never merely
//! because `auto_prove_with_premises` returned `Some`.

use std::time::Duration;

use clean_auto::premise::{MePoSelector, PremiseDatabase};
use clean_auto::{classify_goal, route_goal, AutomationEngine, GoalClass, RoutedEngine};
use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, Level, TypeChecker};

// ─── shared expression builders ────────────────────────────────────────────

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn konst(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn ty_a() -> Expr {
    konst("A")
}

/// Universe level `1` (the universe of `A : Type`).
fn level_one() -> Level {
    Level::succ(Level::zero())
}

/// `@Eq.{lvl} ty lhs rhs`.
fn eq_at(lvl: Level, ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(name("Eq"), vec![lvl]),
        [ty.clone(), lhs.clone(), rhs.clone()],
    )
}

/// `@Eq.{1} A lhs rhs` — equality of elements of the base type `A`.
fn eq_a(lhs: &Expr, rhs: &Expr) -> Expr {
    eq_at(level_one(), &ty_a(), lhs, rhs)
}

fn nat() -> Expr {
    konst("Nat")
}

/// `Nat.add a b`.
fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(konst("Nat.add"), [a, b])
}

// ─── ROUTER classification tests ───────────────────────────────────────────

/// An equation between *compound* terms with no arithmetic routes to the
/// superposition lane first (its paramodulation/rewriting wheelhouse).
#[test]
fn test_router_equational_goal_leads_with_superposition() {
    // f a = f b  — both sides are applications of an uninterpreted `f`.
    let goal = eq_a(
        &Expr::app(konst("f"), konst("a")),
        &Expr::app(konst("f"), konst("b")),
    );
    assert_eq!(classify_goal(&goal), GoalClass::Equational);
    assert_eq!(
        route_goal(&goal)[0],
        RoutedEngine::Superposition,
        "equational goals must try superposition first"
    );
}

/// A goal carrying an arithmetic operation routes to the SMT theory solver first.
#[test]
fn test_router_arithmetic_goal_leads_with_smt() {
    // Nat.add a b = c
    let goal = eq_a(&nat_add(konst("a"), konst("b")), &konst("c"));
    assert_eq!(classify_goal(&goal), GoalClass::Arithmetic);
    assert_eq!(
        route_goal(&goal)[0],
        RoutedEngine::Smt,
        "arithmetic goals must try SMT first"
    );
}

/// A `∀ (n : Nat), P n` goal routes to the structural-induction lane first.
#[test]
fn test_router_inductive_goal_leads_with_induction() {
    // ∀ (n : Nat), 0 + n = n
    let body = eq_a_nat(nat_add(konst("Nat.zero"), Expr::bvar(0)), Expr::bvar(0));
    let goal = Expr::pi(BinderInfo::Default, nat(), body);
    assert_eq!(classify_goal(&goal), GoalClass::Inductive);
    assert_eq!(
        route_goal(&goal)[0],
        RoutedEngine::Induction,
        "∀(n:Nat) goals must try the induction lane first"
    );
}

/// A top-level logical connective routes to SMT (DPLL) first.
#[test]
fn test_router_propositional_goal_leads_with_smt() {
    // And p q
    let goal = Expr::apps(konst("And"), [konst("p"), konst("q")]);
    assert_eq!(classify_goal(&goal), GoalClass::Propositional);
    assert_eq!(route_goal(&goal)[0], RoutedEngine::Smt);
}

/// A bare-atom equality (`a = b`, both sides atoms) is NOT compound: it stays in
/// the general/SMT-first class so EUF closes it — preserving historical order.
#[test]
fn test_router_atom_equality_is_general_smt_first() {
    let goal = eq_a(&konst("a"), &konst("b"));
    assert_eq!(classify_goal(&goal), GoalClass::General);
    assert_eq!(route_goal(&goal)[0], RoutedEngine::Smt);
    // Every plan is a permutation of all four engines (fall back to trying all).
    let plan = route_goal(&goal);
    for engine in [
        RoutedEngine::Smt,
        RoutedEngine::Induction,
        RoutedEngine::Superposition,
        RoutedEngine::Oracle,
    ] {
        assert!(plan.contains(&engine), "plan must include {engine:?}");
    }
}

/// `@Eq.{1} Nat lhs rhs` — equalities over `Nat` used inside the inductive goal.
fn eq_a_nat(lhs: Expr, rhs: Expr) -> Expr {
    eq_at(level_one(), &nat(), &lhs, &rhs)
}

// ─── improved premise SELECTION test ───────────────────────────────────────

/// The conclusion-weighted refinement ranks a lemma that *concludes* about the
/// goal's symbols above one that only *mentions* them in a hypothesis, even when
/// plain symbol overlap ties the two.
#[test]
fn test_select_relevant_prefers_conclusion_match() {
    let mut db = PremiseDatabase::new();

    // P_concl : @Eq A a b  — the goal's symbols {Eq, A, a, b} are all in the
    // conclusion (the whole statement).
    let p_concl = db.add(name("P_concl"), eq_a(&konst("a"), &konst("b")));

    // P_hyp : (@Eq A a b) → @Eq A c d  — the goal symbols a, b appear only in
    // the *antecedent*; the conclusion is about c, d.
    let p_hyp = db.add(
        name("P_hyp"),
        Expr::pi(
            BinderInfo::Default,
            eq_a(&konst("a"), &konst("b")),
            eq_a(&konst("c"), &konst("d")),
        ),
    );

    let goal = eq_a(&konst("a"), &konst("b"));
    let selector = MePoSelector::new(&db);
    let ranked = selector.select_relevant(&goal, 8);

    assert!(!ranked.is_empty(), "should select at least one premise");
    assert_eq!(
        ranked[0].id, p_concl,
        "conclusion-matching premise must rank above the hypothesis-only one"
    );
    // Sanity: both premises are in scope; the ordering (not membership) is the point.
    assert!(ranked.iter().any(|p| p.id == p_hyp));
}

// ─── premise INJECTION end-to-end (kernel-checked) ─────────────────────────

fn axiom(env: &mut Environment, n: &str, level_params: Vec<Name>, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: name(n),
        level_params,
        type_,
    })
    .unwrap_or_else(|e| panic!("axiom `{n}` should type-check: {e:?}"));
}

/// Minimal faithful env: `Eq` + `Eq.trans` with their genuine Lean types, a base
/// type `A`, elements `a`/`b`/`c`/`d`, and the transitivity lemmas as named
/// axioms (so the injected proof can reference them as constants).
fn build_injection_env() -> Environment {
    let mut env = Environment::new();
    let u = || name("u");
    let su = || Expr::sort(Level::param(u()));
    let pu = || Level::param(u());
    let b = Expr::bvar;
    let d = BinderInfo::Default;

    // Eq : {α : Sort u} → α → α → Prop
    axiom(
        &mut env,
        "Eq",
        vec![u()],
        Expr::pi(d, su(), Expr::pi(d, b(0), Expr::pi(d, b(1), Expr::prop()))),
    );

    // Eq.trans : {α}{a b c} → @Eq α a b → @Eq α b c → @Eq α a c
    axiom(
        &mut env,
        "Eq.trans",
        vec![u()],
        Expr::pi(
            d,
            su(),
            Expr::pi(
                d,
                b(0),
                Expr::pi(
                    d,
                    b(1),
                    Expr::pi(
                        d,
                        b(2),
                        Expr::pi(
                            d,
                            eq_at(pu(), &b(3), &b(2), &b(1)),
                            Expr::pi(
                                d,
                                eq_at(pu(), &b(4), &b(2), &b(1)),
                                eq_at(pu(), &b(5), &b(4), &b(2)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );

    // Base type A : Type and elements a, b, c, d : A.
    axiom(&mut env, "A", vec![], Expr::type_());
    for elem in ["a", "b", "c", "d"] {
        axiom(&mut env, elem, vec![], ty_a());
    }

    // The transitivity-chain lemmas as named axioms (constants the injected proof
    // closes over), plus a distractor.
    axiom(&mut env, "lemAB", vec![], eq_a(&konst("a"), &konst("b")));
    axiom(&mut env, "lemBC", vec![], eq_a(&konst("b"), &konst("c")));
    axiom(&mut env, "lemCD", vec![], eq_a(&konst("c"), &konst("d")));
    env
}

/// A premise database mirroring the env's lemmas, so MePo can select them.
fn build_injection_db() -> PremiseDatabase {
    let mut db = PremiseDatabase::new();
    db.add(name("lemAB"), eq_a(&konst("a"), &konst("b")));
    db.add(name("lemBC"), eq_a(&konst("b"), &konst("c")));
    db.add(name("lemCD"), eq_a(&konst("c"), &konst("d")));
    db
}

/// Baseline: without premises, `a = c` is unprovable (no hypotheses, EUF has
/// nothing to chain, superposition saturates). This is the "before" state that
/// premise selection newly closes.
#[test]
fn test_goal_unprovable_without_premises() {
    let env = build_injection_env();
    let goal = eq_a(&konst("a"), &konst("c"));
    let engine = AutomationEngine::new();
    assert!(
        engine
            .auto_prove(&env, &goal, Duration::from_secs(10), None)
            .is_none(),
        "a = c must be unprovable without the supporting lemmas"
    );
}

/// With the premise database, the injection lane selects `lemAB`/`lemBC`, feeds
/// them to SMT, and the closed proof (`lemAB`/`lemBC` substituted for the
/// injected hypothesis fvars) KERNEL-CHECKS against `a = c`.
#[test]
fn test_premise_injection_closes_goal_kernel_checked() {
    let env = build_injection_env();
    let db = build_injection_db();
    let goal = eq_a(&konst("a"), &konst("c"));

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove_with_premises(&env, &goal, Vec::new(), &db, Duration::from_secs(20), None)
        .expect("a = c should be provable once the relevant lemmas are injected");

    // SOUNDNESS GATE: the emitted proof term must kernel-check against the goal.
    let proof_term = result.proof_term();
    assert!(
        result.proof_context().is_none(),
        "an injected-premise proof over a closed goal must itself be closed"
    );
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof_term)
        .unwrap_or_else(|e| panic!("injected-premise proof failed to type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &goal),
        "injected-premise proof kernel-checks to {inferred:?}, not the goal {goal:?}"
    );
}
