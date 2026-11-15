// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof irrelevance is three-valued, and both definite answers are final.
//!
//! Pinned Lean returns from `is_def_eq_core` on either answer of
//! `is_def_eq_proof_irrel` (`type_checker.cpp@v4.30.0-rc2:1087-1088`,
//! `@v4.35.0:1163-1164`): two proofs whose propositions differ are unequal at
//! once, without unfolding either proof.
//!
//! The fixture mirrors the pinned-Lean measurements of the plan item
//! `kernel-proof-irrel-three-valued`
//! (`docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`). `slowRefl m : m = m` is
//! proved by an `m`-step `Nat.rec`, so unfolding it costs Θ(m). On v4.30.0-rc2
//! and v4.33.1, `Kernel.isDefEq (slowRefl n) (slowRefl (n+1))` is false at 28
//! heartbeats and `f n (slowRefl n) =?= f (n+1) (slowRefl (n+1))` is true at
//! 50, at both n = 1,000 and n = 100,000. Every declaration below that the
//! kernel must accept or refuse is one pinned Lean accepts or refuses. The Lean
//! sources and their outputs on both toolchains are in
//! `reports/proof-irrel-three-valued-2026-10-17/` (`m_<version>.txt` for the
//! heartbeats; `Controls*`, `cc_*` and `IdxShape_*` for the verdicts and the
//! motive's shape); its README gives the command.

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::{TypeChecker, TypeError};
use crate::work_meter::stats::{self, WorkStats};

const N_SMALL: u64 = 1_000;
const N_LARGE: u64 = 100_000;
/// Finite (a limit of 0 disables counting) and far above the unfolding route's
/// cost at `N_LARGE`, so that route finishes and shows its cost.
const LIMIT: u32 = 50_000_000;

/// How the `Nat.rec` proof of `m = m` spells its motive.
#[derive(Clone, Copy, Debug)]
enum Shape {
    /// `fun _ => m = m`. Unfolded at a count of at least 2^16, the closed-fold
    /// guard (`native_closed_fold_grind_stuck`) leaves this `Nat.rec` stuck.
    SlowRefl,
    /// `fun k => (fun _ => m = m) k`. The motive body has a loose bvar, so no
    /// guard fires at any count. Pinned Lean keeps this redex as written.
    SlowReflIdx,
}

const SHAPES: [Shape; 2] = [Shape::SlowRefl, Shape::SlowReflIdx];

impl Shape {
    fn name(self) -> &'static str {
        match self {
            Shape::SlowRefl => "slowRefl",
            Shape::SlowReflIdx => "slowReflIdx",
        }
    }
}

fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat() -> Expr {
    konst("Nat")
}

fn lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

fn level_one() -> Level {
    Level::succ(Level::zero())
}

/// `@Eq.{1} Nat lhs rhs`
fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![level_one()]);
    Expr::apps(eq, [nat(), lhs, rhs])
}

/// `@Eq.refl.{1} Nat value`
fn refl_nat(value: Expr) -> Expr {
    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![level_one()]);
    Expr::apps(refl, [nat(), value])
}

/// `@Eq.{0} prop lhs rhs`: equality of two proofs of `prop`.
fn eq_proofs(prop: Expr, lhs: Expr, rhs: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::zero()]);
    Expr::apps(eq, [prop, lhs, rhs])
}

/// `@Eq.refl.{0} prop proof`
fn refl_proof(prop: Expr, proof: Expr) -> Expr {
    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::zero()]);
    Expr::apps(refl, [prop, proof])
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

/// `(m : Nat) → m = m`
fn slow_refl_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat(),
        eq_nat(Expr::bvar(0), Expr::bvar(0)),
    )
}

/// `fun m => Nat.rec.{0} (motive) (Eq.refl m) (fun _ ih => ih) m`
fn slow_refl_value(shape: Shape) -> Expr {
    // Under `fun m`, m is #0; under the motive's binder it is #1.
    let motive = match shape {
        Shape::SlowRefl => lam(nat(), eq_nat(Expr::bvar(1), Expr::bvar(1))),
        Shape::SlowReflIdx => lam(
            nat(),
            Expr::app(
                lam(nat(), eq_nat(Expr::bvar(2), Expr::bvar(2))),
                Expr::bvar(0),
            ),
        ),
    };
    let step = lam(
        nat(),
        lam(eq_nat(Expr::bvar(1), Expr::bvar(1)), Expr::bvar(0)),
    );
    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let body = Expr::apps(rec, [motive, refl_nat(Expr::bvar(0)), step, Expr::bvar(0)]);
    lam(nat(), body)
}

/// `(m : Nat) → m = m → Nat`
fn consumer_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(
            BinderInfo::Default,
            eq_nat(Expr::bvar(0), Expr::bvar(0)),
            nat(),
        ),
    )
}

/// A non-reducible definition, like Lean's `noncomputable def`. A theorem
/// carries Opaque hints and never enters lazy delta, which would hide the
/// unfolding route these tests measure.
fn definition(name: &str, type_: Expr, value: Expr, is_reducible: bool) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible,
    }
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// `slowRefl`, `slowReflIdx`, `f := fun _ _ => 0` and `g := fun m _ => m`.
fn fixture_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    for shape in SHAPES {
        env.add_decl(definition(
            shape.name(),
            slow_refl_type(),
            slow_refl_value(shape),
            false,
        ))
        .expect("slowRefl fixture");
    }
    let f = lam(nat(), lam(eq_nat(Expr::bvar(0), Expr::bvar(0)), lit(0)));
    let g = lam(
        nat(),
        lam(eq_nat(Expr::bvar(0), Expr::bvar(0)), Expr::bvar(1)),
    );
    for (name, value) in [("f", f), ("g", g)] {
        env.add_decl(definition(name, consumer_type(), value, false))
            .expect("consumer fixture");
    }
    env
}

/// `slowRefl n` (or `slowReflIdx n`), a proof of `n = n`.
fn sr(shape: Shape, n: u64) -> Expr {
    Expr::app(konst(shape.name()), lit(n))
}

/// `head n (sr n)` for a consumer `head` of `f` or `g`.
fn consume(head: &str, shape: Shape, n: u64) -> Expr {
    Expr::apps(konst(head), [lit(n), sr(shape, n)])
}

#[derive(Debug)]
struct Cost {
    answer: bool,
    spent: u32,
    work: WorkStats,
}

/// One `is_def_eq` on a fresh environment and checker, so no cache carries
/// over from another measurement.
fn measure(lhs: &Expr, rhs: &Expr) -> Cost {
    let env = fixture_env();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(LIMIT);
    let _ = stats::take();
    let answer = tc.is_def_eq(lhs, rhs);
    let work = stats::take();
    let spent = LIMIT - tc.heartbeat_remaining();
    assert!(
        !tc.heartbeat_spent(),
        "the budget must not decide the answer"
    );
    Cost {
        answer,
        spent,
        work,
    }
}

/// The comparison `pair(n)` gives `expected` at both counts, at the same
/// heartbeat count and the same kernel work.
fn assert_flat_in_n(label: &str, expected: bool, pair: impl Fn(u64) -> (Expr, Expr)) {
    // Warm-up on this thread: absorbs one-time lazy and thread-local setup.
    let (lhs, rhs) = pair(N_SMALL);
    let _ = measure(&lhs, &rhs);
    let [small, large] = [N_SMALL, N_LARGE].map(|n| {
        let (lhs, rhs) = pair(n);
        measure(&lhs, &rhs)
    });
    // The figures the decision record quotes; `--nocapture` prints them.
    eprintln!("{label}: n = {N_SMALL}: {small:?}; n = {N_LARGE}: {large:?}");
    for (n, cost) in [(N_SMALL, &small), (N_LARGE, &large)] {
        assert_eq!(cost.answer, expected, "{label} at n = {n}: {cost:?}");
        assert!(
            cost.work.step_ticks > 0,
            "{label} at n = {n} must reach the def-eq algorithm: {cost:?}"
        );
    }
    assert!(
        small.spent == large.spent && small.work == large.work,
        "{label}: the cost must not depend on n\n  n = {N_SMALL}: {} heartbeats, {:?}\n  \
         n = {N_LARGE}: {} heartbeats, {:?}",
        small.spent,
        small.work,
        large.spent,
        large.work
    );
}

fn proof_irrel_answer(env: &Environment, lhs: &Expr, rhs: &Expr) -> Option<bool> {
    TypeChecker::new(env).is_def_eq_proof_irrel(lhs, rhs)
}

#[test]
fn test_proof_irrel_refutes_slow_refl_with_counts_independent_of_n() {
    let env = fixture_env();
    for n in [N_SMALL, N_LARGE] {
        let (lhs, rhs) = (sr(Shape::SlowRefl, n), sr(Shape::SlowRefl, n + 1));
        assert_eq!(proof_irrel_answer(&env, &lhs, &rhs), Some(false));
    }
    assert_flat_in_n("slowRefl n =?= slowRefl (n+1)", false, |n| {
        (sr(Shape::SlowRefl, n), sr(Shape::SlowRefl, n + 1))
    });
}

#[test]
fn test_proof_irrel_false_inside_same_head_args_keeps_f_true_with_counts_independent_of_n() {
    for shape in SHAPES {
        let label = format!("f n ({0} n) =?= f (n+1) ({0} (n+1))", shape.name());
        assert_flat_in_n(&label, true, |n| {
            (consume("f", shape, n), consume("f", shape, n + 1))
        });
    }
}

#[test]
fn test_proof_irrel_false_inside_same_head_args_refutes_g_with_counts_independent_of_n() {
    for shape in SHAPES {
        let label = format!("g n ({0} n) =?= g (n+1) ({0} (n+1))", shape.name());
        assert_flat_in_n(&label, false, |n| {
            (consume("g", shape, n), consume("g", shape, n + 1))
        });
    }
}

#[test]
fn test_proof_irrel_refutes_guard_free_slow_refl_counts_independent_of_n() {
    let env = fixture_env();
    for n in [N_SMALL, N_LARGE] {
        let (lhs, rhs) = (sr(Shape::SlowReflIdx, n), sr(Shape::SlowReflIdx, n + 1));
        assert_eq!(proof_irrel_answer(&env, &lhs, &rhs), Some(false));
    }
    assert_flat_in_n("slowReflIdx n =?= slowReflIdx (n+1)", false, |n| {
        (sr(Shape::SlowReflIdx, n), sr(Shape::SlowReflIdx, n + 1))
    });
}

#[test]
fn test_proof_irrel_true_answer_is_constant_in_n() {
    let env = fixture_env();
    for shape in SHAPES {
        for n in [N_SMALL, N_LARGE] {
            let answer = proof_irrel_answer(&env, &sr(shape, n), &refl_nat(lit(n)));
            assert_eq!(answer, Some(true), "{} {n}", shape.name());
        }
        let label = format!("{} n =?= Eq.refl n", shape.name());
        assert_flat_in_n(&label, true, |n| (sr(shape, n), refl_nat(lit(n))));
    }
}

/// `P : Nat.add 500 500 = 1000`, `Q : 1000 = 1000`, `R : 1001 = 1001`.
/// Pinned Lean: `P ≡ Q`, `Q ≡ P`, `Q ≢ R`, `P ≢ R`.
fn axiom_env() -> Environment {
    let mut env = fixture_env();
    let sum = Expr::apps(konst("Nat.add"), [lit(500), lit(500)]);
    for (name, type_) in [
        ("P", eq_nat(sum, lit(1000))),
        ("Q", eq_nat(lit(1000), lit(1000))),
        ("R", eq_nat(lit(1001), lit(1001))),
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

#[test]
fn test_proof_irrel_defeq_distinct_prop_types_stay_equal() {
    let env = axiom_env();
    let (p, q, r) = (konst("P"), konst("Q"), konst("R"));
    assert_eq!(proof_irrel_answer(&env, &p, &q), Some(true));
    assert_eq!(proof_irrel_answer(&env, &q, &r), Some(false));
    let tc = TypeChecker::new(&env);
    assert!(tc.is_def_eq(&p, &q), "P ≡ Q: their propositions are defeq");
    assert!(tc.is_def_eq(&q, &p), "Q ≡ P");
    assert!(!tc.is_def_eq(&q, &r), "Q ≢ R");
    assert!(!tc.is_def_eq(&p, &r), "P ≢ R");
}

#[test]
fn test_kernel_accepts_what_pinned_lean_accepts_proof_irrel_shapes() {
    let mut env = fixture_env();
    for shape in SHAPES {
        for n in [N_SMALL, N_LARGE] {
            let tag = format!("{}_{n}", shape.name());
            // refutes : f n (sr n) = f (n+1) (sr (n+1)) := rfl
            let refutes = theorem(
                &format!("refutes_{tag}"),
                eq_nat(consume("f", shape, n), consume("f", shape, n + 1)),
                refl_nat(consume("f", shape, n)),
            );
            env.add_decl(refutes)
                .unwrap_or_else(|e| panic!("refutes_{tag}: pinned Lean accepts it: {e:?}"));
            // same_prop : @Eq (n = n) (sr n) (Eq.refl n) := rfl
            let prop = eq_nat(lit(n), lit(n));
            let same_prop = theorem(
                &format!("same_prop_{tag}"),
                eq_proofs(prop.clone(), sr(shape, n), refl_nat(lit(n))),
                refl_proof(prop, sr(shape, n)),
            );
            env.add_decl(same_prop)
                .unwrap_or_else(|e| panic!("same_prop_{tag}: pinned Lean accepts it: {e:?}"));
        }
    }
}

/// The declaration is refused as a type mismatch, never by a spent budget:
/// pinned Lean refuses it with "(kernel) declaration type mismatch".
fn assert_refused_as_mismatch(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    match env.add_decl(theorem(name, type_, value)) {
        Err(EnvError::TypeCheckFailed {
            name: failed,
            source: TypeError::TypeMismatch { .. },
        }) => assert_eq!(failed, Name::from_string(name)),
        other => panic!("{name}: pinned Lean refuses it as a type mismatch; Clean: {other:?}"),
    }
}

#[test]
fn test_kernel_rejects_what_pinned_lean_rejects_proof_irrel_shapes() {
    let mut env = fixture_env();
    for shape in SHAPES {
        for n in [N_SMALL, N_LARGE] {
            let tag = format!("{}_{n}", shape.name());
            // carrier_bad : @Eq (n = n) (sr n) (sr n) := @Eq.refl (n+1 = n+1) (sr (n+1))
            let next = n + 1;
            assert_refused_as_mismatch(
                &mut env,
                &format!("carrier_bad_{tag}"),
                eq_proofs(eq_nat(lit(n), lit(n)), sr(shape, n), sr(shape, n)),
                refl_proof(eq_nat(lit(next), lit(next)), sr(shape, next)),
            );
            // f_one_bad : f n (sr n) = 1 := rfl
            assert_refused_as_mismatch(
                &mut env,
                &format!("f_one_bad_{tag}"),
                eq_nat(consume("f", shape, n), lit(1)),
                refl_nat(consume("f", shape, n)),
            );
            // g_bad : g n (sr n) = g (n+1) (sr (n+1)) := rfl. The same-head
            // arguments attempt meets the proof pair first, at the changed line.
            assert_refused_as_mismatch(
                &mut env,
                &format!("g_bad_{tag}"),
                eq_nat(consume("g", shape, n), consume("g", shape, next)),
                refl_nat(consume("g", shape, n)),
            );
        }
    }
}

#[path = "proof_irrel_three_valued_modes_tests.rs"]
mod modes;
