// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Search ROBUSTNESS regression tests for the native automation engine
// (`clean_auto::AutomationEngine::auto_prove`). These pin the two guarantees the
// capstone integration bench exposed as broken:
//
//   * BUG 1 — TIMEOUT IGNORED. A pathologically deep goal drove the induction
//     lane's kernel re-checks (`infer_type` + `is_def_eq` over the assembled
//     `@I.rec` term) for *minutes*, ignoring its soft timeout (a ~29-min runaway
//     was wall-killed in the capstone; a deep `∀`-telescope "solved" in ~261 s
//     against a 5 s budget). `auto_prove` must now ALWAYS return well within a
//     small grace of its timeout. Enforced by (a) a structural-depth rail that
//     declines a too-deep goal up front and (b) a wall-clock deadline polled
//     INSIDE the superposition saturation loop and at every induction-recursion /
//     premise-injection step.
//
//   * BUG 2 — STACK OVERFLOW. The same deep goals overflowed the prover (even on
//     a 1 GiB worker stack). The depth rail declines them GRACEFULLY (`None`)
//     before any recursive descent, so there is no panic / abort.
//
// SOUNDNESS: these are search-side robustness bounds only. Declining a goal
// returns `None` (an honest "could not prove"); it never fabricates a proof, and
// any proof that IS returned is still kernel-checked by the caller. The goals
// here are deliberately pathological rails — we WANT them declined, never solved.
//
// NOTE: this file is also `include!`d by a standalone trust-ir-free workspace
// (`bench-runner/tests/search_robustness_regression.rs`) so the exact same
// `#[test]`s compile + run inside a worktree, where the full-workspace lockfile
// collides on `clean-kernel`. Keep the header as regular `//` comments (not
// `//!`) so the `include!` stays legal — this guards against the "agent harness
// builds can hide a broken test target" failure mode.

use std::time::{Duration, Instant};

use clean_auto::AutomationEngine;
use clean_kernel::{BinderInfo, Environment, Expr, Level};

/// Soft timeout handed to `auto_prove`. The guarded search returns far inside
/// `TIMEOUT + GRACE`; the unguarded search took minutes (or did not terminate).
const TIMEOUT: Duration = Duration::from_secs(2);

/// Wall-clock grace above `TIMEOUT`. `TIMEOUT + GRACE` sits far below the minutes
/// the unguarded search took and far above the microseconds the guarded search
/// takes, so the bound catches a regression in either guard without flaking.
const GRACE: Duration = Duration::from_secs(28);

fn nat() -> Expr {
    Expr::const_str("Nat")
}

/// `@Eq.{1} Nat l r`.
fn nat_eq(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [nat(), l, r],
    )
}

fn forall_nat(body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat(), body)
}

/// `Nat`/`List`/`Eq` over the classical bootstrap — the same small real env the
/// integration bench's inductive goals use.
fn robustness_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_list().expect("init_list");
    env.init_classical().expect("init_classical");
    env
}

/// Run `auto_prove` on a 1 GiB worker thread (matching the integration bench: the
/// hard goals recurse deeply and the macOS 8 MiB default is too small for the
/// declined/​attempted boundary). Returns `(solved, elapsed)`. A scoped thread
/// lets the worker borrow `goal` without cloning. A stack overflow in the prover
/// would abort the whole process (caught as a test failure); a panic surfaces
/// through `join().expect(...)`.
fn run_bounded(env: &Environment, goal: &Expr, timeout: Duration) -> (bool, Duration) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1usize << 30)
            .spawn_scoped(s, || {
                let engine = AutomationEngine::new();
                let start = Instant::now();
                let result = engine.auto_prove(env, goal, timeout, None);
                (result.is_some(), start.elapsed())
            })
            .expect("spawn robustness worker")
            .join()
            .expect("robustness worker panicked (stack overflow / abort?)")
    })
}

/// `∀ x₁ … xₙ : Nat, x₁ = x₁` — a deep `∀`-telescope. With `n` large the goal
/// nests far past the search's structural-depth rail. The body is a reflexive
/// equation, so the goal is *true*: the UNGUARDED induction lane "solved" `n` in
/// the low thousands, but in ~minutes while ignoring its timeout. The guarded
/// lane must DECLINE it fast instead.
fn deep_forall_nat(n: u32) -> Expr {
    // x₁ is the outermost binder; under `n` binders its de Bruijn index is n-1.
    let x1 = Expr::bvar(n - 1);
    let mut goal = nat_eq(x1.clone(), x1);
    for _ in 0..n {
        goal = forall_nat(goal);
    }
    goal
}

/// `∀ x : Nat, succ^d x = succ^d x` — a deep application spine. Reflexive (true),
/// but nested `d` deep; the unguarded search ran for tens of seconds at d≈3000
/// (and risks a stack overflow deeper), the guarded one declines it fast.
fn deep_succ_nat(d: u32) -> Expr {
    let mut spine = Expr::bvar(0);
    for _ in 0..d {
        spine = Expr::app(Expr::const_str("Nat.succ"), spine);
    }
    forall_nat(nat_eq(spine.clone(), spine))
}

/// BUG 1: a goal that previously ran the prover away past its timeout now returns
/// within `TIMEOUT + GRACE` (assert wall-clock bounded) and returns `None`.
#[test]
fn auto_prove_deep_forall_is_wall_clock_bounded() {
    let env = robustness_env();
    // Far deeper than the depth rail; unguarded this "solved" in ~minutes.
    let goal = deep_forall_nat(2000);

    let (solved, elapsed) = run_bounded(&env, &goal, TIMEOUT);

    assert!(
        elapsed < TIMEOUT + GRACE,
        "auto_prove ignored its timeout on a deep ∀-telescope: ran {elapsed:?} \
         (bound {:?}) — the deadline/​depth guard regressed",
        TIMEOUT + GRACE,
    );
    assert!(
        !solved,
        "the deep ∀-telescope rail should be DECLINED (None), not solved — \
         a returned proof here means the depth guard let a runaway goal through",
    );
}

/// BUG 2: a deeply-nested goal that previously overflowed the prover now returns
/// `None` gracefully (no panic / abort) and within the wall bound.
#[test]
fn auto_prove_deep_succ_spine_declines_without_overflow() {
    let env = robustness_env();
    // A succ-spine far deeper than the depth rail; unguarded this was slow at
    // ~3000 and overflow-prone deeper. Reaching the assertions proves the worker
    // neither overflowed (process abort) nor panicked.
    let goal = deep_succ_nat(5000);

    let (solved, elapsed) = run_bounded(&env, &goal, TIMEOUT);

    assert!(
        elapsed < TIMEOUT + GRACE,
        "auto_prove ran a deep succ-spine for {elapsed:?} (bound {:?}) — \
         the deadline/​depth guard regressed",
        TIMEOUT + GRACE,
    );
    assert!(
        !solved,
        "the deep succ-spine rail should be DECLINED (None), not solved",
    );
}

/// A SHALLOW true inductive goal still solves — the depth rail is a robustness
/// bound, not a capability cap, and must not regress the lane's real reach.
#[test]
fn auto_prove_shallow_inductive_still_solves() {
    let env = robustness_env();
    // ∀ n : Nat, 0 + n = n — the lane's canonical base lemma (depth well under
    // the rail). Proven by `Nat.rec`; the returned term is kernel-checked here.
    let goal = forall_nat(nat_eq(
        Expr::apps(
            Expr::const_str("Nat.add"),
            [Expr::const_str("Nat.zero"), Expr::bvar(0)],
        ),
        Expr::bvar(0),
    ));

    let (solved, elapsed) = run_bounded(&env, &goal, TIMEOUT);

    assert!(
        elapsed < TIMEOUT + GRACE,
        "a shallow inductive goal should solve quickly, ran {elapsed:?}",
    );
    assert!(
        solved,
        "the depth rail must not decline a shallow real goal (0 + n = n) — \
         capability regression",
    );
}
