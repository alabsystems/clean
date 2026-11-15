// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Signed-Int automation probe. Tracks which Bool-form goals clean-auto discharges
// for Nat vs Int. The trust-wp kernel lane renders every ensures as `⟦clause⟧ = true`
// over Bool ops (Nat.beq/Nat.ble unsigned; Int.beq/Int.ble signed). Goal: the Int
// rows should reach parity with the Nat rows.
// Run: cargo test -p clean-auto --test int_automation_probe -- --nocapture

use std::time::{Duration, Instant};

use clean_auto::{AutomationEngine, InductionSearch};
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Environment, Expr, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn eq(ty: Expr, l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [ty, l, r],
    )
}
fn forall(ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body)
}
fn app(f: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(f), args)
}
/// Hang backstop of one asserted row. It never decides the row: fifteen times
/// the 8 s wall the whole pipeline met on an idle host, and when it fires the
/// row reports could-not-run, never "unproved".
const ROW_BACKSTOP: Duration = Duration::from_secs(120);

/// An asserted row, decided by counts (R-INDUCTION-BACKSTOP-20261014).
///
/// Every asserted goal is a `∀` over a data type, so `auto_prove` routes it to
/// the structural-induction lane first, and that lane is what proves it (the
/// flagship I1 by the non-recursive-eliminator field-induction fallback). Under
/// `auto_prove` the lane's backstop is the 8 s timeout (`engine_detailed.rs`
/// builds its `SearchStop` from it), and once it fires the pipeline stops
/// (`start.elapsed() >= query.timeout`), so a host too loaded to finish the
/// search in 8 s answered "unproved" (I1 did so on main). The counted entry
/// is decided by the lane's counts instead: `INDUCTION_FUEL`, the goal-depth
/// rail, the rewrite and synthesis depths, the SMT solver's 10,000-conflict
/// CDCL limit (`SMT_CONFLICT_LIMIT`), superposition's 10,000 given-clause
/// steps and the kernel's heartbeats. The clock is only `ROW_BACKSTOP`.
fn prove(engine: &AutomationEngine, env: &Environment, name: &str, goal: &Expr) -> bool {
    let backstop = Instant::now() + ROW_BACKSTOP;
    let (label, proved) = match engine.prove_by_induction_counted(env, goal, backstop) {
        InductionSearch::Proved(_) => ("PROVED ", true),
        InductionSearch::NotProved => ("unproved", false),
        InductionSearch::CountLimit(_) => ("count-limit", false),
        InductionSearch::BackstopFired => panic!(
            "COULD NOT RUN {name}: the {ROW_BACKSTOP:?} hang backstop fired before the \
             search's counts decided; this is not an answer about the goal"
        ),
    };
    println!("  [{label}] {name}");
    proved
}

/// A diagnostic row (I2, I3, M_ble: the known-open boundary). Nothing asserts
/// it, so it keeps the whole `auto_prove` pipeline under its 8 s wall, and its
/// answer decides nothing.
fn probe(engine: &AutomationEngine, env: &Environment, name: &str, goal: &Expr) {
    let ok = engine
        .auto_prove(env, goal, Duration::from_secs(8), None)
        .is_some();
    println!("  [{}] {}", if ok { "PROVED " } else { "unproved" }, name);
}

#[test]
fn int_automation_probe_battery() {
    let env = Environment::with_prelude();
    let engine = AutomationEngine::new();

    let bool_ty = c("Bool");
    let btrue = c("Bool.true");
    let nat = c("Nat");
    let int = c("Int");
    let zero_nat = Expr::nat_lit(0);
    let int_zero = app("Int.ofNat", [Expr::nat_lit(0)]);
    let v = Expr::bvar(0);

    println!("\n=== Nat Bool-form (the working unsigned analog) ===");
    let n1 = prove(
        &engine,
        &env,
        "N1 ∀n, Nat.beq n n = true",
        &forall(
            nat.clone(),
            eq(
                bool_ty.clone(),
                app("Nat.beq", [v.clone(), v.clone()]),
                btrue.clone(),
            ),
        ),
    );
    let n2 = prove(
        &engine,
        &env,
        "N2 ∀n, Nat.ble n n = true",
        &forall(
            nat.clone(),
            eq(
                bool_ty.clone(),
                app("Nat.ble", [v.clone(), v.clone()]),
                btrue.clone(),
            ),
        ),
    );
    let n3 = prove(
        &engine,
        &env,
        "N3 ∀n, Nat.beq (n+0) n = true",
        &forall(
            nat.clone(),
            eq(
                bool_ty.clone(),
                app(
                    "Nat.beq",
                    [app("Nat.add", [v.clone(), zero_nat.clone()]), v.clone()],
                ),
                btrue.clone(),
            ),
        ),
    );

    println!("\n=== Int Bool-form (what the signed lane emits) ===");
    let i1 = prove(
        &engine,
        &env,
        "I1 ∀x, Int.beq x x = true",
        &forall(
            int.clone(),
            eq(
                bool_ty.clone(),
                app("Int.beq", [v.clone(), v.clone()]),
                btrue.clone(),
            ),
        ),
    );
    probe(
        &engine,
        &env,
        "I2 ∀x, Int.ble x x = true",
        &forall(
            int.clone(),
            eq(
                bool_ty.clone(),
                app("Int.ble", [v.clone(), v.clone()]),
                btrue.clone(),
            ),
        ),
    );
    probe(
        &engine,
        &env,
        "I3 ∀x, Int.beq (x+0) x = true",
        &forall(
            int.clone(),
            eq(
                bool_ty.clone(),
                app(
                    "Int.beq",
                    [app("Int.add", [v.clone(), int_zero.clone()]), v.clone()],
                ),
                btrue.clone(),
            ),
        ),
    );

    println!("\n=== diagnostic minors (Int.rec ofNat/negSucc slices) ===");
    let m_ofnat = prove(
        &engine,
        &env,
        "M_beq_ofNat ∀n, Int.beq (ofNat n)(ofNat n) = true",
        &forall(
            nat.clone(),
            eq(
                bool_ty.clone(),
                app(
                    "Int.beq",
                    [app("Int.ofNat", [v.clone()]), app("Int.ofNat", [v.clone()])],
                ),
                btrue.clone(),
            ),
        ),
    );
    let m_negsucc = prove(
        &engine,
        &env,
        "M_beq_negSucc ∀m, Int.beq (negSucc m)(negSucc m) = true",
        &forall(
            nat.clone(),
            eq(
                bool_ty.clone(),
                app(
                    "Int.beq",
                    [
                        app("Int.negSucc", [v.clone()]),
                        app("Int.negSucc", [v.clone()]),
                    ],
                ),
                btrue.clone(),
            ),
        ),
    );
    probe(
        &engine,
        &env,
        "M_ble_ofNat ∀n, Int.ble (ofNat n)(ofNat n) = true",
        &forall(
            nat.clone(),
            eq(
                bool_ty.clone(),
                app(
                    "Int.ble",
                    [app("Int.ofNat", [v.clone()]), app("Int.ofNat", [v.clone()])],
                ),
                btrue.clone(),
            ),
        ),
    );
    println!();

    // Regression guards for the signed-Int capability (Int.beq symbolic
    // reduction + the non-recursive-eliminator field-induction fallback):
    // the Nat analogs and the Int.beq goals — including the flagship I1
    // `∀x:Int, Int.beq x x = true` and both Int.rec minors — must PROVE.
    // I2/I3/M_ble (Int.ble / arithmetic) remain the known-open boundary and
    // are diagnostic-only (not asserted).
    assert!(
        n1 && n2 && n3,
        "Nat Bool-form regressed (N1/N2/N3 must prove)"
    );
    assert!(
        m_ofnat && m_negsucc,
        "Int.rec beq minors regressed (M_beq_ofNat/negSucc must prove)"
    );
    assert!(i1, "FLAGSHIP I1 `∀x:Int, Int.beq x x = true` must prove");
}
