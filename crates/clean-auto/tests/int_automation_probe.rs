// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Signed-Int automation probe. Tracks which Bool-form goals clean-auto discharges
// for Nat vs Int. The trust-wp kernel lane renders every ensures as `⟦clause⟧ = true`
// over Bool ops (Nat.beq/Nat.ble unsigned; Int.beq/Int.ble signed). Goal: the Int
// rows should reach parity with the Nat rows.
// Run: cargo test -p clean-auto --test int_automation_probe -- --nocapture

use std::time::Duration;

use clean_auto::AutomationEngine;
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
fn probe(engine: &AutomationEngine, env: &Environment, name: &str, goal: &Expr) -> bool {
    let ok = engine
        .auto_prove(env, goal, Duration::from_secs(8), None)
        .is_some();
    println!("  [{}] {}", if ok { "PROVED " } else { "unproved" }, name);
    ok
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
    let n1 = probe(
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
    let n2 = probe(
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
    let n3 = probe(
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
    let i1 = probe(
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
    let m_ofnat = probe(
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
    let m_negsucc = probe(
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
