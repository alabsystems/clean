// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual 4.35 definitions, independently reviewed before admitting new
//! dependency-closed extension bindings. No review bootstrap is enabled here.

use clean_kernel::env::{native_fold_review, Environment};
use clean_kernel::tc::TypeChecker;
use clean_kernel::{Expr, LeanWorld, Level, Name};
use std::path::Path;

#[path = "extension_binding_lean435/forgeries.rs"]
mod forgeries;
#[path = "extension_binding_lean435/namespace.rs"]
mod namespace;
#[path = "extension_binding_lean435/oracle.rs"]
mod oracle;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn load() -> Environment {
    assert!(std::env::var_os("CLEAN_NATIVE_FOLD_REPIN").is_none());
    assert!(std::env::var_os("CLEAN_NATIVE_FOLD_BOOTSTRAP_LOAD").is_none());
    let world = LeanWorld::Lean435;
    let decision = clean_olean::source_world_for_file(Path::new("Bindings435.lean"), Some(world))
        .expect("the exact official 4.35 library is required");
    let Ok(clean_olean::ImportWorld::Explicit { lib, .. }) = decision.imports() else {
        panic!("an explicit official library is required")
    };
    let mut env = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut env, world.tag()).unwrap();
    clean_olean::load_module_with_deps(&mut env, "Init.Data.UInt.Basic", std::slice::from_ref(lib))
        .expect("the genuine UInt/Char prerequisites must load without a fold-authority bypass");
    assert_eq!(clean_olean::environment_world(&env), Some(world.tag()));
    assert_eq!(
        env.get_inductive(&n("Decidable"))
            .unwrap()
            .constructor_names,
        vec![n("Decidable.intro")]
    );
    env
}

fn production_equal(env: &Environment, term: &Expr, answer: &Expr, ty: &Expr) -> bool {
    production_comparison(env, term, answer, ty, true)
}

fn production_comparison(
    env: &Environment,
    term: &Expr,
    answer: &Expr,
    ty: &Expr,
    expect_equal: bool,
) -> bool {
    let mut checker = TypeChecker::new(env);
    checker.set_heartbeat_limit(native_fold_review::REVIEW_HEARTBEATS);
    let typed = checker.check_type(term, ty).is_ok() && checker.check_type(answer, ty).is_ok();
    let equal = typed && checker.is_def_eq(term, answer);
    // Observe persistent budget/world errors even when defeq returned true.
    let finished = checker.infer_type(&Expr::sort(Level::zero())).is_ok();
    eprintln!("PRODUCTION typed={typed} equal={equal} finished={finished}");
    typed && equal == expect_equal && finished
}

#[test]
fn genuine_435_div_mod_and_character_definition_reviews() {
    let env = load();
    let mut passed = true;
    for key in ["Nat.div", "Nat.mod", "Char.ofNat"] {
        let review = native_fold_review::review(&env, &n(key), true);
        eprintln!("LEAN435_REVIEW {key}: {review:#?}");
        let expected = if key == "Char.ofNat" { 17 } else { 169 };
        passed &= review.cases == expected
            && review.fired == expected
            && review.unanswered == 0
            && review.passed();
    }
    assert!(passed, "one or more actual-definition review legs failed");
}

#[test]
fn genuine_435_ordinary_production_large_nat_and_zero_divisors() {
    let env = load();
    let mut passed = true;
    // Independent u128 arithmetic, rather than the kernel's BigNat operations.
    // The shared review skips D/P on values >1000; every P leg here executes.
    for (a, b) in [
        (0, 0),
        (37, 0),
        (37, 1),
        (37, 6),
        (1_u128 << 100, 0),
        ((1_u128 << 100) + 19, 3),
        ((1_u128 << 100) + 19, (1_u128 << 64) + 1),
        (u128::MAX, (1_u128 << 64) + 1),
        ((1_u128 << 64) + 1, (1_u128 << 100) + 19),
    ] {
        for key in ["Nat.div", "Nat.mod"] {
            if let Err(reason) = native_fold_review::fold_row_fires(&env, &n(key)) {
                eprintln!("LEAN435_LARGE_P UNEXECUTED {key}: {reason}");
                passed = false;
                continue;
            }
            let expected = if key == "Nat.div" {
                a.checked_div(b).unwrap_or(0)
            } else {
                a.checked_rem(b).unwrap_or(a)
            };
            let term = Expr::apps(c(key), [Expr::nat_lit_u128(a), Expr::nat_lit_u128(b)]);
            eprintln!("LEAN435_LARGE_P {key} {a} {b} expected={expected}");
            passed &= production_equal(&env, &term, &Expr::nat_lit_u128(expected), &c("Nat"));
            passed &= production_comparison(
                &env,
                &term,
                &Expr::nat_lit_u128(expected + 1),
                &c("Nat"),
                false,
            );
        }
    }
    assert!(
        passed,
        "ordinary production large-Nat/zero-divisor leg failed"
    );
}

fn expansion(text: &str) -> Expr {
    let mut list = Expr::app(Expr::const_(n("List.nil"), vec![Level::zero()]), c("Char"));
    for ch in text.chars().rev() {
        list = Expr::apps(
            Expr::const_(n("List.cons"), vec![Level::zero()]),
            [
                c("Char"),
                Expr::app(c("Char.ofNat"), Expr::nat_lit(u64::from(u32::from(ch)))),
                list,
            ],
        );
    }
    Expr::app(c("String.ofList"), list)
}

#[test]
fn genuine_435_ordinary_production_literal_boundaries() {
    let env = load();
    let mut passed = true;
    // The specialized literal review has reference D/I legs only. These are
    // additional ordinary-production checks; no test theory override occurs.
    for cp in [
        0,
        0x41,
        0xD7FF,
        0xD800,
        0xDFFF,
        0xE000,
        0x10FFFF,
        0x110000,
        0x7FFF_FFFF,
    ] {
        let expected = if cp < 0xD800 || (0xDFFF < cp && cp < 0x110000) {
            cp
        } else {
            0
        };
        let read = Expr::app(
            c("Char.toNat"),
            Expr::app(c("Char.ofNat"), Expr::nat_lit(cp)),
        );
        eprintln!("LEAN435_CHAR_P {cp:#x} expected={expected:#x}");
        passed &= production_equal(&env, &read, &Expr::nat_lit(expected), &c("Nat"));
    }
    for text in ["", "ab", "a b\n", "héllo", "Ä\u{3000}", "😀z", "\u{10ffff}"] {
        let literal = Expr::str_lit(text);
        let expanded = expansion(text);
        eprintln!("LEAN435_STRING_P {text:?}");
        passed &= production_equal(&env, &literal, &expanded, &c("String"));
        passed &= production_equal(&env, &expanded, &literal, &c("String"));
        let wrong = expansion(&format!("{text}x"));
        let mut checker = TypeChecker::new(&env);
        checker.set_heartbeat_limit(native_fold_review::REVIEW_HEARTBEATS);
        assert!(checker.check_type(&wrong, &c("String")).is_ok());
        assert!(
            !checker.is_def_eq(&literal, &wrong),
            "distinct strings identified"
        );
        assert!(checker.infer_type(&Expr::sort(Level::zero())).is_ok());
    }
    assert!(passed, "ordinary production literal leg failed");
}
