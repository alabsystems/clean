// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Int.instMin` / `Int.instMax` through the kernel: registered as checked,
//! axiom-free instances; they COMPUTE on literals; and on open arguments each
//! is definitionally Lean's `minOfLe` / `maxOfLe` body — the equation Lean
//! 4.8.0 proves by `rfl` (`Int.min_def` / `Int.max_def`) holds, and the
//! swapped one Lean refuses does not.

use super::*;
use crate::env::types::ConstantKind;
use crate::tc::TypeChecker;

fn int() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

fn of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

/// `-(n + 1)`.
fn neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    )
}

/// `@Min.min Int Int.instMin a b` (resp. `Max.max` / `Int.instMax`).
fn extremum(class: &str, a: Expr, b: Expr) -> Expr {
    let (method, instance) = match class {
        "Min" => ("Min.min", "Int.instMin"),
        _ => ("Max.max", "Int.instMax"),
    };
    Expr::apps(
        Expr::const_(Name::from_string(method), vec![Level::zero()]),
        [
            int(),
            Expr::const_(Name::from_string(instance), vec![]),
            a,
            b,
        ],
    )
}

/// `fun (n m : Int) => <body n m>`, built over de Bruijn indices.
fn binary_fn(body: impl FnOnce(Expr, Expr) -> Expr) -> Expr {
    let n = Expr::bvar(1);
    let m = Expr::bvar(0);
    Expr::lam(
        BinderInfo::Default,
        int(),
        Expr::lam(BinderInfo::Default, int(), body(n, m)),
    )
}

/// `@ite Int (@LE.le Int instLEInt n m) (Int.decLe n m) t e`.
fn ite_le(n: &Expr, m: &Expr, t: Expr, e: Expr) -> Expr {
    let le = Expr::apps(
        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
        [
            int(),
            Expr::const_(Name::from_string("instLEInt"), vec![]),
            n.clone(),
            m.clone(),
        ],
    );
    let decision = Expr::apps(
        Expr::const_(Name::from_string("Int.decLe"), vec![]),
        [n.clone(), m.clone()],
    );
    Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [int(), le, decision, t, e],
    )
}

#[test]
fn test_int_minmax_instances_registered_checked_axiom_free() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (instance, class) in [("Int.instMin", "Min"), ("Int.instMax", "Max")] {
        let name = Name::from_string(instance);
        let info = env.get_const(&name).expect("instance is registered");
        assert_eq!(info.kind, ConstantKind::Definition, "{instance}");
        assert!(info.value.is_some(), "{instance} keeps its value");
        assert!(
            env.instances()
                .any(|i| i.name == name && i.class_name == Name::from_string(class)),
            "{instance} is registered as a {class} instance"
        );
        let deps = env.axiom_deps(&name).expect("registered");
        assert!(deps.is_empty(), "{instance}: axiom closure {deps:?}");
        let ty = tc
            .infer_type(&Expr::const_(name, vec![]))
            .expect("instance type-checks");
        let expected = Expr::app(
            Expr::const_(Name::from_string(class), vec![Level::zero()]),
            int(),
        );
        assert!(tc.is_def_eq(&ty, &expected), "{instance} : {class} Int");
    }
}

#[test]
fn test_int_minmax_compute_on_literals() {
    // Lean 4.8.0: `#eval (min (3:Int) (-2), max (3:Int) (-2))` = `(-2, 3)`.
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let min = extremum("Min", of_nat(3), neg_succ(1));
    assert!(tc.is_def_eq(&min, &neg_succ(1)));
    assert!(!tc.is_def_eq(&min, &of_nat(3)), "min 3 (-2) is not 3");
    let max = extremum("Max", of_nat(3), neg_succ(1));
    assert!(tc.is_def_eq(&max, &of_nat(3)));
    assert!(!tc.is_def_eq(&max, &neg_succ(1)), "max 3 (-2) is not -2");
    // Both orders, and a tie.
    assert!(tc.is_def_eq(&extremum("Min", neg_succ(1), of_nat(3)), &neg_succ(1)));
    assert!(tc.is_def_eq(&extremum("Max", neg_succ(1), of_nat(3)), &of_nat(3)));
    assert!(tc.is_def_eq(&extremum("Min", of_nat(2), of_nat(2)), &of_nat(2)));
}

#[test]
fn test_int_minmax_are_min_of_le_on_open_arguments() {
    // Lean 4.8.0 `Init/Data/Int/Order.lean`: `Int.min_def (n m : Int) :
    // min n m = if n ≤ m then n else m := rfl`, `Int.max_def … = if n ≤ m
    // then m else n := rfl`.
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let min_fn = binary_fn(|n, m| extremum("Min", n, m));
    let min_def = binary_fn(|n, m| ite_le(&n, &m, n.clone(), m.clone()));
    assert!(tc.is_def_eq(&min_fn, &min_def), "Int.min_def is rfl");
    let max_fn = binary_fn(|n, m| extremum("Max", n, m));
    let max_def = binary_fn(|n, m| ite_le(&n, &m, m.clone(), n.clone()));
    assert!(tc.is_def_eq(&max_fn, &max_def), "Int.max_def is rfl");

    // Negative controls Lean refuses (`type mismatch` at `rfl`): the swapped
    // branches.
    assert!(!tc.is_def_eq(&min_fn, &max_def));
    assert!(!tc.is_def_eq(&max_fn, &min_def));
}

#[test]
fn test_int_minmax_import_mode_is_not_seeded() {
    // Under `.olean` import Lean's genuine `Int.instMin` / `Int.instMax` must
    // win; a seeded instance would shadow them (first-registered-wins).
    let env = Environment::try_with_prelude_for_import().expect("import prelude builds");
    assert!(env.get_const(&Name::from_string("Int.instMin")).is_none());
    assert!(env.get_const(&Name::from_string("Int.instMax")).is_none());
}
