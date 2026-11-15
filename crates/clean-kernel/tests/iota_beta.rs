// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use clean_kernel::env::Environment;
use clean_kernel::{BinderInfo, Expr, KernelTypeError, Level, Name, TypeChecker};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}
fn recursor(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())])
}
fn env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_bool().unwrap();
    env
}

#[test]
fn beta_telescope_preserves_dependent_domains_and_argument_order() {
    let env = env();
    let tc = TypeChecker::new(&env);
    // (fun (A : Type) (x : A) (y : A) => x) Nat 13
    let choose = lam(
        Expr::type_(),
        lam(Expr::bvar(0), lam(Expr::bvar(1), Expr::bvar(1))),
    );
    let partial = Expr::apps(choose, [c("Nat"), Expr::nat_lit(13)]);
    let expected = lam(c("Nat"), Expr::nat_lit(13));
    assert_eq!(tc.whnf(&partial), expected);
    let complete = Expr::app(partial, Expr::nat_lit(29));
    tc.check_type(&complete, &c("Nat")).unwrap();
    assert_eq!(tc.whnf(&complete), Expr::nat_lit(13));
}

#[test]
fn recursor_argument_orders_preserve_fields_and_recursive_result() {
    let env = env();
    for name in ["Nat.rec", "Nat.recOn"] {
        let tc = TypeChecker::new(&env);
        let motive = lam(c("Nat"), c("Nat"));
        // Returning the predecessor distinguishes the field from the IH.
        let successor = lam(c("Nat"), lam(c("Nat"), Expr::bvar(1)));
        let args = if name == "Nat.rec" {
            vec![motive, Expr::nat_lit(41), successor, Expr::nat_lit(3)]
        } else {
            vec![motive, Expr::nat_lit(3), Expr::nat_lit(41), successor]
        };
        let term = Expr::apps(recursor(name), args);
        tc.check_type(&term, &c("Nat")).unwrap();
        assert_eq!(tc.whnf(&term), Expr::nat_lit(2), "{name}");
        assert!(!tc.is_def_eq(&term, &Expr::nat_lit(41)));
    }
}

#[test]
fn recursor_extra_arguments_are_forwarded_in_order_for_both_layouts() {
    let env = env();
    for name in ["Nat.rec", "Nat.recOn"] {
        let tc = TypeChecker::new(&env);
        let value_ty = Expr::arrow(c("Nat"), Expr::arrow(c("Nat"), c("Nat")));
        let motive = lam(c("Nat"), value_ty.clone());
        let zero = lam(c("Nat"), lam(c("Nat"), Expr::bvar(1)));
        let successor = lam(c("Nat"), lam(value_ty, Expr::bvar(0)));
        let args = if name == "Nat.rec" {
            vec![motive, zero, successor, Expr::nat_lit(2)]
        } else {
            vec![motive, Expr::nat_lit(2), zero, successor]
        };
        let term = Expr::apps(
            Expr::apps(recursor(name), args),
            [Expr::nat_lit(13), Expr::nat_lit(29)],
        );
        tc.check_type(&term, &c("Nat")).unwrap();
        assert_eq!(tc.whnf(&term), Expr::nat_lit(13), "{name}");
        assert!(!tc.is_def_eq(&term, &Expr::nat_lit(29)));
    }
}

#[test]
fn beta_substitution_preserves_capture_under_a_remaining_binder() {
    let env = env();
    let tc = TypeChecker::new(&env);
    // fun outer => (fun x unused => x) outer
    let term = lam(
        c("Nat"),
        Expr::app(lam(c("Nat"), lam(c("Nat"), Expr::bvar(1))), Expr::bvar(0)),
    );
    let expected = lam(c("Nat"), lam(c("Nat"), Expr::bvar(1)));
    tc.check_type(
        &term,
        &Expr::arrow(c("Nat"), Expr::arrow(c("Nat"), c("Nat"))),
    )
    .unwrap();
    assert!(tc.is_def_eq(&term, &expected));
    assert!(!tc.is_def_eq(&term, &lam(c("Nat"), lam(c("Nat"), Expr::bvar(0)))));
}

#[test]
fn iota_optimization_does_not_admit_a_wrong_minor_type() {
    let env = env();
    let tc = TypeChecker::new(&env);
    let term = Expr::apps(
        recursor("Nat.rec"),
        [
            lam(c("Nat"), c("Nat")),
            c("Bool.true"),
            lam(c("Nat"), lam(c("Nat"), Expr::bvar(0))),
            Expr::nat_lit(0),
        ],
    );
    assert!(matches!(
        tc.check_type(&term, &c("Nat")),
        Err(KernelTypeError::TypeMismatch { .. })
    ));
}

#[test]
fn wrong_recursor_universe_arity_remains_stuck_and_rejected() {
    let env = env();
    let tc = TypeChecker::new(&env);
    let term = Expr::apps(
        c("Nat.rec"),
        [
            lam(c("Nat"), c("Nat")),
            Expr::nat_lit(13),
            lam(c("Nat"), lam(c("Nat"), Expr::bvar(0))),
            Expr::nat_lit(0),
        ],
    );
    assert_eq!(tc.whnf(&term), term);
    assert!(tc.check_type(&term, &c("Nat")).is_err());
}
