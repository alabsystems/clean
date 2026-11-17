// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr, Name, TypeChecker};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn call(n: usize, argument: Expr) -> Expr {
    Expr::app(c(&format!("alias{n}")), argument)
}
fn aliases() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let ty = Expr::arrow(c("Nat"), c("Nat"));
    for n in 0..=20 {
        let value = if n == 0 {
            Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(0))
        } else {
            c(&format!("alias{}", n - 1))
        };
        env.add_decl(Declaration::Definition {
            name: Name::from_string(&format!("alias{n}")),
            level_params: vec![],
            type_: ty.clone(),
            value,
            is_reducible: true,
        })
        .unwrap();
    }
    env
}

#[test]
fn whnf_cache_keys_include_all_arguments() {
    let env = aliases();
    let tc = TypeChecker::new(&env);
    assert_eq!(tc.whnf(&call(20, Expr::nat_lit(13))), Expr::nat_lit(13));
    assert_eq!(tc.whnf(&call(15, Expr::nat_lit(29))), Expr::nat_lit(29));
    assert!(!tc.is_def_eq(&call(15, Expr::nat_lit(29)), &Expr::nat_lit(13)));
}

#[test]
fn an_exhausted_delta_path_is_not_retained_as_completed() {
    let env = aliases();
    let mut tc = TypeChecker::new(&env);
    let term = call(20, Expr::nat_lit(13));
    tc.set_heartbeat_limit(3);
    assert_ne!(tc.whnf(&term), Expr::nat_lit(13));
    assert!(tc.heartbeat_spent());
    assert_eq!(tc.whnf_cache_entries(), 0);
    tc.set_heartbeat_limit(10_000);
    assert_eq!(tc.whnf(&term), Expr::nat_lit(13));
    assert!(!tc.heartbeat_spent());
}

#[test]
fn whnf_cache_does_not_confuse_retired_and_new_binders() {
    let env = aliases();
    let tc = TypeChecker::new(&env);
    let old = tc.push_binder_local(Name::from_string("old"), c("Nat"), BinderInfo::Default);
    assert_eq!(tc.whnf(&call(20, Expr::fvar(old))), Expr::fvar(old));
    tc.pop_binder_local();
    let new = tc.push_binder_local(Name::from_string("new"), c("Nat"), BinderInfo::Default);
    assert_ne!(old, new);
    let term = call(15, Expr::fvar(new));
    assert_eq!(tc.whnf(&term), Expr::fvar(new));
    tc.check_type(&term, &c("Nat")).unwrap();
    assert!(!tc.is_def_eq(&Expr::fvar(new), &Expr::nat_lit(13)));
    tc.pop_binder_local();
}

#[test]
fn completed_closed_nat_reductions_avoid_rewalking_alias_spines() {
    let env = aliases();
    let left = call(20, Expr::nat_lit(13));
    let right = call(15, Expr::nat_lit(13));
    let wrong = call(15, Expr::nat_lit(29));
    let mut cold = TypeChecker::new(&env);
    cold.set_heartbeat_limit(1);
    assert!(!cold.is_def_eq(&left, &right));
    assert!(cold.heartbeat_spent());

    let mut warm = TypeChecker::new(&env);
    assert_eq!(warm.whnf(&left), Expr::nat_lit(13));
    assert_eq!(warm.whnf(&right), Expr::nat_lit(13));
    assert_eq!(warm.whnf(&wrong), Expr::nat_lit(29));
    warm.set_heartbeat_limit(1);
    assert!(warm.is_def_eq(&left, &right));
    assert!(!warm.heartbeat_spent());
    assert!(!warm.is_def_eq(&left, &wrong));
    assert!(!warm.heartbeat_spent());
}

#[test]
fn completed_nat_answers_do_not_cross_a_theory_change() {
    let env = aliases();
    let left = call(20, Expr::nat_lit(13));
    let right = call(15, Expr::nat_lit(13));
    let mut checker = TypeChecker::new(&env);
    assert_eq!(checker.whnf(&left), Expr::nat_lit(13));
    assert_eq!(checker.whnf(&right), Expr::nat_lit(13));
    checker.set_kernel_theory(clean_kernel::env::KernelTheory::Lean);
    checker.set_heartbeat_limit(1);
    assert!(!checker.is_def_eq(&left, &right));
    assert!(checker.heartbeat_spent());
    let mut recomputed = TypeChecker::new(&env);
    recomputed.set_kernel_theory(clean_kernel::env::KernelTheory::Lean);
    recomputed.set_heartbeat_limit(10_000);
    assert!(recomputed.is_def_eq(&left, &right));
    assert!(!recomputed.heartbeat_spent());
}
