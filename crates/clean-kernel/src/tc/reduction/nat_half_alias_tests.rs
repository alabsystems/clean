// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::env::{Declaration, Environment, KernelTheory};

fn call(name: &str, input: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string(name), vec![]), input)
}

#[test]
fn actual_halving_computes_at_word_boundaries_and_nested_closed_inputs() {
    let env = Environment::with_prelude();
    for (input, expected) in [
        (0u128, 0u128),
        (1, 0),
        (2, 1),
        (3, 1),
        (4_294_967_295, 2_147_483_647),
        (18_446_744_073_709_551_615, 9_223_372_036_854_775_807),
        (
            u128::MAX,
            170_141_183_460_469_231_731_687_303_715_884_105_727,
        ),
    ] {
        let tc = TypeChecker::new(&env);
        let term = call("Nat.div2", Expr::nat_lit_u128(input));
        assert!(tc.reduce_unary_shift_alias(&term).is_some());
        assert!(tc.is_def_eq(&term, &Expr::nat_lit_u128(expected)));
        assert!(!tc.heartbeat_spent());
    }
    let tc = TypeChecker::new(&env);
    let nested = call("Nat.div2", call("Nat.div2", Expr::nat_lit(u64::MAX)));
    assert!(tc.is_def_eq(&nested, &Expr::nat_lit(4_611_686_018_427_387_903u64)));
    assert!(!tc.heartbeat_spent());
}

#[test]
fn open_wrong_level_and_other_unary_calls_do_not_use_the_alias() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    assert!(tc
        .reduce_unary_shift_alias(&call("Nat.div2", Expr::bvar(0)))
        .is_none());
    assert!(tc
        .reduce_unary_shift_alias(&call("Nat.div2Par", Expr::nat_lit(3)))
        .is_none());
    let wrong_level = Expr::app(
        Expr::const_(Name::from_string("Nat.div2"), vec![Level::zero()]),
        Expr::nat_lit(3),
    );
    assert!(tc.reduce_unary_shift_alias(&wrong_level).is_none());
    assert!(!tc.unary_shift_alias_verified.get());
}

#[test]
fn the_universal_identity_refuses_the_wrong_shift_and_survives_theory_reset() {
    let env = Environment::with_prelude();
    let mut tc = TypeChecker::new(&env);
    let lhs = call("Nat.div2", Expr::bvar(0));
    let rhs = Expr::apps(
        Expr::const_(names::NAT_SHIFT_RIGHT.clone(), vec![]),
        [Expr::bvar(0), Expr::nat_lit(2)],
    );
    let one = vec![Level::succ(Level::zero())];
    let claim = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), one.clone()),
            [nat(), lhs.clone(), rhs],
        ),
    );
    let proof = lambda(
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), one),
            [nat(), lhs],
        ),
    );
    assert!(tc.check_type(&proof, &claim).is_err());
    assert!(!tc.heartbeat_spent());
    assert!(tc
        .reduce_unary_shift_alias(&call("Nat.div2", Expr::nat_lit(3)))
        .is_some());
    assert!(tc.unary_shift_alias_verified.get());
    tc.set_kernel_theory(KernelTheory::LeanReference);
    assert!(!tc.unary_shift_alias_verified.get());
    assert!(tc.is_def_eq(&call("Nat.div2", Expr::nat_lit(3)), &Expr::nat_lit(1)));
    assert!(!tc.heartbeat_spent());
}

fn counterfeit_environment(changed_base: bool) -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("Nat foundation");
    let alias = Name::from_string("Counterfeit.half");
    env.add_decl(Declaration::Definition {
        name: alias.clone(),
        level_params: vec![],
        type_: Expr::arrow(nat(), nat()),
        value: lambda(nat(), Expr::nat_lit(0)),
        is_reducible: true,
    })
    .expect("independent false halving function");
    let iterator = Name::from_string("Counterfeit.iterator");
    let mut value = iterator_value(&alias);
    if changed_base {
        // Preserve a well-typed iterator, but change its zero-step result.
        let ExprKind::Lam(_, _, body) = value.kind() else {
            panic!("iterator lambda")
        };
        let mut args: Vec<Expr> = body.get_app_args().iter().map(|e| (*e).clone()).collect();
        args[1] = lambda(nat(), call("Nat.succ", Expr::bvar(0)));
        value = lambda(nat(), Expr::apps(body.get_app_fn().clone(), args));
    }
    env.add_decl(Declaration::Definition {
        name: iterator.clone(),
        level_params: vec![],
        type_: Expr::arrow(nat(), Expr::arrow(nat(), nat())),
        value,
        is_reducible: true,
    })
    .expect("well-typed counterfeit iterator");
    assert!(env.discharge_axiom_for_redefinition(&names::NAT_SHIFT_RIGHT));
    env.add_decl(Declaration::Definition {
        name: names::NAT_SHIFT_RIGHT.clone(),
        level_params: vec![],
        type_: Expr::arrow(nat(), Expr::arrow(nat(), nat())),
        value: lambda(
            nat(),
            lambda(
                nat(),
                Expr::apps(
                    Expr::const_(iterator, vec![]),
                    [Expr::bvar(0), Expr::bvar(1)],
                ),
            ),
        ),
        is_reducible: true,
    })
    .expect("well-typed counterfeit shift definition");
    env
}

#[test]
fn an_exact_hint_never_authorizes_counterfeit_arithmetic() {
    let env = counterfeit_environment(false);
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.derive_unary_shift_alias(),
        Some(Name::from_string("Counterfeit.half"))
    );
    assert!(!tc.fold_admitted(&names::NAT_SHIFT_RIGHT));
    assert!(tc
        .reduce_unary_shift_alias(&call("Counterfeit.half", Expr::nat_lit(3)))
        .is_none());
    assert!(!tc.unary_shift_alias_verified.get());
}

#[test]
fn a_changed_zero_step_cannot_supply_an_alias_hint() {
    let env = counterfeit_environment(true);
    let tc = TypeChecker::new(&env);
    assert!(tc.derive_unary_shift_alias().is_none());
    assert!(tc
        .reduce_unary_shift_alias(&call("Counterfeit.half", Expr::nat_lit(3)))
        .is_none());
}

#[test]
fn certified_halving_retains_the_reference_primitive_inventory() {
    let mut env = Environment::with_prelude();
    env.set_kernel_theory(KernelTheory::LeanReference);
    let tc = TypeChecker::new(&env);
    assert!(tc.hardwired_fold_admitted(&names::NAT_SHIFT_RIGHT));
    assert!(!tc.hardwired_fold_admitted(&names::NAT_PRED));
    let term = call("Nat.div2", Expr::nat_lit(u64::MAX));
    assert_eq!(
        tc.reduce_unary_shift_alias(&term),
        Some(Expr::nat_lit(u64::MAX / 2)),
    );
    assert!(tc.unary_shift_alias_verified.get());
    assert!(!tc.heartbeat_spent());
}
