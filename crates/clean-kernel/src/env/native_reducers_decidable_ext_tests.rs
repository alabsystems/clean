// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended decidable native reducers.

use super::native_reducers_decidable_ext::*;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use std::sync::LazyLock;

static DECIDABLE_IS_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Decidable.isTrue"));
static DECIDABLE_IS_FALSE: LazyLock<Name> =
    LazyLock::new(|| Name::from_string("Decidable.isFalse"));
static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));

/// Check if a `Decidable` instance expression is `Decidable.isTrue _` or
/// `Decidable.isFalse _`.
fn get_decidable_val(e: &Expr) -> Option<bool> {
    let head = e.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        if *name == *DECIDABLE_IS_TRUE {
            return Some(true);
        }
        if *name == *DECIDABLE_IS_FALSE {
            return Some(false);
        }
    }
    None
}

#[test]
fn test_reduce_nat_dec_le_true() {
    let result = reduce_nat_dec_le(&[&Expr::nat_lit(3), &Expr::nat_lit(5)]);
    assert!(result.is_some(), "Nat.decLe 3 5 should reduce");
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_nat_dec_le_false() {
    let result = reduce_nat_dec_le(&[&Expr::nat_lit(5), &Expr::nat_lit(3)]);
    assert!(result.is_some(), "Nat.decLe 5 3 should reduce");
    assert!(get_decidable_val(&result.unwrap()) == Some(false));
}

#[test]
fn test_reduce_nat_dec_le_equal() {
    let result = reduce_nat_dec_le(&[&Expr::nat_lit(3), &Expr::nat_lit(3)]);
    assert!(result.is_some(), "Nat.decLe 3 3 should reduce");
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_nat_dec_lt_true() {
    let result = reduce_nat_dec_lt(&[&Expr::nat_lit(3), &Expr::nat_lit(5)]);
    assert!(result.is_some(), "Nat.decLt 3 5 should reduce");
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_nat_dec_lt_false_equal() {
    let result = reduce_nat_dec_lt(&[&Expr::nat_lit(3), &Expr::nat_lit(3)]);
    assert!(result.is_some(), "Nat.decLt 3 3 should reduce");
    assert!(get_decidable_val(&result.unwrap()) == Some(false));
}

#[test]
fn test_reduce_decide_true() {
    let prop = Expr::const_(Name::from_string("True"), vec![]);
    let is_true = Expr::app(
        Expr::const_(DECIDABLE_IS_TRUE.clone(), vec![]),
        Expr::const_(Name::from_string("sorryAx"), vec![]),
    );
    let result = reduce_decide(&[&prop, &is_true]);
    assert!(result.is_some(), "decide with isTrue should reduce");
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, *BOOL_TRUE);
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_decide_false() {
    let prop = Expr::const_(Name::from_string("False"), vec![]);
    let is_false = Expr::app(
        Expr::const_(DECIDABLE_IS_FALSE.clone(), vec![]),
        Expr::const_(Name::from_string("sorryAx"), vec![]),
    );
    let result = reduce_decide(&[&prop, &is_false]);
    assert!(result.is_some(), "decide with isFalse should reduce");
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, *BOOL_FALSE);
    } else {
        panic!("Expected Bool.false");
    }
}

#[test]
fn test_reduce_decide_non_concrete_returns_none() {
    let prop = Expr::const_(Name::from_string("P"), vec![]);
    let non_concrete = Expr::const_(Name::from_string("some_inst"), vec![]);
    let result = reduce_decide(&[&prop, &non_concrete]);
    assert!(
        result.is_none(),
        "Non-concrete Decidable should return None"
    );
}

// Fully-applied `@Decidable.isX prop h` — the shape the sound equality reducers
// emit; the combinator reducers reuse the inner proof `h`.
fn dec_true(prop: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(DECIDABLE_IS_TRUE.clone(), vec![]),
        [prop.clone(), Expr::const_(Name::from_string("h"), vec![])],
    )
}
fn dec_false(prop: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(DECIDABLE_IS_FALSE.clone(), vec![]),
        [prop.clone(), Expr::const_(Name::from_string("h"), vec![])],
    )
}

#[test]
fn test_reduce_inst_decidable_and_both_true() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let result = reduce_inst_decidable_and(&[&p, &q, &dec_true(&p), &dec_true(&q)]);
    assert!(result.is_some());
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_inst_decidable_and_one_false() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let result = reduce_inst_decidable_and(&[&p, &q, &dec_true(&p), &dec_false(&q)]);
    assert!(result.is_some());
    assert!(get_decidable_val(&result.unwrap()) == Some(false));
}

#[test]
fn test_reduce_inst_decidable_or_one_true() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let result = reduce_inst_decidable_or(&[&p, &q, &dec_false(&p), &dec_true(&q)]);
    assert!(result.is_some());
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_inst_decidable_or_both_false() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let result = reduce_inst_decidable_or(&[&p, &q, &dec_false(&p), &dec_false(&q)]);
    assert!(result.is_some());
    assert!(get_decidable_val(&result.unwrap()) == Some(false));
}

#[test]
fn test_reduce_inst_decidable_not_true_gives_false() {
    // Fully-applied inner decision `@Decidable.isTrue P hp` — the shape the sound
    // equality reducers now emit; instDecidableNot reuses the inner proof `hp`.
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let hp = Expr::const_(Name::from_string("hp"), vec![]);
    let dp_true = Expr::apps(
        Expr::const_(DECIDABLE_IS_TRUE.clone(), vec![]),
        [p.clone(), hp],
    );
    let result = reduce_inst_decidable_not(&[&p, &dp_true]);
    assert!(result.is_some());
    assert!(get_decidable_val(&result.unwrap()) == Some(false));
}

#[test]
fn test_reduce_inst_decidable_not_false_gives_true() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let hp = Expr::const_(Name::from_string("hp"), vec![]);
    let dp_false = Expr::apps(
        Expr::const_(DECIDABLE_IS_FALSE.clone(), vec![]),
        [p.clone(), hp],
    );
    let result = reduce_inst_decidable_not(&[&p, &dp_false]);
    assert!(result.is_some());
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_int_dec_eq_equal() {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    let a = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(42));
    let b = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(42));
    let result = reduce_int_dec_eq(&[&a, &b]);
    assert!(result.is_some(), "Int.decEq should reduce equal Int values");
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_int_dec_eq_not_equal() {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    static INT_NEG_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.negSucc"));
    let a = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(1));
    let b = Expr::app(Expr::const_(INT_NEG_SUCC.clone(), vec![]), Expr::nat_lit(0));
    // a = 1, b = -(0+1) = -1
    let result = reduce_int_dec_eq(&[&a, &b]);
    assert!(
        result.is_some(),
        "Int.decEq should reduce unequal Int values"
    );
    assert!(get_decidable_val(&result.unwrap()) == Some(false));
}

#[test]
fn test_inst_decidable_eq_int_alias_reduces() {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    let mut env = Environment::new();
    env.init_decidable_ext_native_reducers();
    let reducer = *env
        .get_native_reducer(&names::INST_DECIDABLE_EQ_INT)
        .expect("instDecidableEqInt should be registered");
    let a = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(9));
    let b = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(9));
    let result = reducer(&[&a, &b]);
    assert!(
        result.is_some(),
        "instDecidableEqInt should reduce through the alias"
    );
    assert!(get_decidable_val(&result.unwrap()) == Some(true));
}

#[test]
fn test_reduce_int_dec_le_true() {
    static INT_NEG_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.negSucc"));
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    // -1 <= 0
    let a = Expr::app(Expr::const_(INT_NEG_SUCC.clone(), vec![]), Expr::nat_lit(0));
    let b = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(0));
    // Int ordering now declines (sound: not backed by an in-kernel order proof)
    // rather than emitting `Decidable.isTrue sorryAx`.
    assert!(reduce_int_dec_le(&[&a, &b]).is_none(), "Int.decLe declines");
}

#[test]
fn test_reduce_int_dec_le_false() {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    // 7 <= 2 is false
    let a = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(7));
    let b = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(2));
    assert!(reduce_int_dec_le(&[&a, &b]).is_none(), "Int.decLe declines");
}

#[test]
fn test_reduce_int_dec_lt_true() {
    static INT_NEG_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.negSucc"));
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    // -1 < 0
    let a = Expr::app(Expr::const_(INT_NEG_SUCC.clone(), vec![]), Expr::nat_lit(0));
    let b = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(0));
    // Int ordering now declines (sound: not backed by an in-kernel order proof).
    assert!(reduce_int_dec_lt(&[&a, &b]).is_none(), "Int.decLt declines");
}

#[test]
fn test_reduce_int_dec_lt_false() {
    static INT_OF_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Int.ofNat"));
    // 5 < 3 is false
    let a = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(5));
    let b = Expr::app(Expr::const_(INT_OF_NAT.clone(), vec![]), Expr::nat_lit(3));
    assert!(reduce_int_dec_lt(&[&a, &b]).is_none(), "Int.decLt declines");
}

#[test]
fn test_reduce_nat_dec_le_insufficient_args() {
    let result = reduce_nat_dec_le(&[&Expr::nat_lit(3)]);
    assert!(result.is_none(), "Single arg should not reduce");
}

#[test]
fn test_reduce_decide_insufficient_args() {
    let result = reduce_decide(&[&Expr::const_(Name::from_string("P"), vec![])]);
    assert!(result.is_none(), "Single arg should not reduce");
}

#[test]
fn test_registration() {
    let mut env = Environment::new();
    env.init_decidable_ext_native_reducers();
    assert!(env.get_native_reducer(&names::NAT_DEC_LE).is_some());
    assert!(env.get_native_reducer(&names::NAT_DEC_LT).is_some());
    assert!(env.get_native_reducer(&names::DECIDE).is_some());
    assert!(env.get_native_reducer(&names::DECIDABLE_DECIDE).is_some());
    assert!(env.get_native_reducer(&names::INST_DECIDABLE_AND).is_some());
    assert!(env.get_native_reducer(&names::INST_DECIDABLE_OR).is_some());
    assert!(env.get_native_reducer(&names::INST_DECIDABLE_NOT).is_some());
    assert!(env.get_native_reducer(&names::INT_DEC_EQ).is_some());
    assert!(env.get_native_reducer(&names::INT_DEC_LE).is_some());
    assert!(env.get_native_reducer(&names::INT_DEC_LT).is_some());
}

#[test]
fn test_and_or_reducers_are_sound_and_typecheck() {
    use crate::env::native_reducers::{mk_dec_is_true, mk_nat_dec_is_false};
    use crate::tc::TypeChecker;
    fn mentions_sorry(e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                s == "sorryAx" || s == "sorry"
            }
            ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                mentions_sorry(t) || mentions_sorry(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b)
            }
            _ => false,
        }
    }
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let one = crate::level::Level::succ(crate::level::Level::zero());
    let eqn = |a: &Expr, b: &Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            [nat(), a.clone(), b.clone()],
        )
    };
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let l1 = Expr::nat_lit(1);
    let l2 = Expr::nat_lit(2);

    // And, both true: p = (1=1), q = (1=1)
    let p = eqn(&l1, &l1);
    let dp = mk_dec_is_true(&Name::from_string("Nat"), &l1);
    let and_res = reduce_inst_decidable_and(&[&p, &p, &dp, &dp]).expect("and reduces");
    assert!(
        !mentions_sorry(&and_res),
        "And-true must be sorry-free: {and_res:?}"
    );
    let _ = tc
        .infer_type(&and_res)
        .expect("And-true output type-checks");

    // And, dp false: p = (1=2), q = (1=1)
    let pf = eqn(&l1, &l2);
    let dpf = mk_nat_dec_is_false(&l1, &l2);
    let and_f = reduce_inst_decidable_and(&[&pf, &p, &dpf, &dp]).expect("and reduces");
    assert!(
        !mentions_sorry(&and_f),
        "And-false must be sorry-free: {and_f:?}"
    );
    let _ = tc.infer_type(&and_f).expect("And-false output type-checks");

    // Or, both false: p = (1=2), q = (1=2)  → exercises Or.rec/elim
    let or_f = reduce_inst_decidable_or(&[&pf, &pf, &dpf, &dpf]).expect("or reduces");
    assert!(
        !mentions_sorry(&or_f),
        "Or-false must be sorry-free: {or_f:?}"
    );
    let _ = tc.infer_type(&or_f).expect("Or-false output type-checks");

    // Or, dp true: p = (1=1), q = (1=2)
    let or_t = reduce_inst_decidable_or(&[&p, &pf, &dp, &dpf]).expect("or reduces");
    assert!(
        !mentions_sorry(&or_t),
        "Or-true must be sorry-free: {or_t:?}"
    );
    let _ = tc.infer_type(&or_t).expect("Or-true output type-checks");
}

#[test]
fn test_reduce_int_dec_eq_is_sound() {
    use crate::env::Environment;
    use crate::tc::TypeChecker;
    fn mentions_sorry(e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                s == "sorryAx" || s == "sorry"
            }
            ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                mentions_sorry(t) || mentions_sorry(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b)
            }
            _ => false,
        }
    }
    let ofnat = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    };
    let negsucc = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n),
        )
    };
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    // 3 unequal cases: ofNat/ofNat, negSucc/negSucc, ofNat/negSucc
    for (a, b) in [
        (ofnat(1), ofnat(2)),
        (negsucc(0), negsucc(1)),
        (ofnat(0), negsucc(0)),
    ] {
        let term = reduce_int_dec_eq(&[&a, &b]).expect("int decEq reduces");
        assert!(
            !mentions_sorry(&term),
            "Int decEq must be sorry-free: {term:?}"
        );
        let _ = tc.infer_type(&term).expect("int decEq output type-checks");
    }
}

/// Track Q: the COMPOUND `Decidable` INSTANCE TERMS (not just the native
/// reducers) `instDecidableAnd` / `instDecidableOr` must be:
///   (1) registered as real `Definition`s (so the elaborator can resolve them),
///   (2) registered as resolvable `Decidable` class instances,
///   (3) infer_type-clean against the kernel type-checker, and
///   (4) backed by an EMPTY axiom closure (no `sorry`/`sorryAx`, no axiom).
/// This is the soundness gate behind `if (p ∧ q)` / `if (p ∨ q)` resolving
/// without a synthetic sorry.
#[test]
fn test_decidable_and_or_instances_registered_typecheck_axiom_free() {
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // The `Decidable` class instance list must contain both combinators.
    let decidable_insts: Vec<String> = env
        .get_class_instances(&Name::from_string("Decidable"))
        .iter()
        .map(|i| i.name.to_string())
        .collect();

    for name in ["instDecidableAnd", "instDecidableOr"] {
        // (1) registered as a Definition that retains its value.
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered by the prelude"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} must be a Definition"
        );
        assert!(
            info.value.is_some(),
            "{name} Definition must retain its value"
        );

        // (2) registered as a resolvable `Decidable` class instance.
        assert!(
            decidable_insts.iter().any(|s| s == name),
            "{name} must be a registered Decidable instance; got {decidable_insts:?}"
        );

        // (3) the instance term type-checks (this also re-validates the body
        // against the declared type via the kernel).
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));

        // (4) empty axiom closure — no sorry, no axiom of any kind.
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} is registered, axiom_deps should be Some"));
        let dep_names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(
            !dep_names.iter().any(|s| s == "sorry" || s == "sorryAx"),
            "{name} must not depend on sorry/sorryAx; closure = {dep_names:?}"
        );
        assert!(
            dep_names.is_empty(),
            "{name} must have an empty axiom closure, got {dep_names:?}"
        );
    }
}
