// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Decidable native reducers (instDecidableNatLt/Le, instDecidableEq*,
//! Fin.decEq).

use super::native_reducers_decidable::*;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;

// --- instDecidableNatLt tests ---

#[test]
fn test_inst_decidable_nat_lt_true() {
    let result = reduce_inst_decidable_nat_lt(&[&Expr::nat_lit(3), &Expr::nat_lit(5)]);
    let result = result.expect("3 < 5 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Decidable.isTrue",
            "3 < 5 should be isTrue"
        );
    } else {
        panic!("Expected Decidable.isTrue, got {:?}", head);
    }
}

#[test]
fn test_inst_decidable_nat_lt_false_equal() {
    let result = reduce_inst_decidable_nat_lt(&[&Expr::nat_lit(5), &Expr::nat_lit(5)]);
    let result = result.expect("5 < 5 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Decidable.isFalse",
            "5 < 5 should be isFalse"
        );
    } else {
        panic!("Expected Decidable.isFalse, got {:?}", head);
    }
}

#[test]
fn test_inst_decidable_nat_lt_false_greater() {
    let result = reduce_inst_decidable_nat_lt(&[&Expr::nat_lit(7), &Expr::nat_lit(3)]);
    let result = result.expect("7 < 3 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Decidable.isFalse",
            "7 < 3 should be isFalse"
        );
    } else {
        panic!("Expected Decidable.isFalse, got {:?}", head);
    }
}

#[test]
fn test_inst_decidable_nat_lt_zero() {
    // 0 < 1 should be true
    let result = reduce_inst_decidable_nat_lt(&[&Expr::nat_lit(0), &Expr::nat_lit(1)]);
    let result = result.expect("0 < 1 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isTrue");
    } else {
        panic!("Expected Decidable.isTrue");
    }

    // 0 < 0 should be false
    let result = reduce_inst_decidable_nat_lt(&[&Expr::nat_lit(0), &Expr::nat_lit(0)]);
    let result = result.expect("0 < 0 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isFalse");
    } else {
        panic!("Expected Decidable.isFalse");
    }
}

#[test]
fn test_inst_decidable_nat_lt_non_literal() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let result = reduce_inst_decidable_nat_lt(&[&x, &Expr::nat_lit(5)]);
    assert!(result.is_none(), "Non-literal should return None");
}

#[test]
fn test_inst_decidable_nat_lt_insufficient_args() {
    let result = reduce_inst_decidable_nat_lt(&[&Expr::nat_lit(3)]);
    assert!(result.is_none(), "Single arg should return None");
}

// --- instDecidableNatLe tests ---

#[test]
fn test_inst_decidable_nat_le_true_less() {
    let result = reduce_inst_decidable_nat_le(&[&Expr::nat_lit(3), &Expr::nat_lit(5)]);
    let result = result.expect("3 <= 5 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isTrue");
    } else {
        panic!("Expected Decidable.isTrue");
    }
}

#[test]
fn test_inst_decidable_nat_le_true_equal() {
    let result = reduce_inst_decidable_nat_le(&[&Expr::nat_lit(5), &Expr::nat_lit(5)]);
    let result = result.expect("5 <= 5 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isTrue");
    } else {
        panic!("Expected Decidable.isTrue");
    }
}

#[test]
fn test_inst_decidable_nat_le_false() {
    let result = reduce_inst_decidable_nat_le(&[&Expr::nat_lit(7), &Expr::nat_lit(3)]);
    let result = result.expect("7 <= 3 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isFalse");
    } else {
        panic!("Expected Decidable.isFalse");
    }
}

#[test]
fn test_inst_decidable_nat_le_zero() {
    let result = reduce_inst_decidable_nat_le(&[&Expr::nat_lit(0), &Expr::nat_lit(0)]);
    let result = result.expect("0 <= 0 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isTrue");
    } else {
        panic!("Expected Decidable.isTrue");
    }
}

#[test]
fn test_inst_decidable_nat_le_non_literal() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let result = reduce_inst_decidable_nat_le(&[&x, &Expr::nat_lit(5)]);
    assert!(result.is_none(), "Non-literal should return None");
}

// --- instDecidableEqNat tests ---

#[test]
fn test_inst_decidable_eq_nat_equal() {
    let result = reduce_inst_decidable_eq_nat(&[&Expr::nat_lit(42), &Expr::nat_lit(42)]);
    let result = result.expect("42 = 42 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isTrue");
    } else {
        panic!("Expected Decidable.isTrue");
    }
}

#[test]
fn test_inst_decidable_eq_nat_not_equal() {
    let result = reduce_inst_decidable_eq_nat(&[&Expr::nat_lit(1), &Expr::nat_lit(2)]);
    let result = result.expect("1 = 2 should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isFalse");
    } else {
        panic!("Expected Decidable.isFalse");
    }
}

// --- instDecidableEqBool tests ---

#[test]
fn test_inst_decidable_eq_bool_equal() {
    let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let result = reduce_inst_decidable_eq_bool(&[&t, &t]);
    let result = result.expect("true = true should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isTrue");
    } else {
        panic!("Expected Decidable.isTrue");
    }
}

#[test]
fn test_inst_decidable_eq_bool_not_equal() {
    let t = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let f = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let result = reduce_inst_decidable_eq_bool(&[&t, &f]);
    let result = result.expect("true = false should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isFalse");
    } else {
        panic!("Expected Decidable.isFalse");
    }
}

// --- instDecidableEqString tests ---

#[test]
fn test_inst_decidable_eq_string_equal() {
    let a = Expr::str_lit("hello");
    let b = Expr::str_lit("hello");
    let result = reduce_inst_decidable_eq_string(&[&a, &b]);
    let result = result.expect("equal strings should reduce");
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isTrue");
    } else {
        panic!("Expected Decidable.isTrue");
    }
}

#[test]
fn test_inst_decidable_eq_string_not_equal() {
    let a = Expr::str_lit("hello");
    let b = Expr::str_lit("world");
    // Distinct strings need `List Char` disequality (not yet built), so the
    // reducer declines rather than launder a `Decidable.isFalse sorryAx`.
    assert!(
        reduce_inst_decidable_eq_string(&[&a, &b]).is_none(),
        "String ≠ declines"
    );
}

// --- Fin.decEq tests ---

#[test]
fn test_fin_dec_eq_equal() {
    let n = Expr::nat_lit(10);
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(3);
    // Fin.decEq now declines (a sound witness needs `@Eq (Fin n)` built over the
    // proof-irrelevant `Fin.val` projection; the old body was type-incorrect).
    assert!(
        reduce_fin_dec_eq(&[&n, &a, &b]).is_none(),
        "Fin.decEq declines"
    );
}

#[test]
fn test_fin_dec_eq_not_equal() {
    let n = Expr::nat_lit(10);
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(7);
    assert!(
        reduce_fin_dec_eq(&[&n, &a, &b]).is_none(),
        "Fin.decEq declines"
    );
}

#[test]
fn test_fin_dec_eq_insufficient_args() {
    let n = Expr::nat_lit(10);
    let a = Expr::nat_lit(3);
    let result = reduce_fin_dec_eq(&[&n, &a]);
    assert!(result.is_none(), "2 args should return None for Fin.decEq");
}

#[test]
fn test_fin_dec_eq_non_literal_value() {
    let n = Expr::nat_lit(10);
    let a = Expr::const_(Name::from_string("x"), vec![]);
    let b = Expr::nat_lit(3);
    let result = reduce_fin_dec_eq(&[&n, &a, &b]);
    assert!(result.is_none(), "Non-literal Fin value should return None");
}

// --- Registration tests ---

#[test]
fn test_decidable_reducers_registered() {
    use super::native_reducers_decidable::names;
    let mut env = Environment::new();
    env.init_decidable_native_reducers();

    assert!(
        env.get_native_reducer(&names::INST_DECIDABLE_NAT_LT)
            .is_some(),
        "instDecidableNatLt should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DECIDABLE_NAT_LE)
            .is_some(),
        "instDecidableNatLe should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DECIDABLE_EQ_NAT)
            .is_some(),
        "instDecidableEqNat should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DECIDABLE_EQ_BOOL)
            .is_some(),
        "instDecidableEqBool should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DECIDABLE_EQ_STRING)
            .is_some(),
        "instDecidableEqString should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DECIDABLE_EQ_FIN)
            .is_some(),
        "instDecidableEqFin should be registered"
    );
    assert!(
        env.get_native_reducer(&names::FIN_DEC_EQ).is_some(),
        "Fin.decEq should be registered"
    );
}

// --- End-to-end tests via TypeChecker ---

#[test]
fn test_reduce_native_fires_inst_decidable_nat_lt() {
    use super::native_reducers_decidable::names;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_decidable_native_reducers();
    let tc = TypeChecker::new(&env);

    let app = Expr::app(
        Expr::app(
            Expr::const_(names::INST_DECIDABLE_NAT_LT.clone(), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(5),
    );

    let result = tc.reduce_native_for_test(&app);
    assert!(
        result.is_some(),
        "reduce_native should fire for instDecidableNatLt 3 5"
    );
}

#[test]
fn test_reduce_native_fires_inst_decidable_nat_le() {
    use super::native_reducers_decidable::names;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_decidable_native_reducers();
    let tc = TypeChecker::new(&env);

    let app = Expr::app(
        Expr::app(
            Expr::const_(names::INST_DECIDABLE_NAT_LE.clone(), vec![]),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(5),
    );

    let result = tc.reduce_native_for_test(&app);
    assert!(
        result.is_some(),
        "reduce_native should fire for instDecidableNatLe 5 5"
    );
}
