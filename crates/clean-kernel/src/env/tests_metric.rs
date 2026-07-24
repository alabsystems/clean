// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for metric spaces and distance functions
//!
//! This module tests:
//! - Int.abs properties
//! - Nat.absDiff (absolute difference)
//! - Distance functions for Rat, Int, Nat
//! - MetricSpace typeclass
//! - Metric space instances
//! - Metric concepts: balls, continuous, Lipschitz, uniform continuity
//! - Cauchy sequences, completeness, boundedness, compactness
//! - Total boundedness and separability

use super::test_helpers::{assert_bvar, assert_const, pi_domain_at};
use super::*;
use crate::expr::BinderInfo;
use crate::tc::TypeError;

#[test]
fn test_classical_choice_bad_argument_reports_type_mismatch() {
    let mut env = Environment::new();
    env.init_classical()
        .expect("init_classical should enable Classical.choice");

    // Classical.choice : {α : Sort u} -> Nonempty α -> α
    // Use Prop where Nonempty Prop is required to trigger a type mismatch.
    let choice_const = Expr::const_(Name::from_string("Classical.choice"), vec![Level::zero()]);
    let bad_choice_app = Expr::app(
        Expr::app(choice_const, Expr::prop()), // α = Prop
        Expr::prop(),                          // expected Nonempty Prop
    );

    let result = env.add_decl(Declaration::Definition {
        name: Name::from_string("bad_choice_1335_type_mismatch"),
        level_params: vec![],
        type_: Expr::prop(),
        value: bad_choice_app,
        is_reducible: false,
    });

    match result {
        Err(EnvError::TypeCheckFailed {
            source: TypeError::TypeMismatch { .. },
            ..
        }) => {}
        other => panic!(
            "expected TypeCheckFailed(TypeMismatch) for ill-typed Classical.choice, got {other:?}"
        ),
    }
}

#[test]
fn test_int_abs_props_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_abs_props());

    env.init_int_abs_props().unwrap();
    assert!(env.has_int_abs_props());

    // Check properties exist
    for s in [
        "Int.abs_nonneg",
        "Int.abs_of_nonneg",
        "Int.abs_of_neg",
        "Int.abs_neg",
        "Int.abs_zero",
        "Int.abs_mul",
        "Int.abs_add_le",
        "Int.abs_sub_le",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_abs_props_idempotent() {
    let mut env = Environment::new();
    env.init_int_abs_props().unwrap();
    env.init_int_abs_props().unwrap(); // Should be idempotent
    assert!(env.has_int_abs_props());
}

#[test]
fn test_int_abs_nonneg_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_abs_props().unwrap();

    // Int.abs_nonneg : ∀ a : Int, Int.le (Int.ofNat 0) (Int.abs a)
    let abs_nonneg_info = env.get_const(&Name::from_string("Int.abs_nonneg")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ a : Int, Prop
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &abs_nonneg_info.type_
    {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(tc.is_def_eq(domain, &int_const), "Domain should be Int");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Int.le"),
            "Int.abs_nonneg codomain head should be Int.le, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", abs_nonneg_info.type_);
    }
}

#[test]
fn test_int_abs_add_le_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_abs_props().unwrap();

    // Int.abs_add_le : ∀ a b : Int, Int.le (Int.abs (Int.add a b)) (Int.add (Int.abs a) (Int.abs b))
    let abs_add_le_info = env.get_const(&Name::from_string("Int.abs_add_le")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ a b : Int, Prop
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &abs_add_le_info.type_
    {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(
            tc.is_def_eq(domain, &int_const),
            "Outer domain should be Int"
        );
        // Inner should be ∀ b : Int, Int.le ...
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &int_const),
                "Inner domain should be Int"
            );
            let head = codomain_head_const(inner_codomain);
            assert_eq!(
                head.as_deref(),
                Some("Int.le"),
                "Int.abs_add_le codomain head should be Int.le, got {head:?}"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", abs_add_le_info.type_);
    }
}

#[test]
fn test_int_abs_neg_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_abs_props().unwrap();

    // Int.abs_neg : ∀ a : Int, Eq (Int.abs (Int.neg a)) (Int.abs a)
    let abs_neg_info = env.get_const(&Name::from_string("Int.abs_neg")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ a : Int, Eq Int ... ...
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &abs_neg_info.type_
    {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(tc.is_def_eq(domain, &int_const), "Domain should be Int");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Eq"),
            "Int.abs_neg codomain head should be Eq, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", abs_neg_info.type_);
    }
}

#[test]
fn test_int_abs_props_dependencies() {
    let mut env = Environment::new();
    env.init_int_abs_props().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_int_ord());
    assert!(env.has_int_arith());
    assert!(env.has_eq());
    // Int.abs is from init_int_sign_abs
}

// ========================================
// Nat.absDiff tests
// ========================================

#[test]
fn test_nat_abs_diff_init() {
    let mut env = Environment::new();
    assert!(!env.has_nat_abs_diff());

    env.init_nat_abs_diff().unwrap();
    assert!(env.has_nat_abs_diff());

    // Check functions and properties exist
    for s in [
        "Nat.absDiff",
        "Nat.absDiff_self",
        "Nat.absDiff_comm",
        "Nat.absDiff_zero_left",
        "Nat.absDiff_zero_right",
        "Nat.absDiff_add_same",
        "Nat.absDiff_triangle",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_nat_abs_diff_idempotent() {
    let mut env = Environment::new();
    env.init_nat_abs_diff().unwrap();
    env.init_nat_abs_diff().unwrap(); // Should be idempotent
    assert!(env.has_nat_abs_diff());
}

#[test]
fn test_nat_abs_diff_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_abs_diff().unwrap();

    // Nat.absDiff : Nat → Nat → Nat
    let abs_diff_info = env.get_const(&Name::from_string("Nat.absDiff")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: Nat → Nat → Nat
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &abs_diff_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &nat_const),
            "Outer domain should be Nat"
        );
        // Inner should be Nat → Nat
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &nat_const),
                "Inner domain should be Nat"
            );
            assert!(
                tc.is_def_eq(inner_codomain, &nat_const),
                "Codomain should be Nat"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", abs_diff_info.type_);
    }
}

#[test]
fn test_nat_abs_diff_self_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_abs_diff().unwrap();

    // Nat.absDiff_self : ∀ n : Nat, Eq (Nat.absDiff n n) Nat.zero
    let abs_diff_self_info = env
        .get_const(&Name::from_string("Nat.absDiff_self"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ n : Nat, Eq Nat ... Nat.zero
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &abs_diff_self_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(tc.is_def_eq(domain, &nat_const), "Domain should be Nat");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Eq"),
            "Nat.absDiff_self codomain head should be Eq, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", abs_diff_self_info.type_);
    }
}

#[test]
fn test_nat_abs_diff_triangle_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_abs_diff().unwrap();

    // Nat.absDiff_triangle : ∀ a b c : Nat, Nat.le ...
    let triangle_info = env
        .get_const(&Name::from_string("Nat.absDiff_triangle"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check type structure: ∀ a b c : Nat, Prop
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &triangle_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &nat_const),
            "Outer domain should be Nat"
        );
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &nat_const),
                "Second domain should be Nat"
            );
            if let Expr {
                kind: ExprKind::Pi(_, ref third_domain, ref third_codomain),
                ..
            } = inner_codomain.as_ref()
            {
                assert!(
                    tc.is_def_eq(third_domain, &nat_const),
                    "Third domain should be Nat"
                );
                let head = codomain_head_const(third_codomain);
                assert_eq!(
                    head.as_deref(),
                    Some("Nat.le"),
                    "Nat.absDiff_triangle codomain head should be Nat.le, got {head:?}"
                );
            } else {
                panic!("Expected third Pi type");
            }
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", triangle_info.type_);
    }
}

#[test]
fn test_nat_abs_diff_dependencies() {
    let mut env = Environment::new();
    env.init_nat_abs_diff().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_nat());
    assert!(env.has_nat_linear_order());
    assert!(env.has_decidable());
    assert!(env.has_eq());
}

// ==========================================
// Rat.dist tests
// ==========================================

#[test]
fn test_rat_dist_init() {
    let mut env = Environment::new();
    assert!(!env.has_rat_dist());
    env.init_rat_dist().unwrap();
    assert!(env.has_rat_dist());

    // Check all functions exist
    for s in [
        "Rat.dist",
        "Rat.dist_self",
        "Rat.dist_comm",
        "Rat.dist_nonneg",
        "Rat.dist_triangle",
        "Rat.dist_eq_abs_sub",
        "Rat.abs_sub_abs_le_dist",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_rat_dist_idempotent() {
    let mut env = Environment::new();
    env.init_rat_dist().unwrap();
    env.init_rat_dist().unwrap(); // Should not error
    assert!(env.has_rat_dist());
}

#[test]
fn test_rat_dist_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_dist().unwrap();

    // Rat.dist : Rat → Rat → Rat
    let dist = Expr::const_(Name::from_string("Rat.dist"), vec![]);
    let tc = TypeChecker::new(&env);
    let dist_ty = tc.infer_type(&dist).unwrap();

    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let expected_ty = Expr::pi(
        BinderInfo::Default,
        rat_const.clone(),
        Expr::pi(BinderInfo::Default, rat_const.clone(), rat_const),
    );

    assert!(
        tc.is_def_eq(&dist_ty, &expected_ty),
        "Rat.dist should have type Rat → Rat → Rat"
    );
}

#[test]
fn test_rat_dist_self_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_dist().unwrap();

    // Rat.dist_self : ∀ a : Rat, Eq (Rat.dist a a) Rat.zero
    let dist_self_info = env.get_const(&Name::from_string("Rat.dist_self")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a Pi type with domain Rat, codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_self_info.type_
    {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(tc.is_def_eq(domain, &rat_const), "Domain should be Rat");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Eq"),
            "Rat.dist_self codomain head should be Eq, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", dist_self_info.type_);
    }
}

#[test]
fn test_rat_dist_comm_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_dist().unwrap();

    // Rat.dist_comm : ∀ a b : Rat, Eq (Rat.dist a b) (Rat.dist b a)
    let dist_comm_info = env.get_const(&Name::from_string("Rat.dist_comm")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type with codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_comm_info.type_
    {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &rat_const),
            "Outer domain should be Rat"
        );
        // Inner type should also be Pi
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &rat_const),
                "Inner domain should be Rat"
            );
            let head = codomain_head_const(inner_codomain);
            assert_eq!(
                head.as_deref(),
                Some("Eq"),
                "Rat.dist_comm codomain head should be Eq, got {head:?}"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_comm_info.type_);
    }
}

#[test]
fn test_rat_dist_triangle_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_dist().unwrap();

    // Rat.dist_triangle : ∀ a b c : Rat, Rat.le (Rat.dist a c) (Rat.add (Rat.dist a b) (Rat.dist b c))
    let dist_triangle_info = env
        .get_const(&Name::from_string("Rat.dist_triangle"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a triple-nested Pi type
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_triangle_info.type_
    {
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &rat_const),
            "First domain should be Rat"
        );
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &rat_const),
                "Second domain should be Rat"
            );
            if let Expr {
                kind: ExprKind::Pi(_, ref innermost_domain, ref innermost_codomain),
                ..
            } = inner_codomain.as_ref()
            {
                assert!(
                    tc.is_def_eq(innermost_domain, &rat_const),
                    "Third domain should be Rat"
                );
                let head = codomain_head_const(innermost_codomain);
                assert_eq!(
                    head.as_deref(),
                    Some("Rat.le"),
                    "Rat.dist_triangle codomain head should be Rat.le, got {head:?}"
                );
            } else {
                panic!("Expected third Pi type");
            }
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_triangle_info.type_);
    }
}

#[test]
fn test_rat_dist_dependencies() {
    let mut env = Environment::new();
    env.init_rat_dist().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_rat_abs());
    assert!(env.has_rat());
    assert!(env.has_eq());
}

// ==========================================
// Int.dist tests
// ==========================================

#[test]
fn test_int_dist_init() {
    let mut env = Environment::new();
    assert!(!env.has_int_dist());
    env.init_int_dist().unwrap();
    assert!(env.has_int_dist());

    // Check all functions exist
    for s in [
        "Int.dist",
        "Int.dist_self",
        "Int.dist_comm",
        "Int.dist_nonneg",
        "Int.dist_triangle",
        "Int.dist_eq_abs_sub",
        "Int.abs_sub_abs_le_dist",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_int_dist_idempotent() {
    let mut env = Environment::new();
    env.init_int_dist().unwrap();
    env.init_int_dist().unwrap(); // Should not error
    assert!(env.has_int_dist());
}

#[test]
fn test_int_dist_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_dist().unwrap();

    // Int.dist : Int → Int → Int
    let dist = Expr::const_(Name::from_string("Int.dist"), vec![]);
    let tc = TypeChecker::new(&env);
    let dist_ty = tc.infer_type(&dist).unwrap();

    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let expected_ty = Expr::pi(
        BinderInfo::Default,
        int_const.clone(),
        Expr::pi(BinderInfo::Default, int_const.clone(), int_const),
    );

    assert!(
        tc.is_def_eq(&dist_ty, &expected_ty),
        "Int.dist should have type Int → Int → Int"
    );
}

#[test]
fn test_int_dist_self_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_dist().unwrap();

    // Int.dist_self : ∀ a : Int, Eq (Int.dist a a) (Int.ofNat 0)
    let dist_self_info = env.get_const(&Name::from_string("Int.dist_self")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a Pi type with domain Int, codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_self_info.type_
    {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(tc.is_def_eq(domain, &int_const), "Domain should be Int");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Eq"),
            "Int.dist_self codomain head should be Eq, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", dist_self_info.type_);
    }
}

#[test]
fn test_int_dist_comm_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_dist().unwrap();

    // Int.dist_comm : ∀ a b : Int, Eq (Int.dist a b) (Int.dist b a)
    let dist_comm_info = env.get_const(&Name::from_string("Int.dist_comm")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type with codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_comm_info.type_
    {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(
            tc.is_def_eq(domain, &int_const),
            "Outer domain should be Int"
        );
        // Inner type should also be Pi
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &int_const),
                "Inner domain should be Int"
            );
            let head = codomain_head_const(inner_codomain);
            assert_eq!(
                head.as_deref(),
                Some("Eq"),
                "Int.dist_comm codomain head should be Eq, got {head:?}"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_comm_info.type_);
    }
}

#[test]
fn test_int_dist_triangle_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_dist().unwrap();

    // Int.dist_triangle : ∀ a b c : Int, Int.le (Int.dist a c) (Int.add (Int.dist a b) (Int.dist b c))
    let dist_triangle_info = env
        .get_const(&Name::from_string("Int.dist_triangle"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a triple-nested Pi type
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_triangle_info.type_
    {
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        assert!(
            tc.is_def_eq(domain, &int_const),
            "First domain should be Int"
        );
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &int_const),
                "Second domain should be Int"
            );
            if let Expr {
                kind: ExprKind::Pi(_, ref innermost_domain, ref innermost_codomain),
                ..
            } = inner_codomain.as_ref()
            {
                assert!(
                    tc.is_def_eq(innermost_domain, &int_const),
                    "Third domain should be Int"
                );
                let head = codomain_head_const(innermost_codomain);
                assert_eq!(
                    head.as_deref(),
                    Some("Int.le"),
                    "Int.dist_triangle codomain head should be Int.le, got {head:?}"
                );
            } else {
                panic!("Expected third Pi type");
            }
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_triangle_info.type_);
    }
}

#[test]
fn test_int_dist_dependencies() {
    let mut env = Environment::new();
    env.init_int_dist().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_int_abs_props());
    assert!(env.has_int());
    assert!(env.has_int_ord());
    assert!(env.has_eq());
}

// =====================================================
// Nat.dist tests
// =====================================================

#[test]
fn test_nat_dist_init() {
    let mut env = Environment::new();
    assert!(!env.has_nat_dist());
    env.init_nat_dist().unwrap();
    assert!(env.has_nat_dist());
}

#[test]
fn test_nat_dist_idempotent() {
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();
    env.init_nat_dist().unwrap(); // Should not error
    assert!(env.has_nat_dist());
}

#[test]
fn test_nat_dist_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist : Nat → Nat → Nat
    let dist = Expr::const_(Name::from_string("Nat.dist"), vec![]);
    let tc = TypeChecker::new(&env);
    let dist_ty = tc.infer_type(&dist).unwrap();

    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let expected_ty = Expr::pi(
        BinderInfo::Default,
        nat_const.clone(),
        Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const),
    );

    assert!(
        tc.is_def_eq(&dist_ty, &expected_ty),
        "Nat.dist should have type Nat → Nat → Nat"
    );
}

#[test]
fn test_nat_dist_self_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist_self : ∀ a : Nat, Eq (Nat.dist a a) Nat.zero
    let dist_self_info = env.get_const(&Name::from_string("Nat.dist_self")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a Pi type with domain Nat, codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_self_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(tc.is_def_eq(domain, &nat_const), "Domain should be Nat");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Eq"),
            "Nat.dist_self codomain head should be Eq, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", dist_self_info.type_);
    }
}

#[test]
fn test_nat_dist_comm_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist_comm : ∀ a b : Nat, Eq (Nat.dist a b) (Nat.dist b a)
    let dist_comm_info = env.get_const(&Name::from_string("Nat.dist_comm")).unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type with codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_comm_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &nat_const),
            "Outer domain should be Nat"
        );
        // Inner type should also be Pi
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &nat_const),
                "Inner domain should be Nat"
            );
            let head = codomain_head_const(inner_codomain);
            assert_eq!(
                head.as_deref(),
                Some("Eq"),
                "Nat.dist_comm codomain head should be Eq, got {head:?}"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_comm_info.type_);
    }
}

#[test]
fn test_nat_dist_nonneg_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist_nonneg : ∀ a b : Nat, Nat.le Nat.zero (Nat.dist a b)
    let dist_nonneg_info = env
        .get_const(&Name::from_string("Nat.dist_nonneg"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type with codomain headed by Nat.le
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_nonneg_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &nat_const),
            "Outer domain should be Nat"
        );
        // Inner type should also be Pi
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &nat_const),
                "Inner domain should be Nat"
            );
            let head = codomain_head_const(inner_codomain);
            assert_eq!(
                head.as_deref(),
                Some("Nat.le"),
                "Nat.dist_nonneg codomain head should be Nat.le, got {head:?}"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_nonneg_info.type_);
    }
}

#[test]
fn test_nat_dist_triangle_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist_triangle : ∀ a b c : Nat, Nat.le (Nat.dist a c) (Nat.add (Nat.dist a b) (Nat.dist b c))
    let dist_triangle_info = env
        .get_const(&Name::from_string("Nat.dist_triangle"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a triply nested Pi type
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref body),
        ..
    } = &dist_triangle_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &nat_const),
            "First domain should be Nat"
        );
        if let Expr {
            kind: ExprKind::Pi(_, ref domain2, ref body2),
            ..
        } = body.as_ref()
        {
            assert!(
                tc.is_def_eq(domain2, &nat_const),
                "Second domain should be Nat"
            );
            if let Expr {
                kind: ExprKind::Pi(_, ref domain3, ref codomain3),
                ..
            } = body2.as_ref()
            {
                assert!(
                    tc.is_def_eq(domain3, &nat_const),
                    "Third domain should be Nat"
                );
                let head = codomain_head_const(codomain3);
                assert_eq!(
                    head.as_deref(),
                    Some("Nat.le"),
                    "Nat.dist_triangle codomain head should be Nat.le, got {head:?}"
                );
            } else {
                panic!("Expected third Pi type");
            }
        } else {
            panic!("Expected second Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_triangle_info.type_);
    }
}

#[test]
fn test_nat_dist_eq_abs_diff_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist_eq_absDiff : ∀ a b : Nat, Eq (Nat.dist a b) (Nat.absDiff a b)
    let dist_eq_info = env
        .get_const(&Name::from_string("Nat.dist_eq_absDiff"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a nested Pi type with codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_eq_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(
            tc.is_def_eq(domain, &nat_const),
            "Outer domain should be Nat"
        );
        // Inner type should also be Pi
        if let Expr {
            kind: ExprKind::Pi(_, ref inner_domain, ref inner_codomain),
            ..
        } = codomain.as_ref()
        {
            assert!(
                tc.is_def_eq(inner_domain, &nat_const),
                "Inner domain should be Nat"
            );
            let head = codomain_head_const(inner_codomain);
            assert_eq!(
                head.as_deref(),
                Some("Eq"),
                "Nat.dist_eq_absDiff codomain head should be Eq, got {head:?}"
            );
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type, got {:?}", dist_eq_info.type_);
    }
}

#[test]
fn test_nat_dist_zero_left_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist_zero_left : ∀ n : Nat, Eq (Nat.dist Nat.zero n) n
    let dist_zero_left_info = env
        .get_const(&Name::from_string("Nat.dist_zero_left"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a Pi type with domain Nat, codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_zero_left_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(tc.is_def_eq(domain, &nat_const), "Domain should be Nat");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Eq"),
            "Nat.dist_zero_left codomain head should be Eq, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", dist_zero_left_info.type_);
    }
}

#[test]
fn test_nat_dist_zero_right_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Nat.dist_zero_right : ∀ n : Nat, Eq (Nat.dist n Nat.zero) n
    let dist_zero_right_info = env
        .get_const(&Name::from_string("Nat.dist_zero_right"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Check it's a Pi type with domain Nat, codomain headed by Eq
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &dist_zero_right_info.type_
    {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(tc.is_def_eq(domain, &nat_const), "Domain should be Nat");
        let head = codomain_head_const(codomain);
        assert_eq!(
            head.as_deref(),
            Some("Eq"),
            "Nat.dist_zero_right codomain head should be Eq, got {head:?}"
        );
    } else {
        panic!("Expected Pi type, got {:?}", dist_zero_right_info.type_);
    }
}

#[test]
fn test_nat_dist_dependencies() {
    let mut env = Environment::new();
    env.init_nat_dist().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_nat_abs_diff());
    assert!(env.has_nat());
    assert!(env.has_nat_linear_order());
    assert!(env.has_eq());
}

// ============================================================================
// MetricSpace Tests
// ============================================================================

#[test]
fn test_metric_space_type() {
    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // MetricSpace : Type u → Type u
    // Type u = Sort (u+1), so we expect Sort (Succ (Param "u"))
    let metric_space_info = env.get_const(&Name::from_string("MetricSpace")).unwrap();

    // Check it's a Pi type
    if let Expr {
        kind: ExprKind::Pi(_, ref domain, ref codomain),
        ..
    } = &metric_space_info.type_
    {
        // Domain should be Type u = Sort (u+1) = Sort (Succ (Param "u"))
        if let Expr {
            kind: ExprKind::Sort(ref level),
            ..
        } = domain.as_ref()
        {
            assert!(
                matches!(level, Level::Succ(_)),
                "Domain should be Type u = Sort (u+1), got: {:?}",
                level
            );
        } else {
            panic!("Expected Sort for domain");
        }
        // Codomain should also be Type u = Sort (u+1)
        if let Expr {
            kind: ExprKind::Sort(ref level),
            ..
        } = codomain.as_ref()
        {
            assert!(
                matches!(level, Level::Succ(_)),
                "Codomain should be Type u = Sort (u+1), got: {:?}",
                level
            );
        } else {
            panic!("Expected Sort for codomain");
        }
    } else {
        panic!("Expected Pi type for MetricSpace");
    }
}

#[test]
fn test_metric_space_mk_type() {
    fn pi_body_after(expr: &Expr, binder_count: usize) -> Option<&Expr> {
        let mut current = expr;
        for _ in 0..binder_count {
            match &current.kind {
                ExprKind::Pi(_, _, body) => current = body.as_ref(),
                _ => return None,
            }
        }
        Some(current)
    }

    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // MetricSpace.mk should exist
    let mk_info = env.get_const(&Name::from_string("MetricSpace.mk")).unwrap();

    // Should have universe parameter u
    assert_eq!(mk_info.level_params.len(), 1);
    assert_eq!(mk_info.level_params[0].to_string(), "u");

    // Type should be a Pi (implicit α, then 5 fields, then MetricSpace α)
    assert!(matches!(&mk_info.type_.kind, ExprKind::Pi(_, _, _)));

    // Ensure the dist field uses in-scope α for both argument domains.
    let dist_domain =
        pi_domain_at(&mk_info.type_, 1).expect("MetricSpace.mk should expose dist as 2nd binder");
    match &dist_domain.kind {
        ExprKind::Pi(_, x_domain, x_body) => {
            assert_bvar(x_domain, 0, "MetricSpace.mk dist x-domain");
            match &x_body.kind {
                ExprKind::Pi(_, y_domain, _) => {
                    assert_bvar(y_domain, 1, "MetricSpace.mk dist y-domain");
                }
                _ => panic!("MetricSpace.mk dist domain should be Pi x => Pi y => Rat"),
            }
        }
        _ => panic!("MetricSpace.mk dist binder domain should be a function type"),
    }

    // Ensure final result is `MetricSpace α` where α is still in scope.
    let result = pi_body_after(&mk_info.type_, 6)
        .expect("MetricSpace.mk should have 6 top-level binders before result");
    let result_args = result.get_app_args();
    assert_eq!(
        result_args.len(),
        1,
        "MetricSpace.mk result should apply MetricSpace to one argument"
    );
    assert_bvar(
        result_args[0],
        5,
        "MetricSpace.mk result argument should reference α binder",
    );
}

#[test]
fn test_metric_space_dist_projection() {
    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // MetricSpace.dist : {α : Type u} → [MetricSpace α] → α → α → Rat
    let dist_info = env
        .get_const(&Name::from_string("MetricSpace.dist"))
        .unwrap();

    // Check it's a Pi type with implicit first argument
    if let Expr {
        kind: ExprKind::Pi(binder_info, ref _domain, ref _codomain),
        ..
    } = &dist_info.type_
    {
        assert_eq!(
            binder_info.info,
            BinderInfo::Implicit,
            "First argument should be implicit"
        );
    } else {
        panic!("Expected Pi type for MetricSpace.dist");
    }

    // Codomain after all Pi binders should be Rat
    let (count, codomain) = strip_pi_binders(&dist_info.type_);
    assert_eq!(count, 4, "MetricSpace.dist should have 4 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Rat"),
        "MetricSpace.dist codomain should be Rat, got {head:?}"
    );
}

#[test]
fn test_metric_space_dist_self_projection() {
    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // MetricSpace.dist_self should exist
    let dist_self_info = env
        .get_const(&Name::from_string("MetricSpace.dist_self"))
        .unwrap();

    // Should have universe parameter u
    assert_eq!(dist_self_info.level_params.len(), 1);
    assert!(matches!(&dist_self_info.type_.kind, ExprKind::Pi(_, _, _)));
}

#[test]
fn test_metric_space_dist_comm_projection() {
    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // MetricSpace.dist_comm should exist
    let dist_comm_info = env
        .get_const(&Name::from_string("MetricSpace.dist_comm"))
        .unwrap();

    // Should have universe parameter u
    assert_eq!(dist_comm_info.level_params.len(), 1);
    assert!(matches!(&dist_comm_info.type_.kind, ExprKind::Pi(_, _, _)));
}

#[test]
fn test_metric_space_dist_triangle_projection() {
    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // MetricSpace.dist_triangle should exist
    let dist_triangle_info = env
        .get_const(&Name::from_string("MetricSpace.dist_triangle"))
        .unwrap();

    // Should have universe parameter u
    assert_eq!(dist_triangle_info.level_params.len(), 1);
    assert!(matches!(
        &dist_triangle_info.type_.kind,
        ExprKind::Pi(_, _, _)
    ));
}

#[test]
fn test_metric_space_eq_of_dist_eq_zero_projection() {
    fn pi_body_after(expr: &Expr, binder_count: usize) -> Option<&Expr> {
        let mut current = expr;
        for _ in 0..binder_count {
            match &current.kind {
                ExprKind::Pi(_, _, body) => current = body.as_ref(),
                _ => return None,
            }
        }
        Some(current)
    }

    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // MetricSpace.eq_of_dist_eq_zero should exist
    let eq_of_dist_info = env
        .get_const(&Name::from_string("MetricSpace.eq_of_dist_eq_zero"))
        .unwrap();

    // Should have universe parameter u
    assert_eq!(eq_of_dist_info.level_params.len(), 1);
    assert!(matches!(&eq_of_dist_info.type_.kind, ExprKind::Pi(_, _, _)));

    // Should have 5 binders: {α} [inst] (x) (y) (h)
    let mut binder_count = 0;
    let mut current = &eq_of_dist_info.type_;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        binder_count += 1;
        current = body.as_ref();
    }
    assert_eq!(
        binder_count, 5,
        "MetricSpace.eq_of_dist_eq_zero should have 5 binders"
    );

    // Result should be Eq α x y where α/x/y refer to in-scope binders.
    let result = pi_body_after(&eq_of_dist_info.type_, 5)
        .expect("MetricSpace.eq_of_dist_eq_zero should expose result after 5 binders");
    let result_head = result.get_app_fn();
    assert!(
        matches!(&result_head.kind, ExprKind::Const(n, _) if n == &Name::from_string("Eq")),
        "Result should be an Eq application"
    );
    let result_args = result.get_app_args();
    assert_eq!(
        result_args.len(),
        3,
        "Eq result should have exactly 3 arguments (α, x, y)"
    );
    assert_bvar(
        result_args[0],
        4,
        "MetricSpace.eq_of_dist_eq_zero result α argument",
    );
    assert_bvar(
        result_args[1],
        2,
        "MetricSpace.eq_of_dist_eq_zero result x argument",
    );
    assert_bvar(
        result_args[2],
        1,
        "MetricSpace.eq_of_dist_eq_zero result y argument",
    );
}

#[test]
fn test_metric_space_dependencies() {
    let mut env = Environment::new();
    env.init_metric_space().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_rat());
    assert!(env.has_eq());
    assert!(env.has_le());
    assert!(env.has_metric_space());
}

#[test]
fn test_metric_space_idempotent() {
    let mut env = Environment::new();
    env.init_metric_space().unwrap();
    env.init_metric_space().unwrap(); // Should succeed without error
    assert!(env.has_metric_space());
}

// ============================================================================
// MetricSpace Instance Tests
// ============================================================================

#[test]
fn test_nat_metric_space_instance() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_nat_metric_space().unwrap();

    // instMetricSpaceNat : MetricSpace Nat
    let inst_info = env
        .get_const(&Name::from_string("instMetricSpaceNat"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Type should be MetricSpace Nat
    // Nat : Type 0, so MetricSpace.{0}
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("MetricSpace"), vec![Level::zero()]),
        nat_const,
    );

    assert!(
        tc.is_def_eq(&inst_info.type_, &expected_type),
        "Instance type should be MetricSpace Nat"
    );

    // No universe parameters for concrete type
    assert!(inst_info.level_params.is_empty());
}

#[test]
fn test_nat_metric_space_dependencies() {
    let mut env = Environment::new();
    env.init_nat_metric_space().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_metric_space());
    assert!(env.has_nat_dist());
    assert!(env.has_nat_metric_space());
}

#[test]
fn test_int_metric_space_instance() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_int_metric_space().unwrap();

    // instMetricSpaceInt : MetricSpace Int
    let inst_info = env
        .get_const(&Name::from_string("instMetricSpaceInt"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Type should be MetricSpace Int
    // Int : Type 0, so MetricSpace.{0}
    let int_const = Expr::const_(Name::from_string("Int"), vec![]);
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("MetricSpace"), vec![Level::zero()]),
        int_const,
    );

    assert!(
        tc.is_def_eq(&inst_info.type_, &expected_type),
        "Instance type should be MetricSpace Int"
    );

    // No universe parameters for concrete type
    assert!(inst_info.level_params.is_empty());
}

#[test]
fn test_int_metric_space_dependencies() {
    let mut env = Environment::new();
    env.init_int_metric_space().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_metric_space());
    assert!(env.has_int_dist());
    assert!(env.has_int_metric_space());
}

#[test]
fn test_rat_metric_space_instance() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_rat_metric_space().unwrap();

    // instMetricSpaceRat : MetricSpace Rat
    let inst_info = env
        .get_const(&Name::from_string("instMetricSpaceRat"))
        .unwrap();
    let tc = TypeChecker::new(&env);

    // Type should be MetricSpace Rat
    // Rat : Type 0, so MetricSpace.{0}
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let expected_type = Expr::app(
        Expr::const_(Name::from_string("MetricSpace"), vec![Level::zero()]),
        rat_const,
    );

    assert!(
        tc.is_def_eq(&inst_info.type_, &expected_type),
        "Instance type should be MetricSpace Rat"
    );

    // No universe parameters for concrete type
    assert!(inst_info.level_params.is_empty());
}

#[test]
fn test_rat_metric_space_dependencies() {
    let mut env = Environment::new();
    env.init_rat_metric_space().unwrap();

    // Should have initialized all dependencies
    assert!(env.has_metric_space());
    assert!(env.has_rat_dist());
    assert!(env.has_rat_metric_space());
}

#[test]
fn test_metric_space_instances_idempotent() {
    let mut env = Environment::new();

    // Initialize all instances
    env.init_nat_metric_space().unwrap();
    env.init_int_metric_space().unwrap();
    env.init_rat_metric_space().unwrap();

    // Call again - should be idempotent
    env.init_nat_metric_space().unwrap();
    env.init_int_metric_space().unwrap();
    env.init_rat_metric_space().unwrap();

    assert!(env.has_nat_metric_space());
    assert!(env.has_int_metric_space());
    assert!(env.has_rat_metric_space());
}

// ============================================================================
// Metric balls and closed balls
// ============================================================================

#[test]
fn test_metric_ball_init() {
    let mut env = Environment::new();
    assert!(!env.has_metric_ball());
    env.init_metric_ball().unwrap();
    assert!(env.has_metric_ball());

    // Constants should exist
    for s in [
        "Metric.ball",
        "Metric.closedBall",
        "Metric.mem_ball_self",
        "Metric.mem_closedBall_self",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_metric_ball_idempotent() {
    let mut env = Environment::new();
    env.init_metric_ball().unwrap();
    env.init_metric_ball().unwrap();
    assert!(env.has_metric_ball());
}

#[test]
fn test_metric_ball_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_metric_ball().unwrap();

    let tc = TypeChecker::new(&env);
    let u_level = Level::succ(Level::zero());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

    let expected_ty = Expr::pi(
        BinderInfo::Implicit,
        type_u, // {α}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space.clone(), Expr::bvar(0)), // [MetricSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // center
                Expr::pi(
                    BinderInfo::Default,
                    rat_const.clone(), // radius
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(3),                                  // x
                        Expr::from_kind(ExprKind::Sort(Level::zero())), // Prop
                    ),
                ),
            ),
        ),
    );

    let ball_const = Expr::const_(Name::from_string("Metric.ball"), vec![u_level.clone()]);
    let ball_ty = tc.infer_type(&ball_const).unwrap();
    assert!(tc.is_def_eq(&ball_ty, &expected_ty));
}

#[test]
fn test_metric_closed_ball_type() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_metric_ball().unwrap();

    let tc = TypeChecker::new(&env);
    let u_level = Level::succ(Level::zero());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

    let expected_ty = Expr::pi(
        BinderInfo::Implicit,
        type_u, // {α}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space.clone(), Expr::bvar(0)), // [MetricSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // center
                Expr::pi(
                    BinderInfo::Default,
                    rat_const.clone(), // radius
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(3),                                  // x
                        Expr::from_kind(ExprKind::Sort(Level::zero())), // Prop
                    ),
                ),
            ),
        ),
    );

    let closed_ball_const = Expr::const_(
        Name::from_string("Metric.closedBall"),
        vec![u_level.clone()],
    );
    let closed_ball_ty = tc.infer_type(&closed_ball_const).unwrap();
    assert!(tc.is_def_eq(&closed_ball_ty, &expected_ty));
}

#[test]
fn test_metric_ball_self_membership_types() {
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_metric_ball().unwrap();

    let tc = TypeChecker::new(&env);
    let u_level = Level::succ(Level::zero());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_lt = Expr::const_(Name::from_string("Rat.lt"), vec![]);
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
    let ball = Expr::const_(Name::from_string("Metric.ball"), vec![u_level.clone()]);
    let closed_ball = Expr::const_(
        Name::from_string("Metric.closedBall"),
        vec![u_level.clone()],
    );

    // Metric.mem_ball_self : {α} → [MetricSpace α] → ∀ x r, 0 < r → Metric.ball x r x
    let expected_mem_ball_self = Expr::pi(
        BinderInfo::Implicit,
        type_u.clone(), // {α}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space.clone(), Expr::bvar(0)), // [MetricSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // x
                Expr::pi(
                    BinderInfo::Default,
                    rat_const.clone(), // r
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(Expr::app(rat_lt, rat_zero.clone()), Expr::bvar(0)),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(ball.clone(), Expr::bvar(4)),
                                        Expr::bvar(3),
                                    ),
                                    Expr::bvar(2),
                                ),
                                Expr::bvar(1),
                            ),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        ),
    );

    let mem_ball_self = Expr::const_(
        Name::from_string("Metric.mem_ball_self"),
        vec![u_level.clone()],
    );
    let mem_ball_self_ty = tc.infer_type(&mem_ball_self).unwrap();
    assert!(tc.is_def_eq(&mem_ball_self_ty, &expected_mem_ball_self));

    // Metric.mem_closedBall_self : {α} → [MetricSpace α] → ∀ x r, 0 ≤ r → Metric.closedBall x r x
    let expected_mem_closed_ball_self = Expr::pi(
        BinderInfo::Implicit,
        type_u, // {α}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space, Expr::bvar(0)), // [MetricSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // x
                Expr::pi(
                    BinderInfo::Default,
                    rat_const, // r
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(Expr::app(rat_le, rat_zero), Expr::bvar(0)),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(closed_ball.clone(), Expr::bvar(4)),
                                        Expr::bvar(3),
                                    ),
                                    Expr::bvar(2),
                                ),
                                Expr::bvar(1),
                            ),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        ),
    );

    let mem_closed_ball_self = Expr::const_(
        Name::from_string("Metric.mem_closedBall_self"),
        vec![u_level.clone()],
    );
    let mem_closed_ball_self_ty = tc.infer_type(&mem_closed_ball_self).unwrap();
    assert!(tc.is_def_eq(&mem_closed_ball_self_ty, &expected_mem_closed_ball_self));
}

#[test]
fn test_all_metric_space_constants() {
    let mut env = Environment::new();
    env.init_nat_metric_space().unwrap();
    env.init_int_metric_space().unwrap();
    env.init_rat_metric_space().unwrap();
    env.init_metric_ball().unwrap();

    // Check all MetricSpace constants exist
    let constants = vec![
        "MetricSpace",
        "MetricSpace.mk",
        "MetricSpace.dist",
        "MetricSpace.dist_self",
        "MetricSpace.dist_comm",
        "MetricSpace.dist_triangle",
        "MetricSpace.eq_of_dist_eq_zero",
        "instMetricSpaceNat",
        "instMetricSpaceInt",
        "instMetricSpaceRat",
        "Metric.ball",
        "Metric.closedBall",
        "Metric.mem_ball_self",
        "Metric.mem_closedBall_self",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

#[test]
fn test_metric_continuous_init() {
    let mut env = Environment::new();
    assert!(!env.has_metric_continuous());
    env.init_metric_continuous().unwrap();
    assert!(env.has_metric_continuous());

    // Check that Metric.Continuous exists
    for s in [
        "Metric.Continuous",
        "Metric.continuous_id",
        "Metric.continuous_const",
    ] {
        assert_const(&env, s);
    }
}

#[test]
fn test_metric_continuous_idempotent() {
    let mut env = Environment::new();
    env.init_metric_continuous().unwrap();
    env.init_metric_continuous().unwrap();
    assert!(env.has_metric_continuous());
}

#[test]
fn test_metric_continuous_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Continuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] → (α → β) → Prop
    let continuous = Expr::const_(
        Name::from_string("Metric.Continuous"),
        vec![u_level.clone()],
    );
    let continuous_ty = tc.infer_type(&continuous).unwrap();

    // Just check we can infer the type (it's a Pi type)
    assert!(
        matches!(&continuous_ty.kind, ExprKind::Pi(..)),
        "Metric.Continuous should be a Pi type"
    );

    // Ensure the declaration lands in Prop, not Type.
    // Metric.Continuous has 5 binders: α, β, instα, instβ, f.
    let mut codomain = continuous_ty;
    for _ in 0..5 {
        codomain = match &codomain.kind {
            ExprKind::Pi(_, _, body) => body.as_ref().clone(),
            _ => panic!("Metric.Continuous should expose 5 Pi binders before codomain"),
        };
    }
    match &codomain.kind {
        ExprKind::Sort(level) => assert_eq!(
            *level,
            Level::zero(),
            "Metric.Continuous codomain should be Prop (Sort 0)"
        ),
        _ => panic!("Metric.Continuous codomain should be Sort(0)"),
    }
}

#[test]
fn test_metric_continuous_id_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.continuous_id : {α : Type u} → [MetricSpace α] → Metric.Continuous (fun x => x)
    let continuous_id = Expr::const_(
        Name::from_string("Metric.continuous_id"),
        vec![u_level.clone()],
    );
    let continuous_id_ty = tc.infer_type(&continuous_id).unwrap();

    // Just check we can infer the type (it's a Pi type)
    assert!(
        matches!(&continuous_id_ty.kind, ExprKind::Pi(..)),
        "Metric.continuous_id should be a Pi type"
    );
}

#[test]
fn test_metric_continuous_const_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.continuous_const : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                           ∀ c : β, Metric.Continuous (fun _ => c)
    let continuous_const = Expr::const_(
        Name::from_string("Metric.continuous_const"),
        vec![u_level.clone()],
    );
    let continuous_const_ty = tc.infer_type(&continuous_const).unwrap();

    // Just check we can infer the type (it's a Pi type)
    assert!(
        matches!(&continuous_const_ty.kind, ExprKind::Pi(..)),
        "Metric.continuous_const should be a Pi type"
    );
}

#[test]
fn test_metric_continuous_comp_exists() {
    let mut env = Environment::new();
    env.init_metric_continuous().unwrap();

    // Verify the continuous_comp constant exists
    assert_const(&env, "Metric.continuous_comp");
}

#[test]
fn test_metric_continuous_comp_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.continuous_comp : {α β γ : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                          [MetricSpace γ] → (f : α → β) → (g : β → γ) →
    //                          Metric.Continuous f → Metric.Continuous g →
    //                          Metric.Continuous (fun x => g (f x))
    let continuous_comp = Expr::const_(
        Name::from_string("Metric.continuous_comp"),
        vec![u_level.clone()],
    );
    let continuous_comp_ty = tc.infer_type(&continuous_comp).unwrap();

    let (count, codomain) = strip_pi_binders(&continuous_comp_ty);
    assert_eq!(
        count, 10,
        "Metric.continuous_comp should have 10 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Continuous"),
        "Metric.continuous_comp codomain head should be Metric.Continuous, got {head:?}"
    );
}

#[test]
fn test_all_metric_continuous_constants() {
    let mut env = Environment::new();
    env.init_metric_continuous().unwrap();

    let constants = vec![
        "Metric.Continuous",
        "Metric.continuous_id",
        "Metric.continuous_const",
        "Metric.continuous_comp",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// ================================================================
// Metric.Lipschitz Tests
// ================================================================

#[test]
fn test_metric_lipschitz_init() {
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();

    // Should have initialized dependencies
    assert!(env.has_metric_space());
    assert!(env.has_metric_continuous());
    assert!(env.has_metric_lipschitz());
}

#[test]
fn test_metric_lipschitz_idempotent() {
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();
    env.init_metric_lipschitz().unwrap(); // Should succeed without error
    assert!(env.has_metric_lipschitz());
}

#[test]
fn test_metric_lipschitz_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Lipschitz : {α β : Type u} → [MetricSpace α] → [MetricSpace β] → Rat → (α → β) → Prop
    let lipschitz = Expr::const_(Name::from_string("Metric.Lipschitz"), vec![u_level.clone()]);
    let lipschitz_ty = tc.infer_type(&lipschitz).unwrap();

    let (count, _codomain) = strip_pi_binders(&lipschitz_ty);
    assert_eq!(count, 6, "Metric.Lipschitz should have 6 parameters");
    assert_codomain_is_prop(&lipschitz_ty, "Metric.Lipschitz");
}

#[test]
fn test_metric_lipschitz_continuous_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.lipschitz_continuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                               ∀ K f, 0 ≤ K → Metric.Lipschitz K f → Metric.Continuous f
    let lipschitz_continuous = Expr::const_(
        Name::from_string("Metric.lipschitz_continuous"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&lipschitz_continuous).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 8,
        "Metric.lipschitz_continuous should have 8 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Continuous"),
        "Metric.lipschitz_continuous codomain head should be Metric.Continuous, got {head:?}"
    );
}

#[test]
fn test_metric_lipschitz_id_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.lipschitz_id : {α : Type u} → [MetricSpace α] → Metric.Lipschitz Rat.one (fun x => x)
    let lipschitz_id = Expr::const_(
        Name::from_string("Metric.lipschitz_id"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&lipschitz_id).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 2, "Metric.lipschitz_id should have 2 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Lipschitz"),
        "Metric.lipschitz_id codomain head should be Metric.Lipschitz, got {head:?}"
    );
}

#[test]
fn test_metric_lipschitz_const_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.lipschitz_const : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                          ∀ c : β, Metric.Lipschitz Rat.zero (fun _ => c)
    let lipschitz_const = Expr::const_(
        Name::from_string("Metric.lipschitz_const"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&lipschitz_const).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 5, "Metric.lipschitz_const should have 5 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Lipschitz"),
        "Metric.lipschitz_const codomain head should be Metric.Lipschitz, got {head:?}"
    );
}

#[test]
fn test_metric_lipschitz_comp_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.lipschitz_comp : {α β γ : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                         [MetricSpace γ] → ∀ K₁ K₂ f g,
    //                         Metric.Lipschitz K₁ f → Metric.Lipschitz K₂ g →
    //                         Metric.Lipschitz (Rat.mul K₂ K₁) (fun x => g (f x))
    let lipschitz_comp = Expr::const_(
        Name::from_string("Metric.lipschitz_comp"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&lipschitz_comp).unwrap();

    // 12 binders: α, β, γ, instα, instβ, instγ, K₁, K₂, f, g, hf, hg
    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 12, "Metric.lipschitz_comp should have 12 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Lipschitz"),
        "Metric.lipschitz_comp codomain head should be Metric.Lipschitz, got {head:?}"
    );
}

#[test]
fn test_all_metric_lipschitz_constants() {
    let mut env = Environment::new();
    env.init_metric_lipschitz().unwrap();

    let constants = vec![
        "Metric.Lipschitz",
        "Metric.lipschitz_continuous",
        "Metric.lipschitz_id",
        "Metric.lipschitz_const",
        "Metric.lipschitz_comp",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// ================================================================
// Metric.UniformContinuous Tests
// ================================================================

#[test]
fn test_metric_uniform_continuous_init() {
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    // Should have initialized dependencies
    assert!(env.has_metric_space());
    assert!(env.has_metric_continuous());
    assert!(env.has_metric_lipschitz());
    assert!(env.has_metric_uniform_continuous());
}

#[test]
fn test_metric_uniform_continuous_idempotent() {
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();
    env.init_metric_uniform_continuous().unwrap(); // Should succeed without error
    assert!(env.has_metric_uniform_continuous());
}

#[test]
fn test_metric_uniform_continuous_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.UniformContinuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] → (α → β) → Prop
    let uc = Expr::const_(
        Name::from_string("Metric.UniformContinuous"),
        vec![u_level.clone()],
    );
    let uc_ty = tc.infer_type(&uc).unwrap();

    let (count, _codomain) = strip_pi_binders(&uc_ty);
    assert_eq!(
        count, 5,
        "Metric.UniformContinuous should have 5 parameters"
    );
    assert_codomain_is_prop(&uc_ty, "Metric.UniformContinuous");
}

#[test]
fn test_metric_uniform_continuous_continuous_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.uniform_continuous_continuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                                        ∀ f, UniformContinuous f → Continuous f
    let uc_c = Expr::const_(
        Name::from_string("Metric.uniform_continuous_continuous"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&uc_c).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 6,
        "Metric.uniform_continuous_continuous should have 6 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Continuous"),
        "Metric.uniform_continuous_continuous codomain head should be Metric.Continuous, got {head:?}"
    );
}

#[test]
fn test_metric_lipschitz_uniform_continuous_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.lipschitz_uniform_continuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                                       ∀ K f, 0 ≤ K → Lipschitz K f → UniformContinuous f
    let lip_uc = Expr::const_(
        Name::from_string("Metric.lipschitz_uniform_continuous"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&lip_uc).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 8,
        "Metric.lipschitz_uniform_continuous should have 8 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.UniformContinuous"),
        "Metric.lipschitz_uniform_continuous codomain head should be Metric.UniformContinuous, got {head:?}"
    );
}

#[test]
fn test_metric_uniform_continuous_id_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.uniform_continuous_id : {α : Type u} → [MetricSpace α] → UniformContinuous (fun x => x)
    let uc_id = Expr::const_(
        Name::from_string("Metric.uniform_continuous_id"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&uc_id).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 2,
        "Metric.uniform_continuous_id should have 2 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.UniformContinuous"),
        "Metric.uniform_continuous_id codomain head should be Metric.UniformContinuous, got {head:?}"
    );
}

#[test]
fn test_metric_uniform_continuous_const_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.uniform_continuous_const : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                                   ∀ c : β, UniformContinuous (fun _ => c)
    let uc_const = Expr::const_(
        Name::from_string("Metric.uniform_continuous_const"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&uc_const).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 5,
        "Metric.uniform_continuous_const should have 5 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.UniformContinuous"),
        "Metric.uniform_continuous_const codomain head should be Metric.UniformContinuous, got {head:?}"
    );
}

#[test]
fn test_metric_uniform_continuous_comp_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.uniform_continuous_comp : {α β γ : Type u} → [MetricSpace α] → [MetricSpace β] →
    //                                  [MetricSpace γ] → ∀ f g,
    //                                  UniformContinuous f → UniformContinuous g →
    //                                  UniformContinuous (fun x => g (f x))
    let uc_comp = Expr::const_(
        Name::from_string("Metric.uniform_continuous_comp"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&uc_comp).unwrap();

    // 10 binders: α, β, γ, instα, instβ, instγ, f, g, hf, hg
    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 10,
        "Metric.uniform_continuous_comp should have 10 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.UniformContinuous"),
        "Metric.uniform_continuous_comp codomain head should be Metric.UniformContinuous, got {head:?}"
    );
}

#[test]
fn test_all_metric_uniform_continuous_constants() {
    let mut env = Environment::new();
    env.init_metric_uniform_continuous().unwrap();

    let constants = vec![
        "Metric.UniformContinuous",
        "Metric.uniform_continuous_continuous",
        "Metric.lipschitz_uniform_continuous",
        "Metric.uniform_continuous_id",
        "Metric.uniform_continuous_const",
        "Metric.uniform_continuous_comp",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// ========================================================================
// Helpers for metric property type assertions
// ========================================================================

/// Build the expected type `{α : Type u} → [MetricSpace α] → Prop`
/// which is shared by Metric.Complete, Metric.Bounded, Metric.Compact,
/// Metric.TotallyBounded, Metric.Separable.
fn expected_metric_prop_type(u_level: &Level) -> Expr {
    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
    Expr::pi(
        BinderInfo::Implicit,
        type_u, // {α : Sort(u+1)}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space, Expr::bvar(0)), // [MetricSpace α]
            Expr::from_kind(ExprKind::Sort(Level::zero())), // Prop
        ),
    )
}

/// Build the expected type `{α : Type u} → [MetricSpace α] → (Nat → α) → Prop`
/// for Metric.CauchySeq.
fn expected_cauchy_seq_type(u_level: &Level) -> Expr {
    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
    let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::pi(
        BinderInfo::Implicit,
        type_u, // {α : Sort(u+1)}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space, Expr::bvar(0)), // [MetricSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, nat_const, Expr::bvar(2)), // (Nat → α)
                Expr::from_kind(ExprKind::Sort(Level::zero())),          // Prop
            ),
        ),
    )
}

/// Build the expected type `{α : Type u} → [MetricSpace α] → α → Prop`
/// for Metric.Dense.
fn expected_dense_type(u_level: &Level) -> Expr {
    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
    Expr::pi(
        BinderInfo::Implicit,
        type_u, // {α : Sort(u+1)}
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space, Expr::bvar(0)), // [MetricSpace α]
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),                                  // (x : α)
                Expr::from_kind(ExprKind::Sort(Level::zero())), // Prop
            ),
        ),
    )
}

/// Assert that the codomain after stripping all Pi binders is Prop (Sort 0).
/// Use for predicate-defining types where the literal codomain is Sort(0).
fn assert_codomain_is_prop(ty: &Expr, name: &str) {
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, ref body) = t.kind {
        t = body.as_ref().clone();
    }
    assert!(
        matches!(&t.kind, ExprKind::Sort(l) if *l == Level::zero()),
        "{name} codomain should be Prop (Sort 0), got {:?}",
        t.kind
    );
}

/// Strip Pi binders from a type and return the binder count + codomain expression.
fn strip_pi_binders(ty: &Expr) -> (usize, Expr) {
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, ref body) = t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    (count, t)
}

/// Extract the head constant name from a (possibly applied) expression.
/// Walks through App nodes to find the leftmost Const.
fn codomain_head_const(expr: &Expr) -> Option<String> {
    let mut cur = expr;
    loop {
        match &cur.kind {
            ExprKind::App(f, _) => cur = f.as_ref(),
            ExprKind::Const(name, _) => return Some(name.to_string()),
            _ => return None,
        }
    }
}

// ========================================================================
// Metric.CauchySeq tests
// ========================================================================

#[test]
fn test_metric_cauchy_seq_init() {
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    // Should have initialized dependencies
    assert!(env.has_metric_space());
    assert!(env.has_metric_uniform_continuous());
    assert!(env.has_metric_cauchy_seq());
}

#[test]
fn test_metric_cauchy_seq_idempotent() {
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();
    env.init_metric_cauchy_seq().unwrap(); // Should succeed without error
    assert!(env.has_metric_cauchy_seq());
}

#[test]
fn test_metric_cauchy_seq_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.CauchySeq : {α : Type u} → [MetricSpace α] → (Nat → α) → Prop
    let cauchy_seq = Expr::const_(Name::from_string("Metric.CauchySeq"), vec![u_level.clone()]);
    let ty = tc.infer_type(&cauchy_seq).unwrap();

    let expected = expected_cauchy_seq_type(&u_level);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Metric.CauchySeq type mismatch: expected {{α : Type u}} → [MetricSpace α] → (Nat → α) → Prop"
    );
}

#[test]
fn test_metric_cauchy_const_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.cauchy_const : {α : Type u} → [MetricSpace α] → ∀ (c : α), CauchySeq (fun _ => c)
    let cauchy_const = Expr::const_(
        Name::from_string("Metric.cauchy_const"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&cauchy_const).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 3, "Metric.cauchy_const should have 3 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.CauchySeq"),
        "Metric.cauchy_const codomain head should be Metric.CauchySeq, got {head:?}"
    );
}

#[test]
fn test_metric_cauchy_tail_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.cauchy_tail : {α : Type u} → [MetricSpace α] → ∀ (seq : Nat → α) (k : Nat),
    //                      CauchySeq seq → CauchySeq (fun n => seq (n + k))
    let cauchy_tail = Expr::const_(
        Name::from_string("Metric.cauchy_tail"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&cauchy_tail).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 5, "Metric.cauchy_tail should have 5 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.CauchySeq"),
        "Metric.cauchy_tail codomain head should be Metric.CauchySeq, got {head:?}"
    );
}

#[test]
fn test_metric_cauchy_of_uniform_continuous_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.cauchy_of_uniform_continuous : {α β : Type u} → [MetricSpace α] → [MetricSpace β] →
    //   ∀ (f : α → β) (seq : Nat → α), UniformContinuous f → CauchySeq seq → CauchySeq (fun n => f (seq n))
    let cauchy_uc = Expr::const_(
        Name::from_string("Metric.cauchy_of_uniform_continuous"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&cauchy_uc).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 8,
        "Metric.cauchy_of_uniform_continuous should have 8 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.CauchySeq"),
        "Metric.cauchy_of_uniform_continuous codomain head should be Metric.CauchySeq, got {head:?}"
    );
}

#[test]
fn test_metric_converges_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Converges : {α : Type u} → [MetricSpace α] → (Nat → α) → α → Prop
    let converges = Expr::const_(Name::from_string("Metric.Converges"), vec![u_level.clone()]);
    let ty = tc.infer_type(&converges).unwrap();

    let (count, _codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 4, "Metric.Converges should have 4 parameters");
    assert_codomain_is_prop(&ty, "Metric.Converges");
}

#[test]
fn test_metric_cauchy_of_converges_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.cauchy_of_converges : {α : Type u} → [MetricSpace α] →
    //   ∀ (seq : Nat → α) (limit : α), Converges seq limit → CauchySeq seq
    let cauchy_conv = Expr::const_(
        Name::from_string("Metric.cauchy_of_converges"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&cauchy_conv).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 5,
        "Metric.cauchy_of_converges should have 5 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.CauchySeq"),
        "Metric.cauchy_of_converges codomain head should be Metric.CauchySeq, got {head:?}"
    );
}

#[test]
fn test_metric_converges_const_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.converges_const : {α : Type u} → [MetricSpace α] → ∀ (c : α), Converges (fun _ => c) c
    let conv_const = Expr::const_(
        Name::from_string("Metric.converges_const"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&conv_const).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 3, "Metric.converges_const should have 3 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Converges"),
        "Metric.converges_const codomain head should be Metric.Converges, got {head:?}"
    );
}

#[test]
fn test_all_metric_cauchy_seq_constants() {
    let mut env = Environment::new();
    env.init_metric_cauchy_seq().unwrap();

    let constants = vec![
        "Metric.CauchySeq",
        "Metric.cauchy_const",
        "Metric.cauchy_tail",
        "Metric.cauchy_of_uniform_continuous",
        "Metric.Converges",
        "Metric.cauchy_of_converges",
        "Metric.converges_const",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// ================================================================
// Metric.Complete Tests
// ================================================================

#[test]
fn test_metric_complete_init() {
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();

    // Should have initialized dependencies
    assert!(env.has_metric_space());
    assert!(env.has_metric_cauchy_seq());
    assert!(env.has_metric_complete());
}

#[test]
fn test_metric_complete_idempotent() {
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();
    env.init_metric_complete().unwrap(); // Should succeed without error
    assert!(env.has_metric_complete());
}

#[test]
fn test_metric_complete_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Complete : {α : Type u} → [MetricSpace α] → Prop
    let complete = Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);
    let ty = tc.infer_type(&complete).unwrap();

    let expected = expected_metric_prop_type(&u_level);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Metric.Complete type mismatch: expected {{α : Type u}} → [MetricSpace α] → Prop"
    );
}

#[test]
fn test_metric_complete_spec_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.complete_spec : {α : Type u} → [MetricSpace α] →
    //                        Complete α → ∀ seq, CauchySeq seq → ∃ limit, Converges seq limit
    let complete_spec = Expr::const_(
        Name::from_string("Metric.complete_spec"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&complete_spec).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 5, "Metric.complete_spec should have 5 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Exists"),
        "Metric.complete_spec codomain head should be Exists, got {head:?}"
    );
}

#[test]
fn test_metric_complete_of_seq_limit_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.complete_of_seq_limit : {α : Type u} → [MetricSpace α] →
    //   (∀ seq, CauchySeq seq → ∃ limit, Converges seq limit) → Complete α
    let complete_of_seq_limit = Expr::const_(
        Name::from_string("Metric.complete_of_seq_limit"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&complete_of_seq_limit).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.complete_of_seq_limit should have 3 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Complete"),
        "Metric.complete_of_seq_limit codomain head should be Metric.Complete, got {head:?}"
    );
}

#[test]
fn test_metric_converges_unique_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.converges_unique : {α : Type u} → [MetricSpace α] →
    //   ∀ seq limit₁ limit₂, Converges seq limit₁ → Converges seq limit₂ → limit₁ = limit₂
    let converges_unique = Expr::const_(
        Name::from_string("Metric.converges_unique"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&converges_unique).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 7, "Metric.converges_unique should have 7 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Eq"),
        "Metric.converges_unique codomain head should be Eq, got {head:?}"
    );
}

#[test]
fn test_metric_converges_of_cauchy_complete_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.converges_of_cauchy_complete : {α : Type u} → [MetricSpace α] →
    //   Complete α → ∀ seq, CauchySeq seq → ∃ limit, Converges seq limit
    let converges_of_cauchy_complete = Expr::const_(
        Name::from_string("Metric.converges_of_cauchy_complete"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&converges_of_cauchy_complete).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 5,
        "Metric.converges_of_cauchy_complete should have 5 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Exists"),
        "Metric.converges_of_cauchy_complete codomain head should be Exists, got {head:?}"
    );
}

#[test]
fn test_all_metric_complete_constants() {
    let mut env = Environment::new();
    env.init_metric_complete().unwrap();

    let constants = vec![
        "Metric.Complete",
        "Metric.complete_spec",
        "Metric.complete_of_seq_limit",
        "Metric.converges_unique",
        "Metric.converges_of_cauchy_complete",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// ================================================================
// Metric.Bounded Tests
// ================================================================

#[test]
fn test_metric_bounded_init() {
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();

    // Should have initialized dependencies
    assert!(env.has_metric_space());
    assert!(env.has_metric_bounded());
}

#[test]
fn test_metric_bounded_idempotent() {
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();
    env.init_metric_bounded().unwrap(); // Should succeed without error
    assert!(env.has_metric_bounded());
}

#[test]
fn test_metric_bounded_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Bounded : {α : Type u} → [MetricSpace α] → Prop
    let bounded = Expr::const_(Name::from_string("Metric.Bounded"), vec![u_level.clone()]);
    let ty = tc.infer_type(&bounded).unwrap();

    let expected = expected_metric_prop_type(&u_level);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Metric.Bounded type mismatch: expected {{α : Type u}} → [MetricSpace α] → Prop"
    );
}

#[test]
fn test_metric_bounded_spec_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.bounded_spec : {α : Type u} → [MetricSpace α] →
    //                       Bounded α → ∃ M, ∀ x y, dist x y ≤ M
    let bounded_spec = Expr::const_(
        Name::from_string("Metric.bounded_spec"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&bounded_spec).unwrap();

    // Check it's a Pi type with 3 binders (α, inst, hbounded)
    assert!(
        matches!(&ty.kind, ExprKind::Pi(..)),
        "Metric.bounded_spec should be a Pi type"
    );

    let mut count = 0;
    let mut t = ty;
    while let Expr {
        kind: ExprKind::Pi(_, _, ref body),
        ..
    } = t
    {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 3, "Metric.bounded_spec should have 3 parameters");

    // Ensure bounded_spec witnesses are Rat-based (not Nat-based) and the codomain
    // proposition is closed through Exists : Sort(1) -> (.. -> Prop) -> Prop.
    match &t.kind {
        ExprKind::App(exists_with_ty, predicate) => {
            assert!(
                matches!(&predicate.kind, ExprKind::Lam(..)),
                "Metric.bounded_spec codomain should apply Exists to a predicate lambda"
            );
            match &exists_with_ty.kind {
                ExprKind::App(exists_const, witness_ty) => {
                    match &witness_ty.kind {
                        ExprKind::Const(name, _) => assert_eq!(
                            name,
                            &Name::from_string("Rat"),
                            "Metric.bounded_spec witness type should be Rat"
                        ),
                        _ => panic!("Metric.bounded_spec witness type should be a constant"),
                    }
                    match &exists_const.kind {
                        ExprKind::Const(name, levels) => {
                            assert_eq!(
                                name,
                                &Name::from_string("Exists"),
                                "Metric.bounded_spec codomain should be existential"
                            );
                            assert_eq!(
                                levels.as_slice(),
                                &[Level::succ(Level::zero())],
                                "Metric.bounded_spec should use Exists at universe level 1 for Rat"
                            );
                        }
                        _ => panic!("Metric.bounded_spec codomain should start with Exists"),
                    }

                    let exists_ty = tc
                        .infer_type(exists_const)
                        .expect("Exists should type-check");
                    let mut exists_result = exists_ty;
                    for _ in 0..2 {
                        exists_result = match &exists_result.kind {
                            ExprKind::Pi(_, _, body) => body.as_ref().clone(),
                            _ => panic!("Exists type should expose two Pi binders"),
                        };
                    }
                    match &exists_result.kind {
                        ExprKind::Sort(level) => assert_eq!(
                            *level,
                            Level::zero(),
                            "Exists should return Prop (Sort 0), so bounded_spec codomain is Prop"
                        ),
                        _ => panic!("Exists codomain should be Sort(0)"),
                    }
                }
                _ => panic!("Metric.bounded_spec codomain should apply Exists to witness type"),
            }
        }
        _ => panic!("Metric.bounded_spec codomain should be an Exists application"),
    }
}

#[test]
fn test_metric_bounded_of_diam_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.bounded_of_diam : {α : Type u} → [MetricSpace α] →
    //   (∃ M, ∀ x y, dist x y ≤ M) → Bounded α
    let bounded_of_diam = Expr::const_(
        Name::from_string("Metric.bounded_of_diam"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&bounded_of_diam).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 3, "Metric.bounded_of_diam should have 3 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Bounded"),
        "Metric.bounded_of_diam codomain head should be Metric.Bounded, got {head:?}"
    );
}

#[test]
fn test_metric_bounded_dist_le_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.bounded_dist_le : {α : Type u} → [MetricSpace α] →
    //   Bounded α → ∀ x y, ∃ M, dist x y ≤ M
    let bounded_dist_le = Expr::const_(
        Name::from_string("Metric.bounded_dist_le"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&bounded_dist_le).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 5, "Metric.bounded_dist_le should have 5 parameters");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Exists"),
        "Metric.bounded_dist_le codomain head should be Exists, got {head:?}"
    );
}

#[test]
fn test_metric_complete_bounded_cauchy_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.complete_bounded_cauchy : {α : Type u} → [MetricSpace α] →
    //   Complete α → Bounded α → ∀ seq, CauchySeq seq → ∃ limit, Converges seq limit
    let complete_bounded_cauchy = Expr::const_(
        Name::from_string("Metric.complete_bounded_cauchy"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&complete_bounded_cauchy).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 6,
        "Metric.complete_bounded_cauchy should have 6 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Exists"),
        "Metric.complete_bounded_cauchy codomain head should be Exists, got {head:?}"
    );
}

#[test]
fn test_all_metric_bounded_constants() {
    let mut env = Environment::new();
    env.init_metric_bounded().unwrap();

    let constants = vec![
        "Metric.Bounded",
        "Metric.bounded_spec",
        "Metric.bounded_of_diam",
        "Metric.bounded_dist_le",
        "Metric.complete_bounded_cauchy",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// ================================================================
// Metric.Compact Tests
// ================================================================

#[test]
fn test_metric_compact_init() {
    let mut env = Environment::new();
    env.init_metric_compact().unwrap();

    assert!(env.has_metric_space());
    assert!(env.has_metric_bounded());
    assert!(env.has_metric_complete());
    assert!(env.has_metric_compact());
}

#[test]
fn test_metric_compact_idempotent() {
    let mut env = Environment::new();
    env.init_metric_compact().unwrap();
    env.init_metric_compact().unwrap();
    assert!(env.has_metric_compact());
}

#[test]
fn test_metric_compact_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_compact().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Compact : {α : Type u} → [MetricSpace α] → Prop
    let compact = Expr::const_(Name::from_string("Metric.Compact"), vec![u_level.clone()]);
    let ty = tc.infer_type(&compact).unwrap();

    let expected = expected_metric_prop_type(&u_level);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Metric.Compact type mismatch: expected {{α : Type u}} → [MetricSpace α] → Prop"
    );
}

#[test]
fn test_metric_bounded_of_compact_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_compact().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.bounded_of_compact : {α : Type u} → [MetricSpace α] →
    //   Metric.Compact α → Metric.Bounded α
    let bounded_of_compact = Expr::const_(
        Name::from_string("Metric.bounded_of_compact"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&bounded_of_compact).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.bounded_of_compact should have 3 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Bounded"),
        "Metric.bounded_of_compact codomain head should be Metric.Bounded, got {head:?}"
    );
}

#[test]
fn test_metric_complete_of_compact_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_compact().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.complete_of_compact : {α : Type u} → [MetricSpace α] →
    //   Metric.Compact α → Metric.Complete α
    let complete_of_compact = Expr::const_(
        Name::from_string("Metric.complete_of_compact"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&complete_of_compact).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.complete_of_compact should have 3 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Complete"),
        "Metric.complete_of_compact codomain head should be Metric.Complete, got {head:?}"
    );
}

#[test]
fn test_metric_compact_cauchy_converges_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_compact().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.compact_cauchy_converges :
    //   {α : Type u} → [MetricSpace α] →
    //   Metric.Compact α → ∀ seq, CauchySeq seq → ∃ limit, Converges seq limit
    let compact_cauchy_converges = Expr::const_(
        Name::from_string("Metric.compact_cauchy_converges"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&compact_cauchy_converges).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 5,
        "Metric.compact_cauchy_converges should have 5 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Exists"),
        "Metric.compact_cauchy_converges codomain head should be Exists, got {head:?}"
    );
}

#[test]
fn test_all_metric_compact_constants() {
    let mut env = Environment::new();
    env.init_metric_compact().unwrap();

    let constants = vec![
        "Metric.Compact",
        "Metric.bounded_of_compact",
        "Metric.complete_of_compact",
        "Metric.compact_cauchy_converges",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// =====================================================================
// Metric.TotallyBounded Tests
// =====================================================================

#[test]
fn test_metric_totally_bounded_init() {
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    // Check dependencies are initialized
    assert!(env.has_metric_space());
    assert!(env.has_metric_bounded());
    assert!(env.has_metric_complete());
    assert!(env.has_metric_compact());
    assert!(env.has_metric_totally_bounded());
}

#[test]
fn test_metric_totally_bounded_idempotent() {
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();
    env.init_metric_totally_bounded().unwrap();
    assert!(env.has_metric_totally_bounded());
}

#[test]
fn test_metric_totally_bounded_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.TotallyBounded : {α : Type u} → [MetricSpace α] → Prop
    let totally_bounded = Expr::const_(
        Name::from_string("Metric.TotallyBounded"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&totally_bounded).unwrap();

    let expected = expected_metric_prop_type(&u_level);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Metric.TotallyBounded type mismatch: expected {{α : Type u}} → [MetricSpace α] → Prop"
    );
}

#[test]
fn test_metric_totally_bounded_of_compact_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.totally_bounded_of_compact : {α : Type u} → [MetricSpace α] →
    //   Metric.Compact α → Metric.TotallyBounded α
    let tb_of_compact = Expr::const_(
        Name::from_string("Metric.totally_bounded_of_compact"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&tb_of_compact).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.totally_bounded_of_compact should have 3 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.TotallyBounded"),
        "Metric.totally_bounded_of_compact codomain head should be Metric.TotallyBounded, got {head:?}"
    );
}

#[test]
fn test_metric_bounded_of_totally_bounded_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.bounded_of_totally_bounded : {α : Type u} → [MetricSpace α] →
    //   Metric.TotallyBounded α → Metric.Bounded α
    let bounded_of_tb = Expr::const_(
        Name::from_string("Metric.bounded_of_totally_bounded"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&bounded_of_tb).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.bounded_of_totally_bounded should have 3 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Bounded"),
        "Metric.bounded_of_totally_bounded codomain head should be Metric.Bounded, got {head:?}"
    );
}

#[test]
fn test_metric_compact_iff_complete_totally_bounded_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.compact_iff_complete_totally_bounded : {α : Type u} → [MetricSpace α] →
    //   Iff (Compact α) (Complete α ∧ TotallyBounded α)
    let compact_iff = Expr::const_(
        Name::from_string("Metric.compact_iff_complete_totally_bounded"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&compact_iff).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 2,
        "Metric.compact_iff_complete_totally_bounded should have 2 parameters (result is Iff)"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Iff"),
        "Metric.compact_iff_complete_totally_bounded codomain head should be Iff, got {head:?}"
    );
}

#[test]
fn test_metric_totally_bounded_spec_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.totally_bounded_spec : {α : Type u} → [MetricSpace α] →
    //   TotallyBounded α → ∀ ε, 0 < ε → ∀ x, ∃ c, dist x c < ε
    let tb_spec = Expr::const_(
        Name::from_string("Metric.totally_bounded_spec"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&tb_spec).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 6,
        "Metric.totally_bounded_spec should have 6 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Exists"),
        "Metric.totally_bounded_spec codomain head should be Exists, got {head:?}"
    );
}

#[test]
fn test_metric_totally_bounded_of_eps_net_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.totally_bounded_of_eps_net : {α : Type u} → [MetricSpace α] →
    //   (∀ ε, 0 < ε → ∀ x, ∃ c, dist x c < ε) → TotallyBounded α
    let tb_intro = Expr::const_(
        Name::from_string("Metric.totally_bounded_of_eps_net"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&tb_intro).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.totally_bounded_of_eps_net should have 3 parameters"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.TotallyBounded"),
        "Metric.totally_bounded_of_eps_net codomain head should be Metric.TotallyBounded, got {head:?}"
    );
}

#[test]
fn test_all_metric_totally_bounded_constants() {
    let mut env = Environment::new();
    env.init_metric_totally_bounded().unwrap();

    let constants = vec![
        "Metric.TotallyBounded",
        "Metric.totally_bounded_of_compact",
        "Metric.bounded_of_totally_bounded",
        "Metric.compact_iff_complete_totally_bounded",
        "Metric.totally_bounded_spec",
        "Metric.totally_bounded_of_eps_net",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// Metric.Separable Tests

#[test]
fn test_metric_separable_init() {
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    // Check dependencies are initialized
    assert!(env.has_metric_space());
    assert!(env.has_metric_bounded());
    assert!(env.has_metric_complete());
    assert!(env.has_metric_compact());
    assert!(env.has_metric_totally_bounded());
    assert!(env.has_metric_separable());
}

#[test]
fn test_metric_separable_idempotent() {
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();
    env.init_metric_separable().unwrap();
    assert!(env.has_metric_separable());
}

#[test]
fn test_metric_dense_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Dense : {α : Type u} → [MetricSpace α] → α → Prop
    let dense = Expr::const_(Name::from_string("Metric.Dense"), vec![u_level.clone()]);
    let ty = tc.infer_type(&dense).unwrap();

    let expected = expected_dense_type(&u_level);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Metric.Dense type mismatch: expected {{α : Type u}} → [MetricSpace α] → α → Prop"
    );
}

#[test]
fn test_metric_separable_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Separable : {α : Type u} → [MetricSpace α] → Prop
    let separable = Expr::const_(Name::from_string("Metric.Separable"), vec![u_level.clone()]);
    let ty = tc.infer_type(&separable).unwrap();

    let expected = expected_metric_prop_type(&u_level);
    assert!(
        tc.is_def_eq(&ty, &expected),
        "Metric.Separable type mismatch: expected {{α : Type u}} → [MetricSpace α] → Prop"
    );
}

#[test]
fn test_metric_separable_of_totally_bounded_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.separable_of_totally_bounded :
    //   {α : Type u} → [MetricSpace α] → TotallyBounded α → Separable α
    let separable_of_tb = Expr::const_(
        Name::from_string("Metric.separable_of_totally_bounded"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&separable_of_tb).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.separable_of_totally_bounded should have 3 Pi binders"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Separable"),
        "Metric.separable_of_totally_bounded codomain head should be Metric.Separable, got {head:?}"
    );
}

#[test]
fn test_metric_separable_of_compact_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.separable_of_compact :
    //   {α : Type u} → [MetricSpace α] → Compact α → Separable α
    let separable_of_compact = Expr::const_(
        Name::from_string("Metric.separable_of_compact"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&separable_of_compact).unwrap();

    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.separable_of_compact should have 3 Pi binders"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Separable"),
        "Metric.separable_of_compact codomain head should be Metric.Separable, got {head:?}"
    );
}

#[test]
fn test_metric_separable_spec_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.separable_spec :
    //   {α : Type u} → [MetricSpace α] → Separable α →
    //   ∀ (x : α) (ε : Nat), 0 < ε → ∃ (d : α), Dense d ∧ dist x d < ε
    let separable_spec = Expr::const_(
        Name::from_string("Metric.separable_spec"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&separable_spec).unwrap();

    // {α} [inst] hsep x ε hpos = 6 Pi binders
    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(count, 6, "Metric.separable_spec should have 6 Pi binders");
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Exists"),
        "Metric.separable_spec codomain head should be Exists, got {head:?}"
    );
}

#[test]
fn test_metric_separable_of_dense_exists_type() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.separable_of_dense_exists :
    //   {α : Type u} → [MetricSpace α] →
    //   (∀ x ε, 0 < ε → ∃ d, Dense d ∧ dist x d < ε) → Separable α
    let separable_of_dense = Expr::const_(
        Name::from_string("Metric.separable_of_dense_exists"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&separable_of_dense).unwrap();

    // {α} [inst] h = 3 Pi binders
    let (count, codomain) = strip_pi_binders(&ty);
    assert_eq!(
        count, 3,
        "Metric.separable_of_dense_exists should have 3 Pi binders"
    );
    let head = codomain_head_const(&codomain);
    assert_eq!(
        head.as_deref(),
        Some("Metric.Separable"),
        "Metric.separable_of_dense_exists codomain head should be Metric.Separable, got {head:?}"
    );
}

#[test]
fn test_all_metric_separable_constants() {
    let mut env = Environment::new();
    env.init_metric_separable().unwrap();

    let constants = vec![
        "Metric.Dense",
        "Metric.Separable",
        "Metric.separable_of_totally_bounded",
        "Metric.separable_of_compact",
        "Metric.separable_spec",
        "Metric.separable_of_dense_exists",
    ];

    for name in constants {
        assert_const(&env, name);
    }
}

// ============================================================================
// Negative test: wrong universe level is rejected
// ============================================================================

/// AC3: Verify that a wrong universe level in the expected type makes is_def_eq fail.
/// This ensures our full type equality assertions are actually discriminating.
#[test]
fn test_metric_wrong_universe_level_rejected() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_complete().expect("init_metric_complete");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Get the actual type of Metric.Complete
    let complete = Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);
    let actual_ty = tc
        .infer_type(&complete)
        .expect("infer Metric.Complete type");

    // Build an INCORRECT expected type with wrong universe level:
    // Use Level::zero() instead of u_level for the Sort domain → should fail is_def_eq
    let wrong_type_u = Expr::sort(Level::succ(Level::zero())); // Type 0 instead of Type u
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);
    let wrong_expected = Expr::pi(
        BinderInfo::Implicit,
        wrong_type_u, // WRONG: Type 0 instead of Type u
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space, Expr::bvar(0)),
            Expr::from_kind(ExprKind::Sort(Level::zero())),
        ),
    );

    // The correct expected type should match
    let correct_expected = expected_metric_prop_type(&u_level);
    assert!(
        tc.is_def_eq(&actual_ty, &correct_expected),
        "Correct expected type should match Metric.Complete"
    );

    // The wrong expected type should NOT match
    assert!(
        !tc.is_def_eq(&actual_ty, &wrong_expected),
        "Wrong universe level should be rejected by is_def_eq"
    );
}

// ============================================================================
// BVar depth sensitivity test
// ============================================================================

/// AC4: Verify that metric type assertions would fail if bvar depth is off by 1.
/// Constructs an expected type with BVar(1) where BVar(0) is correct.
#[test]
fn test_metric_bvar_depth_sensitivity() {
    use crate::tc::TypeChecker;
    let mut env = Environment::new();
    env.init_metric_complete().expect("init_metric_complete");

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Metric.Complete : {α : Type u} → [MetricSpace α] → Prop
    // The inst implicit binder domain is `MetricSpace (BVar 0)` (referring to α)
    // If we use BVar(1) instead, it's wrong — no such variable in scope.

    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let metric_space = Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]);

    let wrong_bvar_expected = Expr::pi(
        BinderInfo::Implicit,
        type_u,
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(metric_space, Expr::bvar(1)), // WRONG: BVar(1) instead of BVar(0)
            Expr::from_kind(ExprKind::Sort(Level::zero())),
        ),
    );

    let complete = Expr::const_(Name::from_string("Metric.Complete"), vec![u_level.clone()]);
    let actual_ty = tc
        .infer_type(&complete)
        .expect("infer Metric.Complete type");

    // The correct type should match
    let correct_expected = expected_metric_prop_type(&u_level);
    assert!(
        tc.is_def_eq(&actual_ty, &correct_expected),
        "Correct expected type should match Metric.Complete"
    );

    // The wrong BVar depth should NOT match
    assert!(
        !tc.is_def_eq(&actual_ty, &wrong_bvar_expected),
        "BVar depth off by 1 should be rejected by is_def_eq"
    );
}

// ============================================================================
// Algebra.LinearAlgebra (Linear Algebra) tests
// ============================================================================
