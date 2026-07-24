// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// --- Uninterpreted sort handling tests (#2357) ---

#[test]
fn test_sort_to_lean_type_uninterpreted_distinct() {
    // Distinct uninterpreted sorts must produce distinct type constants.
    // Previously, all uninterpreted sorts collapsed to Unit.
    let sort_a = Sort::Uninterpreted("MyTypeA".to_string());
    let sort_b = Sort::Uninterpreted("MyTypeB".to_string());
    let expr_a = sort_to_lean_type(&sort_a);
    let expr_b = sort_to_lean_type(&sort_b);

    match expr_a.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "MyTypeA"),
        _ => panic!("expected Const(MyTypeA), got {:?}", expr_a),
    }
    match expr_b.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "MyTypeB"),
        _ => panic!("expected Const(MyTypeB), got {:?}", expr_b),
    }
    assert_ne!(
        expr_a, expr_b,
        "distinct uninterpreted sorts must produce distinct constants"
    );
}

#[test]
fn test_sort_to_lean_type_string() {
    let expr = sort_to_lean_type(&Sort::String);
    match expr.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "String"),
        _ => panic!("expected Const(String), got {:?}", expr),
    }
}

// --- Universe inference tests (#2357) ---

#[test]
fn test_mk_eq_prop_universe() {
    // @Eq.{1} Prop True False — Prop = Sort 0 : Sort 1, so u = 1
    let ty = Expr::sort(Level::zero()); // Prop
    let a = Expr::const_(Name::from_string("True"), vec![]);
    let b = Expr::const_(Name::from_string("False"), vec![]);
    let eq = mk_eq(&ty, &a, &b);
    let head = eq.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Eq");
            assert_eq!(levels.len(), 1);
            assert_eq!(levels[0], Level::succ(Level::zero()));
        }
        _ => panic!("expected Const(Eq, [1]), got {:?}", head),
    }
}

#[test]
fn test_mk_eq_type0_universe() {
    // @Eq.{2} (Type 0) Nat Int — Type 0 = Sort 1 : Sort 2, so u = 2
    let ty = Expr::sort(Level::succ(Level::zero())); // Type 0 = Sort 1
    let a = Expr::const_(Name::from_string("Nat"), vec![]);
    let b = Expr::const_(Name::from_string("Int"), vec![]);
    let eq = mk_eq(&ty, &a, &b);
    let head = eq.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Eq");
            assert_eq!(levels.len(), 1);
            // u = succ(succ(0)) = 2
            assert_eq!(levels[0], Level::succ(Level::succ(Level::zero())));
        }
        _ => panic!("expected Const(Eq, [2]), got {:?}", head),
    }
}

#[test]
fn test_infer_universe_level_const() {
    // Constants like Nat, Int → universe 1 (they live in Type 0)
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let u = infer_universe_level(&ty);
    assert_eq!(u, Level::succ(Level::zero()));
}

#[test]
fn test_infer_universe_level_sort() {
    // Sort 0 (Prop) → universe succ(0) = 1
    let prop = Expr::sort(Level::zero());
    assert_eq!(infer_universe_level(&prop), Level::succ(Level::zero()));
    // Sort 1 (Type 0) → universe succ(1) = 2
    let type0 = Expr::sort(Level::succ(Level::zero()));
    assert_eq!(
        infer_universe_level(&type0),
        Level::succ(Level::succ(Level::zero()))
    );
}

// --- mk_ite_checked argument position verification (#302 P1 finding 2) ---

#[test]
fn test_mk_ite_checked_arg_positions() {
    // Lean 4: @ite.{u} {alpha} (c : Prop) [h : Decidable c] (a b : alpha) : alpha
    // Spine: ite alpha c h a b — condition at pos 2, Decidable at pos 3.
    // Regression test for 7da4f09 which fixed the condition/Decidable swap.
    let cond = mk_lt(
        &Sort::Int,
        &Expr::fvar(FVarId::new(1)),
        &Expr::fvar(FVarId::new(2)),
    );
    let then_br = Expr::const_(Name::from_string("myThen"), vec![]);
    let else_br = Expr::const_(Name::from_string("myElse"), vec![]);
    let ite = mk_ite_checked(&Sort::Int, &cond, &then_br, &else_br)
        .expect("should resolve Decidable for LT.lt");

    // Deconstruct: App(App(App(App(App(ite, alpha), cond), dec), then), else)
    let ExprKind::App(f1, e) = ite.kind() else {
        panic!("not 5-arg app")
    };
    let ExprKind::App(f2, t) = f1.kind() else {
        panic!("not 4-arg app")
    };
    let ExprKind::App(f3, dec) = f2.kind() else {
        panic!("not 3-arg app")
    };
    let ExprKind::App(f4, c) = f3.kind() else {
        panic!("not 2-arg app")
    };
    let ExprKind::App(head, alpha) = f4.kind() else {
        panic!("not 1-arg app")
    };

    assert!(matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "ite"));
    assert!(matches!(alpha.kind(), ExprKind::Const(n, _) if n.to_string() == "Int"));
    assert!(expr_contains_const(c, "LT.lt"), "pos 2 must be condition");
    assert!(
        !expr_contains_const(c, "instDecidable"),
        "pos 2 must NOT be Decidable"
    );
    assert!(
        expr_contains_const(dec, "instDecidableNatLt"),
        "pos 3 must be Decidable"
    );
    assert!(matches!(t.kind(), ExprKind::Const(n, _) if n.to_string() == "myThen"));
    assert!(matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == "myElse"));
}

// --- mk_ite_checked and Decidable resolution tests ---

#[test]
fn test_mk_ite_checked_with_lt_condition() {
    // @ite.{1} Int instDecidableNatLt (LT.lt ...) 0 1
    // mk_ite_checked should resolve Decidable for LT.lt conditions
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let cond = mk_lt(&Sort::Int, &a, &b);
    let then_br = Expr::const_(Name::from_string("zero"), vec![]);
    let else_br = Expr::const_(Name::from_string("one"), vec![]);
    let ite = mk_ite_checked(&Sort::Int, &cond, &then_br, &else_br);
    assert!(
        ite.is_some(),
        "mk_ite_checked should resolve Decidable for LT.lt"
    );
    let ite = ite.unwrap();
    let head = ite.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "ite");
            assert_eq!(levels.len(), 1);
            assert_eq!(levels[0], Level::succ(Level::zero()));
        }
        _ => panic!("expected Const(ite, [1]), got {:?}", head),
    }
    assert!(
        expr_contains_const(&ite, "instDecidableNatLt"),
        "should use instDecidableNatLt, not fabricated instDecidable"
    );
}

#[test]
fn test_mk_ite_checked_with_le_condition() {
    // mk_ite_checked should resolve Decidable for LE.le conditions
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let cond = mk_le(&Sort::Int, &a, &b);
    let then_br = Expr::const_(Name::from_string("zero"), vec![]);
    let else_br = Expr::const_(Name::from_string("one"), vec![]);
    let ite = mk_ite_checked(&Sort::Int, &cond, &then_br, &else_br);
    assert!(
        ite.is_some(),
        "mk_ite_checked should resolve Decidable for LE.le"
    );
    assert!(
        expr_contains_const(&ite.unwrap(), "instDecidableNatLe"),
        "should use instDecidableNatLe"
    );
}

#[test]
fn test_mk_ite_checked_unknown_condition_returns_none() {
    // A condition that is not LT.lt or LE.le should return None
    let unknown_cond = Expr::const_(Name::from_string("SomeUnknownProp"), vec![]);
    let then_br = Expr::const_(Name::from_string("zero"), vec![]);
    let else_br = Expr::const_(Name::from_string("one"), vec![]);
    let result = mk_ite_checked(&Sort::Int, &unknown_cond, &then_br, &else_br);
    assert!(
        result.is_none(),
        "mk_ite_checked should return None for unknown conditions"
    );
}
