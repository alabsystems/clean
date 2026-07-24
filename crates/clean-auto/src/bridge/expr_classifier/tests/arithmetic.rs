// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for arithmetic operator classification:
//! Add, Sub, Mul, Div, Mod, Neg in direct, typeclass, and H-forms.

use super::*;

#[test]
fn test_classify_add_direct() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    match classify_expr(&app2(mk_const("Nat.add"), a.clone(), b.clone())) {
        LogicalForm::Add { ty, lhs, rhs, .. } => {
            assert_eq!(ty, mk_const("Nat"));
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Add, got {other:?}"),
    }
    assert!(matches!(
        classify_expr(&app2(mk_const("Int.add"), a.clone(), b.clone())),
        LogicalForm::Add { .. }
    ));
    match classify_expr(&app2(mk_const("Real.add"), a.clone(), b.clone())) {
        LogicalForm::Add { ty, lhs, rhs, .. } => {
            assert_eq!(ty, mk_const("Real"));
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Add for Real.add, got {other:?}"),
    }
}

#[test]
fn test_classify_add_typeclass() {
    // @HAdd.hAdd Nat Nat Nat inst a b — 6 args
    let nat = mk_const("Nat");
    let inst = mk_const("instHAddNatNat");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let hadd = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(mk_const("HAdd.hAdd"), nat.clone()), nat.clone()),
                    nat.clone(),
                ),
                inst,
            ),
            a.clone(),
        ),
        b.clone(),
    );
    match classify_expr(&hadd) {
        LogicalForm::Add { ty, lhs, rhs, .. } => {
            assert_eq!(ty, nat);
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Add (HAdd.hAdd), got {other:?}"),
    }
}

#[test]
fn test_classify_sub_nat_monus() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    match classify_expr(&app2(mk_const("Nat.sub"), a.clone(), b.clone())) {
        LogicalForm::Sub { ty, lhs, rhs, .. } => {
            assert_eq!(ty, mk_const("Nat"), "Nat.sub should carry Nat type");
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Sub, got {other:?}"),
    }
}

#[test]
fn test_classify_sub_int() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    match classify_expr(&app2(mk_const("Int.sub"), a.clone(), b.clone())) {
        LogicalForm::Sub { ty, .. } => {
            assert_eq!(ty, mk_const("Int"), "Int.sub should carry Int type");
        }
        other => panic!("expected Sub, got {other:?}"),
    }
    match classify_expr(&app2(mk_const("Real.sub"), a.clone(), b.clone())) {
        LogicalForm::Sub { ty, lhs, rhs, .. } => {
            assert_eq!(ty, mk_const("Real"), "Real.sub should carry Real type");
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Sub for Real.sub, got {other:?}"),
    }
}

#[test]
fn test_classify_mul() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    assert!(matches!(
        classify_expr(&app2(mk_const("Nat.mul"), a.clone(), b.clone())),
        LogicalForm::Mul { .. }
    ));
    assert!(matches!(
        classify_expr(&app2(mk_const("Int.mul"), a.clone(), b.clone())),
        LogicalForm::Mul { .. }
    ));
    match classify_expr(&app2(mk_const("Real.mul"), a.clone(), b.clone())) {
        LogicalForm::Mul { ty, lhs, rhs, .. } => {
            assert_eq!(ty, mk_const("Real"));
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Mul for Real.mul, got {other:?}"),
    }
}

#[test]
fn test_classify_div() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    match classify_expr(&app2(mk_const("Nat.div"), a.clone(), b.clone())) {
        LogicalForm::Div { ty, .. } => {
            assert_eq!(
                ty,
                mk_const("Nat"),
                "Nat.div carries Nat type for total-div dispatch"
            );
        }
        other => panic!("expected Div, got {other:?}"),
    }
    assert!(matches!(
        classify_expr(&app2(mk_const("Int.div"), a.clone(), b.clone())),
        LogicalForm::Div { .. }
    ));
    match classify_expr(&app2(mk_const("Real.div"), a.clone(), b.clone())) {
        LogicalForm::Div { ty, lhs, rhs, .. } => {
            assert_eq!(ty, mk_const("Real"), "Real.div should carry Real type");
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Div for Real.div, got {other:?}"),
    }
}

#[test]
fn test_classify_mod() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    match classify_expr(&app2(mk_const("Nat.mod"), a.clone(), b.clone())) {
        LogicalForm::Mod { ty, .. } => {
            assert_eq!(
                ty,
                mk_const("Nat"),
                "Nat.mod carries Nat type for total-mod dispatch"
            );
        }
        other => panic!("expected Mod, got {other:?}"),
    }
    assert!(matches!(
        classify_expr(&app2(mk_const("Int.mod"), a.clone(), b.clone())),
        LogicalForm::Mod { .. }
    ));
}

#[test]
fn test_classify_neg() {
    let a = mk_fvar(1);
    match classify_expr(&Expr::app(mk_const("Int.neg"), a.clone())) {
        LogicalForm::Neg { ty, inner, .. } => {
            assert_eq!(ty, mk_const("Int"));
            assert_eq!(inner, a);
        }
        other => panic!("expected Neg, got {other:?}"),
    }
}

#[test]
fn test_classify_neg_typeclass() {
    // @Neg.neg Int instNegInt a — 3 args: [type, instance, operand]
    let int = mk_const("Int");
    let inst = mk_const("instNegInt");
    let a = mk_fvar(1);
    let neg = Expr::app(
        Expr::app(Expr::app(mk_const("Neg.neg"), int.clone()), inst),
        a.clone(),
    );
    // 3 args with min_typed_args=3 for Neg → args[0] = Int used as type (#2301)
    match classify_expr(&neg) {
        LogicalForm::Neg { ty, .. } => {
            assert_eq!(ty, int, "Neg.neg 3-arg form should use args[0] as type");
        }
        other => panic!("expected Neg, got {other:?}"),
    }
}

#[test]
fn test_classify_hsub_typeclass() {
    // @HSub.hSub Int Int Int instHSubIntInt a b — 6 args
    let int = mk_const("Int");
    let inst = mk_const("instHSubIntInt");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let hsub = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(mk_const("HSub.hSub"), int.clone()), int.clone()),
                    int.clone(),
                ),
                inst,
            ),
            a.clone(),
        ),
        b.clone(),
    );
    match classify_expr(&hsub) {
        LogicalForm::Sub { ty, lhs, rhs, .. } => {
            assert_eq!(ty, int, "HSub.hSub with Int type args should carry Int");
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Sub (HSub.hSub), got {other:?}"),
    }
}

#[test]
fn test_arithmetic_original_preserves_expr() {
    // Verify that the `original` field preserves the input expression
    // for faithful round-trip through logicalform_to_expr.
    let a = mk_fvar(1);
    let b = mk_fvar(2);

    // Binary: Nat.add a b
    let add_expr = app2(mk_const("Nat.add"), a.clone(), b.clone());
    match classify_expr(&add_expr) {
        LogicalForm::Add { original, .. } => {
            assert_eq!(
                original, add_expr,
                "original should be the classified expression"
            );
        }
        other => panic!("expected Add, got {other:?}"),
    }

    // Unary: Int.neg a
    let neg_expr = Expr::app(mk_const("Int.neg"), a.clone());
    match classify_expr(&neg_expr) {
        LogicalForm::Neg { original, .. } => {
            assert_eq!(original, neg_expr, "Neg original should preserve negation");
        }
        other => panic!("expected Neg, got {other:?}"),
    }
}

#[test]
fn test_classify_hsub_nat_typeclass() {
    // @HSub.hSub Nat Nat Nat instHSubNat a b — 6 args
    // This is the common elaboration of `a - b` for Nat in .olean files.
    // The type (args[0] = Nat) must propagate so translate_arithmetic_form
    // applies monus semantics (#2254).
    let nat = mk_const("Nat");
    let inst = mk_const("instHSubNat");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let hsub = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(mk_const("HSub.hSub"), nat.clone()), nat.clone()),
                    nat.clone(),
                ),
                inst,
            ),
            a.clone(),
        ),
        b.clone(),
    );
    match classify_expr(&hsub) {
        LogicalForm::Sub { ty, lhs, rhs, .. } => {
            assert_eq!(ty, nat, "HSub.hSub with Nat type args should carry Nat");
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Sub (HSub.hSub Nat), got {other:?}"),
    }
}

#[test]
fn test_classify_hdiv_nat_typeclass() {
    // @HDiv.hDiv Nat Nat Nat instHDivNat a b — 6 args
    let nat = mk_const("Nat");
    let inst = mk_const("instHDivNat");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let hdiv = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(mk_const("HDiv.hDiv"), nat.clone()), nat.clone()),
                    nat.clone(),
                ),
                inst,
            ),
            a.clone(),
        ),
        b.clone(),
    );
    match classify_expr(&hdiv) {
        LogicalForm::Div { ty, lhs, rhs, .. } => {
            assert_eq!(ty, nat, "HDiv.hDiv with Nat type args should carry Nat");
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Div (HDiv.hDiv Nat), got {other:?}"),
    }
}

#[test]
fn test_classify_hmod_nat_typeclass() {
    // @HMod.hMod Nat Nat Nat instHModNat a b — 6 args
    let nat = mk_const("Nat");
    let inst = mk_const("instHModNat");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let hmod = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(mk_const("HMod.hMod"), nat.clone()), nat.clone()),
                    nat.clone(),
                ),
                inst,
            ),
            a.clone(),
        ),
        b.clone(),
    );
    match classify_expr(&hmod) {
        LogicalForm::Mod { ty, lhs, rhs, .. } => {
            assert_eq!(ty, nat, "HMod.hMod with Nat type args should carry Nat");
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Mod (HMod.hMod Nat), got {other:?}"),
    }
}

#[test]
fn test_classify_bare_typeclass_arithmetic_not_classified() {
    // Bare 2-arg typeclass forms without type/instance args should NOT classify (#2301).
    let a = mk_fvar(1);
    let b = mk_fvar(2);

    // HAdd.hAdd with only 2 args — missing α, β, γ, inst
    assert!(
        matches!(
            classify_expr(&app2(mk_const("HAdd.hAdd"), a.clone(), b.clone())),
            LogicalForm::Atom(_)
        ),
        "HAdd.hAdd with 2 args should fall through to Atom"
    );

    // Add.add with only 2 args — missing type and instance
    assert!(
        matches!(
            classify_expr(&app2(mk_const("Add.add"), a.clone(), b.clone())),
            LogicalForm::Atom(_)
        ),
        "Add.add with 2 args should fall through to Atom"
    );

    // LT.lt with only 2 args — missing type and instance
    assert!(
        matches!(
            classify_expr(&app2(mk_const("LT.lt"), a.clone(), b.clone())),
            LogicalForm::Atom(_)
        ),
        "LT.lt with 2 args should fall through to Atom"
    );
}

#[test]
fn test_classify_bare_typeclass_all_arith_forms_not_classified() {
    // All binary typeclass arith forms with only 2 args (missing type/instance)
    // should fall through to Atom (#2301).
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let binary_forms = [
        "HSub.hSub",
        "Sub.sub",
        "HMul.hMul",
        "Mul.mul",
        "HDiv.hDiv",
        "Div.div",
        "HMod.hMod",
        "Mod.mod",
    ];
    for name in binary_forms {
        assert!(
            matches!(
                classify_expr(&app2(mk_const(name), a.clone(), b.clone())),
                LogicalForm::Atom(_)
            ),
            "{name} with 2 args should fall through to Atom"
        );
    }
}

#[test]
fn test_classify_neg_with_insufficient_args_not_classified() {
    // Neg.neg (typeclass) with 2 args (missing instance) — has FromArgs sort hint
    // so resolve_arithmetic_type returns None since n=2 < min_typed_args=3
    let a = mk_fvar(1);
    let dummy = mk_fvar(2);
    assert!(
        matches!(
            classify_expr(&app2(mk_const("Neg.neg"), a, dummy)),
            LogicalForm::Atom(_)
        ),
        "Neg.neg with 2 args should fall through to Atom"
    );
}
