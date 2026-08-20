// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::encoding::{TlaArithOp, TlaCmpOp, TlaExpr, TlaFormula, TlaOperator};
use crate::obligation::TlaDeclare;
use crate::tla_core::{self, ast as core_ast, Spanned};
use crate::TlaError;
use std::convert::TryFrom;

#[test]
fn test_tla_core_reexport_uses_real_ty_interner() {
    let first = tla_core::intern_name("clean_tla_real_ty_interner_first");
    let second = tla_core::intern_name("clean_tla_real_ty_interner_second");

    assert_ne!(
        first, second,
        "clean-tla must use Ty's real interner, not a constant compatibility stub"
    );
}

// ============================================================================
// Expression conversion tests (from_tla_core)
// ============================================================================

#[test]
fn test_expr_from_tla_core_add() {
    let expr = Spanned::dummy(core_ast::Expr::Add(
        Box::new(Spanned::dummy(core_ast::Expr::Int(2.into()))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(3.into()))),
    ));
    let compat = TlaExpr::from_tla_core(&expr).expect("addition should convert");
    assert_eq!(
        compat,
        TlaExpr::Arith(
            TlaArithOp::Add,
            Box::new(TlaExpr::Int(2)),
            Box::new(TlaExpr::Int(3))
        )
    );
}

#[test]
fn test_expr_from_tla_core_bool_true() {
    let expr = Spanned::dummy(core_ast::Expr::Bool(true));
    assert_eq!(TlaExpr::from_tla_core(&expr).unwrap(), TlaExpr::True);
}

#[test]
fn test_expr_from_tla_core_bool_false() {
    let expr = Spanned::dummy(core_ast::Expr::Bool(false));
    assert_eq!(TlaExpr::from_tla_core(&expr).unwrap(), TlaExpr::False);
}

#[test]
fn test_expr_from_tla_core_string_literal() {
    let expr = Spanned::dummy(core_ast::Expr::String("hello".to_string()));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Str("hello".to_string())
    );
}

#[test]
fn test_expr_from_tla_core_ident() {
    let expr = Spanned::dummy(core_ast::Expr::Ident(
        "x".to_string(),
        tla_core::intern_name("x"),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Var("x".to_string())
    );
}

#[test]
fn test_expr_from_tla_core_opref() {
    let expr = Spanned::dummy(core_ast::Expr::OpRef("MyOp".to_string()));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Const("MyOp".to_string())
    );
}

#[test]
fn test_expr_from_tla_core_neg() {
    let expr = Spanned::dummy(core_ast::Expr::Neg(Box::new(Spanned::dummy(
        core_ast::Expr::Int(5.into()),
    ))));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Neg(Box::new(TlaExpr::Int(5)))
    );
}

#[test]
fn test_expr_from_tla_core_set_enum() {
    let expr = Spanned::dummy(core_ast::Expr::SetEnum(vec![
        Spanned::dummy(core_ast::Expr::Int(1.into())),
        Spanned::dummy(core_ast::Expr::Int(2.into())),
    ]));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::SetEnum(vec![TlaExpr::Int(1), TlaExpr::Int(2)])
    );
}

#[test]
fn test_expr_from_tla_core_membership() {
    let expr = Spanned::dummy(core_ast::Expr::In(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "x".to_string(),
            tla_core::intern_name("x"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "S".to_string(),
            tla_core::intern_name("S"),
        ))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Mem(
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Var("S".to_string()))
        )
    );
}

#[test]
fn test_expr_from_tla_core_subseteq() {
    let expr = Spanned::dummy(core_ast::Expr::Subseteq(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "A".to_string(),
            tla_core::intern_name("A"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "B".to_string(),
            tla_core::intern_name("B"),
        ))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Subset(
            Box::new(TlaExpr::Var("A".to_string())),
            Box::new(TlaExpr::Var("B".to_string()))
        )
    );
}

#[test]
fn test_expr_from_tla_core_func_apply() {
    let expr = Spanned::dummy(core_ast::Expr::FuncApply(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "f".to_string(),
            tla_core::intern_name("f"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Apply(
            Box::new(TlaExpr::Var("f".to_string())),
            Box::new(TlaExpr::Int(1))
        )
    );
}

#[test]
fn test_expr_from_tla_core_domain() {
    let expr = Spanned::dummy(core_ast::Expr::Domain(Box::new(Spanned::dummy(
        core_ast::Expr::Ident("f".to_string(), tla_core::intern_name("f")),
    ))));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Domain(Box::new(TlaExpr::Var("f".to_string())))
    );
}

#[test]
fn test_expr_from_tla_core_range() {
    let expr = Spanned::dummy(core_ast::Expr::Range(
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(10.into()))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Range(Box::new(TlaExpr::Int(1)), Box::new(TlaExpr::Int(10)))
    );
}

#[test]
fn test_expr_from_tla_core_all_arith_ops() {
    let cases: Vec<(fn(_, _) -> core_ast::Expr, TlaArithOp)> = vec![
        (|l, r| core_ast::Expr::Add(l, r), TlaArithOp::Add),
        (|l, r| core_ast::Expr::Sub(l, r), TlaArithOp::Sub),
        (|l, r| core_ast::Expr::Mul(l, r), TlaArithOp::Mul),
        (|l, r| core_ast::Expr::Div(l, r), TlaArithOp::Div),
        (|l, r| core_ast::Expr::Mod(l, r), TlaArithOp::Mod),
    ];
    for (ctor, expected_op) in cases {
        let expr = Spanned::dummy(ctor(
            Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
            Box::new(Spanned::dummy(core_ast::Expr::Int(2.into()))),
        ));
        let result = TlaExpr::from_tla_core(&expr).unwrap();
        assert_eq!(
            result,
            TlaExpr::Arith(
                expected_op,
                Box::new(TlaExpr::Int(1)),
                Box::new(TlaExpr::Int(2))
            )
        );
    }
}

#[test]
fn test_expr_from_tla_core_all_cmp_ops() {
    let cases: Vec<(fn(_, _) -> core_ast::Expr, TlaCmpOp)> = vec![
        (|l, r| core_ast::Expr::Lt(l, r), TlaCmpOp::Lt),
        (|l, r| core_ast::Expr::Leq(l, r), TlaCmpOp::Le),
        (|l, r| core_ast::Expr::Gt(l, r), TlaCmpOp::Gt),
        (|l, r| core_ast::Expr::Geq(l, r), TlaCmpOp::Ge),
    ];
    for (ctor, expected_op) in cases {
        let expr = Spanned::dummy(ctor(
            Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
            Box::new(Spanned::dummy(core_ast::Expr::Int(2.into()))),
        ));
        let result = TlaExpr::from_tla_core(&expr).unwrap();
        assert_eq!(
            result,
            TlaExpr::Cmp(
                expected_op,
                Box::new(TlaExpr::Int(1)),
                Box::new(TlaExpr::Int(2))
            )
        );
    }
}

#[test]
fn test_expr_from_tla_core_set_ops() {
    // Union
    let expr = Spanned::dummy(core_ast::Expr::Union(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "A".to_string(),
            tla_core::intern_name("A"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "B".to_string(),
            tla_core::intern_name("B"),
        ))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Union(
            Box::new(TlaExpr::Var("A".to_string())),
            Box::new(TlaExpr::Var("B".to_string()))
        )
    );

    // Intersect
    let expr = Spanned::dummy(core_ast::Expr::Intersect(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "A".to_string(),
            tla_core::intern_name("A"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "B".to_string(),
            tla_core::intern_name("B"),
        ))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Inter(
            Box::new(TlaExpr::Var("A".to_string())),
            Box::new(TlaExpr::Var("B".to_string()))
        )
    );

    // SetMinus
    let expr = Spanned::dummy(core_ast::Expr::SetMinus(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "A".to_string(),
            tla_core::intern_name("A"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "B".to_string(),
            tla_core::intern_name("B"),
        ))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Diff(
            Box::new(TlaExpr::Var("A".to_string())),
            Box::new(TlaExpr::Var("B".to_string()))
        )
    );
}

#[test]
fn test_expr_from_tla_core_powerset() {
    let expr = Spanned::dummy(core_ast::Expr::Powerset(Box::new(Spanned::dummy(
        core_ast::Expr::Ident("S".to_string(), tla_core::intern_name("S")),
    ))));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::PowerSet(Box::new(TlaExpr::Var("S".to_string())))
    );
}

#[test]
fn test_expr_from_tla_core_big_union() {
    let expr = Spanned::dummy(core_ast::Expr::BigUnion(Box::new(Spanned::dummy(
        core_ast::Expr::Ident("S".to_string(), tla_core::intern_name("S")),
    ))));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::BigUnion(Box::new(TlaExpr::Var("S".to_string())))
    );
}

#[test]
fn test_expr_from_tla_core_if_then_else() {
    let expr = Spanned::dummy(core_ast::Expr::If(
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(0.into()))),
    ));
    let result = TlaExpr::from_tla_core(&expr).unwrap();
    assert!(matches!(result, TlaExpr::IfThenElse(_, _, _)));
}

/// Build the bounded CHOOSE `CHOOSE x ∈ S : x > 0` as a tla-core expression.
fn core_bounded_choose() -> Spanned<core_ast::Expr> {
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("x".to_string()),
        domain: Some(Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "S".to_string(),
            tla_core::intern_name("S"),
        )))),
        pattern: None,
    };
    let predicate = Spanned::dummy(core_ast::Expr::Gt(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "x".to_string(),
            tla_core::intern_name("x"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(0.into()))),
    ));
    Spanned::dummy(core_ast::Expr::Choose(bound, Box::new(predicate)))
}

#[test]
fn test_expr_from_tla_core_bounded_choose_maps_to_choose() {
    // CHOOSE x ∈ S : x > 0 → TlaExpr::Choose("x", S, x > 0)
    let result =
        TlaExpr::from_tla_core(&core_bounded_choose()).expect("bounded CHOOSE should convert");
    match result {
        TlaExpr::Choose(name, domain, pred) => {
            assert_eq!(name, "x");
            assert_eq!(*domain, TlaExpr::Var("S".to_string()));
            assert_eq!(
                *pred,
                TlaFormula::Expr(TlaExpr::Cmp(
                    TlaCmpOp::Gt,
                    Box::new(TlaExpr::Var("x".to_string())),
                    Box::new(TlaExpr::Int(0)),
                ))
            );
        }
        other => panic!("expected TlaExpr::Choose, got {other:?}"),
    }
}

#[test]
fn test_expr_from_tla_core_unbounded_choose_returns_error() {
    // CHOOSE x : x > 0 (no domain) is not representable — must error, not
    // fabricate a domain.
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("x".to_string()),
        domain: None,
        pattern: None,
    };
    let predicate = Spanned::dummy(core_ast::Expr::Gt(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "x".to_string(),
            tla_core::intern_name("x"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(0.into()))),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Choose(bound, Box::new(predicate)));
    assert!(
        TlaExpr::from_tla_core(&expr).is_err(),
        "unbounded CHOOSE must not convert"
    );
}

#[test]
fn test_expr_from_tla_core_tuple_pattern_choose_returns_error() {
    // CHOOSE <<a, b>> ∈ S : P — tuple-pattern binders are not representable.
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("p".to_string()),
        domain: Some(Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "S".to_string(),
            tla_core::intern_name("S"),
        )))),
        pattern: Some(core_ast::BoundPattern::Tuple(vec![
            Spanned::dummy("a".to_string()),
            Spanned::dummy("b".to_string()),
        ])),
    };
    let predicate = Spanned::dummy(core_ast::Expr::Bool(true));
    let expr = Spanned::dummy(core_ast::Expr::Choose(bound, Box::new(predicate)));
    assert!(
        TlaExpr::from_tla_core(&expr).is_err(),
        "tuple-pattern CHOOSE must not convert"
    );
}

#[test]
fn test_expr_from_tla_core_choose_translates_to_tla_choose() {
    use crate::encoding::TlaContext;
    use clean_kernel::expr::ExprKind;

    fn outermost(expr: &clean_kernel::expr::Expr) -> Option<String> {
        match expr.kind() {
            ExprKind::Const(name, _) => Some(name.to_string()),
            ExprKind::App(f, _) => outermost(f),
            _ => None,
        }
    }

    // End-to-end: a bounded CHOOSE coming through the tla-core path encodes
    // to the `TLA.choose` operator (no UnsupportedCoreAst on the way).
    let mut ctx = TlaContext::new();
    let lean = ctx
        .translate_tla_core_expr(&core_bounded_choose())
        .expect("bounded CHOOSE should translate end-to-end");
    assert_eq!(outermost(&lean).as_deref(), Some("TLA.choose"));
}

#[test]
fn test_expr_from_tla_core_tuple() {
    let expr = Spanned::dummy(core_ast::Expr::Tuple(vec![
        Spanned::dummy(core_ast::Expr::Int(1.into())),
        Spanned::dummy(core_ast::Expr::Int(2.into())),
        Spanned::dummy(core_ast::Expr::Int(3.into())),
    ]));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Tuple(vec![TlaExpr::Int(1), TlaExpr::Int(2), TlaExpr::Int(3)])
    );
}

#[test]
fn test_expr_from_tla_core_record_set_preserves_fields_in_order() {
    // A record-set `[a: S, b: T]` converts to `TlaExpr::RecordSet`, mirroring
    // the `Record` value constructor: field names are kept in order and each
    // domain set is converted structurally.
    let expr = Spanned::dummy(core_ast::Expr::RecordSet(vec![
        (Spanned::dummy("a".to_string()), ident("S")),
        (Spanned::dummy("b".to_string()), ident("T")),
    ]));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("record set should convert"),
        TlaExpr::RecordSet(vec![
            ("a".to_string(), TlaExpr::Var("S".to_string())),
            ("b".to_string(), TlaExpr::Var("T".to_string())),
        ])
    );
}

#[test]
fn test_expr_from_tla_core_pow_maps_to_arith_pow() {
    // `x ^ 2` → TlaExpr::Arith(Pow, Var("x"), Int(2)).
    let expr = Spanned::dummy(core_ast::Expr::Pow(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "x".to_string(),
            tla_core::intern_name("x"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(2.into()))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("exponentiation should convert"),
        TlaExpr::Arith(
            TlaArithOp::Pow,
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Int(2)),
        )
    );
}

#[test]
fn test_expr_from_tla_core_prime_maps_to_prime() {
    // x' → TlaExpr::Prime(Var("x"))
    let expr = Spanned::dummy(core_ast::Expr::Prime(Box::new(Spanned::dummy(
        core_ast::Expr::Ident("x".to_string(), tla_core::intern_name("x")),
    ))));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("prime should convert"),
        TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string())))
    );
}

#[test]
fn test_formula_from_tla_core_unchanged_maps_to_unchanged() {
    // UNCHANGED v → TlaFormula::Unchanged(Var("v"))
    let expr = Spanned::dummy(core_ast::Expr::Unchanged(Box::new(Spanned::dummy(
        core_ast::Expr::Ident("v".to_string(), tla_core::intern_name("v")),
    ))));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).expect("unchanged should convert"),
        TlaFormula::Unchanged(Box::new(TlaExpr::Var("v".to_string())))
    );
}

#[test]
fn test_formula_from_tla_core_enabled_maps_to_enabled() {
    // ENABLED (x' = x) → TlaFormula::Enabled(Eq(Prime(x), x))
    let action = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(Spanned::dummy(core_ast::Expr::Prime(Box::new(
            Spanned::dummy(core_ast::Expr::Ident(
                "x".to_string(),
                tla_core::intern_name("x"),
            )),
        )))),
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "x".to_string(),
            tla_core::intern_name("x"),
        ))),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Enabled(Box::new(action)));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).expect("enabled should convert"),
        TlaFormula::Enabled(Box::new(TlaFormula::Eq(
            Box::new(TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string())))),
            Box::new(TlaExpr::Var("x".to_string())),
        )))
    );
}

#[test]
fn test_expr_from_tla_core_prime_in_action_round_trips() {
    // Full action: x' = x + 1 (mixing primed and unprimed) converts cleanly.
    let action = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(Spanned::dummy(core_ast::Expr::Prime(Box::new(
            Spanned::dummy(core_ast::Expr::Ident(
                "x".to_string(),
                tla_core::intern_name("x"),
            )),
        )))),
        Box::new(Spanned::dummy(core_ast::Expr::Add(
            Box::new(Spanned::dummy(core_ast::Expr::Ident(
                "x".to_string(),
                tla_core::intern_name("x"),
            ))),
            Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
        ))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&action).expect("action should convert"),
        TlaFormula::Eq(
            Box::new(TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string())))),
            Box::new(TlaExpr::Arith(
                TlaArithOp::Add,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(1)),
            )),
        )
    );
}

// ============================================================================
// Formula conversion tests (from_tla_core)
// ============================================================================

#[test]
fn test_formula_from_tla_core_bounded_forall() {
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("x".to_string()),
        domain: Some(Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "S".to_string(),
            tla_core::intern_name("S"),
        )))),
        pattern: None,
    };
    let expr = Spanned::dummy(core_ast::Expr::Forall(
        vec![bound],
        Box::new(Spanned::dummy(core_ast::Expr::Eq(
            Box::new(Spanned::dummy(core_ast::Expr::Ident(
                "x".to_string(),
                tla_core::intern_name("x"),
            ))),
            Box::new(Spanned::dummy(core_ast::Expr::Ident(
                "x".to_string(),
                tla_core::intern_name("x"),
            ))),
        ))),
    ));
    let compat = TlaFormula::from_tla_core(&expr).expect("forall should convert");
    assert!(matches!(compat, TlaFormula::ForallIn(_, _, _)));
}

#[test]
fn test_formula_from_tla_core_unbounded_forall() {
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("x".to_string()),
        domain: None,
        pattern: None,
    };
    let expr = Spanned::dummy(core_ast::Expr::Forall(
        vec![bound],
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    let result = TlaFormula::from_tla_core(&expr).unwrap();
    assert!(matches!(result, TlaFormula::Forall(_, _)));
}

#[test]
fn test_formula_from_tla_core_bounded_exists() {
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("x".to_string()),
        domain: Some(Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "S".to_string(),
            tla_core::intern_name("S"),
        )))),
        pattern: None,
    };
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![bound],
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    let result = TlaFormula::from_tla_core(&expr).unwrap();
    assert!(matches!(result, TlaFormula::ExistsIn(_, _, _)));
}

#[test]
fn test_formula_from_tla_core_and() {
    let expr = Spanned::dummy(core_ast::Expr::And(
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(false))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::And(Box::new(TlaFormula::True), Box::new(TlaFormula::False))
    );
}

#[test]
fn test_formula_from_tla_core_or() {
    let expr = Spanned::dummy(core_ast::Expr::Or(
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(false))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Or(Box::new(TlaFormula::True), Box::new(TlaFormula::False))
    );
}

#[test]
fn test_formula_from_tla_core_not() {
    let expr = Spanned::dummy(core_ast::Expr::Not(Box::new(Spanned::dummy(
        core_ast::Expr::Bool(true),
    ))));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Not(Box::new(TlaFormula::True))
    );
}

#[test]
fn test_formula_from_tla_core_implies() {
    let expr = Spanned::dummy(core_ast::Expr::Implies(
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(false))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Implies(Box::new(TlaFormula::True), Box::new(TlaFormula::False))
    );
}

#[test]
fn test_formula_from_tla_core_equiv_to_iff() {
    let expr = Spanned::dummy(core_ast::Expr::Equiv(
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Iff(Box::new(TlaFormula::True), Box::new(TlaFormula::True))
    );
}

#[test]
fn test_formula_from_tla_core_eq() {
    let expr = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Eq(Box::new(TlaExpr::Int(1)), Box::new(TlaExpr::Int(1)))
    );
}

#[test]
fn test_formula_from_tla_core_neq_desugars_to_not_eq() {
    let expr = Spanned::dummy(core_ast::Expr::Neq(
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
        Box::new(Spanned::dummy(core_ast::Expr::Int(2.into()))),
    ));
    let result = TlaFormula::from_tla_core(&expr).unwrap();
    assert!(matches!(result, TlaFormula::Not(inner) if matches!(*inner, TlaFormula::Eq(_, _))));
}

#[test]
fn test_formula_from_tla_core_notin_desugars_to_not_mem() {
    let expr = Spanned::dummy(core_ast::Expr::NotIn(
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "x".to_string(),
            tla_core::intern_name("x"),
        ))),
        Box::new(Spanned::dummy(core_ast::Expr::Ident(
            "S".to_string(),
            tla_core::intern_name("S"),
        ))),
    ));
    let result = TlaFormula::from_tla_core(&expr).unwrap();
    assert!(matches!(result, TlaFormula::Not(inner) if matches!(*inner, TlaFormula::Mem(_, _))));
}

#[test]
fn test_formula_from_tla_core_always() {
    let expr = Spanned::dummy(core_ast::Expr::Always(Box::new(Spanned::dummy(
        core_ast::Expr::Bool(true),
    ))));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Always(Box::new(TlaFormula::True))
    );
}

#[test]
fn test_formula_from_tla_core_eventually() {
    let expr = Spanned::dummy(core_ast::Expr::Eventually(Box::new(Spanned::dummy(
        core_ast::Expr::Bool(true),
    ))));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Eventually(Box::new(TlaFormula::True))
    );
}

#[test]
fn test_formula_from_tla_core_leads_to() {
    let expr = Spanned::dummy(core_ast::Expr::LeadsTo(
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(false))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::LeadsTo(Box::new(TlaFormula::True), Box::new(TlaFormula::False))
    );
}

#[test]
fn test_formula_from_tla_core_non_formula_falls_through_to_expr() {
    // An integer literal is not a formula, so it should be wrapped in TlaFormula::Expr
    let expr = Spanned::dummy(core_ast::Expr::Int(42.into()));
    let result = TlaFormula::from_tla_core(&expr).unwrap();
    assert_eq!(result, TlaFormula::Expr(TlaExpr::Int(42)));
}

#[test]
fn test_formula_from_tla_core_always_eventually_nested() {
    // []<>P : Always(Eventually(P)) — the conversion must recurse into the
    // nested temporal sub-formula rather than dropping it.
    let expr = Spanned::dummy(core_ast::Expr::Always(Box::new(Spanned::dummy(
        core_ast::Expr::Eventually(Box::new(Spanned::dummy(core_ast::Expr::OpRef(
            "P".to_string(),
        )))),
    ))));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Always(Box::new(TlaFormula::Eventually(Box::new(
            TlaFormula::Expr(TlaExpr::Const("P".to_string()))
        ))))
    );
}

#[test]
fn test_formula_from_tla_core_eventually_always_nested() {
    // <>[]P : Eventually(Always(P)) — eventually-always (stabilization).
    let expr = Spanned::dummy(core_ast::Expr::Eventually(Box::new(Spanned::dummy(
        core_ast::Expr::Always(Box::new(Spanned::dummy(core_ast::Expr::OpRef(
            "P".to_string(),
        )))),
    ))));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Eventually(Box::new(TlaFormula::Always(Box::new(TlaFormula::Expr(
            TlaExpr::Const("P".to_string())
        )))))
    );
}

#[test]
fn test_expr_from_tla_core_always_in_value_position_wraps_formula() {
    // []<>P appearing in value position (e.g. an operator body) must be
    // representable: it is wrapped in TlaExpr::TemporalFormula, not rejected.
    let expr = Spanned::dummy(core_ast::Expr::Always(Box::new(Spanned::dummy(
        core_ast::Expr::Eventually(Box::new(Spanned::dummy(core_ast::Expr::OpRef(
            "P".to_string(),
        )))),
    ))));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("[]<>P should convert in value position"),
        TlaExpr::TemporalFormula(Box::new(TlaFormula::Always(Box::new(
            TlaFormula::Eventually(Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string()))))
        ))))
    );
}

#[test]
fn test_operator_def_with_nested_temporal_body_converts() {
    // Liveness == []<>P  — the canonical infinitely-often liveness spec as an
    // operator definition. This previously failed with UnsupportedCoreAst.
    let op = core_ast::OperatorDef {
        name: Spanned::dummy("Liveness".to_string()),
        params: vec![],
        body: Spanned::dummy(core_ast::Expr::Always(Box::new(Spanned::dummy(
            core_ast::Expr::Eventually(Box::new(Spanned::dummy(core_ast::Expr::OpRef(
                "P".to_string(),
            )))),
        )))),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    let result = TlaOperator::try_from(&op).expect("liveness operator should convert");
    assert_eq!(result.name, "Liveness");
    assert_eq!(
        result.body,
        TlaExpr::TemporalFormula(Box::new(TlaFormula::Always(Box::new(
            TlaFormula::Eventually(Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string()))))
        ))))
    );
}

#[test]
fn test_operator_def_with_weak_fair_body_converts() {
    // Fairness == WF_vars(Next)  as an operator body.
    let op = core_ast::OperatorDef {
        name: Spanned::dummy("Fairness".to_string()),
        params: vec![],
        body: Spanned::dummy(core_ast::Expr::WeakFair(
            Box::new(Spanned::dummy(core_ast::Expr::Ident(
                "vars".to_string(),
                tla_core::intern_name("vars"),
            ))),
            Box::new(Spanned::dummy(core_ast::Expr::OpRef("Next".to_string()))),
        )),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    let result = TlaOperator::try_from(&op).expect("fairness operator should convert");
    assert_eq!(
        result.body,
        TlaExpr::TemporalFormula(Box::new(TlaFormula::WeakFairness(
            Box::new(TlaExpr::Var("vars".to_string())),
            Box::new(TlaFormula::Expr(TlaExpr::Const("Next".to_string())))
        )))
    );
}

// ============================================================================
// TryFrom trait impl tests (structured conversion layer)
// ============================================================================

#[test]
fn test_try_from_spanned_expr_for_tla_expr() {
    let expr = Spanned::dummy(core_ast::Expr::Int(99.into()));
    let result = TlaExpr::try_from(&expr).expect("TryFrom should succeed for Int");
    assert_eq!(result, TlaExpr::Int(99));
}

#[test]
fn test_try_from_spanned_expr_for_tla_formula() {
    let expr = Spanned::dummy(core_ast::Expr::And(
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(false))),
    ));
    let result = TlaFormula::try_from(&expr).expect("TryFrom should succeed for And");
    assert_eq!(
        result,
        TlaFormula::And(Box::new(TlaFormula::True), Box::new(TlaFormula::False))
    );
}

#[test]
fn test_try_from_operator_def_for_tla_operator() {
    let op = core_ast::OperatorDef {
        name: Spanned::dummy("Inc".to_string()),
        params: vec![core_ast::OpParam {
            name: Spanned::dummy("x".to_string()),
            arity: 0,
        }],
        body: Spanned::dummy(core_ast::Expr::Add(
            Box::new(Spanned::dummy(core_ast::Expr::Ident(
                "x".to_string(),
                tla_core::intern_name("x"),
            ))),
            Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
        )),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    let result = TlaOperator::try_from(&op).expect("TryFrom should succeed for operator");
    assert_eq!(result.name, "Inc");
    assert_eq!(result.params, vec!["x".to_string()]);
    assert_eq!(
        result.body,
        TlaExpr::Arith(
            TlaArithOp::Add,
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Int(1))
        )
    );
}

#[test]
fn test_try_from_unsupported_expr_returns_error() {
    // SubstIn (`expr WITH subs`) has no TlaExpr representation; the TryFrom
    // bridge must surface the conversion failure.
    let expr = Spanned::dummy(core_ast::Expr::SubstIn(
        vec![],
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
    ));
    assert!(TlaExpr::try_from(&expr).is_err());
}

// ============================================================================
// Declaration conversion tests (from_tla_core_unit)
// ============================================================================

#[test]
fn test_declare_from_tla_core_constant_unit() {
    let unit = core_ast::Unit::Constant(vec![core_ast::ConstantDecl {
        name: Spanned::dummy("C".to_string()),
        arity: Some(2),
    }]);
    let declares = TlaDeclare::from_tla_core_unit(&unit).expect("constant unit should convert");
    assert_eq!(
        declares,
        vec![TlaDeclare::Constant {
            name: "C".to_string(),
            arity: 2,
        }]
    );
}

#[test]
fn test_declare_from_tla_core_variable_unit() {
    let unit = core_ast::Unit::Variable(vec![
        Spanned::dummy("x".to_string()),
        Spanned::dummy("y".to_string()),
    ]);
    let declares = TlaDeclare::from_tla_core_unit(&unit).unwrap();
    assert_eq!(declares.len(), 2);
    assert_eq!(
        declares[0],
        TlaDeclare::Variable {
            name: "x".to_string()
        }
    );
    assert_eq!(
        declares[1],
        TlaDeclare::Variable {
            name: "y".to_string()
        }
    );
}

#[test]
fn test_declare_from_tla_core_separator_returns_empty() {
    let unit = core_ast::Unit::Separator;
    let declares = TlaDeclare::from_tla_core_unit(&unit).unwrap();
    assert!(declares.is_empty());
}

#[test]
fn test_declare_from_tla_core_instance_with_substitution_captures_mapping() {
    // INSTANCE M WITH x <- e  — must NO LONGER be dropped; it converts to a
    // TlaDeclare::Instance capturing the module name and the x <- e mapping.
    let unit = core_ast::Unit::Instance(core_ast::InstanceDecl {
        module: Spanned::dummy("M".to_string()),
        substitutions: vec![core_ast::Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(core_ast::Expr::Ident(
                "e".to_string(),
                tla_core::intern_name("e"),
            )),
        }],
        local: false,
    });
    let declares = TlaDeclare::from_tla_core_unit(&unit).expect("instance unit should convert");
    assert_eq!(
        declares,
        vec![TlaDeclare::Instance {
            module: "M".to_string(),
            substitutions: vec![("x".to_string(), TlaExpr::Var("e".to_string()))],
        }]
    );
}

#[test]
fn test_declare_from_tla_core_parameterless_instance_captures_empty_mapping() {
    // INSTANCE M (no WITH clause) — a parameterless instantiation. It still
    // produces an Instance declaration, just with an empty substitution list.
    let unit = core_ast::Unit::Instance(core_ast::InstanceDecl {
        module: Spanned::dummy("M".to_string()),
        substitutions: vec![],
        local: false,
    });
    let declares =
        TlaDeclare::from_tla_core_unit(&unit).expect("parameterless instance should convert");
    assert_eq!(
        declares,
        vec![TlaDeclare::Instance {
            module: "M".to_string(),
            substitutions: vec![],
        }]
    );
}

#[test]
fn test_declare_from_tla_core_refinement_mapping_instance_converts() {
    // Impl => Spec via  INSTANCE Spec WITH s <- impl_state, c <- impl_count
    // (a refinement mapping). All substitutions are captured, none dropped.
    let unit = core_ast::Unit::Instance(core_ast::InstanceDecl {
        module: Spanned::dummy("Spec".to_string()),
        substitutions: vec![
            core_ast::Substitution {
                from: Spanned::dummy("s".to_string()),
                to: Spanned::dummy(core_ast::Expr::Ident(
                    "impl_state".to_string(),
                    tla_core::intern_name("impl_state"),
                )),
            },
            core_ast::Substitution {
                from: Spanned::dummy("c".to_string()),
                to: Spanned::dummy(core_ast::Expr::Add(
                    Box::new(Spanned::dummy(core_ast::Expr::Ident(
                        "impl_count".to_string(),
                        tla_core::intern_name("impl_count"),
                    ))),
                    Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
                )),
            },
        ],
        local: false,
    });
    let declares =
        TlaDeclare::from_tla_core_unit(&unit).expect("refinement instance should convert");
    assert_eq!(
        declares,
        vec![TlaDeclare::Instance {
            module: "Spec".to_string(),
            substitutions: vec![
                ("s".to_string(), TlaExpr::Var("impl_state".to_string())),
                (
                    "c".to_string(),
                    TlaExpr::Arith(
                        TlaArithOp::Add,
                        Box::new(TlaExpr::Var("impl_count".to_string())),
                        Box::new(TlaExpr::Int(1)),
                    ),
                ),
            ],
        }]
    );
}

// ============================================================================
// Package A — success-path Expr conversions (additive coverage)
// ============================================================================

/// Helper: a dummy `Spanned<Expr>` identifier referencing `name`.
fn ident(name: &str) -> Spanned<core_ast::Expr> {
    Spanned::dummy(core_ast::Expr::Ident(
        name.to_string(),
        tla_core::intern_name(name),
    ))
}

/// Helper: a single `BoundVar` named `name` with an explicit identifier domain.
fn bound_in(name: &str, domain: &str) -> core_ast::BoundVar {
    core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy(name.to_string()),
        domain: Some(Box::new(ident(domain))),
        pattern: None,
    }
}

#[test]
fn test_expr_from_tla_core_record() {
    // [a |-> x, b |-> y] -> Record([("a", Var x), ("b", Var y)])
    let expr = Spanned::dummy(core_ast::Expr::Record(vec![
        (Spanned::dummy("a".to_string()), ident("x")),
        (Spanned::dummy("b".to_string()), ident("y")),
    ]));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Record(vec![
            ("a".to_string(), TlaExpr::Var("x".to_string())),
            ("b".to_string(), TlaExpr::Var("y".to_string())),
        ])
    );
}

#[test]
fn test_expr_from_tla_core_record_access() {
    // r.field -> Field(Var r, "field")
    let expr = Spanned::dummy(core_ast::Expr::RecordAccess(
        Box::new(ident("r")),
        core_ast::RecordFieldName::new(Spanned::dummy("field".to_string())),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Field(Box::new(TlaExpr::Var("r".to_string())), "field".to_string())
    );
}

#[test]
fn test_expr_from_tla_core_set_builder() {
    // {x : x \in S} -> SetMap(Var x, "x", Var S, None)
    let expr = Spanned::dummy(core_ast::Expr::SetBuilder(
        Box::new(ident("x")),
        vec![bound_in("x", "S")],
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::SetMap(
            Box::new(TlaExpr::Var("x".to_string())),
            "x".to_string(),
            Box::new(TlaExpr::Var("S".to_string())),
            None,
        )
    );
}

#[test]
fn test_expr_from_tla_core_set_filter() {
    // {x \in S : TRUE} -> SetOf(Var S, "x", True)
    let expr = Spanned::dummy(core_ast::Expr::SetFilter(
        bound_in("x", "S"),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::SetOf(
            Box::new(TlaExpr::Var("S".to_string())),
            "x".to_string(),
            Box::new(TlaFormula::True),
        )
    );
}

#[test]
fn test_expr_from_tla_core_func_def() {
    // [x \in S |-> x] -> Func("x", Var S, Var x)
    let expr = Spanned::dummy(core_ast::Expr::FuncDef(
        vec![bound_in("x", "S")],
        Box::new(ident("x")),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Func(
            "x".to_string(),
            Box::new(TlaExpr::Var("S".to_string())),
            Box::new(TlaExpr::Var("x".to_string())),
        )
    );
}

#[test]
fn test_expr_from_tla_core_case() {
    // CASE TRUE -> 1 [] OTHER -> 0
    let expr = Spanned::dummy(core_ast::Expr::Case(
        vec![core_ast::CaseArm {
            guard: Spanned::dummy(core_ast::Expr::Bool(true)),
            body: Spanned::dummy(core_ast::Expr::Int(1.into())),
        }],
        Some(Box::new(Spanned::dummy(core_ast::Expr::Int(0.into())))),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Case(
            vec![(TlaFormula::True, TlaExpr::Int(1))],
            Some(Box::new(TlaExpr::Int(0))),
        )
    );
}

#[test]
fn test_expr_from_tla_core_let_single_def() {
    // LET y == 1 IN y -> Let("y", Int 1, Var y)
    let def = core_ast::OperatorDef {
        name: Spanned::dummy("y".to_string()),
        params: vec![],
        body: Spanned::dummy(core_ast::Expr::Int(1.into())),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    let expr = Spanned::dummy(core_ast::Expr::Let(vec![def], Box::new(ident("y"))));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Let(
            "y".to_string(),
            Box::new(TlaExpr::Int(1)),
            Box::new(TlaExpr::Var("y".to_string())),
        )
    );
}

#[test]
fn test_expr_from_tla_core_module_ref() {
    // M!Op(x) -> OpApply("M!Op", [Var x])
    let expr = Spanned::dummy(core_ast::Expr::ModuleRef(
        core_ast::ModuleTarget::Named("M".to_string()),
        "Op".to_string(),
        vec![ident("x")],
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::OpApply("M!Op".to_string(), vec![TlaExpr::Var("x".to_string())])
    );
}

#[test]
fn test_expr_from_tla_core_apply_op() {
    // F(x, y) -> OpApply("F", [Var x, Var y])
    let expr = Spanned::dummy(core_ast::Expr::Apply(
        Box::new(Spanned::dummy(core_ast::Expr::OpRef("F".to_string()))),
        vec![ident("x"), ident("y")],
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::OpApply(
            "F".to_string(),
            vec![TlaExpr::Var("x".to_string()), TlaExpr::Var("y".to_string())],
        )
    );
}

#[test]
fn test_expr_from_tla_core_label_unwraps_body() {
    // lbl :: x -> Var x (label name is dropped, body converted)
    let expr = Spanned::dummy(core_ast::Expr::Label(core_ast::ExprLabel {
        name: Spanned::dummy("lbl".to_string()),
        body: Box::new(ident("x")),
    }));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Var("x".to_string())
    );
}

#[test]
fn test_expr_from_tla_core_state_var() {
    // StateVar maps to Var by name (same as Ident).
    let expr = Spanned::dummy(core_ast::Expr::StateVar(
        "s".to_string(),
        0,
        tla_core::intern_name("s"),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).unwrap(),
        TlaExpr::Var("s".to_string())
    );
}

// ============================================================================
// Package B — error branches returning UnsupportedCoreAst (additive coverage)
// ============================================================================

/// Helper: a plain (non-parameterized, non-recursive) LET value definition
/// `name == <body>`.
fn let_def(name: &str, body: Spanned<core_ast::Expr>) -> core_ast::OperatorDef {
    core_ast::OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body,
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

#[test]
fn test_expr_from_tla_core_let_multi_def_no_forward_refs_left_nests() {
    // LET a == 1  b == 2 IN a + b
    //   -> Let(a, 1, Let(b, 2, a + b))   (left-nested; a is outermost so b can
    //      see it, matching TLA+ simultaneous scoping for the no-forward subset)
    let plus = Spanned::dummy(core_ast::Expr::Add(
        Box::new(ident("a")),
        Box::new(ident("b")),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Let(
        vec![
            let_def("a", Spanned::dummy(core_ast::Expr::Int(1.into()))),
            let_def("b", Spanned::dummy(core_ast::Expr::Int(2.into()))),
        ],
        Box::new(plus),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("no-forward multi-def LET should lower"),
        TlaExpr::Let(
            "a".to_string(),
            Box::new(TlaExpr::Int(1)),
            Box::new(TlaExpr::Let(
                "b".to_string(),
                Box::new(TlaExpr::Int(2)),
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Add,
                    Box::new(TlaExpr::Var("a".to_string())),
                    Box::new(TlaExpr::Var("b".to_string())),
                )),
            )),
        )
    );
}

#[test]
fn test_expr_from_tla_core_let_multi_def_backward_ref_lowers() {
    // LET a == 1  b == a + 1 IN b
    //   b references the *earlier* sibling a, which is in scope under the
    //   left-nested lowering, so this is faithful and accepted.
    let b_body = Spanned::dummy(core_ast::Expr::Add(
        Box::new(ident("a")),
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Let(
        vec![
            let_def("a", Spanned::dummy(core_ast::Expr::Int(1.into()))),
            let_def("b", b_body),
        ],
        Box::new(ident("b")),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("backward-ref multi-def LET should lower"),
        TlaExpr::Let(
            "a".to_string(),
            Box::new(TlaExpr::Int(1)),
            Box::new(TlaExpr::Let(
                "b".to_string(),
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Add,
                    Box::new(TlaExpr::Var("a".to_string())),
                    Box::new(TlaExpr::Int(1)),
                )),
                Box::new(TlaExpr::Var("b".to_string())),
            )),
        )
    );
}

#[test]
fn test_expr_from_tla_core_let_multi_def_forward_ref_errors() {
    // LET a == b + 1  b == 2 IN a
    //   a references the *later* sibling b: left-nesting would not see b, and
    //   TLA+ scopes both simultaneously, so this must be rejected rather than
    //   silently mis-scoped.
    let a_body = Spanned::dummy(core_ast::Expr::Add(
        Box::new(ident("b")),
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Let(
        vec![
            let_def("a", a_body),
            let_def("b", Spanned::dummy(core_ast::Expr::Int(2.into()))),
        ],
        Box::new(ident("a")),
    ));
    let err =
        TlaExpr::from_tla_core(&expr).expect_err("forward-ref multi-def LET must be rejected");
    match err {
        TlaError::UnsupportedCoreAst(msg) => {
            assert!(
                msg.contains("references `b`") && msg.contains("bound at or after it"),
                "unexpected message: {msg}"
            );
        }
        other => panic!("expected UnsupportedCoreAst, got {other:?}"),
    }
}

#[test]
fn test_expr_from_tla_core_let_multi_def_self_ref_errors() {
    // LET a == a + 1  b == 2 IN b
    //   a references itself (a non-RECURSIVE self reference): the single-binding
    //   node evaluates the value in the enclosing scope, so this is rejected.
    let a_body = Spanned::dummy(core_ast::Expr::Add(
        Box::new(ident("a")),
        Box::new(Spanned::dummy(core_ast::Expr::Int(1.into()))),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Let(
        vec![
            let_def("a", a_body),
            let_def("b", Spanned::dummy(core_ast::Expr::Int(2.into()))),
        ],
        Box::new(ident("b")),
    ));
    let err = TlaExpr::from_tla_core(&expr).expect_err("self-ref multi-def LET must be rejected");
    match err {
        TlaError::UnsupportedCoreAst(msg) => {
            assert!(
                msg.contains("references `a`") && msg.contains("bound at or after it"),
                "unexpected message: {msg}"
            );
        }
        other => panic!("expected UnsupportedCoreAst, got {other:?}"),
    }
}

#[test]
fn test_expr_from_tla_core_let_recursive_def_errors() {
    // A RECURSIVE multi-def LET cannot be represented by the single-binding node.
    let mut rec = let_def("a", Spanned::dummy(core_ast::Expr::Int(1.into())));
    rec.is_recursive = true;
    let expr = Spanned::dummy(core_ast::Expr::Let(
        vec![
            rec,
            let_def("b", Spanned::dummy(core_ast::Expr::Int(2.into()))),
        ],
        Box::new(ident("b")),
    ));
    let err = TlaExpr::from_tla_core(&expr).expect_err("recursive LET must be rejected");
    match err {
        TlaError::UnsupportedCoreAst(msg) => {
            assert!(msg.contains("recursive"), "unexpected message: {msg}");
        }
        other => panic!("expected UnsupportedCoreAst, got {other:?}"),
    }
}

#[test]
fn test_expr_from_tla_core_let_parameterized_def_errors() {
    let def = core_ast::OperatorDef {
        name: Spanned::dummy("f".to_string()),
        params: vec![core_ast::OpParam {
            name: Spanned::dummy("x".to_string()),
            arity: 0,
        }],
        body: Spanned::dummy(core_ast::Expr::Int(1.into())),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    let expr = Spanned::dummy(core_ast::Expr::Let(vec![def], Box::new(ident("f"))));
    assert!(TlaExpr::from_tla_core(&expr).is_err());
}

#[test]
fn test_expr_from_tla_core_set_builder_multi_binder_errors() {
    // {x + y : x \in S, y \in T} -> single_named_domain rejects 2 binders.
    let expr = Spanned::dummy(core_ast::Expr::SetBuilder(
        Box::new(ident("x")),
        vec![bound_in("x", "S"), bound_in("y", "T")],
    ));
    assert!(TlaExpr::from_tla_core(&expr).is_err());
}

#[test]
fn test_expr_from_tla_core_func_def_missing_domain_errors() {
    // [x |-> x] with no domain -> single_named_domain rejects missing domain.
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("x".to_string()),
        domain: None,
        pattern: None,
    };
    let expr = Spanned::dummy(core_ast::Expr::FuncDef(vec![bound], Box::new(ident("x"))));
    assert!(TlaExpr::from_tla_core(&expr).is_err());
}

#[test]
fn test_expr_from_tla_core_set_filter_tuple_pattern_errors() {
    // {<<a, b>> \in S : TRUE} -> bound_name rejects tuple patterns.
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("p".to_string()),
        domain: Some(Box::new(ident("S"))),
        pattern: Some(core_ast::BoundPattern::Tuple(vec![
            Spanned::dummy("a".to_string()),
            Spanned::dummy("b".to_string()),
        ])),
    };
    let expr = Spanned::dummy(core_ast::Expr::SetFilter(
        bound,
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    assert!(TlaExpr::from_tla_core(&expr).is_err());
}

#[test]
fn test_expr_from_tla_core_set_filter_missing_domain_errors() {
    // SetFilter bound without a domain -> rejected.
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("x".to_string()),
        domain: None,
        pattern: None,
    };
    let expr = Spanned::dummy(core_ast::Expr::SetFilter(
        bound,
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    assert!(TlaExpr::from_tla_core(&expr).is_err());
}

// ============================================================================
// Package C — Formula conversions (additive coverage)
// ============================================================================

#[test]
fn test_formula_from_tla_core_subseteq_to_subset() {
    let expr = Spanned::dummy(core_ast::Expr::Subseteq(
        Box::new(ident("A")),
        Box::new(ident("B")),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::Subset(
            Box::new(TlaExpr::Var("A".to_string())),
            Box::new(TlaExpr::Var("B".to_string())),
        )
    );
}

#[test]
fn test_formula_from_tla_core_weak_fair_to_weak_fairness() {
    // WF_vars(Action) -> WeakFairness(Var vars, action-formula)
    let expr = Spanned::dummy(core_ast::Expr::WeakFair(
        Box::new(ident("vars")),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::WeakFairness(
            Box::new(TlaExpr::Var("vars".to_string())),
            Box::new(TlaFormula::True),
        )
    );
}

#[test]
fn test_formula_from_tla_core_strong_fair_to_strong_fairness() {
    // SF_vars(Action) -> StrongFairness(Var vars, action-formula)
    let expr = Spanned::dummy(core_ast::Expr::StrongFair(
        Box::new(ident("vars")),
        Box::new(Spanned::dummy(core_ast::Expr::Bool(false))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::StrongFairness(
            Box::new(TlaExpr::Var("vars".to_string())),
            Box::new(TlaFormula::False),
        )
    );
}

#[test]
fn test_formula_from_tla_core_multi_binder_forall_nesting_order() {
    // \A x \in S, y \in T : TRUE
    // fold_quantifiers folds right-to-left, so the first binder (x) is the
    // OUTERMOST ForallIn and the second binder (y) is nested inside.
    let expr = Spanned::dummy(core_ast::Expr::Forall(
        vec![bound_in("x", "S"), bound_in("y", "T")],
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    assert_eq!(
        TlaFormula::from_tla_core(&expr).unwrap(),
        TlaFormula::ForallIn(
            "x".to_string(),
            Box::new(TlaExpr::Var("S".to_string())),
            Box::new(TlaFormula::ForallIn(
                "y".to_string(),
                Box::new(TlaExpr::Var("T".to_string())),
                Box::new(TlaFormula::True),
            )),
        )
    );
}

// ============================================================================
// Package D — FuncSet / Times / Except conversions (B57)
// ============================================================================

use crate::encoding::{TlaContext, TlaExceptPath, TlaExceptSpec};
use clean_kernel::expr::ExprKind;

/// The leftmost constant name reached by peeling off applications, e.g. the
/// `head` of `((f a) b)`.
fn head_const(expr: &clean_kernel::expr::Expr) -> Option<String> {
    match expr.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        ExprKind::App(f, _) => head_const(f),
        _ => None,
    }
}

#[test]
fn test_expr_from_tla_core_func_set_maps_to_func_set() {
    // [S -> T] -> FuncSet(Var S, Var T)
    let expr = Spanned::dummy(core_ast::Expr::FuncSet(
        Box::new(ident("S")),
        Box::new(ident("T")),
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("function set should convert"),
        TlaExpr::FuncSet(
            Box::new(TlaExpr::Var("S".to_string())),
            Box::new(TlaExpr::Var("T".to_string())),
        )
    );
}

#[test]
fn test_func_set_translates_to_tla_func_set() {
    // End-to-end: [S -> T] encodes to `TLA.funcSet S T`.
    let expr = Spanned::dummy(core_ast::Expr::FuncSet(
        Box::new(ident("S")),
        Box::new(ident("T")),
    ));
    let mut ctx = TlaContext::new();
    let lean = ctx
        .translate_tla_core_expr(&expr)
        .expect("function set should translate end-to-end");
    assert_eq!(head_const(&lean).as_deref(), Some("TLA.funcSet"));
}

#[test]
fn test_expr_from_tla_core_times_maps_to_times() {
    // A \X B \X C -> Times([Var A, Var B, Var C])
    let expr = Spanned::dummy(core_ast::Expr::Times(vec![
        ident("A"),
        ident("B"),
        ident("C"),
    ]));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("Cartesian product should convert"),
        TlaExpr::Times(vec![
            TlaExpr::Var("A".to_string()),
            TlaExpr::Var("B".to_string()),
            TlaExpr::Var("C".to_string()),
        ])
    );
}

#[test]
fn test_times_translates_to_left_folded_tla_times() {
    // A \X B \X C -> TLA.times (TLA.times A B) C : the outermost application is
    // `TLA.times` applied to (the product of A and B) and C.
    let expr = Spanned::dummy(core_ast::Expr::Times(vec![
        ident("A"),
        ident("B"),
        ident("C"),
    ]));
    let mut ctx = TlaContext::new();
    let lean = ctx
        .translate_tla_core_expr(&expr)
        .expect("Cartesian product should translate");
    // Whole expression is headed by TLA.times.
    assert_eq!(head_const(&lean).as_deref(), Some("TLA.times"));
    // The left argument of the outer TLA.times is itself a TLA.times (A \X B),
    // confirming left-associative folding.
    match lean.kind() {
        ExprKind::App(outer_fn, _c) => match outer_fn.kind() {
            ExprKind::App(times_const, inner) => {
                assert_eq!(head_const(times_const).as_deref(), Some("TLA.times"));
                assert_eq!(
                    head_const(inner).as_deref(),
                    Some("TLA.times"),
                    "left factor should be the nested product A \\X B"
                );
            }
            other => panic!("expected `TLA.times applied to product`, got {other:?}"),
        },
        other => panic!("expected applied TLA.times, got {other:?}"),
    }
}

#[test]
fn test_expr_from_tla_core_except_index_maps_to_except() {
    // [f EXCEPT ![k] = v] -> Except(Var f, [{ path: [Index(Var k)], value: Var v }])
    let expr = Spanned::dummy(core_ast::Expr::Except(
        Box::new(ident("f")),
        vec![core_ast::ExceptSpec {
            path: vec![core_ast::ExceptPathElement::Index(ident("k"))],
            value: ident("v"),
        }],
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("EXCEPT update should convert"),
        TlaExpr::Except(
            Box::new(TlaExpr::Var("f".to_string())),
            vec![TlaExceptSpec {
                path: vec![TlaExceptPath::Index(TlaExpr::Var("k".to_string()))],
                value: TlaExpr::Var("v".to_string()),
            }],
        )
    );
}

#[test]
fn test_expr_from_tla_core_except_field_maps_to_field_path() {
    // [r EXCEPT !.f = v] -> Except with a Field path element (field name kept).
    let expr = Spanned::dummy(core_ast::Expr::Except(
        Box::new(ident("r")),
        vec![core_ast::ExceptSpec {
            path: vec![core_ast::ExceptPathElement::Field(
                core_ast::RecordFieldName::new(Spanned::dummy("f".to_string())),
            )],
            value: ident("v"),
        }],
    ));
    assert_eq!(
        TlaExpr::from_tla_core(&expr).expect("field EXCEPT should convert"),
        TlaExpr::Except(
            Box::new(TlaExpr::Var("r".to_string())),
            vec![TlaExceptSpec {
                path: vec![TlaExceptPath::Field("f".to_string())],
                value: TlaExpr::Var("v".to_string()),
            }],
        )
    );
}

#[test]
fn test_except_translates_to_tla_except() {
    // End-to-end: [f EXCEPT ![k] = v] encodes to `TLA.except f <path> v`,
    // i.e. the whole term is headed by `TLA.except`.
    let expr = Spanned::dummy(core_ast::Expr::Except(
        Box::new(ident("f")),
        vec![core_ast::ExceptSpec {
            path: vec![core_ast::ExceptPathElement::Index(ident("k"))],
            value: ident("v"),
        }],
    ));
    let mut ctx = TlaContext::new();
    let lean = ctx
        .translate_tla_core_expr(&expr)
        .expect("EXCEPT should translate end-to-end");
    assert_eq!(head_const(&lean).as_deref(), Some("TLA.except"));
}

#[test]
fn test_except_multi_spec_folds_left() {
    // [f EXCEPT ![a] = 1, ![b] = 2] -> the outer TLA.except wraps the inner
    // one: TLA.except (TLA.except f <[a]> 1) <[b]> 2 (sequential semantics).
    let expr = Spanned::dummy(core_ast::Expr::Except(
        Box::new(ident("f")),
        vec![
            core_ast::ExceptSpec {
                path: vec![core_ast::ExceptPathElement::Index(ident("a"))],
                value: Spanned::dummy(core_ast::Expr::Int(1.into())),
            },
            core_ast::ExceptSpec {
                path: vec![core_ast::ExceptPathElement::Index(ident("b"))],
                value: Spanned::dummy(core_ast::Expr::Int(2.into())),
            },
        ],
    ));
    let mut ctx = TlaContext::new();
    let lean = ctx
        .translate_tla_core_expr(&expr)
        .expect("multi-spec EXCEPT should translate");
    assert_eq!(head_const(&lean).as_deref(), Some("TLA.except"));
    // Peel `TLA.except <base> <path> <value>`: the base of the outer update is
    // another `TLA.except` (the first spec), proving left-associative folding.
    match lean.kind() {
        // value
        ExprKind::App(applied_path, _value) => match applied_path.kind() {
            // path
            ExprKind::App(applied_base, _path) => match applied_base.kind() {
                // base
                ExprKind::App(except_const, base) => {
                    assert_eq!(head_const(except_const).as_deref(), Some("TLA.except"));
                    assert_eq!(
                        head_const(base).as_deref(),
                        Some("TLA.except"),
                        "base of outer EXCEPT should be the inner EXCEPT"
                    );
                }
                other => panic!("expected `TLA.except base`, got {other:?}"),
            },
            other => panic!("expected `(TLA.except base) path`, got {other:?}"),
        },
        other => panic!("expected applied TLA.except, got {other:?}"),
    }
}

#[test]
fn test_except_deep_path_builds_path_cons_list() {
    // [f EXCEPT ![a][b] = v] -> the path is a TLA.pathCons list (head selector
    // applied first). We assert the path argument is headed by TLA.pathCons.
    let expr = Spanned::dummy(core_ast::Expr::Except(
        Box::new(ident("f")),
        vec![core_ast::ExceptSpec {
            path: vec![
                core_ast::ExceptPathElement::Index(ident("a")),
                core_ast::ExceptPathElement::Index(ident("b")),
            ],
            value: ident("v"),
        }],
    ));
    let mut ctx = TlaContext::new();
    let lean = ctx
        .translate_tla_core_expr(&expr)
        .expect("deep EXCEPT should translate");
    // lean = ((TLA.except f) path) v ; extract `path`.
    match lean.kind() {
        ExprKind::App(applied_path, _value) => match applied_path.kind() {
            ExprKind::App(_applied_base, path) => {
                assert_eq!(
                    head_const(path).as_deref(),
                    Some("TLA.pathCons"),
                    "multi-step path should reify as a TLA.pathCons list"
                );
            }
            other => panic!("expected `(TLA.except base) path`, got {other:?}"),
        },
        other => panic!("expected applied TLA.except, got {other:?}"),
    }
}

// ============================================================================
// Package E — tuple-pattern quantifier binders (\E <<x, y>> \in S : P)
// ============================================================================

/// `<<a, b>>` tuple projection helper: `Ident(name)[index]`.
fn projection(name: &str, index: i64) -> TlaExpr {
    TlaExpr::Apply(
        Box::new(TlaExpr::Var(name.to_string())),
        Box::new(TlaExpr::Int(index)),
    )
}

/// A bounded tuple-pattern binder `<<a, b>> \in domain`.
fn tuple_bound(components: &[&str], domain: &str) -> core_ast::BoundVar {
    core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("_tuple".to_string()),
        domain: Some(Box::new(ident(domain))),
        pattern: Some(core_ast::BoundPattern::Tuple(
            components
                .iter()
                .map(|c| Spanned::dummy(c.to_string()))
                .collect(),
        )),
    }
}

#[test]
fn test_formula_tuple_pattern_exists_destructures_into_projections() {
    // \E <<x, y>> \in S : x = y
    //   == \E t \in S : t[1] = t[2]   (a fresh element variable `t`, with each
    //      component replaced by the corresponding 1-based projection).
    let body = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(ident("x")),
        Box::new(ident("y")),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![tuple_bound(&["x", "y"], "S")],
        Box::new(body),
    ));
    let result =
        TlaFormula::from_tla_core(&expr).expect("tuple-pattern \\E should convert faithfully");
    // Fresh name is deterministic: nothing in {S, x, y} collides with the
    // generated `__tla_tuple_0`.
    assert_eq!(
        result,
        TlaFormula::ExistsIn(
            "__tla_tuple_0".to_string(),
            Box::new(TlaExpr::Var("S".to_string())),
            Box::new(TlaFormula::Eq(
                Box::new(projection("__tla_tuple_0", 1)),
                Box::new(projection("__tla_tuple_0", 2)),
            )),
        )
    );
}

#[test]
fn test_formula_tuple_pattern_forall_destructures_into_projections() {
    // \A <<a, b, c>> \in T : a = c  -- three components, 1-based projections.
    let body = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(ident("a")),
        Box::new(ident("c")),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Forall(
        vec![tuple_bound(&["a", "b", "c"], "T")],
        Box::new(body),
    ));
    let result =
        TlaFormula::from_tla_core(&expr).expect("tuple-pattern \\A should convert faithfully");
    assert_eq!(
        result,
        TlaFormula::ForallIn(
            "__tla_tuple_0".to_string(),
            Box::new(TlaExpr::Var("T".to_string())),
            Box::new(TlaFormula::Eq(
                Box::new(projection("__tla_tuple_0", 1)),
                Box::new(projection("__tla_tuple_0", 3)),
            )),
        )
    );
}

#[test]
fn test_formula_tuple_pattern_inner_shadow_is_not_substituted() {
    // \E <<x, y>> \in S : (x = y) /\ (\E x \in T : x = y)
    //   The inner `\E x \in T` re-binds `x`, so the inner occurrence of `x`
    //   must NOT be rewritten to t[1] (shadowing); only the outer `x` and both
    //   `y`s are projected.
    let inner = Spanned::dummy(core_ast::Expr::Exists(
        vec![bound_in("x", "T")],
        Box::new(Spanned::dummy(core_ast::Expr::Eq(
            Box::new(ident("x")),
            Box::new(ident("y")),
        ))),
    ));
    let outer_body = Spanned::dummy(core_ast::Expr::And(
        Box::new(Spanned::dummy(core_ast::Expr::Eq(
            Box::new(ident("x")),
            Box::new(ident("y")),
        ))),
        Box::new(inner),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![tuple_bound(&["x", "y"], "S")],
        Box::new(outer_body),
    ));
    let result =
        TlaFormula::from_tla_core(&expr).expect("shadowed tuple-pattern \\E should convert");
    // Expected: \E t \in S : (t[1] = t[2]) /\ (\E x \in T : x = t[2])
    //   - outer x -> t[1], both y -> t[2]
    //   - the inner, re-bound x stays `x` (its `y` is still the outer t[2]).
    let expected = TlaFormula::ExistsIn(
        "__tla_tuple_0".to_string(),
        Box::new(TlaExpr::Var("S".to_string())),
        Box::new(TlaFormula::And(
            Box::new(TlaFormula::Eq(
                Box::new(projection("__tla_tuple_0", 1)),
                Box::new(projection("__tla_tuple_0", 2)),
            )),
            Box::new(TlaFormula::ExistsIn(
                "x".to_string(),
                Box::new(TlaExpr::Var("T".to_string())),
                Box::new(TlaFormula::Eq(
                    Box::new(TlaExpr::Var("x".to_string())),
                    Box::new(projection("__tla_tuple_0", 2)),
                )),
            )),
        )),
    );
    assert_eq!(result, expected);
}

#[test]
fn test_formula_tuple_pattern_fresh_name_avoids_body_collision() {
    // \E <<x, y>> \in S : x = __tla_tuple_0   -- the body already mentions the
    // default fresh name, so the generator must skip to `__tla_tuple_1`.
    let body = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(ident("x")),
        Box::new(ident("__tla_tuple_0")),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![tuple_bound(&["x", "y"], "S")],
        Box::new(body),
    ));
    let result = TlaFormula::from_tla_core(&expr)
        .expect("tuple-pattern \\E with name collision should convert");
    assert_eq!(
        result,
        TlaFormula::ExistsIn(
            "__tla_tuple_1".to_string(),
            Box::new(TlaExpr::Var("S".to_string())),
            Box::new(TlaFormula::Eq(
                // x -> the *new* fresh name's projection ...
                Box::new(projection("__tla_tuple_1", 1)),
                // ... and the pre-existing `__tla_tuple_0` is left untouched.
                Box::new(TlaExpr::Var("__tla_tuple_0".to_string())),
            )),
        )
    );
}

#[test]
fn test_formula_tuple_pattern_mixed_with_plain_binder() {
    // \E <<x, y>> \in S, z \in T : x = z
    //   The plain binder `z` is preserved; only the tuple binder is desugared.
    let body = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(ident("x")),
        Box::new(ident("z")),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![tuple_bound(&["x", "y"], "S"), bound_in("z", "T")],
        Box::new(body),
    ));
    let result = TlaFormula::from_tla_core(&expr).expect("mixed tuple/plain \\E should convert");
    // fold_quantifiers folds right-to-left: the first binder (the fresh tuple
    // var) is outermost, `z` is nested inside.
    assert_eq!(
        result,
        TlaFormula::ExistsIn(
            "__tla_tuple_0".to_string(),
            Box::new(TlaExpr::Var("S".to_string())),
            Box::new(TlaFormula::ExistsIn(
                "z".to_string(),
                Box::new(TlaExpr::Var("T".to_string())),
                Box::new(TlaFormula::Eq(
                    Box::new(projection("__tla_tuple_0", 1)),
                    Box::new(TlaExpr::Var("z".to_string())),
                )),
            )),
        )
    );
}

#[test]
fn test_formula_tuple_pattern_later_domain_sees_earlier_projection() {
    // \E <<x, y>> \in S, z \in {x} : z = y
    //   `z`'s domain `{x}` is evaluated in the scope of the tuple binder, so the
    //   `x` inside it must become the projection t[1] as well.
    let body = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(ident("z")),
        Box::new(ident("y")),
    ));
    let z_bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("z".to_string()),
        domain: Some(Box::new(Spanned::dummy(core_ast::Expr::SetEnum(vec![
            ident("x"),
        ])))),
        pattern: None,
    };
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![tuple_bound(&["x", "y"], "S"), z_bound],
        Box::new(body),
    ));
    let result = TlaFormula::from_tla_core(&expr)
        .expect("tuple-pattern \\E with dependent later domain should convert");
    assert_eq!(
        result,
        TlaFormula::ExistsIn(
            "__tla_tuple_0".to_string(),
            Box::new(TlaExpr::Var("S".to_string())),
            Box::new(TlaFormula::ExistsIn(
                "z".to_string(),
                // {x} became {t[1]} -- earlier projection threaded into the
                // later binder's domain.
                Box::new(TlaExpr::SetEnum(vec![projection("__tla_tuple_0", 1)])),
                Box::new(TlaFormula::Eq(
                    Box::new(TlaExpr::Var("z".to_string())),
                    Box::new(projection("__tla_tuple_0", 2)),
                )),
            )),
        )
    );
}

#[test]
fn test_formula_tuple_pattern_translates_end_to_end() {
    // End-to-end: \E <<x, y>> \in S : x = y must translate through to a Lean
    // term with no UnsupportedCoreAst, and the projections encode via TLA.apply.
    let body = Spanned::dummy(core_ast::Expr::Eq(
        Box::new(ident("x")),
        Box::new(ident("y")),
    ));
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![tuple_bound(&["x", "y"], "S")],
        Box::new(body),
    ));
    let mut ctx = TlaContext::new();
    let _lean = ctx
        .translate_tla_core_formula(&expr)
        .expect("tuple-pattern \\E should translate end-to-end");
}

#[test]
fn test_formula_tuple_pattern_unbounded_returns_error() {
    // \E <<x, y>> : P  (no domain) has no set to range over and no element to
    // project, so it must be rejected precisely, not given a fabricated domain.
    let bound = core_ast::BoundVar {
        domain_group: None,
        name: Spanned::dummy("_tuple".to_string()),
        domain: None,
        pattern: Some(core_ast::BoundPattern::Tuple(vec![
            Spanned::dummy("x".to_string()),
            Spanned::dummy("y".to_string()),
        ])),
    };
    let expr = Spanned::dummy(core_ast::Expr::Exists(
        vec![bound],
        Box::new(Spanned::dummy(core_ast::Expr::Bool(true))),
    ));
    let err =
        TlaFormula::from_tla_core(&expr).expect_err("unbounded tuple-pattern \\E must be rejected");
    match err {
        TlaError::UnsupportedCoreAst(msg) => {
            assert!(
                msg.contains("tuple pattern") && msg.contains("no set to range over"),
                "unexpected message: {msg}"
            );
        }
        other => panic!("expected UnsupportedCoreAst, got {other:?}"),
    }
}
