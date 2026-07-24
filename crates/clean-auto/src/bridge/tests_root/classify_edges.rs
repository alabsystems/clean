// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::Declaration;

fn setup_dependent_exists_prop_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");
    env.init_exists().expect("init_exists should succeed");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Vec"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), Expr::type_()),
    })
    .expect("Vec should be declared");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Pred"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::pi(
                BinderInfo::Default,
                Expr::app(
                    Expr::const_(Name::from_string("Vec"), vec![]),
                    Expr::bvar(0),
                ),
                Expr::prop(),
            ),
        ),
    })
    .expect("Pred should be declared");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("Q should be declared");

    env
}

/// type_universe_level returns InferSortFailed when sort is not Succ(_).
///
/// When a type lives in Prop (Sort 0) instead of Type u (Sort (u + 1)),
/// the comparison operator reconstruction cannot extract the universe parameter.
#[test]
fn test_type_universe_level_non_succ_returns_error() {
    use clean_kernel::Level;

    let result = SmtBridge::type_universe_level(Ok(Level::zero()));
    assert!(
        result.is_err(),
        "type_universe_level(Sort 0) should fail - Prop has no Type universe"
    );
    let err = result.expect_err("Prop sorts should fail type universe extraction");
    assert!(
        matches!(err, BridgeError::InferSortFailed { .. }),
        "Expected InferSortFailed, got {err:?}"
    );
    if let BridgeError::InferSortFailed { context } = err {
        assert!(
            context.contains("expected Sort (succ u)"),
            "error should explain the sort level mismatch, got: {context}"
        );
    }
}

/// type_universe_level propagates upstream BridgeError.
#[test]
fn test_type_universe_level_propagates_upstream_error() {
    let upstream_err = Err(BridgeError::InferSortFailed {
        context: "upstream: unknown type Z".to_string(),
    });
    let result = SmtBridge::type_universe_level(upstream_err);
    assert!(
        result.is_err(),
        "type_universe_level should propagate upstream errors"
    );
    let err = result.expect_err("upstream sort failures should propagate");
    assert!(
        matches!(err, BridgeError::InferSortFailed { .. }),
        "Expected InferSortFailed, got {err:?}"
    );
    if let BridgeError::InferSortFailed { context } = err {
        assert!(
            context.contains("upstream"),
            "should preserve upstream error context, got: {context}"
        );
    }
}

/// type_universe_level correctly extracts inner level from Succ.
#[test]
fn test_type_universe_level_succ_extracts_inner() {
    use clean_kernel::Level;

    let result = SmtBridge::type_universe_level(Ok(Level::succ(Level::zero())));
    assert!(result.is_ok(), "Succ(zero) should succeed");
    let inner = result.expect("Succ(zero) should yield the inner universe level");
    assert_eq!(
        inner,
        Level::zero(),
        "Type 0 = Sort 1, universe param should be 0"
    );
}

/// mk_comparison_inst errors for non-resolvable non-Const types.
#[test]
fn test_mk_comparison_inst_non_const_type_returns_error() {
    let bvar_type = Expr::bvar(0);
    let err = SmtBridge::mk_comparison_inst("LT", &bvar_type)
        .expect_err("non-const types should fail closed");
    assert!(
        matches!(err, BridgeError::UnsupportedExpr { .. }),
        "expected UnsupportedExpr, got {err:?}"
    );
    if let BridgeError::UnsupportedExpr { context } = err {
        assert_eq!(
            context,
            format!("cannot resolve typeclass instance for type: {bvar_type:?}"),
            "non-resolvable types should fail closed with the original expr in context"
        );
    }
}

/// mk_comparison_inst produces correct instance names for known types.
#[test]
fn test_mk_comparison_inst_known_type_names() {
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let int_type = Expr::const_(Name::from_string("Int"), vec![]);

    let lt_nat = SmtBridge::mk_comparison_inst("LT", &nat_type)
        .expect("Nat should have an LT instance name");
    assert!(matches!(lt_nat.kind(), ExprKind::Const(n, _) if n.to_string() == "instLTNat"));

    let le_int = SmtBridge::mk_comparison_inst("LE", &int_type)
        .expect("Int should have an LE instance name");
    assert!(matches!(le_int.kind(), ExprKind::Const(n, _) if n.to_string() == "instLEInt"));

    let gt_nat = SmtBridge::mk_comparison_inst("GT", &nat_type)
        .expect("Nat should reuse the LT instance name for GT");
    assert!(matches!(gt_nat.kind(), ExprKind::Const(n, _) if n.to_string() == "instLTNat"));

    let ge_int = SmtBridge::mk_comparison_inst("GE", &int_type)
        .expect("Int should reuse the LE instance name for GE");
    assert!(matches!(ge_int.kind(), ExprKind::Const(n, _) if n.to_string() == "instLEInt"));
}

/// mk_comparison_inst unknown tc_name defaults to the "instLE" prefix.
#[test]
fn test_mk_comparison_inst_unknown_tc_defaults_to_le() {
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = SmtBridge::mk_comparison_inst("UNKNOWN_TC", &nat_type)
        .expect("unknown typeclass names should still synthesize an LE instance");
    assert!(
        matches!(inst.kind(), ExprKind::Const(n, _) if n.to_string() == "instLENat"),
        "Unknown tc_name should default to instLE prefix"
    );
}

/// mk_comparison_inst extracts the head const from applied types.
#[test]
fn test_mk_comparison_inst_app_type_extracts_head_const() {
    let fin_type = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        Expr::const_(Name::from_string("n"), vec![]),
    );

    let inst = SmtBridge::mk_comparison_inst("LT", &fin_type)
        .expect("applied types should resolve the application head");

    assert!(
        matches!(inst.kind(), ExprKind::Const(n, _) if n.to_string() == "instLTFin"),
        "applied types should use the application head const for instance naming"
    );
}

/// mk_comparison_inst ignores metadata around applied types and their heads.
#[test]
fn test_mk_comparison_inst_mdata_wrapped_app_type_extracts_head_const() {
    let fin_type = Expr::mdata(
        vec![],
        Expr::app(
            Expr::mdata(vec![], Expr::const_(Name::from_string("Fin"), vec![])),
            Expr::const_(Name::from_string("n"), vec![]),
        ),
    );

    let inst = SmtBridge::mk_comparison_inst("LT", &fin_type)
        .expect("metadata-wrapped applied types should resolve the application head");

    assert!(
        matches!(inst.kind(), ExprKind::Const(n, _) if n.to_string() == "instLTFin"),
        "metadata-wrapped applied types should still resolve the application head const"
    );
}

/// logicalform_to_expr for Lt with non-Succ sort level returns error.
#[test]
fn test_logicalform_to_expr_lt_with_prop_type_returns_error() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let form = LogicalForm::Lt {
        ty: Expr::const_(Name::from_string("Unknown"), vec![]),
        lhs: Expr::const_(Name::from_string("a"), vec![]),
        rhs: Expr::const_(Name::from_string("b"), vec![]),
    };
    let result = bridge.logicalform_to_expr(&form);
    assert!(
        result.is_err(),
        "Lt with unknown type should fail at sort level inference"
    );
}

/// classify_prop folds arithmetic forms to Atom.
#[test]
fn test_classify_prop_folds_arithmetic_to_atom() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let nat_add = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    );

    let result = bridge.classify_prop(&nat_add);
    assert!(
        matches!(result, LogicalForm::Atom(_)),
        "Nat.add should be folded to Atom in propositional context, got {:?}",
        result
    );
}

/// classify_prop decomposes Neq into Not(Eq) when sort inference succeeds.
#[test]
fn test_classify_prop_neq_becomes_not_eq() {
    use clean_kernel::Level;

    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ne_const = Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let ne_expr = Expr::app(
        Expr::app(Expr::app(ne_const, a_ty.clone()), a.clone()),
        b.clone(),
    );

    let result = bridge.classify_prop(&ne_expr);
    assert!(
        !matches!(result, LogicalForm::Neq { .. }),
        "classify_prop should fold Neq to Not(Eq), not pass through as Neq"
    );
}

#[test]
fn test_classify_prop_dependent_exists_arrow_under_outer_binder_is_implies() {
    let env = setup_dependent_exists_prop_env();
    let bridge = SmtBridge::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let vec_x = Expr::app(
        Expr::const_(Name::from_string("Vec"), vec![]),
        Expr::bvar(0),
    );
    let hyp_exists = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            vec_x.clone(),
        ),
        Expr::lam(
            BinderInfo::Default,
            vec_x.clone(),
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Pred"), vec![]),
                    Expr::bvar(1),
                ),
                Expr::bvar(0),
            ),
        ),
    );
    let goal_exists = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            vec_x.clone(),
        ),
        Expr::lam(
            BinderInfo::Default,
            vec_x,
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Pred"), vec![]),
                    Expr::bvar(1),
                ),
                Expr::bvar(0),
            ),
        ),
    );
    let goal = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::arrow(hyp_exists.clone(), goal_exists.clone()),
    );

    let outer_class = bridge.classify_prop(&goal);
    assert!(
        matches!(outer_class, LogicalForm::Forall { .. }),
        "outer dependent binder should classify as Forall, got {outer_class:?}"
    );

    let body = match outer_class {
        LogicalForm::Forall { body, .. } => body,
        _ => unreachable!(),
    };
    let inner_class = bridge.classify_prop(&body);
    assert!(
        matches!(inner_class, LogicalForm::Implies(_, _)),
        "dependent existential antecedent under an outer binder should classify as Implies, got {inner_class:?}"
    );

    if let LogicalForm::Implies(antecedent, consequent) = inner_class {
        assert_eq!(antecedent, hyp_exists);
        assert_eq!(consequent, goal_exists);
    }
}
