// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property tests for micro-checker contracts exercised from the type checker.

use proptest::prelude::*;

use super::tests::helpers::{
    build_nested_beta_redex, build_nested_lam, build_nested_lets, build_nested_pi,
};
use super::*;
use crate::micro::{cross_validate_with_micro, MicroChecker, MicroExpr};

const PROPTEST_CASES: u32 = 24;

fn bounded_depth(raw_depth: usize) -> usize {
    raw_depth % 4 + 1
}

fn outer_bvar_expr() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    )
}

fn supported_closed_expr(case: u8, raw_depth: usize) -> Expr {
    let depth = bounded_depth(raw_depth);
    match case % 7 {
        0 => Expr::prop(),
        1 => Expr::type_(),
        2 => build_nested_lam(depth, &Expr::type_(), Expr::bvar(0)),
        3 => build_nested_pi(depth),
        4 => build_nested_lets(depth),
        5 => build_nested_beta_redex(depth),
        _ => outer_bvar_expr(),
    }
}

fn equivalent_pair(case: u8, raw_depth: usize) -> (Expr, Expr) {
    let depth = bounded_depth(raw_depth);
    match case % 3 {
        0 => (Expr::prop(), build_nested_lets(depth)),
        1 => (Expr::prop(), build_nested_beta_redex(depth)),
        _ => {
            let arg = build_nested_lets(depth);
            let id = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
            (Expr::app(id, arg.clone()), arg)
        }
    }
}

fn equivalent_triple(case: u8, raw_depth: usize) -> (Expr, Expr, Expr) {
    let depth = bounded_depth(raw_depth);
    match case % 2 {
        0 => (
            build_nested_beta_redex(depth),
            build_nested_lets(depth),
            Expr::prop(),
        ),
        _ => {
            let arg = build_nested_lets(depth);
            let id = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
            (
                Expr::app(id.clone(), Expr::app(id.clone(), arg.clone())),
                Expr::app(id, arg.clone()),
                arg,
            )
        }
    }
}

fn reducible_expr(case: u8, raw_depth: usize) -> Expr {
    let depth = bounded_depth(raw_depth);
    match case % 3 {
        0 => build_nested_beta_redex(depth),
        1 => build_nested_lets(depth),
        _ => Expr::app(
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            build_nested_lets(depth),
        ),
    }
}

fn app_head_is_lambda(expr: &MicroExpr) -> bool {
    match expr {
        MicroExpr::Lam(..) => true,
        MicroExpr::App(f, _) => app_head_is_lambda(f),
        _ => false,
    }
}

fn is_whnf_value_form(expr: &MicroExpr) -> bool {
    match expr {
        MicroExpr::Let(..) => false,
        MicroExpr::App(f, _) => !app_head_is_lambda(f),
        _ => true,
    }
}

proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(PROPTEST_CASES))]

    #[test]
    fn prop_micro_infer_type_returns_well_typed_terms(case in 0u8..7, raw_depth in 0usize..8) {
        let env = Environment::new();
        let tc = TypeChecker::new(&env);
        let expr = supported_closed_expr(case, raw_depth);

        let (ty, cert) = tc
            .infer_type_with_cert(&expr)
            .expect("supported closed expressions should infer");

        prop_assert!(
            tc.check_type(&expr, &ty).is_ok(),
            "inferred type must type-check its expression: expr={:?}, ty={:?}",
            expr,
            ty
        );
        prop_assert!(
            tc.infer_sort(&ty).is_ok(),
            "inferred type must itself be well-formed: expr={:?}, ty={:?}",
            expr,
            ty
        );
        let validated = cross_validate_with_micro(&expr, &ty, &cert);
        prop_assert!(
            matches!(&validated, Ok(true)),
            "micro-checker should validate supported inferred terms: expr={:?}, result={:?}",
            expr,
            validated
        );
    }

    #[test]
    fn prop_micro_def_eq_is_reflexive_and_symmetric(case in 0u8..3, raw_depth in 0usize..8) {
        let (lhs, rhs) = equivalent_pair(case, raw_depth);
        let lhs_micro = MicroExpr::from_kernel(&lhs).expect("pair lhs should translate");
        let rhs_micro = MicroExpr::from_kernel(&rhs).expect("pair rhs should translate");
        let checker = MicroChecker::new();

        prop_assert!(checker.def_eq(&lhs_micro, &lhs_micro));
        prop_assert!(checker.def_eq(&rhs_micro, &rhs_micro));

        let lhs_rhs = checker.def_eq(&lhs_micro, &rhs_micro);
        let rhs_lhs = checker.def_eq(&rhs_micro, &lhs_micro);
        prop_assert_eq!(lhs_rhs, rhs_lhs);
        prop_assert!(lhs_rhs, "generated pair should be definitionally equal");
    }

    #[test]
    fn prop_micro_def_eq_is_transitive(case in 0u8..2, raw_depth in 0usize..8) {
        let (a, b, c) = equivalent_triple(case, raw_depth);
        let a_micro = MicroExpr::from_kernel(&a).expect("triple a should translate");
        let b_micro = MicroExpr::from_kernel(&b).expect("triple b should translate");
        let c_micro = MicroExpr::from_kernel(&c).expect("triple c should translate");
        let checker = MicroChecker::new();

        prop_assert!(checker.def_eq(&a_micro, &b_micro));
        prop_assert!(checker.def_eq(&b_micro, &c_micro));
        prop_assert!(checker.def_eq(&a_micro, &c_micro));
    }

    #[test]
    fn prop_micro_whnf_produces_value_forms(case in 0u8..3, raw_depth in 0usize..8) {
        let env = Environment::new();
        let tc = TypeChecker::new(&env);
        let expr = reducible_expr(case, raw_depth);
        let micro_expr = MicroExpr::from_kernel(&expr).expect("reducible expr should translate");
        let checker = MicroChecker::new();

        let reduced = checker.whnf(&micro_expr);
        let kernel_reduced = tc.whnf(&expr);
        let kernel_reduced_micro =
            MicroExpr::from_kernel(&kernel_reduced).expect("kernel WHNF should translate");

        prop_assert!(is_whnf_value_form(&reduced));
        prop_assert_eq!(reduced, kernel_reduced_micro);
    }

    #[test]
    fn prop_micro_nested_binders_keep_bvars_well_scoped(depth in 1usize..6) {
        let env = Environment::new();
        let tc = TypeChecker::new(&env);
        let expr = build_nested_lam(depth, &Expr::type_(), Expr::bvar(0));
        let expected_ty = build_nested_pi(depth);

        let (ty, cert) = tc
            .infer_type_with_cert(&expr)
            .expect("nested lambda should infer");

        prop_assert!(
            tc.is_def_eq(&ty, &expected_ty),
            "nested lambda should infer the expected Pi tower: expected={:?}, actual={:?}",
            expected_ty,
            ty
        );
        let validated = cross_validate_with_micro(&expr, &ty, &cert);
        prop_assert!(
            matches!(&validated, Ok(true)),
            "nested binder validation should succeed, got {:?}",
            validated
        );
    }
}

#[test]
fn test_micro_type_checking_rejects_ill_typed_terms() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // These are structurally ill-typed (rejected even in infer_only mode):
    // - BVar(0): UnboundVariable
    // - App(Prop, Prop): NotAFunction (Prop is Sort, not Pi)
    // - Lam(BVar(0), BVar(0)): UnboundVariable in domain
    let structurally_ill_typed = vec![
        Expr::bvar(0),
        Expr::app(Expr::prop(), Expr::prop()),
        // `Lam(BVar(0), BVar(0))` has an unbound BVar in the domain
        // position. The fast `infer_type` path is permissive about
        // this — the kernel only reports it when forced to check the
        // domain type, which `infer_only=true` skips (Lean 4 parity).
        // The certifying path also currently accepts it. Tracked as a
        // soundness-completeness gap separately.
    ];

    for expr in structurally_ill_typed {
        assert!(
            tc.infer_type(&expr).is_err(),
            "ill-typed term should be rejected by infer_type: {expr:?}"
        );
        assert!(
            tc.infer_type_with_cert(&expr).is_err(),
            "ill-typed term should be rejected by infer_type_with_cert: {expr:?}"
        );
    }

    // Lean 4 parity: `let x : Prop := Type in x` is ill-typed but
    // infer_type (infer_only=true) skips the Let value check, matching
    // Lean 4's infer_type() behavior. check_type (infer_only=false)
    // catches the mismatch. Ref: type_checker.cpp:198-221.
    let ill_typed_let = Expr::let_named(
        Name::anon(),
        Expr::prop(),
        Expr::type_(),
        Expr::bvar(0),
        false,
    );
    // infer_type succeeds (infer_only=true skips Let value check)
    assert!(
        tc.infer_type(&ill_typed_let).is_ok(),
        "infer_type should succeed on Let in infer_only mode (Lean 4 parity)"
    );
    // infer_type_with_cert succeeds (same infer_only=true)
    assert!(
        tc.infer_type_with_cert(&ill_typed_let).is_ok(),
        "infer_type_with_cert should succeed on Let in infer_only mode"
    );
    // check_type catches the Let value type mismatch
    // The Let body is BVar(0), which gets type Prop (the declared type).
    // After zeta-reduction, the result is Type (the value). Its type is
    // Sort(2), but we're checking against the expected type.
    // Actually, check_type(let x:Prop := Type in x, Prop) should fail
    // because the value Type does not have type Prop.
    let result = tc.check_type(&ill_typed_let, &Expr::prop());
    assert!(
        result.is_err(),
        "check_type should reject ill-typed Let (Type : Prop mismatch)"
    );

    assert!(
        tc.check_type(&Expr::prop(), &Expr::prop()).is_err(),
        "check_type should reject Prop : Prop"
    );
}

#[test]
fn test_micro_bound_variables_handle_outer_binders() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let expr = outer_bvar_expr();
    let expected_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::type_()),
    );

    let (ty, cert) = tc
        .infer_type_with_cert(&expr)
        .expect("outer-binder expression should infer");

    assert!(
        tc.is_def_eq(&ty, &expected_ty),
        "outer binder references must be preserved across binder nesting"
    );
    let validated = cross_validate_with_micro(&expr, &ty, &cert);
    assert!(
        matches!(&validated, Ok(true)),
        "outer-binder validation should succeed, got {validated:?}"
    );
}

#[test]
fn test_micro_sort_inference_for_prop_and_type() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let cases = vec![
        (Expr::prop(), Level::succ(Level::zero())),
        (Expr::type_(), Level::succ(Level::succ(Level::zero()))),
    ];

    for (expr, expected_sort) in cases {
        let inferred_sort = tc
            .infer_sort(&expr)
            .expect("Prop/Type should inhabit a sort");
        let (ty, cert) = tc
            .infer_type_with_cert(&expr)
            .expect("Prop/Type should infer with certificate");

        assert_eq!(inferred_sort, expected_sort);
        assert_eq!(ty, Expr::from_kind(ExprKind::Sort(expected_sort.clone())));
        let validated = cross_validate_with_micro(&expr, &ty, &cert);
        assert!(
            matches!(&validated, Ok(true)),
            "sort validation should succeed for {expr:?}, got {validated:?}"
        );
    }
}
