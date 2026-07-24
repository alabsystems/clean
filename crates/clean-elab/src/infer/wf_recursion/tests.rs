// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for well-founded recursion elaboration.

use super::decreasing::{build_nat_decreasing_goal, DecreasingObligation, DecreasingStrategy};
use super::encoding::replace_rec_calls;
use super::equation_lemmas::{extract_equation_cases, EquationCase};
use super::mutual::{build_psum_injection, build_psum_type, MutualPackInfo};
use super::pre_definition::{PreDefinition, TerminationMeasure};
use clean_kernel::name::Name;
use clean_kernel::sorry::create_sorry_term;
use clean_kernel::{Environment, Expr, FVarId, Level};
use clean_parser::{Span, SurfaceExpr};

#[test]
fn test_pre_definition_creation() {
    let env = Environment::with_prelude();
    let ty = Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat"));
    let pre_def = PreDefinition {
        name: Name::from_string("myFunc"),
        universe_params: vec![Name::from_string("u")],
        ty: ty.clone(),
        val: create_sorry_term(&env, &ty),
    };
    assert_eq!(pre_def.name, Name::from_string("myFunc"));
    assert_eq!(pre_def.universe_params.len(), 1);
}

#[test]
fn test_termination_measure_creation() {
    let measure = TerminationMeasure {
        params: vec!["n".to_string()],
        measure_expr: Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        decreasing_by: None,
    };
    assert_eq!(measure.params, vec!["n".to_string()]);
}

#[test]
fn test_termination_measure_with_decreasing_by() {
    let measure = TerminationMeasure {
        params: vec!["n".to_string()],
        measure_expr: Box::new(SurfaceExpr::Ident(Span::dummy(), "n".to_string())),
        decreasing_by: Some(Box::new(SurfaceExpr::Ident(
            Span::dummy(),
            "simp_arith".to_string(),
        ))),
    };
    assert!(measure.decreasing_by.is_some());
}

#[test]
fn test_replace_rec_calls_identity_for_non_recursive() {
    let func_fvar = FVarId::new(100);
    let rec_fvar = FVarId::new(200);
    let x_fvar = FVarId::new(300);

    // A non-recursive body: just `x`
    let body = Expr::fvar(x_fvar);
    let result = replace_rec_calls(&body, func_fvar, rec_fvar);

    // Should be unchanged
    assert_eq!(format!("{result:?}"), format!("{:?}", Expr::fvar(x_fvar)));
}

#[test]
fn test_replace_rec_calls_replaces_function_reference() {
    let func_fvar = FVarId::new(100);
    let rec_fvar = FVarId::new(200);
    let n_fvar = FVarId::new(300);

    // f(n-1) represented as App(FVar(func), App(sub, FVar(n)))
    let sub_expr = Expr::app(Expr::const_str("Nat.sub"), Expr::fvar(n_fvar));
    let body = Expr::app(Expr::fvar(func_fvar), sub_expr.clone());

    let result = replace_rec_calls(&body, func_fvar, rec_fvar);

    // Should be: rec(n-1)
    let expected = Expr::app(Expr::fvar(rec_fvar), sub_expr);
    assert_eq!(format!("{result:?}"), format!("{expected:?}"));
}

#[test]
fn test_replace_rec_calls_nested() {
    let func_fvar = FVarId::new(100);
    let rec_fvar = FVarId::new(200);

    // f (f x) => rec (rec x)
    let x = Expr::const_str("x");
    let inner_call = Expr::app(Expr::fvar(func_fvar), x.clone());
    let body = Expr::app(Expr::fvar(func_fvar), inner_call);

    let result = replace_rec_calls(&body, func_fvar, rec_fvar);

    let inner_expected = Expr::app(Expr::fvar(rec_fvar), x);
    let expected = Expr::app(Expr::fvar(rec_fvar), inner_expected);
    assert_eq!(format!("{result:?}"), format!("{expected:?}"));
}

#[test]
fn test_replace_rec_calls_in_lambda() {
    let func_fvar = FVarId::new(100);
    let rec_fvar = FVarId::new(200);

    // fun x => f x => fun x => rec x
    let body_inner = Expr::app(Expr::fvar(func_fvar), Expr::fvar(FVarId::new(300)));
    let body = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::const_str("Nat"),
        body_inner,
    );

    let result = replace_rec_calls(&body, func_fvar, rec_fvar);

    let expected_inner = Expr::app(Expr::fvar(rec_fvar), Expr::fvar(FVarId::new(300)));
    let expected = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::const_str("Nat"),
        expected_inner,
    );
    assert_eq!(format!("{result:?}"), format!("{expected:?}"));
}

// =====================================================================
// Mutual WF recursion tests (PackMutual encoding)
// =====================================================================

#[test]
fn test_mutual_psum_type_two_functions() {
    let nat = Expr::const_str("Nat");
    let bool_ty = Expr::const_str("Bool");
    let result = build_psum_type(&[nat.clone(), bool_ty.clone()], &Level::zero()).unwrap();

    // Should be: PSum Nat Bool
    let psum = Expr::const_(
        Name::from_string("PSum"),
        vec![Level::zero(), Level::zero()],
    );
    let expected = Expr::app(Expr::app(psum, nat), bool_ty);
    assert_eq!(format!("{result:?}"), format!("{expected:?}"));
}

#[test]
fn test_mutual_psum_type_three_functions() {
    let a = Expr::const_str("A");
    let b = Expr::const_str("B");
    let c = Expr::const_str("C");
    let result = build_psum_type(&[a.clone(), b.clone(), c.clone()], &Level::zero()).unwrap();

    // Should be: PSum A (PSum B C)
    let psum = Expr::const_(
        Name::from_string("PSum"),
        vec![Level::zero(), Level::zero()],
    );
    let inner = Expr::app(Expr::app(psum.clone(), b), c);
    let expected = Expr::app(Expr::app(psum, a), inner);
    assert_eq!(format!("{result:?}"), format!("{expected:?}"));
}

#[test]
fn test_mutual_psum_type_single_passthrough() {
    let nat = Expr::const_str("Nat");
    let result = build_psum_type(std::slice::from_ref(&nat), &Level::zero()).unwrap();
    assert_eq!(format!("{result:?}"), format!("{nat:?}"));
}

#[test]
fn test_mutual_psum_type_empty_errors() {
    let result = build_psum_type(&[], &Level::zero());
    assert!(result.is_err());
}

#[test]
fn test_mutual_psum_injection_single_identity() {
    let nat = Expr::const_str("Nat");
    let inj = build_psum_injection(std::slice::from_ref(&nat), 0, &Level::zero()).unwrap();
    // Should be a lambda: fun (x : Nat) => x
    match inj.kind() {
        clean_kernel::ExprKind::Lam(_, _, _) => {} // expected
        other => panic!(
            "Expected lambda for single-function injection, got {:?}",
            other
        ),
    }
}

#[test]
fn test_mutual_psum_injection_out_of_bounds() {
    let nat = Expr::const_str("Nat");
    let result = build_psum_injection(&[nat], 1, &Level::zero());
    assert!(result.is_err());
}

#[test]
fn test_mutual_pack_info_creation() {
    let info = MutualPackInfo {
        func_names: vec!["f".to_string(), "g".to_string()],
        func_types: vec![
            Expr::arrow(Expr::const_str("Nat"), Expr::const_str("A")),
            Expr::arrow(Expr::const_str("Nat"), Expr::const_str("B")),
        ],
        func_bodies: vec![Expr::const_str("body_f"), Expr::const_str("body_g")],
        func_fvars: vec![FVarId::new(100), FVarId::new(200)],
        binder_fvars: vec![
            vec![(FVarId::new(10), Expr::const_str("Nat"))],
            vec![(FVarId::new(20), Expr::const_str("Nat"))],
        ],
    };
    assert_eq!(info.func_names.len(), 2);
    assert_eq!(info.func_fvars.len(), 2);
}

// =====================================================================
// Decreasing proof tests
// =====================================================================

#[test]
fn test_decreasing_nat_goal_structure() {
    let measure = Expr::const_str("sizeOf");
    let rec_arg = Expr::const_str("smaller");
    let cur_arg = Expr::const_str("current");

    let goal = build_nat_decreasing_goal(&measure, &rec_arg, &cur_arg);

    // Should be: Nat.lt (sizeOf smaller) (sizeOf current)
    let lhs = Expr::app(Expr::const_str("sizeOf"), Expr::const_str("smaller"));
    let rhs = Expr::app(Expr::const_str("sizeOf"), Expr::const_str("current"));
    let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
    let expected = Expr::app(Expr::app(nat_lt, lhs), rhs);
    assert_eq!(format!("{goal:?}"), format!("{expected:?}"));
}

#[test]
fn test_decreasing_obligation_construction() {
    let goal = Expr::const_str("goal");
    let rec = Expr::const_str("n_minus_1");
    let cur = Expr::const_str("n");
    let ob = DecreasingObligation::new(goal.clone(), rec.clone(), cur.clone());
    assert_eq!(format!("{:?}", ob.goal_type), format!("{goal:?}"));
}

#[test]
fn test_decreasing_strategy_equality() {
    assert_eq!(DecreasingStrategy::Sorry, DecreasingStrategy::Sorry);
    assert_ne!(DecreasingStrategy::UserTactic, DecreasingStrategy::Sorry);
    assert_ne!(DecreasingStrategy::SimpArith, DecreasingStrategy::Mathverse);
}

// =====================================================================
// Equation lemma tests
// =====================================================================

#[test]
fn test_equation_case_extraction_empty() {
    // For now, extract_equation_cases returns empty for all inputs
    let body = Expr::const_str("some_body");
    let cases = extract_equation_cases(&body);
    assert!(cases.is_empty());
}

#[test]
fn test_equation_case_construction() {
    let case = EquationCase {
        params: vec![("n".to_string(), Expr::const_str("Nat"))],
        lhs_arg: Expr::app(Expr::const_str("Nat.succ"), Expr::const_str("n")),
        rhs: Expr::const_str("result"),
    };
    assert_eq!(case.params.len(), 1);
    assert_eq!(case.params[0].0, "n");
}
