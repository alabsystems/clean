// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic front-end tactic tests: nlinarith, positivity, field_simp,
//! norm_cast, mathverse, ac_rfl, push_cast, simp_all.

use super::support::close_current_goal_checked;
use super::*;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

// =========================================================================
// nlinarith tests
// =========================================================================

#[test]
fn test_nlinarith_fallback() {
    // nlinarith on a non-arithmetic goal should fail with an error
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let result = nlinarith(&mut state);
    // A is not a linear constraint — nlinarith should report failure, not silently succeed
    assert!(
        result.is_err(),
        "nlinarith should fail on non-arithmetic goal A"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after nlinarith failure"
    );
}

#[test]
fn test_nlinarith_config_default() {
    // Test that NlinarithConfig has sensible defaults
    let config = NlinarithConfig::default();
    assert_eq!(config.max_products, 100);
    assert!(config.add_squares);
    assert_eq!(config.max_constraints, 500);
}

#[test]
fn test_nlinarith_with_config() {
    // nlinarith_with_config on a non-arithmetic goal should fail, regardless of config
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let config = NlinarithConfig {
        max_products: 10,
        add_squares: false,
        max_constraints: 50,
        use_groebner: false,
        groebner_config: Default::default(),
    };
    let result = nlinarith_with_config(&mut state, config);
    assert!(
        result.is_err(),
        "nlinarith_with_config should fail on non-arithmetic goal A"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after nlinarith_with_config failure"
    );
}

#[test]
fn test_try_compute_linear_product_constants() {
    // Test product of two constants
    let e1 = LinearExpr::constant(3);
    let e2 = LinearExpr::constant(4);
    let product = try_compute_linear_product(&e1, &e2);
    let product = product.expect("expected Some");
    assert_eq!(product.constant, 12);
}

#[test]
fn test_try_compute_linear_product_constant_and_var() {
    // Test product of constant and single-variable expression
    let e1 = LinearExpr::constant(5);
    let e2 = LinearExpr::var(0); // x0
    let product = try_compute_linear_product(&e1, &e2);
    let product = product.expect("expected Some");
    let p = product;
    assert_eq!(p.constant, 0);
    assert_eq!(p.get_coeff(0), 5);
}

#[test]
fn test_try_compute_linear_product_nonlinear() {
    // Test product of two multi-term expressions (should be None - nonlinear)
    let mut e1 = LinearExpr::var(0);
    e1.constant = 1; // x0 + 1
    let mut e2 = LinearExpr::var(1);
    e2.constant = 2; // x1 + 2

    let product = try_compute_linear_product(&e1, &e2);
    // Should be None because (x0 + 1)(x1 + 2) is nonlinear
    assert_eq!(product, None);
}

#[test]
fn test_is_zero_expr_literal() {
    // Test is_zero_expr with literal 0
    let zero = Expr::nat_lit(0);
    assert!(is_zero_expr(&zero));

    let one = Expr::nat_lit(1);
    assert!(!is_zero_expr(&one));
}

#[test]
fn test_is_zero_expr_const() {
    // Test is_zero_expr with Nat.zero constant
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(is_zero_expr(&nat_zero));

    let nat_one = Expr::const_(Name::from_string("Nat.one"), vec![]);
    assert!(!is_zero_expr(&nat_one));
}

#[test]
fn test_nlinarith_exprs_equal() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let a2 = Expr::const_(Name::from_string("a"), vec![]);

    assert!(nlinarith_exprs_equal(&a, &a2));
    assert!(!nlinarith_exprs_equal(&a, &b));
}

// =========================================================================
// positivity tests
// =========================================================================

#[test]
fn test_positivity_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now positivity should fail with NoGoals
    let result = positivity(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

// =========================================================================
// field_simp tests
// =========================================================================

#[test]
fn test_field_simp_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now field_simp should fail with NoGoals
    let result = field_simp(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_field_simp_non_equality() {
    let env = setup_env();
    // Goal: A (not an equality)
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let result = field_simp(&mut state);
    // Should fail since goal is not an equality
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_extract_denominators_simple() {
    // Test that extract_denominators finds denominators
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // a / b - create using app
    let div = Expr::const_(Name::from_string("Div.div"), vec![]);
    let div_expr = Expr::app(Expr::app(div, a.clone()), b.clone());

    let denoms = extract_denominators(&div_expr);
    assert_eq!(denoms.len(), 1);
    assert_eq!(denoms[0], b);
}

#[test]
fn test_get_app_fn() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // f a b
    let app = Expr::app(Expr::app(f.clone(), a), b);

    let head = get_app_fn(&app);
    assert!(matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == "f"));
}

// =========================================================================
// norm_cast tests
// =========================================================================

#[test]
fn test_norm_cast_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now norm_cast should fail with NoGoals
    let result = norm_cast(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_is_cast_function() {
    let coe = Expr::const_(Name::from_string("coe"), vec![]);
    let nat_cast = Expr::const_(Name::from_string("Nat.cast"), vec![]);
    let regular = Expr::const_(Name::from_string("foo"), vec![]);

    assert!(is_cast_function(&coe));
    assert!(is_cast_function(&nat_cast));
    assert!(!is_cast_function(&regular));
}

// =========================================================================
// mathverse tests
// =========================================================================

#[test]
fn test_mathverse_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now mathverse should fail with NoGoals
    let result = omega(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_expr_to_linear_constant() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let result = expr_to_linear(&zero, None);
    let result = result.expect("expected Some");
    let lin = result;
    assert_eq!(lin.constant, 0);
    assert!(lin.is_constant());
}

#[test]
fn test_expr_to_linear_fvar() {
    let fvar = Expr::fvar(FVarId::new(42));
    let result = expr_to_linear(&fvar, None);
    let result = result.expect("expected Some");
    let lin = result;
    assert!(!lin.is_constant());
    assert_eq!(lin.variables(), vec![42]);
}

// =========================================================================
// ac_rfl tests
// =========================================================================

#[test]
fn test_ac_rfl_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now ac_rfl should fail with NoGoals
    let result = ac_rfl(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_ac_rfl_non_equality() {
    let env = setup_env();
    // Goal: A (not an equality)
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let result = ac_rfl(&mut state);
    // Should fail since goal is not an equality
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_ac_normalize_bvar() {
    let bv = Expr::bvar(3);
    let norm = ac_normalize(&bv);
    assert!(matches!(norm, ACExpr::BVar(3)));
}

#[test]
fn test_ac_normalize_const() {
    let c = Expr::const_(Name::from_string("foo"), vec![]);
    let norm = ac_normalize(&c);
    assert!(matches!(norm, ACExpr::Atom(s) if s == "foo"));
}

#[test]
fn test_get_ac_op_name_add() {
    let add = Expr::const_(Name::from_string("HAdd.hAdd"), vec![]);
    let result = get_ac_op_name(&add);
    assert_eq!(result, Some("add".to_string()));
}

#[test]
fn test_get_ac_op_name_mul() {
    let mul = Expr::const_(Name::from_string("HMul.hMul"), vec![]);
    let result = get_ac_op_name(&mul);
    assert_eq!(result, Some("mul".to_string()));
}

#[test]
fn test_get_ac_op_name_non_ac() {
    let foo = Expr::const_(Name::from_string("foo"), vec![]);
    let result = get_ac_op_name(&foo);
    assert_eq!(result, None);
}

#[test]
fn test_ac_exprs_equal_atoms() {
    let a1 = ACExpr::Atom("x".to_string());
    let a2 = ACExpr::Atom("x".to_string());
    let a3 = ACExpr::Atom("y".to_string());

    assert!(ac_exprs_equal(&a1, &a2));
    assert!(!ac_exprs_equal(&a1, &a3));
}

#[test]
fn test_ac_exprs_equal_bvars() {
    let b1 = ACExpr::BVar(0);
    let b2 = ACExpr::BVar(0);
    let b3 = ACExpr::BVar(1);

    assert!(ac_exprs_equal(&b1, &b2));
    assert!(!ac_exprs_equal(&b1, &b3));
}

// =========================================================================
// push_cast tests
// =========================================================================

#[test]
fn test_push_cast_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now push_cast should fail with NoGoals
    let result = push_cast(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_exprs_syntactically_equal() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    assert!(exprs_syntactically_equal(&a, &a));
    assert!(!exprs_syntactically_equal(&a, &b));
}

#[test]
fn test_exprs_syntactically_equal_bvar() {
    let b1 = Expr::bvar(0);
    let b2 = Expr::bvar(0);
    let b3 = Expr::bvar(1);

    assert!(exprs_syntactically_equal(&b1, &b2));
    assert!(!exprs_syntactically_equal(&b1, &b3));
}

#[test]
fn test_exprs_syntactically_equal_app() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let app1 = Expr::app(f.clone(), a.clone());
    let app2 = Expr::app(f.clone(), a.clone());
    let app3 = Expr::app(f.clone(), b);

    assert!(exprs_syntactically_equal(&app1, &app2));
    assert!(!exprs_syntactically_equal(&app1, &app3));
}

// =========================================================================
// simp_all tests
// =========================================================================

#[test]
fn test_simp_all_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now simp_all should fail with NoGoals
    let result = simp_all(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_simp_all_basic() {
    let env = setup_env();
    // Goal: A (opaque constant, no simp lemmas apply)
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a.clone());
    let result = simp_all(&mut state);
    // simp_all on an opaque constant with no simp lemmas must fail
    assert!(
        result.is_err(),
        "simp_all should fail with no applicable lemmas"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after simp_all failure"
    );
    assert_eq!(
        state.goals.len(),
        1,
        "simp_all failure should preserve the single goal"
    );
    assert_eq!(
        state.goals[0].target, a,
        "goal target should be unchanged after simp_all failure"
    );
}

#[test]
fn test_is_true_const() {
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    assert!(is_true_const(&true_const));

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    assert!(!is_true_const(&false_const));

    let other = Expr::const_(Name::from_string("A"), vec![]);
    assert!(!is_true_const(&other));
}

#[test]
fn test_is_trivial_equality() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // a = a should be trivial
    let eq_aa = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat.clone(),
            ),
            a.clone(),
        ),
        a.clone(),
    );
    assert!(is_trivial_equality(&eq_aa));

    // a = b should not be trivial
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let eq_ab = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            a,
        ),
        b,
    );
    assert!(!is_trivial_equality(&eq_ab));
}
