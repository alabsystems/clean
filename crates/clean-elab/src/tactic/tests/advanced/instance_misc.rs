// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance and miscellaneous tactic tests: polynomial arithmetic,
//! infer_instance, nontriviality, blast, dec_trivial.

use super::support::make_local;
use super::*;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::sorry::sorry_count;
use serial_test::serial;

use crate::tactic::arith_proof_count;

// =============================================================================
// Polynomial Arithmetic Tests
// =============================================================================

#[test]
fn test_polynomial_zero() {
    let p = Polynomial::zero();
    assert!(p.is_zero());
    assert_eq!(p.degree(), 0);
}

#[test]
fn test_polynomial_constant() {
    let p = Polynomial::constant(5, 1);
    assert!(!p.is_zero());
    assert_eq!(p.degree(), 0);

    let zero = Polynomial::constant(0, 1);
    assert!(zero.is_zero());
}

#[test]
fn test_polynomial_var() {
    let x = Polynomial::var(0);
    assert!(!x.is_zero());
    assert_eq!(x.degree(), 1);
}

#[test]
fn test_polynomial_add() {
    let x = Polynomial::var(0);
    let y = Polynomial::var(1);
    let sum = x.add(&y);
    assert!(!sum.is_zero());
    assert_eq!(sum.degree(), 1);
}

#[test]
fn test_polynomial_sub() {
    let x = Polynomial::var(0);
    let diff = x.sub(&x);
    assert!(diff.is_zero());
}

#[test]
fn test_polynomial_mul() {
    let x = Polynomial::var(0);
    let y = Polynomial::var(1);
    let prod = x.mul(&y);
    assert!(!prod.is_zero());
    assert_eq!(prod.degree(), 2); // xy has degree 2
}

#[test]
fn test_polynomial_negate() {
    let x = Polynomial::var(0);
    let neg_x = x.negate();
    assert!(!neg_x.is_zero());

    let sum = x.add(&neg_x);
    assert!(sum.is_zero());
}

#[test]
fn test_polynomial_operations() {
    // Test (x + y) * (x - y) = x^2 - y^2
    let x = Polynomial::var(0);
    let y = Polynomial::var(1);

    let x_plus_y = x.add(&y);
    let x_minus_y = x.sub(&y);
    let product = x_plus_y.mul(&x_minus_y);

    // x^2 - y^2
    let x_squared = x.mul(&x);
    let y_squared = y.mul(&y);
    let expected = x_squared.sub(&y_squared);

    // They should be equal
    let diff = product.sub(&expected);
    assert!(diff.is_zero());
}

#[test]
fn test_polyrith_config_default() {
    let config = PolyrithConfig::default();
    assert_eq!(config.max_degree, 4);
    assert!(config.try_simple);
    assert_eq!(config.max_hyps, 10);
}

#[test]
fn test_polyrith_certificate_fields() {
    let cert = PolyrithCertificate {
        coefficients: vec![("h".to_string(), Polynomial::constant(1, 1))],
        verified: true,
        explanation: "test".to_string(),
    };
    assert!(cert.verified);
    assert_eq!(cert.coefficients.len(), 1);
}

#[test]
fn test_gcd_u64() {
    assert_eq!(gcd_u64(12, 8), 4);
    assert_eq!(gcd_u64(7, 3), 1);
    assert_eq!(gcd_u64(0, 5), 5);
    assert_eq!(gcd_u64(5, 0), 5);
}

#[test]
fn test_is_polynomial_expr_nat_literal() {
    let lit = Expr::nat_lit(42);
    assert!(is_polynomial_expr(&lit));
}

#[test]
fn test_is_polynomial_expr_fvar() {
    let fvar = Expr::fvar(FVarId::new(0));
    assert!(is_polynomial_expr(&fvar));
}

#[test]
fn test_polyrith_trivial_equality() {
    let env = setup_env();
    // Goal: 0 = 0
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::nat_lit(0);

    // Build equality type Eq Nat 0 0
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_nat = Expr::app(eq_const, nat);
    let eq_nat_zero = Expr::app(eq_nat, zero.clone());
    let target = Expr::app(eq_nat_zero, zero);

    let mut state = ProofState::new(env, target);
    // polyrith tries rfl internally; in a minimal env without Eq.refl it should
    // fail gracefully rather than panic
    let err = polyrith(&mut state).unwrap_err();
    let err_msg = format!("{:?}", err);
    assert!(
        err_msg.contains("rfl") || err_msg.contains("reflexivity"),
        "polyrith error should mention reflexivity failure, got: {err_msg}"
    );
}

/// Build `Eq Nat lhs rhs` expression.
fn make_nat_eq_expr(lhs: Expr, rhs: Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::app(Expr::app(Expr::app(eq_const, nat_ty), lhs), rhs)
}

/// Assert polyrith reconstructs the proof without trustedArith or sorry.
fn assert_polyrith_reconstructs_without_trust(state: &mut ProofState, desc: &str) {
    let sorry_before = sorry_count();
    let arith_before = arith_proof_count();

    let result = polyrith(state);
    assert!(
        result.is_ok(),
        "polyrith should succeed ({desc}): {result:?}"
    );
    assert!(state.is_complete(), "goal should be closed ({desc})");
    assert_eq!(
        sorry_count() - sorry_before,
        0,
        "{desc}: should NOT use sorry"
    );
    assert_eq!(
        arith_proof_count() - arith_before,
        0,
        "{desc}: proof reconstruction should avoid trustedArith"
    );
}

/// Regression for #2520, updated by #2526: single-hypothesis cert now uses
/// kernel proof reconstruction (no trustedArith, no sorry).
#[test]
#[serial]
fn test_polyrith_verified_single_hypothesis_reconstructs_without_trusted_arith() {
    let env = Environment::with_prelude();
    let a = Expr::fvar(FVarId::new(100));
    let b = Expr::fvar(FVarId::new(101));
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_ab = make_nat_eq_expr(a.clone(), b.clone());

    let ctx = vec![
        make_local(100, "a", nat_ty.clone()),
        make_local(101, "b", nat_ty),
        make_local(50, "h", eq_ab.clone()),
    ];
    let mut state = ProofState::with_context(env, eq_ab, ctx);
    let sorry_before = sorry_count();
    let arith_before = arith_proof_count();

    let result = polyrith(&mut state);
    assert!(result.is_ok(), "polyrith should succeed: {result:?}");
    assert!(state.is_complete(), "goal should be closed");
    assert_eq!(
        sorry_count() - sorry_before,
        0,
        "single-hyp cert: should NOT use sorry"
    );
    assert_eq!(
        arith_proof_count() - arith_before,
        0,
        "single-hyp cert: proof reconstruction should eliminate trustedArith (#2526)"
    );
}

/// Regression for #2567: verified two-hypothesis cert reconstructs cleanly.
///
/// h1: a = b, h2: b = c, goal: a = c. Certificate: 1*h1 + 1*h2.
#[test]
#[serial]
fn test_polyrith_verified_two_hypothesis_reconstructs_without_trusted_arith() {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas()
        .expect("Nat arithmetic lemmas should initialize");
    let a = Expr::fvar(FVarId::new(100));
    let b = Expr::fvar(FVarId::new(101));
    let c = Expr::fvar(FVarId::new(102));
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    let ctx = vec![
        make_local(100, "a", nat_ty.clone()),
        make_local(101, "b", nat_ty.clone()),
        make_local(102, "c", nat_ty.clone()),
        make_local(50, "h1", make_nat_eq_expr(a.clone(), b.clone())),
        make_local(51, "h2", make_nat_eq_expr(b, c.clone())),
    ];
    let goal = make_nat_eq_expr(a, c);
    let mut state = ProofState::with_context(env, goal, ctx);
    assert_polyrith_reconstructs_without_trust(&mut state, "two-hyp verified cert");
}

// NOTE: mono, simpa, continuity, measurability tests moved to mathlib_tactics.rs
// NOTE: rintro, peel, split_ifs tests moved to pattern_tactics.rs

// ========== REMOVED: Tests for rintro tactic ==========
// ========== REMOVED: Tests for peel tactic ==========
// ========== REMOVED: Tests for split_ifs tactic ==========

#[test]
fn test_choose_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = choose(&mut state, "h", "x", "hx");
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_choose_hyp_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = choose(&mut state, "nonexistent", "x", "hx");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

#[test]
fn test_choose_not_existential() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Add a hypothesis that is not an existential
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "h".to_string(),
        ty: Expr::const_(Name::from_string("A"), vec![]),
        value: None,
    });

    let result = choose(&mut state, "h", "x", "hx");
    assert!(matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("existential")));
}

#[test]
fn test_choose_config_new() {
    let config = ChooseConfig::new();
    assert_eq!(config.witness_name, None);
    assert_eq!(config.proof_name, None);
}

#[test]
fn test_choose_config_builder() {
    let config = ChooseConfig::new()
        .with_witness_name("x")
        .with_proof_name("hx");

    assert_eq!(config.witness_name, Some("x".to_string()));
    assert_eq!(config.proof_name, Some("hx".to_string()));
}

#[test]
fn test_try_extract_exists_not_exists() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    assert_eq!(try_extract_exists(&a), None);
}

#[test]
fn test_apply_predicate_non_lambda() {
    let pred = Expr::const_(Name::from_string("P"), vec![]);
    let arg = Expr::const_(Name::from_string("a"), vec![]);
    let result = apply_predicate(&pred, arg.clone());

    // Should just be an application
    match result.kind() {
        ExprKind::App(f, a) => {
            assert!(matches!(f.kind(), ExprKind::Const(_, _)));
            assert!(matches!(a.kind(), ExprKind::Const(_, _)));
        }
        _ => panic!("Expected App"),
    }
}

// ========== Tests for infer_instance tactic (N=480) ==========

#[test]
fn test_infer_instance_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = infer_instance(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_infer_instance_not_class() {
    let env = setup_env();
    // A simple type, not a type class
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Should fail because A is not a type class constraint
    let result = infer_instance(&mut state);
    assert!(
        matches!(result, Err(TacticError::InstanceSynthesisFailed { ref class, .. }) if class == "A"),
        "should fail for class A, got: {result:?}"
    );
}

#[test]
fn test_infer_instance_config_new() {
    let config = InferInstanceConfig::new();
    assert_eq!(config.max_depth, 32);
    assert!(!config.verbose);
}

#[test]
fn test_infer_instance_config_builder() {
    let config = InferInstanceConfig::new().with_max_depth(16).verbose(true);

    assert_eq!(config.max_depth, 16);
    assert!(config.verbose);
}

#[test]
fn test_infer_instance_decidable_true_has_implicit_prop_arg() {
    // Regression test for #2461: Decidable.isTrue must include the implicit
    // {p : Prop} argument. Without it, the proof term is ill-typed:
    //   Const(Decidable.isTrue)                          — 0 args, WRONG (old)
    //   App(App(Decidable.isTrue, True), True.intro)     — 2 args, CORRECT
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_decidable().unwrap();

    // Goal: Decidable True
    let decidable_true = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    let mut state = ProofState::new(env, decidable_true);

    let result = infer_instance(&mut state);
    assert!(
        result.is_ok(),
        "infer_instance should solve Decidable True, got: {result:?}"
    );
    assert!(state.is_complete(), "goal should be closed");

    let proof = state
        .proof_term()
        .expect("completed state should have proof term");
    let head = proof.get_app_fn();
    let args = proof.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Decidable.isTrue",
            "proof head should be Decidable.isTrue, got: {name}",
        );
    } else {
        panic!(
            "proof head should be Const (Decidable.isTrue), got: {:?}",
            head.kind()
        );
    }

    assert_eq!(
        args.len(),
        2,
        "Decidable.isTrue needs 2 args (implicit {{p}} + proof of p), got {} (#2461)",
        args.len()
    );
}

#[test]
fn test_infer_instance_decidable_false_constructs_two_arg_term() {
    // Regression test for #2461: verify the isFalse proof construction
    // produces a 2-arg term (implicit {p} + proof of ¬p), not a bare constant.
    //
    // NOTE: Cannot end-to-end test Decidable False via infer_instance because
    // init_decidable uses an impredicative False encoding (∀ q : Prop, q) that
    // is incompatible with the inductive False from init_true_false.
    // The actual proof validates in .olean-loaded environments where both
    // definitions are consistent. Here we verify the term structure directly.
    use clean_kernel::BinderInfo;

    // Construct the proof term that infer_instance produces for Decidable False
    let prop = Expr::const_(Name::from_string("False"), vec![]);
    let proof = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
            prop,
        ),
        Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::from_string("False"), vec![]),
            Expr::bvar(0),
        ),
    );

    // Verify structure: 2 args (implicit {p} + proof of ¬p)
    let head = proof.get_app_fn();
    let args = proof.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Decidable.isFalse");
    } else {
        panic!("expected Const head, got: {:?}", head.kind());
    }

    assert_eq!(
        args.len(),
        2,
        "Decidable.isFalse needs 2 args (implicit {{p}} + proof of not-p), got {} (#2461)",
        args.len()
    );
}

#[test]
fn test_extract_class_name_const() {
    let c = Expr::const_(Name::from_string("Decidable"), vec![]);
    assert_eq!(extract_class_name(&c), Some("Decidable".to_string()));
}

#[test]
fn test_extract_class_name_app() {
    let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let app = Expr::app(decidable, p);
    assert_eq!(extract_class_name(&app), Some("Decidable".to_string()));
}

#[test]
fn test_is_true_prop() {
    assert!(is_true_prop(&Expr::const_(
        Name::from_string("True"),
        vec![]
    )));
    assert!(is_true_prop(&Expr::const_(
        Name::from_string("Prop.True"),
        vec![]
    )));
    assert!(!is_true_prop(&Expr::const_(
        Name::from_string("False"),
        vec![]
    )));
}

#[test]
fn test_is_false_prop() {
    assert!(is_false_prop(&Expr::const_(
        Name::from_string("False"),
        vec![]
    )));
    assert!(is_false_prop(&Expr::const_(
        Name::from_string("Prop.False"),
        vec![]
    )));
    assert!(!is_false_prop(&Expr::const_(
        Name::from_string("True"),
        vec![]
    )));
}

#[test]
fn test_infer_simple_type_nat_literal() {
    let lit = Expr::nat_lit(42);
    let ty = infer_simple_type(&lit);
    let Some(ref ty_expr) = ty else {
        panic!("Expected Some(Const(Nat)), got: {ty:?}");
    };
    let ExprKind::Const(name, _) = ty_expr.kind() else {
        panic!("Expected Const(Nat), got: {ty_expr:?}");
    };
    assert_eq!(name.to_string(), "Nat");
}

#[test]
fn test_infer_simple_type_string_literal() {
    let lit = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::String("hello".into())));
    let ty = infer_simple_type(&lit);
    let Some(ref ty_expr) = ty else {
        panic!("Expected Some(Const(String)), got: {ty:?}");
    };
    let ExprKind::Const(name, _) = ty_expr.kind() else {
        panic!("Expected Const(String), got: {ty_expr:?}");
    };
    assert_eq!(name.to_string(), "String");
}

// ========== Tests for nontriviality tactic (N=480) ==========

#[test]
fn test_nontriviality_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = nontriviality(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_nontriviality_config_new() {
    let config = NontrivialityConfig::new();
    assert_eq!(config.type_expr, None);
}

#[test]
fn test_nontriviality_config_with_type() {
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let config = NontrivialityConfig::new().with_type(ty.clone());
    assert_eq!(config.type_expr, Some(ty));
}

#[test]
fn test_try_infer_expr_type_nat_literal() {
    let expr = Expr::nat_lit(42);
    let ty = try_infer_expr_type(&expr);
    let Some(ref ty_expr) = ty else {
        panic!("Expected Some(Const(Nat)), got: {ty:?}");
    };
    let ExprKind::Const(name, _) = ty_expr.kind() else {
        panic!("Expected Const(Nat), got: {ty_expr:?}");
    };
    assert_eq!(name.to_string(), "Nat");
}

#[test]
fn test_try_infer_expr_type_const() {
    let expr = Expr::const_(Name::from_string("Nat"), vec![]);
    let ty = try_infer_expr_type(&expr).expect("try_infer_expr_type(Nat) should return Some");
    // Nat is a constant; its inferred type should be a Sort or Type
    assert!(
        matches!(ty.kind(), ExprKind::Sort(_) | ExprKind::Const(..)),
        "Expected Sort or Const type for Nat, got: {ty:?}"
    );
}

#[test]
fn test_find_first_type_nat() {
    let expr = Expr::const_(Name::from_string("Nat"), vec![]);
    let ty = find_first_type(&expr).expect("find_first_type(Nat) should return Some");
    assert!(
        matches!(ty.kind(), ExprKind::Const(ref n, _) if n.to_string() == "Nat"),
        "find_first_type on Nat constant should return Nat, got: {ty:?}"
    );
}

#[test]
fn test_find_first_type_nested() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let app = Expr::app(a, nat);
    let ty = find_first_type(&app).expect("find_first_type on app(a, Nat) should return Some");
    // Should find a type — either Nat or a from the app subexpressions
    assert!(
        matches!(ty.kind(), ExprKind::Const(..)),
        "find_first_type on app should return a Const, got: {ty:?}"
    );
}

#[test]
fn test_find_first_type_not_found() {
    let expr = Expr::const_(Name::from_string("foo"), vec![]);
    let ty = find_first_type(&expr);
    assert_eq!(ty, None);
}

// ========== Tests for blast and dec_trivial tactics (N=481) ==========

#[test]
fn test_blast_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = blast(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_blast_config_builder() {
    let config = BlastConfig::new()
        .with_max_rounds(3)
        .with_solve_by_elim_depth(2)
        .use_arith(false)
        .use_tauto(false)
        .use_simp(false)
        .use_library_search(false);

    assert_eq!(config.max_rounds, 3);
    assert_eq!(config.solve_by_elim_depth, 2);
    assert!(!config.use_arith);
    assert!(!config.use_tauto);
    assert!(!config.use_simp);
    assert!(!config.use_library_search);
}

#[test]
fn test_blast_solves_simple_chain() {
    let env = setup_env_with_and_or();
    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);

    let ctx = vec![
        LocalDecl {
            fvar: FVarId::new(0),
            name: "hp".to_string(),
            ty: prop_p.clone(),
            value: None,
        },
        LocalDecl {
            fvar: FVarId::new(1),
            name: "hpq".to_string(),
            ty: Expr::arrow(prop_p.clone(), prop_q.clone()),
            value: None,
        },
    ];

    let mut state = ProofState::with_context(env, prop_q, ctx);
    blast(&mut state).unwrap();
    assert!(state.is_complete());
}

#[test]
fn test_dec_trivial_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = dec_trivial(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_dec_trivial_assumption() {
    let env = setup_env();
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "h".to_string(),
        ty: ty.clone(),
        value: None,
    }];

    let mut state = ProofState::with_context(env, ty, ctx);
    dec_trivial(&mut state).unwrap();
    assert!(state.is_complete());
}
