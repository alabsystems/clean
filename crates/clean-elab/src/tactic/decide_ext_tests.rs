// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended decide tactics.
//!
//! Part of #3082 (Elaboration Parity).

use super::tests::*;
use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::level::Level;

// =========================================================================
// Helpers
// =========================================================================

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn bool_ty() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

fn bool_true() -> Expr {
    Expr::const_(Name::from_string("Bool.true"), vec![])
}

fn bool_false() -> Expr {
    Expr::const_(Name::from_string("Bool.false"), vec![])
}

fn true_prop() -> Expr {
    Expr::const_(Name::from_string("True"), vec![])
}

fn false_prop() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

fn mk_and(p: Expr, q: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p),
        q,
    )
}

fn mk_or(p: Expr, q: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p),
        q,
    )
}

fn mk_not(p: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, p, false_prop())
}

fn mk_iff(p: Expr, q: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p),
        q,
    )
}

fn mk_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

fn mk_bool_eq_true(e: Expr) -> Expr {
    mk_eq(bool_ty(), e, bool_true())
}

fn mk_beq_expr(ty: Expr, inst: Expr, a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("BEq.beq"), vec![]), ty),
                inst,
            ),
            a,
        ),
        b,
    )
}

fn setup_env_with_decidable() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_nat().unwrap();
    env.init_bool().unwrap();
    env.init_eq().unwrap();
    env.init_decidable().unwrap();
    env
}

fn setup_env_with_and() -> Environment {
    let mut env = setup_env_with_decidable();
    env.init_and().unwrap();
    env
}

fn setup_env_full() -> Environment {
    let mut env = setup_env_with_and();
    env.init_or().unwrap();
    env.init_iff().unwrap();
    env
}

// =========================================================================
// DecideExtConfig tests
// =========================================================================

#[test]
fn test_decide_ext_config_default() {
    let config = decide_ext::DecideExtConfig::default();
    assert_eq!(config.max_depth, 16);
    assert!(config.use_mathverse);
}

#[test]
fn test_decide_ext_config_custom() {
    let config = decide_ext::DecideExtConfig {
        max_depth: 4,
        timeout_ms: 100,
        use_mathverse: false,
    };
    assert_eq!(config.max_depth, 4);
    assert!(!config.use_mathverse);
    assert_eq!(config.timeout_ms, 100);
}

// =========================================================================
// eval_decide_ext basic tests
// =========================================================================

#[test]
fn test_decide_ext_no_goals_fails() {
    let env = Environment::new();
    let goal = true_prop();
    let mut state = ProofState::new(env, goal);
    state.goals.clear();
    let result = decide_ext::eval_decide_ext(&mut state);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "decide_ext should fail with NoGoals"
    );
}

#[test]
fn test_decide_ext_true() {
    let env = setup_env_with_decidable();
    let goal = true_prop();
    let mut state = ProofState::new(env, goal);
    decide_ext::eval_decide_ext(&mut state).expect("decide_ext should close True");
    assert!(state.is_complete());
}

#[test]
fn test_decide_ext_nat_eq_reflexive() {
    let env = setup_env_with_decidable();
    let goal = mk_eq(nat_ty(), Expr::nat_lit(7), Expr::nat_lit(7));
    let mut state = ProofState::new(env, goal);
    decide_ext::eval_decide_ext(&mut state).expect("decide_ext should close 7 = 7");
    assert!(state.is_complete());
}

#[test]
fn test_decide_ext_nat_eq_false() {
    let env = setup_env_with_decidable();
    let goal = mk_eq(nat_ty(), Expr::nat_lit(3), Expr::nat_lit(5));
    let mut state = ProofState::new(env, goal);
    let result = decide_ext::eval_decide_ext(&mut state);
    assert!(result.is_err(), "decide_ext should fail on 3 = 5");
}

// =========================================================================
// Compound decidability: And
// =========================================================================

#[test]
fn test_decide_ext_and_true_true() {
    let env = setup_env_with_and();
    let target = mk_and(true_prop(), true_prop());
    let mut state = ProofState::new(env, target);
    let _result = decide_ext::eval_decide_ext(&mut state);
}

#[test]
fn test_decide_ext_and_false_true() {
    let env = setup_env_with_and();
    let target = mk_and(false_prop(), true_prop());
    let mut state = ProofState::new(env, target);
    let _result = decide_ext::eval_decide_ext(&mut state);
}

// =========================================================================
// Compound decidability: Or
// =========================================================================

#[test]
fn test_decide_ext_or_true_false() {
    let env = setup_env_full();
    let target = mk_or(true_prop(), false_prop());
    let mut state = ProofState::new(env, target);
    let _result = decide_ext::eval_decide_ext(&mut state);
}

// =========================================================================
// Compound decidability: Not
// =========================================================================

#[test]
fn test_decide_ext_not_false() {
    let env = setup_env_with_decidable();
    let target = mk_not(false_prop());
    let mut state = ProofState::new(env, target);
    let _result = decide_ext::eval_decide_ext(&mut state);
}

// =========================================================================
// Compound decidability: Iff
// =========================================================================

#[test]
fn test_decide_ext_iff_true_true() {
    let env = setup_env_full();
    let target = mk_iff(true_prop(), true_prop());
    let mut state = ProofState::new(env, target);
    let _result = decide_ext::eval_decide_ext(&mut state);
}

// =========================================================================
// Boolean reflection: match_bool_eq_true
// =========================================================================

#[test]
fn test_match_bool_eq_true_lhs_pattern() {
    let target = mk_bool_eq_true(bool_true());
    let result = decide_ext::match_bool_eq_true(&target);
    assert!(result.is_some(), "should match e = true");
}

#[test]
fn test_match_bool_eq_true_rhs_pattern() {
    let target = mk_eq(bool_ty(), bool_true(), bool_false());
    let result = decide_ext::match_bool_eq_true(&target);
    assert!(result.is_some(), "should match true = e");
}

#[test]
fn test_match_bool_eq_true_non_bool_type() {
    let target = mk_eq(nat_ty(), Expr::nat_lit(0), Expr::nat_lit(0));
    let result = decide_ext::match_bool_eq_true(&target);
    assert!(
        result.is_none(),
        "Nat equality should not match bool_eq_true"
    );
}

#[test]
fn test_match_bool_eq_true_no_true_constant() {
    let target = mk_eq(bool_ty(), bool_false(), bool_false());
    let result = decide_ext::match_bool_eq_true(&target);
    assert!(
        result.is_none(),
        "false = false should not match bool_eq_true"
    );
}

#[test]
fn test_match_bool_eq_true_non_eq() {
    let target = true_prop();
    let result = decide_ext::match_bool_eq_true(&target);
    assert!(result.is_none(), "non-equality should not match");
}

// =========================================================================
// BEq matching: match_beq_eq_true
// =========================================================================

#[test]
fn test_match_beq_eq_true_pattern() {
    let inst = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq = mk_beq_expr(nat_ty(), inst, Expr::nat_lit(1), Expr::nat_lit(2));
    let target = mk_eq(bool_ty(), beq, bool_true());
    let result = decide_ext::match_beq_eq_true(&target);
    assert!(result.is_some(), "BEq.beq a b = true should match");
    let (ty, a, b) = result.unwrap();
    assert!(matches!(ty.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Nat")));
    assert!(
        matches!(a.kind(), ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(1))
    );
    assert!(
        matches!(b.kind(), ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) if n.to_u64() == Some(2))
    );
}

#[test]
fn test_match_beq_eq_true_symmetric() {
    let inst = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq = mk_beq_expr(nat_ty(), inst, Expr::nat_lit(3), Expr::nat_lit(4));
    let target = mk_eq(bool_ty(), bool_true(), beq);
    let result = decide_ext::match_beq_eq_true(&target);
    assert!(result.is_some(), "true = BEq.beq a b should match");
}

#[test]
fn test_match_beq_eq_true_non_beq() {
    let other = Expr::app(
        Expr::const_(Name::from_string("SomeOther"), vec![]),
        Expr::nat_lit(1),
    );
    let target = mk_eq(bool_ty(), other, bool_true());
    let result = decide_ext::match_beq_eq_true(&target);
    assert!(result.is_none(), "non-BEq expression should not match");
}

// =========================================================================
// find_decidable_eq_instance
// =========================================================================

#[test]
fn test_find_decidable_eq_instance_nat_with_dec_eq() {
    let mut env = setup_env_with_decidable();
    let nat = nat_ty();
    let dec_eq_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            nat.clone(),
                        ),
                        Expr::bvar(1),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.decEq"),
        level_params: vec![],
        type_: dec_eq_ty,
    })
    .unwrap();

    let state = ProofState::new(env, true_prop());
    let result = decide_ext::find_decidable_eq_instance(&state, &nat);
    assert!(result.is_some(), "should find Nat.decEq");
    assert_eq!(result.unwrap().to_string(), "Nat.decEq");
}

#[test]
fn test_find_decidable_eq_instance_unknown_type() {
    let env = setup_env_with_decidable();
    let state = ProofState::new(env, true_prop());
    let ty = Expr::const_(Name::from_string("MyCustomType"), vec![]);
    let result = decide_ext::find_decidable_eq_instance(&state, &ty);
    assert!(result.is_none(), "unknown type should not have DecidableEq");
}

#[test]
fn test_find_decidable_eq_instance_fvar() {
    let env = setup_env_with_decidable();
    let state = ProofState::new(env, true_prop());
    let ty = Expr::from_kind(ExprKind::FVar(FVarId::new(42)));
    let result = decide_ext::find_decidable_eq_instance(&state, &ty);
    assert!(result.is_none(), "FVar should not have DecidableEq");
}

// =========================================================================
// Depth limit
// =========================================================================

#[test]
fn test_decide_ext_depth_limit() {
    let env = setup_env_with_and();
    let config = decide_ext::DecideExtConfig {
        max_depth: 0,
        ..Default::default()
    };
    let target = mk_and(true_prop(), true_prop());
    let mut state = ProofState::new(env, target);
    let result = decide_ext::eval_decide_ext_with_config(&mut state, &config);
    let _ = result;
}

// =========================================================================
// Nested compound decidability
// =========================================================================

#[test]
fn test_decide_ext_nested_and_or() {
    let env = setup_env_full();
    let inner = mk_or(true_prop(), false_prop());
    let target = mk_and(inner, true_prop());
    let mut state = ProofState::new(env, target);
    let _result = decide_ext::eval_decide_ext(&mut state);
}

#[test]
fn test_decide_ext_not_not_true() {
    let env = setup_env_with_decidable();
    let not_true = mk_not(true_prop());
    let target = mk_not(not_true);
    let mut state = ProofState::new(env, target);
    let _result = decide_ext::eval_decide_ext(&mut state);
}

// =========================================================================
// Mathverse and config toggles
// =========================================================================

#[test]
fn test_decide_ext_mathverse_disabled() {
    // Wave 94 — Gap 4 CLOSED. `decide` without `mathverse` now closes
    // numeric reflexive equalities via the kernel `is_def_eq` /
    // `Eq.refl` short-circuit inside `synthesize_compound_decidable`.
    let env = setup_env_with_decidable();
    let config = decide_ext::DecideExtConfig {
        use_mathverse: false,
        ..Default::default()
    };
    let target = mk_eq(nat_ty(), Expr::nat_lit(42), Expr::nat_lit(42));
    let mut state = ProofState::new(env, target);
    let result = decide_ext::eval_decide_ext_with_config(&mut state, &config);
    assert!(
        result.is_ok(),
        "decide_ext should close 42=42:Nat without mathverse: {result:?}"
    );
}

#[test]
fn test_decide_ext_mathverse_disabled_non_reflexive_does_not_falsely_close() {
    // Wave 94 — Gap 4 negative test. The kernel `Eq.refl`
    // short-circuit must NOT fire on a genuinely non-reflexive
    // numeric equality. Without `mathverse` and without decidable-eq
    // hooks for Nat in this minimal env, `decide` cannot close
    // `41 = 42 : Nat`; the rewrite must refuse rather than fake a
    // reflexivity proof.
    let env = setup_env_with_decidable();
    let config = decide_ext::DecideExtConfig {
        use_mathverse: false,
        ..Default::default()
    };
    let target = mk_eq(nat_ty(), Expr::nat_lit(41), Expr::nat_lit(42));
    let mut state = ProofState::new(env, target);
    let result = decide_ext::eval_decide_ext_with_config(&mut state, &config);
    assert!(
        result.is_err(),
        "decide_ext without mathverse must NOT close 41=42:Nat: {result:?}"
    );
}

#[test]
fn test_decide_ext_mathverse_enabled_default() {
    let config = decide_ext::DecideExtConfig::default();
    assert!(
        config.use_mathverse,
        "mathverse should be enabled by default"
    );
    assert_eq!(config.timeout_ms, 250, "default timeout should be 250ms");
}

#[test]
fn test_decide_ext_true_with_config() {
    let env = setup_env_with_decidable();
    let config = decide_ext::DecideExtConfig {
        use_mathverse: false,
        ..Default::default()
    };
    let target = true_prop();
    let mut state = ProofState::new(env, target);
    let result = decide_ext::eval_decide_ext_with_config(&mut state, &config);
    assert!(result.is_ok(), "True should close with mathverse disabled");
}

// =========================================================================
// DecidableEq instance search path
// =========================================================================

#[test]
fn test_decide_ext_dec_eq_instance_search() {
    let mut env = setup_env_with_decidable();
    let nat = nat_ty();
    let dec_eq_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Decidable"), vec![]),
                mk_eq(nat.clone(), Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.decEq"),
        level_params: vec![],
        type_: dec_eq_ty,
    })
    .unwrap();

    let goal = mk_eq(nat, Expr::nat_lit(0), Expr::nat_lit(0));
    let mut state = ProofState::new(env, goal);
    decide_ext::eval_decide_ext(&mut state).expect("0 = 0 with DecidableEq should close");
    assert!(state.is_complete());
}
