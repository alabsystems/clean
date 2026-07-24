// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance and miscellaneous tactic tests (continued): linear_combination,
//! dsimp, cast tactics, lift, instance tactics, infer_i, squeeze_simp.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

// ========== Tests for N=482 tactics: linear_combination, dsimp, cast tactics, lift, instance tactics ==========

#[test]
fn test_linear_coeff_one() {
    let coeff = LinearCoeff::one("h1");
    assert_eq!(coeff.hyp_name, "h1");
    assert_eq!(coeff.coeff, (1, 1));
}

#[test]
fn test_linear_coeff_int() {
    let coeff = LinearCoeff::int("h2", -3);
    assert_eq!(coeff.hyp_name, "h2");
    assert_eq!(coeff.coeff, (-3, 1));
}

#[test]
fn test_linear_coeff_rational() {
    let coeff = LinearCoeff::new("h3", 2, 5);
    assert_eq!(coeff.hyp_name, "h3");
    assert_eq!(coeff.coeff, (2, 5));
}

#[test]
fn test_linear_combination_config_default() {
    let config = LinearCombinationConfig::new();
    assert!(config.normalize);
    assert!(!config.exact);
}

#[test]
fn test_linear_combination_config_builder() {
    let config = LinearCombinationConfig::new()
        .with_normalize(false)
        .with_exact(true);
    assert!(!config.normalize);
    assert!(config.exact);
}

#[test]
fn test_linear_combination_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = linear_combination(&mut state, vec![]);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_dsimp_config_default() {
    let config = DsimpConfig::new();
    assert!(!config.at_hyps);
    assert_eq!(config.max_depth, 100);
    assert!(config.beta);
    assert!(config.eta);
    assert!(config.zeta);
    assert!(config.iota);
}

#[test]
fn test_dsimp_config_builder() {
    let config = DsimpConfig::new().at_all().with_beta(false).with_eta(false);
    assert!(config.at_hyps);
    assert!(!config.beta);
    assert!(!config.eta);
}

#[test]
fn test_dsimp_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = dsimp(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_dsimp_at_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = dsimp_at(&mut state, "h");
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

fn add_type_family_p(env: &mut Environment) -> Expr {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::type_(),
        ),
    })
    .unwrap();
    Expr::const_(Name::from_string("P"), vec![])
}

fn make_reducible_hyp_pair(p: &Expr) -> (Expr, Expr, LocalDecl, Expr, LocalDecl) {
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let h1_ty = Expr::let_named(
        Name::from_string("h1_alias"),
        Expr::type_(),
        a_ty.clone(),
        Expr::bvar(0),
        false,
    );
    let h1 = LocalDecl {
        fvar: FVarId::new(0),
        name: "h1".to_string(),
        ty: h1_ty.clone(),
        value: None,
    };
    let h2_ty = Expr::let_named(
        Name::from_string("family_alias"),
        Expr::pi(BinderInfo::Default, a_ty.clone(), Expr::type_()),
        Expr::lam(
            BinderInfo::Default,
            a_ty.clone(),
            Expr::app(p.clone(), Expr::bvar(0)),
        ),
        Expr::app(Expr::bvar(0), Expr::fvar(h1.fvar)),
        false,
    );
    let h2 = LocalDecl {
        fvar: FVarId::new(1),
        name: "h2".to_string(),
        ty: h2_ty.clone(),
        value: None,
    };
    (a_ty, h1_ty, h1, h2_ty, h2)
}

/// Test that dsimp_with_config(.at_all()) simplifies hypotheses even when
/// the goal target is already in normal form. Regression test for the
/// early-return bug fixed in W3 commit 587bed3ae (Re: #1840).
#[test]
fn test_dsimp_at_all_simplifies_hyps_when_target_unchanged() {
    let mut env = setup_env();
    let p = add_type_family_p(&mut env);

    // Goal target: B (already in normal form — dsimp_expr returns it unchanged)
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let (a_ty, h1_ty, h1, h2_ty, h2) = make_reducible_hyp_pair(&p);

    let mut state = ProofState::with_context(env, target.clone(), vec![h1, h2]);

    // Verify precondition: both hypothesis types are reducible.
    let goal_before = state.current_goal().unwrap();
    assert_eq!(
        goal_before.local_ctx[0].ty, h1_ty,
        "precondition: h1 should be unreduced"
    );
    assert_eq!(
        goal_before.local_ctx[1].ty, h2_ty,
        "precondition: h2 should be unreduced"
    );

    // Run dsimp with at_all() — should simplify hypotheses even though target is unchanged.
    let result = dsimp_with_config(&mut state, DsimpConfig::new().at_all());
    assert!(
        result.is_ok(),
        "dsimp_with_config(.at_all()) failed: {result:?}"
    );

    // Goal target should still be B (unchanged)
    let goal_after = state.current_goal().unwrap();
    assert_eq!(
        goal_after.target, target,
        "goal target should remain unchanged"
    );

    assert_eq!(
        goal_after.local_ctx[0].ty, a_ty,
        "first hypothesis type should reduce to A"
    );
    assert_eq!(
        goal_after.local_ctx[1].ty,
        Expr::app(p, Expr::fvar(goal_after.local_ctx[0].fvar)),
        "second hypothesis must be rewritten against the fresh current h1 fvar"
    );
}

#[test]
fn test_cast_config_default() {
    let config = CastConfig::new();
    assert!(config.push_inward);
    assert!(!config.pull_outward);
}

#[test]
fn test_exact_mod_cast_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let proof = Expr::const_(Name::from_string("proof"), vec![]);
    let result = exact_mod_cast(&mut state, proof);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_assumption_mod_cast_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = assumption_mod_cast(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_zify_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = zify(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_qify_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = qify(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_lift_config_default() {
    let config = LiftConfig::new();
    assert_eq!(config.new_name, None);
    assert_eq!(config.proof_name, None);
}

#[test]
fn test_lift_config_builder() {
    let config = LiftConfig::new().with_name("x_int").with_proof("hx");
    assert_eq!(config.new_name, Some("x_int".to_string()));
    assert_eq!(config.proof_name, Some("hx".to_string()));
}

#[test]
fn test_lift_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = lift(&mut state, "x", None);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_lift_var_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = lift(&mut state, "nonexistent", None);
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s.contains("not found"))
    );
}

#[test]
fn test_let_i_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let ty = Expr::const_(Name::from_string("Decidable"), vec![]);
    let value = Expr::const_(Name::from_string("inst"), vec![]);
    let result = let_i(&mut state, "inst", ty, value);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_let_i_adds_to_context() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let value = Expr::const_(Name::from_string("a"), vec![]);
    let_i(&mut state, "inst", ty.clone(), value).unwrap();

    let goal = state.current_goal().unwrap();
    assert!(goal.local_ctx.iter().any(|d| d.name == "inst"));
}

#[test]
fn test_have_i_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let ty = Expr::const_(Name::from_string("Decidable"), vec![]);
    let result = have_i(&mut state, "inst", ty);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_infer_i_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let ty = Expr::const_(Name::from_string("Decidable"), vec![]);
    let result = infer_i(&mut state, "inst", ty);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_infer_i_adds_to_context() {
    use crate::instances::InstanceTable;

    let mut env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);

    // Register a Decidable class with a concrete instance so resolution succeeds
    let mut instances = InstanceTable::new();
    let decidable_name = Name::from_string("Decidable");
    instances.register_class(decidable_name.clone(), 0, vec![]);
    let inst_name = Name::from_string("instDecidable");
    let inst_expr = Expr::const_(inst_name.clone(), vec![]);
    let inst_ty = Expr::const_(decidable_name.clone(), vec![]);
    env.add_decl(Declaration::Axiom {
        name: decidable_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: inst_name.clone(),
        level_params: vec![],
        type_: inst_ty.clone(),
    })
    .unwrap();
    instances.add_instance(inst_name, decidable_name, inst_expr, inst_ty, 100);

    let mut state = ProofState::with_instances(env, target, instances);

    let ty = Expr::const_(Name::from_string("Decidable"), vec![]);
    infer_i(&mut state, "inst", ty).unwrap();

    let goal = state.current_goal().unwrap();
    assert!(goal.local_ctx.iter().any(|d| d.name == "inst"));
}

// ========== Tests for infer_i with InstanceTable ==========

#[test]
fn test_infer_i_with_instance_table_resolves_instance() {
    use crate::instances::InstanceTable;

    let mut env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);

    // Create instance table with a registered class and instance
    let mut instances = InstanceTable::new();
    let add_class = Name::from_string("Add");
    instances.register_class(add_class.clone(), 1, vec![]);

    // Register an instance: instAddNat : Add Nat
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let add_nat = Expr::app(Expr::const_(add_class.clone(), vec![]), nat_ty.clone());
    let inst_expr = Expr::const_(Name::from_string("instAddNat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: add_class.clone(),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::prop()),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("instAddNat"),
        level_params: vec![],
        type_: add_nat.clone(),
    })
    .unwrap();
    instances.add_instance(
        Name::from_string("instAddNat"),
        add_class.clone(),
        inst_expr.clone(),
        add_nat.clone(),
        100,
    );

    // Create proof state with instances
    let mut state = ProofState::with_instances(env, target, instances);

    // Try to infer Add Nat - should resolve to instAddNat
    infer_i(&mut state, "inst", add_nat).unwrap();

    let goal = state.current_goal().unwrap();
    let inst_decl = goal.local_ctx.iter().find(|d| d.name == "inst").unwrap();

    // The value should be the instance expression, not a sorry
    let value = inst_decl
        .value
        .as_ref()
        .expect("infer_i should produce a value");
    // Value should be instAddNat (not a sorry)
    assert!(
        matches!(value.kind(), ExprKind::Const(n, _) if n.to_string() == "instAddNat"),
        "infer_i should resolve to instAddNat, got {:?}",
        value
    );
}

#[test]
fn test_infer_i_without_instance_table_returns_error() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Try to infer some class without instance table
    let add_class = Name::from_string("Add");
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let add_nat = Expr::app(Expr::const_(add_class, vec![]), nat_ty);

    // Without instance table, infer_i should fail (not silently create sorry)
    let result = infer_i(&mut state, "inst", add_nat);
    assert!(
        result.is_err(),
        "infer_i without instance table should return error"
    );
}

#[test]
fn test_infer_i_with_unregistered_class_returns_error() {
    use crate::instances::InstanceTable;

    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);

    // Create instance table but don't register the class we'll query
    let instances = InstanceTable::new();
    let mut state = ProofState::with_instances(env, target, instances);

    // Try to infer an unregistered class
    let unknown_class = Name::from_string("UnknownClass");
    let unknown_ty = Expr::app(
        Expr::const_(unknown_class, vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );

    // With instance table but unregistered class, infer_i should fail
    let result = infer_i(&mut state, "inst", unknown_ty);
    assert!(
        result.is_err(),
        "infer_i with unregistered class should return error"
    );
}

#[test]
fn test_proof_state_with_instances_constructor() {
    use crate::instances::InstanceTable;

    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let instances = InstanceTable::new();

    let state = ProofState::with_instances(env, target.clone(), instances);

    state.instances().expect("Should have instance table");
    let goal = state.current_goal().expect("Should have goal");
    assert_eq!(
        goal.target, target,
        "Goal target should match construction target"
    );
}

#[test]
fn test_proof_state_set_instances() {
    use crate::instances::InstanceTable;

    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    assert!(state.instances().is_none(), "Initially no instances");

    let instances = InstanceTable::new();
    state.set_instances(instances);

    state
        .instances()
        .expect("After set_instances, should have instance table");
}

#[test]
fn test_occurs_bvar_dsimp_found() {
    let expr = Expr::bvar(0);
    assert!(occurs_bvar_dsimp(&expr, 0));
}

#[test]
fn test_occurs_bvar_dsimp_not_found() {
    let expr = Expr::bvar(1);
    assert!(!occurs_bvar_dsimp(&expr, 0));
}

#[test]
fn test_shift_bvars_dsimp_shifts_correctly() {
    let expr = Expr::bvar(2);
    let shifted = shift_bvars_dsimp(&expr, 1, 0);
    assert_eq!(shifted, Expr::bvar(3));
}

#[test]
fn test_shift_bvars_dsimp_respects_cutoff() {
    let expr = Expr::bvar(0);
    let shifted = shift_bvars_dsimp(&expr, 1, 1);
    assert_eq!(shifted, Expr::bvar(0));
}

// ========================================================================
// Tests for squeeze_simp (N=483)
// ========================================================================

#[test]
fn test_squeeze_simp_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = squeeze_simp(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_squeeze_simp_returns_result() {
    let env = setup_env();
    // Simple goal that simp should handle
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let squeeze_result = squeeze_simp(&mut state).expect("squeeze_simp should succeed");
    // Should return a suggested tactic
    assert!(squeeze_result.suggested_tactic.starts_with("simp only ["));
}

#[test]
fn test_squeeze_simp_with_config() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let config = SqueezeSimpConfig {
        simp_config: SimpConfig::new(),
        verbose: true,
    };
    let squeeze_result = squeeze_simp_with_config(&mut state, config)
        .expect("squeeze_simp_with_config should succeed");
    // Config variant should also return a suggested tactic
    assert!(
        squeeze_result.suggested_tactic.starts_with("simp only ["),
        "squeeze_simp_with_config should produce a suggested tactic, got: {}",
        squeeze_result.suggested_tactic
    );
}

#[test]
fn test_squeeze_simp_and_apply_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = squeeze_simp_and_apply(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_squeeze_simp_config_default() {
    let config = SqueezeSimpConfig::new();
    assert!(!config.verbose);
}

/// Test that squeeze_simp correctly tracks which lemmas were used.
///
/// This test verifies that the `used_lemmas` field in SqueezeSimpResult
/// is populated when simp lemmas are actually applied during simplification.
///
/// Setup:
/// - Environment with Nat, Eq, and Nat.add_zero lemma
/// - Goal: n + 0 = n (should be simplified by Nat.add_zero)
///
/// Expected:
/// - squeeze_simp should track "Nat.add_zero" in used_lemmas
/// - suggested_tactic should contain "Nat.add_zero"
#[test]
fn test_squeeze_simp_tracks_used_lemmas() {
    // Setup environment with Nat arithmetic lemmas including Nat.add_zero
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    // Build goal: Nat.add n Nat.zero = n (i.e., n + 0 = n)
    // where n is some Nat constant we define
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // Add a constant 'n' of type Nat to represent a variable
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .unwrap();

    let n = Expr::const_(Name::from_string("n"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);

    // LHS: Nat.add n Nat.zero
    let lhs = Expr::app(Expr::app(nat_add, n.clone()), nat_zero);

    // Build Eq Nat lhs n
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let goal = Expr::app(Expr::app(Expr::app(eq_const, nat_ty), lhs), n);

    let mut state = ProofState::new(env, goal);
    let squeeze_result = squeeze_simp(&mut state).expect("squeeze_simp should succeed");

    // Verify that Nat.add_zero was tracked as used
    assert!(
        squeeze_result
            .used_lemmas
            .iter()
            .any(|l| l.contains("add_zero")),
        "squeeze_simp should track Nat.add_zero as used lemma, got: {:?}",
        squeeze_result.used_lemmas
    );

    // Verify the suggested tactic includes the lemma
    assert!(
        squeeze_result.suggested_tactic.contains("add_zero"),
        "suggested_tactic should mention add_zero, got: {}",
        squeeze_result.suggested_tactic
    );

    // Verify the closed field is consistent: if closed is true, goals should be empty
    if squeeze_result.closed {
        assert!(
            state.goals().is_empty(),
            "squeeze_simp reports closed=true but goals remain"
        );
    }
}

/// Test that squeeze_simp returns empty used_lemmas when no simplification occurs.
///
/// This verifies that the lemma tracking is accurate - if no lemmas were applied,
/// used_lemmas should be empty.
#[test]
fn test_squeeze_simp_empty_when_no_simplification() {
    // Setup environment without arithmetic lemmas
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Add a simple proposition that simp can't simplify
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, p);

    let squeeze_result = squeeze_simp(&mut state).expect("squeeze_simp should succeed on P");

    // Should have empty used_lemmas or only beta/eta reductions (not named simp lemmas)
    let only_reduction_lemmas = squeeze_result
        .used_lemmas
        .iter()
        .all(|l| l == "beta" || l == "eta");
    assert!(
        squeeze_result.used_lemmas.is_empty() || only_reduction_lemmas,
        "Expected no named simp lemmas used (only beta/eta allowed), got: {:?}",
        squeeze_result.used_lemmas
    );

    // Suggested tactic should be "simp only []" or similar
    assert!(
        squeeze_result.suggested_tactic.starts_with("simp only ["),
        "Expected 'simp only [...]' format, got: {}",
        squeeze_result.suggested_tactic
    );

    // Verify closed field: P is not an equality, so goal cannot be closed by rfl
    assert!(
        !squeeze_result.closed,
        "Goal P should not be closable, closed = {}",
        squeeze_result.closed
    );
}
