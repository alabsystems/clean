// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic reasoning tactic tests: ring_nf, gcongr, convert.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

// =========================================================================
// ring_nf Tests
// =========================================================================

#[test]
fn test_ring_nf_fails_on_non_equality() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = ring_nf(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("equality")));
}

#[test]
fn test_ring_nf_normalizes_equality() {
    let mut env = setup_env_with_nat();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.init_eq().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            x.clone(),
        ),
        zero,
    );

    // x + 0 = x
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat.clone(),
            ),
            lhs,
        ),
        x.clone(),
    );
    let mut state = ProofState::new(env, eq_goal);

    ring_nf(&mut state).expect("ring_nf should succeed on equality");

    // Part of #2442: ring_nf may now close the goal directly via multi-step
    // proof (Eq.refl when sides are def-eq). Accept both behaviors:
    // - Direct closure (0 goals) = better, avoids trustedArith
    // - Normalized goal (1 goal) = original behavior, rfl closes it
    if state.goals.is_empty() {
        // ring_nf closed the goal directly via ring axiom proof
        assert!(
            state.is_complete(),
            "ring_nf should fully close the goal when sides are def-eq"
        );
    } else {
        assert_eq!(
            state.goals.len(),
            1,
            "ring_nf should produce exactly one normalized goal"
        );
        let target = &state.goals[0].target;
        let (ty, lhs, rhs, _) =
            match_equality(target).expect("normalized goal should still be an equality");
        assert_eq!(ty, nat, "normalized equality should be over Nat");
        assert_eq!(lhs, rhs, "normalized x + 0 = x should become x = x");
        rfl(&mut state).expect("rfl should close the normalized x = x goal");
        assert!(
            state.is_complete(),
            "ring_nf followed by rfl should complete"
        );
    }
    assert!(
        state.proof_term().is_some(),
        "ring_nf must keep MetaId(0) connected so proof extraction succeeds"
    );
    assert!(
        state.closed_proof().is_some(),
        "ring_nf must produce an extractable closed proof"
    );
}

#[test]
fn test_ring_expr_to_expr_const() {
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let re = RingExpr::Const(42);
    let expr = ring_expr_to_expr(&re, &mut state);
    assert_eq!(expr, Expr::nat_lit(42));
}

#[test]
fn test_ring_expr_to_expr_var() {
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let re = RingExpr::Var("x".to_string());
    let expr = ring_expr_to_expr(&re, &mut state);
    // "x" not in env, so falls back to vec![]
    assert_eq!(expr, Expr::const_(Name::from_string("x"), vec![]));
}

#[test]
fn test_ring_expr_to_expr_fvar() {
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let re = RingExpr::Var("fvar_42".to_string());
    let expr = ring_expr_to_expr(&re, &mut state);
    assert_eq!(expr, Expr::fvar(FVarId::new(42)));
}

// =========================================================================
// gcongr Tests
// =========================================================================

#[test]
fn test_gcongr_fails_on_non_inequality() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = gcongr(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_match_inequality_le() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let le_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("LE.le"), vec![]), x.clone()),
        y.clone(),
    );

    let result = match_inequality(&le_expr);
    let result = result.expect("expected Some");
    let (rel, _ty, _inst, lhs, rhs) = result;
    assert_eq!(rel, IneqRel::Le);
    assert_eq!(lhs, x);
    assert_eq!(rhs, y);
}

#[test]
fn test_match_inequality_lt() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let lt_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("LT.lt"), vec![]), x.clone()),
        y.clone(),
    );

    let result = match_inequality(&lt_expr);
    let result = result.expect("expected Some");
    let (rel, _ty, _inst, lhs, rhs) = result;
    assert_eq!(rel, IneqRel::Lt);
    assert_eq!(lhs, x);
    assert_eq!(rhs, y);
}

#[test]
fn test_make_ineq_goal() {
    let env = setup_env();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_inst = Expr::const_(Name::from_string("instLENat"), vec![]);
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let goal = make_ineq_goal(IneqRel::Le, &nat_ty, &nat_inst, &x, &y, &mut state);
    let result = match_inequality(&goal);
    let (rel, _ty, _inst, lhs, rhs) = result.expect("expected Some");
    assert_eq!(rel, IneqRel::Le);
    assert_eq!(lhs, x);
    assert_eq!(rhs, y);
}

#[test]
fn test_match_add_pattern() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // HAdd.hAdd a b
    let add_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("HAdd.hAdd"), vec![]),
            a.clone(),
        ),
        b.clone(),
    );

    let result = match_add(&add_expr);
    let result = result.expect("expected Some");
    let (lhs, rhs) = result;
    assert_eq!(lhs, a);
    assert_eq!(rhs, b);
}

// Part of #2075: regression tests for gcongr bug fixes

#[test]
fn test_match_add_rejects_substring_false_positives() {
    // Bug 4: contains("add") falsely matched "addr", "padding", etc.
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    for false_positive in ["addr", "padding", "ReadAddr", "Additive"] {
        let expr = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string(false_positive), vec![]),
                a.clone(),
            ),
            b.clone(),
        );
        assert!(
            match_add(&expr).is_none(),
            "match_add should reject {false_positive}"
        );
    }
}

#[test]
fn test_match_add_accepts_exact_names() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    for name in ["HAdd.hAdd", "Add.add", "Nat.add", "Int.add"] {
        let expr = Expr::app(
            Expr::app(Expr::const_(Name::from_string(name), vec![]), a.clone()),
            b.clone(),
        );
        let result = match_add(&expr);
        assert!(result.is_some(), "match_add should accept {name}");
        let (lhs, rhs) = result.unwrap();
        assert_eq!(lhs, a, "lhs mismatch for {name}");
        assert_eq!(rhs, b, "rhs mismatch for {name}");
    }
}

#[test]
fn test_match_inequality_4arg_extracts_type() {
    // Bug 2: match_inequality should extract type from fully-applied 4-arg form
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let int_inst = Expr::const_(Name::from_string("instLEInt"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Build @LE.le Int instLEInt x y (4 args)
    let le = Expr::const_(Name::from_string("LE.le"), vec![]);
    let expr = Expr::app(
        Expr::app(
            Expr::app(Expr::app(le, int_ty.clone()), int_inst.clone()),
            x.clone(),
        ),
        y.clone(),
    );

    let result = match_inequality(&expr).expect("should match 4-arg LE.le");
    let (rel, ty, inst, lhs, rhs) = result;
    assert_eq!(rel, IneqRel::Le);
    assert_eq!(ty, int_ty, "type should be Int, not Nat");
    assert_eq!(inst, int_inst, "instance should be instLEInt");
    assert_eq!(lhs, x);
    assert_eq!(rhs, y);
}

#[test]
fn test_match_inequality_ge_returns_le_instance() {
    // GE.ge uses an LE instance, not a GE instance
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let ge_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("GE.ge"), vec![]), x.clone()),
        y.clone(),
    );

    let result = match_inequality(&ge_expr).expect("should match GE.ge");
    let (rel, _ty, inst, _lhs, _rhs) = result;
    assert_eq!(rel, IneqRel::Ge);
    // GE.ge should produce an LE instance (instLENat for fallback)
    if let ExprKind::Const(name, _) = inst.kind() {
        assert_eq!(
            name.to_string(),
            "instLENat",
            "GE.ge should use LE instance"
        );
    } else {
        panic!("instance should be a Const");
    }
}

#[test]
fn test_gcongr_refl_errors_when_le_refl_missing() {
    // Reflexivity case should error when {Type}.le_refl is not in the environment,
    // rather than producing an ill-typed proof.
    let env = setup_env();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let int_inst = Expr::const_(Name::from_string("instLEInt"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);

    // Build goal: @LE.le Int instLEInt x x
    let le = Expr::const_(Name::from_string("LE.le"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::app(Expr::app(le, int_ty), int_inst), x.clone()),
        x,
    );

    let mut state = ProofState::new(env, target);
    let result = gcongr(&mut state);
    assert!(
        result.is_err(),
        "gcongr should error when Int.le_refl is missing"
    );
    let err = result.unwrap_err();
    assert!(
        matches!(err, TacticError::EnvironmentMissing { ref constant } if constant == "Int.le_refl"),
        "error should be EnvironmentMissing for Int.le_refl, got: {err:?}"
    );
}

#[test]
fn test_gcongr_refl_nat_succeeds_with_le_refl() {
    // Part of #2075: generic reflexivity via {Type}.le_refl lookup.
    // Nat.le_refl type-checks against the LE.le goal form (uses nat_le_tc
    // for correct universe levels, matching the axiom declaration).
    let mut env = Environment::with_prelude();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .unwrap();
    let x = Expr::const_(Name::from_string("x"), vec![]);

    // Build goal: @LE.le.{0} Nat instLENat x x (using nat_le_tc for correct form)
    let target = make_nat_le_tc(x.clone(), x.clone());

    let mut state = ProofState::new(env, target);
    let result = gcongr(&mut state);
    assert!(
        result.is_ok(),
        "gcongr reflexivity should succeed for Nat: {:?}",
        result.unwrap_err()
    );
    assert_eq!(state.goals.len(), 0, "reflexivity should close all goals");
}

#[test]
fn test_match_inequality_gt_returns_lt_instance() {
    // GT.gt uses an LT instance, not a GT instance
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let gt_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("GT.gt"), vec![]), x.clone()),
        y.clone(),
    );

    let result = match_inequality(&gt_expr).expect("should match GT.gt");
    let (rel, _ty, inst, _lhs, _rhs) = result;
    assert_eq!(rel, IneqRel::Gt);
    if let ExprKind::Const(name, _) = inst.kind() {
        assert_eq!(
            name.to_string(),
            "instLTNat",
            "GT.gt should use LT instance"
        );
    } else {
        panic!("instance should be a Const");
    }
}

#[test]
fn test_gcongr_addition_decomposition_creates_subgoals() {
    // Part of #2075: monotonic addition decomposition should create 2 subgoals
    // for a+b <= c+d and close the original goal
    let mut env = Environment::with_prelude(); // Includes init_nat_add_ord

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    // Declare a, b, c, d as Nat constants
    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    // Build goal: @LE.le.{0} Nat instLENat (Nat.add a b) (Nat.add c d)
    // Uses make_nat_le_tc for correct universe levels matching axiom declarations.
    let add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let lhs_add = Expr::app(Expr::app(add.clone(), a.clone()), b.clone());
    let rhs_add = Expr::app(Expr::app(add, c.clone()), d.clone());
    let target = make_nat_le_tc(lhs_add, rhs_add);

    let mut state = ProofState::new(env, target);
    let result = gcongr(&mut state);
    assert!(
        result.is_ok(),
        "gcongr should decompose addition: {:?}",
        result.unwrap_err()
    );

    // Should produce exactly 2 subgoals: a <= c and b <= d
    assert_eq!(
        state.goals.len(),
        2,
        "addition decomposition should create 2 subgoals, got {}",
        state.goals.len()
    );
}

#[test]
fn test_make_ineq_goal_roundtrips_all_relations() {
    // Well-typedness: make_ineq_goal output is parseable by match_inequality
    // for all 4 relation types
    let env = setup_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_le_inst = Expr::const_(Name::from_string("instLENat"), vec![]);
    let nat_lt_inst = Expr::const_(Name::from_string("instLTNat"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    for (rel, inst, expected_rel) in [
        (IneqRel::Le, &nat_le_inst, IneqRel::Le),
        (IneqRel::Lt, &nat_lt_inst, IneqRel::Lt),
        (IneqRel::Ge, &nat_le_inst, IneqRel::Ge),
        (IneqRel::Gt, &nat_lt_inst, IneqRel::Gt),
    ] {
        let goal_expr = make_ineq_goal(rel, &nat_ty, inst, &x, &y, &mut state);
        let parsed =
            match_inequality(&goal_expr).unwrap_or_else(|| panic!("failed to parse {rel:?}"));
        assert_eq!(
            parsed.0, expected_rel,
            "round-trip relation mismatch for {rel:?}"
        );
        assert_eq!(parsed.3, x, "lhs mismatch for {rel:?}");
        assert_eq!(parsed.4, y, "rhs mismatch for {rel:?}");
    }
}

// =========================================================================
// convert Tests
// =========================================================================

#[test]
fn test_convert_exact_match() {
    let env = setup_env();
    let a_type = Expr::const_(Name::from_string("A"), vec![]);
    let a_proof = Expr::const_(Name::from_string("a"), vec![]);
    let mut state = ProofState::new(env, a_type);

    convert(&mut state, a_proof).expect("convert with exact type match should succeed");
    assert_eq!(state.goals.len(), 0);
}

#[test]
fn test_convert_creates_subgoals_for_mismatch() {
    let mut env = setup_env();
    // Strategy 2 requires Eq.mpr for the type-cast proof term
    env.init_eq().unwrap();
    let b_type = Expr::const_(Name::from_string("B"), vec![]);

    // Goal is A, proof is of type B - should create subgoal to prove A = B
    // Add b : B to environment
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: b_type,
    })
    .unwrap();
    let b_proof = Expr::const_(Name::from_string("b"), vec![]);

    let mut state = ProofState::new(env, Expr::const_(Name::from_string("A"), vec![]));
    // convert creates a subgoal to prove A = B (type equality) when types mismatch
    convert(&mut state, b_proof).expect("convert should succeed and create type equality subgoal");
    assert_eq!(
        state.goals().len(),
        1,
        "convert should create exactly one subgoal for A = B"
    );
}

#[test]
fn test_convert_hyp_not_found() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = convert_hyp(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"));
}

// =========================================================================
// gcongr multiplication monotonicity Tests (elab-gcongr-mul)
// =========================================================================

/// Build a Nat environment with a..d declared as Nat axioms.
fn nat_env_with_abcd() -> Environment {
    let mut env = Environment::with_prelude();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty.clone(),
        })
        .unwrap();
    }
    env
}

fn nat_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_mul(x: Expr, y: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mul"), vec![]), x),
        y,
    )
}

#[test]
fn test_match_mul_accepts_exact_names() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    for name in ["HMul.hMul", "Mul.mul", "Nat.mul", "Int.mul"] {
        let expr = Expr::app(
            Expr::app(Expr::const_(Name::from_string(name), vec![]), a.clone()),
            b.clone(),
        );
        let result = match_mul(&expr);
        assert!(result.is_some(), "match_mul should accept {name}");
        let (lhs, rhs) = result.unwrap();
        assert_eq!(lhs, a, "lhs mismatch for {name}");
        assert_eq!(rhs, b, "rhs mismatch for {name}");
    }
}

#[test]
fn test_match_mul_rejects_substring_false_positives() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    for false_positive in ["mult", "Multiset", "cumulative", "Nat.muldiv"] {
        let expr = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string(false_positive), vec![]),
                a.clone(),
            ),
            b.clone(),
        );
        assert!(
            match_mul(&expr).is_none(),
            "match_mul should reject {false_positive}"
        );
    }
}

#[test]
fn test_gcongr_nat_mul_two_sided_creates_two_subgoals() {
    // a*c <= b*d from a<=b, c<=d should decompose into exactly two subgoals.
    let env = nat_env_with_abcd();
    let target = make_nat_le_tc(
        nat_mul(nat_const("a"), nat_const("c")),
        nat_mul(nat_const("b"), nat_const("d")),
    );
    let mut state = ProofState::new(env, target);

    let result = gcongr(&mut state);
    assert!(
        result.is_ok(),
        "gcongr should decompose a*c <= b*d: {:?}",
        result.unwrap_err()
    );
    assert_eq!(
        state.goals.len(),
        2,
        "two-sided mul decomposition should create 2 subgoals, got {}",
        state.goals.len()
    );
    // Subgoal 1 should be a <= b, subgoal 2 should be c <= d.
    let (_, _, _, l1, r1) =
        match_inequality(&state.goals[0].target).expect("subgoal 1 should be an inequality");
    assert_eq!(l1, nat_const("a"), "subgoal 1 lhs should be a");
    assert_eq!(r1, nat_const("b"), "subgoal 1 rhs should be b");
    let (_, _, _, l2, r2) =
        match_inequality(&state.goals[1].target).expect("subgoal 2 should be an inequality");
    assert_eq!(l2, nat_const("c"), "subgoal 2 lhs should be c");
    assert_eq!(r2, nat_const("d"), "subgoal 2 rhs should be d");
}

#[test]
fn test_gcongr_nat_mul_left_one_sided_creates_single_subgoal() {
    // c*a <= c*b (shared left factor c) should use Nat.mul_le_mul_left and
    // produce exactly ONE subgoal: a <= b.
    let env = nat_env_with_abcd();
    let target = make_nat_le_tc(
        nat_mul(nat_const("c"), nat_const("a")),
        nat_mul(nat_const("c"), nat_const("b")),
    );
    let mut state = ProofState::new(env, target);

    let result = gcongr(&mut state);
    assert!(
        result.is_ok(),
        "gcongr should decompose c*a <= c*b: {:?}",
        result.unwrap_err()
    );
    assert_eq!(
        state.goals.len(),
        1,
        "one-sided (shared left) mul should create 1 subgoal, got {}",
        state.goals.len()
    );
    let (_, _, _, lhs, rhs) =
        match_inequality(&state.goals[0].target).expect("subgoal should be an inequality");
    assert_eq!(lhs, nat_const("a"), "subgoal lhs should be a");
    assert_eq!(rhs, nat_const("b"), "subgoal rhs should be b");
}

#[test]
fn test_gcongr_nat_mul_right_one_sided_creates_single_subgoal() {
    // a*c <= b*c (shared right factor c) should use Nat.mul_le_mul_right and
    // produce exactly ONE subgoal: a <= b.
    let env = nat_env_with_abcd();
    let target = make_nat_le_tc(
        nat_mul(nat_const("a"), nat_const("c")),
        nat_mul(nat_const("b"), nat_const("c")),
    );
    let mut state = ProofState::new(env, target);

    let result = gcongr(&mut state);
    assert!(
        result.is_ok(),
        "gcongr should decompose a*c <= b*c: {:?}",
        result.unwrap_err()
    );
    assert_eq!(
        state.goals.len(),
        1,
        "one-sided (shared right) mul should create 1 subgoal, got {}",
        state.goals.len()
    );
    let (_, _, _, lhs, rhs) =
        match_inequality(&state.goals[0].target).expect("subgoal should be an inequality");
    assert_eq!(lhs, nat_const("a"), "subgoal lhs should be a");
    assert_eq!(rhs, nat_const("b"), "subgoal rhs should be b");
}

#[test]
fn test_gcongr_int_mul_left_nonneg_creates_mono_and_nonneg_subgoals() {
    // Int shared-left-factor case c*a <= c*b discharges via
    // Int.mul_le_mul_of_nonneg_left, producing the monotonicity subgoal a<=b
    // AND the nonneg side condition 0<=c.
    let mut env = setup_env_with_int_ord();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["x", "y", "z"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap();
    }
    let int_inst = Expr::const_(Name::from_string("instLEInt"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let int_mul = |a: Expr, b: Expr| {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Int.mul"), vec![]), a),
            b,
        )
    };
    let mut builder = ProofState::new(env.clone(), Expr::prop());
    // Goal: z*x <= z*y
    let target = make_ineq_goal(
        IneqRel::Le,
        &int_ty,
        &int_inst,
        &int_mul(z.clone(), x.clone()),
        &int_mul(z.clone(), y.clone()),
        &mut builder,
    );
    let mut state = ProofState::new(env, target);

    let result = gcongr(&mut state);
    assert!(
        result.is_ok(),
        "gcongr should decompose Int z*x <= z*y: {:?}",
        result.unwrap_err()
    );
    assert_eq!(
        state.goals.len(),
        2,
        "Int shared-left mul should create mono + nonneg subgoals, got {}",
        state.goals.len()
    );
    // First subgoal: x <= y (monotonicity premise).
    let (_, _, _, l1, r1) =
        match_inequality(&state.goals[0].target).expect("mono subgoal should be an inequality");
    assert_eq!(l1, x, "mono subgoal lhs should be x");
    assert_eq!(r1, y, "mono subgoal rhs should be y");
    // Second subgoal: 0 <= z (nonneg side condition).
    let (_, _, _, l2, r2) =
        match_inequality(&state.goals[1].target).expect("nonneg subgoal should be an inequality");
    assert_eq!(r2, z, "nonneg subgoal rhs should be z");
    // lhs is Int.ofNat Nat.zero.
    let expected_zero = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    assert_eq!(l2, expected_zero, "nonneg subgoal lhs should be 0");
}

#[test]
fn test_gcongr_int_mul_no_shared_factor_leaves_goal() {
    // Int two-sided x*a <= y*b (no shared factor) is NOT sound via the
    // one-sided nonneg lemma alone, so gcongr should leave the goal (error).
    let mut env = setup_env_with_int_ord();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["x", "y", "a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap();
    }
    let int_inst = Expr::const_(Name::from_string("instLEInt"), vec![]);
    let int_mul = |p: &str, q: &str| {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Int.mul"), vec![]),
                Expr::const_(Name::from_string(p), vec![]),
            ),
            Expr::const_(Name::from_string(q), vec![]),
        )
    };
    let mut builder = ProofState::new(env.clone(), Expr::prop());
    let target = make_ineq_goal(
        IneqRel::Le,
        &int_ty,
        &int_inst,
        &int_mul("x", "a"),
        &int_mul("y", "b"),
        &mut builder,
    );
    let mut state = ProofState::new(env, target);

    let result = gcongr(&mut state);
    assert!(
        result.is_err(),
        "gcongr should leave Int x*a <= y*b (no shared factor) unsolved"
    );
    assert_eq!(
        state.goals.len(),
        1,
        "the original goal should remain untouched"
    );
}

#[test]
fn test_gcongr_nat_mul_missing_hyp_shape_still_decomposes() {
    // gcongr does NOT need hypotheses in context to decompose; it produces the
    // subgoals. But a goal whose head is NOT a recognized op (e.g. f a <= f b
    // with unknown f and differing args) must NOT close via mul and should
    // report SearchExhausted, leaving the goal.
    let mut env = Environment::with_prelude();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_nat = Expr::arrow(nat_ty.clone(), nat_ty.clone());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: nat_to_nat,
    })
    .unwrap();
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty.clone(),
        })
        .unwrap();
    }
    let g_a = Expr::app(nat_const("g"), nat_const("a"));
    let g_b = Expr::app(nat_const("g"), nat_const("b"));
    let target = make_nat_le_tc(g_a, g_b);
    let mut state = ProofState::new(env, target);

    let result = gcongr(&mut state);
    assert!(
        result.is_err(),
        "gcongr should not close g a <= g b without a monotonicity rule"
    );
    assert_eq!(state.goals.len(), 1, "the goal should remain");
}
