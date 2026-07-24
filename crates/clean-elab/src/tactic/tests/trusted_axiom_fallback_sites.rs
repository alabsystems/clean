// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-chain regressions for trusted fallback and proof-carry tactic rewrites.
//! #2516 cast-normalization cases must stay trust-free or fail closed.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn assert_zero_trusted_fallback_exact<F>(
    mut state: ProofState,
    tactic_name: &str,
    proof: Expr,
    tactic: F,
) where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{tactic_name} state should start with no trusted axioms"
    );

    tactic(&mut state).unwrap_or_else(|err| panic!("{tactic_name} should succeed: {err:?}"));
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{tactic_name} should not record any trusted fallback"
    );

    exact(&mut state, proof)
        .unwrap_or_else(|err| panic!("exact should close the {tactic_name} goal: {err:?}"));
    assert!(state.is_complete(), "{tactic_name} proof should complete");
    assert!(
        state.proof_term().is_some(),
        "{tactic_name} must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "{tactic_name} must preserve closed_proof() extraction"
    );
}

fn assert_no_progress_without_trust<F>(mut state: ProofState, tactic_name: &str, tactic: F)
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    let original_target = state
        .current_goal()
        .expect("no-progress tests require an active goal")
        .target
        .clone();

    let result = tactic(&mut state);
    assert!(
        matches!(result, Err(TacticError::NoProgress { .. })),
        "{tactic_name} should fail closed with NoProgress, got {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{tactic_name} should not record trusted fallback on unsupported shapes"
    );
    assert_eq!(
        state
            .current_goal()
            .expect("goal should remain open")
            .target,
        original_target,
        "{tactic_name} should leave the original target unchanged on NoProgress"
    );
}

fn setup_cast_proof_env() -> Environment {
    let mut env = Environment::new();
    env.init_cast_simp_lemmas().unwrap();
    env
}

fn add_typed_axioms(env: &mut Environment, names: &[&str], type_: Expr) {
    for name in names {
        add_axiom(env, name, type_.clone());
    }
}

fn app2(name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(name), vec![]), lhs),
        rhs,
    )
}

fn int_of_nat(expr: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), expr)
}

fn rat_of_int(expr: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Rat.ofInt"), vec![]), expr)
}

#[test]
#[serial]
fn test_push_neg_double_negation_stays_trust_free() {
    let mut env = setup_env_with_prop_ext();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "p", prop_p.clone());

    let goal = make_not(&make_not(&prop_p));
    assert_zero_trusted_fallback_exact(
        ProofState::new(env, goal),
        "push_neg",
        Expr::const_(Name::from_string("p"), vec![]),
        push_neg,
    );
}

#[test]
#[serial]
fn test_contrapose_stays_trust_free() {
    let mut env = setup_env_with_prop_ext();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());
    add_axiom(
        &mut env,
        "hcontra",
        Expr::arrow(make_not(&prop_q), make_not(&prop_p)),
    );

    assert_zero_trusted_fallback_exact(
        ProofState::new(env, Expr::arrow(prop_p, prop_q)),
        "contrapose",
        Expr::const_(Name::from_string("hcontra"), vec![]),
        contrapose,
    );
}

#[test]
#[serial]
fn test_contrapose_hyp_uses_local_proof_carry_without_trust() {
    reset_all_counters();
    let mut env = setup_env_with_prop_ext();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());

    let initial_target = prop_p.clone();
    let axiom_before = axiom_snapshot();
    let goal = Expr::pi(
        BinderInfo::Default,
        Expr::arrow(prop_p.clone(), prop_q.clone()),
        Expr::pi(BinderInfo::Default, prop_p.clone(), initial_target.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create h");
    intro(&mut state, "hp").expect("intro should create hp");
    let goal = state.current_goal().expect("goal should exist after intro");
    let old_h_fvar = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .map(|decl| decl.fvar)
        .expect("h should exist after intro");
    let hp_fvar = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "hp")
        .map(|decl| decl.fvar)
        .expect("hp should exist after intro");

    contrapose_hyp(&mut state, "h").expect("contrapose_hyp should rewrite through proof carry");

    let goal = state.current_goal().expect("goal should remain open");
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("rewritten hypothesis should remain visible");
    assert_ne!(h.fvar, old_h_fvar, "replacement must allocate a fresh fvar");
    assert_eq!(
        h.ty,
        Expr::arrow(
            make_not(&prop_q),
            Expr::arrow(
                prop_p.clone(),
                Expr::const_(Name::from_string("False"), vec![])
            ),
        )
    );
    assert_eq!(
        goal.target, initial_target,
        "contrapose_hyp should not rewrite the target"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "contrapose_hyp should not record any trusted fallback"
    );
    assert_no_trusted_axiom_usage("contrapose h", "hypothesis rewrite", axiom_before);

    exact(&mut state, Expr::fvar(hp_fvar)).expect("hp should close the unchanged goal");
    assert!(state.is_complete(), "contrapose_hyp proof should complete");
    assert!(
        state.proof_term().is_some(),
        "contrapose_hyp must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "contrapose_hyp must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_push_cast_nat_add_goal_rewrites_without_trust() {
    let mut env = setup_cast_proof_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    add_typed_axioms(&mut env, &["m", "n"], nat.clone());
    add_typed_axioms(&mut env, &["z"], int.clone());

    let m = Expr::const_(Name::from_string("m"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let goal = make_eq(
        int.clone(),
        int_of_nat(app2("Nat.add", m.clone(), n.clone())),
        z.clone(),
    );
    let expected_target = make_eq(
        int.clone(),
        app2("Int.add", int_of_nat(m.clone()), int_of_nat(n.clone())),
        z,
    );
    add_axiom(&mut env, "hpushed", expected_target);

    assert_zero_trusted_fallback_exact(
        ProofState::new(env, goal),
        "push_cast",
        Expr::const_(Name::from_string("hpushed"), vec![]),
        push_cast,
    );
}

fn field_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Div.div"), vec![]), lhs),
        rhs,
    )
}

fn field_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Mul.mul"), vec![]), lhs),
        rhs,
    )
}

fn field_ne_zero(carrier: &Expr, value: Expr, zero: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                carrier.clone(),
            ),
            value,
        ),
        zero.clone(),
    )
}

fn field_iff(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), lhs),
        rhs,
    )
}

fn add_field_simp_theorems(
    env: &mut Environment,
    carrier: &Expr,
    zero: &Expr,
    vars: &[(&str, Expr)],
) {
    let lookup = |name: &str| {
        vars.iter()
            .find(|(var_name, _)| *var_name == name)
            .map(|(_, expr)| expr.clone())
            .expect("requested field_simp theorem variable must exist")
    };

    let a = lookup("a");
    let b = lookup("b");
    let c = lookup("c");
    let d = lookup("d");
    let x = lookup("x");
    let y = lookup("y");
    let z = lookup("z");

    add_axiom(
        env,
        "div_eq_iff",
        Expr::arrow(
            field_ne_zero(carrier, y.clone(), zero),
            field_iff(
                make_eq(carrier.clone(), field_div(x.clone(), y.clone()), z.clone()),
                make_eq(carrier.clone(), x, field_mul(z, y)),
            ),
        ),
    );
    add_axiom(
        env,
        "eq_div_iff_mul_eq",
        Expr::arrow(
            field_ne_zero(carrier, d.clone(), zero),
            field_iff(
                make_eq(carrier.clone(), a.clone(), field_div(c.clone(), d.clone())),
                make_eq(carrier.clone(), field_mul(a.clone(), d.clone()), c.clone()),
            ),
        ),
    );
    add_axiom(
        env,
        "div_eq_div_iff",
        Expr::arrow(
            field_ne_zero(carrier, b.clone(), zero),
            Expr::arrow(
                field_ne_zero(carrier, d.clone(), zero),
                field_iff(
                    make_eq(
                        carrier.clone(),
                        field_div(a.clone(), b.clone()),
                        field_div(c.clone(), d.clone()),
                    ),
                    make_eq(carrier.clone(), field_mul(a, d), field_mul(c, b)),
                ),
            ),
        ),
    );
}

/// Build a test environment with field-style division/multiplication theorems.
/// Used by field_simp proof-carry regressions (#1143).
fn make_field_simp_test_env(
    var_names: &[&str],
    include_propext: bool,
    include_theorems: bool,
) -> (Environment, Expr, Expr) {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_iff().unwrap();
    if include_propext {
        env.init_propext().unwrap();
    }

    let carrier = Expr::const_(Name::from_string("Carrier"), vec![]);
    add_axiom(&mut env, "Carrier", Expr::type_());
    let zero = Expr::const_(Name::from_string("zero"), vec![]);
    add_axiom(&mut env, "zero", carrier.clone());

    let default_names = ["a", "b", "c", "d", "x", "y", "z"];
    let mut vars = Vec::new();
    for name in default_names {
        add_axiom(&mut env, name, carrier.clone());
        vars.push((name, Expr::const_(Name::from_string(name), vec![])));
    }
    for name in var_names {
        if !default_names.contains(name) {
            add_axiom(&mut env, name, carrier.clone());
            vars.push((*name, Expr::const_(Name::from_string(name), vec![])));
        }
    }
    let binop = Expr::arrow(
        carrier.clone(),
        Expr::arrow(carrier.clone(), carrier.clone()),
    );
    add_axiom(&mut env, "Div.div", binop.clone());
    add_axiom(&mut env, "Mul.mul", binop);
    if include_theorems {
        add_field_simp_theorems(&mut env, &carrier, &zero, &vars);
    }
    (env, carrier, zero)
}

/// Regression: field_simp cross-multiplies `x/y = z` with one side goal (#1143).
#[test]
#[serial]
fn test_field_simp_cross_multiplies_with_side_goals() {
    let (env, carrier, zero) = make_field_simp_test_env(&["x", "y", "z"], true, true);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    reset_all_counters();
    let mut state = ProofState::new(
        env,
        make_eq(carrier.clone(), field_div(x.clone(), y.clone()), z.clone()),
    );

    let result = field_simp(&mut state);
    assert!(result.is_ok(), "field_simp should succeed: {result:?}");
    assert_eq!(state.trusted_axiom_count(), 0, "expected 0 trusted axioms");
    assert!(!state.goals.is_empty(), "should leave open goals");

    let ne_goals: Vec<_> = state
        .goals
        .iter()
        .filter(|g| g.tag.as_deref() == Some("field_simp:ne_zero"))
        .collect();
    assert_eq!(ne_goals.len(), 1, "expected exactly one non-zero side goal");
    assert_eq!(
        ne_goals[0].target,
        field_ne_zero(&carrier, y, &zero),
        "field_simp should preserve the theorem-generated denominator premise"
    );
}

/// Regression: field_simp on `a = c/d` preserves one visible non-zero side goal (#1143).
#[test]
#[serial]
fn test_field_simp_rhs_division_preserves_single_side_goal() {
    let (env, carrier, zero) = make_field_simp_test_env(&["a", "c", "d"], true, true);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    reset_all_counters();
    let mut state = ProofState::new(
        env,
        make_eq(carrier.clone(), a.clone(), field_div(c.clone(), d.clone())),
    );

    let result = field_simp(&mut state);
    assert!(
        result.is_ok(),
        "field_simp on a = c/d should succeed: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "field_simp on a = c/d should not record trusted fallback"
    );

    let ne_goals: Vec<_> = state
        .goals
        .iter()
        .filter(|g| g.tag.as_deref() == Some("field_simp:ne_zero"))
        .collect();
    assert_eq!(
        ne_goals.len(),
        1,
        "field_simp on a = c/d should produce exactly one non-zero side goal"
    );
    assert_eq!(
        ne_goals[0].target,
        field_ne_zero(&carrier, d, &zero),
        "right denominator premise should remain visible"
    );

    let visible_open_meta_ids: std::collections::HashSet<_> =
        state.goals.iter().map(|goal| goal.meta_id).collect();
    let unassigned_meta_ids: std::collections::HashSet<_> =
        state.metas().unassigned().into_iter().collect();
    assert_eq!(
        unassigned_meta_ids, visible_open_meta_ids,
        "field_simp should not leave hidden unassigned metas on the rhs-only rewrite path"
    );
}

/// Regression: field_simp on `a/b = c/d` produces two non-zero side goals (#1143).
#[test]
#[serial]
fn test_field_simp_both_sides_denominator_two_side_goals() {
    let (env, carrier, zero) = make_field_simp_test_env(&["a", "b", "c", "d"], true, true);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    reset_all_counters();
    let mut state = ProofState::new(
        env,
        make_eq(
            carrier.clone(),
            field_div(a.clone(), b.clone()),
            field_div(c.clone(), d.clone()),
        ),
    );

    let result = field_simp(&mut state);
    assert!(
        result.is_ok(),
        "field_simp on a/b = c/d should succeed: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "field_simp on a/b = c/d should not record trusted fallback"
    );

    let ne_goals: Vec<_> = state
        .goals
        .iter()
        .filter(|g| g.tag.as_deref() == Some("field_simp:ne_zero"))
        .collect();
    assert_eq!(
        ne_goals.len(),
        2,
        "field_simp on a/b = c/d should produce exactly 2 non-zero side goals"
    );
    assert_eq!(
        ne_goals[0].target,
        field_ne_zero(&carrier, b, &zero),
        "left denominator premise should remain first"
    );
    assert_eq!(
        ne_goals[1].target,
        field_ne_zero(&carrier, d, &zero),
        "right denominator premise should remain second"
    );

    let visible_open_meta_ids: std::collections::HashSet<_> =
        state.goals.iter().map(|goal| goal.meta_id).collect();
    let unassigned_meta_ids: std::collections::HashSet<_> =
        state.metas().unassigned().into_iter().collect();
    assert_eq!(
        unassigned_meta_ids, visible_open_meta_ids,
        "field_simp should not leave hidden unassigned metas after the theorem-backed rewrite"
    );
}

/// Positive regression: field_simp on denominator-free equality delegates to ring.
#[test]
#[serial]
fn test_field_simp_no_denominator_delegates_to_ring() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: Nat.zero = Nat.zero  (no denominators, ring closes via rfl)
    let mut state = ProofState::new(env, make_eq(nat, zero.clone(), zero));

    reset_all_counters();
    let result = field_simp(&mut state);
    assert!(
        result.is_ok(),
        "field_simp on denominator-free equality should succeed via ring: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "no-denominator field_simp should not introduce trusted axioms"
    );
}

#[test]
#[serial]
fn test_field_simp_missing_propext_fails_without_trust_or_target_mutation() {
    let (env, carrier, _zero) = make_field_simp_test_env(&["x", "y", "z"], false, true);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let original_target = make_eq(carrier.clone(), field_div(x, y), z);

    reset_all_counters();
    let mut state = ProofState::new(env, original_target.clone());
    let result = field_simp(&mut state);

    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "propext"),
        "expected missing propext, got {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "missing propext should not record trusted fallback"
    );
    assert_eq!(
        state
            .current_goal()
            .expect("goal should remain open")
            .target,
        original_target,
        "missing propext should leave the target unchanged"
    );
}

#[test]
#[serial]
fn test_field_simp_missing_rewrite_theorem_fails_without_trust_or_target_mutation() {
    let (env, carrier, _zero) = make_field_simp_test_env(&["x", "y", "z"], true, false);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let original_target = make_eq(carrier.clone(), field_div(x, y), z);

    reset_all_counters();
    let mut state = ProofState::new(env, original_target.clone());
    let result = field_simp(&mut state);

    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "div_eq_iff"),
        "expected missing div_eq_iff, got {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "missing theorem should not record trusted fallback"
    );
    assert_eq!(
        state
            .current_goal()
            .expect("goal should remain open")
            .target,
        original_target,
        "missing theorem should leave the target unchanged"
    );
}

#[test]
#[serial]
fn test_norm_cast_equality_branch_rewrites_without_trust() {
    let mut env = setup_cast_proof_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    add_typed_axioms(&mut env, &["m", "n"], nat.clone());
    add_typed_axioms(&mut env, &["z"], int.clone());

    let m = Expr::const_(Name::from_string("m"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let goal = make_eq(
        int.clone(),
        int_of_nat(app2("Nat.add", m.clone(), n.clone())),
        z.clone(),
    );
    let expected_target = make_eq(
        int.clone(),
        app2("Int.add", int_of_nat(m.clone()), int_of_nat(n.clone())),
        z,
    );
    add_axiom(&mut env, "hnorm_eq", expected_target);

    assert_zero_trusted_fallback_exact(
        ProofState::new(env, goal),
        "norm_cast equality branch",
        Expr::const_(Name::from_string("hnorm_eq"), vec![]),
        norm_cast,
    );
}

#[test]
#[serial]
fn test_norm_cast_proposition_branch_rewrites_without_trust() {
    let mut env = setup_cast_proof_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    add_typed_axioms(&mut env, &["m", "n", "k"], nat.clone());

    let m = Expr::const_(Name::from_string("m"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let k = Expr::const_(Name::from_string("k"), vec![]);
    let goal = make_eq(
        nat.clone(),
        app2("Nat.add", m.clone(), n.clone()),
        k.clone(),
    );
    let expected_target = make_eq(
        int.clone(),
        app2("Int.add", int_of_nat(m.clone()), int_of_nat(n.clone())),
        int_of_nat(k),
    );
    add_axiom(&mut env, "hnorm_prop", expected_target);

    assert_zero_trusted_fallback_exact(
        ProofState::new(env, goal),
        "norm_cast proposition branch",
        Expr::const_(Name::from_string("hnorm_prop"), vec![]),
        norm_cast,
    );
}

#[test]
#[serial]
fn test_zify_nat_le_goal_rewrites_without_trust() {
    let mut env = setup_cast_proof_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    add_typed_axioms(&mut env, &["m", "n"], nat);

    let m = Expr::const_(Name::from_string("m"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let goal = app2("Nat.le", m.clone(), n.clone());
    let expected_target = app2("Int.le", int_of_nat(m), int_of_nat(n));
    add_axiom(&mut env, "hzified", expected_target);

    assert_zero_trusted_fallback_exact(
        ProofState::new(env, goal),
        "zify",
        Expr::const_(Name::from_string("hzified"), vec![]),
        zify,
    );
}

#[test]
#[serial]
fn test_zify_nat_lt_goal_rewrites_without_trust() {
    let mut env = setup_cast_proof_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    add_typed_axioms(&mut env, &["m", "n"], nat);

    let m = Expr::const_(Name::from_string("m"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let goal = app2("Nat.lt", m.clone(), n.clone());
    let expected_target = app2("Int.lt", int_of_nat(m), int_of_nat(n));
    add_axiom(&mut env, "hzified_lt", expected_target);

    assert_zero_trusted_fallback_exact(
        ProofState::new(env, goal),
        "zify lt",
        Expr::const_(Name::from_string("hzified_lt"), vec![]),
        zify,
    );
}

#[test]
#[serial]
fn test_zify_nat_sub_goal_fails_closed_without_trust() {
    let mut env = setup_cast_proof_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    add_typed_axioms(&mut env, &["m", "n", "k"], nat.clone());

    let m = Expr::const_(Name::from_string("m"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let k = Expr::const_(Name::from_string("k"), vec![]);
    let goal = make_eq(nat, app2("Nat.sub", m, n), k);

    assert_no_progress_without_trust(ProofState::new(env, goal), "zify", zify);
}

#[test]
#[serial]
fn test_qify_int_lt_goal_rewrites_without_trust() {
    let mut env = setup_cast_proof_env();
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    add_typed_axioms(&mut env, &["i", "j"], int);

    let i = Expr::const_(Name::from_string("i"), vec![]);
    let j = Expr::const_(Name::from_string("j"), vec![]);
    let goal = app2("Int.lt", i.clone(), j.clone());
    let expected_target = app2("Rat.lt", rat_of_int(i), rat_of_int(j));
    add_axiom(&mut env, "hqified", expected_target);

    assert_zero_trusted_fallback_exact(
        ProofState::new(env, goal),
        "qify",
        Expr::const_(Name::from_string("hqified"), vec![]),
        qify,
    );
}

#[test]
#[serial]
fn test_qify_int_div_goal_fails_closed_without_trust() {
    let mut env = setup_cast_proof_env();
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    add_typed_axioms(&mut env, &["i", "j", "k"], int.clone());

    let i = Expr::const_(Name::from_string("i"), vec![]);
    let j = Expr::const_(Name::from_string("j"), vec![]);
    let k = Expr::const_(Name::from_string("k"), vec![]);
    let goal = make_eq(int, app2("Int.div", i, j), k);

    assert_no_progress_without_trust(ProofState::new(env, goal), "qify", qify);
}

/// Verify create_trusted_arith_term (the helper ring.rs now delegates to)
/// increments the global arith counter and produces a trustedArith-headed term.
/// Part of #2487.
///
/// ring_nf's internal ring_expr_to_expr uses HAdd.hAdd / instHAddNat which
/// require the full algebra stack not available in unit-test environments.
/// Testing create_trusted_arith_term directly exercises the exact code path
/// that ring.rs delegates to after the #2487 refactor.
#[test]
#[serial]
fn test_trusted_axiom_count_tracks_ring_nf_fallback() {
    use crate::tactic::arith_linarith::{
        create_trusted_arith_term, enable_arith_location_tracking,
    };

    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_trusted_arith().unwrap();

    let old_target = Expr::const_(Name::from_string("True"), vec![]);
    let new_target = Expr::const_(Name::from_string("True"), vec![]);
    let eq_ty = make_eq(Expr::prop(), old_target, new_target);

    let axiom_before = axiom_snapshot();
    enable_arith_location_tracking();
    let direct_before = direct_arith_file_count(file!());
    let proof = create_trusted_arith_term(&env, &eq_ty);
    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        1,
        "create_trusted_arith_term should increment arith_proof_count exactly once"
    );
    assert_eq!(
        direct_arith_file_count(file!()),
        direct_before + 1,
        "direct trustedArith emission should keep the caller file:line key"
    );

    // The proof term should be headed by the trustedArith constant.
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == "trustedArith"),
        "create_trusted_arith_term should produce a trustedArith-headed term"
    );
}

/// Verify the shared replace-target fallback increments both counters after the
/// #2495 move into tactic core. Part of #2487.
///
/// Exercise the core helper directly with a non-definitional target rewrite so
/// the test stays focused on shared fallback accounting rather than the broader
/// `simp` rewrite engine.
#[test]
#[serial]
fn test_trusted_axiom_count_tracks_simp_target_replacement_fallback() {
    use crate::tactic::arith_linarith::enable_arith_location_tracking;

    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());

    let mut state = ProofState::new(env, prop_p);
    assert_eq!(state.trusted_axiom_count(), 0);
    let axiom_before = axiom_snapshot();
    enable_arith_location_tracking();
    let helper_key = "helper:replace_target_with_trusted_fallback:simp";
    let helper_before = tracked_arith_location_count(helper_key);
    let direct_before = direct_arith_file_count(file!());

    state
        .replace_target_with_trusted_fallback(prop_q.clone(), "simp")
        .expect("shared replace-target fallback should rewrite P to Q");

    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        1,
        "simp should increment global arith_proof_count exactly once via helper provenance recording"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        1,
        "simp should increment per-state trusted_axiom_count exactly once"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 1);
    assert_eq!(ledger.trusted_arith_provenance.direct_steps, 0);
    assert_eq!(ledger.trusted_arith_provenance.goal_close_helper_steps, 0);
    assert_eq!(
        ledger.trusted_arith_provenance.target_rewrite_helper_steps,
        1
    );
    assert_eq!(ledger.trusted_arith_provenance.unclassified_steps, 0);
    assert_eq!(
        tracked_arith_location_count(helper_key),
        helper_before + 1,
        "replace-target fallback should expose the helper+tactic provenance key"
    );
    assert_eq!(
        direct_arith_file_count(file!()),
        direct_before,
        "replace-target fallback should not collapse into the test callsite line"
    );
    let goal = state
        .current_goal()
        .expect("fallback should leave the rewritten goal open");
    assert_eq!(
        goal.target, prop_q,
        "fallback should rewrite the goal target"
    );
}
