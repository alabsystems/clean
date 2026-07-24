// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, ExprKind, Name};

struct TrackingFixture {
    state: ProofState,
    goal: Goal,
    config: SimpConfig,
    simp_lemmas: SimpLemmaSet,
    expr: Expr,
    wrap_expr: Expr,
}

fn nat_eq_const() -> (Expr, Expr) {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_const = Expr::const_(
        Name::from_string("Eq"),
        vec![clean_kernel::level::Level::succ(
            clean_kernel::level::Level::zero(),
        )],
    );
    (nat_ty, eq_const)
}

fn add_test_axioms(env: &mut clean_kernel::Environment, nat_ty: &Expr, eq_const: &Expr) {
    for name in ["n", "m"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty.clone(),
        })
        .unwrap();
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Test.wrap"),
        level_params: vec![],
        type_: Expr::arrow(nat_ty.clone(), nat_ty.clone()),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Test.pack"),
        level_params: vec![],
        type_: Expr::arrow(nat_ty.clone(), Expr::arrow(nat_ty.clone(), nat_ty.clone())),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Test.wrap_id"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            nat_ty.clone(),
            Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), nat_ty.clone()),
                    Expr::app(
                        Expr::const_(Name::from_string("Test.wrap"), vec![]),
                        Expr::bvar(0),
                    ),
                ),
                Expr::bvar(0),
            ),
        ),
    })
    .unwrap();
}

fn build_fixture() -> TrackingFixture {
    let mut env = clean_kernel::Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    let (nat_ty, eq_const) = nat_eq_const();
    add_test_axioms(&mut env, &nat_ty, &eq_const);

    let n = Expr::const_(Name::from_string("n"), vec![]);
    let m = Expr::const_(Name::from_string("m"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Test.pack"), vec![]),
            Expr::app(Expr::app(nat_add, n), nat_zero),
        ),
        Expr::app(
            Expr::const_(Name::from_string("Test.wrap"), vec![]),
            m.clone(),
        ),
    );
    let wrap_expr = Expr::app(Expr::const_(Name::from_string("Test.wrap"), vec![]), m);
    let goal_target = Expr::app(
        Expr::app(Expr::app(eq_const, nat_ty), expr.clone()),
        expr.clone(),
    );
    let state = ProofState::new(env, goal_target);
    let goal = state.current_goal().expect("goal should exist").clone();
    let mut config = SimpConfig::new();
    config.extra_lemmas.push("Test.wrap_id".to_string());
    let simp_lemmas = collect_simp_lemmas(&state, &config);

    TrackingFixture {
        state,
        goal,
        config,
        simp_lemmas,
        expr,
        wrap_expr,
    }
}

fn applied_named_lemmas(fixture: &TrackingFixture, expr: &Expr) -> Vec<String> {
    simp_expr_tracking(
        &fixture.state,
        &fixture.goal,
        expr,
        &fixture.simp_lemmas,
        &fixture.config,
    )
    .applied_named_lemmas
}

fn build_recursive_app_result_case() -> (ProofState, SqueezeSimpConfig) {
    let mut env = clean_kernel::Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    let (nat_ty, eq_const) = nat_eq_const();
    add_test_axioms(&mut env, &nat_ty, &eq_const);

    let n = Expr::const_(Name::from_string("n"), vec![]);
    let m = Expr::const_(Name::from_string("m"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Test.pack"), vec![]),
            Expr::app(Expr::app(nat_add, n.clone()), nat_zero),
        ),
        Expr::app(
            Expr::const_(Name::from_string("Test.wrap"), vec![]),
            m.clone(),
        ),
    );
    let rhs = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Test.pack"), vec![]), n),
        m,
    );
    let goal_target = Expr::app(Expr::app(Expr::app(eq_const, nat_ty), lhs), rhs);
    let mut config = SqueezeSimpConfig::new();
    config
        .simp_config
        .extra_lemmas
        .push("Test.wrap_id".to_string());
    (ProofState::new(env, goal_target), config)
}

fn build_recursive_let_expr() -> Expr {
    let (nat_ty, _) = nat_eq_const();
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let m = Expr::const_(Name::from_string("m"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    Expr::let_named(
        Name::anon(),
        nat_ty,
        Expr::app(Expr::const_(Name::from_string("Test.wrap"), vec![]), m),
        Expr::app(Expr::app(nat_add, n), nat_zero),
        false,
    )
}

#[test]
fn test_simp_expr_tracking_collects_recursive_app_lemmas() {
    let fixture = build_fixture();
    assert!(
        fixture
            .simp_lemmas
            .iter()
            .any(|lemma| lemma.name.to_string() == "Test.wrap_id"),
        "Test.wrap_id should be collected as an extra simp lemma"
    );
    assert_eq!(
        applied_named_lemmas(&fixture, &fixture.wrap_expr),
        vec!["Test.wrap_id".to_string()],
        "the right child should simplify via Test.wrap_id before testing the App merge"
    );

    let tracked = applied_named_lemmas(&fixture, &fixture.expr);
    assert_eq!(
        tracked,
        vec!["Nat.add_zero".to_string(), "Test.wrap_id".to_string()],
        "recursive App tracking should keep both child lemmas in order"
    );

    let mut used_lemmas = Vec::new();
    extend_unique_lemmas(&mut used_lemmas, tracked);
    assert_eq!(
        used_lemmas,
        vec!["Nat.add_zero".to_string(), "Test.wrap_id".to_string()],
        "used_lemmas should keep both recursive App lemmas"
    );
    assert_eq!(
        format!("simp only [{}]", used_lemmas.join(", ")),
        "simp only [Nat.add_zero, Test.wrap_id]"
    );
}

#[test]
fn test_simp_expr_tracking_collects_recursive_let_lemmas() {
    let fixture = build_fixture();
    let let_expr = build_recursive_let_expr();
    let ExprKind::Let(_, _, val, body, _) = let_expr.kind() else {
        panic!("expected recursive let fixture");
    };
    assert_eq!(
        applied_named_lemmas(&fixture, val),
        vec!["Test.wrap_id".to_string()],
        "the let value should simplify via Test.wrap_id before aggregation"
    );
    assert_eq!(
        applied_named_lemmas(&fixture, body),
        vec!["Nat.add_zero".to_string()],
        "the let body should simplify via Nat.add_zero before aggregation"
    );

    let tracked = applied_named_lemmas(&fixture, &let_expr);
    assert_eq!(
        tracked,
        vec!["Test.wrap_id".to_string(), "Nat.add_zero".to_string()],
        "recursive Let tracking should keep value and body lemmas in order"
    );

    let mut used_lemmas = Vec::new();
    extend_unique_lemmas(&mut used_lemmas, tracked);
    assert_eq!(
        used_lemmas,
        vec!["Test.wrap_id".to_string(), "Nat.add_zero".to_string()],
        "used_lemmas should keep both recursive Let lemmas"
    );
}

#[test]
fn test_squeeze_simp_tracks_recursive_app_lemmas_in_result() {
    let (mut state, config) = build_recursive_app_result_case();
    let result = squeeze_simp_with_config(&mut state, config).expect("squeeze_simp should succeed");

    assert_eq!(
        result.used_lemmas,
        vec!["Nat.add_zero".to_string(), "Test.wrap_id".to_string()],
        "squeeze_simp should keep both recursive App lemmas in result order"
    );
    assert_eq!(
        result.suggested_tactic, "simp only [Nat.add_zero, Test.wrap_id]",
        "squeeze_simp should expose both child lemmas in the suggestion"
    );
    assert!(
        result.closed,
        "squeeze_simp should close the simplified goal"
    );
    assert!(
        state.goals().is_empty(),
        "closed squeeze_simp result should leave no goals"
    );
}

#[test]
fn test_simp_expr_tracking_collects_proj_inner_lemmas() {
    let fixture = build_fixture();
    // Proj("Test.Struct", 0, Test.wrap(m)) — simp should find Test.wrap_id inside the Proj
    let proj_expr = Expr::proj(
        Name::from_string("Test.Struct"),
        0,
        fixture.wrap_expr.clone(),
    );
    let tracked = applied_named_lemmas(&fixture, &proj_expr);
    assert_eq!(
        tracked,
        vec!["Test.wrap_id".to_string()],
        "recursive Proj tracking should find lemmas inside the projection target"
    );
}

#[test]
fn test_simp_expr_tracking_collects_mdata_inner_lemmas() {
    let fixture = build_fixture();
    // MData([], Test.wrap(m)) — simp should find Test.wrap_id inside the MData wrapper
    let mdata_expr = Expr::mdata(vec![], fixture.wrap_expr.clone());
    let tracked = applied_named_lemmas(&fixture, &mdata_expr);
    assert_eq!(
        tracked,
        vec!["Test.wrap_id".to_string()],
        "MData should be transparent — simp should find lemmas inside the metadata wrapper"
    );
}
