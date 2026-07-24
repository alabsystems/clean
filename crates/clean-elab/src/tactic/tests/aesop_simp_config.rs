// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::{AesopRule, AesopRuleBuilder, AesopRulePhase, Environment};

fn setup_env_with_simp_lemma() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Foo"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for name in ["bar", "baz"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("Foo"), vec![]),
        })
        .unwrap();
    }

    let foo = Expr::const_(Name::from_string("Foo"), vec![]);
    let bar = Expr::const_(Name::from_string("bar"), vec![]);
    let baz = Expr::const_(Name::from_string("baz"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_type = Expr::app(Expr::app(Expr::app(eq, foo), bar), baz);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("bar_eq_baz"),
        level_params: vec![],
        type_: eq_type,
    })
    .unwrap();

    env.register_aesop_rule(AesopRule {
        name: Name::from_string("bar_eq_baz"),
        phase: AesopRulePhase::Norm,
        builder: AesopRuleBuilder::Simp,
        builder_args: vec![],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    env
}

fn build_prebuilt_simp_state(only_simplify: bool) -> (ProofState, SimpConfig, Expr) {
    let mut env = setup_env_with_simp_lemma();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Foo"), vec![]),
    })
    .unwrap();

    let foo = Expr::const_(Name::from_string("Foo"), vec![]);
    let bar = Expr::const_(Name::from_string("bar"), vec![]);
    let baz = Expr::const_(Name::from_string("baz"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let h_ty = Expr::app(
        Expr::app(Expr::app(eq.clone(), foo.clone()), bar.clone()),
        q.clone(),
    );
    let goal = Expr::app(
        Expr::app(Expr::app(eq.clone(), foo.clone()), baz.clone()),
        q.clone(),
    );

    let state = ProofState::with_context(
        env,
        goal.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let mut config = SimpConfig::new();
    config.only_simplify = only_simplify;
    config.aesop_simp_lemmas.push(SimpLemma {
        name: Name::from_string("bar_eq_baz"),
        lhs: bar,
        rhs: baz,
        eq_type: Some(foo),
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 100,
    });

    (state, config, goal)
}

#[test]
fn aesop_simp_integration_documentation() {
    let env = setup_env_with_simp_lemma();
    assert!(
        !env.get_aesop_norm_rules().is_empty(),
        "should have registered norm rules"
    );

    let norm_rules = env.get_aesop_norm_rules();
    let simp_rules: Vec<_> = norm_rules
        .iter()
        .filter(|r| r.builder == AesopRuleBuilder::Simp)
        .collect();
    assert_eq!(simp_rules.len(), 1, "should have one simp rule");
    assert_eq!(
        simp_rules[0].name.to_string(),
        "bar_eq_baz",
        "simp rule should be bar_eq_baz"
    );
}

#[test]
fn test_simp_all_with_config_preserves_prebuilt_simp_lemmas() {
    let (mut state, config, _) = build_prebuilt_simp_state(false);
    let result = simp_all_with_config(&mut state, config);

    assert!(
        result.is_ok(),
        "simp_all_with_config should preserve prebuilt caller lemmas so \
         h : bar = q rewrites to baz = q and closes by assumption. Got: {result:?}"
    );
    assert!(state.is_complete(), "all goals should be closed");
}

#[test]
fn test_simp_all_with_config_only_simplify_skips_closers() {
    let (mut state, config, goal) = build_prebuilt_simp_state(true);
    let result = simp_all_with_config(&mut state, config);

    assert!(
        result.is_ok(),
        "simp_all_with_config should still report simplification progress with \
         only_simplify enabled. Got: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "only_simplify should leave the goal open instead of closing via assumption"
    );

    let current_goal = state.current_goal().expect("goal should remain open");
    let h_decl = current_goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("hypothesis h should still be present");
    assert_eq!(
        h_decl.ty, goal,
        "only_simplify should still rewrite h : bar = q to h : baz = q"
    );
}
