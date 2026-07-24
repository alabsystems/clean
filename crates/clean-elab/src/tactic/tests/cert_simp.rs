// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the project-tuned `cert_simp` tactic.

use super::*;
use clean_kernel::env::SimpPriority;
use serial_test::serial;

#[test]
#[serial]
fn test_cert_simp_closes_local_rewrite_without_trusted_fallback() {
    reset_all_counters();

    let env = setup_env_with_eq();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let h_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let target = Expr::pi(
        BinderInfo::Default,
        h_ty,
        make_eq(a_ty, Expr::app(f.clone(), a), Expr::app(f, b)),
    );
    let mut state = ProofState::new(env, target);
    intro(&mut state, "h").expect("intro should expose local equality");
    let axiom_before = axiom_snapshot();

    cert_simp(&mut state).expect("cert_simp should rewrite with the local equality");

    assert!(state.is_complete(), "cert_simp should close the goal");
    assert_eq!(
        state.trust_ledger().trusted_arith_count,
        0,
        "cert_simp must not record trustedArith usage"
    );
    assert_eq!(
        state.trust_ledger().sorry_count,
        0,
        "cert_simp must not record sorry usage"
    );
    assert_no_trusted_axiom_usage("cert_simp", "local equality rewrite", axiom_before);
}

#[test]
fn test_cert_simp_reports_certificate_blocker_on_no_progress() {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("List.filter"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    let target = Expr::const_(Name::from_string("List.filter"), vec![]);
    let mut state = ProofState::new(env, target);

    let err = cert_simp(&mut state).expect_err("unsupported head should fail closed");

    match err {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "cert_simp");
            assert!(
                detail.contains("List.filter"),
                "blocker detail should mention List.filter, got {detail}"
            );
        }
        other => panic!("expected SearchExhausted, got {other:?}"),
    }
}

#[test]
fn test_cert_simp_unfolds_certificate_definition_in_hypothesis() {
    let mut env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("m"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat,
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Cert.PB.checkBound"),
        level_params: vec![],
        type_: Expr::prop(),
        value: make_nat_le_tc(
            Expr::const_(Name::from_string("m"), vec![]),
            Expr::const_(Name::from_string("n"), vec![]),
        ),
        is_reducible: true,
    })
    .unwrap();

    let mut state = ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".into(),
            ty: Expr::const_(Name::from_string("Cert.PB.checkBound"), vec![]),
            value: None,
        }],
    );

    cert_simp(&mut state).expect("cert_simp should unfold certificate definitions");

    let h = state
        .current_goal()
        .expect("symbolic bound should not close by simplification alone")
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("simplified hypothesis should keep its name");
    assert!(
        expr_contains_const(&h.ty, "LE.le"),
        "certificate bound should expose an arithmetic relation, got {:?}",
        h.ty
    );
    assert!(
        !expr_contains_const(&h.ty, "Cert.PB.checkBound"),
        "certificate wrapper should be unfolded away, got {:?}",
        h.ty
    );
}

#[test]
fn test_cert_simp_lemma_pack_filters_missing_and_axiom_candidates() {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("List.map"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Expr::prop(),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("List.filter"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("domainAxiom"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    })
    .unwrap();
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("List.map_append"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
        value: Expr::const_(Name::from_string("domainAxiom"), vec![]),
    })
    .unwrap();
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("List.filter_append"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
        value: Expr::const_(Name::from_string("True.intro"), vec![]),
    })
    .unwrap();
    assert!(
        matches!(
            env.proof_quality(&Name::from_string("List.filter_append")),
            Some(clean_kernel::ProofQuality::Constructive)
        ),
        "test setup should make List.filter_append constructive"
    );

    let state = ProofState::new(env, Expr::prop());
    let names = super::super::cert_simp::cert_simp_lemma_names(&state, &CertSimpConfig::default());

    assert!(
        names.iter().any(|name| name == "List.map"),
        "checked definitions present in the environment should be selected"
    );
    assert!(
        !names.iter().any(|name| name == "List.filter"),
        "axiom-backed candidates should be skipped by default"
    );
    assert!(
        !names.iter().any(|name| name == "List.map_append"),
        "axiom-dependent theorem candidates should be skipped by default"
    );
    assert!(
        !names.iter().any(|name| name == "List.filter_append"),
        "constructive theorem candidates that are not rewrite equations should be skipped"
    );
    assert!(
        !names.iter().any(|name| name == "List.flatMap"),
        "missing candidates should be ignored"
    );
}

#[test]
fn test_cert_simp_ignores_global_simp_registry_outside_project_pack() {
    let mut env = Environment::with_prelude();
    let target = make_eq(
        Expr::prop(),
        Expr::const_(Name::from_string("False"), vec![]),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("rogue_axiom"),
        level_params: vec![],
        type_: target.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("rogue_simp"),
        level_params: vec![],
        type_: target.clone(),
        value: Expr::const_(Name::from_string("rogue_axiom"), vec![]),
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("rogue_simp"), SimpPriority::Default);

    let mut state = ProofState::new(env, target.clone());

    let err = cert_simp(&mut state)
        .expect_err("cert_simp must not use arbitrary global simp registry lemmas");

    assert!(
        matches!(err, TacticError::SearchExhausted { .. }),
        "expected fail-closed no-progress diagnostic, got {err:?}"
    );
    assert_eq!(
        state
            .current_goal()
            .expect("goal should remain open")
            .target,
        target,
        "registry-only rewrite should not mutate the target"
    );
}

fn expr_contains_const(expr: &Expr, needle: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == needle,
        ExprKind::App(f, arg) => expr_contains_const(f, needle) || expr_contains_const(arg, needle),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, needle) || expr_contains_const(body, needle)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, needle)
                || expr_contains_const(val, needle)
                || expr_contains_const(body, needle)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            expr_contains_const(inner, needle)
        }
        _ => false,
    }
}
